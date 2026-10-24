/**
 * Recursive-descent parser for OPL 3.x models, data files and OPLScript.
 */

import type {
  Binder, CStmt, DataAst, DataInit, Dim, Expr, FieldDecl, ModelAst, Quantifier, ResourceDeclKind,
  ScriptAst, ScriptStmt, SStmt, Stmt, TypeExpr,
} from './ast.js';
import { fail, type SourcePos } from './errors.js';
import { tokenize, type Token } from './lexer.js';

const COMPARISON = new Set(['=', '==', '!=', '<>', '<', '<=', '>', '>=']);
const AGGREGATES = new Set(['sum', 'prod', 'min', 'max', 'or', 'and', 'all', 'union', 'inter']);
/** Binary scheduling constraints written infix: `a precedes b;`, `a requires(2) r;`. */
const INFIX_CONSTRAINTS = new Set(['precedes', 'requires', 'consumes', 'produces']);
const FILTER_LEVELS = new Set(['onValue', 'onDomain', 'onRange', 'onBounds']);
const RESOURCE_KINDS = new Set(['UnaryResource', 'DiscreteResource', 'Reservoir', 'StateResource', 'AlternativeResources']);
/** `sorted {int}`, `ordered {string}`, `reversed {int}`: ordering qualifiers of set types. */
const SET_QUALIFIERS = new Set(['sorted', 'ordered', 'reversed']);
const STRATEGIES = new Set(['LDSearch', 'DFSearch', 'BFSearch', 'IDFSearch', 'SBSearch', 'DDSearch']);

class Parser {
  private i = 0;
  constructor(private readonly toks: Token[]) {}

  // ------------------------------------------------------------ token helpers

  peek(k = 0): Token {
    return this.toks[Math.min(this.i + k, this.toks.length - 1)];
  }
  next(): Token {
    const t = this.toks[this.i];
    if (this.i < this.toks.length - 1) this.i++;
    return t;
  }
  get pos(): SourcePos {
    return this.peek().pos;
  }
  atEnd(): boolean {
    return this.peek().kind === 'eof';
  }
  isPunct(text: string, k = 0): boolean {
    const t = this.peek(k);
    return t.kind === 'punct' && t.text === text;
  }
  isIdent(text?: string, k = 0): boolean {
    const t = this.peek(k);
    return t.kind === 'ident' && (text === undefined || t.text === text);
  }
  acceptPunct(text: string): boolean {
    if (!this.isPunct(text)) return false;
    this.next();
    return true;
  }
  acceptIdent(text: string): boolean {
    if (!this.isIdent(text)) return false;
    this.next();
    return true;
  }
  expectPunct(text: string): Token {
    if (!this.isPunct(text)) this.unexpected(`'${text}'`);
    return this.next();
  }
  expectIdent(text?: string): Token {
    if (!this.isIdent(text)) this.unexpected(text ? `'${text}'` : 'an identifier');
    return this.next();
  }
  expectString(): string {
    const t = this.peek();
    if (t.kind !== 'string') this.unexpected('a string');
    this.next();
    return t.value as string;
  }
  unexpected(expected: string): never {
    const t = this.peek();
    fail(`expected ${expected} but found '${t.text}'`, t.pos);
  }

  // ------------------------------------------------------------ expressions

  parseExpr(): Expr {
    const c = this.parseImplies();
    if (this.isPunct('?')) {
      const pos = this.next().pos;
      const a = this.parseExpr();
      this.expectPunct(':');
      const b = this.parseExpr();
      return { k: 'cond', c, a, b, pos };
    }
    return c;
  }

  /** a => b, a <=> b (lowest-precedence logical operators, right-associative). */
  private parseImplies(): Expr {
    const l = this.parseOr();
    if (this.isPunct('=>') || this.isPunct('<=>')) {
      const t = this.next();
      return { k: 'bin', op: t.text, l, r: this.parseImplies(), pos: t.pos };
    }
    return l;
  }

  private parseOr(): Expr {
    let l = this.parseAnd();
    while (this.isPunct('||') || this.isPunct('\\/') || this.isIdent('or')) {
      const pos = this.next().pos;
      l = { k: 'bin', op: '||', l, r: this.parseAnd(), pos };
    }
    return l;
  }

  private parseAnd(): Expr {
    let l = this.parseNot();
    while (this.isPunct('&&') || this.isPunct('&') || this.isPunct('/\\') || this.isIdent('and')) {
      const pos = this.next().pos;
      l = { k: 'bin', op: '&&', l, r: this.parseNot(), pos };
    }
    return l;
  }

  private parseNot(): Expr {
    if (this.isPunct('!') || (this.isIdent('not') && !this.isIdent('in', 1))) {
      const pos = this.next().pos;
      return { k: 'unary', op: '!', e: this.parseNot(), pos };
    }
    return this.parseCompare();
  }

  private parseCompare(): Expr {
    const first = this.parseIn();
    const ops: string[] = [];
    const exprs: Expr[] = [first];
    for (;;) {
      const t = this.peek();
      let op: string | null = null;
      if (t.kind === 'punct' && COMPARISON.has(t.text)) op = t.text;
      if (!op) break;
      this.next();
      ops.push(op === '==' ? '=' : op === '<>' ? '!=' : op);
      exprs.push(this.parseIn());
    }
    if (ops.length === 0) return first;
    if (ops.length === 1) return { k: 'bin', op: ops[0], l: exprs[0], r: exprs[1], pos: first.pos };
    return { k: 'chain', ops, exprs, pos: first.pos };
  }

  /** x in S binds tighter than comparisons: 0 == <o,d> in S  is  0 == (<o,d> in S). */
  private parseIn(): Expr {
    let l = this.parseRange();
    for (;;) {
      let op: string | null = null;
      if (this.isIdent('in')) op = 'in';
      else if (this.isIdent('not') && this.isIdent('in', 1)) op = 'not in';
      if (!op) return l;
      const pos = this.next().pos;
      if (op === 'not in') this.next();
      l = { k: 'bin', op, l, r: this.parseRange(), pos };
    }
  }

  parseRange(): Expr {
    const lo = this.parseAdd();
    if (this.isPunct('..')) {
      this.next();
      const hi = this.parseAdd();
      return { k: 'range', lo, hi, pos: lo.pos };
    }
    return lo;
  }

  parseAdd(): Expr {
    let l = this.parseMul();
    for (;;) {
      let op: string | null = null;
      if (this.isPunct('+') || this.isPunct('-')) op = this.peek().text;
      else if (this.isIdent('union') || this.isIdent('diff') || this.isIdent('symdiff')) op = this.peek().text;
      if (!op) return l;
      const pos = this.next().pos;
      l = { k: 'bin', op, l, r: this.parseMul(), pos };
    }
  }

  private parseMul(): Expr {
    let l = this.parseUnary();
    for (;;) {
      let op: string | null = null;
      if (this.isPunct('*') || this.isPunct('/') || this.isPunct('%')) op = this.peek().text;
      else if (this.isIdent('div') || this.isIdent('mod') || this.isIdent('inter')) op = this.peek().text;
      if (!op) return l;
      const pos = this.next().pos;
      l = { k: 'bin', op: op === '%' ? 'mod' : op, l, r: this.parseUnary(), pos };
    }
  }

  parseUnary(): Expr {
    if (this.isPunct('-') || this.isPunct('+')) {
      const t = this.next();
      const e = this.parseUnary();
      if (e.k === 'num' && t.text === '-') return { ...e, value: -e.value, pos: t.pos };
      return { k: 'unary', op: t.text as '-' | '+', e, pos: t.pos };
    }
    if (this.isPunct('!')) {
      const pos = this.next().pos;
      return { k: 'unary', op: '!', e: this.parseUnary(), pos };
    }
    const base = this.parsePostfix();
    if (this.isPunct('^')) {
      const pos = this.next().pos;
      return { k: 'bin', op: '^', l: base, r: this.parseUnary(), pos };
    }
    return base;
  }

  parsePostfix(): Expr {
    let e = this.parsePrimary();
    for (;;) {
      if (this.isPunct('[')) {
        const pos = this.next().pos;
        const args = [this.parseExpr()];
        while (this.acceptPunct(',')) args.push(this.parseExpr());
        this.expectPunct(']');
        e = { k: 'index', target: e, args, pos };
      } else if (this.isPunct('.') && this.peek(1).kind === 'ident') {
        this.next();
        const name = this.next();
        if (this.isPunct('(')) {
          this.next();
          const args = this.parseArgs(')');
          e = { k: 'method', target: e, name: name.text, args, pos: name.pos };
        } else {
          e = { k: 'field', target: e, name: name.text, pos: name.pos };
        }
      } else {
        return e;
      }
    }
  }

  /** Parses comma separated expressions up to (and including) the closing token. */
  private parseArgs(close: string): Expr[] {
    const args: Expr[] = [];
    if (this.acceptPunct(close)) return args;
    args.push(this.parseExpr());
    while (this.acceptPunct(',')) args.push(this.parseExpr());
    this.expectPunct(close);
    return args;
  }

  private parsePrimary(): Expr {
    const t = this.peek();
    const pos = t.pos;
    if (t.kind === 'int' || t.kind === 'float') {
      this.next();
      return { k: 'num', value: t.value as number, isInt: t.kind === 'int', pos };
    }
    if (t.kind === 'string') {
      this.next();
      return { k: 'str', value: t.value as string, pos };
    }
    if (t.kind === 'ident') {
      if (t.text === 'piecewise' && (this.isPunct('{', 1) || this.isPunct('(', 1))) return this.parsePiecewise();
      if (t.text === 'stepwise' && (this.isPunct('{', 1) || this.isPunct('(', 1))) {
        // stepwise{ v1 -> x1; v2 -> x2; ...; vn }: the same shape as piecewise.
        const e = this.parsePiecewise();
        if (e.k !== 'piecewise' || e.origin || e.operand) this.unexpected('stepwise{ value -> point; ...; last value }');
        return { k: 'stepwise', q: e.q, items: e.items, last: e.last, pos: e.pos };
      }
      if (AGGREGATES.has(t.text) && this.isPunct('(', 1) &&
          (t.text === 'sum' || t.text === 'prod' || this.binderFollows(2))) {
        this.next();
        this.next();
        const q = this.parseQuantifier(')');
        // all(...) builds an array argument: its body extends to the closing parenthesis.
        // all(...) builds an array argument: its body extends to the closing parenthesis;
        // or(...) / and(...) take a condition.
        const body = t.text === 'all' ? this.parseExpr() : t.text === 'or' || t.text === 'and' ? this.parseNot() : this.parseMul();
        return { k: 'agg', op: t.text, q, body, pos };
      }
      this.next();
      if (this.isPunct('(')) {
        this.next();
        return { k: 'call', fn: t.text, args: this.parseArgs(')'), pos };
      }
      return { k: 'id', name: t.text, pos };
    }
    if (this.acceptPunct('(')) {
      const e = this.parseExpr();
      this.expectPunct(')');
      return e;
    }
    if (this.acceptPunct('{')) {
      if (this.acceptPunct('}')) return { k: 'setLit', items: [], pos };
      const first = this.parseExpr();
      if (this.acceptPunct('|')) {
        const q = this.parseQuantifier('}');
        return { k: 'setComp', head: first, q, pos };
      }
      const items = [first];
      this.parseItems(items, '}', () => this.parseExpr());
      return { k: 'setLit', items, pos };
    }
    if (this.acceptPunct('[')) {
      if (this.acceptPunct(']')) return { k: 'arrayLit', items: [], pos };
      const first = this.parseExpr();
      // [key : value | quantifier] and [value | quantifier]
      if (this.isPunct(':') || this.isPunct('|')) {
        let key: Expr | null = null;
        let value = first;
        if (this.acceptPunct(':')) {
          key = first;
          value = this.parseExpr();
          // [key : value] (no quantifier): one entry, as in [i : [t : v] | <i,t,v> in S]
          if (this.acceptPunct(']')) return { k: 'indexedLit', entries: [{ key, value }], pos };
        }
        this.expectPunct('|');
        return { k: 'arrayComp', key, value, q: this.parseQuantifier(']'), pos };
      }
      const items: Expr[] = [first];
      this.parseItems(items, ']', () => this.parseExpr());
      return { k: 'arrayLit', items, pos };
    }
    if (this.acceptPunct('#[')) {
      return { k: 'indexedLit', entries: this.parseIndexedEntries(() => this.parseRange(), () => this.parseExpr()), pos };
    }
    if (this.acceptPunct('<')) {
      const items: Expr[] = [];
      this.parseItems(items, '>', () => this.parseRange());
      return { k: 'tuple', items, pos };
    }
    if (this.acceptPunct('#<')) {
      return { k: 'namedTuple', fields: this.parseNamedFields(() => this.parseRange()), pos };
    }
    this.unexpected('an expression');
  }

  /** piecewise[(q)]{ slope -> breakpoint; ...; lastSlope } [(x0, y0)] [operand] */
  private parsePiecewise(): Expr {
    const pos = this.next().pos;
    const q = this.acceptPunct('(') ? this.parseQuantifier(')') : null;
    this.expectPunct('{');
    const items: { slope: Expr; bp: Expr }[] = [];
    let last: Expr;
    for (;;) {
      const e = this.parseExpr();
      if (this.acceptPunct('->')) {
        items.push({ slope: e, bp: this.parseExpr() });
        this.expectPunct(';');
        continue;
      }
      last = e;
      this.acceptPunct(';');
      this.expectPunct('}');
      break;
    }
    let origin: [Expr, Expr] | null = null;
    let operand: Expr | null = null;
    if (this.acceptPunct('(')) {
      const args = this.parseArgs(')');
      if (args.length === 2) origin = [args[0], args[1]];
      else if (args.length === 1) operand = args[0];
      else this.unexpected('(x0, y0) or an operand');
    }
    const t = this.peek();
    if (!operand && (t.kind === 'ident' || t.kind === 'int' || t.kind === 'float' || this.isPunct('(') || this.isPunct('-'))) {
      operand = this.parseUnary();
    }
    return { k: 'piecewise', q, items, last, origin, operand, pos };
  }

  /** Items separated by optional commas, up to the closing token. */
  private parseItems(items: Expr[], close: string, item: () => Expr): void {
    for (;;) {
      if (this.acceptPunct(close)) return;
      if (items.length > 0) this.acceptPunct(',');
      if (this.acceptPunct(close)) return;
      items.push(item());
    }
  }

  private parseIndexedEntries(key: () => Expr, value: () => Expr): { key: Expr; value: Expr }[] {
    const entries: { key: Expr; value: Expr }[] = [];
    for (;;) {
      if (this.acceptPunct(']#')) return entries;
      if (entries.length > 0) this.acceptPunct(',');
      if (this.acceptPunct(']#')) return entries;
      const k = key();
      this.expectPunct(':');
      entries.push({ key: k, value: value() });
    }
  }

  private parseNamedFields(value: () => Expr): { name: string; value: Expr }[] {
    const fields: { name: string; value: Expr }[] = [];
    for (;;) {
      if (this.acceptPunct('>#')) return fields;
      if (fields.length > 0) this.acceptPunct(',');
      if (this.acceptPunct('>#')) return fields;
      const name = this.expectIdent().text;
      this.expectPunct(':');
      fields.push({ name, value: value() });
    }
  }

  /** True when the tokens at offset k start a binder: `i in`, `i, j in` or `<`. */
  private binderFollows(k: number): boolean {
    if (this.isIdent('ordered', k) && !this.isIdent('by', k + 1)) k++;
    if (this.isPunct('<', k)) return true;
    let j = k;
    for (;;) {
      if (!this.isIdent(undefined, j)) return false;
      j++;
      if (this.isIdent('in', j)) return true;
      if (!this.isPunct(',', j)) return false;
      j++;
    }
  }

  /** Parses binders up to (and including) the closing token. */
  parseQuantifier(close: string): Quantifier {
    const pos = this.pos;
    const binders: Binder[] = [];
    for (;;) {
      const bpos = this.pos;
      const names: string[] = [];
      let pattern = false;
      const ordered = this.isIdent('ordered') && !this.isIdent('by', 1) && this.isIdent(undefined, 1) ? (this.next(), true) : false;
      let patternExprs: (Expr | null)[] | undefined;
      if (this.acceptPunct('<')) {
        pattern = true;
        const exprs: (Expr | null)[] = [];
        do {
          if (this.isIdent() && (this.isPunct(',', 1) || this.isPunct('>', 1))) {
            names.push(this.next().text);
            exprs.push(null);
          } else {
            names.push(`$pattern${names.length}`);
            exprs.push(this.parseAdd());
          }
        } while (this.acceptPunct(','));
        this.expectPunct('>');
        if (exprs.some((x) => x)) patternExprs = exprs;
      } else {
        names.push(this.expectIdent().text);
        while (this.acceptPunct(',')) names.push(this.expectIdent().text);
      }
      this.expectIdent('in');
      const domain = this.parseRange();
      const binder: Binder = { names, pattern, domain, pos: bpos };
      if (patternExprs) binder.patternExprs = patternExprs;
      if (ordered) binder.ordered = true;
      if (this.acceptPunct(':')) binder.filter = this.parseExpr();
      binders.push(binder);
      if (this.acceptPunct(',')) continue;
      const q: Quantifier = { binders, pos };
      if (this.isIdent('ordered') && this.isIdent('by', 1)) {
        this.next();
        this.next();
        const dir = this.expectIdent().text;
        if (dir !== 'increasing' && dir !== 'decreasing') fail("expected 'increasing' or 'decreasing'", this.pos);
        q.order = { dir: dir === 'increasing' ? 1 : -1, key: this.parseExpr() };
      }
      this.expectPunct(close);
      return q;
    }
  }

  // ------------------------------------------------------------ declarations

  isTypeStart(): boolean {
    const t = this.peek();
    if (t.kind === 'punct') return t.text === '{';
    if (t.kind !== 'ident') return false;
    if (['int', 'float', 'string', 'setof', 'boolean'].includes(t.text)) return true;
    if (SET_QUALIFIERS.has(t.text) && this.isPunct('{', 1)) return true;
    // `Name name` is a declaration with a user-defined type.
    return this.peek(1).kind === 'ident' && !['in', 'to', 'not'].includes(this.peek(1).text);
  }

  parseType(): TypeExpr {
    if (this.isIdent() && SET_QUALIFIERS.has(this.peek().text) && this.isPunct('{', 1)) this.next();
    const t = this.peek();
    if (this.acceptPunct('{')) {
      const of = this.parseType();
      this.expectPunct('}');
      return { k: 'set', of };
    }
    const id = this.expectIdent();
    switch (id.text) {
      case 'int':
        return { k: 'int', nonneg: this.acceptPunct('+') };
      case 'float':
        return { k: 'float', nonneg: this.acceptPunct('+') };
      case 'string':
        return { k: 'string' };
      case 'setof': {
        this.expectPunct('(');
        const of = this.parseType();
        this.expectPunct(')');
        return { k: 'set', of };
      }
      default:
        return { k: 'named', name: id.text, pos: t.pos };
    }
  }

  parseDims(): Dim[] {
    const dims: Dim[] = [];
    while (this.acceptPunct('[')) {
      for (;;) {
        if (this.isIdent() && this.isIdent('in', 1)) {
          const name = this.next().text;
          this.next();
          dims.push({ name, domain: this.parseRange() });
        } else {
          dims.push({ domain: this.parseRange() });
        }
        if (!this.acceptPunct(',')) break;
      }
      this.expectPunct(']');
    }
    return dims;
  }

  parseRangeBody(): Expr {
    if (this.acceptPunct('[')) {
      const e = this.parseRange();
      this.expectPunct(']');
      return e;
    }
    this.acceptPunct('=');
    return this.parseRange();
  }

  private parseEnumValues(): string[] {
    const values: string[] = [];
    this.expectPunct('{');
    for (;;) {
      if (this.acceptPunct('}')) return values;
      if (values.length > 0) this.acceptPunct(',');
      if (this.acceptPunct('}')) return values;
      values.push(this.expectIdent().text);
    }
  }

  // ------------------------------------------------------------ model

  parseModel(file: string): ModelAst {
    const stmts: Stmt[] = [];
    while (!this.atEnd()) {
      if (this.acceptPunct(';')) continue;
      stmts.push(...this.parseModelStmt());
    }
    return { file, stmts };
  }

  private parseModelStmt(): Stmt[] {
    const t = this.peek();
    const pos = t.pos;
    if (t.kind === 'ident') {
      switch (t.text) {
        case 'range': {
          this.next();
          this.acceptIdent('int');
          const name = this.expectIdent().text;
          const e = this.parseRangeBody();
          this.expectPunct(';');
          return [{ k: 'range', name, e, pos }];
        }
        case 'enum': {
          this.next();
          const name = this.expectIdent().text;
          this.acceptPunct('=');
          let values: string[] | null = null;
          if (!this.acceptPunct('...')) values = this.parseEnumValues();
          this.expectPunct(';');
          return [{ k: 'enum', name, values, pos }];
        }
        case 'struct':
        case 'tuple': {
          this.next();
          const name = this.expectIdent().text;
          this.expectPunct('{');
          const fields: FieldDecl[] = [];
          while (!this.acceptPunct('}')) {
            const fpos = this.pos;
            const key = this.acceptIdent('key');
            const type = this.parseType();
            const fname = this.expectIdent().text;
            const dims = this.parseDims();
            this.expectPunct(';');
            fields.push({ type, name: fname, dims, key, pos: fpos });
          }
          this.acceptPunct(';');
          return [{ k: 'struct', name, fields, pos }];
        }
        case 'var':
        case 'dvar': {
          this.next();
          const modern = t.text === 'dvar';
          if (this.acceptIdent('interval')) return this.parseIntervalVars(modern);
          if (this.acceptIdent('sequence')) return this.parseSequenceVars();
          const type = this.parseType();
          const out: Stmt[] = [];
          do {
            const vpos = this.pos;
            const name = this.expectIdent().text;
            const dims = this.parseDims();
            const domain = this.acceptIdent('in') ? this.parseRange() : null;
            // dvar int x[1..3] = [a, b, c];  (an array of existing variables)
            const alias = this.acceptPunct('=') ? this.parseExpr() : undefined;
            out.push({ k: 'var', type, name, dims, domain, modern, alias, pos: vpos });
          } while (this.acceptPunct(','));
          this.expectPunct(';');
          return out;
        }
        case 'dexpr': {
          this.next();
          const type = this.parseType();
          const name = this.expectIdent().text;
          const dims = this.parseDims();
          this.expectPunct('=');
          const e = this.parseExpr();
          this.expectPunct(';');
          return [{ k: 'dexpr', type, name, dims, e, pos }];
        }
        case 'using': {
          this.next();
          const solver = this.expectIdent().text;
          this.expectPunct(';');
          return [{ k: 'using', solver, pos }];
        }
        case 'execute':
        case 'main': {
          this.next();
          const name = t.text === 'execute' && this.peek().kind === 'ident' ? this.next().text : null;
          const body = this.peek();
          if (body.kind !== 'script') this.unexpected("'{'");
          this.next();
          this.acceptPunct(';');
          return [{ k: 'script', kind: t.text, name, code: body.text, pos: body.pos }];
        }
        case 'assert': {
          this.next();
          let label: string | null = null;
          if (this.isIdent() && this.isPunct(':', 1)) {
            label = this.next().text;
            this.next();
          }
          const binders: Binder[] = [];
          while (this.isIdent('forall') && this.isPunct('(', 1)) {
            this.next();
            this.next();
            binders.push(...this.parseQuantifier(')').binders);
          }
          const q: Quantifier | null = binders.length ? { binders, pos } : null;
          if (q && !label && this.isIdent() && this.isPunct(':', 1)) {
            label = this.next().text;
            this.next();
          }
          const e = this.parseExpr();
          this.expectPunct(';');
          return [{ k: 'assert', label, q, e, pos }];
        }
        case 'predicate': {
          // predicate p(int a, int b) in S;  ->  p(x, y) means <x, y> in S
          this.next();
          const name = this.expectIdent().text;
          this.expectPunct('(');
          let arity = 0;
          while (!this.acceptPunct(')')) {
            this.parseType();
            this.expectIdent();
            arity++;
            this.acceptPunct(',');
          }
          this.expectIdent('in');
          const set = this.parseExpr();
          this.expectPunct(';');
          return [{ k: 'predicate', name, arity, set, pos }];
        }
        case 'include': {
          this.next();
          const file = this.expectString();
          this.acceptPunct(';');
          return [{ k: 'include', file, pos }];
        }
        case 'constraints': {
          if (!this.isPunct('{', 1)) break;
          this.next();
          return [{ k: 'objective', sense: null, e: null, constraints: this.parseCBlock(), pos }];
        }
        case 'constraint':
          if (this.isIdent(undefined, 1)) {
            this.next();
            const out: Stmt[] = [];
            do {
              const cpos = this.pos;
              const name = this.expectIdent().text;
              out.push({ k: 'constraintDecl', name, dims: this.parseDims(), pos: cpos });
            } while (this.acceptPunct(','));
            this.expectPunct(';');
            return out;
          }
          break;
        case 'minimize':
        case 'maximize': {
          this.next();
          const e = this.parseExpr();
          let constraints: CStmt[] = [];
          if (this.acceptIdent('subject')) {
            this.expectIdent('to');
            constraints = this.parseCBlock();
          } else if (this.isIdent('constraints') && this.isPunct('{', 1)) {
            this.next();
            constraints = this.parseCBlock();
          } else {
            this.acceptPunct(';');
          }
          return [{ k: 'objective', sense: t.text, e, constraints, pos }];
        }
        case 'subject': {
          this.next();
          this.expectIdent('to');
          return [{ k: 'objective', sense: null, e: null, constraints: this.parseCBlock(), pos }];
        }
        case 'solve': {
          this.next();
          return [{ k: 'objective', sense: null, e: null, constraints: this.parseCBlock(), pos }];
        }
        case 'display':
          this.next();
          return this.parseDisplay(pos);
        case 'search': {
          this.next();
          const body = this.parseSBlock();
          return [{ k: 'search', body, pos }];
        }
        case 'scheduleHorizon':
        case 'ScheduleHorizon':
        case 'scheduleOrigin':
        case 'ScheduleOrigin':
          if (this.isPunct('=', 1)) {
            this.next();
            this.next();
            const e = this.parseExpr();
            this.expectPunct(';');
            return [{ k: 'horizon', which: /horizon/i.test(t.text) ? 'horizon' : 'origin', e, pos }];
          }
          break;
        case 'Activity': {
          this.next();
          const out: Stmt[] = [];
          do {
            const apos = this.pos;
            const name = this.expectIdent().text;
            const dims = this.parseDims();
            let duration: Expr | null = null;
            if (this.acceptPunct('(')) {
              duration = this.parseExpr();
              this.expectPunct(')');
            }
            let breakable = false;
            let transitionType: Expr | null = null;
            for (;;) {
              if (this.acceptIdent('breakable')) breakable = true;
              else if (this.acceptIdent('transitionType')) transitionType = this.parseExpr();
              else break;
            }
            out.push({ k: 'activity', name, dims, duration, breakable, transitionType, pos: apos });
          } while (this.acceptPunct(','));
          this.expectPunct(';');
          return out;
        }
        case 'DBconnection':
        case 'DBConnection': {
          this.next();
          const name = this.expectIdent().text;
          this.expectPunct('(');
          const args = this.parseArgs(')');
          this.expectPunct(';');
          return [{ k: 'dbConnection', name, args, pos }];
        }
        case 'DBupdate':
        case 'DBUpdate':
        case 'DBexecute':
        case 'DBExecute': {
          this.next();
          this.expectPunct('(');
          const conn = this.expectIdent().text;
          this.expectPunct(',');
          const sql = this.parseExpr();
          this.expectPunct(')');
          let e: Expr | null = null;
          if (/update/i.test(t.text)) {
            this.expectPunct('(');
            e = this.parseExpr();
            this.expectPunct(')');
          }
          this.expectPunct(';');
          return [{ k: 'dbUpdate', conn, sql, e, pos }];
        }
        case 'SheetConnection': {
          this.next();
          const name = this.expectIdent().text;
          this.expectPunct('(');
          const args = this.parseArgs(')');
          this.expectPunct(';');
          return [{ k: 'sheetConnection', name, args, pos }];
        }
        case 'SheetWrite': {
          this.next();
          this.expectPunct('(');
          const conn = this.expectIdent().text;
          this.expectPunct(',');
          const range = this.parseExpr();
          this.expectPunct(')');
          this.expectPunct('(');
          const e = this.parseExpr();
          this.expectPunct(')');
          this.expectPunct(';');
          return [{ k: 'sheetWrite', conn, range, e, pos }];
        }
      }
    }
    if (t.kind === 'ident' && RESOURCE_KINDS.has(t.text) && this.isIdent(undefined, 1)) {
      this.next();
      const out: Stmt[] = [];
      do {
        const rpos = this.pos;
        const name = this.expectIdent().text;
        const dims = this.parseDims();
        const args = this.acceptPunct('(') ? this.parseArgs(')') : [];
        out.push({ k: 'resource', kind: t.text as ResourceDeclKind, name, dims, args, pos: rpos });
      } while (this.acceptPunct(','));
      this.expectPunct(';');
      return out;
    }
    if (!this.isTypeStart()) this.unexpected('a declaration or statement');
    return [this.parseDataDecl()];
  }

  /** dvar sequence s[dims] in intervals [types t]; */
  private parseSequenceVars(): Stmt[] {
    const out: Stmt[] = [];
    do {
      const pos = this.pos;
      const name = this.expectIdent().text;
      const dims = this.parseDims();
      if (!this.acceptIdent('in')) this.unexpected("'in' and the intervals of the sequence");
      const intervals = this.parseExpr();
      const types = this.acceptIdent('types') ? this.parseExpr() : null;
      out.push({ k: 'sequence', name, dims, intervals, types, pos });
    } while (this.acceptPunct(','));
    this.expectPunct(';');
    return out;
  }

  /** dvar interval a[dims] [optional] [in lo..hi] [size s] [intensity F]; */
  private parseIntervalVars(modern: boolean): Stmt[] {
    const out: Stmt[] = [];
    do {
      const pos = this.pos;
      const name = this.expectIdent().text;
      const dims = this.parseDims();
      const spec = { optional: false, window: null as Expr | null, size: null as Expr | null, intensity: null as Expr | null };
      for (;;) {
        if (this.acceptIdent('optional')) {
          if (this.acceptPunct('(')) {
            this.parseExpr();
            this.expectPunct(')');
          }
          spec.optional = true;
        } else if (this.acceptIdent('in')) spec.window = this.parseRange();
        else if (this.acceptIdent('size')) spec.size = this.parseRange();
        else if (this.acceptIdent('intensity')) spec.intensity = this.parseExpr();
        else break;
      }
      out.push({ k: 'var', type: { k: 'int', nonneg: true }, name, dims, domain: null, modern, interval: spec, pos });
    } while (this.acceptPunct(','));
    this.expectPunct(';');
    return out;
  }

  private parseDataDecl(): Stmt {
    const pos = this.pos;
    const type = this.parseType();
    const name = this.expectIdent().text;
    const dims = this.parseDims();
    // `{Arc} arcs with o in Nodes, d in Nodes = ...;` (referential integrity, not checked)
    if (this.acceptIdent('with')) {
      do {
        this.expectIdent();
        while (this.acceptPunct(',')) this.expectIdent();
        this.expectIdent('in');
        this.parseRange();
      } while (this.acceptPunct(','));
    }
    let init: DataInit | null = null;
    if (this.acceptPunct('=')) {
      init = this.acceptPunct('...') ? { k: 'external' } : { k: 'expr', e: this.parseExpr() };
    } else if (this.acceptIdent('from')) {
      const src = this.expectIdent().text;
      if (src !== 'SheetRead' && !/^DBread$/i.test(src)) fail(`expected SheetRead or DBread, found '${src}'`, this.pos);
      this.expectPunct('(');
      const conn = this.expectIdent().text;
      this.expectPunct(',');
      const range = this.parseExpr();
      this.expectPunct(')');
      init = src === 'SheetRead' ? { k: 'sheet', conn, range } : { k: 'db', conn, sql: range };
    } else if (this.acceptPunct('<<')) {
      init = { k: 'prompt', text: this.expectString() };
    } else if (this.acceptPunct('<')) {
      init = { k: 'file', path: this.expectString() };
    }
    this.expectPunct(';');
    return { k: 'data', type, name, dims, init, pos };
  }

  parseDisplay(pos: SourcePos): { k: 'display'; q: Quantifier | null; e: Expr; pos: SourcePos }[] {
    let q: Quantifier | null = null;
    if (this.isPunct('(') && this.binderFollows(1)) {
      this.next();
      q = this.parseQuantifier(')');
    }
    const out = [{ k: 'display' as const, q, e: this.parseExpr(), pos }];
    while (this.acceptPunct(',')) out.push({ k: 'display', q, e: this.parseExpr(), pos });
    this.expectPunct(';');
    return out;
  }

  private parseCBlock(): CStmt[] {
    if (this.acceptPunct('{')) {
      const body: CStmt[] = [];
      while (!this.acceptPunct('}')) {
        if (this.acceptPunct(';')) continue;
        body.push(...this.parseCStmt());
      }
      this.acceptPunct(';');
      return body;
    }
    return this.parseCStmt();
  }

  private parseCStmt(): CStmt[] {
    const pos = this.pos;
    if (this.isIdent('forall') && this.isPunct('(', 1)) {
      this.next();
      this.next();
      const q = this.parseQuantifier(')');
      return [{ k: 'forall', q, body: this.parseCBlock(), pos }];
    }
    if (this.isIdent('if') && this.isPunct('(', 1)) {
      this.next();
      this.next();
      const c = this.parseExpr();
      this.expectPunct(')');
      const then = this.parseCBlock();
      const els = this.acceptIdent('else') ? this.parseCBlock() : [];
      return [{ k: 'if', c, then, else: els, pos }];
    }
    if (this.isPunct('{')) return this.parseCBlock();
    let label: Expr | null = null;
    let e = this.parseConstraintExpr();
    if (this.acceptPunct(':')) {
      label = e;
      // A label before forall or a block names every constraint inside it.
      if (((this.isIdent('forall') || this.isIdent('if')) && this.isPunct('(', 1)) || this.isPunct('{')) {
        const body = this.parseCStmt();
        return body.map((c) => applyLabel(c, label!));
      }
      e = this.parseConstraintExpr();
    }
    const level = this.isIdent() && FILTER_LEVELS.has(this.peek().text) ? this.next().text : undefined;
    // OPL 3 accepts a missing ';' before the closing brace of a block.
    if (!this.isPunct('}')) this.expectPunct(';');
    return [{ k: 'constraint', label, e, level, pos }];
  }

  /** An expression, or a scheduling constraint written infix (`a precedes b`, `a requires(2) r`). */
  private parseConstraintExpr(): Expr {
    const e = this.parseExpr();
    if (!this.isIdent() || !INFIX_CONSTRAINTS.has(this.peek().text)) return e;
    const op = this.next();
    let amount: Expr | null = null;
    if (op.text !== 'precedes' && this.isPunct('(')) {
      this.next();
      amount = this.parseExpr();
      this.expectPunct(')');
    }
    const other = this.parseExpr();
    return { k: 'call', fn: op.text, args: amount ? [e, other, amount] : [e, other], pos: op.pos };
  }

  // ------------------------------------------------------------ search procedures

  private parseSBlock(): SStmt[] {
    if (this.acceptPunct('{')) {
      const body: SStmt[] = [];
      while (!this.acceptPunct('}')) {
        if (this.acceptPunct(';')) continue;
        body.push(...this.parseSStmt());
      }
      this.acceptPunct(';');
      return body;
    }
    return this.parseSStmt();
  }

  /** Statements up to (not including) one of the given keywords. */
  private parseSUntil(stop: string[]): SStmt[] {
    const body: SStmt[] = [];
    while (!(this.isIdent() && stop.includes(this.peek().text))) {
      if (this.atEnd()) this.unexpected(`'${stop[stop.length - 1]}'`);
      if (this.acceptPunct(';')) continue;
      body.push(...this.parseSStmt());
    }
    return body;
  }

  private parseSStmt(): SStmt[] {
    const t = this.peek();
    const pos = t.pos;
    if (this.isPunct('{')) return this.parseSBlock();
    if (t.kind === 'ident') {
      switch (t.text) {
        case 'forall':
        case 'tryall':
        case 'select':
          if (this.isPunct('(', 1)) {
            this.next();
            this.next();
            const q = this.parseQuantifier(')');
            return [{ k: t.text, q, body: this.parseSBlock(), pos }];
          }
          break;
        case 'try': {
          this.next();
          const alts: SStmt[][] = [];
          do {
            alts.push(this.parseAlternative());
          } while (this.acceptPunct('|'));
          this.expectIdent('endtry');
          this.acceptPunct(';');
          return [{ k: 'try', alts, pos }];
        }
        case 'if': {
          this.next();
          const c = this.parseExpr();
          if (this.acceptIdent('then')) {
            const then = this.parseSUntil(['else', 'endif']);
            const els = this.acceptIdent('else') ? this.parseSUntil(['endif']) : [];
            this.expectIdent('endif');
            this.acceptPunct(';');
            return [{ k: 'if', c, then, else: els, pos }];
          }
          const then = this.parseSBlock();
          const els = this.acceptIdent('else') ? this.parseSBlock() : [];
          return [{ k: 'if', c, then, else: els, pos }];
        }
        case 'while': {
          this.next();
          const c = this.parseExpr();
          this.acceptIdent('do');
          return [{ k: 'while', c, body: this.parseSBlock(), pos }];
        }
      }
      if (STRATEGIES.has(t.text)) {
        this.next();
        const args = this.acceptPunct('(') ? this.parseArgs(')') : [];
        return [{ k: 'strategy', name: t.text, args, body: this.parseSBlock(), pos }];
      }
    }
    const e = this.parseConstraintExpr();
    if (!this.isPunct('}')) this.expectPunct(';');
    return [{ k: 'post', e, pos }];
  }

  /** One alternative of try ... | ... endtry. */
  private parseAlternative(): SStmt[] {
    const pos = this.pos;
    if (this.isPunct('{')) return this.parseSBlock();
    if (this.isIdent() && ['forall', 'tryall', 'select', 'try', 'if', 'while'].includes(this.peek().text)) return this.parseSStmt();
    const e = this.parseConstraintExpr();
    this.acceptPunct(';');
    return [{ k: 'post', e, pos }];
  }

  // ------------------------------------------------------------ data files

  parseData(file: string): DataAst {
    const entries: DataAst['entries'] = [];
    const connections: NonNullable<DataAst['connections']> = [];
    const writes: NonNullable<DataAst['writes']> = [];
    while (!this.atEnd()) {
      if (this.acceptPunct(';')) continue;
      const t = this.expectIdent();
      if (t.text === 'prepare' && this.peek().kind === 'script') {
        // prepare { ... } adjusts data sources with a script; not needed here.
        this.next();
        continue;
      }
      if (/^(SheetConnection|DBConnection|DBconnection)$/.test(t.text)) {
        const name = this.expectIdent().text;
        this.expectPunct('(');
        const args = this.parseArgs(')');
        this.expectPunct(';');
        connections.push({ kind: t.text === 'SheetConnection' ? 'sheet' : 'db', name, args, pos: t.pos });
        continue;
      }
      if (this.acceptIdent('from')) {
        entries.push({ name: t.text, value: this.parsePostfixExpr(), pos: t.pos });
      } else if (this.acceptIdent('to')) {
        writes.push({ name: t.text, call: this.parsePostfixExpr(), pos: t.pos });
      } else {
        this.expectPunct('=');
        entries.push({ name: t.text, value: this.parseDataValue(), pos: t.pos });
      }
      if (!this.atEnd()) this.expectPunct(';');
    }
    return { file, entries, connections, writes };
  }

  /** A call such as SheetRead(conn, "A1:B2"). */
  private parsePostfixExpr(): Expr {
    return this.parsePostfix();
  }

  parseDataValue(): Expr {
    const t = this.peek();
    const pos = t.pos;
    if ((t.kind === 'punct' && (t.text === '-' || t.text === '+')) &&
        (this.peek(1).kind === 'int' || this.peek(1).kind === 'float' || this.isIdent('infinity', 1) || this.isIdent('maxint', 1))) {
      this.next();
      const v = this.parseDataValue();
      if (v.k !== 'num') fail('expected a number', pos);
      return t.text === '-' ? { ...v, value: -v.value, pos } : v;
    }
    if (t.kind === 'int' || t.kind === 'float') {
      this.next();
      return { k: 'num', value: t.value as number, isInt: t.kind === 'int', pos };
    }
    if (t.kind === 'string') {
      this.next();
      return { k: 'str', value: t.value as string, pos };
    }
    if (t.kind === 'ident') {
      this.next();
      if (t.text === 'maxint') return { k: 'num', value: 2147483647, isInt: true, pos };
      if (t.text === 'infinity') return { k: 'num', value: Infinity, isInt: false, pos };
      return { k: 'sym', name: t.text, pos };
    }
    const value = () => this.parseDataValue();
    if (this.acceptPunct('{')) {
      const items: Expr[] = [];
      this.parseItems(items, '}', value);
      return { k: 'setLit', items, pos };
    }
    if (this.acceptPunct('[')) {
      const items: Expr[] = [];
      this.parseItems(items, ']', value);
      return { k: 'arrayLit', items, pos };
    }
    if (this.acceptPunct('#[')) return { k: 'indexedLit', entries: this.parseIndexedEntries(value, value), pos };
    if (this.acceptPunct('<')) {
      const items: Expr[] = [];
      this.parseItems(items, '>', value);
      return { k: 'tuple', items, pos };
    }
    if (this.acceptPunct('#<')) return { k: 'namedTuple', fields: this.parseNamedFields(value), pos };
    this.unexpected('a data value');
  }

  // ------------------------------------------------------------ OPLScript

  parseScript(file: string): ScriptAst {
    const stmts: ScriptStmt[] = [];
    while (!this.atEnd()) {
      if (this.acceptPunct(';')) continue;
      stmts.push(...this.parseScriptStmt());
    }
    return { file, stmts };
  }

  private parseScriptBlock(): ScriptStmt[] {
    if (this.acceptPunct('{')) {
      const body: ScriptStmt[] = [];
      while (!this.acceptPunct('}')) {
        if (this.acceptPunct(';')) continue;
        body.push(...this.parseScriptStmt());
      }
      return body;
    }
    return this.parseScriptStmt();
  }

  private parseScriptStmt(): ScriptStmt[] {
    const t = this.peek();
    const pos = t.pos;
    if (this.isPunct('{')) return this.parseScriptBlock();
    if (t.kind === 'ident') {
      switch (t.text) {
        case 'Model': {
          this.next();
          const name = this.expectIdent().text;
          this.expectPunct('(');
          const files = [this.expectString()];
          while (this.acceptPunct(',')) files.push(this.expectString());
          this.expectPunct(')');
          const editMode = this.acceptIdent('editMode');
          this.expectPunct(';');
          return [{ k: 'model', name, files, editMode, pos }];
        }
        case 'import': {
          this.next();
          const kind = this.isIdent('enum') ? this.next().text : 'data';
          const name = this.expectIdent().text;
          const from = this.parseExpr();
          this.expectPunct(';');
          return [{ k: 'import', kind, name, from, pos }];
        }
        case 'enum': {
          this.next();
          const name = this.expectIdent().text;
          this.acceptPunct('=');
          const values = this.parseEnumValues();
          this.expectPunct(';');
          return [{ k: 'enum', name, values, pos }];
        }
        case 'Basis':
        case 'Solution':
        case 'MipStart': {
          this.next();
          const name = this.expectIdent().text;
          const args = this.acceptPunct('(') ? this.parseArgs(')') : [];
          this.expectPunct(';');
          return [{ k: 'object', type: t.text, name, args, pos }];
        }
        case 'ofile': {
          this.next();
          const name = this.expectIdent().text;
          this.expectPunct('(');
          const path = this.parseExpr();
          this.expectPunct(')');
          this.expectPunct(';');
          return [{ k: 'ofile', name, path, pos }];
        }
        case 'range': {
          this.next();
          const name = this.expectIdent().text;
          const e = this.parseRangeBody();
          this.expectPunct(';');
          return [{ k: 'range', name, e, pos }];
        }
        case 'forall':
          if (this.isPunct('(', 1)) {
            this.next();
            this.next();
            const q = this.parseQuantifier(')');
            return [{ k: 'forall', q, body: this.parseScriptBlock(), pos }];
          }
          break;
        case 'while': {
          this.next();
          const c = this.parseExpr();
          this.acceptIdent('do');
          return [{ k: 'while', c, body: this.parseScriptBlock(), pos }];
        }
        case 'repeat': {
          this.next();
          const body: ScriptStmt[] = [];
          while (!this.isIdent('until')) {
            if (this.atEnd()) this.unexpected("'until'");
            if (this.acceptPunct(';')) continue;
            body.push(...this.parseScriptStmt());
          }
          this.next();
          const c = this.parseExpr();
          this.expectPunct(';');
          return [{ k: 'repeat', body, c, pos }];
        }
        case 'if': {
          this.next();
          const c = this.parseExpr();
          this.acceptIdent('then');
          const then = this.parseScriptBlock();
          const els = this.acceptIdent('else') ? this.parseScriptBlock() : [];
          return [{ k: 'if', c, then, else: els, pos }];
        }
        case 'display':
          this.next();
          return this.parseDisplay(pos);
      }
    }
    if (this.isTypeStart()) {
      const type = this.parseType();
      const out: ScriptStmt[] = [];
      do {
        const dpos = this.pos;
        const name = this.expectIdent().text;
        const dims = this.parseDims();
        let init: Expr | null = null;
        if (this.acceptPunct(':=') || this.acceptPunct('=')) init = this.parseExpr();
        out.push({ k: 'decl', type, name, dims, init, pos: dpos });
      } while (this.acceptPunct(','));
      this.expectPunct(';');
      return out;
    }
    const e = this.parseExpr();
    if (this.acceptPunct(':=')) {
      const value = this.parseExpr();
      this.expectPunct(';');
      return [{ k: 'assign', target: e, e: value, pos }];
    }
    if (this.isPunct('<<')) {
      const items: (Expr | 'endl')[] = [];
      while (this.acceptPunct('<<')) {
        if (this.acceptIdent('endl')) items.push('endl');
        else items.push(this.parseExpr());
      }
      this.expectPunct(';');
      return [{ k: 'output', target: e, items, pos }];
    }
    this.expectPunct(';');
    return [{ k: 'expr', e, pos }];
  }
}

function applyLabel(c: CStmt, label: Expr): CStmt {
  if (c.k === 'forall') return { ...c, label: c.label ?? label };
  if (c.k === 'constraint') return { ...c, label: c.label ?? label };
  return { ...c, then: c.then.map((x) => applyLabel(x, label)), else: c.else.map((x) => applyLabel(x, label)) };
}

export function parseModel(src: string, file: string): ModelAst {
  return new Parser(tokenize(src, file)).parseModel(file);
}

export function parseData(src: string, file: string): DataAst {
  return new Parser(tokenize(src, file)).parseData(file);
}

/** Parses a single data value (used by `int a[...] < "file";`). */
export function parseDataValue(src: string, file: string): Expr {
  const p = new Parser(tokenize(src, file));
  const v = p.parseDataValue();
  p.acceptPunct(';');
  if (!p.atEnd()) p.unexpected('end of file');
  return v;
}

export function parseScript(src: string, file: string): ScriptAst {
  return new Parser(tokenize(src, file)).parseScript(file);
}
