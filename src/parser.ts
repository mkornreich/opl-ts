/**
 * Recursive-descent parser for OPL 3.x models, data files and OPLScript.
 */

import type {
  Binder, CStmt, DataAst, DataInit, Dim, Expr, FieldDecl, ModelAst, Quantifier,
  ScriptAst, ScriptStmt, Stmt, TypeExpr,
} from './ast.js';
import { fail, type SourcePos } from './errors.js';
import { tokenize, type Token } from './lexer.js';

const COMPARISON = new Set(['=', '==', '!=', '<>', '<', '<=', '>', '>=']);
const AGGREGATES = new Set(['sum', 'prod', 'min', 'max', 'or', 'and']);

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
    const c = this.parseOr();
    if (this.isPunct('?')) {
      const pos = this.next().pos;
      const a = this.parseExpr();
      this.expectPunct(':');
      const b = this.parseExpr();
      return { k: 'cond', c, a, b, pos };
    }
    return c;
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
    const first = this.parseRange();
    const ops: string[] = [];
    const exprs: Expr[] = [first];
    for (;;) {
      const t = this.peek();
      let op: string | null = null;
      if (t.kind === 'punct' && COMPARISON.has(t.text)) op = t.text;
      else if (this.isIdent('in')) op = 'in';
      else if (this.isIdent('not') && this.isIdent('in', 1)) op = 'not in';
      if (!op) break;
      this.next();
      if (op === 'not in') this.next();
      ops.push(op === '==' ? '=' : op === '<>' ? '!=' : op);
      exprs.push(this.parseRange());
    }
    if (ops.length === 0) return first;
    if (ops.length === 1) return { k: 'bin', op: ops[0], l: exprs[0], r: exprs[1], pos: first.pos };
    return { k: 'chain', ops, exprs, pos: first.pos };
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

  private parseAdd(): Expr {
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

  private parseUnary(): Expr {
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

  private parsePostfix(): Expr {
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
      if (AGGREGATES.has(t.text) && this.isPunct('(', 1) &&
          (t.text === 'sum' || t.text === 'prod' || this.binderFollows(2))) {
        this.next();
        this.next();
        const q = this.parseQuantifier(')');
        const body = this.parseMul();
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
      const items: Expr[] = [];
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
      if (this.acceptPunct('<')) {
        pattern = true;
        names.push(this.expectIdent().text);
        while (this.acceptPunct(',')) names.push(this.expectIdent().text);
        this.expectPunct('>');
      } else {
        names.push(this.expectIdent().text);
        while (this.acceptPunct(',')) names.push(this.expectIdent().text);
      }
      this.expectIdent('in');
      const domain = this.parseRange();
      const binder: Binder = { names, pattern, domain, pos: bpos };
      if (this.acceptPunct(':')) binder.filter = this.parseExpr();
      binders.push(binder);
      if (this.acceptPunct(',')) continue;
      this.expectPunct(close);
      return { binders, pos };
    }
  }

  // ------------------------------------------------------------ declarations

  isTypeStart(): boolean {
    const t = this.peek();
    if (t.kind === 'punct') return t.text === '{';
    if (t.kind !== 'ident') return false;
    if (['int', 'float', 'string', 'setof'].includes(t.text)) return true;
    // `Name name` is a declaration with a user-defined type.
    return this.peek(1).kind === 'ident' && !['in', 'to', 'not'].includes(this.peek(1).text);
  }

  parseType(): TypeExpr {
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
            const type = this.parseType();
            const fname = this.expectIdent().text;
            const dims = this.parseDims();
            this.expectPunct(';');
            fields.push({ type, name: fname, dims, pos: fpos });
          }
          this.acceptPunct(';');
          return [{ k: 'struct', name, fields, pos }];
        }
        case 'var':
        case 'dvar': {
          this.next();
          const type = this.parseType();
          const out: Stmt[] = [];
          do {
            const vpos = this.pos;
            const name = this.expectIdent().text;
            const dims = this.parseDims();
            const domain = this.acceptIdent('in') ? this.parseRange() : null;
            out.push({ k: 'var', type, name, dims, domain, pos: vpos });
          } while (this.acceptPunct(','));
          this.expectPunct(';');
          return out;
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
    if (!this.isTypeStart()) this.unexpected('a declaration or statement');
    return [this.parseDataDecl()];
  }

  private parseDataDecl(): Stmt {
    const pos = this.pos;
    const type = this.parseType();
    const name = this.expectIdent().text;
    const dims = this.parseDims();
    let init: DataInit | null = null;
    if (this.acceptPunct('=')) {
      init = this.acceptPunct('...') ? { k: 'external' } : { k: 'expr', e: this.parseExpr() };
    } else if (this.acceptIdent('from')) {
      this.expectIdent('SheetRead');
      this.expectPunct('(');
      const conn = this.expectIdent().text;
      this.expectPunct(',');
      const range = this.parseExpr();
      this.expectPunct(')');
      init = { k: 'sheet', conn, range };
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
    let e = this.parseExpr();
    if (this.acceptPunct(':')) {
      label = e;
      e = this.parseExpr();
    }
    // OPL 3 accepts a missing ';' before the closing brace of a block.
    if (!this.isPunct('}')) this.expectPunct(';');
    return [{ k: 'constraint', label, e, pos }];
  }

  // ------------------------------------------------------------ data files

  parseData(file: string): DataAst {
    const entries: DataAst['entries'] = [];
    while (!this.atEnd()) {
      if (this.acceptPunct(';')) continue;
      const t = this.expectIdent();
      this.expectPunct('=');
      entries.push({ name: t.text, value: this.parseDataValue(), pos: t.pos });
      if (!this.atEnd()) this.expectPunct(';');
    }
    return { file, entries };
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
