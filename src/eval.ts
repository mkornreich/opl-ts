/**
 * Expression evaluation, static typing (for formatting), quantifier iteration
 * and shaping of literal data into declared types.
 */

import type { Binder, Dim, Expr, Quantifier, TypeExpr } from './ast.js';
import { fail, type SourcePos } from './errors.js';
import { ConstraintRef, DVar, isLinear, LinExpr, linAdd, linMul, type Linear } from './linear.js';
import {
  arrayType, asIndexSet, elementsOf, elementType, EnumType, FLOAT, formatValue, INT, indexType,
  isIntType, isNumericType, keyOf, NamedTuple, OplArray, OplRange, OplSet, OplTuple, RawArray,
  RawIndexed, STRING, StructType, typeName, UNKNOWN, valuesEqual,
  type Binding, type HostObject, type IndexSet, type Type, type Value,
} from './values.js';

export const MAXINT = 2147483647;

/**
 * 'data': decision variables may not appear.
 * 'model': decision variables build linear expressions (objective, constraints).
 * 'post': decision variables evaluate to their solution values.
 */
export type Phase = 'data' | 'model' | 'post';

export class Scope {
  private readonly vars = new Map<string, Binding>();
  /** Consulted when a name is not bound anywhere in the scope chain. */
  fallback: ((name: string) => Binding | undefined) | null = null;
  constructor(readonly parent: Scope | null = null) {}

  lookup(name: string): Binding | undefined {
    let s: Scope | null = this;
    for (; s; s = s.parent) {
      const b = s.vars.get(name);
      if (b) return b;
      if (!s.parent) return s.fallback?.(name);
    }
    return undefined;
  }

  define(name: string, b: Binding): void {
    this.vars.set(name, b);
  }
}

function isHost(v: Value): v is HostObject {
  return typeof v === 'object' && v !== null && 'hostKind' in v;
}

export class Evaluator {
  phase: Phase = 'data';
  readonly structs = new Map<string, StructType>();
  private readonly expanded = new WeakMap<Quantifier, Binder[]>();

  // ------------------------------------------------------------ evaluation

  /** Evaluates e; in the post phase decision variables become their values. */
  eval(e: Expr, s: Scope): Value {
    const v = this.evalRef(e, s);
    if (v instanceof DVar) {
      if (this.phase === 'post') return v.value;
      if (this.phase === 'data') fail(`decision variable ${v.name} used in data`, e.pos);
    }
    return v;
  }

  num(e: Expr, s: Scope): number {
    const v = this.eval(e, s);
    if (typeof v !== 'number') fail(`expected a number, found a ${typeName(v)}`, e.pos);
    return v;
  }

  truthy(e: Expr, s: Scope): boolean {
    const v = this.eval(e, s);
    if (typeof v !== 'number') {
      if (isLinear(v)) fail('decision variables cannot appear in a condition', e.pos);
      fail(`expected a condition, found a ${typeName(v)}`, e.pos);
    }
    return v !== 0;
  }

  /** Like eval, but keeps decision variables and constraints as references. */
  evalRef(e: Expr, s: Scope): Value {
    switch (e.k) {
      case 'num':
      case 'str':
        return e.value;
      case 'sym':
        return e.name;
      case 'id': {
        const b = s.lookup(e.name);
        if (b) return b.value;
        if (e.name === 'maxint') return MAXINT;
        if (e.name === 'infinity') return Infinity;
        fail(`unknown identifier '${e.name}'`, e.pos);
      }
      // falls through (unreachable)
      case 'index': {
        let target = this.evalRef(e.target, s);
        for (const a of e.args) target = this.indexInto(target, this.eval(a, s), a.pos);
        return target;
      }
      case 'field':
        return this.field(this.evalRef(e.target, s), e.name, e.pos);
      case 'call':
        return this.call(e.fn, e.args, s, e.pos);
      case 'method':
        return this.method(e, s).value;
      case 'unary': {
        if (e.op === '!') return this.truthy(e.e, s) ? 0 : 1;
        const v = this.eval(e.e, s);
        if (e.op === '+') return v;
        if (typeof v === 'number') return -v;
        if (isLinear(v)) return linMul(v, -1, e.pos);
        fail(`cannot negate a ${typeName(v)}`, e.pos);
      }
      // falls through (unreachable)
      case 'bin':
        return this.binary(e.op, e.l, e.r, s, e.pos);
      case 'chain': {
        for (let i = 0; i < e.ops.length; i++) {
          const l = this.eval(e.exprs[i], s);
          const r = this.eval(e.exprs[i + 1], s);
          if (!this.compare(e.ops[i], l, r, e.pos)) return 0;
        }
        return 1;
      }
      case 'agg':
        return this.aggregate(e.op, e.q, e.body, s, e.pos);
      case 'range': {
        const lo = this.num(e.lo, s);
        const hi = this.num(e.hi, s);
        if (!Number.isInteger(lo) || !Number.isInteger(hi)) fail('range bounds must be integers', e.pos);
        return new OplRange(lo, hi);
      }
      case 'setLit':
        return new OplSet(e.items.map((x) => this.eval(x, s)));
      case 'setComp': {
        const out = new OplSet();
        this.forEach(e.q, s, (sc) => out.add(this.eval(e.head, sc)));
        const t = this.typeOf(e, s);
        out.elemType = t.k === 'set' ? t.of : null;
        return out;
      }
      case 'arrayLit':
        return new RawArray(e.items.map((x) => this.eval(x, s)));
      case 'indexedLit':
        return new RawIndexed(e.entries.map((en) => [this.eval(en.key, s), this.eval(en.value, s)]));
      case 'tuple':
        return new OplTuple(null, e.items.map((x) => this.eval(x, s)));
      case 'namedTuple':
        return new NamedTuple(new Map(e.fields.map((f) => [f.name, this.eval(f.value, s)])));
      case 'cond':
        return this.truthy(e.c, s) ? this.evalRef(e.a, s) : this.evalRef(e.b, s);
    }
  }

  /** Evaluates e and returns its value with its type (method calls report their own type). */
  evalTyped(e: Expr, s: Scope): Binding {
    if (e.k === 'method') {
      const r = this.method(e, s);
      return r.value instanceof DVar && this.phase === 'post' ? { value: r.value.value, type: r.type } : r;
    }
    return { value: this.eval(e, s), type: this.typeOf(e, s) };
  }

  indexInto(target: Value, key: Value, pos: SourcePos): Value {
    if (key instanceof DVar || key instanceof LinExpr) fail('decision variables cannot be used as indices', pos);
    if (!(target instanceof OplArray)) fail(`cannot index a ${typeName(target)}`, pos);
    const i = target.index.indexOf(key);
    if (i < 0) fail(`index ${formatValue(key, UNKNOWN, 'display')} is out of bounds`, pos);
    return target.items[i];
  }

  private field(target: Value, name: string, pos: SourcePos): Value {
    if (target instanceof OplTuple) {
      const i = target.struct?.index.get(name);
      if (i === undefined) fail(`tuple has no field '${name}'`, pos);
      return target.values[i];
    }
    if (target instanceof NamedTuple) {
      if (!target.fields.has(name)) fail(`tuple has no field '${name}'`, pos);
      return target.fields.get(name)!;
    }
    if (target instanceof DVar) {
      if (name === 'lb') return target.lb;
      if (name === 'ub') return target.ub;
      this.requireSolution(target.value, pos);
      switch (name) {
        case 'rc':
        case 'reducedCost':
          return target.rc;
        case 'value':
        case 'sol':
          return target.value;
      }
      fail(`decision variables have no field '${name}' (use rc, lb or ub)`, pos);
    }
    if (target instanceof ConstraintRef) {
      this.requireSolution(target.dual, pos);
      switch (name) {
        case 'dual':
          return target.dual;
        case 'slack':
          return target.slack;
        case 'value':
          return target.activity;
      }
      fail(`constraints have no field '${name}' (use dual or slack)`, pos);
    }
    if (isHost(target) && target.getField) {
      const b = target.getField(name);
      if (b) return b.value;
      fail(`${target.hostKind} has no member '${name}'`, pos);
    }
    fail(`a ${typeName(target)} has no field '${name}'`, pos);
  }

  private requireSolution(v: number, pos: SourcePos): void {
    if (this.phase !== 'post' || Number.isNaN(v)) fail('solution values are only available after solving', pos);
  }

  private method(e: Extract<Expr, { k: 'method' }>, s: Scope): Binding {
    const target = this.evalRef(e.target, s);
    if (isHost(target) && target.callMethod) {
      return target.callMethod(e.name, e.args.map((a) => this.eval(a, s)));
    }
    fail(`a ${typeName(target)} has no method '${e.name}'`, e.pos);
  }

  private binary(op: string, le: Expr, re: Expr, s: Scope, pos: SourcePos): Value {
    if (op === '&&') return this.truthy(le, s) && this.truthy(re, s) ? 1 : 0;
    if (op === '||') return this.truthy(le, s) || this.truthy(re, s) ? 1 : 0;
    const l = this.eval(le, s);
    const r = this.eval(re, s);
    switch (op) {
      case '+':
      case '-':
        if (typeof l === 'number' && typeof r === 'number') return op === '+' ? l + r : l - r;
        if (op === '+' && (typeof l === 'string' || typeof r === 'string')) {
          return formatValue(l, UNKNOWN, 'stream') + formatValue(r, UNKNOWN, 'stream');
        }
        return linAdd(this.linear(l, le.pos), this.linear(r, re.pos), op === '+' ? 1 : -1);
      case '*':
        return linMul(this.linear(l, le.pos), this.linear(r, re.pos), pos);
      case '/': {
        if (typeof r !== 'number') fail('division by a non-constant expression', pos);
        if (r === 0) fail('division by zero', pos);
        if (typeof l === 'number') return l / r;
        return linMul(this.linear(l, le.pos), 1 / r, pos);
      }
      case 'div':
      case 'mod': {
        if (typeof l !== 'number' || typeof r !== 'number') fail(`'${op}' needs numbers`, pos);
        if (r === 0) fail('division by zero', pos);
        return op === 'div' ? Math.trunc(l / r) : l % r;
      }
      case '^':
        if (typeof l !== 'number' || typeof r !== 'number') fail("'^' needs numbers", pos);
        return Math.pow(l, r);
      case 'union':
      case 'inter':
      case 'diff':
      case 'symdiff':
        return setOp(op, l, r, pos);
      case 'in':
      case 'not in': {
        const set = asIndexSet(r);
        if (!set) fail(`'in' needs a set, found a ${typeName(r)}`, pos);
        const member = set.indexOf(l) >= 0;
        return member === (op === 'in') ? 1 : 0;
      }
      default:
        return this.compare(op, l, r, pos) ? 1 : 0;
    }
  }

  private compare(op: string, l: Value, r: Value, pos: SourcePos): boolean {
    if (isLinear(l) || isLinear(r)) fail('decision variables cannot appear in a condition', pos);
    switch (op) {
      case '=':
        return valuesEqual(l, r);
      case '!=':
        return !valuesEqual(l, r);
    }
    if (!((typeof l === 'number' && typeof r === 'number') || (typeof l === 'string' && typeof r === 'string'))) {
      fail(`cannot compare a ${typeName(l)} with a ${typeName(r)}`, pos);
    }
    switch (op) {
      case '<':
        return l < r;
      case '<=':
        return l <= r;
      case '>':
        return l > r;
      case '>=':
        return l >= r;
    }
    fail(`unknown operator '${op}'`, pos);
  }

  linear(v: Value, pos: SourcePos): Linear {
    if (typeof v === 'number' || v instanceof DVar || v instanceof LinExpr) return v;
    fail(`expected a numeric expression, found a ${typeName(v)}`, pos);
  }

  private aggregate(op: string, q: Quantifier, body: Expr, s: Scope, pos: SourcePos): Value {
    switch (op) {
      case 'sum': {
        let constant = 0;
        let acc: LinExpr | null = null;
        this.forEach(q, s, (sc) => {
          const v = this.eval(body, sc);
          if (typeof v === 'number') constant += v;
          else (acc ??= new LinExpr()).addScaled(this.linear(v, body.pos), 1);
        });
        return acc ? (acc as LinExpr).addScaled(constant, 1) : constant;
      }
      case 'prod': {
        let p = 1;
        this.forEach(q, s, (sc) => (p *= this.num(body, sc)));
        return p;
      }
      case 'min':
      case 'max': {
        let m = op === 'min' ? Infinity : -Infinity;
        this.forEach(q, s, (sc) => {
          const v = this.num(body, sc);
          m = op === 'min' ? Math.min(m, v) : Math.max(m, v);
        });
        return m;
      }
      case 'and':
      case 'or': {
        let r = op === 'and';
        this.forEach(q, s, (sc) => {
          const v = this.truthy(body, sc);
          r = op === 'and' ? r && v : r || v;
        });
        return r ? 1 : 0;
      }
    }
    fail(`unknown aggregate '${op}'`, pos);
  }

  private call(fn: string, argExprs: Expr[], s: Scope, pos: SourcePos): Value {
    const args = argExprs.map((a) => this.eval(a, s));
    const numArg = (i: number): number => {
      const v = args[i];
      if (typeof v !== 'number') fail(`${fn}: argument ${i + 1} must be a number`, pos);
      return v;
    };
    const setArg = (i: number): IndexSet => {
      const v = args[i];
      const set = v === undefined ? null : asIndexSet(v);
      if (!set) fail(`${fn}: argument ${i + 1} must be a set`, pos);
      return set;
    };
    const arity = (n: number) => {
      if (args.length !== n) fail(`${fn} expects ${n} argument(s)`, pos);
    };
    switch (fn) {
      case 'abs':
        arity(1);
        return Math.abs(numArg(0));
      case 'floor':
        arity(1);
        return Math.floor(numArg(0));
      case 'ceil':
        arity(1);
        return Math.ceil(numArg(0));
      case 'round':
        arity(1);
        return Math.round(numArg(0));
      case 'trunc':
      case 'ftoi':
        arity(1);
        return Math.trunc(numArg(0));
      case 'frac':
        arity(1);
        return numArg(0) - Math.trunc(numArg(0));
      case 'sqrt':
        arity(1);
        return Math.sqrt(numArg(0));
      case 'exp':
        arity(1);
        return Math.exp(numArg(0));
      case 'log':
      case 'ln':
        arity(1);
        return Math.log(numArg(0));
      case 'pow':
        arity(2);
        return Math.pow(numArg(0), numArg(1));
      case 'min':
      case 'max':
      case 'minl':
      case 'maxl': {
        if (args.length === 0) fail(`${fn} needs arguments`, pos);
        const nums = args.map((_, i) => numArg(i));
        return fn.startsWith('min') ? Math.min(...nums) : Math.max(...nums);
      }
      case 'card':
        arity(1);
        return setArg(0).size;
      case 'ord': {
        arity(2);
        const i = setArg(0).indexOf(args[1]);
        if (i < 0) fail('ord: value is not in the set', pos);
        return i;
      }
      case 'first':
      case 'last': {
        arity(1);
        const set = setArg(0);
        if (set.size === 0) fail(`${fn}: empty set`, pos);
        return set.at(fn === 'first' ? 0 : set.size - 1);
      }
      case 'next':
      case 'prev':
      case 'nextc':
      case 'prevc': {
        arity(2);
        const set = setArg(0);
        const i = set.indexOf(args[1]);
        if (i < 0) fail(`${fn}: value is not in the set`, pos);
        const step = fn.startsWith('next') ? 1 : -1;
        let j = i + step;
        if (fn.endsWith('c')) j = (j + set.size) % set.size;
        else if (j < 0 || j >= set.size) fail(`${fn}: no ${step > 0 ? 'next' : 'previous'} element`, pos);
        return set.at(j);
      }
      case 'item': {
        arity(2);
        const set = setArg(0);
        const i = numArg(1);
        if (i < 0 || i >= set.size) fail('item: index out of bounds', pos);
        return set.at(i);
      }
    }
    fail(`unknown function '${fn}'`, pos);
  }

  // ------------------------------------------------------------ iteration

  private binders(q: Quantifier): Binder[] {
    let out = this.expanded.get(q);
    if (!out) {
      // `i, j in S` is `i in S, j in S`.
      out = q.binders.flatMap((b) =>
        b.pattern || b.names.length === 1
          ? [b]
          : b.names.map((n, i) => ({ ...b, names: [n], filter: i === b.names.length - 1 ? b.filter : undefined })),
      );
      this.expanded.set(q, out);
    }
    return out;
  }

  /** Calls fn once per assignment of the quantifier's iterators (in a child scope). */
  forEach(q: Quantifier, s: Scope, fn: (scope: Scope) => void): void {
    const binders = this.binders(q);
    const scope = new Scope(s);
    const run = (bi: number): void => {
      if (bi === binders.length) {
        fn(scope);
        return;
      }
      const b = binders[bi];
      const dv = this.eval(b.domain, scope);
      const elems = elementsOf(dv);
      if (!elems) fail(`cannot iterate over a ${typeName(dv)}`, b.domain.pos);
      const et = elementType(this.typeOf(b.domain, scope), dv);
      const slots: Binding[] = b.names.map((n, i) => {
        const slot: Binding = { value: 0, type: b.pattern ? tupleFieldType(et, i) : et };
        scope.define(n, slot);
        return slot;
      });
      for (const el of elems) {
        if (b.pattern) {
          if (!(el instanceof OplTuple) || el.values.length !== slots.length) {
            fail(`tuple pattern does not match ${formatValue(el, et, 'display')}`, b.pos);
          }
          slots.forEach((slot, i) => (slot.value = el.values[i]));
        } else {
          slots[0].value = el;
        }
        if (b.filter && !this.truthy(b.filter, scope)) continue;
        run(bi + 1);
      }
    };
    run(0);
  }

  /** A scope binding each iterator of q to a placeholder with its type (for typeOf). */
  private typeScope(q: Quantifier, s: Scope): Scope {
    const scope = new Scope(s);
    for (const b of this.binders(q)) {
      let dv: Value | undefined;
      let dt = this.typeOf(b.domain, scope);
      if (elementType(dt).k === 'unknown') {
        try {
          dv = this.eval(b.domain, scope);
        } catch {
          dv = undefined;
        }
        dt = elementType(dt, dv);
      } else {
        dt = elementType(dt);
      }
      b.names.forEach((n, i) => scope.define(n, { value: 0, type: b.pattern ? tupleFieldType(dt, i) : dt }));
    }
    return scope;
  }

  // ------------------------------------------------------------ types

  typeOf(e: Expr, s: Scope): Type {
    switch (e.k) {
      case 'num':
        return e.isInt ? INT : FLOAT;
      case 'str':
      case 'sym':
        return STRING;
      case 'id': {
        const b = s.lookup(e.name);
        if (b) return b.type.k === 'unknown' ? valueType(b.value) : b.type;
        if (e.name === 'maxint') return INT;
        if (e.name === 'infinity') return FLOAT;
        return UNKNOWN;
      }
      case 'index': {
        const t = this.typeOf(e.target, s);
        if (t.k === 'array') return indexType(t, e.args.length);
        return UNKNOWN;
      }
      case 'field': {
        const t = this.typeOf(e.target, s);
        if (t.k === 'struct') {
          const i = t.s.index.get(e.name);
          return i === undefined ? UNKNOWN : t.s.fields[i].type;
        }
        if (t.k === 'var') return e.name === 'value' || e.name === 'sol' ? { k: t.of } : FLOAT;
        if (t.k === 'constraint') return FLOAT;
        let target: Value | undefined;
        try {
          target = this.evalRef(e.target, s);
        } catch {
          return UNKNOWN;
        }
        if (isHost(target)) return target.getField?.(e.name)?.type ?? UNKNOWN;
        if (target instanceof OplTuple && target.struct) {
          const i = target.struct.index.get(e.name);
          return i === undefined ? UNKNOWN : target.struct.fields[i].type;
        }
        return UNKNOWN;
      }
      case 'call':
        switch (e.fn) {
          case 'abs':
            return e.args[0] ? this.typeOf(e.args[0], s) : UNKNOWN;
          case 'card':
          case 'ord':
          case 'floor':
          case 'ceil':
          case 'round':
          case 'trunc':
          case 'ftoi':
            return INT;
          case 'sqrt':
          case 'exp':
          case 'log':
          case 'ln':
          case 'frac':
          case 'pow':
            return FLOAT;
          case 'min':
          case 'max':
          case 'minl':
          case 'maxl':
            return e.args.map((a) => this.typeOf(a, s)).reduce(numJoin);
          case 'first':
          case 'last':
          case 'next':
          case 'prev':
          case 'nextc':
          case 'prevc':
          case 'item':
            return e.args[0] ? elementType(this.typeOf(e.args[0], s)) : UNKNOWN;
        }
        return UNKNOWN;
      case 'method':
        return UNKNOWN;
      case 'unary':
        return e.op === '!' ? INT : this.typeOf(e.e, s);
      case 'bin':
        switch (e.op) {
          case '+':
          case '-':
          case '*':
          case '^':
            return numJoin(this.typeOf(e.l, s), this.typeOf(e.r, s));
          case '/':
            return FLOAT;
          case 'div':
          case 'mod':
            return INT;
          case 'union':
          case 'inter':
          case 'diff':
          case 'symdiff':
            return this.typeOf(e.l, s);
        }
        return INT;
      case 'chain':
        return INT;
      case 'agg':
        if (e.op === 'and' || e.op === 'or') return INT;
        return this.typeOf(e.body, this.typeScope(e.q, s));
      case 'range':
        return { k: 'range' };
      case 'setLit':
        return { k: 'set', of: e.items.length ? this.typeOf(e.items[0], s) : UNKNOWN };
      case 'setComp':
        return { k: 'set', of: this.typeOf(e.head, this.typeScope(e.q, s)) };
      case 'tuple':
        return { k: 'tuple', items: e.items.map((x) => this.typeOf(x, s)) };
      case 'cond':
        return this.typeOf(e.a, s);
      case 'arrayLit':
      case 'indexedLit':
      case 'namedTuple':
        return UNKNOWN;
    }
  }

  resolveType(te: TypeExpr, s: Scope): Type {
    switch (te.k) {
      case 'int':
        return te.nonneg ? { k: 'int', nonneg: true } : INT;
      case 'float':
        return te.nonneg ? { k: 'float', nonneg: true } : FLOAT;
      case 'string':
        return STRING;
      case 'set':
        return { k: 'set', of: this.resolveType(te.of, s) };
      case 'named': {
        const st = this.structs.get(te.name);
        if (st) return { k: 'struct', s: st };
        const b = s.lookup(te.name);
        if (b?.type.k === 'enumType') return { k: 'enum', e: b.type.e };
        if (b?.type.k === 'range' && b.value instanceof OplRange) return { k: 'int', range: b.value };
        fail(`unknown type '${te.name}'`, te.pos);
      }
    }
  }

  indexSets(dims: Dim[], s: Scope): IndexSet[] {
    return dims.map((d) => {
      const v = this.eval(d.domain, s);
      const set = asIndexSet(v);
      if (!set) fail(`an array index must be a range, enum or set, found a ${typeName(v)}`, d.domain.pos);
      return set;
    });
  }

  /**
   * Builds a (possibly multi-dimensional) array, calling leaf for every cell
   * with named dimensions (`a[i in R]`) bound in its scope.
   */
  buildArray(dims: Dim[], sets: IndexSet[], s: Scope, leaf: (scope: Scope, path: Value[]) => Value): Value {
    const scope = new Scope(s);
    const slots = dims.map((d, k) => {
      if (!d.name) return null;
      const slot: Binding = { value: 0, type: elementType(UNKNOWN, sets[k] as Value) };
      scope.define(d.name, slot);
      return slot;
    });
    const path: Value[] = [];
    const rec = (k: number): Value => {
      if (k === sets.length) return leaf(scope, path);
      const set = sets[k];
      const items: Value[] = new Array(set.size);
      for (let i = 0; i < set.size; i++) {
        const key = set.at(i);
        const slot = slots[k];
        if (slot) slot.value = key;
        path.push(key);
        items[i] = rec(k + 1);
        path.pop();
      }
      return new OplArray(set, items);
    };
    return rec(0);
  }

  // ------------------------------------------------------------ shaping

  /** Converts a (literal) value into the declared type, validating it. */
  shape(v: Value, t: Type, pos: SourcePos): Value {
    switch (t.k) {
      case 'array': {
        const [first, ...rest] = t.dims;
        const inner = arrayType(t.of, rest);
        if (v instanceof RawArray || v instanceof OplArray) {
          if (v.items.length !== first.size) {
            fail(`expected ${first.size} array element(s), found ${v.items.length}`, pos);
          }
          return new OplArray(first, v.items.map((x) => this.shape(x, inner, pos)));
        }
        if (v instanceof RawIndexed) {
          const items: (Value | undefined)[] = new Array(first.size).fill(undefined);
          for (const [k, x] of v.entries) {
            const key = first instanceof EnumType ? this.shape(k, { k: 'enum', e: first }, pos) : k;
            const i = first.indexOf(key);
            if (i < 0) fail(`index ${formatValue(k, UNKNOWN, 'display')} is out of bounds`, pos);
            items[i] = this.shape(x, inner, pos);
          }
          const missing = items.findIndex((x) => x === undefined);
          if (missing >= 0) fail(`no value given for index ${formatValue(first.at(missing), UNKNOWN, 'display')}`, pos);
          return new OplArray(first, items as Value[]);
        }
        fail(`expected an array, found a ${typeName(v)}`, pos);
      }
      // falls through (unreachable)
      case 'set': {
        const elems = elementsOf(v);
        if (!elems || v instanceof EnumType) {
          if (v instanceof EnumType) return new OplSet(v.values, t.of);
          fail(`expected a set, found a ${typeName(v)}`, pos);
        }
        return new OplSet(elems.map((x) => this.shape(x, t.of, pos)), t.of);
      }
      case 'struct': {
        const fields = t.s.fields;
        if (v instanceof OplTuple) {
          if (v.values.length !== fields.length) {
            fail(`tuple ${t.s.name} has ${fields.length} field(s), found ${v.values.length} value(s)`, pos);
          }
          return new OplTuple(t.s, v.values.map((x, i) => this.shape(x, fields[i].type, pos)));
        }
        if (v instanceof NamedTuple) {
          return new OplTuple(t.s, fields.map((f) => {
            if (!v.fields.has(f.name)) fail(`missing field '${f.name}' of ${t.s.name}`, pos);
            return this.shape(v.fields.get(f.name)!, f.type, pos);
          }));
        }
        fail(`expected a ${t.s.name} tuple, found a ${typeName(v)}`, pos);
      }
      // falls through (unreachable)
      case 'int': {
        if (typeof v !== 'number') fail(`expected an int, found a ${typeName(v)}`, pos);
        if (!Number.isInteger(v) && Math.abs(v) !== Infinity) fail(`expected an int, found ${v}`, pos);
        if (t.nonneg && v < 0) fail(`expected a non-negative int, found ${v}`, pos);
        if (t.range && t.range.indexOf(v) < 0) fail(`${v} is not in ${t.range.lo}..${t.range.hi}`, pos);
        return v;
      }
      case 'float':
        if (typeof v !== 'number') fail(`expected a float, found a ${typeName(v)}`, pos);
        if (t.nonneg && v < 0) fail(`expected a non-negative float, found ${v}`, pos);
        return v;
      case 'string':
        if (typeof v !== 'string') fail(`expected a string, found a ${typeName(v)}`, pos);
        return v;
      case 'enum':
        if (typeof v !== 'string' || t.e.indexOf(v) < 0) {
          fail(`${formatValue(v, UNKNOWN, 'display')} is not a value of enum ${t.e.name}`, pos);
        }
        return v;
    }
    return v;
  }

  /** Fills a declared type from a flat list of cells (spreadsheet ranges). */
  shapeFlat(cells: Value[], t: Type, pos: SourcePos): Value {
    let i = 0;
    const take = (tt: Type): Value => {
      if (tt.k === 'array') {
        const [first, ...rest] = tt.dims;
        const inner = arrayType(tt.of, rest);
        const items: Value[] = [];
        for (let k = 0; k < first.size; k++) items.push(take(inner));
        return new OplArray(first, items);
      }
      if (tt.k === 'struct') return new OplTuple(tt.s, tt.s.fields.map((f) => take(f.type)));
      if (i >= cells.length) fail(`the sheet range has too few cells (${cells.length})`, pos);
      return this.shape(cells[i++], tt, pos);
    };
    if (t.k === 'set') {
      const out = new OplSet([], t.of);
      while (i < cells.length) out.add(take(t.of));
      return out;
    }
    const v = take(t);
    if (i !== cells.length) fail(`the sheet range has ${cells.length} cells, expected ${i}`, pos);
    return v;
  }

  defaultValue(t: Type): Value {
    switch (t.k) {
      case 'int':
        return t.range ? t.range.lo : 0;
      case 'float':
        return 0;
      case 'string':
        return '';
      case 'enum':
        return t.e.values[0] ?? '';
      case 'set':
        return new OplSet([], t.of);
      case 'struct':
        return new OplTuple(t.s, t.s.fields.map((f) => this.defaultValue(f.type)));
      case 'array': {
        const [first, ...rest] = t.dims;
        const inner = arrayType(t.of, rest);
        return new OplArray(first, Array.from({ length: first.size }, () => this.defaultValue(inner)));
      }
    }
    return 0;
  }
}

function tupleFieldType(t: Type, i: number): Type {
  if (t.k === 'struct') return t.s.fields[i]?.type ?? UNKNOWN;
  if (t.k === 'tuple') return t.items[i] ?? UNKNOWN;
  return UNKNOWN;
}

function numJoin(a: Type, b: Type): Type {
  if (a.k === 'string' || b.k === 'string') return STRING;
  if (isNumericType(a) && isNumericType(b)) return isIntType(a) && isIntType(b) ? INT : FLOAT;
  if ((a.k === 'float' || (a.k === 'var' && a.of === 'float')) || (b.k === 'float' || (b.k === 'var' && b.of === 'float'))) return FLOAT;
  return UNKNOWN;
}

/** Best-effort type of a runtime value (for bindings without a declared type). */
export function valueType(v: Value): Type {
  if (typeof v === 'number') return Number.isInteger(v) ? INT : FLOAT;
  if (typeof v === 'string') return STRING;
  if (v instanceof OplRange) return { k: 'range' };
  if (v instanceof EnumType) return { k: 'enumType', e: v };
  if (v instanceof OplSet) return { k: 'set', of: v.elemType ?? UNKNOWN };
  if (v instanceof OplTuple && v.struct) return { k: 'struct', s: v.struct };
  if (v instanceof DVar) return { k: 'var', of: v.isInt ? 'int' : 'float' };
  if (v instanceof ConstraintRef) return { k: 'constraint' };
  return UNKNOWN;
}

function setOp(op: string, l: Value, r: Value, pos: SourcePos): OplSet {
  const a = elementsOf(l);
  const b = elementsOf(r);
  if (!a || !b) fail(`'${op}' needs two sets`, pos);
  const inB = new Set(b.map(keyOf));
  const inA = new Set(a.map(keyOf));
  const et = l instanceof OplSet ? l.elemType : null;
  switch (op) {
    case 'union':
      return new OplSet([...a, ...b], et);
    case 'inter':
      return new OplSet(a.filter((x) => inB.has(keyOf(x))), et);
    case 'diff':
      return new OplSet(a.filter((x) => !inB.has(keyOf(x))), et);
    default:
      return new OplSet([...a.filter((x) => !inB.has(keyOf(x))), ...b.filter((x) => !inA.has(keyOf(x)))], et);
  }
}
