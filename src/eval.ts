/**
 * Expression evaluation, static typing (for formatting), quantifier iteration
 * and shaping of literal data into declared types.
 */

import type { Binder, Dim, Expr, Quantifier, TypeExpr } from './ast.js';
import { fail, type SourcePos } from './errors.js';
import { Activity, CPConstraint, Flattener, isIntegral, linBounds, Resource, type CmpOp, type CPCons, type CPHooks } from './cp/terms.js';
import { ConstraintRef, DVar, isLinear, LinExpr, linAdd, linMul, type Linear } from './linear.js';
import { checkMemory } from './solver/memory.js';
import {
  arrayType, asIndexSet, elementsOf, elementType, EnumType, FLOAT, formatValue, INT, indexType,
  isIntType, isNumericType, keyOf, NamedTuple, OplArray, OplRange, OplSet, OplTuple, RawArray,
  RawIndexed, STRING, StructType, typeName, UNKNOWN, valuesEqual,
  type Binding, type HostObject, type IndexSet, type Type, type Value,
} from './values.js';

export const MAXINT = 2147483647;

/**
 * 'data': decision variables may not appear.
 * 'model': decision variables build linear expressions and CP constraints.
 * 'search': like 'model', but bound variables evaluate to their values.
 * 'post': decision variables evaluate to their solution values.
 */
export type Phase = 'data' | 'model' | 'search' | 'post';

const CMP_OPS = new Set(['=', '!=', '<', '<=', '>', '>=']);

/** Value of a solved variable (enum variables give the enum value). */
export function dvarValue(v: DVar): number | string {
  if (v.enumType && !Number.isNaN(v.value)) return v.enumType.values[v.value];
  return v.value;
}

/** A cumul function (CP Optimizer): a sum of pulse(interval, height) terms. */
export class CumulExpr {
  constructor(readonly pulses: { act: Activity; height: Linear }[]) {}
}

/** A piecewise-linear function: slopes[k] applies before bps[k] (the last slope after the last breakpoint). */
export class PwlFunction {
  constructor(
    readonly slopes: number[],
    readonly bps: number[],
    readonly x0: number,
    readonly y0: number,
  ) {}

  slopeAt(x: number): number {
    let k = 0;
    while (k < this.bps.length && x >= this.bps[k]) k++;
    return this.slopes[k];
  }

  /** Integral of the slope from a to b. */
  private integral(a: number, b: number): number {
    if (b < a) return -this.integral(b, a);
    const cuts = [a, ...this.bps.filter((p) => p > a && p < b), b];
    let s = 0;
    for (let i = 0; i + 1 < cuts.length; i++) s += this.slopeAt((cuts[i] + cuts[i + 1]) / 2) * (cuts[i + 1] - cuts[i]);
    return s;
  }

  at(x: number): number {
    return this.y0 + this.integral(this.x0, x);
  }
}

/** predicate p(...) in S: calling p(x1, ..., xn) states <x1, ..., xn> in S. */
export class Predicate {
  constructor(
    readonly name: string,
    readonly arity: number,
    readonly set: OplSet,
  ) {}
}

/** a[x] where x is a variable and a has more dimensions: completed by the next index. */
export class VarIndexed {
  constructor(
    readonly target: OplArray,
    readonly key: Linear,
  ) {}
}

/** A named decision expression (dexpr): evaluated where it is used. */
export class DExpr {
  constructor(
    readonly name: string,
    readonly e: Expr,
    readonly scope: Scope,
  ) {}
}

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
  /** Model generation or live search: creates auxiliary variables for CP expressions. */
  cp: CPHooks | null = null;
  /** Selection variables of activities on alternative resources (for post-solve queries). */
  selections: Map<Activity, Map<Resource, DVar[]>> | null = null;
  /** Search-time queries such as isRanked(r) (set by the search engine). */
  searchFns: ((fn: string, args: Value[], pos: SourcePos) => Value | undefined) | null = null;
  private flatCache: { hooks: CPHooks; flat: Flattener } | null = null;

  private get cpPhase(): boolean {
    return this.phase === 'model' || this.phase === 'search';
  }

  private flat(pos: SourcePos): Flattener {
    const h = this.cp;
    if (!h || !this.cpPhase) fail('this expression over decision variables is only allowed in constraints', pos);
    if (this.flatCache?.hooks !== h) this.flatCache = { hooks: h, flat: new Flattener(h) };
    return this.flatCache.flat;
  }

  // ------------------------------------------------------------ evaluation

  /** Evaluates e; in the post phase decision variables become their values. */
  eval(e: Expr, s: Scope): Value {
    const v = this.evalRef(e, s);
    if (v instanceof DVar) {
      if (this.phase === 'post') return dvarValue(v);
      if (this.phase === 'search') {
        const d = this.cp?.domain(v);
        if (d && d.size === 1) return v.enumType ? v.enumType.values[d.min] : d.min;
      }
      if (this.phase === 'data') fail(`decision variable ${v.name} used in data`, e.pos);
    }
    return v;
  }

  /** A condition: a number, or (over decision variables) a CP constraint. */
  private cond(e: Expr, s: Scope): number | CPConstraint {
    const v = this.eval(e, s);
    if (typeof v === 'number' || v instanceof CPConstraint) return v;
    if (this.cpPhase && isLinear(v)) return new CPConstraint({ k: 'cmp', op: '!=', l: v, r: 0 });
    fail(`expected a condition, found a ${typeName(v)}`, e.pos);
  }

  num(e: Expr, s: Scope): number {
    const v = this.eval(e, s);
    if (typeof v !== 'number') fail(`expected a number, found a ${typeName(v)}`, e.pos);
    return v;
  }

  truthy(e: Expr, s: Scope): boolean {
    const v = this.eval(e, s);
    if (typeof v !== 'number') {
      if (isLinear(v) || v instanceof CPConstraint) {
        fail(this.phase === 'search'
          ? 'this condition depends on unbound variables (use bound, dmin, dmax or dsize)'
          : 'decision variables cannot appear in a condition', e.pos);
      }
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
        if (b) return b.value instanceof DExpr ? this.evalRef(b.value.e, b.value.scope) : b.value;
        if (e.name === 'maxint') return MAXINT;
        if (e.name === 'infinity') return Infinity;
        fail(`unknown identifier '${e.name}'`, e.pos);
      }
      // falls through (unreachable)
      case 'index': {
        let target = this.evalRef(e.target, s);
        for (const a of e.args) target = this.indexInto(target, this.eval(a, s), a.pos);
        return target instanceof DExpr ? this.evalRef(target.e, target.scope) : target;
      }
      case 'field':
        return this.field(this.evalRef(e.target, s), e.name, e.pos);
      case 'call':
        return this.call(e.fn, e.args, s, e.pos);
      case 'method':
        return this.method(e, s).value;
      case 'unary': {
        if (e.op === '!') {
          if (!this.cpPhase) return this.truthy(e.e, s) ? 0 : 1;
          const c = this.cond(e.e, s);
          return typeof c === 'number' ? (c ? 0 : 1) : new CPConstraint({ k: 'not', a: c.c });
        }
        const v = this.eval(e.e, s);
        if (e.op === '+') return v;
        if (typeof v === 'number') return -v;
        if (isLinear(v) || v instanceof CPConstraint) return linMul(this.linear(v, e.pos), -1, e.pos);
        fail(`cannot negate a ${typeName(v)}`, e.pos);
      }
      // falls through (unreachable)
      case 'bin':
        return this.binary(e.op, e.l, e.r, s, e.pos);
      case 'chain': {
        const vals = e.exprs.map((x) => this.eval(x, s));
        if (this.cpPhase && vals.some((v) => isLinear(v) || v instanceof CPConstraint)) {
          let c: CPCons | null = null;
          for (let i = 0; i < e.ops.length; i++) {
            const part = this.cmpCons(e.ops[i] as CmpOp, vals[i], vals[i + 1], e.pos).c;
            c = c ? { k: 'and', a: c, b: part } : part;
          }
          return new CPConstraint(c!);
        }
        for (let i = 0; i < e.ops.length; i++) {
          if (!this.compare(e.ops[i], vals[i], vals[i + 1], e.pos)) return 0;
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
      case 'arrayComp': {
        const entries: [Value, Value][] = [];
        const items: Value[] = [];
        this.forEach(e.q, s, (sc) => {
          if (e.key) entries.push([this.eval(e.key, sc), this.eval(e.value, sc)]);
          else items.push(this.eval(e.value, sc));
        });
        return e.key ? new RawIndexed(entries) : new RawArray(items);
      }
      case 'indexedLit':
        return new RawIndexed(e.entries.map((en) => [this.eval(en.key, s), this.eval(en.value, s)]));
      case 'tuple':
        return new OplTuple(null, e.items.map((x) => this.eval(x, s)));
      case 'namedTuple':
        return new NamedTuple(new Map(e.fields.map((f) => [f.name, this.eval(f.value, s)])));
      case 'cond':
        return this.truthy(e.c, s) ? this.evalRef(e.a, s) : this.evalRef(e.b, s);
      case 'piecewise': {
        const slopes: number[] = [];
        const bps: number[] = [];
        const add = (sc: Scope) => {
          for (const it of e.items) {
            slopes.push(this.num(it.slope, sc));
            bps.push(this.num(it.bp, sc));
          }
        };
        if (e.q) this.forEach(e.q, s, add);
        else add(s);
        slopes.push(this.num(e.last, s));
        const f = new PwlFunction(slopes, bps, e.origin ? this.num(e.origin[0], s) : 0, e.origin ? this.num(e.origin[1], s) : 0);
        return e.operand ? this.applyPwl(f, this.eval(e.operand, s), e.pos) : f;
      }
    }
  }

  private applyPwl(f: PwlFunction, x: Value, pos: SourcePos): Value {
    if (typeof x === 'number') return f.at(x);
    return this.flat(pos).piecewise(f, this.linear(x, pos), pos);
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
    if (target instanceof VarIndexed) {
      // a[x][k]: index every row by k, then select the row with x.
      const rows = target.target.items.map((row) => this.indexInto(row, key, pos));
      return this.element(new OplArray(target.target.index, rows), target.key, pos);
    }
    if (key instanceof DVar || key instanceof LinExpr || key instanceof CPConstraint) {
      if (!this.cpPhase) fail('decision variables cannot be used as indices', pos);
      return this.element(target, this.linear(key, pos), pos);
    }
    if (!(target instanceof OplArray)) fail(`cannot index a ${typeName(target)}`, pos);
    const i = target.index.indexOf(key);
    if (i < 0) fail(`index ${formatValue(key, UNKNOWN, 'display')} is out of bounds`, pos);
    return target.items[i];
  }

  /** target[x] for a decision-variable index x (element constraint). */
  private element(target: Value, key: Linear, pos: SourcePos): Value {
    if (!(target instanceof OplArray)) fail(`cannot index a ${typeName(target)} by a decision variable`, pos);
    const set = target.index;
    const keys: number[] = [];
    const items: Linear[] = [];
    for (let i = 0; i < set.size; i++) {
      const k = set.at(i);
      keys.push(set instanceof EnumType ? i : typeof k === 'number' ? k : fail('only arrays indexed by integers or enums can be indexed by a variable', pos));
      let item = target.items[i];
      if (item instanceof OplArray || item instanceof VarIndexed) return new VarIndexed(target, key);
      if (item instanceof DExpr) item = this.evalRef(item.e, item.scope);
      items.push(this.linear(item, pos));
    }
    return this.flat(pos).element(keys, items, key, 'element');
  }

  private field(target: Value, name: string, pos: SourcePos): Value {
    if (target instanceof Activity) {
      switch (name) {
        case 'start':
          return target.start;
        case 'end':
          return target.end;
        case 'duration':
          return target.duration;
      }
      fail(`activities have no field '${name}' (use start, end or duration)`, pos);
    }
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
    if (this.phase !== 'post') fail('solution values are only available after solving', pos);
    if (Number.isNaN(v)) fail('not available: duals and reduced costs exist only for linear programs, and only after solving', pos);
  }

  private method(e: Extract<Expr, { k: 'method' }>, s: Scope): Binding {
    const target = this.evalRef(e.target, s);
    if (isHost(target) && target.callMethod) {
      return target.callMethod(e.name, e.args.map((a) => this.eval(a, s)));
    }
    fail(`a ${typeName(target)} has no method '${e.name}'`, e.pos);
  }

  private binary(op: string, le: Expr, re: Expr, s: Scope, pos: SourcePos): Value {
    if (op === '&&' || op === '||' || op === '=>' || op === '<=>') return this.logic(op, le, re, s, pos);
    const l = this.eval(le, s);
    const r = this.eval(re, s);
    const nonConst = (v: Value) => isLinear(v) || v instanceof CPConstraint;
    if (l instanceof CumulExpr || r instanceof CumulExpr) return this.cumulOp(op, l, r, pos);
    switch (op) {
      case '+':
      case '-':
        if (typeof l === 'number' && typeof r === 'number') return op === '+' ? l + r : l - r;
        if (op === '+' && (typeof l === 'string' || typeof r === 'string')) {
          return formatValue(l, UNKNOWN, 'stream') + formatValue(r, UNKNOWN, 'stream');
        }
        return linAdd(this.linear(l, le.pos), this.linear(r, re.pos), op === '+' ? 1 : -1);
      case '*': {
        const a = this.linear(l, le.pos);
        const b = this.linear(r, re.pos);
        if (this.cpPhase && !isConstant(a) && !isConstant(b)) return this.flat(pos).mul(a, b);
        return linMul(a, b, pos);
      }
      case '/': {
        if (nonConst(r)) {
          if (!this.cpPhase) fail('division by a non-constant expression', pos);
          return this.flat(pos).div(this.linear(l, le.pos), this.linear(r, re.pos), 'realdiv');
        }
        if (typeof r !== 'number') fail('division by a non-constant expression', pos);
        if (r === 0) fail('division by zero', pos);
        if (typeof l === 'number') return l / r;
        return linMul(this.linear(l, le.pos), 1 / r, pos);
      }
      case 'div':
      case 'mod': {
        if (this.cpPhase && (nonConst(l) || nonConst(r))) {
          return this.flat(pos).div(this.linear(l, le.pos), this.linear(r, re.pos), op);
        }
        if (typeof l !== 'number' || typeof r !== 'number') fail(`'${op}' needs numbers`, pos);
        if (r === 0) fail('division by zero', pos);
        return op === 'div' ? Math.trunc(l / r) : l % r;
      }
      case '^':
        if (this.cpPhase && nonConst(l) && typeof r === 'number') return this.flat(pos).pow(this.linear(l, le.pos), r, pos);
        if (typeof l !== 'number' || typeof r !== 'number') fail("'^' needs numbers", pos);
        return Math.pow(l, r);
      case 'union':
      case 'inter':
      case 'diff':
      case 'symdiff':
        return setOp(op, l, r, pos);
      case 'in':
      case 'not in': {
        if (this.cpPhase && nonConst(l)) {
          const x = this.linear(l, le.pos);
          const elems = elementsOf(r);
          if (!elems) fail(`'in' needs a set, found a ${typeName(r)}`, pos);
          const values = elems.map((v) => this.enumOrdinal(v, x, pos));
          const c: CPCons = { k: 'member', x, values };
          return new CPConstraint(op === 'in' ? c : { k: 'not', a: c });
        }
        const set = asIndexSet(r);
        if (!set) fail(`'in' needs a set, found a ${typeName(r)}`, pos);
        const member = set.indexOf(l) >= 0;
        return member === (op === 'in') ? 1 : 0;
      }
      default:
        if (this.cpPhase && CMP_OPS.has(op) && (nonConst(l) || nonConst(r))) return this.cmpCons(op as CmpOp, l, r, pos);
        return this.compare(op, l, r, pos) ? 1 : 0;
    }
  }

  /** &&, ||, => and <=> (over numbers, or building CP constraints). */
  private logic(op: string, le: Expr, re: Expr, s: Scope, pos: SourcePos): Value {
    if (!this.cpPhase) {
      const a = this.truthy(le, s);
      if (op === '&&') return a && this.truthy(re, s) ? 1 : 0;
      if (op === '||') return a || this.truthy(re, s) ? 1 : 0;
      if (op === '=>') return !a || this.truthy(re, s) ? 1 : 0;
      return a === this.truthy(re, s) ? 1 : 0;
    }
    const a = this.cond(le, s);
    if (typeof a === 'number' && op !== '<=>') {
      if (op === '&&' && !a) return 0;
      if (op === '||' && a) return 1;
      if (op === '=>' && !a) return 1;
      const b = this.cond(re, s);
      return typeof b === 'number' ? (b ? 1 : 0) : b;
    }
    const b = this.cond(re, s);
    if (typeof a === 'number' && typeof b === 'number') return (a !== 0) === (b !== 0) ? 1 : 0;
    const ca: CPCons = typeof a === 'number' ? { k: 'const', value: a !== 0 } : a.c;
    const cb: CPCons = typeof b === 'number' ? { k: 'const', value: b !== 0 } : b.c;
    const k = op === '&&' ? 'and' : op === '||' ? 'or' : op === '=>' ? 'imp' : 'equiv';
    void pos;
    return new CPConstraint({ k, a: ca, b: cb });
  }

  /** l op r over decision variables. */
  private cmpCons(op: CmpOp, l: Value, r: Value, pos: SourcePos): CPConstraint {
    const lv = typeof l === 'string' ? null : this.linear(l, pos);
    const rv = typeof r === 'string' ? null : this.linear(r, pos);
    const L = lv ?? this.enumOrdinal(l, rv!, pos);
    const R = rv ?? this.enumOrdinal(r, lv!, pos);
    return new CPConstraint({ k: 'cmp', op, l: L, r: R });
  }

  /** An enum value compared with an enum-typed variable becomes the value's ordinal. */
  private enumOrdinal(v: Value, other: Linear, pos: SourcePos): number {
    if (typeof v === 'number') return v;
    if (typeof v === 'string') {
      const e = other instanceof DVar ? other.enumType : undefined;
      const i = e?.indexOf(v) ?? -1;
      if (i < 0) fail(`cannot compare '${v}' with a ${e ? `variable of enum ${e.name}` : 'numeric expression'}`, pos);
      return i;
    }
    fail(`expected a number, found a ${typeName(v)}`, pos);
  }

  private compare(op: string, l: Value, r: Value, pos: SourcePos): boolean {
    if (isLinear(l) || isLinear(r) || l instanceof CPConstraint || r instanceof CPConstraint) {
      fail('decision variables cannot appear in a condition', pos);
    }
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
    // A constraint used as a number (meta-constraint) is its 0/1 truth value.
    if (v instanceof CPConstraint) return this.flat(pos).reify(v.c);
    fail(`expected a numeric expression, found a ${typeName(v)}`, pos);
  }

  private aggregate(op: string, q: Quantifier, body: Expr, s: Scope, pos: SourcePos): Value {
    switch (op) {
      case 'sum': {
        let constant = 0;
        let acc: LinExpr | null = null;
        let cumul: CumulExpr | null = null;
        this.forEach(q, s, (sc) => {
          const v = this.eval(body, sc);
          if (typeof v === 'number') constant += v;
          else if (v instanceof CumulExpr) cumul = new CumulExpr([...((cumul as CumulExpr | null)?.pulses ?? []), ...v.pulses]);
          else (acc ??= new LinExpr()).addScaled(this.linear(v, body.pos), 1);
        });
        if (cumul) return cumul;
        return acc ? (acc as LinExpr).addScaled(constant, 1) : constant;
      }
      case 'all': {
        const items: Value[] = [];
        this.forEach(q, s, (sc) => items.push(this.eval(body, sc)));
        return new RawArray(items);
      }
      case 'union':
      case 'inter': {
        let acc: OplSet | null = null;
        this.forEach(q, s, (sc) => {
          const v = this.eval(body, sc);
          acc = acc ? setOp(op, acc, v, pos) : setOp('union', new OplSet(), v, pos);
        });
        return acc ?? new OplSet();
      }
      case 'prod':
      case 'min':
      case 'max': {
        const vals: Value[] = [];
        this.forEach(q, s, (sc) => vals.push(this.eval(body, sc)));
        if (this.cpPhase && vals.some((v) => isLinear(v) || v instanceof CPConstraint)) {
          const lin = vals.map((v) => this.linear(v, body.pos));
          if (op !== 'prod') return lin.length ? this.flat(pos).minmax(lin, op === 'min') : op === 'min' ? Infinity : -Infinity;
          return lin.reduce((a, b) => (isConstant(a) || isConstant(b) ? linMul(a, b, pos) : this.flat(pos).mul(a, b)), 1 as Linear);
        }
        const nums = vals.map((v) => {
          if (typeof v !== 'number') fail(`expected a number, found a ${typeName(v)}`, body.pos);
          return v;
        });
        if (op === 'prod') return nums.reduce((a, b) => a * b, 1);
        return op === 'min' ? Math.min(Infinity, ...nums) : Math.max(-Infinity, ...nums);
      }
      case 'and':
      case 'or': {
        let r = op === 'and';
        let c: CPCons | null = null;
        this.forEach(q, s, (sc) => {
          if (!this.cpPhase) {
            const v = this.truthy(body, sc);
            r = op === 'and' ? r && v : r || v;
            return;
          }
          const v = this.cond(body, sc);
          if (typeof v === 'number') r = op === 'and' ? r && v !== 0 : r || v !== 0;
          else c = c ? { k: op, a: c, b: v.c } : v.c;
        });
        if (!c) return r ? 1 : 0;
        if (op === 'and' && !r) return 0;
        if (op === 'or' && r) return 1;
        return new CPConstraint(c);
      }
    }
    fail(`unknown aggregate '${op}'`, pos);
  }

  private call(fn: string, argExprs: Expr[], s: Scope, pos: SourcePos): Value {
    const args = argExprs.map((a) => this.eval(a, s));
    const special = this.cpCall(fn, args, pos, s);
    if (special !== undefined) return special;
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
        const k = args[1];
        if (k instanceof OplTuple) {
          // item(S, <key fields>): the element whose leading fields match
          for (let j = 0; j < set.size; j++) {
            const el = set.at(j);
            if (el instanceof OplTuple && k.values.every((v, n) => valuesEqual(v, el.values[n]))) return el;
          }
          fail('item: no element with this key', pos);
        }
        const i = numArg(1);
        if (i < 0 || i >= set.size) fail('item: index out of bounds', pos);
        return set.at(i);
      }
    }
    fail(`unknown function '${fn}'`, pos);
  }

  /** Constraint-programming and scheduling built-ins; undefined when fn is not one. */
  private cpCall(fn: string, args: Value[], pos: SourcePos, s?: Scope): Value | undefined {
    const fromSearch = this.searchFns?.(fn, args, pos);
    if (fromSearch !== undefined) return fromSearch;
    const pwl = s?.lookup(fn)?.value;
    if (pwl instanceof PwlFunction) {
      if (args.length !== 1) fail(`${fn} takes one argument`, pos);
      return this.applyPwl(pwl, args[0], pos);
    }
    const pred = s?.lookup(fn)?.value;
    if (pred instanceof Predicate) {
      if (args.length !== pred.arity) fail(`${fn} expects ${pred.arity} argument(s)`, pos);
      if (args.every((a) => typeof a === 'number' || typeof a === 'string')) {
        return pred.set.elems.some((t) => t instanceof OplTuple && t.values.every((v, i) => valuesEqual(v, args[i]))) ? 1 : 0;
      }
      return this.cpCall('allowedAssignments', [pred.set, ...args], pos);
    }
    const nonConst = args.some((a) => isLinear(a) || a instanceof CPConstraint);
    const lin = (v: Value) => this.linear(v, pos);
    switch (fn) {
      case 'abs':
        return nonConst ? this.flat(pos).abs(lin(args[0])) : undefined;
      case 'floor':
      case 'ceil':
      case 'round':
      case 'ftoi':
      case 'trunc': {
        if (!nonConst) return undefined;
        const x = lin(args[0]);
        if (isIntegral(x) && (!(x instanceof LinExpr) || [...x.terms.keys()].every((id) => this.cp?.dvar(id)?.isInt))) return x;
        return this.flat(pos).rounding(fn === 'ftoi' ? 'trunc' : fn, x);
      }
      case 'sqrt':
      case 'exp':
      case 'log':
        return nonConst ? this.flat(pos).fn(fn, lin(args[0])) : undefined;
      case 'pow': {
        if (!nonConst) return undefined;
        const [b, k] = args;
        if (typeof b === 'number' && isLinear(k)) {
          // b ^ x for a variable exponent: an element constraint over x's values
          const flat = this.flat(pos);
          const [lo, hi] = linBounds(flat.h, k, flat.vars);
          if (!isFinite(lo) || !isFinite(hi) || hi - lo > 10000) fail('pow(b, x) needs a variable exponent with a small domain', pos);
          const keys: number[] = [];
          for (let v = Math.ceil(lo); v <= hi; v++) keys.push(v);
          return flat.element(keys, keys.map((v) => Math.pow(b, v)), k, 'pow');
        }
        return this.flat(pos).pow(lin(b), k as number, pos);
      }
      case 'min':
      case 'max':
      case 'minl':
      case 'maxl':
        return nonConst ? this.flat(pos).minmax(args.map(lin), fn.startsWith('min')) : undefined;
      case 'dsize':
      case 'dmin':
      case 'dmax':
      case 'bound':
      case 'regretdmin':
      case 'regretdmax':
      case 'dnext':
      case 'dprev':
        return this.domainFn(fn, args, pos);
      case 'alldifferent':
      case 'allDifferent':
        return new CPConstraint({ k: 'alldiff', xs: this.atoms(args, pos), level: 'onValue' });
      case 'allMinDistance': {
        const xs = this.atoms([args[0]], pos);
        const k = args[1];
        if (typeof k !== 'number') fail('allMinDistance(x, k): k must be a number', pos);
        let c: CPCons = { k: 'const', value: true };
        for (let i = 0; i < xs.length; i++) {
          for (let j = i + 1; j < xs.length; j++) {
            const d = linAdd(xs[i], xs[j], -1);
            c = { k: 'and', a: c, b: { k: 'or', a: { k: 'cmp', op: '>=', l: d, r: k }, b: { k: 'cmp', op: '<=', l: d, r: -k } } };
          }
        }
        return new CPConstraint(c);
      }
      case 'append':
        return new RawArray(args.flatMap((a) => this.leaves(a)));
      case 'asSet': {
        const elems = args[0] === undefined ? null : elementsOf(args[0]);
        if (!elems) fail('asSet needs a range or set', pos);
        return new OplSet(elems);
      }
      case 'rand': {
        const n = args[0];
        if (typeof n !== 'number') fail('rand(n) needs a number', pos);
        return Math.floor(Math.random() * n);
      }
      case 'count': {
        if (args.length !== 2) fail('count(array, value) expects 2 arguments', pos);
        const xs = this.leaves(args[0]);
        const v = args[1];
        if (!nonConst && xs.every((x) => typeof x === 'number' || typeof x === 'string')) return xs.filter((x) => valuesEqual(x, v)).length;
        const sum = new LinExpr();
        for (const x of xs) {
          const lx = typeof x === 'string' ? fail('count over strings needs data values', pos) : this.linear(x, pos);
          const target = typeof v === 'string' ? this.enumOrdinal(v, lx, pos) : this.linear(v, pos);
          sum.addScaled(this.linear(new CPConstraint({ k: 'cmp', op: '=', l: lx, r: target }), pos), 1);
        }
        return sum;
      }
      case 'sgn': {
        if (!nonConst) return Math.sign(this.linear(args[0], pos) as number);
        const x = lin(args[0]);
        const pos1 = this.linear(new CPConstraint({ k: 'cmp', op: '>', l: x, r: 0 }), pos);
        const neg1 = this.linear(new CPConstraint({ k: 'cmp', op: '<', l: x, r: 0 }), pos);
        return linAdd(pos1, neg1, -1);
      }
      case 'ifThen':
      case 'ifthen': {
        const [a, b] = args.map((v) => (v instanceof CPConstraint ? v.c : typeof v === 'number' ? { k: 'const' as const, value: v !== 0 } : fail('ifThen needs two constraints', pos)));
        return new CPConstraint({ k: 'imp', a, b });
      }
      case 'element': {
        // element(array, index) or element(index, array)
        const [a, b] = args;
        const arr = a instanceof OplArray || a instanceof RawArray ? a : b;
        const idx = arr === a ? b : a;
        const target = arr instanceof RawArray ? new OplArray(new OplRange(0, arr.items.length - 1), arr.items) : arr;
        return this.indexInto(target, idx, pos);
      }
      case 'inverse': {
        const [f, g] = args;
        if (!(f instanceof OplArray) || !(g instanceof OplArray)) fail('inverse(f, g) needs two arrays of variables', pos);
        let c: CPCons = { k: 'const', value: true };
        for (let i = 0; i < f.index.size; i++) {
          const key = f.index.at(i);
          const fi = lin(f.items[i]);
          c = { k: 'and', a: c, b: { k: 'cmp', op: '=', l: this.linear(this.indexInto(g, fi, pos), pos), r: typeof key === 'number' ? key : i } };
        }
        return new CPConstraint(c);
      }
      case 'allowedAssignments':
      case 'forbiddenAssignments': {
        const [tuples, ...rest] = args;
        const elems = elementsOf(tuples);
        if (!elems) fail(`${fn}(tuples, x1, ..., xn) needs a set of tuples`, pos);
        const xs = this.atoms(rest, pos);
        const rows = elems.map((t) => {
          const vals = t instanceof OplTuple ? t.values : [t];
          if (vals.length !== xs.length) fail(`${fn}: tuples have ${vals.length} values for ${xs.length} variables`, pos);
          return vals.map((v, i) => this.enumOrdinal(v, xs[i], pos));
        });
        return new CPConstraint({ k: 'table', xs, tuples: rows, positive: fn === 'allowedAssignments' });
      }
      case 'lex':
      case 'lexicographic': {
        // x <=lex y: for each i, x[0..i-1] = y[0..i-1] implies x[i] <= y[i]
        const xs = this.atoms([args[0]], pos);
        const ys = this.atoms([args[1]], pos);
        let prefix: CPCons = { k: 'const', value: true };
        let c: CPCons = { k: 'const', value: true };
        for (let i = 0; i < Math.min(xs.length, ys.length); i++) {
          c = { k: 'and', a: c, b: { k: 'imp', a: prefix, b: { k: 'cmp', op: '<=', l: xs[i], r: ys[i] } } };
          prefix = { k: 'and', a: prefix, b: { k: 'cmp', op: '=', l: xs[i], r: ys[i] } };
        }
        return new CPConstraint(c);
      }
      case 'staticLex': {
        // Lexicographic objective as one weighted objective (exact for bounded integer criteria).
        const crit = args.map(lin);
        const flat = this.flat(pos);
        let total: Linear = 0;
        let weight = 1;
        for (let i = crit.length - 1; i >= 0; i--) {
          total = linAdd(total, linMul(crit[i], weight, pos), 1);
          const [lo, hi] = linBounds(flat.h, crit[i], flat.vars);
          if (!isFinite(lo) || !isFinite(hi) || !isIntegral(crit[i])) {
            fail('staticLex needs bounded integer criteria', pos);
          }
          weight *= hi - lo + 1;
        }
        return total;
      }
      case 'distribute':
      case 'atmost':
      case 'atleast': {
        if (args.length !== 3) fail(`${fn}(card, value, base) expects 3 arguments`, pos);
        const base = this.atoms([args[2]], pos);
        const values = this.leaves(args[1]).map((v) => this.enumOrdinal(v, base[0] ?? 0, pos));
        const cards = this.atoms([args[0]], pos);
        if (cards.length !== values.length) fail(`${fn}: card and value must have the same size`, pos);
        return new CPConstraint({ k: 'count', mode: fn === 'distribute' ? 'exact' : fn, cards, values, base });
      }
      case 'pack': {
        // pack(load, where, size): load[b] = sum of size[i] over the items with where[i] = b
        const [loadArr, whereArr, sizeArr] = args;
        if (!(loadArr instanceof OplArray)) fail('pack(load, where, size) needs an array of bin loads', pos);
        const where = this.atoms([whereArr], pos);
        const size = this.leaves(sizeArr);
        let c: CPCons = { k: 'const', value: true };
        for (let bin = 0; bin < loadArr.index.size; bin++) {
          const key = loadArr.index.at(bin);
          const sum = new LinExpr();
          where.forEach((w, i) => {
            const isIn = this.linear(new CPConstraint({ k: 'cmp', op: '=', l: w, r: typeof key === 'number' ? key : bin }), pos);
            sum.addScaled(linMul(isIn, this.linear(size[i], pos), pos), 1);
          });
          c = { k: 'and', a: c, b: { k: 'cmp', op: '=', l: this.linear(loadArr.items[bin], pos), r: sum } };
        }
        return new CPConstraint(c);
      }
      case 'subCircuit': {
        const arr = args[0];
        if (!(arr instanceof OplArray) || !(arr.index instanceof OplRange)) fail('subCircuit needs an array of variables indexed by a range', pos);
        return new CPConstraint({ k: 'circuit', xs: this.atoms(args, pos), offset: arr.index.lo, sub: true });
      }
      case 'circuit': {
        const arr = args[0];
        if (!(arr instanceof OplArray) || !(arr.index instanceof OplRange)) fail('circuit needs an array of variables indexed by a range', pos);
        return new CPConstraint({ k: 'circuit', xs: this.atoms(args, pos), offset: arr.index.lo });
      }
      case 'precedes':
        return this.temporal('end', 'start', args, pos, '<=', 0);
      // CP Optimizer interval variables
      case 'startOf':
      case 'endOf':
      case 'sizeOf':
      case 'lengthOf': {
        const a = this.activityArg(args[0], pos);
        const v: Linear = fn === 'startOf' ? a.start : fn === 'endOf' ? a.end : a.duration;
        if (!a.presence || this.phase === 'post') return this.phase === 'post' && a.presence && dvarValue(a.presence) === 0 ? (args[1] ?? 0) : v;
        // absent intervals take the value given as second argument (default 0)
        const absent = args[1] === undefined ? 0 : this.linear(args[1], pos);
        return linAdd(this.flat(pos).mul(a.presence, v), linMul(linAdd(1, a.presence, -1), absent, pos), 1);
      }
      case 'presenceOf': {
        const a = this.activityArg(args[0], pos);
        if (!a.presence) return 1;
        return this.phase === 'post' ? dvarValue(a.presence) : new CPConstraint({ k: 'cmp', op: '=', l: a.presence, r: 1 });
      }
      case 'endBeforeStart':
        return this.ifPresent(args, this.temporal('end', 'start', args, pos, '<=', undefined, true), pos);
      case 'endBeforeEnd':
        return this.ifPresent(args, this.temporal('end', 'end', args, pos, '<=', undefined, true), pos);
      case 'startBeforeStart':
        return this.ifPresent(args, this.temporal('start', 'start', args, pos, '<=', undefined, true), pos);
      case 'startBeforeEnd':
        return this.ifPresent(args, this.temporal('start', 'end', args, pos, '<=', undefined, true), pos);
      case 'endAtStart':
        return this.ifPresent(args, this.temporal('end', 'start', args, pos, '=', undefined, true), pos);
      case 'endAtEnd':
        return this.ifPresent(args, this.temporal('end', 'end', args, pos, '=', undefined, true), pos);
      case 'startAtStart':
        return this.ifPresent(args, this.temporal('start', 'start', args, pos, '=', undefined, true), pos);
      case 'startAtEnd':
        return this.ifPresent(args, this.temporal('start', 'end', args, pos, '=', undefined, true), pos);
      case 'noOverlap': {
        const acts = this.leaves(args[0]).map((a) => this.activityArg(a, pos));
        const res = new Resource(`noOverlap#${acts.length}`, 'unary', 1, 0);
        return this.usesAll(acts.map((act) => ({ act, height: 1 })), res, pos);
      }
      case 'pulse': {
        const act = this.activityArg(args[0], pos);
        return new CumulExpr([{ act, height: args[1] === undefined ? 1 : this.linear(args[1], pos) }]);
      }
      case 'startsAfterEnd':
        return this.temporal('start', 'end', args, pos, '>=');
      case 'startsAfterStart':
        return this.temporal('start', 'start', args, pos, '>=');
      case 'endsAfterEnd':
        return this.temporal('end', 'end', args, pos, '>=');
      case 'endsAfterStart':
        return this.temporal('end', 'start', args, pos, '>=');
      case 'startsAtEnd':
        return this.temporal('start', 'end', args, pos, '=');
      case 'startsAtStart':
        return this.temporal('start', 'start', args, pos, '=');
      case 'endsAtEnd':
        return this.temporal('end', 'end', args, pos, '=');
      case 'endsAtStart':
        return this.temporal('end', 'start', args, pos, '=');
      case 'requires':
      case 'consumes':
      case 'produces':
        return this.uses(fn, args, pos);
      case 'activityHasSelectedResource': {
        const [a, alt, r] = args;
        if (!(a instanceof Activity) || !(alt instanceof Resource) || !(r instanceof Resource) || alt.kind !== 'alternative') {
          fail('activityHasSelectedResource(activity, alternativeResources, resource)', pos);
        }
        const k = alt.members.indexOf(r);
        if (k < 0) fail(`${r.name} is not one of the alternative resources ${alt.name}`, pos);
        if (this.phase === 'post') {
          const sel = this.selections?.get(a)?.get(alt);
          return sel ? dvarValue(sel[k]) : 0;
        }
        return new CPConstraint({ k: 'cmp', op: '=', l: this.flat(pos).selection(a, alt)[k], r: 1 });
      }
    }
    return undefined;
  }

  /** dsize(x), dmin(x), ... over the current domain of x (or a value). */
  private domainFn(fn: string, args: Value[], pos: SourcePos): Value {
    const x = args[0];
    let lo: number;
    let hi: number;
    let size: number;
    let dom: import('./cp/domain.js').Dom | null = null;
    if (typeof x === 'number') {
      lo = hi = x;
      size = 1;
    } else if (typeof x === 'string') {
      return fn === 'bound' ? 1 : fn === 'dsize' ? 1 : fail(`${fn} needs a numeric variable`, pos);
    } else if (x instanceof DVar) {
      dom = this.cp?.domain(x) ?? null;
      if (dom) {
        lo = dom.min;
        hi = dom.max;
        size = dom.size;
      } else {
        lo = x.lb;
        hi = x.ub;
        size = x.isInt ? hi - lo + 1 : Infinity;
      }
    } else fail(`${fn} needs a decision variable, found a ${typeName(x)}`, pos);
    switch (fn) {
      case 'dsize':
        return size;
      case 'dmin':
        return lo;
      case 'dmax':
        return hi;
      case 'bound':
        return size === 1 ? 1 : 0;
      case 'regretdmin': {
        const second = dom ? dom.next(lo) : size > 1 ? lo + 1 : null;
        return second === null ? 0 : second - lo;
      }
      case 'regretdmax': {
        const second = dom ? dom.prev(hi) : size > 1 ? hi - 1 : null;
        return second === null ? 0 : hi - second;
      }
      case 'dnext':
      case 'dprev': {
        const v = args[1];
        if (typeof v !== 'number') fail(`${fn}(x, v) needs a number v`, pos);
        const r = dom ? (fn === 'dnext' ? dom.next(v) : dom.prev(v)) : fn === 'dnext' ? Math.min(v + 1, hi) : Math.max(v - 1, lo);
        return r ?? v;
      }
    }
    return fail(`unknown function ${fn}`, pos);
  }

  /** Leaves of arrays, sets and tuples (arguments of global constraints). */
  private leaves(v: Value): Value[] {
    if (v instanceof OplArray || v instanceof RawArray) return v.items.flatMap((x) => this.leaves(x));
    if (v instanceof OplSet) return v.elems;
    if (v instanceof OplRange) return elementsOf(v)!;
    return [v];
  }

  private atoms(args: Value[], pos: SourcePos): Linear[] {
    return args.flatMap((a) => this.leaves(a)).map((v) => this.linear(v, pos));
  }

  private activityArg(v: Value, pos: SourcePos): Activity {
    if (!(v instanceof Activity)) fail(`expected an activity, found a ${typeName(v)}`, pos);
    return v;
  }

  /**
   * Precedence constraints between activities: a.<fa> op b.<fb> + delay
   * (forward: a.<fa> + delay op b.<fb>, the CP Optimizer argument order).
   */
  private temporal(fa: 'start' | 'end', fb: 'start' | 'end', args: Value[], pos: SourcePos, op: CmpOp, fixedDelay?: number, forward = false): CPConstraint {
    if (args.length < 2) fail('expected two activities', pos);
    const a = this.activityArg(args[0], pos);
    const b = this.activityArg(args[1], pos);
    const delay = fixedDelay ?? (args[2] === undefined ? 0 : this.linear(args[2], pos));
    if (forward) return new CPConstraint({ k: 'cmp', op, l: linAdd(a[fa], delay, 1), r: b[fb] });
    return new CPConstraint({ k: 'cmp', op, l: a[fa], r: linAdd(b[fb], delay, 1) });
  }

  /** A precedence between optional intervals holds only when both are present. */
  private ifPresent(args: Value[], c: CPConstraint, pos: SourcePos): CPConstraint {
    const ps = [args[0], args[1]].map((a) => this.activityArg(a, pos).presence).filter((p): p is DVar => p !== null);
    if (ps.length === 0) return c;
    let cond: CPCons = { k: 'cmp', op: '=', l: ps[0], r: 1 };
    if (ps[1]) cond = { k: 'and', a: cond, b: { k: 'cmp', op: '=', l: ps[1], r: 1 } };
    return new CPConstraint({ k: 'imp', a: cond, b: c.c });
  }

  /** Requirements of several activities on one resource (presence = the interval's own presence). */
  private usesAll(items: { act: Activity; height: Linear }[], res: Resource, pos: SourcePos): CPConstraint {
    void pos;
    let c: CPCons = { k: 'const', value: true };
    for (const { act, height } of items) {
      c = { k: 'and', a: c, b: { k: 'uses', how: 'requires', act, res, amount: height, presence: act.presence } };
    }
    return new CPConstraint(c);
  }

  /** f <= C for a cumul function, and sums of cumul functions. */
  private cumulOp(op: string, l: Value, r: Value, pos: SourcePos): Value {
    if (op === '+' && l instanceof CumulExpr && r instanceof CumulExpr) return new CumulExpr([...l.pulses, ...r.pulses]);
    const [f, cap, flipped] = l instanceof CumulExpr ? [l, r, false] : [r as CumulExpr, l, true];
    const le = flipped ? op === '>=' : op === '<=';
    if (!le || typeof cap !== 'number') fail('a cumul function can only be bounded by a constant: f <= C', pos);
    return this.usesAll(f.pulses, new Resource(`cumul#${f.pulses.length}`, 'discrete', cap, 0), pos);
  }

  private uses(how: 'requires' | 'consumes' | 'produces', args: Value[], pos: SourcePos): CPConstraint {
    const act = this.activityArg(args[0], pos);
    const res = args[1];
    if (!(res instanceof Resource)) fail(`${how}: expected a resource, found a ${typeName(res)}`, pos);
    let amount: Linear = 1;
    const a2 = args[2];
    if (typeof a2 === 'string') {
      // requires(state) on a StateResource
      const states = res.kind === 'alternative' ? res.members[0]?.states : res.states;
      const i = states?.indexOf(a2) ?? -1;
      if (i < 0) fail(`'${a2}' is not a state of ${res.name}`, pos);
      amount = i;
    } else if (a2 !== undefined) amount = this.linear(a2, pos);
    if (res.kind !== 'alternative') return new CPConstraint({ k: 'uses', how, act, res, amount, presence: null });
    const sel = this.flat(pos).selection(act, res);
    let c: CPCons | null = null;
    res.members.forEach((m, k) => {
      const part: CPCons = { k: 'uses', how, act, res: m, amount, presence: sel[k] };
      c = c ? { k: 'and', a: c, b: part } : part;
    });
    return new CPConstraint(c ?? { k: 'const', value: false });
  }

  // ------------------------------------------------------------ iteration

  private binders(q: Quantifier): Binder[] {
    let out = this.expanded.get(q);
    if (!out) {
      // `i, j in S` is `i in S, j in S`; with `ordered`, j comes after i in S.
      out = q.binders.flatMap((b) =>
        b.pattern || b.names.length === 1
          ? [b]
          : b.names.map((n, i): Binder & { after?: string } => ({
              ...b,
              names: [n],
              filter: i === b.names.length - 1 ? b.filter : undefined,
              after: b.ordered && i > 0 ? b.names[i - 1] : undefined,
            })),
      );
      this.expanded.set(q, out);
    }
    return out;
  }

  /** Calls fn once per assignment of the quantifier's iterators (in a child scope). */
  forEach(q: Quantifier, s: Scope, fn: (scope: Scope) => void): void {
    if (q.order) {
      // `ordered by`: evaluate every assignment's key, then visit them in key order.
      const items: { scope: Scope; key: number }[] = [];
      this.forEach({ ...q, order: undefined, binders: this.binders(q) }, s, (sc) => {
        const copy = new Scope(s);
        for (const b of q.binders) for (const n of b.names) copy.define(n, { ...sc.lookup(n)! });
        items.push({ scope: copy, key: q.order!.dir * this.num(q.order!.key, copy) });
      });
      items.sort((a, b) => a.key - b.key);
      for (const it of items) fn(it.scope);
      return;
    }
    const binders = this.binders(q) as (Binder & { after?: string })[];
    const scope = new Scope(s);
    const run = (bi: number): void => {
      if (bi === binders.length) {
        checkMemory();
        fn(scope);
        return;
      }
      const b = binders[bi];
      const dv = this.eval(b.domain, scope);
      const elems = elementsOf(dv);
      if (!elems) fail(`cannot iterate over a ${typeName(dv)}`, b.domain.pos);
      const et = elementType(this.typeOf(b.domain, scope), dv);
      // In a tuple pattern, names already bound to enclosing iterators select matching tuples.
      const fixed = b.pattern ? b.names.map((n) => (scope.lookup(n)?.iterator ? scope.lookup(n)!.value : undefined)) : [];
      const slots: Binding[] = b.names.map((n, i) => {
        const slot: Binding = { value: 0, type: b.pattern ? tupleFieldType(et, i) : et, iterator: true };
        if (fixed[i] === undefined) scope.define(n, slot);
        return slot;
      });
      let from = 0;
      if (b.after) {
        const prev = scope.lookup(b.after)!.value;
        from = elems.findIndex((x) => valuesEqual(x, prev)) + 1;
      }
      for (let k = from; k < elems.length; k++) {
        const el = elems[k];
        if (b.pattern) {
          if (!(el instanceof OplTuple) || el.values.length !== slots.length) {
            fail(`tuple pattern does not match ${formatValue(el, et, 'display')}`, b.pos);
          }
          if (fixed.some((f, i) => f !== undefined && !valuesEqual(f, el.values[i]))) continue;
          if (b.patternExprs?.some((pe, i) => pe && !valuesEqual(this.eval(pe, scope), el.values[i]))) continue;
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
        if (target instanceof Activity) return INT;
        if (target instanceof ConstraintRef) return FLOAT;
        if (target instanceof DVar) return (e.name === 'value' || e.name === 'sol') && target.isInt ? INT : FLOAT;
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
      case 'arrayComp':
      case 'indexedLit':
      case 'namedTuple':
        return UNKNOWN;
      case 'piecewise':
        return e.operand ? FLOAT : UNKNOWN;
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
        if (te.name === 'boolean' || te.name === 'bool') return { k: 'int', range: new OplRange(0, 1) };
        if (te.name === 'pwlFunction' || te.name === 'stepFunction' || te.name === 'cumulFunction') return UNKNOWN;
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
      const slot: Binding = { value: 0, type: elementType(UNKNOWN, sets[k] as Value), iterator: true };
      scope.define(d.name, slot);
      return slot;
    });
    const path: Value[] = [];
    const rec = (k: number): Value => {
      if (k === sets.length) {
        checkMemory();
        return leaf(scope, path);
      }
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

  /**
   * buildArray whose cells are made on first access (dexpr arrays over large
   * index spaces): the items are a proxy that fills itself in.
   */
  buildLazyArray(dims: Dim[], sets: IndexSet[], s: Scope, leaf: (scope: Scope, path: Value[]) => Value): Value {
    const scope = new Scope(s);
    const slots = dims.map((d, k) => {
      if (!d.name) return null;
      const slot: Binding = { value: 0, type: elementType(UNKNOWN, sets[k] as Value), iterator: true };
      scope.define(d.name, slot);
      return slot;
    });
    const cell = (path: Value[]): Value => {
      path.forEach((key, k) => {
        const slot = slots[k];
        if (slot) slot.value = key;
      });
      return leaf(scope, path);
    };
    const level = (k: number, path: Value[]): OplArray => {
      const set = sets[k];
      const target: Value[] = new Array(set.size);
      const items = new Proxy(target, {
        get: (t, p, r) => {
          if (typeof p === 'string' && p.charCodeAt(0) >= 48 && p.charCodeAt(0) <= 57) {
            const i = Number(p);
            if (Number.isInteger(i) && i < set.size && t[i] === undefined) {
              const at = [...path, set.at(i)];
              t[i] = k + 1 === sets.length ? cell(at) : level(k + 1, at);
            }
          }
          return Reflect.get(t, p, r);
        },
      });
      return new OplArray(set, items);
    };
    return level(0, []);
  }

  // ------------------------------------------------------------ shaping

  /** Converts a (literal) value into the declared type, validating it. */
  /** lenient: data-file arrays may be shorter than declared (padded with defaults). */
  shape(v: Value, t: Type, pos: SourcePos, lenient = false): Value {
    switch (t.k) {
      case 'array': {
        const [first, ...rest] = t.dims;
        const inner = arrayType(t.of, rest);
        if (v instanceof RawArray || v instanceof OplArray) {
          if (v.items.length > first.size || (!lenient && v.items.length < first.size)) {
            fail(`expected ${first.size} array element(s), found ${v.items.length}`, pos);
          }
          // Missing trailing elements take the default value (0), as OPL does.
          const items = v.items.map((x) => this.shape(x, inner, pos, lenient));
          while (items.length < first.size) items.push(this.defaultValue(inner));
          return new OplArray(first, items);
        }
        if (v instanceof RawIndexed) {
          // Entries for the same key with indexed values merge: [i : [t : v] | <i,t,v> in S]
          const raw: (Value | undefined)[] = new Array(first.size).fill(undefined);
          for (const [k, x] of v.entries) {
            const key = first instanceof EnumType ? this.shape(k, { k: 'enum', e: first }, pos, lenient) : k;
            const i = first.indexOf(key);
            if (i < 0) fail(`index ${formatValue(k, UNKNOWN, 'display')} is out of bounds`, pos);
            const prev = raw[i];
            raw[i] = prev instanceof RawIndexed && x instanceof RawIndexed ? new RawIndexed([...prev.entries, ...x.entries]) : x;
          }
          // Keys without a value take the default value (generic arrays are often sparse).
          return new OplArray(first, raw.map((x) => (x === undefined ? this.defaultValue(inner) : this.shape(x, inner, pos, lenient))));
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
        const set = new OplSet(elems.map((x) => this.shape(x, t.of, pos, lenient)), t.of);
        if (t.of.k === 'struct') for (const x of set.elems) if (x instanceof OplTuple) t.of.s.register(x);
        return set;
      }
      case 'struct': {
        const fields = t.s.fields;
        // A reference by key: "Anne" for <"Anne", ...>, or <keys...> for a tuple with key fields.
        const keys = t.s.keyFields;
        if (keys.length && (typeof v === 'number' || typeof v === 'string' || (v instanceof OplTuple && v.values.length === keys.length && keys.length < fields.length))) {
          const found = t.s.byKey.get(t.s.keyOfValues(v instanceof OplTuple ? v.values : [v]));
          if (found) return found;
          if (!(v instanceof OplTuple)) fail(`no ${t.s.name} with key ${formatValue(v, UNKNOWN, 'display')}`, pos);
        }
        if (v instanceof OplTuple) {
          if (v.values.length !== fields.length) {
            fail(`tuple ${t.s.name} has ${fields.length} field(s), found ${v.values.length} value(s)`, pos);
          }
          return new OplTuple(t.s, v.values.map((x, i) => this.shape(x, fields[i].type, pos, lenient)));
        }
        if (v instanceof NamedTuple) {
          return new OplTuple(t.s, fields.map((f) => {
            if (!v.fields.has(f.name)) fail(`missing field '${f.name}' of ${t.s.name}`, pos);
            return this.shape(v.fields.get(f.name)!, f.type, pos, lenient);
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

function isConstant(v: Linear): boolean {
  return typeof v === 'number' || (v instanceof LinExpr && v.isConstant());
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
