/**
 * Expression evaluation, static typing (for formatting), quantifier iteration
 * and shaping of literal data into declared types.
 */

import type { Binder, Dim, Expr, Quantifier, TypeExpr } from './ast.js';
import { fail, type SourcePos } from './errors.js';
import { cumulSegments, cumulValue, stateSegments, type StateFixed } from './cp/cumul.js';
import {
  Activity, CP_MAXINT, CPConstraint, Flattener, isIntegral, linBounds, Resource, Sequence, StateFunction, StepFunction,
  type CmpOp, type CPCons, type CPHooks, type CumulTerm, type FunctionWindow, type StateWindow,
} from './cp/terms.js';
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

/** A cumul function (CP Optimizer): a sum of pulses and steps. */
export class CumulExpr {
  constructor(readonly terms: CumulTerm[]) {}
}

/** The time line of CP Optimizer: [-IntervalMax, IntervalMax]. */
const INTERVAL_MAX = 1073741823;

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
  /** noOverlap constraints so far (their resources are numbered). */
  private noOverlaps = 0;
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
  /** Cumul functions built from a dexpr: one value, so its height variables are shared. */
  private readonly cumulOf = new WeakMap<DExpr, CumulExpr>();

  private deref(d: DExpr): Value {
    const known = this.cumulOf.get(d);
    if (known) return known;
    const v = this.evalRef(d.e, d.scope);
    if (v instanceof CumulExpr) this.cumulOf.set(d, v);
    return v;
  }

  evalRef(e: Expr, s: Scope): Value {
    switch (e.k) {
      case 'num':
      case 'str':
        return e.value;
      case 'sym':
        return e.name;
      case 'id': {
        const b = s.lookup(e.name);
        if (b) return b.value instanceof DExpr ? this.deref(b.value) : b.value;
        if (e.name === 'maxint') return MAXINT;
        if (e.name === 'infinity') return Infinity;
        if (e.name === 'true') return 1;
        if (e.name === 'false') return 0;
        fail(`unknown identifier '${e.name}'`, e.pos);
      }
      // falls through (unreachable)
      case 'index': {
        let target = this.evalRef(e.target, s);
        for (const a of e.args) target = this.indexInto(target, this.eval(a, s), a.pos);
        return target instanceof DExpr ? this.deref(target) : target;
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
        if (v instanceof CumulExpr) return this.negCumul(v, e.pos);
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
      case 'stepwise': {
        const values: number[] = [];
        const points: number[] = [];
        const add = (sc: Scope) => {
          for (const it of e.items) {
            values.push(this.num(it.slope, sc));
            points.push(this.num(it.bp, sc));
          }
        };
        if (e.q) this.forEach(e.q, s, add);
        else add(s);
        values.push(this.num(e.last, s));
        for (let k = 1; k < points.length; k++) if (points[k] < points[k - 1]) fail('stepwise points must be increasing', e.pos);
        return new StepFunction(values, points);
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
      if (item instanceof DExpr) item = this.deref(item);
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
          else if (v instanceof CumulExpr) cumul = new CumulExpr([...((cumul as CumulExpr | null)?.terms ?? []), ...v.terms]);
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
      case 'ln':
        arity(1);
        return Math.log(numArg(0));
      case 'log':
        // OPL: log is base 10, lg base 2, ln natural.
        arity(1);
        return Math.log10(numArg(0));
      case 'lg':
        arity(1);
        return Math.log2(numArg(0));
      case 'distToInt':
        arity(1);
        return Math.abs(numArg(0) - Math.round(numArg(0)));
      case 'intValue':
      case 'floatValue': {
        arity(1);
        const v = Number(String(args[0]).trim());
        if (Number.isNaN(v) || (fn === 'intValue' && !Number.isInteger(v))) fail(`${fn}: cannot convert "${args[0]}"`, pos);
        return v;
      }
      case 'matchAt': {
        arity(2);
        if (typeof args[0] !== 'string' || typeof args[1] !== 'string') fail('matchAt(string, substring)', pos);
        return args[0].indexOf(args[1]);
      }
      case 'srand':
        arity(1);
        seedRandom(numArg(0));
        return numArg(0);
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
        return nonConst ? this.flat(pos).fn(fn, lin(args[0])) : undefined;
      case 'ln':
      case 'log':
      case 'lg':
        // natural log, scaled for base 10 / base 2
        if (!nonConst) return undefined;
        return linMul(this.flat(pos).fn('log', lin(args[0])), fn === 'ln' ? 1 : 1 / Math.log(fn === 'log' ? 10 : 2), pos);
      case 'standardDeviation': {
        // Population standard deviation (the n formula).
        const xs = this.leaves(args[0]);
        if (!xs.length) fail('standardDeviation of an empty array', pos);
        if (xs.every((x) => typeof x === 'number')) {
          const v = xs as number[];
          const mean = v.reduce((a, b) => a + b, 0) / v.length;
          return Math.sqrt(v.reduce((a, b) => a + (b - mean) ** 2, 0) / v.length);
        }
        const flat = this.flat(pos);
        const ls = xs.map((x) => this.linear(x, pos));
        const mean = ls.reduce<Linear>((a, b) => linAdd(a, b, 1), 0);
        let sq: Linear = 0;
        for (const x of ls) {
          const d = linAdd(linMul(x, ls.length, pos), mean, -1);
          sq = linAdd(sq, flat.mul(d, d), 1);
        }
        // sum (n x_i - sum x)^2 = n^2 sum (x_i - mean)^2 = n^3 variance
        return linMul(flat.fn('sqrt', sq), 1 / (ls.length * Math.sqrt(ls.length)), pos);
      }
      case 'strictLex':
      case 'lex':
      case 'lexicographic': {
        // x <lex y (strictLex) or x <=lex y: the first difference is smaller in x.
        const strict = fn === 'strictLex';
        const xv = this.leaves(args[0]);
        const yv = this.leaves(args[1]);
        if (xv.length !== yv.length) fail(`${fn} needs two arrays of the same size`, pos);
        if (![...xv, ...yv].some((v) => isLinear(v) || v instanceof CPConstraint)) {
          for (let i = 0; i < xv.length; i++) {
            const [a, b] = [Number(xv[i]), Number(yv[i])];
            if (a !== b) return a < b ? 1 : 0;
          }
          return strict ? 0 : 1;
        }
        const xs = xv.map((x) => this.linear(x, pos));
        const ys = yv.map((y) => this.linear(y, pos));
        let prefix: CPCons = { k: 'const', value: true };
        let c: CPCons = { k: 'const', value: true };
        for (let i = 0; i < xs.length; i++) {
          c = { k: 'and', a: c, b: { k: 'imp', a: prefix, b: { k: 'cmp', op: '<=', l: xs[i], r: ys[i] } } };
          prefix = { k: 'and', a: prefix, b: { k: 'cmp', op: '=', l: xs[i], r: ys[i] } };
        }
        // Strict: not all equal.
        if (strict) c = { k: 'and', a: c, b: { k: 'not', a: prefix } };
        return new CPConstraint(c);
      }
      case 'strong':
      case 'inferred':
        // Hints to CP Optimizer (stronger inference, inferred variables): no restriction.
        return new CPConstraint({ k: 'const', value: true });
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
        if (n === undefined) return Math.floor(random() * 2147483647);
        if (typeof n !== 'number') fail('rand(n) needs a number', pos);
        return Math.floor(random() * n);
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
        // pack(load, where, size[, used]): load[b] = sum of size[i] over the items with where[i] = b
        const [loadArr, whereArr, sizeArr, used] = args;
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
        if (used !== undefined) {
          // used = the number of bins with a non-zero load
          const nonzero = new LinExpr();
          for (const l of loadArr.items) nonzero.addScaled(this.linear(new CPConstraint({ k: 'cmp', op: '!=', l: this.linear(l, pos), r: 0 }), pos), 1);
          c = { k: 'and', a: c, b: { k: 'cmp', op: '=', l: this.linear(used, pos), r: nonzero } };
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
        const v: Linear =
          fn === 'startOf' ? a.start : fn === 'endOf' ? a.end : fn === 'lengthOf' && (a.intensity || a.breakable) ? linAdd(a.end, a.start, -1) : a.duration;
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
        if (args[0] instanceof Sequence) return this.noOverlapSequence(args[0], args[1], args[2], pos);
        const acts = this.leaves(args[0]).map((a) => this.activityArg(a, pos));
        const res = new Resource(`noOverlap#${++this.noOverlaps}`, 'unary', 1, 0);
        return this.usesAll(acts.map((act) => ({ act, height: 1 })), res, pos);
      }
      case 'alternative':
        return this.alternative(args, pos);
      case 'span':
        return this.span(args, pos);
      case 'synchronize': {
        const a = this.activityArg(args[0], pos);
        let c: CPCons = { k: 'const', value: true };
        for (const b of this.leaves(args[1]).map((x) => this.activityArg(x, pos))) {
          const same: CPCons = { k: 'and', a: { k: 'cmp', op: '=', l: b.start, r: a.start }, b: { k: 'cmp', op: '=', l: b.end, r: a.end } };
          c = { k: 'and', a: c, b: { k: 'imp', a: this.presentCons([a, b]), b: same } };
        }
        return new CPConstraint(c);
      }
      case 'first':
      case 'last':
      case 'before':
      case 'prev':
        if (args[0] instanceof Sequence) return this.sequenceOrder(fn, args[0], args.slice(1), pos);
        return undefined;
      case 'typeOfNext':
      case 'startOfNext':
      case 'endOfNext':
      case 'sizeOfNext':
      case 'lengthOfNext':
      case 'typeOfPrev':
      case 'startOfPrev':
      case 'endOfPrev':
      case 'sizeOfPrev':
      case 'lengthOfPrev':
        if (!(args[0] instanceof Sequence)) fail(`${fn} needs a sequence variable`, pos);
        return this.neighbour(fn, args[0], args.slice(1), pos);
      case 'forbidStart':
      case 'forbidEnd':
      case 'forbidExtent': {
        const a = this.activityArg(args[0], pos);
        const f = args[1];
        if (!(f instanceof StepFunction)) fail(`${fn} needs a stepFunction`, pos);
        let c: CPCons = { k: 'const', value: true };
        for (const [from, to] of f.zeros()) {
          // start / end / the whole interval outside [from, to)
          const out: CPCons =
            fn === 'forbidStart'
              ? { k: 'or', a: { k: 'cmp', op: '<', l: a.start, r: from }, b: { k: 'cmp', op: '>=', l: a.start, r: to } }
              : fn === 'forbidEnd'
                ? { k: 'or', a: { k: 'cmp', op: '<=', l: a.end, r: from }, b: { k: 'cmp', op: '>', l: a.end, r: to } }
                : { k: 'or', a: { k: 'cmp', op: '<=', l: a.end, r: from }, b: { k: 'or', a: { k: 'cmp', op: '>=', l: a.start, r: to }, b: { k: 'cmp', op: '=', l: a.end, r: a.start } } };
          c = { k: 'and', a: c, b: out };
        }
        return new CPConstraint({ k: 'imp', a: this.presentCons([a]), b: c });
      }
      case 'addBreak':
      case 'addPeriodicBreak': {
        // OPL 3 resource breaks: addBreak(r, from, to), addPeriodicBreak(r, from, length, period, until).
        const r = args[0];
        if (!(r instanceof Resource)) fail(`${fn} needs a resource`, pos);
        const n = (k: number) => (typeof args[k] === 'number' ? (args[k] as number) : fail(`${fn}: argument ${k + 1} must be a number`, pos));
        if (fn === 'addBreak') r.breaks.push([n(1), n(2)]);
        else {
          const [from, len, period, until] = [n(1), n(2), n(3), n(4)];
          if (period <= 0) fail('addPeriodicBreak needs a positive period', pos);
          for (let t = from; t < until; t += period) r.breaks.push([t, Math.min(t + len, until)]);
        }
        return new CPConstraint({ k: 'const', value: true });
      }
      case 'pulse':
      case 'step':
      case 'stepAtStart':
      case 'stepAtEnd':
        return this.cumulTerm(fn, args, pos);
      case 'heightAtStart':
      case 'heightAtEnd': {
        // The contribution of a to f at its start (pulses, steps at start) or end (steps).
        const a = this.activityArg(args[0], pos);
        const f = args[1];
        if (!(f instanceof CumulExpr)) fail(`${fn} needs an interval and a cumul function`, pos);
        const atStart = fn === 'heightAtStart';
        let sum: Linear = 0;
        for (const t of f.terms) if (t.act === a && (atStart ? t.kind === 'pulse' || t.at === 'start' : t.kind === 'step')) sum = linAdd(sum, t.height, 1);
        const dval = args[2] === undefined ? 0 : args[2];
        if (this.phase === 'post') return a.presence && dvarValue(a.presence) === 0 ? dval : this.solvedValue(sum);
        return this.presentOr(a, sum, this.linear(dval, pos), pos);
      }
      case 'cumulFunctionValue':
      case 'stateFunctionValue': {
        const f = args[0];
        const t = args[1];
        if (typeof t !== 'number') fail(`${fn} needs a time`, pos);
        if (this.phase !== 'post') fail(`${fn} is only available after solving`, pos);
        if (fn === 'cumulFunctionValue') {
          if (!(f instanceof CumulExpr)) fail('cumulFunctionValue needs a cumul function', pos);
          return cumulValue(this.solvedCumul(f), t);
        }
        if (!(f instanceof StateFunction)) fail('stateFunctionValue needs a state function', pos);
        // -1: no state
        return this.solvedStates(f).find(([a, b]) => a <= t && t < b)?.[2] ?? -1;
      }
      case 'numberOfSegments':
      case 'segmentStart':
      case 'segmentEnd':
      case 'segmentValue': {
        if (this.phase !== 'post') fail(`${fn} is only available after solving`, pos);
        const f = args[0];
        const segs =
          f instanceof CumulExpr
            ? cumulSegments(this.solvedCumul(f), INTERVAL_MAX)
            : f instanceof StateFunction
              ? this.withGaps(this.solvedStates(f))
              : fail(`${fn} needs a cumul function or a state function`, pos);
        if (fn === 'numberOfSegments') return segs.length;
        const i = args[1];
        if (typeof i !== 'number' || !Number.isInteger(i) || i < 0 || i >= segs.length) fail(`${fn}: there is no segment ${String(i)} (segments 0..${segs.length - 1})`, pos);
        const [a, b, v] = segs[i];
        return fn === 'segmentStart' ? a : fn === 'segmentEnd' ? b : v;
      }
      case 'startEval':
      case 'endEval':
      case 'sizeEval':
      case 'lengthEval': {
        const a = this.activityArg(args[0], pos);
        const F = args[1];
        const fun =
          F instanceof PwlFunction
            ? { at: (x: number) => F.at(x), points: F.bps, isInt: false }
            : F instanceof StepFunction
              ? { at: (x: number) => F.valueAt(x), points: F.points, isInt: F.values.every(Number.isInteger) }
              : fail(`${fn} needs an interval and a piecewise-linear or step function`, pos);
        const x: Linear = fn === 'startEval' ? a.start : fn === 'endEval' ? a.end : fn === 'lengthEval' ? linAdd(a.end, a.start, -1) : a.duration;
        const dval = args[2] === undefined ? 0 : args[2];
        if (this.phase === 'post') return a.presence && dvarValue(a.presence) === 0 ? dval : fun.at(this.solvedValue(x));
        const z = typeof x === 'number' ? fun.at(x) : this.flat(pos).func(fun.at, fun.points, x, fun.isInt, `${fn}(${a.name})`);
        return this.presentOr(a, z, this.linear(dval, pos), pos);
      }
      case 'overlapLength': {
        // max(0, min(ends) - max(starts)) when present, absVal otherwise
        const a = this.activityArg(args[0], pos);
        const b = typeof args[1] === 'number' ? null : this.activityArg(args[1], pos);
        const fixedArg = (i: number) => (typeof args[i] === 'number' ? (args[i] as number) : fail('overlapLength(a, start, end[, absVal]) needs a fixed start and end', pos));
        const [s2, e2]: Linear[] = b ? [b.start, b.end] : [fixedArg(1), fixedArg(2)];
        const absVal = (b ? args[2] : args[3]) ?? 0;
        if (this.phase === 'post') {
          if ((a.presence && dvarValue(a.presence) === 0) || (b?.presence && dvarValue(b.presence) === 0)) return absVal;
          return Math.max(0, Math.min(a.end.value, this.solvedValue(e2)) - Math.max(a.start.value, this.solvedValue(s2)));
        }
        const flat = this.flat(pos);
        const len = linAdd(flat.minmax([a.end, e2], true), flat.minmax([a.start, s2], false), -1);
        const d = this.linear(absVal, pos);
        let v: Linear = flat.minmax([0, len], false);
        v = this.presentOr(a, v, d, pos);
        return b ? this.presentOr(b, v, d, pos) : v;
      }
      case 'isomorphism':
        return this.isomorphism(args, pos);
      case 'sameSequence':
      case 'sameCommonSubsequence':
        return this.sameSequence(fn === 'sameSequence', args, pos);
      case 'alwaysEqual':
      case 'alwaysConstant':
      case 'alwaysNoState':
      case 'alwaysIn':
        return this.alwaysCons(fn, args, pos);
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

  /** All of the activities are present. */
  private presentCons(acts: Activity[]): CPCons {
    let c: CPCons = { k: 'const', value: true };
    for (const a of acts) if (a.presence) c = { k: 'and', a: c, b: { k: 'cmp', op: '=', l: a.presence, r: 1 } };
    return c;
  }

  private presenceLin(a: Activity): Linear {
    return a.presence ?? 1;
  }

  /** alternative(a, B[, c]): a is present iff c members of B are, and they coincide with it. */
  private alternative(args: Value[], pos: SourcePos): CPConstraint {
    const a = this.activityArg(args[0], pos);
    const bs = this.leaves(args[1]).map((x) => this.activityArg(x, pos));
    const card = args[2] === undefined ? 1 : this.linear(args[2], pos);
    const sum = new LinExpr();
    for (const b of bs) sum.addScaled(this.presenceLin(b), 1);
    const want = a.presence ? (typeof card === 'number' ? linMul(card, a.presence, pos) : this.flat(pos).mul(card, a.presence)) : card;
    let c: CPCons = { k: 'cmp', op: '=', l: sum, r: want };
    for (const b of bs) {
      const same: CPCons = { k: 'and', a: { k: 'cmp', op: '=', l: b.start, r: a.start }, b: { k: 'cmp', op: '=', l: b.end, r: a.end } };
      c = { k: 'and', a: c, b: b.presence ? { k: 'imp', a: { k: 'cmp', op: '=', l: b.presence, r: 1 }, b: same } : same };
    }
    return new CPConstraint(c);
  }

  /** span(a, B): a is present iff some member of B is, and covers exactly the present ones. */
  private span(args: Value[], pos: SourcePos): CPConstraint {
    const a = this.activityArg(args[0], pos);
    const bs = this.leaves(args[1]).map((x) => this.activityArg(x, pos));
    if (!bs.length) return new CPConstraint(a.presence ? { k: 'cmp', op: '=', l: a.presence, r: 0 } : { k: 'const', value: false });
    const flat = this.flat(pos);
    let any: CPCons = { k: 'const', value: false };
    for (const b of bs) any = b.presence ? { k: 'or', a: any, b: { k: 'cmp', op: '=', l: b.presence, r: 1 } } : { k: 'const', value: true };
    let c: CPCons = a.presence ? { k: 'equiv', a: { k: 'cmp', op: '=', l: a.presence, r: 1 }, b: any } : any;
    // Absent members do not count: their start reads as +big, their end as -big.
    const big = CP_MAXINT >> 2;
    const starts = bs.map((b) => (b.presence ? linAdd(flat.mul(b.presence, linAdd(b.start, -big, 1)), big, 1) : b.start));
    const ends = bs.map((b) => (b.presence ? linAdd(flat.mul(b.presence, linAdd(b.end, big, 1)), -big, 1) : b.end));
    const cover: CPCons = {
      k: 'and',
      a: { k: 'cmp', op: '=', l: a.start, r: flat.minmax(starts, true) },
      b: { k: 'cmp', op: '=', l: a.end, r: flat.minmax(ends, false) },
    };
    c = { k: 'and', a: c, b: a.presence ? { k: 'imp', a: { k: 'cmp', op: '=', l: a.presence, r: 1 }, b: cover } : cover };
    return new CPConstraint(c);
  }

  /**
   * noOverlap(sequence[, transition distances[, isDirect]]): no two present
   * intervals overlap, and they run in the sequence's order.  A transition
   * distance M[type(a)][type(b)] separates a from every later b (from the next
   * one only when isDirect).
   */
  private noOverlapSequence(seq: Sequence, matrix: Value | undefined, direct: Value | undefined, pos: SourcePos): CPConstraint {
    const res = new Resource(`noOverlap#${++this.noOverlaps}`, 'unary', 1, 0);
    const c = this.usesAll(seq.acts.map((act) => ({ act, height: 1 })), res, pos).c;
    const dist = matrix === undefined ? () => 0 : this.transitionDistance(matrix, pos);
    const isDirect = direct !== undefined && this.truthyValue(direct);
    const state = this.sequenceState(seq);
    state.overlaps.push({ dist, isDirect });
    // Without order functions or direct transitions the order is the time order:
    // pairwise disjunctions with the distances, no rank variables.
    if (!isDirect && !state.ranks) return new CPConstraint({ k: 'and', a: c, b: this.timeDisjunctions(seq, dist) });
    // Creating the ranks links every registered noOverlap, this one included.
    if (state.ranks) this.linkOrder(seq, { dist, isDirect }, pos);
    else this.ranks(seq, pos);
    return new CPConstraint(c);
  }

  /** Present a, b: a + d(a, b) before b, or b + d(b, a) before a. */
  private timeDisjunctions(seq: Sequence, dist: (a: number, b: number) => number): CPCons {
    let c: CPCons = { k: 'const', value: true };
    const acts = seq.acts;
    for (let i = 0; i < acts.length; i++) {
      for (let j = i + 1; j < acts.length; j++) {
        const dij = dist(seq.types[i], seq.types[j]);
        const dji = dist(seq.types[j], seq.types[i]);
        if (!dij && !dji) continue;
        const [a, b] = [acts[i], acts[j]];
        const order: CPCons = {
          k: 'or',
          a: { k: 'cmp', op: '<=', l: linAdd(a.end, dij, 1), r: b.start },
          b: { k: 'cmp', op: '<=', l: linAdd(b.end, dji, 1), r: a.start },
        };
        c = { k: 'and', a: c, b: { k: 'imp', a: this.presentCons([a, b]), b: order } };
      }
    }
    return c;
  }

  private truthyValue(v: Value): boolean {
    return typeof v === 'number' ? v !== 0 : typeof v === 'string' ? v !== '' : !!v;
  }

  /** A transition distance matrix: int M[T][T] or a set of <from, to, distance> tuples. */
  private transitionDistance(m: Value, pos: SourcePos): (a: number, b: number) => number {
    return this.transitionTable(m, pos).dist;
  }

  /** A transition matrix (a 2-D array, or <from, to, distance> tuples: missing pairs 0, the largest of duplicates). */
  transitionTable(m: Value, pos: SourcePos): { dist: (a: number, b: number) => number; states: number[] } {
    if (m instanceof OplArray) {
      const states = m.index instanceof OplRange ? m.items.map((_, i) => (m.index as OplRange).lo + i) : [];
      const dist = (a: number, b: number) => {
        const row = m.items[m.index.indexOf(a)];
        if (!(row instanceof OplArray)) fail(`no transition distances for type ${a}`, pos);
        const v = row.items[row.index.indexOf(b)];
        return typeof v === 'number' ? v : fail(`no transition distance from type ${a} to ${b}`, pos);
      };
      return { dist, states };
    }
    const elems = elementsOf(m);
    if (!elems) fail('a transition distance needs a matrix or a set of <from, to, distance> tuples', pos);
    const table = new Map<string, number>();
    const states = new Set<number>();
    for (const t of elems) {
      if (!(t instanceof OplTuple) || t.values.length < 3) fail('transition tuples are <from, to, distance>', pos);
      const key = `${t.values[0]},${t.values[1]}`;
      table.set(key, Math.max(table.get(key) ?? -Infinity, Number(t.values[2])));
      for (const v of t.values.slice(0, 2)) if (typeof v === 'number') states.add(v);
    }
    return { dist: (a, b) => table.get(`${a},${b}`) ?? 0, states: [...states] };
  }

  private seqIndex(seq: Sequence, v: Value, pos: SourcePos): number {
    const a = this.activityArg(v, pos);
    const i = seq.acts.indexOf(a);
    if (i < 0) fail(`${a.name} is not in sequence ${seq.name}`, pos);
    return i;
  }

  private readonly sequenceStates = new WeakMap<Sequence, SequenceState>();
  /** Rank variables of every sequence modelled so far (the search labels them first). */
  private readonly rankSets: DVar[][] = [];

  /** The sequence ranks among the given problem variables. */
  rankVarsOf(vars: DVar[]): DVar[] {
    return this.rankSets.filter((rs) => rs.every((v) => vars[v.id] === v)).flat();
  }

  private sequenceState(seq: Sequence): SequenceState {
    let st = this.sequenceStates.get(seq);
    if (!st) this.sequenceStates.set(seq, (st = { ranks: null, overlaps: [] }));
    return st;
  }

  /**
   * The permutation of a sequence: rank[i] in 0..n-1, all different; the
   * present intervals take the ranks 0..count-1 (absent ones the others, in
   * index order), next[i][j] = j directly follows i, first / last flags.
   */
  private ranks(seq: Sequence, pos: SourcePos): RankModel {
    const st = this.sequenceState(seq);
    if (st.ranks) return st.ranks;
    const flat = this.flat(pos);
    const acts = seq.acts;
    const n = acts.length;
    const post = (c: CPCons) => flat.h.define({ k: 'post', cons: c });
    const rank = acts.map((a) => flat.h.newVar(0, Math.max(0, n - 1), true, `rank(${seq.name},${a.name})`));
    const count = new LinExpr();
    for (const a of acts) count.addScaled(this.presenceLin(a), 1);
    if (n > 1) post({ k: 'alldiff', xs: rank, level: 'default' });
    const present = (a: Activity): CPCons => (a.presence ? { k: 'cmp', op: '=', l: a.presence, r: 1 } : { k: 'const', value: true });
    acts.forEach((a, i) => {
      const inside: CPCons = { k: 'cmp', op: '<=', l: rank[i], r: linAdd(count, -1, 1) };
      if (!a.presence) return post(inside);
      post({ k: 'equiv', a: present(a), b: inside });
      // Absent intervals keep their index order (no symmetric permutations).
      acts.forEach((b, j) => {
        if (j <= i || !b.presence) return;
        post({ k: 'imp', a: { k: 'and', a: { k: 'cmp', op: '=', l: a.presence!, r: 0 }, b: { k: 'cmp', op: '=', l: b.presence, r: 0 } }, b: { k: 'cmp', op: '<', l: rank[i], r: rank[j] } });
      });
    });
    const next = acts.map((a, i) =>
      acts.map((b, j) => {
        const v = flat.h.newVar(0, i === j ? 0 : 1, true, `next(${a.name},${b.name})`);
        if (i !== j) {
          const follows: CPCons = { k: 'and', a: { k: 'and', a: present(a), b: present(b) }, b: { k: 'cmp', op: '=', l: rank[j], r: linAdd(rank[i], 1, 1) } };
          post({ k: 'equiv', a: { k: 'cmp', op: '=', l: v, r: 1 }, b: follows });
        }
        return v;
      }),
    );
    const last = acts.map((a, i) => linAdd(this.presenceLin(a), next[i].reduce((e, v) => e.addScaled(v, 1), new LinExpr()), -1));
    const first = acts.map((a, i) => linAdd(this.presenceLin(a), acts.reduce((e, _, j) => e.addScaled(next[j][i], 1), new LinExpr()), -1));
    st.ranks = { rank, next, first, last, count };
    this.rankSets.push(rank);
    // noOverlap constraints posted before the ranks existed now follow them too.
    for (const o of st.overlaps) this.linkOrder(seq, o, pos);
    return st.ranks;
  }

  /** noOverlap ties the sequence order to time: a ranked before b ends (plus its distance) before b starts. */
  private linkOrder(seq: Sequence, o: { dist: (a: number, b: number) => number; isDirect: boolean }, pos: SourcePos): void {
    const { rank, next } = this.ranks(seq, pos);
    const flat = this.flat(pos);
    const acts = seq.acts;
    acts.forEach((a, i) => {
      acts.forEach((b, j) => {
        if (i === j) return;
        const d = o.dist(seq.types[i], seq.types[j]);
        const before: CPCons = { k: 'and', a: this.presentCons([a, b]), b: { k: 'cmp', op: '<', l: rank[i], r: rank[j] } };
        flat.h.define({ k: 'post', cons: { k: 'imp', a: before, b: { k: 'cmp', op: '<=', l: a.end, r: b.start } } });
        if (d && o.isDirect) {
          flat.h.define({ k: 'post', cons: { k: 'imp', a: { k: 'cmp', op: '=', l: next[i][j], r: 1 }, b: { k: 'cmp', op: '<=', l: linAdd(a.end, d, 1), r: b.start } } });
        } else if (d) {
          flat.h.define({ k: 'post', cons: { k: 'imp', a: before, b: { k: 'cmp', op: '<=', l: linAdd(a.end, d, 1), r: b.start } } });
        }
      });
    });
  }

  /** first / last / before / prev: constraints on the sequence's permutation. */
  private sequenceOrder(fn: string, seq: Sequence, args: Value[], pos: SourcePos): Value {
    if (this.phase === 'post') {
      const order = this.solvedOrder(seq);
      const at = (v: Value) => order.indexOf(this.activityArg(v, pos));
      const [x, y] = [at(args[0]), args[1] === undefined ? -1 : at(args[1])];
      if (fn === 'first') return x < 0 || x === 0 ? 1 : 0;
      if (fn === 'last') return x < 0 || x === order.length - 1 ? 1 : 0;
      if (x < 0 || y < 0) return 1;
      return fn === 'before' ? (x < y ? 1 : 0) : y === x + 1 ? 1 : 0;
    }
    const i = this.seqIndex(seq, args[0], pos);
    const a = seq.acts[i];
    const { rank, next, count } = this.ranks(seq, pos);
    if (fn === 'first') return new CPConstraint({ k: 'imp', a: this.presentCons([a]), b: { k: 'cmp', op: '=', l: rank[i], r: 0 } });
    if (fn === 'last') return new CPConstraint({ k: 'imp', a: this.presentCons([a]), b: { k: 'cmp', op: '=', l: rank[i], r: linAdd(count, -1, 1) } });
    const j = this.seqIndex(seq, args[1], pos);
    const b = seq.acts[j];
    if (fn === 'before') return new CPConstraint({ k: 'imp', a: this.presentCons([a, b]), b: { k: 'cmp', op: '<', l: rank[i], r: rank[j] } });
    return new CPConstraint({ k: 'imp', a: this.presentCons([a, b]), b: { k: 'cmp', op: '=', l: next[i][j], r: 1 } });
  }

  /** The present intervals of a solved sequence, in sequence order (ranks, else start times). */
  private solvedOrder(seq: Sequence): Activity[] {
    const st = this.sequenceStates.get(seq);
    const rankOf = (a: Activity) => (st?.ranks ? Number(dvarValue(st.ranks.rank[seq.acts.indexOf(a)])) : 0);
    return seq.acts
      .filter((a) => !a.presence || dvarValue(a.presence) === 1)
      .sort((x, y) => rankOf(x) - rankOf(y) || Number(dvarValue(x.start)) - Number(dvarValue(y.start)) || Number(dvarValue(x.end)) - Number(dvarValue(y.end)));
  }

  /** typeOfNext / startOfNext / ... / lengthOfPrev(sequence, a, lastValue, absentValue). */
  private neighbour(fn: string, seq: Sequence, args: Value[], pos: SourcePos): Value {
    const i = this.seqIndex(seq, args[0], pos);
    const a = seq.acts[i];
    const isNext = fn.endsWith('Next');
    const what = fn.slice(0, fn.length - 4);
    const value = (j: number): Linear => {
      const b = seq.acts[j];
      if (what === 'typeOf') return seq.types[j];
      if (what === 'startOf') return b.start;
      if (what === 'endOf') return b.end;
      if (what === 'lengthOf') return linAdd(b.end, b.start, -1);
      return b.duration;
    };
    const lastVal = args[1] === undefined ? (what === 'typeOf' ? seq.types[i] : 0) : this.linear(args[1], pos);
    const absVal = args[2] === undefined ? 0 : this.linear(args[2], pos);
    if (this.phase === 'post') {
      if (a.presence && dvarValue(a.presence) === 0) return absVal;
      const order = this.solvedOrder(seq);
      const at = order.indexOf(a) + (isNext ? 1 : -1);
      if (at < 0 || at >= order.length) return lastVal;
      const j = seq.acts.indexOf(order[at]);
      const b = seq.acts[j];
      const num = (x: DVar | number) => (typeof x === 'number' ? x : Number(dvarValue(x)));
      if (what === 'typeOf') return seq.types[j];
      if (what === 'startOf') return num(b.start);
      if (what === 'endOf') return num(b.end);
      if (what === 'lengthOf') return num(b.end) - num(b.start);
      return num(b.duration);
    }
    const flat = this.flat(pos);
    const { next: n, last, first } = this.ranks(seq, pos);
    let e: Linear = 0;
    seq.acts.forEach((_, j) => {
      if (j === i) return;
      const link = isNext ? n[i][j] : n[j][i];
      const v = value(j);
      e = linAdd(e, typeof v === 'number' ? linMul(v, link, pos) : flat.mul(link, v), 1);
    });
    const end = isNext ? last[i] : first[i];
    e = linAdd(e, typeof lastVal === 'number' ? linMul(lastVal, end, pos) : flat.mul(flat.atom(end), lastVal), 1);
    const absent = linAdd(1, this.presenceLin(a), -1);
    e = linAdd(e, typeof absVal === 'number' ? linMul(absVal, absent, pos) : flat.mul(flat.atom(absent), absVal), 1);
    return e;
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

  /** f <= h, f >= h for a cumul function, and sums and differences of cumul functions. */
  private cumulOp(op: string, l: Value, r: Value, pos: SourcePos): Value {
    if (op === '+' || op === '-') {
      if (!(l instanceof CumulExpr) || !(r instanceof CumulExpr)) fail('a cumul function can only be added to or subtracted from a cumul function', pos);
      return new CumulExpr([...l.terms, ...(op === '-' ? this.negCumul(r, pos).terms : r.terms)]);
    }
    const [f, h, flipped] = l instanceof CumulExpr ? [l, r, false] : [r as CumulExpr, l, true];
    const le = flipped ? op === '>=' : op === '<=';
    const ge = flipped ? op === '<=' : op === '>=';
    if ((!le && !ge) || typeof h !== 'number') fail('a cumul function can only be bounded by a constant: f <= h or f >= h', pos);
    return this.cumulCons(f, le ? -Infinity : h, le ? h : Infinity, { k: 'all' });
  }

  private cumuls = 0;

  /** lo <= f <= hi on the window (f >= 0 holds everywhere). */
  private cumulCons(f: CumulExpr, lo: number, hi: number, window: FunctionWindow): CPConstraint {
    if (this.phase === 'post') return new CPConstraint({ k: 'const', value: true });
    // Non-negative interval pulses under a capacity: a discrete resource (with edge finding).
    const plain = f.terms.every((t) => t.kind === 'pulse' && t.act && typeof t.height === 'number' && t.height >= 0);
    if (window.k === 'all' && lo <= 0 && isFinite(hi) && plain) {
      const res = new Resource(`cumul#${++this.cumuls}`, 'discrete', hi, 0);
      let c: CPCons = { k: 'const', value: true };
      for (const t of f.terms) c = { k: 'and', a: c, b: { k: 'uses', how: 'requires', act: t.act!, res, amount: t.height, presence: t.act!.presence } };
      return new CPConstraint(c);
    }
    return new CPConstraint({ k: 'cumul', terms: f.terms, lo, hi, window });
  }

  /** pulse(a, h), pulse(a, hmin, hmax), pulse(u, v, h), step(u, h), stepAtStart / stepAtEnd(a, h | hmin, hmax). */
  private cumulTerm(fn: string, args: Value[], pos: SourcePos): CumulExpr {
    const n = (i: number): number => (typeof args[i] === 'number' ? (args[i] as number) : fail(`${fn}: argument ${i + 1} must be a number`, pos));
    if (fn === 'step') return new CumulExpr([{ kind: 'step', act: null, at: 'start', from: n(0), to: Infinity, height: n(1) }]);
    if (fn === 'pulse' && !(args[0] instanceof Activity)) {
      if (n(1) < n(0)) fail('pulse(u, v, h) needs u <= v', pos);
      return new CumulExpr([{ kind: 'pulse', act: null, at: 'start', from: n(0), to: n(1), height: n(2) }]);
    }
    const act = this.activityArg(args[0], pos);
    let height: Linear;
    if (args.length >= 3) {
      // A height chosen in [hmin, hmax]
      const [lo, hi] = [n(1), n(2)];
      if (lo > hi) fail(`${fn}(a, hmin, hmax) needs hmin <= hmax`, pos);
      height = lo === hi ? lo : this.flat(pos).h.newVar(lo, hi, true, `${fn}(${act.name}).height`);
    } else {
      const h = args[1] === undefined ? 1 : this.linear(args[1], pos);
      height = typeof h === 'number' ? h : this.flat(pos).atom(h, `${fn}(${act.name}).height`);
    }
    if (height instanceof DVar) this.heightVars.set(height.id, height);
    return new CumulExpr([{ kind: fn === 'pulse' ? 'pulse' : 'step', act, at: fn === 'stepAtEnd' ? 'end' : 'start', from: 0, to: 0, height }]);
  }

  /** Variables of cumul function heights, for their values after solving. */
  private readonly heightVars = new Map<number, DVar>();

  private negCumul(f: CumulExpr, pos: SourcePos): CumulExpr {
    return new CumulExpr(f.terms.map((t) => ({ ...t, height: typeof t.height === 'number' ? -t.height : linMul(t.height, -1, pos) })));
  }

  /** The value of an expression over interval bounds and heights, after solving. */
  private solvedValue(v: Linear): number {
    if (typeof v === 'number') return v;
    if (v instanceof DVar) return v.value;
    let sum = v.constant;
    for (const [id, c] of v.terms) {
      const x = this.heightVars.get(id) ?? this.cp?.dvar(id);
      if (!x) fail('internal: a variable without a solution value');
      sum += c * x.value;
    }
    return sum;
  }

  /** v when a is present, d otherwise. */
  private presentOr(a: Activity, v: Linear, d: Linear, pos: SourcePos): Linear {
    if (!a.presence) return v;
    const diff = linAdd(v, d, -1);
    const scaled = typeof diff === 'number' ? linMul(a.presence, diff, pos) : this.flat(pos).mul(a.presence, diff);
    return linAdd(scaled, d, 1);
  }

  private solvedCumul(f: CumulExpr): { step: boolean; start: number; end: number; height: number; present: boolean }[] {
    return f.terms.map((t) => {
      const height = this.solvedValue(t.height);
      if (!t.act) return { step: t.kind === 'step', start: t.from, end: t.to, height, present: true };
      const present = !t.act.presence || dvarValue(t.act.presence) === 1;
      const start = t.kind === 'step' && t.at === 'end' ? t.act.end.value : t.act.start.value;
      return { step: t.kind === 'step', start, end: t.act.end.value, height, present };
    });
  }

  /** The state segments [start, end, state] of a solved state function. */
  private solvedStates(f: StateFunction): [number, number, number][] {
    const ws: StateFixed[] = [];
    for (const w of f.windows) {
      const win = w.window;
      if (win.k === 'interval' && win.act.presence && dvarValue(win.act.presence) === 0) continue;
      const [s, e] = win.k === 'all' ? [-INTERVAL_MAX, INTERVAL_MAX] : win.k === 'fixed' ? [win.from, win.to] : [win.act.start.value, win.act.end.value];
      ws.push({ kind: w.kind, s, e, v: w.kind === 'equal' ? w.value : (w.state?.value ?? 0), lo: w.lo, hi: w.hi, aligns: w.aligns, aligne: w.aligne });
    }
    return stateSegments(ws, (a, b) => f.distance(a, b)) ?? [];
  }

  /** State segments with the stretches without state (-1) between them, from -IntervalMax to IntervalMax. */
  private withGaps(segs: [number, number, number][]): [number, number, number][] {
    const out: [number, number, number][] = [];
    let t = -INTERVAL_MAX;
    for (const [a, b, v] of segs) {
      if (a > t) out.push([t, a, -1]);
      out.push([a, b, v]);
      t = b;
    }
    if (t < INTERVAL_MAX) out.push([t, INTERVAL_MAX, -1]);
    return out;
  }

  /** alwaysEqual / alwaysConstant / alwaysNoState / alwaysIn on a state function, alwaysIn on a cumul function. */
  private alwaysCons(fn: string, args: Value[], pos: SourcePos): CPConstraint {
    const f = args[0];
    const n = (i: number): number => (typeof args[i] === 'number' ? (args[i] as number) : fail(`${fn}: argument ${i + 1} must be a number`, pos));
    const byAct = args[1] instanceof Activity;
    const window: FunctionWindow = byAct ? { k: 'interval', act: args[1] as Activity } : { k: 'fixed', from: n(1), to: n(2) };
    const at = byAct ? 2 : 3;
    if (!byAct && n(2) < n(1)) fail(`${fn}: the window needs start <= end`, pos);
    if (fn === 'alwaysIn' && f instanceof CumulExpr) {
      if (n(at) > n(at + 1)) fail('alwaysIn needs hmin <= hmax', pos);
      return this.cumulCons(f, n(at), n(at + 1), window);
    }
    if (!(f instanceof StateFunction)) fail(`${fn} needs a state function${fn === 'alwaysIn' ? ' or a cumul function' : ''}`, pos);
    const flag = (i: number) => args[i] !== undefined && this.truthyValue(args[i]);
    const w: StateWindow = { kind: 'none', window, value: 0, lo: 0, hi: 0, aligns: false, aligne: false };
    if (fn === 'alwaysEqual') {
      const v = n(at);
      if (!Number.isInteger(v) || v < 0) fail('alwaysEqual needs a non-negative integer state', pos);
      Object.assign(w, { kind: 'equal', value: v, aligns: flag(at + 1), aligne: flag(at + 2) });
    } else if (fn === 'alwaysConstant') Object.assign(w, { kind: 'constant', aligns: flag(at), aligne: flag(at + 1) });
    else if (fn === 'alwaysIn') {
      if (n(at) > n(at + 1)) fail('alwaysIn needs vmin <= vmax', pos);
      Object.assign(w, { kind: 'in', lo: n(at), hi: n(at + 1) });
    }
    // The pairwise constraints and the check are made with the model (finishScheduling).
    if (this.phase === 'model') f.windows.push(w);
    return new CPConstraint({ k: 'const', value: true });
  }

  /** Indexes of a one-dimensional array (0-based for arrays built with all). */
  private arrayKeys(v: Value, n: number): number[] {
    if (v instanceof OplArray && v.items.length === n) {
      const set = v.index;
      if (set instanceof OplRange) return v.items.map((_, i) => set.lo + i);
      if (set instanceof OplSet && set.elems.every((k) => typeof k === 'number')) return set.elems as number[];
    }
    return [...Array(n).keys()];
  }

  /**
   * isomorphism(A, B[, M, v]): the present intervals of A and B match one to
   * one with the same start and end; M[i] is the index in A matched with B[i]
   * (v when B[i] is absent).
   */
  private isomorphism(args: Value[], pos: SourcePos): CPConstraint {
    const A = this.leaves(args[0]).map((a) => this.activityArg(a, pos));
    const B = this.leaves(args[1]).map((b) => this.activityArg(b, pos));
    const M = args[2] === undefined ? null : this.leaves(args[2]).map((m) => this.linear(m, pos));
    if (M && M.length !== B.length) fail('isomorphism: the map array needs one entry per interval of B', pos);
    if (this.phase === 'post') return new CPConstraint({ k: 'const', value: true });
    const absent = args[3] === undefined ? 0 : this.linear(args[3], pos);
    const keys = this.arrayKeys(args[0], A.length);
    const flat = this.flat(pos);
    const x = B.map((b) => A.map((a) => flat.h.newVar(0, 1, true, `isomorphism(${a.name},${b.name})`)));
    let c: CPCons = { k: 'const', value: true };
    const and = (d: CPCons) => (c = { k: 'and', a: c, b: d });
    B.forEach((b, i) => {
      const row = new LinExpr();
      for (const v of x[i]) row.addScaled(v, 1);
      and({ k: 'cmp', op: '=', l: row, r: this.presenceLin(b) });
      if (M) {
        const m = new LinExpr();
        x[i].forEach((v, j) => m.addScaled(v, keys[j]));
        const off = linAdd(1, this.presenceLin(b), -1);
        m.addScaled(typeof absent === 'number' || typeof off === 'number' ? linMul(off, absent, pos) : flat.mul(off, absent), 1);
        and({ k: 'cmp', op: '=', l: M[i], r: m });
      }
      A.forEach((a, j) => {
        const same: CPCons = { k: 'and', a: { k: 'cmp', op: '=', l: a.start, r: b.start }, b: { k: 'cmp', op: '=', l: a.end, r: b.end } };
        and({ k: 'imp', a: { k: 'cmp', op: '=', l: x[i][j], r: 1 }, b: same });
      });
    });
    A.forEach((a, j) => {
      const col = new LinExpr();
      for (const row of x) col.addScaled(row[j], 1);
      and({ k: 'cmp', op: '=', l: col, r: this.presenceLin(a) });
    });
    return new CPConstraint(c);
  }

  /**
   * sameSequence(s1, s2[, A1, A2]): A1[k] and A2[k] (by default the k-th
   * intervals of the sequences) have the same presence, and the present ones
   * come in the same order.  sameCommonSubsequence: only the pairs present in
   * both keep their order.
   */
  private sameSequence(same: boolean, args: Value[], pos: SourcePos): CPConstraint {
    const [s1, s2] = args;
    const name = same ? 'sameSequence' : 'sameCommonSubsequence';
    if (!(s1 instanceof Sequence) || !(s2 instanceof Sequence)) fail(`${name} needs two sequences`, pos);
    const A1 = args.length >= 4 ? this.leaves(args[2]).map((a) => this.activityArg(a, pos)) : s1.acts;
    const A2 = args.length >= 4 ? this.leaves(args[3]).map((a) => this.activityArg(a, pos)) : s2.acts;
    if (A1.length !== A2.length) fail(`${name} needs as many intervals in both sequences`, pos);
    const at = (seq: Sequence, a: Activity) => {
      const k = seq.acts.indexOf(a);
      if (k < 0) fail(`${a.name} is not an interval of the sequence ${seq.name}`, pos);
      return k;
    };
    const k1 = A1.map((a) => at(s1, a));
    const k2 = A2.map((a) => at(s2, a));
    if (this.phase === 'post') return new CPConstraint({ k: 'const', value: true });
    const r1 = this.ranks(s1, pos).rank;
    const r2 = this.ranks(s2, pos).rank;
    let c: CPCons = { k: 'const', value: true };
    if (same) {
      A1.forEach((a, k) => {
        if (a.presence || A2[k].presence) c = { k: 'and', a: c, b: { k: 'cmp', op: '=', l: this.presenceLin(a), r: this.presenceLin(A2[k]) } };
      });
    }
    for (let i = 0; i < A1.length; i++) {
      for (let j = i + 1; j < A1.length; j++) {
        const cond = this.presentCons(same ? [A1[i], A1[j]] : [A1[i], A1[j], A2[i], A2[j]]);
        const order: CPCons = {
          k: 'equiv',
          a: { k: 'cmp', op: '<', l: r1[k1[i]], r: r1[k1[j]] },
          b: { k: 'cmp', op: '<', l: r2[k2[i]], r: r2[k2[j]] },
        };
        c = { k: 'and', a: c, b: cond.k === 'const' ? order : { k: 'imp', a: cond, b: order } };
      }
    }
    return new CPConstraint(c);
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
          case 'lg':
          case 'distToInt':
          case 'standardDeviation':
          case 'startEval':
          case 'endEval':
          case 'sizeEval':
          case 'lengthEval':
          case 'floatValue':
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
      case 'stepwise':
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

/** The permutation model of a sequence variable (see Evaluator.ranks). */
interface RankModel {
  rank: DVar[];
  next: DVar[][];
  first: Linear[];
  last: Linear[];
  count: LinExpr;
}

interface SequenceState {
  ranks: RankModel | null;
  /** noOverlap constraints on the sequence, linked to the ranks once they exist. */
  overlaps: { dist: (a: number, b: number) => number; isDirect: boolean }[];
}

/** OPL's rand / srand: a seeded generator (mulberry32), shared with scripts. */
let randomState = 0x9e3779b9;
export function seedRandom(seed: number): void {
  randomState = (seed >>> 0) ^ 0x9e3779b9;
}
export function random(): number {
  randomState = (randomState + 0x6d2b79f5) | 0;
  let t = randomState;
  t = Math.imul(t ^ (t >>> 15), t | 1);
  t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
}
