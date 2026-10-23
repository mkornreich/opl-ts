/**
 * Constraint-programming values produced by the evaluator, and flattening of
 * non-linear expressions into auxiliary variables.
 *
 * Comparisons and logical combinations over decision variables evaluate to
 * CPConstraint objects (posted by the model, or reified into 0/1 variables
 * when used as numbers: meta-constraints).  Non-linear terms (x*y, abs(x),
 * a[x], ...) become auxiliary variables defined by a CPDef.
 */

import { fail, type SourcePos } from '../errors.js';
import { DVar, LinExpr, type Linear } from '../linear.js';
import type { Dom } from './domain.js';
import type { CountMode } from './propagators.js';

export const CP_MAXINT = 2147483647;
/** Bound used for float variables without finite bounds. */
export const CP_FLOAT_BOUND = 1e9;

export type CmpOp = '<=' | '<' | '>=' | '>' | '=' | '!=';

export class Activity {
  constructor(
    readonly name: string,
    readonly start: DVar,
    readonly end: DVar,
    readonly duration: DVar | number,
    readonly breakable: boolean,
    /** Optional interval variables (CP Optimizer): 0/1 presence. */
    readonly presence: DVar | null = null,
  ) {}
}

export type ResourceKind = 'unary' | 'discrete' | 'reservoir' | 'state' | 'alternative';

export class Resource {
  constructor(
    readonly name: string,
    readonly kind: ResourceKind,
    readonly capacity: number,
    readonly initial: number,
    /** Members of an AlternativeResources set. */
    readonly members: Resource[] = [],
    /** States of a StateResource (enum values are mapped to their ordinal). */
    readonly states: string[] | null = null,
  ) {}
}

export type CPCons =
  | { k: 'cmp'; op: CmpOp; l: Linear; r: Linear }
  | { k: 'and' | 'or' | 'imp' | 'equiv'; a: CPCons; b: CPCons }
  | { k: 'not'; a: CPCons }
  | { k: 'member'; x: Linear; values: number[] }
  | { k: 'const'; value: boolean }
  | { k: 'alldiff'; xs: Linear[]; level: string }
  | { k: 'count'; mode: CountMode; cards: Linear[]; values: number[]; base: Linear[] }
  /** sub: subCircuit (nodes may point to themselves to stay out of the circuit) */
  | { k: 'circuit'; xs: Linear[]; offset: number; sub?: boolean }
  | { k: 'table'; xs: Linear[]; tuples: number[][]; positive: boolean }
  | { k: 'uses'; how: 'requires' | 'consumes' | 'produces'; act: Activity; res: Resource; amount: Linear; presence: DVar | null };

export class CPConstraint {
  constructor(readonly c: CPCons) {}
}

export type CPDef =
  | { k: 'mul'; z: DVar; x: DVar; y: DVar }
  | { k: 'div' | 'mod' | 'realdiv'; z: DVar; x: DVar; y: DVar }
  | { k: 'abs'; z: DVar; x: DVar }
  | { k: 'fn'; fn: 'sqrt' | 'exp' | 'log'; z: DVar; x: DVar }
  | { k: 'minmax'; isMin: boolean; z: DVar; xs: DVar[] }
  | { k: 'element'; z: DVar; idx: DVar; keys: number[]; items: (DVar | number)[] }
  | { k: 'reify'; b: DVar; cons: CPCons }
  | { k: 'linear'; z: DVar; e: LinExpr }
  | { k: 'post'; cons: CPCons };

/** What the evaluator needs from the model (generation) or the live search. */
export interface CPHooks {
  newVar(lo: number, hi: number, isInt: boolean, name: string): DVar;
  define(def: CPDef): void;
  /** Finite bounds of a variable. */
  bounds(v: DVar): [number, number];
  /** Current domain during search; null while generating the model. */
  domain(v: DVar): Dom | null;
  dvar(id: number): DVar | undefined;
  /** Selection variables of an activity on the members of an AlternativeResources set. */
  selections: Map<Activity, Map<Resource, DVar[]>>;
}

export function isIntegral(e: Linear): boolean {
  if (typeof e === 'number') return Number.isInteger(e);
  if (e instanceof DVar) return e.isInt;
  return Number.isInteger(e.constant) && [...e.terms.values()].every((c) => Number.isInteger(c));
}

/** isIntegral, also checking that every variable is an integer variable. */
export function isIntegerExpr(e: Linear, vars: (id: number) => DVar | undefined): boolean {
  if (!(e instanceof LinExpr)) return isIntegral(e);
  if (!isIntegral(e)) return false;
  for (const id of e.terms.keys()) if (!vars(id)?.isInt) return false;
  return true;
}

export function linBounds(h: CPHooks, e: Linear, vars: (id: number) => DVar | undefined): [number, number] {
  if (typeof e === 'number') return [e, e];
  if (e instanceof DVar) return h.bounds(e);
  let lo = e.constant;
  let hi = e.constant;
  for (const [id, c] of e.terms) {
    if (c === 0) continue;
    const [a, b] = h.bounds(vars(id)!);
    lo += c > 0 ? c * a : c * b;
    hi += c > 0 ? c * b : c * a;
  }
  return [lo, hi];
}

/** Flattens expressions into auxiliary variables. */
export class Flattener {
  readonly vars: (id: number) => DVar | undefined;
  constructor(readonly h: CPHooks) {
    this.vars = (id) => h.dvar(id);
  }

  /** A variable (or constant) equal to e. */
  atom(e: Linear, name = 'expr'): DVar | number {
    if (typeof e === 'number' || e instanceof DVar) return e;
    const entries = [...e.terms].filter(([, c]) => c !== 0);
    if (entries.length === 0) return e.constant;
    if (entries.length === 1 && entries[0][1] === 1 && e.constant === 0) return this.vars(entries[0][0])!;
    const [lo, hi] = linBounds(this.h, e, this.vars);
    const z = this.h.newVar(lo, hi, isIntegerExpr(e, this.vars), name);
    this.h.define({ k: 'linear', z, e });
    return z;
  }

  private varAtom(e: Linear, name: string): DVar {
    const a = this.atom(e, name);
    if (typeof a !== 'number') return a;
    return this.h.newVar(a, a, Number.isInteger(a), String(a));
  }

  private isInt(e: Linear): boolean {
    return isIntegerExpr(e, this.vars);
  }

  mul(a: Linear, b: Linear): DVar {
    const x = this.varAtom(a, 'mul');
    const y = this.varAtom(b, 'mul');
    const [xl, xu] = this.h.bounds(x);
    const [yl, yu] = this.h.bounds(y);
    const ps = [xl * yl, xl * yu, xu * yl, xu * yu];
    const z = this.h.newVar(Math.min(...ps), Math.max(...ps), x.isInt && y.isInt, `${x.name}*${y.name}`);
    this.h.define({ k: 'mul', z, x, y });
    return z;
  }

  pow(a: Linear, k: number, pos: SourcePos): Linear {
    if (!Number.isInteger(k) || k < 0) fail('the exponent of a decision variable must be a non-negative integer', pos);
    let r: Linear = 1;
    for (let i = 0; i < k; i++) r = i === 0 ? a : this.mul(r, a);
    return r;
  }

  div(a: Linear, b: Linear, kind: 'div' | 'mod' | 'realdiv'): DVar {
    const x = this.varAtom(a, kind);
    const y = this.varAtom(b, kind);
    const [xl, xu] = this.h.bounds(x);
    const [yl, yu] = this.h.bounds(y);
    let lo: number;
    let hi: number;
    if (kind === 'mod') {
      const m = Math.max(Math.abs(yl), Math.abs(yu));
      lo = xl >= 0 ? 0 : -m;
      hi = xu <= 0 ? 0 : m;
    } else {
      const ys = [yl, yu, ...(yl <= -1 && yu >= -1 ? [-1] : []), ...(yl <= 1 && yu >= 1 ? [1] : [])].filter((v) => v !== 0);
      const qs = ys.length ? [xl, xu].flatMap((p) => ys.map((q) => p / q)) : [0];
      lo = Math.min(...qs);
      hi = Math.max(...qs);
      if (kind === 'realdiv' && yl <= 0 && yu >= 0) {
        lo = -CP_FLOAT_BOUND;
        hi = CP_FLOAT_BOUND;
      }
    }
    const isInt = kind !== 'realdiv';
    const z = this.h.newVar(isInt ? Math.floor(lo) : lo, isInt ? Math.ceil(hi) : hi, isInt, `${x.name} ${kind} ${y.name}`);
    this.h.define({ k: kind, z, x, y });
    return z;
  }

  abs(a: Linear): DVar {
    const x = this.varAtom(a, 'abs');
    const [xl, xu] = this.h.bounds(x);
    const z = this.h.newVar(xl >= 0 ? xl : xu <= 0 ? -xu : 0, Math.max(-xl, xu), x.isInt, `abs(${x.name})`);
    this.h.define({ k: 'abs', z, x });
    return z;
  }

  fn(fn: 'sqrt' | 'exp' | 'log', a: Linear): DVar {
    const x = this.varAtom(a, fn);
    const [xl, xu] = this.h.bounds(x);
    const f = fn === 'sqrt' ? Math.sqrt : fn === 'exp' ? Math.exp : Math.log;
    const lo = f(Math.max(xl, fn === 'exp' ? xl : 0));
    const hi = f(xu);
    const z = this.h.newVar(Number.isFinite(lo) ? lo : -CP_FLOAT_BOUND, Number.isFinite(hi) ? Math.min(hi, CP_FLOAT_BOUND) : CP_FLOAT_BOUND, false, `${fn}(${x.name})`);
    this.h.define({ k: 'fn', fn, z, x });
    return z;
  }

  minmax(items: Linear[], isMin: boolean): DVar {
    const xs = items.map((e) => this.varAtom(e, isMin ? 'min' : 'max'));
    const bs = xs.map((x) => this.h.bounds(x));
    const lo = isMin ? Math.min(...bs.map((b) => b[0])) : Math.max(...bs.map((b) => b[0]));
    const hi = isMin ? Math.min(...bs.map((b) => b[1])) : Math.max(...bs.map((b) => b[1]));
    const z = this.h.newVar(lo, hi, xs.every((x) => x.isInt), isMin ? 'min' : 'max');
    this.h.define({ k: 'minmax', isMin, z, xs });
    return z;
  }

  /** items[k] for the key equal to the index expression. */
  element(keys: number[], items: Linear[], index: Linear, name: string): DVar {
    const idx = this.varAtom(index, 'index');
    const atoms = items.map((it) => this.atom(it, 'item'));
    let lo = Infinity;
    let hi = -Infinity;
    let isInt = true;
    for (const a of atoms) {
      const [l, u] = typeof a === 'number' ? [a, a] : this.h.bounds(a);
      lo = Math.min(lo, l);
      hi = Math.max(hi, u);
      if (typeof a === 'number' ? !Number.isInteger(a) : !a.isInt) isInt = false;
    }
    const z = this.h.newVar(lo, hi, isInt, name);
    this.h.define({ k: 'element', z, idx, keys, items: atoms });
    return z;
  }

  /**
   * f(e) for a piecewise-linear f, as  x = lo + sum(d[k]),  0 <= d[k] <= len[k],
   * with ordering binaries (segment k+1 is used only when segment k is full).
   */
  piecewise(f: { slopeAt(x: number): number; at(x: number): number; bps: number[] }, e: Linear, pos: SourcePos): Linear {
    const x = this.varAtom(e, 'pwl');
    const [lo, hi] = this.h.bounds(x);
    if (!isFinite(lo) || !isFinite(hi) || Math.max(Math.abs(lo), Math.abs(hi)) >= CP_FLOAT_BOUND) {
      fail('a piecewise-linear function needs an argument with finite bounds', pos);
    }
    const pts = [lo, ...[...new Set(f.bps)].filter((p) => p > lo && p < hi).sort((a, b) => a - b), hi];
    const result = new LinExpr(new Map(), f.at(lo));
    const sum = new LinExpr(new Map(), lo);
    let prev: DVar | null = null;
    let prevLen = 0;
    for (let k = 0; k < pts.length - 1; k++) {
      const len = pts[k + 1] - pts[k];
      const d = this.h.newVar(0, len, false, 'segment');
      result.addScaled(d, f.slopeAt(pts[k] + len / 2));
      sum.addScaled(d, 1);
      if (prev) {
        // Segment k is used only once segment k-1 is full: d <= len * w, prev >= prevLen * w.
        const w = this.h.newVar(0, 1, true, 'segmentUsed');
        this.h.define({ k: 'post', cons: { k: 'cmp', op: '>=', l: prev, r: new LinExpr().addScaled(w, prevLen) } });
        this.h.define({ k: 'post', cons: { k: 'cmp', op: '<=', l: d, r: new LinExpr().addScaled(w, len) } });
      }
      prev = d;
      prevLen = len;
    }
    this.h.define({ k: 'post', cons: { k: 'cmp', op: '=', l: x, r: sum } });
    return result;
  }

  /** z = floor / ceil / round / trunc(e) for a non-integral expression e. */
  rounding(kind: 'floor' | 'ceil' | 'round' | 'trunc', e: Linear): DVar {
    const [lo, hi] = linBounds(this.h, e, this.vars);
    const z = this.h.newVar(Math.floor(lo) - 1, Math.ceil(hi) + 1, true, `${kind}`);
    // floor: z <= e < z + 1;  ceil: z - 1 < e <= z;  round: z - 0.5 <= e < z + 0.5
    const lower = kind === 'ceil' ? -1 : kind === 'round' ? -0.5 : 0;
    const upper = kind === 'ceil' ? 0 : kind === 'round' ? 0.5 : 1;
    const zl = LinExpr.of(z).clone().addScaled(lower, 1);
    const zu = LinExpr.of(z).clone().addScaled(upper, 1);
    if (kind === 'trunc') {
      // trunc rounds towards 0: floor for e >= 0, ceil for e < 0
      const nonneg: CPCons = { k: 'cmp', op: '>=', l: e, r: 0 };
      const asFloor: CPCons = { k: 'and', a: { k: 'cmp', op: '<=', l: z, r: e }, b: { k: 'cmp', op: '<', l: e, r: LinExpr.of(z).clone().addScaled(1, 1) } };
      const asCeil: CPCons = { k: 'and', a: { k: 'cmp', op: '<', l: LinExpr.of(z).clone().addScaled(-1, 1), r: e }, b: { k: 'cmp', op: '<=', l: e, r: z } };
      this.h.define({ k: 'post', cons: { k: 'and', a: { k: 'imp', a: nonneg, b: asFloor }, b: { k: 'imp', a: { k: 'not', a: nonneg }, b: asCeil } } });
      return z;
    }
    const ceil = kind === 'ceil';
    this.h.define({ k: 'post', cons: { k: 'and', a: { k: 'cmp', op: ceil ? '<' : '<=', l: zl, r: e }, b: { k: 'cmp', op: ceil ? '<=' : '<', l: e, r: zu } } });
    return z;
  }

  /** A 0/1 variable equal to the truth value of c. */
  reify(c: CPCons): DVar {
    if (c.k === 'const') return this.h.newVar(c.value ? 1 : 0, c.value ? 1 : 0, true, String(c.value));
    const b = this.h.newVar(0, 1, true, 'bool');
    this.h.define({ k: 'reify', b, cons: c });
    return b;
  }

  /** Selection variables of `act` over the members of the alternative set. */
  selection(act: Activity, alt: Resource): DVar[] {
    let byAlt = this.h.selections.get(act);
    if (!byAlt) this.h.selections.set(act, (byAlt = new Map()));
    let sel = byAlt.get(alt);
    if (!sel) {
      sel = alt.members.map((r) => this.h.newVar(0, 1, true, `${act.name} on ${r.name}`));
      const sum = new LinExpr();
      for (const p of sel) sum.addScaled(p, 1);
      this.h.define({ k: 'post', cons: { k: 'cmp', op: '=', l: sum, r: 1 } });
      byAlt.set(alt, sel);
    }
    return sel;
  }
}
