/**
 * Propagators for arithmetic, logical and global constraints.
 *
 * Bounds may be computed in real arithmetic: integer domains round them
 * (Dom.withMin uses ceil, withMax floor), after a small tolerance below.
 */

import { Dom } from './domain.js';
import type { Propagator, Store } from './store.js';

const EPS = 1e-9;

/** setMax / setMin with a tolerance so 2.9999999999 still allows 3 on integer variables. */
function setMax(s: Store, v: number, m: number): boolean {
  return s.setMax(v, s.real[v] ? m : m + EPS * Math.max(1, Math.abs(m)));
}
function setMin(s: Store, v: number, m: number): boolean {
  return s.setMin(v, s.real[v] ? m : m - EPS * Math.max(1, Math.abs(m)));
}

function sumBounds(s: Store, coefs: readonly number[], vars: readonly number[], c: number): [number, number] {
  let lo = c;
  let hi = c;
  for (let i = 0; i < vars.length; i++) {
    const a = coefs[i];
    const d = s.dom(vars[i]);
    if (a > 0) {
      lo += a * d.min;
      hi += a * d.max;
    } else {
      lo += a * d.max;
      hi += a * d.min;
    }
  }
  return [lo, hi];
}

function tol(x: number): number {
  return EPS * Math.max(1, Math.abs(x));
}

/** sum(coefs[i] * vars[i]) + c <= 0, or = 0 when eq. */
export class Linear implements Propagator {
  queued?: boolean;
  constructor(
    readonly coefs: number[],
    readonly vars: number[],
    readonly c: number,
    readonly eq: boolean,
  ) {}

  propagate(s: Store): boolean {
    const { coefs, vars } = this;
    const [lo, hi] = sumBounds(s, coefs, vars, this.c);
    if (lo > tol(lo)) return false;
    if (this.eq && hi < -tol(hi)) return false;
    for (let i = 0; i < vars.length; i++) {
      const a = coefs[i];
      const v = vars[i];
      const d = s.dom(v);
      const termMin = a > 0 ? a * d.min : a * d.max;
      const termMax = a > 0 ? a * d.max : a * d.min;
      const upper = termMin - lo; // a*x <= upper
      if (a > 0 ? !setMax(s, v, upper / a) : !setMin(s, v, upper / a)) return false;
      if (this.eq) {
        const lower = termMax - hi; // a*x >= lower
        if (a > 0 ? !setMin(s, v, lower / a) : !setMax(s, v, lower / a)) return false;
      }
    }
    return true;
  }
}

/** sum(coefs[i] * vars[i]) + c != 0. */
export class LinearNe implements Propagator {
  queued?: boolean;
  constructor(
    readonly coefs: number[],
    readonly vars: number[],
    readonly c: number,
  ) {}

  propagate(s: Store): boolean {
    let unbound = -1;
    let sum = this.c;
    for (let i = 0; i < this.vars.length; i++) {
      const v = this.vars[i];
      if (s.isBound(v)) sum += this.coefs[i] * s.value(v);
      else if (unbound >= 0) return true;
      else unbound = i;
    }
    if (unbound < 0) return Math.abs(sum) > tol(sum);
    const v = this.vars[unbound];
    if (s.real[v]) return true;
    const value = -sum / this.coefs[unbound];
    const r = Math.round(value);
    return Math.abs(value - r) > 1e-9 ? true : s.remove(v, r);
  }
}

export type LinKind = 'le' | 'eq' | 'ne';

/** b <=> (sum(coefs * vars) + c  kind  0). */
export class ReifLinear implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  private readonly pos: Propagator;
  private readonly neg: Propagator;

  constructor(
    readonly b: number,
    readonly coefs: number[],
    readonly xs: number[],
    readonly c: number,
    readonly kind: LinKind,
    allInt: boolean,
  ) {
    this.vars = [b, ...xs];
    const negCoefs = coefs.map((a) => -a);
    if (kind === 'le') {
      this.pos = new Linear(coefs, xs, c, false);
      // not (e <= 0)  <=>  e >= 1 for integers (e >= 0 for reals)
      this.neg = new Linear(negCoefs, xs, -c + (allInt ? 1 : 0), false);
    } else if (kind === 'eq') {
      this.pos = new Linear(coefs, xs, c, true);
      this.neg = new LinearNe(coefs, xs, c);
    } else {
      this.pos = new LinearNe(coefs, xs, c);
      this.neg = new Linear(coefs, xs, c, true);
    }
  }

  propagate(s: Store): boolean {
    const b = this.b;
    if (s.isBound(b)) return (s.value(b) === 1 ? this.pos : this.neg).propagate(s);
    const truth = this.decided(s);
    return truth === null ? true : s.assign(b, truth ? 1 : 0);
  }

  /** true / false when the constraint is entailed / disentailed. */
  private decided(s: Store): boolean | null {
    const [lo, hi] = sumBounds(s, this.coefs, this.xs, this.c);
    if (this.kind === 'le') {
      if (hi <= tol(hi)) return true;
      if (lo > tol(lo)) return false;
      return null;
    }
    let eq: boolean | null = null;
    if (lo > tol(lo) || hi < -tol(hi)) eq = false;
    else if (Math.abs(lo) <= tol(lo) && Math.abs(hi) <= tol(hi)) eq = true;
    else {
      // One free variable: is the value it would need still in its domain?
      let free = -1;
      let sum = this.c;
      for (let i = 0; i < this.xs.length; i++) {
        if (s.isBound(this.xs[i])) sum += this.coefs[i] * s.value(this.xs[i]);
        else if (free >= 0) {
          free = -2;
          break;
        } else free = i;
      }
      if (free >= 0 && !s.real[this.xs[free]]) {
        const need = -sum / this.coefs[free];
        if (!s.dom(this.xs[free]).contains(Math.round(need)) || Math.abs(need - Math.round(need)) > 1e-9) eq = false;
      }
    }
    if (eq === null) return null;
    return this.kind === 'eq' ? eq : !eq;
  }
}

function corners(a: Dom, b: Dom, f: (x: number, y: number) => number): [number, number] {
  const vals = [f(a.min, b.min), f(a.min, b.max), f(a.max, b.min), f(a.max, b.max)].filter((v) => !Number.isNaN(v));
  return [Math.min(...vals), Math.max(...vals)];
}

/** z = x * y */
export class Times implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly z: number,
    readonly x: number,
    readonly y: number,
  ) {
    this.vars = [z, x, y];
  }

  propagate(s: Store): boolean {
    const { z, x, y } = this;
    for (let round = 0; round < 2; round++) {
      const dx = s.dom(x);
      const dy = s.dom(y);
      const [lo, hi] = corners(dx, dy, (a, b) => a * b);
      if (!setMin(s, z, lo) || !setMax(s, z, hi)) return false;
      const dz = s.dom(z);
      if (!dz.contains(0) && !s.real[z]) {
        if (!s.remove(x, 0) || !s.remove(y, 0)) return false;
      }
      if (!this.divide(s, x, dz, s.dom(y)) || !this.divide(s, y, s.dom(z), s.dom(x))) return false;
    }
    if (!s.real[z] && s.isBound(z) && s.isBound(x) && s.value(x) !== 0) {
      let q = s.value(z) / s.value(x);
      if (!s.real[y]) {
        // 1 / 0.333... is 3.0000000000000004: integers within rounding.
        const r = Math.round(q);
        if (Math.abs(q - r) > 1e-9 * Math.max(1, Math.abs(q))) return false;
        q = r;
      }
      if (!s.assign(y, q)) return false;
    }
    return true;
  }

  /** v * other = z  =>  v in z / other when other excludes 0. */
  private divide(s: Store, v: number, dz: Dom, other: Dom): boolean {
    if (other.min > 0 || other.max < 0) {
      const [lo, hi] = corners(dz, other, (a, b) => a / b);
      return setMin(s, v, lo) && setMax(s, v, hi);
    }
    return true;
  }
}

/** z = x div y (truncating integer division). */
export class Div implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly z: number,
    readonly x: number,
    readonly y: number,
  ) {
    this.vars = [z, x, y];
  }

  propagate(s: Store): boolean {
    const { z, x, y } = this;
    if (!s.remove(y, 0)) return false;
    const dx = s.dom(x);
    const dy = s.dom(y);
    const ys = [dy.min, dy.max];
    if (dy.contains(-1)) ys.push(-1);
    if (dy.contains(1)) ys.push(1);
    const qs: number[] = [];
    for (const a of [dx.min, dx.max]) for (const b of ys) if (b !== 0) qs.push(Math.trunc(a / b));
    if (!s.setMin(z, Math.min(...qs)) || !s.setMax(z, Math.max(...qs))) return false;
    if (s.isBound(y)) {
      const c = s.value(y);
      const k = Math.abs(c);
      const dz = s.dom(z);
      // trunc(x / c) in [zl, zu]  =>  bounds on x
      const zl = c > 0 ? dz.min : -dz.max;
      const zu = c > 0 ? dz.max : -dz.min;
      const xlo = zl > 0 ? zl * k : zl * k - (k - 1);
      const xhi = zu < 0 ? zu * k : zu * k + (k - 1);
      if (!s.setMin(x, xlo) || !s.setMax(x, xhi)) return false;
    }
    if (s.isBound(x) && s.isBound(y)) return s.assign(z, Math.trunc(s.value(x) / s.value(y)));
    return true;
  }
}

/** z = x mod y (sign of x, like C). */
export class Mod implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly z: number,
    readonly x: number,
    readonly y: number,
  ) {
    this.vars = [z, x, y];
  }

  propagate(s: Store): boolean {
    const { z, x, y } = this;
    if (!s.remove(y, 0)) return false;
    const dx = s.dom(x);
    const dy = s.dom(y);
    const m = Math.max(Math.abs(dy.min), Math.abs(dy.max)) - 1;
    const lo = dx.min >= 0 ? 0 : Math.max(-m, dx.min);
    const hi = dx.max <= 0 ? 0 : Math.min(m, dx.max);
    if (!s.setMin(z, lo) || !s.setMax(z, hi)) return false;
    if (s.isBound(y) && s.size(x) <= 4096) {
      const c = s.value(y);
      const dz = s.dom(z);
      const keep: number[] = [];
      const zs: number[] = [];
      for (const v of s.dom(x).values()) {
        const r = v % c;
        if (dz.contains(r + 0)) {
          keep.push(v);
          zs.push(r + 0);
        }
      }
      if (!s.restrict(x, Dom.values(keep)) || !s.restrict(z, Dom.values(zs))) return false;
    }
    if (s.isBound(x) && s.isBound(y)) return s.assign(z, (s.value(x) % s.value(y)) + 0);
    return true;
  }
}

/** z = |x| */
export class Abs implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly z: number,
    readonly x: number,
  ) {
    this.vars = [z, x];
  }

  propagate(s: Store): boolean {
    const { z, x } = this;
    let dx = s.dom(x);
    const zlo = dx.min >= 0 ? dx.min : dx.max <= 0 ? -dx.max : 0;
    const zhi = Math.max(-dx.min, dx.max);
    if (!s.setMin(z, zlo) || !s.setMax(z, zhi)) return false;
    const dz = s.dom(z);
    if (!s.setMin(x, -dz.max) || !s.setMax(x, dz.max)) return false;
    dx = s.dom(x);
    if (dx.min >= 0) return s.setMin(x, dz.min) && s.setMin(z, dx.min) && s.setMax(z, dx.max);
    if (dx.max <= 0) return s.setMax(x, -dz.min) && s.setMin(z, -dx.max) && s.setMax(z, -dx.min);
    if (!s.real[x] && dx.size <= 4096) {
      const keep: number[] = [];
      const zs: number[] = [];
      for (const v of dx.values()) {
        if (s.dom(z).contains(Math.abs(v))) {
          keep.push(v);
          zs.push(Math.abs(v));
        }
      }
      return s.restrict(x, Dom.values(keep)) && s.restrict(z, Dom.values(zs));
    }
    return true;
  }
}

/** z = f(x) for an increasing function f with inverse g (sqrt, exp, log, odd powers). */
export class Monotone implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly z: number,
    readonly x: number,
    readonly f: (v: number) => number,
    readonly g: (v: number) => number,
    readonly xmin = -Infinity,
  ) {
    this.vars = [z, x];
  }

  propagate(s: Store): boolean {
    if (!setMin(s, this.x, this.xmin)) return false;
    const dx = s.dom(this.x);
    if (!setMin(s, this.z, this.f(dx.min)) || !setMax(s, this.z, this.f(dx.max))) return false;
    const dz = s.dom(this.z);
    return setMin(s, this.x, this.g(dz.min)) && setMax(s, this.x, this.g(dz.max));
  }
}

/** z = min(xs) or max(xs). */
export class MinMax implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly z: number,
    readonly xs: number[],
    readonly isMin: boolean,
  ) {
    this.vars = [z, ...xs];
  }

  propagate(s: Store): boolean {
    const { z, xs } = this;
    if (this.isMin) {
      let lo = Infinity;
      let hi = Infinity;
      for (const x of xs) {
        lo = Math.min(lo, s.min(x));
        hi = Math.min(hi, s.max(x));
      }
      if (!s.setMin(z, lo) || !s.setMax(z, hi)) return false;
      for (const x of xs) if (!s.setMin(x, s.min(z))) return false;
      const candidates = xs.filter((x) => s.min(x) <= s.max(z));
      if (candidates.length === 1) return s.setMax(candidates[0], s.max(z));
      return candidates.length > 0;
    }
    let lo = -Infinity;
    let hi = -Infinity;
    for (const x of xs) {
      lo = Math.max(lo, s.min(x));
      hi = Math.max(hi, s.max(x));
    }
    if (!s.setMin(z, lo) || !s.setMax(z, hi)) return false;
    for (const x of xs) if (!s.setMax(x, s.max(z))) return false;
    const candidates = xs.filter((x) => s.max(x) >= s.min(z));
    if (candidates.length === 1) return s.setMin(candidates[0], s.min(z));
    return candidates.length > 0;
  }
}

/** z = items[k] where idx = keys[k]. */
export class Element implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  private readonly byKey = new Map<number, number>();
  private readonly keyDom: Dom;

  constructor(
    readonly z: number,
    readonly idx: number,
    keys: number[],
    readonly items: number[],
  ) {
    keys.forEach((k, i) => this.byKey.set(k, items[i]));
    this.keyDom = Dom.values(keys);
    this.vars = [z, idx, ...new Set(items)];
  }

  propagate(s: Store): boolean {
    const { z, idx } = this;
    if (!s.restrict(idx, this.keyDom)) return false;
    const dz = s.dom(z);
    const keep: number[] = [];
    const values: number[] = [];
    let lo = Infinity;
    let hi = -Infinity;
    let allFixed = true;
    for (const k of s.dom(idx).values()) {
      const item = this.byKey.get(k)!;
      const di = s.dom(item);
      if (!di.intersects(dz)) continue;
      keep.push(k);
      lo = Math.min(lo, di.min);
      hi = Math.max(hi, di.max);
      if (di.size === 1) values.push(di.min);
      else allFixed = false;
    }
    if (!s.restrict(idx, Dom.values(keep))) return false;
    if (allFixed && !s.real[z]) {
      if (!s.restrict(z, Dom.values(values))) return false;
    } else if (!s.setMin(z, lo) || !s.setMax(z, hi)) return false;
    if (s.isBound(idx)) {
      const item = this.byKey.get(s.value(idx))!;
      if (!s.restrict(z, s.dom(item)) || !s.restrict(item, s.dom(z))) return false;
    }
    return true;
  }
}

/** b <=> x in set */
export class ReifMember implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly b: number,
    readonly x: number,
    readonly set: Dom,
  ) {
    this.vars = [b, x];
  }

  propagate(s: Store): boolean {
    const { b, x, set } = this;
    if (s.isBound(b)) return s.value(b) === 1 ? s.restrict(x, set) : s.setDom(x, s.dom(x).minus(set));
    const inter = s.dom(x).intersect(set);
    if (inter.size === 0) return s.assign(b, 0);
    if (inter.size === s.size(x)) return s.assign(b, 1);
    return true;
  }
}

/**
 * alldifferent: removes the values of bound variables from the others and
 * checks that enough values remain; level 'domain' / 'range' also applies
 * Hall-interval reasoning on the bounds.
 */
export class AllDifferent implements Propagator {
  queued?: boolean;
  constructor(
    readonly vars: number[],
    readonly hall: boolean,
  ) {}

  propagate(s: Store): boolean {
    const xs = this.vars;
    const n = xs.length;
    let changed = true;
    const done = new Uint8Array(n);
    while (changed) {
      changed = false;
      for (let i = 0; i < n; i++) {
        if (done[i] || !s.isBound(xs[i])) continue;
        done[i] = 1;
        const v = s.value(xs[i]);
        for (let j = 0; j < n; j++) {
          if (j === i) continue;
          const before = s.size(xs[j]);
          if (!s.remove(xs[j], v)) return false;
          if (s.size(xs[j]) !== before && s.isBound(xs[j])) changed = true;
        }
      }
    }
    // Pigeonhole: n variables need n distinct values.
    let total = 0;
    for (const x of xs) total += s.size(x);
    if (total <= 8192) {
      const union = new Set<number>();
      for (const x of xs) for (const v of s.dom(x).values()) union.add(v);
      if (union.size < n) return false;
    }
    return this.hall ? this.hallIntervals(s) : true;
  }

  private hallIntervals(s: Store): boolean {
    const xs = this.vars;
    const mins = [...new Set(xs.map((x) => s.min(x)))];
    const maxs = [...new Set(xs.map((x) => s.max(x)))];
    for (const a of mins) {
      for (const b of maxs) {
        if (b < a) continue;
        const inside = xs.filter((x) => s.min(x) >= a && s.max(x) <= b);
        const width = b - a + 1;
        if (inside.length > width) return false;
        if (inside.length === width) {
          for (const x of xs) {
            if (inside.includes(x)) continue;
            if (s.min(x) >= a && s.min(x) <= b && !s.setMin(x, b + 1)) return false;
            if (s.max(x) >= a && s.max(x) <= b && !s.setMax(x, a - 1)) return false;
          }
        }
      }
    }
    return true;
  }
}

export type CountMode = 'exact' | 'atmost' | 'atleast';

/**
 * distribute(card, value, base): card[k] = #{ j | base[j] = value[k] }
 * (atmost / atleast: <= / >=).
 */
export class Distribute implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly cards: number[],
    readonly values: number[],
    readonly base: number[],
    readonly mode: CountMode,
  ) {
    this.vars = [...cards, ...base];
  }

  propagate(s: Store): boolean {
    for (let k = 0; k < this.values.length; k++) {
      const v = this.values[k];
      const card = this.cards[k];
      let sure = 0;
      let possible = 0;
      for (const b of this.base) {
        const d = s.dom(b);
        if (!d.contains(v)) continue;
        possible++;
        if (d.size === 1) sure++;
      }
      if (this.mode !== 'atleast' && sure > s.max(card)) return false;
      if (this.mode !== 'atmost' && possible < s.min(card)) return false;
      if (this.mode === 'exact' && (!s.setMin(card, sure) || !s.setMax(card, possible))) return false;
      if (this.mode !== 'atleast' && sure === s.max(card) && possible > sure) {
        for (const b of this.base) if (s.size(b) > 1 && !s.remove(b, v)) return false;
      }
      if (this.mode !== 'atmost' && possible === s.min(card) && possible > sure) {
        for (const b of this.base) if (s.size(b) > 1 && s.dom(b).contains(v) && !s.assign(b, v)) return false;
      }
    }
    return true;
  }
}

/** succ[i] = offset + j means node i is followed by node j; the successors form one cycle. */
export class Circuit implements Propagator {
  queued?: boolean;
  constructor(
    readonly vars: number[],
    readonly offset: number,
    /** subCircuit: succ[i] = i leaves node i out; the other nodes form one cycle. */
    readonly sub = false,
  ) {}

  propagate(s: Store): boolean {
    if (this.sub) return this.propagateSub(s);
    const succ = this.vars;
    const n = succ.length;
    if (n === 1) return s.assign(succ[0], this.offset);
    for (let i = 0; i < n; i++) {
      if (!s.remove(succ[i], this.offset + i) || !s.setMin(succ[i], this.offset) || !s.setMax(succ[i], this.offset + n - 1)) return false;
    }
    const hasPred = new Uint8Array(n);
    for (let i = 0; i < n; i++) if (s.isBound(succ[i])) hasPred[s.value(succ[i]) - this.offset] = 1;
    for (let start = 0; start < n; start++) {
      if (!s.isBound(succ[start])) continue;
      if (hasPred[start] && !this.onCycleCheck(s, start)) return false;
      if (hasPred[start]) continue;
      // Follow the chain start -> ... -> end (end has an unbound successor).
      let end = start;
      let length = 0;
      while (s.isBound(succ[end])) {
        end = s.value(succ[end]) - this.offset;
        length++;
        if (end === start || length > n) return false;
      }
      if (length < n - 1 && !s.remove(succ[end], this.offset + start)) return false;
    }
    return true;
  }

  private propagateSub(s: Store): boolean {
    const succ = this.vars;
    const n = succ.length;
    for (const x of succ) if (!s.setMin(x, this.offset) || !s.setMax(x, this.offset + n - 1)) return false;
    if (!succ.every((x) => s.isBound(x))) return true;
    // Check: the nodes not pointing to themselves form exactly one cycle.
    const next = succ.map((x) => s.value(x) - this.offset);
    const active = next.map((j, i) => j !== i);
    const start = active.indexOf(true);
    if (start < 0) return true;
    let count = 0;
    let node = start;
    do {
      node = next[node];
      count++;
      if (count > n) return false;
    } while (node !== start);
    return count === active.filter(Boolean).length;
  }

  /** A node on a fully bound cycle: the cycle must contain all nodes. */
  private onCycleCheck(s: Store, start: number): boolean {
    let node = start;
    for (let length = 1; length <= this.vars.length; length++) {
      if (!s.isBound(this.vars[node])) return true;
      node = s.value(this.vars[node]) - this.offset;
      if (node === start) return length === this.vars.length;
    }
    return true;
  }
}

/** allowedAssignments (positive table) / forbiddenAssignments (negative table). */
export class Table implements Propagator {
  queued?: boolean;
  constructor(
    readonly vars: number[],
    readonly tuples: number[][],
    readonly positive: boolean,
  ) {}

  propagate(s: Store): boolean {
    const xs = this.vars;
    if (this.positive) {
      // Keep the values supported by at least one tuple that fits all domains.
      const supported = xs.map(() => new Set<number>());
      let any = false;
      for (const t of this.tuples) {
        if (!t.every((v, i) => s.dom(xs[i]).contains(v))) continue;
        any = true;
        t.forEach((v, i) => supported[i].add(v));
      }
      if (!any) return false;
      return xs.every((x, i) => s.restrict(x, Dom.values(supported[i])));
    }
    // Forbidden: when all but one variable are bound, remove the completing values.
    let free = -1;
    for (let i = 0; i < xs.length; i++) {
      if (s.isBound(xs[i])) continue;
      if (free >= 0) return true;
      free = i;
    }
    for (const t of this.tuples) {
      if (!t.every((v, i) => i === free || s.value(xs[i]) === v)) continue;
      if (free < 0) return false;
      if (!s.remove(xs[free], t[free])) return false;
    }
    return true;
  }
}

/**
 * end = the earliest time at which `size` units of work are done since
 * start, work accruing at f(t) percent per unit (CP Optimizer intensity,
 * OPL 3 breakable activities).  end is a nondecreasing function of start.
 */
export class Calendar implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly start: number,
    readonly end: number,
    readonly size: number,
    readonly f: import('./terms.js').StepFunction,
  ) {
    this.vars = [start, end];
  }

  propagate(s: Store): boolean {
    const { start, end } = this;
    const amount = this.size * 100;
    const F = (t: number) => this.f.endFrom(t, amount);
    const sMin = s.min(start);
    const sMax = s.max(start);
    const fMin = F(sMin);
    if (!isFinite(fMin) || !s.setMin(end, fMin)) return false;
    const fMax = F(sMax);
    if (isFinite(fMax) && !s.setMax(end, fMax)) return false;
    const eMin = s.min(end);
    const eMax = s.max(end);
    // The smallest start reaching eMin, the largest one not passing eMax.
    let lo = sMin;
    let hi = sMax;
    if (F(hi) < eMin) return false;
    while (lo < hi) {
      const mid = Math.floor((lo + hi) / 2);
      if (F(mid) >= eMin) hi = mid;
      else lo = mid + 1;
    }
    if (!s.setMin(start, lo)) return false;
    lo = s.min(start);
    hi = sMax;
    if (F(lo) > eMax) return false;
    while (lo < hi) {
      const mid = Math.ceil((lo + hi) / 2);
      if (F(mid) <= eMax) lo = mid;
      else hi = mid - 1;
    }
    return s.setMax(start, lo);
  }
}
