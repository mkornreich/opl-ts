/**
 * CP Optimizer cumul and state functions, and fixed functions of one variable
 * (startEval and friends).
 *
 * A cumul function is a sum of pulses and steps whose positions, heights and
 * presence are variables.  CumulProfile bounds it on time windows with a
 * timetable: from the compulsory parts it gets the least and the largest
 * possible value of the function on each segment of time, fails when a bound
 * cannot hold, and moves terms (or fixes their presence and heights) that
 * would break a bound.  With every variable fixed the profile is exact, so
 * the same pass checks solutions.
 */

import type { Propagator, Store } from './store.js';

export interface CumulItem {
  step: boolean;
  /** Store variables: the start point (pulses and steps) and the end (pulses). */
  start: number;
  end: number;
  /** Duration of an interval pulse (-1 when the points are fixed). */
  dur: number;
  height: number;
  /** -1 when always present. */
  presence: number;
}

/** lo <= f <= hi on [start, end): store variables, or null for -/+ infinity. */
export interface CumulBound {
  start: number | null;
  end: number | null;
  presence: number;
  lo: number;
  hi: number;
}

function presenceOf(s: Store, p: number): number {
  if (p < 0) return 1;
  return s.isBound(p) ? s.value(p) : -1;
}

export class CumulProfile implements Propagator {
  readonly vars: number[];
  queued?: boolean;

  constructor(
    readonly name: string,
    readonly items: CumulItem[],
    readonly bounds: CumulBound[],
  ) {
    const vs = new Set<number>();
    for (const it of items) {
      vs.add(it.start);
      if (!it.step) vs.add(it.end);
      if (it.dur >= 0) vs.add(it.dur);
      vs.add(it.height);
      if (it.presence >= 0) vs.add(it.presence);
    }
    for (const b of bounds) {
      if (b.start !== null) vs.add(b.start);
      if (b.end !== null) vs.add(b.end);
      if (b.presence >= 0) vs.add(b.presence);
    }
    this.vars = [...vs];
  }

  propagate(s: Store): boolean {
    // Geometry of each term: may cover [a0, a1), surely covers [c0, c1) when surely present.
    type Geo = { i: number; a0: number; a1: number; c0: number; c1: number; sure: boolean; hmin: number; hmax: number };
    const geo: Geo[] = [];
    for (let i = 0; i < this.items.length; i++) {
      const it = this.items[i];
      const p = presenceOf(s, it.presence);
      if (p === 0) continue;
      const est = s.min(it.start);
      const lst = s.max(it.start);
      const [a1, c1] = it.step ? [Infinity, Infinity] : [s.max(it.end), s.min(it.end)];
      geo.push({ i, a0: est, a1, c0: lst, c1, sure: p === 1, hmin: s.min(it.height), hmax: s.max(it.height) });
    }
    const wins: { w0: number; w1: number; lo: number; hi: number }[] = [];
    for (const b of this.bounds) {
      if (presenceOf(s, b.presence) !== 1) continue;
      const w0 = b.start === null ? -Infinity : s.max(b.start);
      const w1 = b.end === null ? Infinity : s.min(b.end);
      if (w0 < w1) wins.push({ w0, w1, lo: b.lo, hi: b.hi });
    }
    if (!wins.length) return true;

    // Segments between the breakpoints: 0 = (-inf, P[0]), k + 1 = [P[k], P[k+1]), m = [P[m-1], +inf).
    const pts = new Set<number>();
    const addPt = (t: number) => {
      if (isFinite(t)) pts.add(t);
    };
    for (const g of geo) {
      addPt(g.a0);
      addPt(g.a1);
      if (g.c0 < g.c1) {
        addPt(g.c0);
        addPt(g.c1);
      }
    }
    for (const w of wins) {
      addPt(w.w0);
      addPt(w.w1);
    }
    const P = [...pts].sort((x, y) => x - y);
    const m = P.length;
    const index = new Map<number, number>();
    P.forEach((t, k) => index.set(t, k + 1));
    const seg = (t: number) => (t === -Infinity ? 0 : t === Infinity ? m + 1 : index.get(t)!);
    const n = m + 1;
    const segStart = (k: number) => (k === 0 ? -Infinity : P[k - 1]);
    const segEnd = (k: number) => (k === m ? Infinity : P[k]);

    const dMin = new Float64Array(n + 1);
    const dMax = new Float64Array(n + 1);
    const add = (d: Float64Array, from: number, to: number, v: number) => {
      if (v === 0 || from >= to) return;
      d[from] += v;
      d[to] -= v;
    };
    const parts = (g: Geo) => {
      const [a0, a1] = [seg(g.a0), seg(g.a1)];
      const hasC = g.c0 < g.c1;
      const [c0, c1] = hasC ? [seg(g.c0), seg(g.c1)] : [a0, a0];
      return { a0, a1, c0, c1, hasC };
    };
    for (const g of geo) {
      const { a0, a1, c0, c1, hasC } = parts(g);
      const outMin = Math.min(0, g.hmin);
      const outMax = Math.max(0, g.hmax);
      add(dMin, a0, a1, outMin);
      add(dMax, a0, a1, outMax);
      if (hasC && g.sure) {
        add(dMin, c0, c1, g.hmin - outMin);
        add(dMax, c0, c1, g.hmax - outMax);
      }
    }
    const minF = new Float64Array(n);
    const maxF = new Float64Array(n);
    for (let k = 0, a = 0, b = 0; k < n; k++) {
      a += dMin[k];
      b += dMax[k];
      minF[k] = a;
      maxF[k] = b;
    }
    const lo = new Float64Array(n).fill(-Infinity);
    const hi = new Float64Array(n).fill(Infinity);
    for (const w of wins) {
      for (let k = seg(w.w0); k < seg(w.w1); k++) {
        if (w.lo > lo[k]) lo[k] = w.lo;
        if (w.hi < hi[k]) hi[k] = w.hi;
      }
    }
    const EPS = 1e-9;
    for (let k = 0; k < n; k++) if (minF[k] > hi[k] + EPS || maxF[k] < lo[k] - EPS) return false;

    // Each term against the others.
    for (const g of geo) {
      const it = this.items[g.i];
      const fixed = s.isBound(it.start) && (it.step || s.isBound(it.end)) && s.isBound(it.height) && g.sure;
      if (fixed) continue;
      const { a0, a1, c0, c1, hasC } = parts(g);
      const outMin = Math.min(0, g.hmin);
      const outMax = Math.max(0, g.hmax);
      let hLo = -Infinity;
      let hHi = Infinity;
      const forbidden: number[] = [];
      let firstReq = -1;
      let lastReq = -1;
      for (let k = a0; k < a1; k++) {
        if (lo[k] === -Infinity && hi[k] === Infinity) continue;
        const inC = hasC && g.sure && k >= c0 && k < c1;
        const mnEx = minF[k] - (inC ? g.hmin : outMin);
        const mxEx = maxF[k] - (inC ? g.hmax : outMax);
        const forbid = mnEx + g.hmin > hi[k] + EPS || mxEx + g.hmax < lo[k] - EPS;
        const require = mnEx > hi[k] + EPS || mxEx < lo[k] - EPS;
        if (forbid && require) return false;
        if (forbid) forbidden.push(k);
        if (require) {
          if (firstReq < 0) firstReq = k;
          lastReq = k;
        }
        if (inC || require) {
          hHi = Math.min(hHi, hi[k] - mnEx);
          hLo = Math.max(hLo, lo[k] - mxEx);
        }
      }
      if (firstReq >= 0) {
        if (it.presence >= 0 && !s.assign(it.presence, 1)) return false;
        if (!s.setMax(it.start, segStart(firstReq))) return false;
        if (!it.step && !s.setMin(it.end, segEnd(lastReq))) return false;
      }
      if (hLo > -Infinity && !s.setMin(it.height, Math.ceil(hLo - EPS))) return false;
      if (hHi < Infinity && !s.setMax(it.height, Math.floor(hHi + EPS))) return false;
      if (!forbidden.length) continue;
      // Earliest and latest placements that cover no forbidden segment.
      let est = s.min(it.start);
      let lct = it.step ? Infinity : s.max(it.end);
      if (it.step) {
        est = Math.max(est, segEnd(forbidden[forbidden.length - 1]));
      } else {
        const d = it.dur >= 0 ? s.min(it.dur) : s.min(it.end) - s.max(it.start);
        if (d <= 0) continue;
        for (const k of forbidden) if (segEnd(k) > est && segStart(k) < est + d) est = segEnd(k);
        for (let j = forbidden.length - 1; j >= 0; j--) {
          const k = forbidden[j];
          if (segStart(k) < lct && segEnd(k) > lct - d) lct = segStart(k);
        }
        if (lct - est < d) est = Infinity;
      }
      const none = est > s.max(it.start) || (!it.step && lct < s.min(it.end));
      if (!g.sure) {
        // Only an impossible placement says something about an optional term.
        if (none && !s.assign(it.presence, 0)) return false;
        continue;
      }
      if (none) return false;
      if (!s.setMin(it.start, est)) return false;
      if (!it.step && !s.setMax(it.end, lct)) return false;
    }
    return true;
  }
}

/** The value of a cumul function at time t in a solution. */
export function cumulValue(items: { step: boolean; start: number; end: number; height: number; present: boolean }[], t: number): number {
  let v = 0;
  for (const it of items) if (it.present && it.start <= t && (it.step || t < it.end)) v += it.height;
  return v;
}

/** The segments of a solved cumul function, from -inf to +inf. */
export function cumulSegments(items: { step: boolean; start: number; end: number; height: number; present: boolean }[], big: number): [number, number, number][] {
  const pts = new Set<number>();
  for (const it of items) {
    if (!it.present || it.height === 0) continue;
    pts.add(it.start);
    if (!it.step) pts.add(it.end);
  }
  const P = [-big, ...[...pts].filter((t) => t > -big && t < big).sort((x, y) => x - y), big];
  const out: [number, number, number][] = [];
  for (let k = 0; k + 1 < P.length; k++) {
    const v = cumulValue(items, P[k]);
    const last = out[out.length - 1];
    if (last && last[2] === v) last[1] = P[k + 1];
    else out.push([P[k], P[k + 1], v]);
  }
  return out;
}

// ------------------------------------------------------------ state functions

export interface StateItem {
  kind: 'equal' | 'constant' | 'none' | 'in';
  /** Store variables (constants for fixed windows); null for -/+ infinity. */
  start: number | null;
  end: number | null;
  presence: number;
  /** equal / constant: the state variable. */
  value: number;
  lo: number;
  hi: number;
  aligns: boolean;
  aligne: boolean;
}

/** A fixed window of a state function constraint in a solution. */
export interface StateFixed {
  kind: StateItem['kind'];
  s: number;
  e: number;
  v: number;
  lo: number;
  hi: number;
  aligns: boolean;
  aligne: boolean;
}

/**
 * The segments [s, e, state] of a state function with fixed windows, or null
 * when no state function satisfies them.  Each window asking for a state lies
 * in one segment, so overlapping windows share a segment, and aligned
 * windows start or end with it.  Consecutive segments are at least the
 * transition distance apart; neighbours with the same state share a segment
 * when nothing separates them and the gap is shorter than that distance.
 */
export function stateSegments(ws: StateFixed[], dist: (a: number, b: number) => number): [number, number, number][] | null {
  const live = ws.filter((w) => w.s < w.e);
  const defined = live.filter((w) => w.kind === 'equal' || w.kind === 'constant').sort((a, b) => a.s - b.s || a.e - b.e);
  const none = live.filter((w) => w.kind === 'none');
  for (let i = 0; i < defined.length; i++) {
    for (let j = i + 1; j < defined.length && defined[j].s < defined[i].e; j++) if (defined[j].v !== defined[i].v) return null;
    for (const z of none) if (z.s < defined[i].e && defined[i].s < z.e) return null;
  }
  type Seg = { s: number; e: number; v: number; members: StateFixed[] };
  const groups: Seg[] = [];
  for (const w of defined) {
    const last = groups[groups.length - 1];
    if (last && w.s < last.e) {
      last.e = Math.max(last.e, w.e);
      last.members.push(w);
    } else groups.push({ s: w.s, e: w.e, v: w.v, members: [w] });
  }
  for (const g of groups) for (const w of g.members) if ((w.aligns && w.s !== g.s) || (w.aligne && w.e !== g.e)) return null;
  const segs: Seg[] = [];
  for (const g of groups) {
    const last = segs[segs.length - 1];
    if (last && last.v === g.v) {
      const gap = g.s - last.e;
      const free =
        !last.members.some((w) => w.aligne && w.e === last.e) &&
        !g.members.some((w) => w.aligns && w.s === g.s) &&
        !none.some((z) => z.s < g.s && last.e < z.e) &&
        !live.some((w) => w.kind === 'in' && w.s < g.s && last.e < w.e && (g.v < w.lo || g.v > w.hi));
      if (free && (gap === 0 || gap < dist(g.v, g.v))) {
        last.e = g.e;
        last.members.push(...g.members);
        continue;
      }
    }
    if (last && g.s - last.e < dist(last.v, g.v)) return null;
    segs.push({ ...g, members: [...g.members] });
  }
  for (const w of live) {
    if (w.kind !== 'in') continue;
    for (const g of segs) if (g.s < w.e && w.s < g.e && (g.v < w.lo || g.v > w.hi)) return null;
  }
  return segs.map((g) => [g.s, g.e, g.v]);
}

/** Checks a state function once all of its windows are fixed (pairwise constraints prune before that). */
export class StateCheck implements Propagator {
  readonly vars: number[];
  queued?: boolean;

  constructor(
    readonly name: string,
    readonly items: StateItem[],
    readonly dist: (a: number, b: number) => number,
  ) {
    const vs = new Set<number>();
    for (const it of items) {
      for (const v of [it.start, it.end, it.presence, it.value]) if (v !== null && v >= 0) vs.add(v);
    }
    this.vars = [...vs];
  }

  propagate(s: Store): boolean {
    for (const v of this.vars) if (!s.isBound(v)) return true;
    const ws: StateFixed[] = [];
    for (const it of this.items) {
      if (presenceOf(s, it.presence) !== 1) continue;
      ws.push({
        kind: it.kind,
        s: it.start === null ? -Infinity : s.value(it.start),
        e: it.end === null ? Infinity : s.value(it.end),
        v: it.value >= 0 ? s.value(it.value) : 0,
        lo: it.lo,
        hi: it.hi,
        aligns: it.aligns,
        aligne: it.aligne,
      });
    }
    return stateSegments(ws, this.dist) !== null;
  }
}

// ------------------------------------------------------------ z = f(x)

/** z = f(x) for a fixed function f of an integer variable x (piecewise linear or step). */
export class FuncProp implements Propagator {
  readonly vars: number[];
  queued?: boolean;

  constructor(
    readonly z: number,
    readonly x: number,
    readonly f: (x: number) => number,
    readonly points: number[],
  ) {
    this.vars = [z, x];
  }

  propagate(s: Store): boolean {
    const { z, x, f } = this;
    let lo = s.min(x);
    let hi = s.max(x);
    if (lo === hi) {
      const v = f(lo);
      return s.setMin(z, v) && s.setMax(z, v);
    }
    // Shrink x from both ends while f is outside z's bounds (a few steps at most).
    const zl = s.min(z) - 1e-9;
    const zu = s.max(z) + 1e-9;
    for (let n = 0; n < 64 && lo < hi; n++) {
      const v = f(lo);
      if (v >= zl && v <= zu) break;
      lo++;
    }
    for (let n = 0; n < 64 && lo < hi; n++) {
      const v = f(hi);
      if (v >= zl && v <= zu) break;
      hi--;
    }
    if (!s.setMin(x, lo) || !s.setMax(x, hi)) return false;
    // f is linear between the points, so its range on [lo, hi] is at them or the ends.
    let mn = Math.min(f(lo), f(hi));
    let mx = Math.max(f(lo), f(hi));
    for (const p of this.points) {
      for (const t of [Math.floor(p) - 1, Math.floor(p), Math.ceil(p)]) {
        if (t <= lo || t >= hi) continue;
        const v = f(t);
        if (v < mn) mn = v;
        if (v > mx) mx = v;
      }
    }
    return s.setMin(z, mn) && s.setMax(z, mx);
  }
}
