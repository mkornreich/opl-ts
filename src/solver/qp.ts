/**
 * Convex quadratic programming:  min c'x + 1/2 x'Hx  over the rows and bounds
 * of a LinearProgram, by a primal active-set method; integer columns by
 * branch and bound on top of it.
 *
 * A feasible start comes from the simplex (phase 1 of the LP).  Each
 * iteration solves the equality-constrained problem on the working set:
 * columns at an active bound stay fixed, the free ones F satisfy
 *
 *   [ H_FF   A_WF' ] [ p  ]   [ -g_F ]
 *   [ A_WF    0    ] [ mu ] = [  0   ]
 *
 * (dense LU with partial pivoting), where W are the active rows.  A zero step
 * whose multipliers have the right signs is optimal; otherwise the constraint
 * with the worst multiplier leaves the working set.  A non-zero step goes as
 * far as feasibility allows and adds the constraint that blocks it.  Columns
 * without curvature make H_FF singular: a small diagonal shift then gives a
 * descent direction that some constraint blocks (or the problem is unbounded).
 */

import { OplError } from '../errors.js';
import { emptyResult, type LinearProgram, type LPResult, type MIPResult } from './lp.js';
import { memoryExceeded, reserve } from './memory.js';
import { clean, solveLP } from './simplex.js';

/** Upper triangle of the symmetric matrix H as (i, j, value) with i <= j. */
export interface Hessian {
  i: number[];
  j: number[];
  v: number[];
}

export interface QPOptions {
  /** performance.now() time to stop at. */
  deadline?: number;
}

const TOL = 1e-9;
const INT_TOL = 1e-6;

/** H by rows (both triangles). */
class SymMatrix {
  readonly rows: { col: number[]; val: number[] }[];
  constructor(n: number, h: Hessian) {
    this.rows = Array.from({ length: n }, () => ({ col: [], val: [] }));
    for (let k = 0; k < h.i.length; k++) {
      const [a, b, v] = [h.i[k], h.j[k], h.v[k]];
      if (v === 0) continue;
      this.rows[a].col.push(b);
      this.rows[a].val.push(v);
      if (a !== b) {
        this.rows[b].col.push(a);
        this.rows[b].val.push(v);
      }
    }
  }

  /** H x. */
  times(x: Float64Array): Float64Array {
    const out = new Float64Array(x.length);
    this.rows.forEach((r, i) => {
      let s = 0;
      for (let k = 0; k < r.col.length; k++) s += r.val[k] * x[r.col[k]];
      out[i] = s;
    });
    return out;
  }

  get(i: number, j: number): number {
    const r = this.rows[i];
    let s = 0;
    for (let k = 0; k < r.col.length; k++) if (r.col[k] === j) s += r.val[k];
    return s;
  }
}

/** True when H is positive semidefinite (Cholesky with a small tolerance on the columns it involves). */
export function isConvex(h: Hessian): boolean {
  const used = [...new Set([...h.i, ...h.j])].sort((a, b) => a - b);
  const k = used.length;
  if (k === 0) return true;
  if (k > 3000) return false;
  reserve(k * k * 8, `the convexity check of the quadratic objective (${k} columns)`);
  const at = new Map(used.map((c, t) => [c, t]));
  const a = Array.from({ length: k }, () => new Float64Array(k));
  for (let t = 0; t < h.i.length; t++) {
    const p = at.get(h.i[t])!;
    const q = at.get(h.j[t])!;
    a[p][q] += h.v[t];
    if (p !== q) a[q][p] += h.v[t];
  }
  let scale = 0;
  for (let p = 0; p < k; p++) scale = Math.max(scale, Math.abs(a[p][p]));
  const tol = 1e-9 * Math.max(1, scale);
  // LDL' without pivoting: a zero pivot needs a zero column below it.
  for (let p = 0; p < k; p++) {
    const d = a[p][p];
    if (d < -tol) return false;
    if (d <= tol) {
      for (let q = p + 1; q < k; q++) if (Math.abs(a[q][p]) > Math.sqrt(tol)) return false;
      continue;
    }
    for (let q = p + 1; q < k; q++) {
      const f = a[q][p] / d;
      if (f === 0) continue;
      for (let r = p + 1; r < k; r++) a[q][r] -= f * a[p][r];
    }
  }
  return true;
}

/** Solves a dense system in place (partial pivoting); false when singular. */
function luSolve(a: Float64Array[], b: Float64Array): boolean {
  const s = b.length;
  let scale = 0;
  for (const row of a) for (let j = 0; j < s; j++) scale = Math.max(scale, Math.abs(row[j]));
  const tol = 1e-12 * Math.max(1, scale);
  for (let p = 0; p < s; p++) {
    let best = p;
    for (let r = p + 1; r < s; r++) if (Math.abs(a[r][p]) > Math.abs(a[best][p])) best = r;
    if (Math.abs(a[best][p]) <= tol) return false;
    if (best !== p) {
      [a[p], a[best]] = [a[best], a[p]];
      [b[p], b[best]] = [b[best], b[p]];
    }
    const piv = a[p][p];
    for (let r = p + 1; r < s; r++) {
      const f = a[r][p] / piv;
      if (f === 0) continue;
      const ar = a[r];
      const ap = a[p];
      for (let c = p; c < s; c++) ar[c] -= f * ap[c];
      b[r] -= f * b[p];
    }
  }
  for (let p = s - 1; p >= 0; p--) {
    let v = b[p];
    for (let c = p + 1; c < s; c++) v -= a[p][c] * b[c];
    b[p] = v / a[p][p];
  }
  return true;
}

type Side = 'L' | 'U' | 'E';

/** Solves the continuous QP with the given column bounds. */
export function solveQP(lp: LinearProgram, h: Hessian, lower = lp.lower, upper = lp.upper, options: QPOptions = {}): LPResult {
  return qp(lp, new SymMatrix(lp.numVars, h), lower, upper, options.deadline ?? Infinity);
}

function qp(lp: LinearProgram, H: SymMatrix, lower: Float64Array, upper: Float64Array, deadline: number): LPResult {
  const n = lp.numVars;
  const m = lp.rows.length;
  // A feasible vertex.
  const phase1 = solveLP({ ...lp, objective: new Float64Array(n), objConstant: 0 }, lower, upper, { deadline });
  if (phase1.status !== 'optimal') return emptyResult(lp, phase1.status === 'unbounded' ? 'infeasible' : phase1.status);
  const x = Float64Array.from(phase1.x);
  const c = lp.objective;
  const act = (i: number) => {
    const r = lp.rows[i];
    let s = 0;
    for (let k = 0; k < r.index.length; k++) s += r.value[k] * x[r.index[k]];
    return s;
  };
  const near = (a: number, b: number) => Math.abs(a - b) <= 1e-9 * Math.max(1, Math.abs(b));
  // Working set: column states (0 free, 1 at lower, 2 at upper, 3 fixed) and active rows.
  const colState = new Uint8Array(n);
  for (let j = 0; j < n; j++) {
    if (lower[j] === upper[j]) colState[j] = 3;
    else if (isFinite(lower[j]) && near(x[j], lower[j])) colState[j] = 1;
    else if (isFinite(upper[j]) && near(x[j], upper[j])) colState[j] = 2;
  }
  const work: { row: number; side: Side }[] = [];
  const inWork = new Uint8Array(m);
  for (let i = 0; i < m; i++) {
    if (lp.rows[i].lower === lp.rows[i].upper) {
      work.push({ row: i, side: 'E' });
      inWork[i] = 1;
    }
  }
  dropDependent(lp, colState, work, inWork);

  let iterations = phase1.iterations;
  const maxIterations = 1000 + 20 * (n + m);
  let lambda = new Float64Array(0);
  let shift = 0;
  for (;;) {
    if (++iterations > maxIterations || performance.now() > deadline) return emptyResult(lp, 'iteration_limit', iterations);
    const g = H.times(x);
    for (let j = 0; j < n; j++) g[j] += c[j];
    const free: number[] = [];
    for (let j = 0; j < n; j++) if (colState[j] === 0) free.push(j);
    const nf = free.length;
    const k = work.length;
    const s = nf + k;
    if (s > 4000) throw new OplError(`the quadratic program is too large for the active-set method (${s} free columns and active rows)`);
    reserve(s * s * 8, `the quadratic program's KKT system (${s} x ${s})`);
    const posOf = new Int32Array(n).fill(-1);
    free.forEach((j, t) => (posOf[j] = t));
    const build = (delta: number): [Float64Array[], Float64Array] => {
      const K = Array.from({ length: s }, () => new Float64Array(s));
      const rhs = new Float64Array(s);
      free.forEach((j, t) => {
        const r = H.rows[j];
        for (let q = 0; q < r.col.length; q++) {
          const u = posOf[r.col[q]];
          if (u >= 0) K[t][u] += r.val[q];
        }
        K[t][t] += delta;
        rhs[t] = -g[j];
      });
      work.forEach((w, q) => {
        const r = lp.rows[w.row];
        for (let e = 0; e < r.index.length; e++) {
          const u = posOf[r.index[e]];
          if (u < 0) continue;
          K[nf + q][u] += r.value[e];
          K[u][nf + q] += r.value[e];
        }
      });
      return [K, rhs];
    };
    let [K, sol] = build(shift);
    let shifted = shift > 0;
    if (!luSolve(K, sol)) {
      // No curvature along some free directions: shift the diagonal.
      let scale = 1;
      for (const j of free) scale = Math.max(scale, Math.abs(H.get(j, j)));
      shift = 1e-7 * scale;
      [K, sol] = build(shift);
      shifted = true;
      if (!luSolve(K, sol)) return emptyResult(lp, 'iteration_limit', iterations);
    }
    const p = new Float64Array(n);
    let pmax = 0;
    free.forEach((j, t) => {
      p[j] = sol[t];
      pmax = Math.max(pmax, Math.abs(sol[t]));
    });
    let xmax = 1;
    for (const j of free) xmax = Math.max(xmax, Math.abs(x[j]));

    if (pmax <= 1e-10 * xmax) {
      // Stationary on the working set: multipliers (g = A_W' lambda + bound multipliers).
      lambda = new Float64Array(k);
      for (let q = 0; q < k; q++) lambda[q] = -sol[nf + q];
      const reduced = Float64Array.from(g);
      work.forEach((w, q) => {
        const r = lp.rows[w.row];
        for (let e = 0; e < r.index.length; e++) reduced[r.index[e]] -= lambda[q] * r.value[e];
      });
      let gmax = 1;
      for (let j = 0; j < n; j++) gmax = Math.max(gmax, Math.abs(g[j]));
      let worst = 1e-7 * gmax;
      let leave: { kind: 'row'; q: number } | { kind: 'col'; j: number } | null = null;
      work.forEach((w, q) => {
        const bad = w.side === 'L' ? -lambda[q] : w.side === 'U' ? lambda[q] : 0;
        if (bad > worst) {
          worst = bad;
          leave = { kind: 'row', q };
        }
      });
      for (let j = 0; j < n; j++) {
        const bad = colState[j] === 1 ? -reduced[j] : colState[j] === 2 ? reduced[j] : 0;
        if (bad > worst) {
          worst = bad;
          leave = { kind: 'col', j };
        }
      }
      // (A zero step means g is in the span of the active constraints, shift or not.)
      if (!leave) return finishQP(lp, H, x, work, lambda, reduced, colState, iterations);
      const l = leave as { kind: 'row'; q: number } | { kind: 'col'; j: number };
      if (l.kind === 'row') {
        inWork[work[l.q].row] = 0;
        work.splice(l.q, 1);
      } else colState[l.j] = 0;
      continue;
    }

    // Ratio test.
    let alpha = 1;
    let block: { kind: 'row'; i: number; side: Side } | { kind: 'col'; j: number; state: number } | null = null;
    for (const j of free) {
      const pj = p[j];
      if (pj < -1e-14 && isFinite(lower[j])) {
        const t = (lower[j] - x[j]) / pj;
        if (t < alpha) {
          alpha = Math.max(t, 0);
          block = { kind: 'col', j, state: 1 };
        }
      } else if (pj > 1e-14 && isFinite(upper[j])) {
        const t = (upper[j] - x[j]) / pj;
        if (t < alpha) {
          alpha = Math.max(t, 0);
          block = { kind: 'col', j, state: 2 };
        }
      }
    }
    for (let i = 0; i < m; i++) {
      if (inWork[i]) continue;
      const r = lp.rows[i];
      let ap = 0;
      for (let e = 0; e < r.index.length; e++) ap += r.value[e] * p[r.index[e]];
      if (Math.abs(ap) <= 1e-12 * pmax) continue;
      const a = act(i);
      if (ap < 0 && isFinite(r.lower)) {
        const t = (r.lower - a) / ap;
        if (t < alpha) {
          alpha = Math.max(t, 0);
          block = { kind: 'row', i, side: 'L' };
        }
      } else if (ap > 0 && isFinite(r.upper)) {
        const t = (r.upper - a) / ap;
        if (t < alpha) {
          alpha = Math.max(t, 0);
          block = { kind: 'row', i, side: 'U' };
        }
      }
    }
    if (!block && shifted) {
      // A shifted step that nothing blocks: unbounded when the true curvature is zero.
      const hp = H.times(p);
      let curv = 0;
      let slope = 0;
      for (let j = 0; j < n; j++) {
        curv += p[j] * hp[j];
        slope += g[j] * p[j];
      }
      if (curv <= 1e-12 * pmax * pmax && slope < 0) return emptyResult(lp, 'unbounded', iterations);
    }
    for (let j = 0; j < n; j++) if (p[j] !== 0) x[j] += alpha * p[j];
    if (block) {
      const b = block as { kind: 'row'; i: number; side: Side } | { kind: 'col'; j: number; state: number };
      if (b.kind === 'col') {
        colState[b.j] = b.state;
        x[b.j] = b.state === 1 ? lower[b.j] : upper[b.j];
      } else {
        const r = lp.rows[b.i];
        work.push({ row: b.i, side: r.lower === r.upper ? 'E' : b.side });
        inWork[b.i] = 1;
      }
    } else shift = 0;
  }
}

/** Removes equality rows that depend on the others (restricted to the free columns). */
function dropDependent(lp: LinearProgram, colState: Uint8Array, work: { row: number; side: Side }[], inWork: Uint8Array): void {
  if (work.length === 0) return;
  const free: number[] = [];
  for (let j = 0; j < lp.numVars; j++) if (colState[j] === 0) free.push(j);
  const posOf = new Map(free.map((j, t) => [j, t]));
  reserve(work.length * free.length * 8, 'the quadratic program');
  const basis: { v: Float64Array; piv: number }[] = [];
  const keep: { row: number; side: Side }[] = [];
  for (const w of work) {
    const v = new Float64Array(free.length);
    const r = lp.rows[w.row];
    for (let e = 0; e < r.index.length; e++) {
      const t = posOf.get(r.index[e]);
      if (t !== undefined) v[t] += r.value[e];
    }
    for (const b of basis) {
      const f = v[b.piv] / b.v[b.piv];
      if (f !== 0) for (let t = 0; t < v.length; t++) v[t] -= f * b.v[t];
    }
    let piv = -1;
    let best = 1e-9;
    for (let t = 0; t < v.length; t++) {
      if (Math.abs(v[t]) > best) {
        best = Math.abs(v[t]);
        piv = t;
      }
    }
    if (piv < 0) {
      inWork[w.row] = 0;
      continue;
    }
    basis.push({ v, piv });
    keep.push(w);
  }
  work.length = 0;
  work.push(...keep);
}

function finishQP(
  lp: LinearProgram,
  H: SymMatrix,
  x: Float64Array,
  work: { row: number; side: Side }[],
  lambda: Float64Array,
  reduced: Float64Array,
  colState: Uint8Array,
  iterations: number,
): LPResult {
  const n = lp.numVars;
  const xs = Float64Array.from(x, clean);
  const hx = H.times(xs);
  let obj = lp.objConstant;
  for (let j = 0; j < n; j++) obj += lp.objective[j] * xs[j] + 0.5 * xs[j] * hx[j];
  const duals = new Float64Array(lp.rows.length);
  work.forEach((w, q) => (duals[w.row] = clean(lambda[q])));
  const rc = new Float64Array(n);
  for (let j = 0; j < n; j++) rc[j] = colState[j] ? clean(reduced[j]) : 0;
  return { status: 'optimal', objective: obj, x: xs, duals, reducedCosts: rc, iterations };
}

/** Branch and bound over QP relaxations for the integer columns. */
export function solveMIQP(lp: LinearProgram, h: Hessian, options: { timeLimit?: number } = {}): MIPResult {
  const n = lp.numVars;
  const H = new SymMatrix(n, h);
  const deadline = options.timeLimit ? performance.now() + options.timeLimit * 1000 : Infinity;
  const ints: number[] = [];
  for (let j = 0; j < n; j++) if (lp.integer[j]) ints.push(j);
  const lower0 = Float64Array.from(lp.lower);
  const upper0 = Float64Array.from(lp.upper);
  for (const j of ints) {
    lower0[j] = Math.ceil(lower0[j] - INT_TOL);
    upper0[j] = Math.floor(upper0[j] + INT_TOL);
  }
  let best: LPResult | null = null;
  let incumbent = Infinity;
  let iterations = 0;
  let nodes = 0;
  let hitLimit = false;
  let unbounded = false;
  const stack: { lower: Float64Array; upper: Float64Array; bound: number }[] = [{ lower: lower0, upper: upper0, bound: -Infinity }];
  while (stack.length) {
    if (performance.now() > deadline || ((nodes & 31) === 31 && memoryExceeded())) {
      hitLimit = true;
      break;
    }
    const node = stack.pop()!;
    if (node.bound >= incumbent - 1e-9 * Math.max(1, Math.abs(incumbent))) continue;
    const r = qp(lp, H, node.lower, node.upper, deadline);
    nodes++;
    iterations += r.iterations;
    if (r.status === 'infeasible') continue;
    if (r.status === 'unbounded') {
      unbounded = true;
      break;
    }
    if (r.status !== 'optimal') {
      hitLimit = true;
      continue;
    }
    if (r.objective >= incumbent - 1e-9 * Math.max(1, Math.abs(incumbent))) continue;
    let branch = -1;
    let frac = 0;
    for (const j of ints) {
      const f = Math.abs(r.x[j] - Math.round(r.x[j]));
      if (f > INT_TOL && f > frac) {
        frac = f;
        branch = j;
      }
    }
    if (branch < 0) {
      for (const j of ints) r.x[j] = Math.round(r.x[j]) + 0;
      incumbent = r.objective;
      best = r;
      continue;
    }
    const v = r.x[branch];
    const down = { lower: Float64Array.from(node.lower), upper: Float64Array.from(node.upper), bound: r.objective };
    down.upper[branch] = Math.floor(v);
    const up = { lower: Float64Array.from(node.lower), upper: Float64Array.from(node.upper), bound: r.objective };
    up.lower[branch] = Math.ceil(v);
    // Depth first, nearer side first.
    if (v - Math.floor(v) >= 0.5) stack.push(down, up);
    else stack.push(up, down);
  }
  const zeros = new Float64Array(n);
  if (!best) {
    const status = unbounded ? 'unbounded' : hitLimit ? 'limit' : 'infeasible';
    return { status, objective: Infinity, bound: -Infinity, x: zeros, duals: new Float64Array(lp.rows.length), reducedCosts: zeros, iterations, nodes };
  }
  const b = best as LPResult;
  let bound = incumbent;
  if (hitLimit) for (const s of stack) bound = Math.min(bound, s.bound);
  return {
    status: hitLimit ? 'feasible' : 'optimal',
    objective: incumbent,
    bound,
    x: b.x,
    duals: ints.length ? new Float64Array(lp.rows.length) : b.duals,
    reducedCosts: ints.length ? zeros : b.reducedCosts,
    iterations,
    nodes,
  };
}
