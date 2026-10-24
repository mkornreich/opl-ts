/**
 * Dense bounded-variable simplex with warm starts.
 *
 * Every row i gets a logical column s_i with  a_i . x - s_i = 0  and
 * row.lower <= s_i <= row.upper, so all bounds live on columns.  Rows whose
 * activity at the starting point violates its bounds get an artificial column;
 * phase 1 minimises the sum of artificials, phase 2 the real objective.
 *
 * After an optimal solve, bounds can be changed (setBounds) and the problem
 * re-optimised with the dual simplex (dual), which is how branch and bound
 * re-solves a child node in a few pivots.  snapshot / restore save and
 * rebuild a basis for nodes processed later.
 *
 * The tableau rows satisfy  x_basis[i] + sum_j T[i][j] x_j = 0  (non-basic j).
 */

import { emptyResult, type LinearProgram, type LPResult } from './lp.js';
import { reserve } from './memory.js';

export const FEAS_TOL = 1e-9;
const OPT_TOL = 1e-9;
const PIVOT_TOL = 1e-10;
/** Consecutive degenerate pivots before switching to Bland's rule. */
const DEGENERATE_LIMIT = 50;

export type SimplexStatus = 'optimal' | 'infeasible' | 'unbounded' | 'iteration_limit';

/** A basis: basic columns, and for the others 0 = at lower bound, 1 = at upper bound, 2 = at `other`. */
export interface Snapshot {
  basis: Int32Array;
  status: Uint8Array;
  other: Map<number, number>;
}

export class DenseSimplex {
  readonly n: number;
  readonly m: number;
  readonly N: number;
  readonly lb: Float64Array;
  readonly ub: Float64Array;
  readonly x: Float64Array;
  readonly d: Float64Array;
  private T: Float64Array[];
  /** Artificial column of each row (-1 when none) and the sign used for it. */
  private readonly rowArt: Int32Array;
  private readonly rowSign: Float64Array;
  readonly basis: Int32Array;
  private readonly isBasic: Uint8Array;
  /** Phase-2 costs (the objective on structural columns). */
  private readonly cost: Float64Array;
  private readonly firstArt: number;
  iterations = 0;
  /** performance.now() time after which primal / dual stop with 'iteration_limit' (timedOut set). */
  deadline = Infinity;
  timedOut = false;
  /** Infeasible before any pivot (inconsistent bounds). */
  readonly trivial: boolean = false;
  private nz: Int32Array;

  constructor(
    readonly lp: LinearProgram,
    lower: Float64Array = lp.lower,
    upper: Float64Array = lp.upper,
  ) {
    const n = (this.n = lp.numVars);
    const m = (this.m = lp.rows.length);
    for (let j = 0; j < n; j++) if (lower[j] > upper[j] + FEAS_TOL) this.trivial = true;

    // Starting point: every structural column non-basic at a finite bound (free columns at 0).
    const start = new Float64Array(n);
    for (let j = 0; j < n; j++) start[j] = isFinite(lower[j]) ? lower[j] : isFinite(upper[j]) ? upper[j] : 0;
    const activity = new Float64Array(m);
    const needsArt = new Uint8Array(m);
    let numArt = 0;
    for (let i = 0; i < m; i++) {
      const row = lp.rows[i];
      if (row.lower > row.upper + FEAS_TOL) this.trivial = true;
      let r = 0;
      for (let k = 0; k < row.index.length; k++) r += row.value[k] * start[row.index[k]];
      activity[i] = r;
      if (r < row.lower - FEAS_TOL || r > row.upper + FEAS_TOL) {
        needsArt[i] = 1;
        numArt++;
      }
    }

    const N = (this.N = n + m + numArt);
    this.firstArt = n + m;
    reserve(m * N * 8 + N * 64, `the simplex tableau (${m} rows x ${N} columns)`);
    this.rowArt = new Int32Array(m).fill(-1);
    this.rowSign = new Float64Array(m);
    this.lb = new Float64Array(N);
    this.ub = new Float64Array(N);
    this.x = new Float64Array(N);
    this.d = new Float64Array(N);
    this.T = new Array(m);
    this.basis = new Int32Array(m);
    this.isBasic = new Uint8Array(N);
    this.cost = new Float64Array(N);
    this.cost.set(lp.objective);
    this.nz = new Int32Array(N);
    const { lb, ub, x, T, basis, isBasic } = this;
    for (let j = 0; j < n; j++) {
      lb[j] = lower[j];
      ub[j] = upper[j];
      x[j] = start[j];
    }
    let art = n + m;
    for (let i = 0; i < m; i++) {
      const row = lp.rows[i];
      const s = n + i;
      lb[s] = row.lower;
      ub[s] = row.upper;
      if (!needsArt[i]) {
        // -a_i x + s_i = 0 with s_i basic.
        basis[i] = s;
        x[s] = activity[i];
      } else {
        // (a_i x - s_i) / g + art = 0 with art basic and positive.
        const v = activity[i] < row.lower ? row.lower : row.upper;
        const dv = activity[i] - v;
        this.rowArt[i] = art;
        this.rowSign[i] = dv > 0 ? -1 : 1;
        lb[art] = 0;
        ub[art] = Infinity;
        x[s] = v;
        x[art] = Math.abs(dv);
        basis[i] = art;
        art++;
      }
      T[i] = new Float64Array(N);
      this.initialRow(i, T[i]);
      isBasic[basis[i]] = 1;
    }
    this.initBasis = Int32Array.from(basis);
  }

  /** Row i of the initial tableau (in terms of the initial basis), written into t. */
  private initialRow(i: number, t: Float64Array): void {
    const row = this.lp.rows[i];
    const s = this.n + i;
    t.fill(0);
    const art = this.rowArt[i];
    if (art < 0) {
      for (let k = 0; k < row.index.length; k++) t[row.index[k]] -= row.value[k];
      t[s] = 1;
    } else {
      const g = this.rowSign[i];
      for (let k = 0; k < row.index.length; k++) t[row.index[k]] += row.value[k] / g;
      t[s] = -1 / g;
      t[art] = 1;
    }
  }

  private readonly initBasis: Int32Array;

  // ------------------------------------------------------------ primal simplex

  private computeReducedCosts(c: Float64Array): void {
    const { d, T, basis, m, N } = this;
    d.set(c);
    for (let i = 0; i < m; i++) {
      const cb = c[basis[i]];
      if (cb === 0) continue;
      const t = T[i];
      for (let j = 0; j < N; j++) if (t[j] !== 0) d[j] -= cb * t[j];
    }
    for (let i = 0; i < m; i++) d[basis[i]] = 0;
  }

  /** Pivots column q into the basis at row r (sparse in the pivot row). */
  private pivot(r: number, q: number): void {
    const { T, d, m, N, nz, isBasic, basis } = this;
    const pr = T[r];
    const piv = pr[q];
    let count = 0;
    for (let j = 0; j < N; j++) {
      const v = pr[j];
      if (v === 0) continue;
      const w = v / piv;
      if (w > -1e-14 && w < 1e-14) {
        pr[j] = 0;
        continue;
      }
      pr[j] = w;
      nz[count++] = j;
    }
    pr[q] = 1;
    for (let i = 0; i < m; i++) {
      if (i === r) continue;
      const t = T[i];
      const f = t[q];
      if (f === 0) continue;
      for (let k = 0; k < count; k++) {
        const j = nz[k];
        t[j] -= f * pr[j];
      }
      t[q] = 0;
    }
    const dq = d[q];
    if (dq !== 0) {
      for (let k = 0; k < count; k++) {
        const j = nz[k];
        d[j] -= dq * pr[j];
      }
      d[q] = 0;
    }
    const b = basis[r];
    isBasic[b] = 0;
    isBasic[q] = 1;
    basis[r] = q;
  }

  /** Checks the clock every 16 iterations. */
  private outOfTime(): boolean {
    if ((this.iterations & 15) !== 0 || performance.now() <= this.deadline) return false;
    this.timedOut = true;
    return true;
  }

  private primal(c: Float64Array, maxIterations: number): Exclude<SimplexStatus, 'infeasible'> {
    const { T, x, lb, ub, d, basis, isBasic, m, N } = this;
    this.computeReducedCosts(c);
    let degenerate = 0;
    for (;;) {
      if (this.iterations >= maxIterations || this.outOfTime()) return 'iteration_limit';
      const bland = degenerate > DEGENERATE_LIMIT;

      let q = -1;
      let dir = 0;
      let best = 0;
      for (let j = 0; j < N; j++) {
        if (isBasic[j] || ub[j] - lb[j] <= FEAS_TOL) continue;
        const dj = d[j];
        let score: number;
        let jdir: number;
        if (dj < -OPT_TOL && x[j] < ub[j] - FEAS_TOL) {
          score = -dj;
          jdir = 1;
        } else if (dj > OPT_TOL && x[j] > lb[j] + FEAS_TOL) {
          score = dj;
          jdir = -1;
        } else continue;
        if (bland) {
          q = j;
          dir = jdir;
          break;
        }
        if (score > best) {
          best = score;
          q = j;
          dir = jdir;
        }
      }
      if (q < 0) return 'optimal';

      let tMin = dir > 0 ? ub[q] - x[q] : x[q] - lb[q];
      let leave = -1;
      let leaveAlpha = 0;
      for (let i = 0; i < m; i++) {
        const alpha = T[i][q] * dir;
        if (alpha > -PIVOT_TOL && alpha < PIVOT_TOL) continue;
        const b = basis[i];
        let ti: number;
        if (alpha > 0) {
          if (!isFinite(lb[b])) continue;
          ti = (x[b] - lb[b]) / alpha;
        } else {
          if (!isFinite(ub[b])) continue;
          ti = (ub[b] - x[b]) / -alpha;
        }
        if (ti < 0) ti = 0;
        const absAlpha = Math.abs(alpha);
        if (ti < tMin - 1e-12 || (leave >= 0 && ti <= tMin + 1e-12 && (bland ? b < basis[leave] : absAlpha > leaveAlpha))) {
          tMin = ti;
          leave = i;
          leaveAlpha = absAlpha;
        }
      }
      if (!isFinite(tMin)) return 'unbounded';

      this.iterations++;
      degenerate = tMin <= 1e-12 ? degenerate + 1 : 0;
      if (tMin > 0) {
        x[q] += dir * tMin;
        for (let i = 0; i < m; i++) {
          const a = T[i][q];
          if (a !== 0) x[basis[i]] -= a * dir * tMin;
        }
      }
      if (leave < 0) continue;
      const b = basis[leave];
      x[b] = T[leave][q] * dir > 0 ? lb[b] : ub[b];
      this.pivot(leave, q);
    }
  }

  /** Two-phase primal simplex from the starting basis. */
  solve(maxIterations = 1000 + 50 * (this.m + this.N)): SimplexStatus {
    if (this.trivial) return 'infeasible';
    const { n, m, N, x, ub, isBasic } = this;
    if (N > n + m) {
      const c1 = new Float64Array(N);
      for (let j = this.firstArt; j < N; j++) c1[j] = 1;
      const st = this.primal(c1, maxIterations);
      if (st === 'iteration_limit') return st;
      let infeas = 0;
      for (let j = this.firstArt; j < N; j++) infeas += x[j];
      if (infeas > 1e-7) return 'infeasible';
      for (let j = this.firstArt; j < N; j++) {
        ub[j] = 0;
        if (!isBasic[j]) x[j] = 0;
      }
    }
    const st = this.primal(this.cost, maxIterations);
    if (st === 'optimal') this.recomputeBasics();
    return st;
  }

  // ------------------------------------------------------------ warm starts

  /** Changes the bounds of structural column j (keeping the basis). */
  setBounds(j: number, lo: number, hi: number): void {
    const { lb, ub, x, T, basis, m, isBasic, d } = this;
    lb[j] = lo;
    ub[j] = hi;
    if (isBasic[j]) return;
    const old = x[j];
    let v: number;
    if (lo === hi) v = lo;
    else if (d[j] > 0 && isFinite(lo)) v = lo;
    else if (d[j] < 0 && isFinite(hi)) v = hi;
    else v = Math.min(Math.max(old, lo), hi);
    if (!isFinite(v)) v = isFinite(lo) ? lo : isFinite(hi) ? hi : 0;
    if (v === old) return;
    const delta = v - old;
    x[j] = v;
    for (let i = 0; i < m; i++) {
      const a = T[i][j];
      if (a !== 0) x[basis[i]] -= a * delta;
    }
  }

  /**
   * Dual simplex: re-optimises after bound changes, starting from a dual
   * feasible basis.  Returns null when the basis is not dual feasible.
   */
  dual(maxIterations = this.iterations + 1000 + 20 * (this.m + this.N)): SimplexStatus | null {
    const { T, x, lb, ub, d, basis, isBasic, m, N } = this;
    // Dual feasibility of the non-basic columns.
    for (let j = 0; j < N; j++) {
      if (isBasic[j] || ub[j] - lb[j] <= FEAS_TOL) continue;
      const atLb = x[j] <= lb[j] + FEAS_TOL;
      const atUb = x[j] >= ub[j] - FEAS_TOL;
      if (atLb && d[j] < -1e-7) return null;
      if (atUb && d[j] > 1e-7) return null;
      if (!atLb && !atUb && Math.abs(d[j]) > 1e-7) return null;
    }
    let stall = 0;
    for (;;) {
      if (this.iterations >= maxIterations || this.outOfTime()) return 'iteration_limit';
      // Leaving row: the most infeasible basic variable.
      let r = -1;
      let worst = FEAS_TOL * 10;
      for (let i = 0; i < m; i++) {
        const b = basis[i];
        const v = x[b];
        const inf = v < lb[b] ? lb[b] - v : v > ub[b] ? v - ub[b] : 0;
        const scaled = inf / Math.max(1, Math.abs(v));
        if (scaled > worst) {
          worst = scaled;
          r = i;
        }
      }
      if (r < 0) {
        this.recomputeBasics();
        return 'optimal';
      }
      const b = basis[r];
      const increase = x[b] < lb[b];
      const target = increase ? lb[b] : ub[b];
      const row = T[r];
      // Entering column: keeps the reduced costs dual feasible (minimum ratio).
      let q = -1;
      let bestRatio = Infinity;
      let bestAlpha = 0;
      const bland = stall > 200;
      for (let j = 0; j < N; j++) {
        if (isBasic[j] || ub[j] - lb[j] <= FEAS_TOL) continue;
        const a = row[j];
        if (a > -PIVOT_TOL && a < PIVOT_TOL) continue;
        // x_b changes by -a * delta: the move of x_j that pushes x_b towards target.
        const dir = increase ? (a < 0 ? 1 : -1) : a > 0 ? 1 : -1;
        if (dir > 0 && !(x[j] < ub[j] - FEAS_TOL)) continue;
        if (dir < 0 && !(x[j] > lb[j] + FEAS_TOL)) continue;
        const ratio = Math.abs(d[j]) / Math.abs(a);
        const absA = Math.abs(a);
        if (ratio < bestRatio - 1e-12 || (ratio <= bestRatio + 1e-12 && (bland ? j < q : absA > bestAlpha))) {
          bestRatio = ratio;
          q = j;
          bestAlpha = absA;
        }
      }
      if (q < 0) return 'infeasible';
      this.iterations++;
      stall = bestRatio <= 1e-12 ? stall + 1 : 0;
      const delta = (target - x[b]) / -row[q];
      x[q] += delta;
      for (let i = 0; i < m; i++) {
        const a = T[i][q];
        if (a !== 0) x[basis[i]] -= a * delta;
      }
      x[b] = target;
      this.pivot(r, q);
    }
  }

  snapshot(): Snapshot {
    const { N, x, lb, ub, isBasic } = this;
    const status = new Uint8Array(N);
    const other = new Map<number, number>();
    for (let j = 0; j < N; j++) {
      if (isBasic[j] || x[j] === lb[j]) continue;
      if (x[j] === ub[j]) status[j] = 1;
      else {
        status[j] = 2;
        other.set(j, x[j]);
      }
    }
    return { basis: Int32Array.from(this.basis), status, other };
  }

  /**
   * Rebuilds the tableau for a saved basis (Gauss-Jordan from the initial
   * rows).  Bounds are kept as they are; returns false when the basis is singular.
   */
  restore(snap: Snapshot): boolean {
    const { m, N, isBasic, basis } = this;
    for (let i = 0; i < m; i++) this.initialRow(i, this.T[i]);
    // The initial rows are in terms of the initial basis.
    basis.set(this.initBasis);
    isBasic.fill(0);
    for (let i = 0; i < m; i++) isBasic[basis[i]] = 1;
    const target = new Uint8Array(N);
    for (const b of snap.basis) target[b] = 1;
    for (const b of snap.basis) {
      if (isBasic[b]) continue;
      let r = -1;
      let best = 1e-9;
      for (let i = 0; i < m; i++) {
        if (target[basis[i]]) continue;
        const a = Math.abs(this.T[i][b]);
        if (a > best) {
          best = a;
          r = i;
        }
      }
      if (r < 0) return false;
      this.pivotRowsOnly(r, b);
    }
    const { x, lb, ub } = this;
    for (let j = 0; j < N; j++) {
      if (isBasic[j]) continue;
      const st = snap.status[j];
      let v = st === 0 ? lb[j] : st === 1 ? ub[j] : (snap.other.get(j) ?? 0);
      if (v < lb[j]) v = lb[j];
      if (v > ub[j]) v = ub[j];
      if (!isFinite(v)) v = isFinite(lb[j]) ? lb[j] : isFinite(ub[j]) ? ub[j] : 0;
      x[j] = v;
    }
    this.recomputeBasics();
    this.computeReducedCosts(this.cost);
    return true;
  }

  /** A pivot without reduced costs (used while rebuilding). */
  private pivotRowsOnly(r: number, q: number): void {
    const { T, m, N, nz, isBasic, basis } = this;
    const pr = T[r];
    const piv = pr[q];
    let count = 0;
    for (let j = 0; j < N; j++) {
      if (pr[j] === 0) continue;
      pr[j] /= piv;
      nz[count++] = j;
    }
    pr[q] = 1;
    for (let i = 0; i < m; i++) {
      if (i === r) continue;
      const t = T[i];
      const f = t[q];
      if (f === 0) continue;
      for (let k = 0; k < count; k++) t[nz[k]] -= f * pr[nz[k]];
      t[q] = 0;
    }
    isBasic[basis[r]] = 0;
    isBasic[q] = 1;
    basis[r] = q;
  }

  /** Basic values from the non-basic ones (limits drift). */
  private recomputeBasics(): void {
    const { T, x, basis, isBasic, m, N } = this;
    for (let i = 0; i < m; i++) {
      const t = T[i];
      let v = 0;
      for (let j = 0; j < N; j++) if (t[j] !== 0 && !isBasic[j]) v -= t[j] * x[j];
      x[basis[i]] = v;
    }
  }

  objective(): number {
    let obj = this.lp.objConstant;
    for (let j = 0; j < this.n; j++) obj += this.lp.objective[j] * this.x[j];
    return obj;
  }

  result(status: SimplexStatus): LPResult {
    const { lp, n, m, x, d } = this;
    if (status !== 'optimal') return emptyResult(lp, status, this.iterations);
    const xs = new Float64Array(n);
    let obj = lp.objConstant;
    for (let j = 0; j < n; j++) {
      xs[j] = clean(x[j]);
      obj += lp.objective[j] * xs[j];
    }
    const duals = new Float64Array(m);
    for (let i = 0; i < m; i++) duals[i] = clean(d[n + i]);
    const rc = new Float64Array(n);
    for (let j = 0; j < n; j++) rc[j] = clean(d[j]);
    return { status, objective: obj, x: xs, duals, reducedCosts: rc, iterations: this.iterations };
  }
}

/** Rounds away floating-point noise (|v| < 1e-11 to 0, near-integers to the integer). */
export function clean(v: number): number {
  if (Math.abs(v) < 1e-11) return 0;
  const r = Math.round(v);
  if (Math.abs(v - r) < Math.min(1e-6, 1e-9 * Math.max(1, Math.abs(v)))) return r;
  return v;
}
