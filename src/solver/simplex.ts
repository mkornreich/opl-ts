/**
 * Dense bounded-variable primal simplex (two phases).
 *
 * Every row i gets a logical column s_i with  a_i . x - s_i = 0  and
 * row.lower <= s_i <= row.upper, so all bounds live on columns.  Rows whose
 * activity at the starting point violates its bounds get an artificial column;
 * phase 1 minimises the sum of artificials, phase 2 the real objective.
 * Duals are read off the reduced costs of the logical columns.
 */

import { emptyResult, type LinearProgram, type LPResult } from './lp.js';

const FEAS_TOL = 1e-9;
const OPT_TOL = 1e-9;
const PIVOT_TOL = 1e-10;
/** Consecutive degenerate pivots before switching to Bland's rule. */
const DEGENERATE_LIMIT = 50;

export interface SimplexOptions {
  maxIterations?: number;
}

export function solveLP(
  lp: LinearProgram,
  lower: Float64Array = lp.lower,
  upper: Float64Array = lp.upper,
  options: SimplexOptions = {},
): LPResult {
  const n = lp.numVars;
  const m = lp.rows.length;

  for (let j = 0; j < n; j++) {
    if (lower[j] > upper[j] + FEAS_TOL) return emptyResult(lp, 'infeasible');
  }

  // Starting point: every structural column non-basic at a finite bound (free columns at 0).
  const start = new Float64Array(n);
  for (let j = 0; j < n; j++) {
    start[j] = isFinite(lower[j]) ? lower[j] : isFinite(upper[j]) ? upper[j] : 0;
  }

  const activity = new Float64Array(m);
  let numArt = 0;
  const needsArt = new Uint8Array(m);
  for (let i = 0; i < m; i++) {
    const row = lp.rows[i];
    if (row.lower > row.upper + FEAS_TOL) return emptyResult(lp, 'infeasible');
    let r = 0;
    for (let k = 0; k < row.index.length; k++) r += row.value[k] * start[row.index[k]];
    activity[i] = r;
    if (r < row.lower - FEAS_TOL || r > row.upper + FEAS_TOL) {
      needsArt[i] = 1;
      numArt++;
    }
  }

  const N = n + m + numArt;
  const lb = new Float64Array(N);
  const ub = new Float64Array(N);
  const x = new Float64Array(N);
  const T: Float64Array[] = new Array(m);
  const basis = new Int32Array(m);
  const isBasic = new Uint8Array(N);

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
    const t = new Float64Array(N);
    T[i] = t;
    if (!needsArt[i]) {
      // -a_i x + s_i = 0 with s_i basic.
      for (let k = 0; k < row.index.length; k++) t[row.index[k]] -= row.value[k];
      t[s] = 1;
      basis[i] = s;
      x[s] = activity[i];
    } else {
      // (a_i x - s_i) / g + art = 0 with art basic and positive.
      const v = activity[i] < row.lower ? row.lower : row.upper;
      const d = activity[i] - v;
      const g = d > 0 ? -1 : 1;
      for (let k = 0; k < row.index.length; k++) t[row.index[k]] += row.value[k] / g;
      t[s] = -1 / g;
      t[art] = 1;
      lb[art] = 0;
      ub[art] = Infinity;
      x[s] = v;
      x[art] = Math.abs(d);
      basis[i] = art;
      art++;
    }
    isBasic[basis[i]] = 1;
  }

  const maxIterations = options.maxIterations ?? 1000 + 50 * (m + N);
  let iterations = 0;
  const d = new Float64Array(N);

  const computeReducedCosts = (c: Float64Array) => {
    d.set(c);
    for (let i = 0; i < m; i++) {
      const cb = c[basis[i]];
      if (cb === 0) continue;
      const t = T[i];
      for (let j = 0; j < N; j++) d[j] -= cb * t[j];
    }
    for (let i = 0; i < m; i++) d[basis[i]] = 0;
  };

  /** Runs simplex iterations on cost vector c. Returns the terminal state. */
  const iterate = (c: Float64Array): 'optimal' | 'unbounded' | 'iteration_limit' => {
    computeReducedCosts(c);
    let degenerate = 0;
    for (;;) {
      if (iterations >= maxIterations) return 'iteration_limit';
      const bland = degenerate > DEGENERATE_LIMIT;

      // Pricing.
      let q = -1;
      let dir = 0;
      let best = 0;
      for (let j = 0; j < N; j++) {
        if (isBasic[j] || ub[j] - lb[j] <= FEAS_TOL) continue;
        const dj = d[j];
        let score = 0;
        let jdir = 0;
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

      // Ratio test.
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
        if (
          ti < tMin - 1e-12 ||
          (leave >= 0 && ti <= tMin + 1e-12 &&
            (bland ? b < basis[leave] : absAlpha > leaveAlpha))
        ) {
          tMin = ti;
          leave = i;
          leaveAlpha = absAlpha;
        }
      }
      if (!isFinite(tMin)) return 'unbounded';

      iterations++;
      degenerate = tMin <= 1e-12 ? degenerate + 1 : 0;

      // Move along the edge.
      if (tMin > 0) {
        x[q] += dir * tMin;
        for (let i = 0; i < m; i++) {
          const a = T[i][q];
          if (a !== 0) x[basis[i]] -= a * dir * tMin;
        }
      }
      if (leave < 0) continue; // bound flip of the entering column

      const b = basis[leave];
      x[b] = T[leave][q] * dir > 0 ? lb[b] : ub[b];

      // Pivot on (leave, q).
      const pr = T[leave];
      const piv = pr[q];
      for (let j = 0; j < N; j++) pr[j] /= piv;
      pr[q] = 1;
      for (let i = 0; i < m; i++) {
        if (i === leave) continue;
        const t = T[i];
        const f = t[q];
        if (f === 0) continue;
        for (let j = 0; j < N; j++) t[j] -= f * pr[j];
        t[q] = 0;
      }
      const dq = d[q];
      if (dq !== 0) {
        for (let j = 0; j < N; j++) d[j] -= dq * pr[j];
        d[q] = 0;
      }
      isBasic[b] = 0;
      isBasic[q] = 1;
      basis[leave] = q;
    }
  };

  // Phase 1.
  if (numArt > 0) {
    const c1 = new Float64Array(N);
    for (let j = n + m; j < N; j++) c1[j] = 1;
    const st = iterate(c1);
    if (st === 'iteration_limit') return emptyResult(lp, 'iteration_limit', iterations);
    let infeas = 0;
    for (let j = n + m; j < N; j++) infeas += x[j];
    if (infeas > 1e-7) return emptyResult(lp, 'infeasible', iterations);
    for (let j = n + m; j < N; j++) {
      ub[j] = 0;
      if (!isBasic[j]) x[j] = 0;
    }
  }

  // Phase 2.
  const c2 = new Float64Array(N);
  c2.set(lp.objective);
  const st = iterate(c2);
  if (st !== 'optimal') return emptyResult(lp, st, iterations);

  // Recompute basic values from the non-basic ones to limit drift.
  for (let i = 0; i < m; i++) {
    const t = T[i];
    let v = 0;
    for (let j = 0; j < N; j++) if (!isBasic[j] && t[j] !== 0) v -= t[j] * x[j];
    x[basis[i]] = v;
  }

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
  return { status: 'optimal', objective: obj, x: xs, duals, reducedCosts: rc, iterations };
}

/** Rounds away floating-point noise (|v| < 1e-11 to 0, near-integers to the integer). */
export function clean(v: number): number {
  if (Math.abs(v) < 1e-11) return 0;
  const r = Math.round(v);
  if (Math.abs(v - r) < Math.min(1e-6, 1e-9 * Math.max(1, Math.abs(v)))) return r;
  return v;
}
