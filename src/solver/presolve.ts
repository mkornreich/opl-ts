/**
 * MIP presolve: removes fixed columns, turns singleton rows into bounds and
 * drops empty and redundant rows, repeating until nothing changes.  The
 * reduced problem keeps the objective value (fixed columns move into the
 * constant); postsolve puts the fixed values back.
 */

import type { LinearProgram, Row } from './lp.js';

export interface Presolved {
  lp: LinearProgram;
  /** Original column of each reduced column. */
  cols: number[];
  /** Values of the removed (fixed) columns, by original column. */
  fixed: Map<number, number>;
  infeasible: boolean;
}

const TOL = 1e-9;

export function presolve(lp: LinearProgram): Presolved {
  const n = lp.numVars;
  const lower = Float64Array.from(lp.lower);
  const upper = Float64Array.from(lp.upper);
  for (let j = 0; j < n; j++) {
    if (lp.integer[j]) {
      lower[j] = Math.ceil(lower[j] - 1e-6);
      upper[j] = Math.floor(upper[j] + 1e-6);
    }
  }
  // Rows as mutable copies; bounds shift as columns are fixed.
  const rows = lp.rows.map((r) => ({ index: [...r.index], value: [...r.value], lower: r.lower, upper: r.upper, alive: true }));
  const infeasible = (): Presolved => ({ lp, cols: [], fixed: new Map(), infeasible: true });
  const tol = (b: number) => (isFinite(b) ? TOL * Math.max(1, Math.abs(b)) : 0);
  for (let pass = 0; ; pass++) {
    if (pass === 50) break;
    let changed = false;
    for (let j = 0; j < n; j++) if (lower[j] > upper[j] + tol(lower[j])) return infeasible();
    for (const r of rows) {
      if (!r.alive) continue;
      // Drop fixed columns from the row.
      let k = 0;
      for (let t = 0; t < r.index.length; t++) {
        const j = r.index[t];
        const a = r.value[t];
        if (a === 0) continue;
        if (lower[j] === upper[j]) {
          r.lower -= a * lower[j];
          r.upper -= a * lower[j];
          changed = true;
          continue;
        }
        r.index[k] = j;
        r.value[k++] = a;
      }
      r.index.length = r.value.length = k;
      if (k === 0) {
        if (r.lower > tol(r.lower) || r.upper < -tol(r.upper)) return infeasible();
        r.alive = false;
        changed = true;
        continue;
      }
      if (k === 1) {
        // a x in [l, u]: a bound on x.
        const j = r.index[0];
        const a = r.value[0];
        let lo = a > 0 ? r.lower / a : r.upper / a;
        let hi = a > 0 ? r.upper / a : r.lower / a;
        if (lp.integer[j]) {
          lo = Math.ceil(lo - 1e-6);
          hi = Math.floor(hi + 1e-6);
        }
        if (lo > lower[j]) lower[j] = lo;
        if (hi < upper[j]) upper[j] = hi;
        if (lower[j] > upper[j] + tol(lower[j])) return infeasible();
        if (isFinite(lower[j]) && isFinite(upper[j]) && upper[j] - lower[j] <= tol(lower[j])) upper[j] = lower[j];
        r.alive = false;
        changed = true;
        continue;
      }
      // Redundant: the activity range is inside the row bounds.
      let min = 0;
      let max = 0;
      for (let t = 0; t < k; t++) {
        const a = r.value[t];
        const j = r.index[t];
        min += a > 0 ? a * lower[j] : a * upper[j];
        max += a > 0 ? a * upper[j] : a * lower[j];
      }
      if (min > r.upper + tol(r.upper) || max < r.lower - tol(r.lower)) return infeasible();
      if (min >= r.lower - tol(r.lower) && max <= r.upper + tol(r.upper)) {
        r.alive = false;
        changed = true;
      }
    }
    if (!changed) break;
  }

  const fixed = new Map<number, number>();
  const cols: number[] = [];
  const at = new Int32Array(n).fill(-1);
  let constant = lp.objConstant;
  for (let j = 0; j < n; j++) {
    if (lower[j] === upper[j]) {
      fixed.set(j, lower[j]);
      constant += lp.objective[j] * lower[j];
    } else {
      at[j] = cols.length;
      cols.push(j);
    }
  }
  const m = cols.length;
  const reduced: LinearProgram = {
    numVars: m,
    objective: Float64Array.from(cols, (j) => lp.objective[j]),
    objConstant: constant,
    lower: Float64Array.from(cols, (j) => lower[j]),
    upper: Float64Array.from(cols, (j) => upper[j]),
    integer: Uint8Array.from(cols, (j) => lp.integer[j]),
    rows: rows.filter((r) => r.alive).map((r): Row => {
      // Columns fixed in the last pass leave the row here.
      const index: number[] = [];
      const value: number[] = [];
      let { lower: lo, upper: hi } = r;
      r.index.forEach((j, t) => {
        if (at[j] >= 0) {
          index.push(at[j]);
          value.push(r.value[t]);
        } else {
          lo -= r.value[t] * fixed.get(j)!;
          hi -= r.value[t] * fixed.get(j)!;
        }
      });
      return { index, value, lower: lo, upper: hi };
    }),
  };
  return { lp: reduced, cols, fixed, infeasible: false };
}

/** A solution of the reduced problem as one of the original. */
export function postsolve(p: Presolved, n: number, x: Float64Array): Float64Array {
  const out = new Float64Array(n);
  for (const [j, v] of p.fixed) out[j] = v;
  p.cols.forEach((j, k) => (out[j] = x[k]));
  return out;
}
