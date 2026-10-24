/**
 * LP solving entry point: the dense tableau simplex (dense.ts) for small
 * problems, the sparse revised simplex (sparse.ts) for large ones.
 */

import { DenseSimplex, type SimplexStatus, type Snapshot } from './dense.js';
import type { LinearProgram, LPResult } from './lp.js';
import { SparseSimplex } from './sparse.js';

export { clean } from './dense.js';

export interface SimplexOptions {
  maxIterations?: number;
  /** performance.now() time at which to stop with 'iteration_limit'. */
  deadline?: number;
}

/** What branch and bound needs from a simplex implementation. */
export interface Simplex {
  readonly lb: Float64Array;
  readonly ub: Float64Array;
  readonly x: Float64Array;
  readonly d: Float64Array;
  iterations: number;
  deadline: number;
  timedOut: boolean;
  solve(maxIterations?: number): SimplexStatus;
  dual(): SimplexStatus | null;
  setBounds(j: number, lo: number, hi: number): void;
  snapshot(): Snapshot;
  restore(snap: Snapshot): boolean;
  objective(): number;
  result(status: SimplexStatus): LPResult;
}

/** Dense tableau entries above which the sparse simplex is used. */
const DENSE_LIMIT = 2_000_000;

/** A simplex for lp; OPL_LP_ENGINE=dense / sparse forces one. */
export function createSimplex(lp: LinearProgram, lower: Float64Array = lp.lower, upper: Float64Array = lp.upper): Simplex {
  const engine = process.env.OPL_LP_ENGINE;
  const m = lp.rows.length;
  const sparse = engine === 'sparse' || (engine !== 'dense' && m * (lp.numVars + 2 * m) > DENSE_LIMIT);
  return sparse ? new SparseSimplex(lp, lower, upper) : new DenseSimplex(lp, lower, upper);
}

export function solveLP(
  lp: LinearProgram,
  lower: Float64Array = lp.lower,
  upper: Float64Array = lp.upper,
  options: SimplexOptions = {},
): LPResult {
  const s = createSimplex(lp, lower, upper);
  if (options.deadline !== undefined) s.deadline = options.deadline;
  return s.result(s.solve(options.maxIterations));
}
