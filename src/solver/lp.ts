/**
 * Problem and result types shared by the LP and MIP solvers.
 *
 * Problems are always stated as minimisations; the model layer negates the
 * objective of a maximisation (and the resulting duals / reduced costs).
 */

export interface Row {
  /** Structural column indices of the non-zero coefficients. */
  index: number[];
  value: number[];
  /** Row activity bounds: lower <= sum(value[k] * x[index[k]]) <= upper. */
  lower: number;
  upper: number;
}

export interface LinearProgram {
  numVars: number;
  /** Objective coefficients (minimised). */
  objective: Float64Array;
  objConstant: number;
  lower: Float64Array;
  upper: Float64Array;
  /** 1 when the column must take an integer value. */
  integer: Uint8Array;
  rows: Row[];
}

export type LPStatus = 'optimal' | 'infeasible' | 'unbounded' | 'iteration_limit';

export interface LPResult {
  status: LPStatus;
  objective: number;
  x: Float64Array;
  /** Row duals: d(objective) / d(row bound) at the optimum. */
  duals: Float64Array;
  /** Reduced costs of the structural columns. */
  reducedCosts: Float64Array;
  iterations: number;
}

export type MIPStatus = 'optimal' | 'feasible' | 'infeasible' | 'unbounded' | 'limit';

export interface MIPResult {
  status: MIPStatus;
  objective: number;
  /** Best proven bound on the objective (equal to objective when optimal). */
  bound: number;
  x: Float64Array;
  duals: Float64Array;
  reducedCosts: Float64Array;
  iterations: number;
  nodes: number;
}

export function emptyResult(lp: LinearProgram, status: LPStatus, iterations = 0): LPResult {
  return {
    status,
    objective: status === 'unbounded' ? -Infinity : Infinity,
    x: new Float64Array(lp.numVars),
    duals: new Float64Array(lp.rows.length),
    reducedCosts: new Float64Array(lp.numVars),
    iterations,
  };
}
