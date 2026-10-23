/**
 * LP-based branch and bound for mixed-integer programs.
 *
 * Node selection follows the CPLEX "nodeSel" parameter used by the OPL Studio
 * tutorial: 0 = depth-first, anything else = best-bound.  Branching is on the
 * most fractional integer column.  Once an optimum is found the integer
 * columns are fixed and the LP is re-solved to report duals and reduced costs
 * (as CPLEX does for MIPs).
 */

import { type LinearProgram, type MIPResult } from './lp.js';
import { solveLP } from './simplex.js';

const INT_TOL = 1e-6;

export interface MIPOptions {
  /** 0 = depth-first, 1 (default) = best-bound. */
  nodeSelection?: number;
  maxNodes?: number;
  /** Seconds. */
  timeLimit?: number;
  /** Relative optimality gap at which a node is pruned. */
  relativeGap?: number;
}

interface Node {
  lower: Float64Array;
  upper: Float64Array;
  bound: number;
  seq: number;
}

export function solveMIP(lp: LinearProgram, options: MIPOptions = {}): MIPResult {
  const n = lp.numVars;
  const ints: number[] = [];
  for (let j = 0; j < n; j++) if (lp.integer[j]) ints.push(j);

  const rootLower = Float64Array.from(lp.lower);
  const rootUpper = Float64Array.from(lp.upper);
  for (const j of ints) {
    rootLower[j] = Math.ceil(rootLower[j] - INT_TOL);
    rootUpper[j] = Math.floor(rootUpper[j] + INT_TOL);
  }

  if (ints.length === 0) {
    const r = solveLP(lp, rootLower, rootUpper);
    return {
      status: r.status === 'iteration_limit' ? 'limit' : r.status,
      objective: r.objective,
      bound: r.objective,
      x: r.x,
      duals: r.duals,
      reducedCosts: r.reducedCosts,
      iterations: r.iterations,
      nodes: 0,
    };
  }

  // Objective values are integral when only integer columns with integer
  // coefficients appear in it: lets us prune nodes that cannot improve by 1.
  let integralObjective = true;
  for (let j = 0; j < n; j++) {
    const c = lp.objective[j];
    if (c !== 0 && (!lp.integer[j] || !Number.isInteger(c))) integralObjective = false;
  }

  const depthFirst = (options.nodeSelection ?? 1) === 0;
  const maxNodes = options.maxNodes ?? 1_000_000;
  const deadline = options.timeLimit ? performance.now() + options.timeLimit * 1000 : Infinity;
  const relGap = options.relativeGap ?? 1e-9;

  let incumbent = Infinity;
  let bestX: Float64Array | null = null;
  let iterations = 0;
  let nodes = 0;
  let seq = 0;
  let hitLimit = false;
  let unbounded = false;

  const cutoff = (): number => {
    if (!isFinite(incumbent)) return Infinity;
    if (integralObjective) return incumbent - 1 + INT_TOL;
    return incumbent - Math.max(1e-9, relGap * Math.abs(incumbent));
  };

  const open = new NodeQueue(depthFirst);
  open.push({ lower: rootLower, upper: rootUpper, bound: -Infinity, seq: seq++ });

  while (open.size > 0) {
    if (nodes >= maxNodes || performance.now() > deadline) {
      hitLimit = true;
      break;
    }
    const node = open.pop();
    if (node.bound >= cutoff()) continue;
    const r = solveLP(lp, node.lower, node.upper);
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
    if (r.objective >= cutoff()) continue;

    let branch = -1;
    let bestFrac = 0;
    for (const j of ints) {
      const v = r.x[j];
      const f = v - Math.floor(v);
      const dist = Math.min(f, 1 - f);
      if (dist > INT_TOL && dist > bestFrac) {
        bestFrac = dist;
        branch = j;
      }
    }
    if (branch < 0) {
      incumbent = r.objective;
      bestX = Float64Array.from(r.x);
      for (const j of ints) bestX[j] = Math.round(bestX[j]);
      continue;
    }

    const v = r.x[branch];
    const down: Node = {
      lower: node.lower,
      upper: Float64Array.from(node.upper),
      bound: r.objective,
      seq: 0,
    };
    down.upper[branch] = Math.floor(v);
    const up: Node = {
      lower: Float64Array.from(node.lower),
      upper: node.upper,
      bound: r.objective,
      seq: 0,
    };
    up.lower[branch] = Math.ceil(v);
    // The child pushed last is explored first by depth-first search.
    const upFirst = v - Math.floor(v) >= 0.5;
    const [first, second] = upFirst ? [up, down] : [down, up];
    second.seq = seq++;
    first.seq = seq++;
    open.push(second);
    open.push(first);
  }

  if (unbounded && !bestX) {
    return finish(lp, 'unbounded', -Infinity, -Infinity, null, iterations, nodes);
  }
  if (!bestX) {
    return finish(lp, hitLimit ? 'limit' : 'infeasible', Infinity, -Infinity, null, iterations, nodes);
  }
  const bound = hitLimit ? Math.min(incumbent, open.minBound()) : incumbent;
  return finish(lp, hitLimit ? 'feasible' : 'optimal', incumbent, bound, bestX, iterations, nodes);
}

function finish(
  lp: LinearProgram,
  status: MIPResult['status'],
  objective: number,
  bound: number,
  x: Float64Array | null,
  iterations: number,
  nodes: number,
): MIPResult {
  const n = lp.numVars;
  let duals: Float64Array = new Float64Array(lp.rows.length);
  let reducedCosts: Float64Array = new Float64Array(n);
  if (x) {
    // Fix the integer columns and re-solve for duals and reduced costs.
    const lower = Float64Array.from(lp.lower);
    const upper = Float64Array.from(lp.upper);
    for (let j = 0; j < n; j++) {
      if (lp.integer[j]) lower[j] = upper[j] = x[j];
    }
    const fixed = solveLP(lp, lower, upper);
    iterations += fixed.iterations;
    if (fixed.status === 'optimal') {
      duals = fixed.duals;
      reducedCosts = fixed.reducedCosts;
      for (let j = 0; j < n; j++) if (!lp.integer[j]) x[j] = fixed.x[j];
    }
  }
  return {
    status,
    objective,
    bound,
    x: x ?? new Float64Array(n),
    duals,
    reducedCosts,
    iterations,
    nodes,
  };
}

/** Stack for depth-first search, binary heap on the bound for best-bound search. */
class NodeQueue {
  private items: Node[] = [];
  constructor(private readonly depthFirst: boolean) {}

  get size(): number {
    return this.items.length;
  }

  minBound(): number {
    let b = Infinity;
    for (const it of this.items) b = Math.min(b, it.bound);
    return b;
  }

  push(node: Node): void {
    const a = this.items;
    a.push(node);
    if (this.depthFirst) return;
    let i = a.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!this.less(a[i], a[p])) break;
      [a[i], a[p]] = [a[p], a[i]];
      i = p;
    }
  }

  pop(): Node {
    const a = this.items;
    if (this.depthFirst) return a.pop()!;
    const top = a[0];
    const last = a.pop()!;
    if (a.length > 0) {
      a[0] = last;
      let i = 0;
      for (;;) {
        const l = 2 * i + 1;
        const r = l + 1;
        let s = i;
        if (l < a.length && this.less(a[l], a[s])) s = l;
        if (r < a.length && this.less(a[r], a[s])) s = r;
        if (s === i) break;
        [a[i], a[s]] = [a[s], a[i]];
        i = s;
      }
    }
    return top;
  }

  /** Lower bound first; among equal bounds the most recently created (deepest) node. */
  private less(a: Node, b: Node): boolean {
    return a.bound < b.bound || (a.bound === b.bound && a.seq > b.seq);
  }
}
