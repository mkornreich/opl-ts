/**
 * LP-based branch and bound for mixed-integer programs.
 *
 * - Every node is re-optimised from its parent's optimal tableau with the dual
 *   simplex (warm start); nodes reached later rebuild a saved basis.
 * - Bounds are tightened by propagation over the rows before each LP, and by
 *   reduced-cost fixing once an incumbent exists.
 * - A rounding heuristic looks for incumbents at every node.
 *
 * Node selection follows the CPLEX "nodeSel" parameter used by the OPL Studio
 * tutorial: 0 = depth-first, otherwise best-bound, diving into one child of
 * each node.  Once an optimum is found the integer columns are fixed and the
 * LP is re-solved to report duals and reduced costs (as CPLEX does for MIPs).
 */

import { DenseSimplex, type SimplexStatus, type Snapshot } from './dense.js';
import { type LinearProgram, type MIPResult } from './lp.js';
import { fits, memoryExceeded } from './memory.js';
import { createSimplex, solveLP } from './simplex.js';
import { SparseSimplex } from './sparse.js';
import { postsolve, presolve } from './presolve.js';

const INT_TOL = 1e-6;

export interface MIPOptions {
  /** 0 = depth-first, 1 (default) = best-bound. */
  nodeSelection?: number;
  maxNodes?: number;
  /** Seconds. */
  timeLimit?: number;
  /** Relative optimality gap at which a node is pruned. */
  relativeGap?: number;
  /** Internal: root cuts on, and a known solution to start from. */
  cuts?: boolean;
  start?: { x: Float64Array; objective: number };
}

/** Nodes after which the search restarts with root cuts. */
const RESTART_NODES = 2000;

/** A node stores its own bound changes on top of its parent's (bounds are rebuilt when it is processed). */
interface Node {
  up: Node | null;
  /** [column, lower, upper] triples. */
  changes: number[];
  bound: number;
  seq: number;
  /** Id of the LP state the node starts from, and that state's basis (null: solve from scratch). */
  parent: number;
  snap: Snapshot | null;
}

/** Above this many open nodes, children keep no basis (memory). */
const MAX_SNAPSHOTS = 2000;

/**
 * Rounds of Gomory mixed-integer cuts at the root (dense simplex only); the
 * cuts are valid for every integer solution, so they stay for the whole search.
 */
function withRootCuts(lp: LinearProgram, lower: Float64Array, upper: Float64Array, deadline: number): LinearProgram {
  const n = lp.numVars;
  const m = lp.rows.length;
  if (m * (n + 2 * m) > 250_000 || process.env.OPL_LP_ENGINE === 'sparse' || process.env.OPL_NO_CUTS) return lp;
  // Logical columns are integer when their row has integer coefficients on integer columns.
  let rows = lp.rows;
  let last = -Infinity;
  for (let round = 0; round < 2 && performance.now() < deadline; round++) {
    const cur = { ...lp, rows };
    const S = new DenseSimplex(cur, lower, upper);
    S.deadline = deadline;
    if (S.solve() !== 'optimal' || S.unstable) break;
    const obj = S.objective();
    if (round > 0 && obj - last <= 1e-6 * Math.max(1, Math.abs(obj))) break;
    last = obj;
    const colInt = new Uint8Array(S.N);
    colInt.set(lp.integer);
    rows.forEach((r, i) => {
      colInt[n + i] = r.index.every((j, k) => lp.integer[j] && Number.isInteger(r.value[k])) ? 1 : 0;
    });
    const cuts = S.gomoryCuts(colInt, 10);
    if (!cuts.length) break;
    rows = [...rows, ...cuts];
  }
  return rows === lp.rows ? lp : { ...lp, rows };
}

/**
 * Branch and bound; a search still open after RESTART_NODES nodes restarts
 * once with Gomory cuts at the root, keeping its best solution.
 */
export function solveMIP(input: LinearProgram, options: MIPOptions = {}): MIPResult {
  if (options.cuts !== undefined || !input.integer.some((v) => v)) return branchAndBound(input, options);
  // The presolve copies the rows twice: skip it when that does not fit the memory budget.
  const nonZeros = input.rows.reduce((n, r) => n + r.index.length, 0);
  if (process.env.OPL_NO_PRESOLVE || !fits(64 * nonZeros + 512 * input.rows.length)) return searchWithRestart(input, options);
  // Presolve, search the reduced problem, then duals from the original.
  const t0 = performance.now();
  const pre = presolve(input);
  const deadline = options.timeLimit ? t0 + options.timeLimit * 1000 : Infinity;
  if (pre.infeasible) return finish(input, 'infeasible', Infinity, -Infinity, null, 0, 0, deadline);
  if (pre.lp.numVars === 0) {
    const x = postsolve(pre, input.numVars, new Float64Array(0));
    const feasible = input.rows.every((r) => {
      let a = 0;
      for (let k = 0; k < r.index.length; k++) a += r.value[k] * x[r.index[k]];
      return a >= r.lower - 1e-7 * Math.max(1, Math.abs(r.lower)) && a <= r.upper + 1e-7 * Math.max(1, Math.abs(r.upper));
    });
    if (!feasible) return finish(input, 'infeasible', Infinity, -Infinity, null, 0, 0, deadline);
    return finish(input, 'optimal', pre.lp.objConstant, pre.lp.objConstant, x, 0, 0, deadline);
  }
  const left = options.timeLimit ? options.timeLimit - (performance.now() - t0) / 1000 : undefined;
  const r = searchWithRestart(pre.lp, { ...options, timeLimit: left });
  if (r.status !== 'optimal' && r.status !== 'feasible') return { ...r, x: new Float64Array(input.numVars), duals: new Float64Array(input.rows.length), reducedCosts: new Float64Array(input.numVars) };
  const x = postsolve(pre, input.numVars, r.x);
  return finish(input, r.status, r.objective, r.bound, x, r.iterations, r.nodes, deadline);
}

function searchWithRestart(input: LinearProgram, options: MIPOptions): MIPResult {
  const t0 = performance.now();
  const maxNodes = options.maxNodes ?? 10_000_000;
  const first = branchAndBound(input, { ...options, cuts: false, maxNodes: Math.min(maxNodes, RESTART_NODES) });
  if (first.nodes < RESTART_NODES || maxNodes <= RESTART_NODES || (first.status !== 'feasible' && first.status !== 'limit')) return first;
  const left = options.timeLimit ? options.timeLimit - (performance.now() - t0) / 1000 : undefined;
  if (left !== undefined && left <= 0.05) return first;
  const start = first.status === 'feasible' ? { x: first.x, objective: first.objective } : undefined;
  const second = branchAndBound(input, { ...options, cuts: true, maxNodes: maxNodes - first.nodes, timeLimit: left, start });
  second.nodes += first.nodes;
  second.iterations += first.iterations;
  if (second.status === 'limit' && first.status === 'feasible') return { ...first, nodes: second.nodes, iterations: second.iterations };
  return second;
}

function branchAndBound(input: LinearProgram, options: MIPOptions): MIPResult {
  let lp = input;
  const n = lp.numVars;
  const ints: number[] = [];
  for (let j = 0; j < n; j++) if (lp.integer[j]) ints.push(j);

  const rootLower = Float64Array.from(lp.lower);
  const rootUpper = Float64Array.from(lp.upper);
  for (const j of ints) {
    rootLower[j] = Math.ceil(rootLower[j] - INT_TOL);
    rootUpper[j] = Math.floor(rootUpper[j] + INT_TOL);
  }

  const deadline = options.timeLimit ? performance.now() + options.timeLimit * 1000 : Infinity;
  if (ints.length === 0) {
    const r = solveLP(lp, rootLower, rootUpper, { deadline });
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
  const maxNodes = options.maxNodes ?? 10_000_000;
  const relGap = options.relativeGap ?? 1e-9;
  let prop = new BoundPropagator(lp);

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

  const objectiveOf = (x: Float64Array): number => {
    let v = lp.objConstant;
    for (let j = 0; j < n; j++) v += lp.objective[j] * x[j];
    return v;
  };

  /** Rounds the integer columns of an LP solution; keeps it when feasible and better. */
  const tryRounding = (xs: Float64Array) => {
    const x = Float64Array.from(xs.subarray(0, n));
    for (const j of ints) x[j] = Math.round(x[j]) + 0;
    for (let j = 0; j < n; j++) if (x[j] < lp.lower[j] - 1e-9 || x[j] > lp.upper[j] + 1e-9) return;
    for (const row of lp.rows) {
      let a = 0;
      for (let k = 0; k < row.index.length; k++) a += row.value[k] * x[row.index[k]];
      if (a < row.lower - 1e-7 * Math.max(1, Math.abs(row.lower)) || a > row.upper + 1e-7 * Math.max(1, Math.abs(row.upper))) return;
    }
    const v = objectiveOf(x);
    if (v < incumbent - 1e-9) {
      incumbent = v;
      bestX = x;
    }
  };

  if (!prop.run(rootLower, rootUpper, 50)) {
    return finish(input, 'infeasible', Infinity, -Infinity, null, iterations, 0, deadline);
  }
  if (options.cuts) lp = withRootCuts(lp, rootLower, rootUpper, deadline);
  if (lp !== input) prop = new BoundPropagator(lp);
  if (options.start) {
    incumbent = options.start.objective;
    bestX = Float64Array.from(options.start.x);
  }

  let S = createSimplex(lp, rootLower, rootUpper);
  S.deadline = deadline;
  let stateId = -1;
  let nextState = 0;
  let solvesSinceRefresh = 0;

  /** Solves the node's LP; returns the status (S then holds the node's optimum). */
  const solveNode = (node: Node): SimplexStatus => {
    let status: SimplexStatus | null = null;
    if (stateId >= 0 && (node.parent === stateId || (node.snap && S.restore(node.snap)))) {
      for (let j = 0; j < n; j++) {
        if (S.lb[j] !== lower[j] || S.ub[j] !== upper[j]) S.setBounds(j, lower[j], upper[j]);
      }
      status = S.dual();
      if (++solvesSinceRefresh > 200 && status === 'optimal') {
        // Rebuild the tableau from the original rows now and then (numerical drift).
        solvesSinceRefresh = 0;
        if (!S.restore(S.snapshot())) status = null;
      }
    }
    if (status === null || (status === 'iteration_limit' && !S.timedOut) || (status === 'optimal' && S.unstable)) {
      iterations += S.iterations;
      S = status === 'optimal' && S.unstable ? new SparseSimplex(lp, lower, upper) : createSimplex(lp, lower, upper);
      S.deadline = deadline;
      status = S.solve();
      if (status === 'optimal' && S.unstable) {
        S = new SparseSimplex(lp, lower, upper);
        S.deadline = deadline;
        status = S.solve();
      }
    }
    stateId = nextState++;
    return status;
  };

  const open = new NodeQueue(depthFirst);
  let current: Node | null = { up: null, changes: [], bound: -Infinity, seq: seq++, parent: -1, snap: null };
  const lower = new Float64Array(n);
  const upper = new Float64Array(n);
  /** The node's bounds before propagation (children store their differences to these). */
  const baseLower = new Float64Array(n);
  const baseUpper = new Float64Array(n);
  const chain: Node[] = [];
  /** The node's bounds into lower / upper. */
  const boundsOf = (node: Node) => {
    lower.set(rootLower);
    upper.set(rootUpper);
    chain.length = 0;
    for (let x: Node | null = node; x; x = x.up) chain.push(x);
    for (let k = chain.length - 1; k >= 0; k--) {
      const c = chain[k].changes;
      for (let i = 0; i < c.length; i += 3) {
        lower[c[i]] = c[i + 1];
        upper[c[i]] = c[i + 2];
      }
    }
  };

  while (current || open.size > 0) {
    if (nodes >= maxNodes || performance.now() > deadline || ((nodes & 63) === 63 && memoryExceeded())) {
      hitLimit = true;
      if (current) open.push(current);
      break;
    }
    const node: Node = current ?? open.pop();
    current = null;
    if (node.bound >= cutoff()) continue;
    boundsOf(node);
    baseLower.set(lower);
    baseUpper.set(upper);
    if (!prop.run(lower, upper, 8)) continue;
    const st = solveNode(node);
    nodes++;
    if (st === 'infeasible') continue;
    if (st === 'unbounded') {
      unbounded = true;
      break;
    }
    if (st !== 'optimal') {
      hitLimit = true;
      continue;
    }
    const obj = S.objective();
    if (obj >= cutoff()) continue;
    tryRounding(S.x);
    if (obj >= cutoff()) continue;

    let branch = -1;
    let bestFrac = 0;
    for (const j of ints) {
      const v = S.x[j];
      const f = v - Math.floor(v);
      const dist = Math.min(f, 1 - f);
      if (dist > INT_TOL && dist > bestFrac + 1e-12) {
        bestFrac = dist;
        branch = j;
      }
    }
    if (branch < 0) {
      const x = Float64Array.from(S.x.subarray(0, n));
      for (const j of ints) x[j] = Math.round(x[j]) + 0;
      const v = objectiveOf(x);
      if (v < incumbent) {
        incumbent = v;
        bestX = x;
      }
      continue;
    }

    // Children: propagated bounds, reduced-cost fixing against the incumbent, the branching bound.
    const common: number[] = [];
    const room = isFinite(incumbent) ? cutoff() - obj : Infinity;
    for (let j = 0; j < n; j++) {
      let lo = lower[j];
      let hi = upper[j];
      if (lp.integer[j] && lo !== hi && isFinite(room)) {
        const dj = S.d[j];
        if (dj > 1e-9 && S.x[j] <= lo + 1e-9) hi = Math.min(hi, lo + Math.floor(room / dj + 1e-9));
        else if (dj < -1e-9 && S.x[j] >= hi - 1e-9) lo = Math.max(lo, hi - Math.floor(room / -dj + 1e-9));
      }
      if (j === branch) continue;
      // Store only what differs from the node's own (rebuilt) bounds.
      if (lo !== baseLower[j] || hi !== baseUpper[j]) common.push(j, lo, hi);
    }
    const v = S.x[branch];
    const snap = open.size < MAX_SNAPSHOTS ? S.snapshot() : null;
    const down: Node = { up: node, changes: [...common, branch, lower[branch], Math.floor(v)], bound: obj, seq: 0, parent: stateId, snap };
    const up: Node = { up: node, changes: [...common, branch, Math.ceil(v), upper[branch]], bound: obj, seq: 0, parent: stateId, snap };
    const upFirst = v - Math.floor(v) >= 0.5;
    const [first, second] = upFirst ? [up, down] : [down, up];
    second.seq = seq++;
    first.seq = seq++;
    open.push(second);
    // Dive into the preferred child: it starts from the current tableau.
    current = first;
  }

  iterations += S.iterations;
  if (unbounded && !bestX) {
    return finish(input, 'unbounded', -Infinity, -Infinity, null, iterations, nodes, deadline);
  }
  if (!bestX) {
    return finish(input, hitLimit ? 'limit' : 'infeasible', Infinity, -Infinity, null, iterations, nodes, deadline);
  }
  const bound = hitLimit ? Math.min(incumbent, open.minBound()) : incumbent;
  return finish(input, hitLimit ? 'feasible' : 'optimal', incumbent, bound, bestX, iterations, nodes, deadline);
}

/** Tightens column bounds from the row activities (in place); false when infeasible. */
export class BoundPropagator {
  private readonly isInt: Uint8Array;
  constructor(private readonly lp: LinearProgram) {
    this.isInt = lp.integer;
  }

  run(lo: Float64Array, hi: Float64Array, maxPasses: number): boolean {
    const { lp, isInt } = this;
    for (let j = 0; j < lp.numVars; j++) if (lo[j] > hi[j] + 1e-9) return false;
    for (let pass = 0; pass < maxPasses; pass++) {
      let changed = false;
      for (const row of lp.rows) {
        const { index, value } = row;
        let minA = 0;
        let maxA = 0;
        let minInf = 0;
        let maxInf = 0;
        for (let k = 0; k < index.length; k++) {
          const a = value[k];
          const j = index[k];
          if (a > 0) {
            if (isFinite(lo[j])) minA += a * lo[j];
            else minInf++;
            if (isFinite(hi[j])) maxA += a * hi[j];
            else maxInf++;
          } else {
            if (isFinite(hi[j])) minA += a * hi[j];
            else minInf++;
            if (isFinite(lo[j])) maxA += a * lo[j];
            else maxInf++;
          }
        }
        const tolU = 1e-7 * Math.max(1, Math.abs(row.upper));
        const tolL = 1e-7 * Math.max(1, Math.abs(row.lower));
        if (minInf === 0 && minA > row.upper + tolU) return false;
        if (maxInf === 0 && maxA < row.lower - tolL) return false;
        if (minInf > 1 && maxInf > 1) continue;
        for (let k = 0; k < index.length; k++) {
          const a = value[k];
          const j = index[k];
          if (a === 0) continue;
          // Contributions of x_j to the minimum and maximum activity.
          const cMin = a > 0 ? (isFinite(lo[j]) ? a * lo[j] : null) : isFinite(hi[j]) ? a * hi[j] : null;
          const cMax = a > 0 ? (isFinite(hi[j]) ? a * hi[j] : null) : isFinite(lo[j]) ? a * lo[j] : null;
          let newLo = lo[j];
          let newHi = hi[j];
          if (isFinite(row.upper)) {
            const rest = cMin === null ? (minInf === 1 ? minA : NaN) : minInf === 0 ? minA - cMin : NaN;
            if (!Number.isNaN(rest)) {
              const b = (row.upper - rest) / a;
              if (a > 0) newHi = Math.min(newHi, b);
              else newLo = Math.max(newLo, b);
            }
          }
          if (isFinite(row.lower)) {
            const rest = cMax === null ? (maxInf === 1 ? maxA : NaN) : maxInf === 0 ? maxA - cMax : NaN;
            if (!Number.isNaN(rest)) {
              const b = (row.lower - rest) / a;
              if (a > 0) newLo = Math.max(newLo, b);
              else newHi = Math.min(newHi, b);
            }
          }
          if (isInt[j]) {
            newLo = Math.ceil(newLo - 1e-6);
            newHi = Math.floor(newHi + 1e-6);
          }
          const width = hi[j] - lo[j];
          const minStep = isInt[j] ? 0.5 : 1e-6 * (isFinite(width) ? Math.max(1, width) : 1);
          if (newLo > lo[j] + minStep) {
            lo[j] = newLo;
            changed = true;
          }
          if (newHi < hi[j] - minStep) {
            hi[j] = newHi;
            changed = true;
          }
          if (lo[j] > hi[j] + 1e-7 * Math.max(1, Math.abs(lo[j]))) return false;
          if (lo[j] > hi[j]) hi[j] = lo[j];
        }
      }
      if (!changed) break;
    }
    return true;
  }
}

function finish(
  lp: LinearProgram,
  status: MIPResult['status'],
  objective: number,
  bound: number,
  x: Float64Array | null,
  iterations: number,
  nodes: number,
  deadline: number,
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
    // A short grace period past the deadline: without it the duals are lost.
    const fixed = solveLP(lp, lower, upper, { deadline: Math.max(deadline, performance.now() + 2000) });
    iterations += fixed.iterations;
    if (fixed.status === 'optimal') {
      duals = fixed.duals;
      reducedCosts = fixed.reducedCosts;
      for (let j = 0; j < n; j++) if (!lp.integer[j]) x[j] = fixed.x[j];
    }
  }
  return { status, objective, bound, x: x ?? new Float64Array(n), duals, reducedCosts, iterations, nodes };
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
