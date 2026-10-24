/**
 * Quadratic constraints and non-convex quadratic objectives: spatial branch
 * and bound over LP relaxations.
 *
 * The input is a LinearProgram whose product columns z stand for
 * quadratic expressions of the other columns (`products`).  Each node solves
 * an LP relaxation:
 *
 * - convex quadratic functions (the objective when its Hessian is PSD, a row
 *   side when its function is convex on that side) are relaxed by tangent
 *   (outer-approximation) cuts, added where the LP solution violates them;
 * - every other product term x_i * x_j gets a column w_ij with McCormick
 *   envelopes over the node's bounds (squares also get tangent cuts), and
 *   the product columns z are linked to the w columns by linear rows.
 *
 * An LP solution that satisfies the true quadratic rows is a feasible point
 * and its true objective an upper bound.  Otherwise the node branches: on a
 * fractional integer column, or on a column of the most violated product
 * (splitting its domain), so that the envelopes tighten.  Nodes are taken
 * best bound first.
 */

import { OplError } from '../errors.js';
import type { LinearProgram, MIPResult, Row } from './lp.js';
import { memoryExceeded } from './memory.js';
import { BoundPropagator } from './mip.js';
import { isConvex, type Hessian } from './qp.js';
import { createSimplex } from './simplex.js';
import { SparseSimplex } from './sparse.js';

/** z = sum(c * x_i * x_j) + sum(c * x_j) + constant (i <= j in terms). */
export interface Product {
  z: number;
  terms: { i: number; j: number; c: number }[];
  linear: { j: number; c: number }[];
  constant: number;
}

export interface GlobalOptions {
  timeLimit?: number;
  /** Relative optimality gap at which a node or the search stops. */
  relativeGap?: number;
  maxNodes?: number;
}

/** A quadratic function of the original columns: x'Hx/2 + a'x + constant (H by triplets, upper triangle). */
interface QuadFunction {
  h: Hessian;
  a: Map<number, number>;
  constant: number;
}

const FEAS = 1e-6;
const BOX = 1e6;
const INT_TOL = 1e-6;

function evalQuad(f: QuadFunction, x: Float64Array): number {
  let v = f.constant;
  for (const [j, c] of f.a) v += c * x[j];
  for (let k = 0; k < f.h.v.length; k++) {
    const [i, j, c] = [f.h.i[k], f.h.j[k], f.h.v[k]];
    v += i === j ? 0.5 * c * x[i] * x[i] : c * x[i] * x[j];
  }
  return v;
}

function gradQuad(f: QuadFunction, x: Float64Array): Map<number, number> {
  const g = new Map(f.a);
  const add = (j: number, v: number) => g.set(j, (g.get(j) ?? 0) + v);
  for (let k = 0; k < f.h.v.length; k++) {
    const [i, j, c] = [f.h.i[k], f.h.j[k], f.h.v[k]];
    if (i === j) add(i, c * x[i]);
    else {
      add(i, c * x[j]);
      add(j, c * x[i]);
    }
  }
  return g;
}

/** Linear part (non-product columns) plus expanded products of a row or of the objective. */
function expand(coef: (j: number) => number, cols: number[], productOf: Map<number, Product>, constant: number): QuadFunction {
  const a = new Map<number, number>();
  const hv = new Map<string, number>();
  let k = constant;
  for (const j of cols) {
    const c = coef(j);
    if (c === 0) continue;
    const p = productOf.get(j);
    if (!p) {
      a.set(j, (a.get(j) ?? 0) + c);
      continue;
    }
    k += c * p.constant;
    for (const l of p.linear) a.set(l.j, (a.get(l.j) ?? 0) + c * l.c);
    for (const t of p.terms) {
      const key = `${t.i},${t.j}`;
      // x'Hx/2: a diagonal entry counts twice.
      hv.set(key, (hv.get(key) ?? 0) + (t.i === t.j ? 2 : 1) * c * t.c);
    }
  }
  const h: Hessian = { i: [], j: [], v: [] };
  for (const [key, v] of hv) {
    if (v === 0) continue;
    const [i, j] = key.split(',').map(Number);
    h.i.push(i);
    h.j.push(j);
    h.v.push(v);
  }
  return { h, a, constant: k };
}

function negate(f: QuadFunction): QuadFunction {
  return {
    h: { i: f.h.i, j: f.h.j, v: f.h.v.map((v) => -v) },
    a: new Map([...f.a].map(([j, c]) => [j, -c])),
    constant: -f.constant,
  };
}

/** A cut  sum(coef x) <= rhs  in the original columns. */
interface Cut {
  index: number[];
  value: number[];
  upper: number;
}

/** Tangent of the convex function f at x: f(x0) + g(x0)(x - x0) <= bound. */
function tangent(f: QuadFunction, x0: Float64Array, bound: number, extra?: { j: number; c: number }): Cut {
  const g = gradQuad(f, x0);
  let rhs = bound - evalQuad(f, x0);
  const index: number[] = [];
  const value: number[] = [];
  for (const [j, c] of g) {
    if (c === 0) continue;
    index.push(j);
    value.push(c);
    rhs += c * x0[j];
  }
  if (extra) {
    index.push(extra.j);
    value.push(extra.c);
  }
  return scaled({ index, value, upper: rhs });
}

/** A cut divided by its largest coefficient (cuts taken far away have huge ones). */
function scaled(c: Cut): Cut {
  let m = 0;
  for (const v of c.value) m = Math.max(m, Math.abs(v));
  if (m === 0 || (m >= 0.5 && m <= 2)) return c;
  return { index: c.index, value: c.value.map((v) => v / m), upper: c.upper / m };
}

interface Node {
  lower: Float64Array;
  upper: Float64Array;
  bound: number;
  depth: number;
}

/** Binary heap on the node bound. */
class Heap {
  private items: Node[] = [];
  get size(): number {
    return this.items.length;
  }
  push(n: Node): void {
    const a = this.items;
    a.push(n);
    let i = a.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (a[p].bound <= a[i].bound) break;
      [a[p], a[i]] = [a[i], a[p]];
      i = p;
    }
  }
  pop(): Node {
    const a = this.items;
    const top = a[0];
    const last = a.pop()!;
    if (a.length) {
      a[0] = last;
      let i = 0;
      for (;;) {
        const l = 2 * i + 1;
        const r = l + 1;
        let m = i;
        if (l < a.length && a[l].bound < a[m].bound) m = l;
        if (r < a.length && a[r].bound < a[m].bound) m = r;
        if (m === i) break;
        [a[m], a[i]] = [a[i], a[m]];
        i = m;
      }
    }
    return top;
  }
  minBound(): number {
    return this.items.length ? Math.min(...this.items.map((n) => n.bound)) : Infinity;
  }
}

/**
 * Checks that the problem can be relaxed: the columns of non-convex products
 * need finite bounds (after propagation).  Returns null when it can, else a
 * reason.
 */
export function quadraticSupport(lp: LinearProgram, products: Product[]): string | null {
  try {
    new GlobalSolver(lp, products, {});
    return null;
  } catch (e) {
    if (e instanceof OplError) return e.message;
    throw e;
  }
}

export function solveQuadratic(lp: LinearProgram, products: Product[], options: GlobalOptions = {}): MIPResult {
  return new GlobalSolver(lp, products, options).run();
}

class GlobalSolver {
  private readonly n: number;
  private readonly productOf = new Map<number, Product>();
  /** The true objective (minimised) and constraints, in the original columns. */
  private readonly objective: QuadFunction;
  private readonly convexObjective: boolean;
  /** Quadratic rows relaxed by cuts only: f(x) <= upper (both sides as needed). */
  private readonly convexRows: { f: QuadFunction; upper: number }[] = [];
  /** Rows kept in the LP (linear rows, and quadratic rows through the product columns). */
  private readonly keptRows: Row[] = [];
  /** Product columns linked to w columns, and the w columns of each term. */
  private readonly linked: Product[] = [];
  private readonly pairs: { i: number; j: number; w: number }[] = [];
  private readonly pairIndex = new Map<string, number>();
  /** The true quadratic rows, to check candidate points. */
  private readonly quadRows: { f: QuadFunction; lower: number; upper: number }[] = [];
  private readonly epigraph: number;
  private readonly numCols: number;
  private readonly cuts: Cut[] = [];
  private readonly rootLower: Float64Array;
  private readonly rootUpper: Float64Array;
  private readonly deadline: number;
  private readonly gap: number;

  constructor(
    private readonly lp: LinearProgram,
    products: Product[],
    private readonly options: GlobalOptions,
  ) {
    const n = (this.n = lp.numVars);
    for (const p of products) this.productOf.set(p.z, p);
    this.deadline = options.timeLimit ? performance.now() + options.timeLimit * 1000 : Infinity;
    this.gap = options.relativeGap ?? 1e-6;

    const allCols = [...Array(n).keys()];
    this.objective = expand((j) => lp.objective[j], allCols, this.productOf, lp.objConstant);
    this.convexObjective = isConvex(this.objective.h);

    // Rows: linear ones stay; quadratic ones are convex (cuts) or go through w columns.
    const linkedZ = new Set<number>();
    for (const row of lp.rows) {
      const zs = row.index.filter((j, k) => row.value[k] !== 0 && this.productOf.has(j));
      if (zs.length === 0) {
        this.keptRows.push(row);
        continue;
      }
      const coef = new Map<number, number>();
      row.index.forEach((j, k) => coef.set(j, (coef.get(j) ?? 0) + row.value[k]));
      const f = expand((j) => coef.get(j) ?? 0, [...coef.keys()], this.productOf, 0);
      this.quadRows.push({ f, lower: row.lower, upper: row.upper });
      const upOk = !isFinite(row.upper) || isConvex(f.h);
      const lowOk = !isFinite(row.lower) || isConvex(negate(f).h);
      if (upOk && lowOk) {
        if (isFinite(row.upper)) this.convexRows.push({ f, upper: row.upper });
        if (isFinite(row.lower)) this.convexRows.push({ f: negate(f), upper: -row.lower });
      } else {
        this.keptRows.push(row);
        for (const z of zs) linkedZ.add(z);
      }
    }
    if (!this.convexObjective) for (const p of products) if (lp.objective[p.z] !== 0) linkedZ.add(p.z);

    // Columns: originals, then w per product term, then the epigraph column.
    let col = n;
    for (const z of linkedZ) {
      const p = this.productOf.get(z)!;
      this.linked.push(p);
      for (const t of p.terms) {
        const key = `${t.i},${t.j}`;
        if (!this.pairIndex.has(key)) {
          this.pairIndex.set(key, this.pairs.length);
          this.pairs.push({ i: t.i, j: t.j, w: col++ });
        }
      }
    }
    this.epigraph = this.convexObjective ? col++ : -1;
    this.numCols = col;

    this.rootLower = new Float64Array(col);
    this.rootUpper = new Float64Array(col);
    this.rootLower.set(lp.lower);
    this.rootUpper.set(lp.upper);
    for (let j = 0; j < n; j++) {
      if (lp.integer[j]) {
        this.rootLower[j] = Math.ceil(this.rootLower[j] - INT_TOL);
        this.rootUpper[j] = Math.floor(this.rootUpper[j] + INT_TOL);
      }
    }
    // Linked product columns are free (their links define them); the others
    // appear only in cut-relaxed functions and are pinned at 0.
    for (const p of products) {
      const free = linkedZ.has(p.z);
      this.rootLower[p.z] = free ? -Infinity : 0;
      this.rootUpper[p.z] = free ? Infinity : 0;
    }
    // Added columns (w, epigraph) are free until their bounds are known.
    for (let j = n; j < col; j++) {
      this.rootLower[j] = -Infinity;
      this.rootUpper[j] = Infinity;
    }
    const prop = new BoundPropagator(this.baseLP(this.rootLower, this.rootUpper));
    prop.run(this.rootLower, this.rootUpper, 20);
    for (const p of this.pairs) {
      for (const j of [p.i, p.j]) {
        if (!isFinite(this.rootLower[j]) || !isFinite(this.rootUpper[j])) {
          throw new OplError('a non-convex quadratic term needs finite bounds on its variables');
        }
      }
    }
    this.setPairBounds(this.rootLower, this.rootUpper);
  }

  /** Bounds of the w columns from those of their factors. */
  private setPairBounds(lo: Float64Array, hi: Float64Array): void {
    for (const p of this.pairs) {
      const [a, b, c, d] = [lo[p.i], hi[p.i], lo[p.j], hi[p.j]];
      if (p.i === p.j) {
        lo[p.w] = a <= 0 && b >= 0 ? 0 : Math.min(a * a, b * b);
        hi[p.w] = Math.max(a * a, b * b);
      } else {
        const ps = [a * c, a * d, b * c, b * d];
        lo[p.w] = Math.min(...ps);
        hi[p.w] = Math.max(...ps);
      }
    }
  }

  /** Kept rows, links z = sum c w + linear, and the cut pool. */
  private baseLP(lo: Float64Array, hi: Float64Array): LinearProgram {
    const rows: Row[] = [...this.keptRows];
    for (const p of this.linked) {
      const index = [p.z];
      const value = [1];
      for (const t of p.terms) {
        if (t.c === 0) continue;
        index.push(this.pairs[this.pairIndex.get(`${t.i},${t.j}`)!].w);
        value.push(-t.c);
      }
      for (const l of p.linear) {
        if (l.c === 0) continue;
        index.push(l.j);
        value.push(-l.c);
      }
      rows.push({ index, value, lower: p.constant, upper: p.constant });
    }
    for (const c of this.cuts) rows.push({ index: c.index, value: c.value, lower: -Infinity, upper: c.upper });
    const objective = new Float64Array(this.numCols);
    if (this.convexObjective) {
      for (const [j, c] of this.objective.a) objective[j] = c;
      objective[this.epigraph] = 1;
    } else {
      objective.set(this.lp.objective);
    }
    const integer = new Uint8Array(this.numCols);
    integer.set(this.lp.integer);
    return {
      numVars: this.numCols,
      objective,
      objConstant: this.convexObjective ? this.objective.constant : this.lp.objConstant,
      lower: lo,
      upper: hi,
      integer,
      rows,
    };
  }

  /** McCormick envelopes (and square secants) for the node's bounds. */
  private envelopes(lo: Float64Array, hi: Float64Array): Row[] {
    const rows: Row[] = [];
    for (const p of this.pairs) {
      const [a, b] = [lo[p.i], hi[p.i]];
      if (p.i === p.j) {
        // w <= (a + b) x - a b  (secant); w >= x^2 by tangents at the bounds.
        rows.push({ index: [p.w, p.i], value: [1, -(a + b)], lower: -Infinity, upper: -a * b });
        for (const t of [a, b, (a + b) / 2]) rows.push({ index: [p.w, p.i], value: [1, -2 * t], lower: -t * t, upper: Infinity });
        continue;
      }
      const [c, d] = [lo[p.j], hi[p.j]];
      // w >= a y + c x - a c,  w >= b y + d x - b d,  w <= b y + c x - b c,  w <= a y + d x - a d
      rows.push({ index: [p.w, p.i, p.j], value: [1, -c, -a], lower: -a * c, upper: Infinity });
      rows.push({ index: [p.w, p.i, p.j], value: [1, -d, -b], lower: -b * d, upper: Infinity });
      rows.push({ index: [p.w, p.i, p.j], value: [1, -c, -b], lower: -Infinity, upper: -b * c });
      rows.push({ index: [p.w, p.i, p.j], value: [1, -d, -a], lower: -Infinity, upper: -a * d });
    }
    return rows;
  }

  /** The true objective and the worst row violation at x (original columns). */
  private check(x: Float64Array): { objective: number; violation: number } {
    let violation = 0;
    for (const r of this.quadRows) {
      const v = evalQuad(r.f, x);
      const tol = (b: number) => FEAS * Math.max(1, Math.abs(b));
      if (v > r.upper + tol(r.upper)) violation = Math.max(violation, (v - r.upper) / Math.max(1, Math.abs(r.upper)));
      if (v < r.lower - tol(r.lower)) violation = Math.max(violation, (r.lower - v) / Math.max(1, Math.abs(r.lower)));
    }
    return { objective: evalQuad(this.objective, x), violation };
  }

  /** Solves the node relaxation with cut rounds; null when infeasible. */
  private relax(lo: Float64Array, hi: Float64Array): { x: Float64Array; bound: number; status: string } | null {
    let last: { x: Float64Array; bound: number; status: string } | null = null;
    for (let round = 0; round < 200; round++) {
      // Free columns get a large box so that cut rounds can start.
      const l = Float64Array.from(lo, (v) => (isFinite(v) ? v : -BOX));
      const u = Float64Array.from(hi, (v) => (isFinite(v) ? v : BOX));
      const base = this.baseLP(l, u);
      base.rows = [...base.rows, ...this.envelopes(lo, hi)];
      let s = createSimplex(base, l, u);
      s.deadline = this.deadline;
      let st = s.solve();
      if (st === 'optimal' && s.unstable) {
        s = new SparseSimplex(base, l, u);
        s.deadline = this.deadline;
        st = s.solve();
      }
      if (st === 'infeasible') return null;
      if (st !== 'optimal') return { x: Float64Array.from(s.x.subarray(0, this.numCols)), bound: -Infinity, status: st };
      const x = Float64Array.from(s.x.subarray(0, this.numCols));
      const bound = s.objective();
      last = { x, bound, status: 'optimal' };
      let added = 0;
      for (const r of this.convexRows) {
        const v = evalQuad(r.f, x);
        if (v > r.upper + FEAS * Math.max(1, Math.abs(r.upper))) {
          this.cuts.push(tangent(r.f, x, r.upper));
          added++;
        }
      }
      if (this.convexObjective) {
        const v = evalQuad({ ...this.objective, a: new Map(), constant: 0 }, x);
        if (v > x[this.epigraph] + FEAS * Math.max(1, Math.abs(v))) {
          // t >= q(x0) + g(x0)(x - x0)  <=>  g x - t <= g x0 - q(x0)
          const q = { h: this.objective.h, a: new Map<number, number>(), constant: 0 };
          this.cuts.push(tangent(q, x, 0, { j: this.epigraph, c: -1 }));
          added++;
        }
      }
      for (const p of this.pairs) {
        if (p.i === p.j && x[p.w] < x[p.i] * x[p.i] - FEAS * Math.max(1, x[p.i] * x[p.i])) {
          this.cuts.push(scaled({ index: [p.i, p.w], value: [2 * x[p.i], -1], upper: x[p.i] * x[p.i] }));
          added++;
        }
      }
      if (!added || performance.now() > this.deadline) return last;
    }
    // Out of cut rounds: the last relaxation still bounds the node.
    return last;
  }

  run(): MIPResult {
    const n = this.n;
    const lp = this.lp;
    let incumbent = Infinity;
    let best: Float64Array | null = null;
    let nodes = 0;
    let hitLimit = false;
    let unbounded = false;
    const maxNodes = this.options.maxNodes ?? 1_000_000;
    const open = new Heap();
    open.push({ lower: this.rootLower, upper: this.rootUpper, bound: -Infinity, depth: 0 });
    // Relative gap, and an absolute one of 1e-6 (CPLEX's defaults are 1e-4 and 1e-6).
    const prune = (b: number) => b >= incumbent - Math.max(1e-6, this.gap * Math.abs(incumbent));
    while (open.size) {
      if (nodes >= maxNodes || performance.now() > this.deadline || ((nodes & 31) === 31 && memoryExceeded())) {
        hitLimit = true;
        break;
      }
      const node = open.pop();
      if (prune(node.bound)) continue;
      const lo = Float64Array.from(node.lower);
      const hi = Float64Array.from(node.upper);
      this.setPairBounds(lo, hi);
      if (!new BoundPropagator(this.baseLP(lo, hi)).run(lo, hi, 4)) continue;
      this.setPairBounds(lo, hi);
      const r = this.relax(lo, hi);
      nodes++;
      if (!r) continue;
      if (r.status !== 'optimal') {
        hitLimit = true;
        continue;
      }
      if (prune(r.bound)) continue;
      const x = r.x;
      // Columns at the artificial box mean an unbounded direction.
      let atBox = false;
      for (let j = 0; j < n; j++) {
        if (this.productOf.has(j) || (isFinite(lp.lower[j]) && isFinite(lp.upper[j]))) continue;
        if (Math.abs(x[j]) >= BOX * 0.999) atBox = true;
      }
      const xo = x.subarray(0, n);
      const { objective, violation } = this.check(xo);
      let frac = -1;
      let worstFrac = 0;
      for (let j = 0; j < n; j++) {
        if (!lp.integer[j]) continue;
        const f = Math.abs(x[j] - Math.round(x[j]));
        if (f > INT_TOL && f > worstFrac) {
          worstFrac = f;
          frac = j;
        }
      }
      if (frac < 0 && violation === 0) {
        if (atBox) {
          unbounded = true;
          break;
        }
        if (objective < incumbent) {
          incumbent = objective;
          best = Float64Array.from(xo);
          for (let j = 0; j < n; j++) if (lp.integer[j]) best[j] = Math.round(best[j]) + 0;
        }
        if (prune(r.bound)) continue;
      }
      // Branch: a fractional integer, else the column of the worst product gap.
      let col = frac;
      let at = frac >= 0 ? x[frac] : 0;
      if (col < 0) {
        let worst = 0;
        for (const p of this.pairs) {
          const gap = Math.abs(x[p.w] - x[p.i] * x[p.j]);
          if (gap <= worst) continue;
          const wi = hi[p.i] - lo[p.i];
          const wj = hi[p.j] - lo[p.j];
          const j = wi >= wj ? p.i : p.j;
          if (hi[j] - lo[j] <= 1e-9 * Math.max(1, Math.abs(lo[j]))) continue;
          worst = gap;
          col = j;
        }
        if (col < 0) {
          // Only convex rows are violated (cut rounds ran out): split the widest column of the worst row.
          let w = 0;
          for (let j = 0; j < n; j++) {
            if (isFinite(hi[j] - lo[j]) && hi[j] - lo[j] > w && this.involved(j)) {
              w = hi[j] - lo[j];
              col = j;
            }
          }
          if (col < 0 || w <= 1e-9) continue;
        }
        const width = hi[col] - lo[col];
        at = x[col] > lo[col] + 0.05 * width && x[col] < hi[col] - 0.05 * width ? x[col] : (lo[col] + hi[col]) / 2;
      }
      const left = { lower: Float64Array.from(lo), upper: Float64Array.from(hi), bound: r.bound, depth: node.depth + 1 };
      const right = { lower: Float64Array.from(lo), upper: Float64Array.from(hi), bound: r.bound, depth: node.depth + 1 };
      if (lp.integer[col]) {
        left.upper[col] = Math.floor(at);
        right.lower[col] = Math.ceil(at);
      } else {
        left.upper[col] = at;
        right.lower[col] = at;
      }
      open.push(left);
      open.push(right);
    }
    const zeros = new Float64Array(n);
    const rows = new Float64Array(lp.rows.length);
    if (unbounded && !best) return { status: 'unbounded', objective: -Infinity, bound: -Infinity, x: zeros, duals: rows, reducedCosts: zeros, iterations: 0, nodes };
    if (!best) return { status: hitLimit ? 'limit' : 'infeasible', objective: Infinity, bound: -Infinity, x: zeros, duals: rows, reducedCosts: zeros, iterations: 0, nodes };
    for (const p of this.productOf.values()) {
      let v = p.constant;
      for (const l of p.linear) v += l.c * best[l.j];
      for (const t of p.terms) v += t.c * best[t.i] * best[t.j];
      best[p.z] = v;
    }
    const bound = hitLimit ? Math.min(incumbent, open.minBound()) : incumbent;
    return { status: hitLimit ? 'feasible' : 'optimal', objective: incumbent, bound, x: best, duals: rows, reducedCosts: zeros, iterations: 0, nodes };
  }

  private involvedCols: Set<number> | null = null;

  /** Whether column j appears in a quadratic function. */
  private involved(j: number): boolean {
    if (!this.involvedCols) {
      this.involvedCols = new Set();
      for (const r of [...this.quadRows.map((q) => q.f), this.objective]) {
        for (const i of r.h.i) this.involvedCols.add(i);
        for (const i of r.h.j) this.involvedCols.add(i);
      }
    }
    return this.involvedCols.has(j);
  }
}
