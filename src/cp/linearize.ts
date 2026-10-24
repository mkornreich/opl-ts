/**
 * Linearization of flattened constraints for the MIP solver, as CPLEX does
 * for OPL's logical constraints and non-linear functions:
 *
 * - abs / min / max in a convex position become plain LP rows, otherwise a
 *   big-M formulation with binaries;
 * - products with a binary factor, element constraints and set domains use
 *   binaries;
 * - meta-constraints and logical constraints (=>, or, not, !=) become
 *   indicator-style big-M rows.
 *
 * - other products of two variables (in the objective or in rows) are left
 *   to the quadratic solvers (listed in input.quadratic).
 *
 * Returns null when something needs constraint programming (alldifferent,
 * scheduling, general products, unbounded big-M terms, ...).
 */

import { DVar, LinExpr, type Linear } from '../linear.js';
import type { CmpOp, CPCons, CPDef } from './terms.js';

export interface LinRow {
  expr: LinExpr;
  lower: number;
  upper: number;
  ref: null;
}

export interface LinearizeInput {
  vars: DVar[];
  rows: { expr: LinExpr; lower: number; upper: number }[];
  defs: CPDef[];
  cons: CPCons[];
  objective: LinExpr;
  sense: 'minimize' | 'maximize' | null;
  newVar(lo: number, hi: number, isInt: boolean, name: string): DVar;
  /** When given, receives the products z = x * y left for a quadratic objective. */
  quadratic?: QuadTerm[];
}

/** z = a * b, the factors expanded through the linear definitions of auxiliary variables. */
export interface QuadTerm {
  z: DVar;
  a: LinExpr;
  b: LinExpr;
}

/** Tolerance used for strict inequalities over continuous expressions. */
const EPS = 1e-6;
/** Larger domains are not expanded into one binary per value. */
const MAX_VALUES = 2000;

class Unsupported extends Error {}

export function linearize(inp: LinearizeInput): LinRow[] | null {
  try {
    return new Linearizer(inp).run();
  } catch (e) {
    if (e instanceof Unsupported) return null;
    throw e;
  }
}

class Linearizer {
  private readonly out: LinRow[] = [];
  constructor(private readonly inp: LinearizeInput) {}

  private no(): never {
    throw new Unsupported();
  }

  private v(id: number): DVar {
    return this.inp.vars[id];
  }

  private lin(e: Linear): LinExpr {
    return LinExpr.of(e).clone();
  }

  private bounds(e: Linear): [number, number] {
    const le = LinExpr.of(e);
    let lo = le.constant;
    let hi = le.constant;
    for (const [id, c] of le.terms) {
      if (c === 0) continue;
      const x = this.v(id);
      lo += c > 0 ? c * x.lb : c * x.ub;
      hi += c > 0 ? c * x.ub : c * x.lb;
    }
    return [lo, hi];
  }

  private finiteBounds(e: Linear): [number, number] {
    const [lo, hi] = this.bounds(e);
    if (!isFinite(lo) || !isFinite(hi) || Math.max(Math.abs(lo), Math.abs(hi)) > 1e9) this.no();
    return [lo, hi];
  }

  private integral(e: Linear): boolean {
    const le = LinExpr.of(e);
    if (!Number.isInteger(le.constant)) return false;
    for (const [id, c] of le.terms) if (c !== 0 && (!Number.isInteger(c) || !this.v(id).isInt)) return false;
    return true;
  }

  /** lower <= e <= upper */
  private row(e: LinExpr, lower: number, upper: number): void {
    const expr = e.clone();
    const k = expr.constant;
    expr.constant = 0;
    this.out.push({ expr, lower: lower - k, upper: upper - k, ref: null });
  }

  private bin(name: string): DVar {
    return this.inp.newVar(0, 1, true, name);
  }

  /** How often each variable appears in non-linear definitions and constraints (rows and linear definitions excluded). */
  private uses: Map<number, number> | null = null;

  /** Whether z is used by something other than rows, linear definitions and the objective. */
  private usedNonLinearly(z: DVar): boolean {
    if (!this.uses) {
      const uses = new Map<number, number>();
      const count = (v: unknown, skip: DVar | null): void => {
        if (v instanceof DVar) {
          if (v !== skip) uses.set(v.id, (uses.get(v.id) ?? 0) + 1);
        } else if (v instanceof LinExpr) {
          for (const [id, c] of v.terms) if (c !== 0 && id !== skip?.id) uses.set(id, (uses.get(id) ?? 0) + 1);
        } else if (Array.isArray(v)) {
          for (const x of v) count(x, skip);
        } else if (v && typeof v === 'object') {
          for (const x of Object.values(v)) count(x, skip);
        }
      };
      for (const d of this.inp.defs) if (d.k !== 'linear') count(d, 'z' in d ? d.z : null);
      for (const c of this.inp.cons) count(c, null);
      this.uses = uses;
    }
    return (this.uses.get(z.id) ?? 0) > 0;
  }

  private linearDefs: Map<number, LinExpr> | null = null;

  /** x in terms of decision variables: auxiliary variables of linear definitions are replaced. */
  private expand(x: DVar): LinExpr {
    if (!this.linearDefs) {
      this.linearDefs = new Map();
      for (const d of this.inp.defs) if (d.k === 'linear') this.linearDefs.set(d.z.id, LinExpr.of(d.e));
    }
    const out = new LinExpr();
    const add = (e: LinExpr, f: number, depth: number) => {
      out.constant += f * e.constant;
      for (const [id, c] of e.terms) {
        const def = depth < 8 ? this.linearDefs!.get(id) : undefined;
        if (def) add(def, f * c, depth + 1);
        else out.addScaled(this.v(id), f * c);
      }
    };
    add(LinExpr.of(x), 1, 0);
    return out;
  }

  run(): LinRow[] {
    for (const v of [...this.inp.vars]) if (v.domain) this.setDomain(v);
    for (const d of this.inp.defs) this.def(d);
    for (const c of this.inp.cons) this.post(c, true);
    return this.out;
  }

  // ------------------------------------------------------------ definitions

  private def(d: CPDef): void {
    switch (d.k) {
      case 'linear':
        this.row(this.lin(d.z).addScaled(d.e, -1), 0, 0);
        return;
      case 'post':
        this.post(d.cons, true);
        return;
      case 'reify':
        this.reify(d.cons, d.b);
        return;
      case 'abs':
        this.abs(d.z, d.x);
        return;
      case 'minmax':
        this.minmax(d.z, d.xs, d.isMin);
        return;
      case 'mul':
        this.mul(d.z, d.x, d.y);
        return;
      case 'element':
        this.element(d);
        return;
    }
    this.no();
  }

  /** How z is used outside its definition: 'down' when only an upper bound on z matters. */
  private usage(z: DVar): 'down' | 'up' | 'both' {
    let down = false;
    let up = false;
    const sense = this.inp.sense;
    const c = this.inp.objective.terms.get(z.id) ?? 0;
    if (c !== 0) {
      if ((sense === 'minimize') === c > 0) down = true;
      else up = true;
    }
    for (const r of [...this.inp.rows, ...this.out]) {
      const a = r.expr.terms.get(z.id) ?? 0;
      if (a === 0) continue;
      if (isFinite(r.upper) && !isFinite(r.lower)) a > 0 ? (down = true) : (up = true);
      else if (isFinite(r.lower) && !isFinite(r.upper)) a > 0 ? (up = true) : (down = true);
      else down = up = true;
    }
    for (const d of this.inp.defs) {
      if (refersTo(d, z.id)) down = up = true;
    }
    for (const c2 of this.inp.cons) if (consRefers(c2, z.id)) down = up = true;
    return down && up ? 'both' : up ? 'up' : 'down';
  }

  private abs(z: DVar, x: DVar): void {
    if (this.usage(z) === 'down') {
      // z >= x, z >= -x
      this.row(this.lin(z).addScaled(x, -1), 0, Infinity);
      this.row(this.lin(z).addScaled(x, 1), 0, Infinity);
      return;
    }
    const [lo, hi] = this.finiteBounds(x);
    if (lo >= 0) return this.row(this.lin(z).addScaled(x, -1), 0, 0);
    if (hi <= 0) return this.row(this.lin(z).addScaled(x, 1), 0, 0);
    // x = p - n, z = p + n, p <= hi * b, n <= -lo * (1 - b)
    const p = this.inp.newVar(0, hi, false, 'absPos');
    const n = this.inp.newVar(0, -lo, false, 'absNeg');
    const b = this.bin('absSign');
    this.row(this.lin(x).addScaled(p, -1).addScaled(n, 1), 0, 0);
    this.row(this.lin(z).addScaled(p, -1).addScaled(n, -1), 0, 0);
    this.row(this.lin(p).addScaled(b, -hi), -Infinity, 0);
    this.row(this.lin(n).addScaled(b, -lo), -Infinity, -lo);
  }

  private minmax(z: DVar, xs: DVar[], isMin: boolean): void {
    const use = this.usage(z);
    // max: z >= x_i; min: z <= x_i
    for (const x of xs) this.row(this.lin(z).addScaled(x, -1), isMin ? -Infinity : 0, isMin ? 0 : Infinity);
    if ((!isMin && use === 'down') || (isMin && use === 'up')) return;
    // One x_i is selected and equals z.
    const bs = xs.map(() => this.bin(isMin ? 'argmin' : 'argmax'));
    const sum = new LinExpr();
    for (const b of bs) sum.addScaled(b, 1);
    this.row(sum, 1, 1);
    const bnds = xs.map((x) => this.finiteBounds(x));
    const top = Math.max(...bnds.map((b) => b[1]));
    const bottom = Math.min(...bnds.map((b) => b[0]));
    xs.forEach((x, i) => {
      if (isMin) {
        // z >= x_i - (hi_i - bottom) (1 - b_i)
        const m = bnds[i][1] - bottom;
        this.row(this.lin(z).addScaled(x, -1).addScaled(bs[i], -m), -m, Infinity);
      } else {
        // z <= x_i + (top - lo_i) (1 - b_i)
        const m = top - bnds[i][0];
        this.row(this.lin(z).addScaled(x, -1).addScaled(bs[i], m), -Infinity, m);
      }
    });
  }

  private isBinary(v: DVar): boolean {
    return v.isInt && v.lb >= 0 && v.ub <= 1;
  }

  private mul(z: DVar, x: DVar, y: DVar): void {
    if (this.isBinary(x) && this.isBinary(y)) {
      this.row(this.lin(z).addScaled(x, -1), -Infinity, 0);
      this.row(this.lin(z).addScaled(y, -1), -Infinity, 0);
      this.row(this.lin(z).addScaled(x, -1).addScaled(y, -1), -1, Infinity);
      return;
    }
    if (!this.isBinary(x) && !this.isBinary(y) && this.inp.quadratic && !this.usedNonLinearly(z)) {
      this.inp.quadratic.push({ z, a: this.expand(x), b: this.expand(y) });
      return;
    }
    const [b, v] = this.isBinary(y) ? [y, x] : this.isBinary(x) ? [x, y] : this.no();
    const [lo, hi] = this.finiteBounds(v);
    // z = v * b
    this.row(this.lin(z).addScaled(b, -hi), -Infinity, 0);
    this.row(this.lin(z).addScaled(b, -lo), 0, Infinity);
    this.row(this.lin(z).addScaled(v, -1).addScaled(b, -lo), -Infinity, -lo);
    this.row(this.lin(z).addScaled(v, -1).addScaled(b, -hi), -hi, Infinity);
  }

  private element(d: Extract<CPDef, { k: 'element' }>): void {
    const [lo, hi] = this.finiteBounds(d.idx);
    const cand = d.keys.map((k, i) => ({ k, i })).filter(({ k }) => k >= lo && k <= hi);
    if (cand.length === 0 || cand.length > MAX_VALUES) this.no();
    const ws = cand.map(() => this.bin('select'));
    const one = new LinExpr();
    const idx = this.lin(d.idx);
    ws.forEach((w, j) => {
      one.addScaled(w, 1);
      idx.addScaled(w, -cand[j].k);
    });
    this.row(one, 1, 1);
    this.row(idx, 0, 0);
    if (d.items.every((it) => typeof it === 'number')) {
      const z = this.lin(d.z);
      ws.forEach((w, j) => z.addScaled(w, -(d.items[cand[j].i] as number)));
      this.row(z, 0, 0);
      return;
    }
    // z = items[k] when w_k = 1
    const [zl, zh] = this.finiteBounds(d.z);
    ws.forEach((w, j) => {
      const item = d.items[cand[j].i];
      const [il, ih] = this.finiteBounds(item);
      const mUp = zh - il;
      const mDown = ih - zl;
      this.row(this.lin(d.z).addScaled(item, -1).addScaled(w, mUp), -Infinity, mUp);
      this.row(this.lin(d.z).addScaled(item, -1).addScaled(w, -mDown), -mDown, Infinity);
    });
  }

  /** x in S for a variable declared with a set domain. */
  private setDomain(x: DVar): void {
    const values = [...new Set(x.domain!)].sort((a, b) => a - b);
    if (values.length === 0) this.no();
    if (values[values.length - 1] - values[0] + 1 === values.length) return;
    if (values.length > MAX_VALUES) this.no();
    const one = new LinExpr();
    const sum = this.lin(x);
    for (const v of values) {
      const w = this.bin('value');
      one.addScaled(w, 1);
      sum.addScaled(w, -v);
    }
    this.row(one, 1, 1);
    this.row(sum, 0, 0);
  }

  // ------------------------------------------------------------ constraints

  /** e op 0 */
  private cmp(op: CmpOp, l: Linear, r: Linear): { e: LinExpr; op: CmpOp } {
    return { e: this.lin(l).addScaled(r, -1), op };
  }

  private post(c: CPCons, positive: boolean): void {
    switch (c.k) {
      case 'const':
        if (c.value !== positive) this.row(new LinExpr(), 1, 1);
        return;
      case 'cmp': {
        const { e, op } = this.cmp(positive ? c.op : NEGATE[c.op], c.l, c.r);
        return this.postCmp(e, op);
      }
      case 'not':
        return this.post(c.a, !positive);
      case 'and':
        if (positive) {
          this.post(c.a, true);
          this.post(c.b, true);
        } else {
          this.row(this.lin(this.reify(c.a)).addScaled(this.reify(c.b), 1), -Infinity, 1);
        }
        return;
      case 'or':
        if (!positive) {
          this.post(c.a, false);
          this.post(c.b, false);
        } else {
          this.row(this.lin(this.reify(c.a)).addScaled(this.reify(c.b), 1), 1, Infinity);
        }
        return;
      case 'imp':
        if (!positive) {
          this.post(c.a, true);
          this.post(c.b, false);
        } else {
          this.row(this.lin(this.reify(c.a)).addScaled(this.reify(c.b), -1), -Infinity, 0);
        }
        return;
      case 'equiv': {
        const d = this.lin(this.reify(c.a)).addScaled(this.reify(c.b), -1);
        if (positive) this.row(d, 0, 0);
        else this.row(this.lin(this.reify(c.a)).addScaled(this.reify(c.b), 1), 1, 1);
        return;
      }
      case 'member': {
        const b = this.reify(c);
        this.row(this.lin(b), positive ? 1 : 0, positive ? 1 : 0);
        return;
      }
    }
    this.no();
  }

  private postCmp(e: LinExpr, op: CmpOp): void {
    const integral = this.integral(e);
    switch (op) {
      case '<=':
        return this.row(e, -Infinity, 0);
      case '>=':
        return this.row(e, 0, Infinity);
      case '=':
        return this.row(e, 0, 0);
      case '<':
        return this.row(e, -Infinity, integral ? -1 : -EPS);
      case '>':
        return this.row(e, integral ? 1 : EPS, Infinity);
      case '!=': {
        // e <= -gap or e >= gap
        const b = this.bin('ne');
        const [lo, hi] = this.finiteBounds(e);
        const gap = integral ? 1 : EPS;
        // b = 0: e <= -gap;  b = 1: e >= gap
        this.row(this.lin(e).addScaled(b, -(hi + gap)), -Infinity, -gap);
        this.row(this.lin(e).addScaled(b, -(gap - lo)), lo, Infinity);
        return;
      }
    }
  }

  /** A binary equal to the truth value of c (target when given). */
  private reify(c: CPCons, target?: DVar): DVar {
    const b = target ?? this.bin('bool');
    switch (c.k) {
      case 'const':
        this.row(this.lin(b), c.value ? 1 : 0, c.value ? 1 : 0);
        return b;
      case 'cmp': {
        const { e, op } = this.cmp(c.op, c.l, c.r);
        this.reifyCmp(b, e, op);
        return b;
      }
      case 'not':
        this.row(this.lin(b).addScaled(this.reify(c.a), 1), 1, 1);
        return b;
      case 'and': {
        const x = this.reify(c.a);
        const y = this.reify(c.b);
        this.row(this.lin(b).addScaled(x, -1), -Infinity, 0);
        this.row(this.lin(b).addScaled(y, -1), -Infinity, 0);
        this.row(this.lin(b).addScaled(x, -1).addScaled(y, -1), -1, Infinity);
        return b;
      }
      case 'or':
      case 'imp': {
        let x = this.reify(c.a);
        if (c.k === 'imp') {
          const nx = this.bin('not');
          this.row(this.lin(nx).addScaled(x, 1), 1, 1);
          x = nx;
        }
        const y = this.reify(c.b);
        this.row(this.lin(b).addScaled(x, -1), 0, Infinity);
        this.row(this.lin(b).addScaled(y, -1), 0, Infinity);
        this.row(this.lin(b).addScaled(x, -1).addScaled(y, -1), -Infinity, 0);
        return b;
      }
      case 'equiv': {
        // b = 1 - (x xor y)
        const x = this.reify(c.a);
        const y = this.reify(c.b);
        const t = this.bin('xor');
        this.row(this.lin(t).addScaled(x, -1).addScaled(y, 1), 0, Infinity);
        this.row(this.lin(t).addScaled(y, -1).addScaled(x, 1), 0, Infinity);
        this.row(this.lin(t).addScaled(x, -1).addScaled(y, -1), -Infinity, 0);
        this.row(this.lin(t).addScaled(x, 1).addScaled(y, 1), -Infinity, 2);
        this.row(this.lin(b).addScaled(t, 1), 1, 1);
        return b;
      }
      case 'member': {
        // b = sum of the indicators of the values of x in S
        const x = c.x;
        const [lo, hi] = this.finiteBounds(x);
        if (!this.integral(x) || hi - lo + 1 > MAX_VALUES) this.no();
        const inS = new Set(c.values);
        const one = new LinExpr();
        const sum = this.lin(x);
        const bsum = this.lin(b);
        for (let v = Math.ceil(lo); v <= hi; v++) {
          const w = this.bin('value');
          one.addScaled(w, 1);
          sum.addScaled(w, -v);
          if (inS.has(v)) bsum.addScaled(w, -1);
        }
        this.row(one, 1, 1);
        this.row(sum, 0, 0);
        this.row(bsum, 0, 0);
        return b;
      }
    }
    this.no();
  }

  /** b <=> (e op 0) with big-M terms from the bounds of e. */
  private reifyCmp(b: DVar, e: LinExpr, op: CmpOp): void {
    const integral = this.integral(e);
    const gap = integral ? 1 : EPS;
    switch (op) {
      case '>=':
        return this.reifyLe(b, neg(e), gap);
      case '>':
        return this.reifyLe(b, neg(e).addScaled(gap, 1), gap);
      case '<':
        return this.reifyLe(b, this.lin(e).addScaled(gap, 1), gap);
      case '<=':
        return this.reifyLe(b, e, gap);
      case '=':
      case '!=': {
        // eq <=> (e <= 0 and e >= 0)
        const le = this.bin('le');
        const ge = this.bin('ge');
        this.reifyLe(le, e, gap);
        this.reifyLe(ge, neg(e), gap);
        if (op === '=') {
          // b = le and ge
          this.row(this.lin(b).addScaled(le, -1), -Infinity, 0);
          this.row(this.lin(b).addScaled(ge, -1), -Infinity, 0);
          this.row(this.lin(b).addScaled(le, -1).addScaled(ge, -1), -1, Infinity);
        } else {
          // b = not (le and ge)
          this.row(this.lin(b).addScaled(le, 1), 1, Infinity);
          this.row(this.lin(b).addScaled(ge, 1), 1, Infinity);
          this.row(this.lin(b).addScaled(le, 1).addScaled(ge, 1), -Infinity, 2);
        }
        return;
      }
    }
  }

  /** b <=> (e <= 0):  e <= hi (1 - b)  and  e >= gap + (lo - gap) b. */
  private reifyLe(b: DVar, e: LinExpr, gap: number): void {
    const [lo, hi] = this.finiteBounds(e);
    if (hi <= 0) return this.row(this.lin(b), 1, 1);
    if (lo > 0) return this.row(this.lin(b), 0, 0);
    this.row(this.lin(e).addScaled(b, hi), -Infinity, hi);
    this.row(this.lin(e).addScaled(b, -(lo - gap)), gap, Infinity);
  }
}

const NEGATE: Record<CmpOp, CmpOp> = { '<=': '>', '<': '>=', '>=': '<', '>': '<=', '=': '!=', '!=': '=' };

function neg(e: LinExpr): LinExpr {
  return new LinExpr().addScaled(e, -1);
}

function refersTo(d: CPDef, id: number): boolean {
  const has = (x: unknown) => x instanceof DVar && x.id === id;
  switch (d.k) {
    case 'linear':
      return d.e.terms.has(id);
    case 'post':
      return consRefers(d.cons, id);
    case 'reify':
      return has(d.b) || consRefers(d.cons, id);
    case 'minmax':
      return d.xs.some(has);
    case 'element':
      return has(d.idx) || d.items.some(has);
    case 'abs':
    case 'fn':
    case 'func':
      return has(d.x);
    case 'calendar':
      return has(d.start) || has(d.end);
    default:
      return has(d.x) || has(d.y);
  }
}

function consRefers(c: CPCons, id: number): boolean {
  const inLin = (e: Linear) => (typeof e === 'number' ? false : e instanceof DVar ? e.id === id : e.terms.has(id));
  switch (c.k) {
    case 'cmp':
      return inLin(c.l) || inLin(c.r);
    case 'and':
    case 'or':
    case 'imp':
    case 'equiv':
      return consRefers(c.a, id) || consRefers(c.b, id);
    case 'not':
      return consRefers(c.a, id);
    case 'member':
      return inLin(c.x);
    case 'const':
      return false;
  }
  return true;
}
