/**
 * Translates flattened constraints (CPCons / CPDef) into store propagators.
 */

import { fail } from '../errors.js';
import { DVar, LinExpr, type Linear } from '../linear.js';
import { Dom } from './domain.js';
import {
  Calendar, Abs, AllDifferent, Circuit, Distribute, Div, Element, Linear as LinearProp, LinearNe, MinMax, Mod, Monotone,
  ReifLinear, ReifMember, Table, Times, type LinKind,
} from './propagators.js';
import { CumulProfile, FuncProp, StateCheck, type CumulBound, type CumulItem, type StateItem } from './cumul.js';
import { Cumulative, Disjunctive, Reservoir, type Task } from './sched.js';
import { Store } from './store.js';
import {
  Activity, CP_FLOAT_BOUND, CP_MAXINT, Resource, StateFunction, type CmpOp, type CPCons, type CPDef, type CumulTerm, type FunctionWindow,
} from './terms.js';

interface LinForm {
  coefs: number[];
  vars: number[];
  c: number;
  /** All variables integer with integer coefficients: strict inequalities can shift by 1. */
  integral: boolean;
}

interface ResourceUse {
  tasks: Task[];
  consumers: Task[];
  producers: Task[];
}

const NEGATE: Record<CmpOp, CmpOp> = { '<=': '>', '<': '>=', '>=': '<', '>': '<=', '=': '!=', '!=': '=' };

/** Finite bounds for constraint programming: infinite bounds become +-maxint (or +-1e9 for floats). */
export function clampBounds(lb: number, ub: number, isInt: boolean): [number, number] {
  const big = isInt ? CP_MAXINT : CP_FLOAT_BOUND;
  return [isFinite(lb) ? lb : -big, isFinite(ub) ? ub : big];
}

export class CPBuilder {
  readonly store = new Store();
  /** Store variable index -> model variable (decision and auxiliary variables). */
  readonly dvars: (DVar | undefined)[] = [];
  private readonly constants = new Map<number, number>();
  private readonly uses = new Map<Resource, ResourceUse>();
  readonly disjunctives = new Map<Resource, Disjunctive>();
  /** False once a constraint failed while building (the model is infeasible). */
  ok = true;

  constructor(vars: DVar[]) {
    for (const v of vars) this.addDVar(v);
  }

  addDVar(v: DVar): number {
    const [lo, hi] = clampBounds(v.lb, v.ub, v.isInt);
    let d = Dom.range(lo, hi, !v.isInt);
    if (v.domain) d = d.intersect(Dom.values(v.domain));
    const idx = this.store.addVar(d, v.name);
    if (idx !== v.id) throw new Error(`internal: variable ${v.name} has id ${v.id} but store index ${idx}`);
    this.dvars[idx] = v;
    if (d.size === 0) this.ok = false;
    return idx;
  }

  dvar(id: number): DVar | undefined {
    return this.dvars[id];
  }

  constant(value: number): number {
    let v = this.constants.get(value);
    if (v === undefined || v >= this.store.numVars) {
      v = this.store.constant(value);
      if (!this.store.searching) this.constants.set(value, v);
    }
    return v;
  }

  /** Store variable for a linear expression (adds an auxiliary variable when needed). */
  varOf(e: Linear | DVar): number {
    if (typeof e === 'number') return this.constant(e);
    if (e instanceof DVar) return e.id;
    const f = this.lin(e, false);
    if (f.vars.length === 0) return this.constant(f.c);
    if (f.vars.length === 1 && f.coefs[0] === 1 && f.c === 0) return f.vars[0];
    let lo = f.c;
    let hi = f.c;
    f.vars.forEach((v, i) => {
      const a = f.coefs[i];
      lo += a > 0 ? a * this.store.min(v) : a * this.store.max(v);
      hi += a > 0 ? a * this.store.max(v) : a * this.store.min(v);
    });
    const z = this.store.addVar(Dom.range(lo, hi, !f.integral), 'expr');
    this.addProp(new LinearProp([...f.coefs, -1], [...f.vars, z], f.c, true));
    return z;
  }

  /** e as coefficients over store variables; scale multiplies integer expressions with rational coefficients to integer ones (only for comparisons with 0). */
  lin(e: Linear, scale = true): LinForm {
    const le = LinExpr.of(e);
    const coefs: number[] = [];
    const vars: number[] = [];
    let integral = Number.isInteger(le.constant);
    for (const [id, c] of le.terms) {
      if (c === 0) continue;
      coefs.push(c);
      vars.push(id);
      if (!Number.isInteger(c) || this.store.real[id]) integral = false;
    }
    let c = le.constant;
    if (scale && !integral && vars.every((v) => !this.store.real[v])) {
      // Scale rational coefficients of integer expressions to integers.
      for (let k = 2; k <= 1_000_000; k *= k < 1000 ? 2 : 10) {
        if ([...coefs, c].every((a) => Math.abs(a * k - Math.round(a * k)) < 1e-9 * Math.max(1, Math.abs(a * k)))) {
          return { coefs: coefs.map((a) => Math.round(a * k)), vars, c: Math.round(c * k), integral: true };
        }
      }
    }
    return { coefs, vars, c, integral };
  }

  private addProp(p: { vars: readonly number[]; propagate(s: Store): boolean }): void {
    this.store.post(p);
  }

  // ------------------------------------------------------------ comparisons

  private postLinear(f: LinForm, kind: LinKind): boolean {
    const s = this.store;
    const { coefs, vars, c } = f;
    if (vars.length === 0) {
      const ok = kind === 'le' ? c <= 1e-9 : kind === 'eq' ? Math.abs(c) <= 1e-9 : Math.abs(c) > 1e-9;
      return ok;
    }
    if (vars.length === 1) {
      const a = coefs[0];
      const v = vars[0];
      const x = -c / a;
      if (kind === 'eq') {
        if (!s.real[v] && Math.abs(x - Math.round(x)) > 1e-9) return false;
        return s.assign(v, s.real[v] ? x : Math.round(x));
      }
      if (kind === 'ne') return s.real[v] || Math.abs(x - Math.round(x)) > 1e-9 ? true : s.remove(v, Math.round(x));
      const t = s.real[v] ? 0 : 1e-9 * Math.max(1, Math.abs(x));
      return a > 0 ? s.setMax(v, x + t) : s.setMin(v, x - t);
    }
    if (kind === 'ne') this.addProp(new LinearNe(coefs, vars, c));
    else this.addProp(new LinearProp(coefs, vars, c, kind === 'eq'));
    return true;
  }

  /** l op r as (coefs, c, kind) over l - r. */
  private cmpForm(op: CmpOp, l: Linear, r: Linear): { f: LinForm; kind: LinKind } {
    const diff = LinExpr.of(l).clone().addScaled(r, -1);
    let f = this.lin(diff);
    const neg = (g: LinForm): LinForm => ({ ...g, coefs: g.coefs.map((a) => -a), c: -g.c });
    switch (op) {
      case '<=':
        return { f, kind: 'le' };
      case '<':
        return { f: { ...f, c: f.c + (f.integral ? 1 : 0) }, kind: 'le' };
      case '>=':
        return { f: neg(f), kind: 'le' };
      case '>':
        f = neg(f);
        return { f: { ...f, c: f.c + (f.integral ? 1 : 0) }, kind: 'le' };
      case '=':
        return { f, kind: 'eq' };
      case '!=':
        return { f, kind: 'ne' };
    }
  }

  // ------------------------------------------------------------ constraints

  /** Posts c (or its negation); returns false when it fails immediately. */
  post(c: CPCons, positive = true): boolean {
    const ok = this.postInner(c, positive);
    if (!ok) this.ok = false;
    return ok;
  }

  private postInner(c: CPCons, positive: boolean): boolean {
    const s = this.store;
    switch (c.k) {
      case 'const':
        return c.value === positive;
      case 'cmp': {
        const { f, kind } = this.cmpForm(positive ? c.op : NEGATE[c.op], c.l, c.r);
        return this.postLinear(f, kind);
      }
      case 'not':
        return this.postInner(c.a, !positive);
      case 'and':
        // not (a and b):  ba + bb <= 1
        if (positive) return this.postInner(c.a, true) && this.postInner(c.b, true);
        return this.postBools([this.reify(c.a), this.reify(c.b)], [1, 1], -1, 'le');
      case 'or':
        // a or b:  ba + bb >= 1
        if (!positive) return this.postInner(c.a, false) && this.postInner(c.b, false);
        return this.postBools([this.reify(c.a), this.reify(c.b)], [-1, -1], 1, 'le');
      case 'imp':
        if (!positive) return this.postInner(c.a, true) && this.postInner(c.b, false);
        return this.postBools([this.reify(c.a), this.reify(c.b)], [1, -1], 0, 'le');
      case 'equiv':
        return this.postBools([this.reify(c.a), this.reify(c.b)], [1, -1], 0, positive ? 'eq' : 'ne');
      case 'member': {
        const x = this.varOf(c.x);
        const set = Dom.values(c.values);
        return positive ? s.restrict(x, set) : s.setDom(x, s.dom(x).minus(set));
      }
    }
    if (!positive) fail(`${describe(c)} cannot be negated or used inside a logical expression`);
    switch (c.k) {
      case 'alldiff':
        this.addProp(new AllDifferent(c.xs.map((x) => this.varOf(x)), c.level === 'onDomain' || c.level === 'onRange'));
        return true;
      case 'count':
        this.addProp(new Distribute(c.cards.map((x) => this.varOf(x)), c.values, c.base.map((x) => this.varOf(x)), c.mode));
        return true;
      case 'table':
        this.addProp(new Table(c.xs.map((x) => this.varOf(x)), c.tuples, c.positive));
        return true;
      case 'circuit': {
        const xs = c.xs.map((x) => this.varOf(x));
        this.addProp(new AllDifferent(xs, false));
        this.addProp(new Circuit(xs, c.offset, !!c.sub));
        return true;
      }
      case 'uses':
        this.use(c.how, c.act, c.res, c.amount, c.presence);
        return true;
      case 'cumul':
        this.cumul(c.terms, c.lo, c.hi, c.window);
        return true;
      case 'stateCheck':
        this.stateCheck(c.f);
        return true;
    }
  }

  private windowVars(w: FunctionWindow): { start: number | null; end: number | null; presence: number } {
    if (w.k === 'all') return { start: null, end: null, presence: -1 };
    if (w.k === 'fixed') return { start: this.constant(w.from), end: this.constant(w.to), presence: -1 };
    return { start: w.act.start.id, end: w.act.end.id, presence: w.act.presence ? w.act.presence.id : -1 };
  }

  /** lo <= f <= hi on the window, and f >= 0 everywhere. */
  private cumul(terms: CumulTerm[], lo: number, hi: number, window: FunctionWindow): void {
    const items: CumulItem[] = terms.map((t) => {
      const height = this.varOf(t.height);
      if (!t.act) {
        return { step: t.kind === 'step', start: this.constant(t.from), end: this.constant(t.to), dur: -1, height, presence: -1 };
      }
      const presence = t.act.presence ? t.act.presence.id : -1;
      if (t.kind === 'pulse') {
        const task = this.task(t.act, presence, 0);
        return { step: false, start: task.start, end: task.end, dur: task.dur, height, presence };
      }
      return { step: true, start: (t.at === 'start' ? t.act.start : t.act.end).id, end: -1, dur: -1, height, presence };
    });
    const bounds: CumulBound[] = [{ start: null, end: null, presence: -1, lo: 0, hi: Infinity }];
    bounds.push({ ...this.windowVars(window), lo, hi });
    this.addProp(new CumulProfile('cumul function', items, bounds));
  }

  private stateCheck(f: StateFunction): void {
    const items: StateItem[] = f.windows.map((w) => ({
      kind: w.kind,
      ...this.windowVars(w.window),
      value: w.kind === 'equal' ? this.constant(w.value) : w.state ? w.state.id : -1,
      lo: w.lo,
      hi: w.hi,
      aligns: w.aligns,
      aligne: w.aligne,
    }));
    this.addProp(new StateCheck(f.name, items, (a, b) => f.distance(a, b)));
  }

  /** sum(coefs * bools) + c  kind  0 */
  private postBools(bs: number[], coefs: number[], c: number, kind: LinKind): boolean {
    return this.postLinear({ coefs, vars: bs, c, integral: true }, kind);
  }

  /** A 0/1 store variable equal to the truth value of c (or `target` when given). */
  reify(c: CPCons, target?: number): number {
    const s = this.store;
    const b = target ?? s.addVar(Dom.range(0, 1), 'bool');
    switch (c.k) {
      case 'const':
        if (!s.assign(b, c.value ? 1 : 0)) this.ok = false;
        return b;
      case 'cmp': {
        const { f, kind } = this.cmpForm(c.op, c.l, c.r);
        if (f.vars.length === 0) {
          const truth = kind === 'le' ? f.c <= 1e-9 : kind === 'eq' ? Math.abs(f.c) <= 1e-9 : Math.abs(f.c) > 1e-9;
          if (!s.assign(b, truth ? 1 : 0)) this.ok = false;
        } else {
          this.addProp(new ReifLinear(b, f.coefs, f.vars, f.c, kind, f.integral));
        }
        return b;
      }
      case 'not': {
        const a = this.reify(c.a);
        this.addProp(new LinearProp([1, 1], [b, a], -1, true));
        return b;
      }
      case 'and': {
        const [x, y] = [this.reify(c.a), this.reify(c.b)];
        this.addProp(new LinearProp([1, -1], [b, x], 0, false));
        this.addProp(new LinearProp([1, -1], [b, y], 0, false));
        this.addProp(new LinearProp([-1, 1, 1], [b, x, y], -1, false));
        return b;
      }
      case 'or':
      case 'imp': {
        let x = this.reify(c.a);
        if (c.k === 'imp') {
          const nx = s.addVar(Dom.range(0, 1), 'bool');
          this.addProp(new LinearProp([1, 1], [nx, x], -1, true));
          x = nx;
        }
        const y = this.reify(c.b);
        this.addProp(new LinearProp([-1, 1], [b, x], 0, false));
        this.addProp(new LinearProp([-1, 1], [b, y], 0, false));
        this.addProp(new LinearProp([1, -1, -1], [b, x, y], 0, false));
        return b;
      }
      case 'equiv': {
        const [x, y] = [this.reify(c.a), this.reify(c.b)];
        this.addProp(new ReifLinear(b, [1, -1], [x, y], 0, 'eq', true));
        return b;
      }
      case 'member':
        this.addProp(new ReifMember(b, this.varOf(c.x), Dom.values(c.values)));
        return b;
    }
    fail(`${describe(c)} cannot be used inside a logical expression or as a value`);
  }

  // ------------------------------------------------------------ definitions

  define(def: CPDef): void {
    const v = (x: DVar | number) => this.varOf(x);
    switch (def.k) {
      case 'mul':
        this.addProp(new Times(v(def.z), v(def.x), v(def.y)));
        return;
      case 'div':
        this.addProp(new Div(v(def.z), v(def.x), v(def.y)));
        return;
      case 'realdiv':
        // z = x / y  <=>  x = z * y
        this.addProp(new Times(v(def.x), v(def.z), v(def.y)));
        return;
      case 'mod':
        this.addProp(new Mod(v(def.z), v(def.x), v(def.y)));
        return;
      case 'abs':
        this.addProp(new Abs(v(def.z), v(def.x)));
        return;
      case 'fn':
        if (def.fn === 'sqrt') this.addProp(new Monotone(v(def.z), v(def.x), Math.sqrt, (y) => y * y, 0));
        else if (def.fn === 'exp') this.addProp(new Monotone(v(def.z), v(def.x), Math.exp, Math.log));
        else this.addProp(new Monotone(v(def.z), v(def.x), (x) => Math.log(Math.max(x, 1e-300)), Math.exp, 0));
        return;
      case 'minmax':
        this.addProp(new MinMax(v(def.z), def.xs.map(v), def.isMin));
        return;
      case 'element':
        this.addProp(new Element(v(def.z), v(def.idx), def.keys, def.items.map(v)));
        return;
      case 'reify':
        this.reify(def.cons, v(def.b));
        return;
      case 'linear': {
        const f = this.lin(def.e, false);
        this.addProp(new LinearProp([...f.coefs, -1], [...f.vars, v(def.z)], f.c, true));
        return;
      }
      case 'post':
        this.post(def.cons);
        return;
      case 'calendar':
        this.addProp(new Calendar(v(def.start), v(def.end), def.size, def.f));
        return;
      case 'func':
        this.addProp(new FuncProp(v(def.z), v(def.x), def.f, def.points));
        return;
    }
  }

  // ------------------------------------------------------------ scheduling

  task(act: Activity, presence: number, amount: Linear): Task {
    // Calendar activities occupy [start, end), longer than their size.
    const occupied = act.intensity || act.breakable ? LinExpr.of(act.end).clone().addScaled(act.start, -1) : act.duration;
    return {
      start: act.start.id,
      end: act.end.id,
      dur: this.varOf(occupied),
      presence,
      amount: this.varOf(amount),
      name: act.name,
    };
  }

  private useOf(r: Resource): ResourceUse {
    let u = this.uses.get(r);
    if (!u) this.uses.set(r, (u = { tasks: [], consumers: [], producers: [] }));
    return u;
  }

  /** A requirement; presence is the selection variable for a member of an alternative set. */
  private use(how: 'requires' | 'consumes' | 'produces', act: Activity, res: Resource, amount: Linear, presence: DVar | null): void {
    if (this.store.searching) fail('resource constraints cannot be posted during search');
    if (res.kind === 'alternative') fail('internal: alternative resources are expanded before building');
    this.addUse(this.useOf(res), res, how, this.task(act, presence ? presence.id : -1, amount));
  }

  private addUse(u: ResourceUse, res: Resource, how: string, t: Task): void {
    if (res.kind === 'reservoir') {
      if (how === 'produces') u.producers.push(t);
      else u.consumers.push(t);
      return;
    }
    if (how !== 'requires') fail(`${how} needs a Reservoir (${res.name} is a ${res.kind} resource); use requires`);
    u.tasks.push(t);
  }

  /** Posts one propagator per resource once all requirements are known. */
  finishResources(): void {
    for (const [res, u] of this.uses) {
      switch (res.kind) {
        case 'unary':
        case 'state': {
          const d = new Disjunctive(res.name, u.tasks, res.kind === 'state');
          this.disjunctives.set(res, d);
          this.addProp(d);
          break;
        }
        case 'discrete':
          this.addProp(new Cumulative(res.name, u.tasks, this.constant(res.capacity)));
          break;
        case 'reservoir':
          this.addProp(new Reservoir(res.name, u.consumers, u.producers, res.capacity, res.initial));
          break;
      }
    }
  }
}

function describe(c: CPCons): string {
  switch (c.k) {
    case 'alldiff':
      return 'alldifferent';
    case 'count':
      return c.mode === 'exact' ? 'distribute' : c.mode;
    case 'circuit':
      return 'circuit';
    case 'table':
      return c.positive ? 'allowedAssignments' : 'forbiddenAssignments';
    case 'uses':
      return `${c.how}`;
    case 'cumul':
      return 'a cumul function constraint';
    case 'stateCheck':
      return 'a state function constraint';
  }
  return c.k;
}
