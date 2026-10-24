/**
 * Constraint store: variable domains, propagators, a propagation queue and a
 * trail for backtracking.
 */

import { Dom } from './domain.js';

export interface Propagator {
  readonly vars: readonly number[];
  /** Narrows domains; returns false on failure. */
  propagate(s: Store): boolean;
  /** Managed by the store. */
  queued?: boolean;
}

type TrailEntry = { v: number; d: Dom } | { undo: () => void };

/** Default precision for float variables in constraint programming. */
export const FLOAT_PRECISION = 1e-6;

export class Store {
  readonly doms: Dom[] = [];
  readonly names: string[] = [];
  readonly real: boolean[] = [];
  private readonly watchers: Propagator[][] = [];
  private readonly trail: TrailEntry[] = [];
  private queue: Propagator[] = [];
  private qhead = 0;
  /** When true, structural changes (new variables, propagators) are undone on backtrack. */
  searching = false;
  /** Minimisation bound for branch and bound: value(objVar) <= objBound. */
  objVar = -1;
  objBound = Infinity;
  precision = FLOAT_PRECISION;
  fails = 0;
  choicePoints = 0;
  propagations = 0;

  get numVars(): number {
    return this.doms.length;
  }

  addVar(d: Dom, name: string): number {
    const v = this.doms.length;
    this.doms.push(d);
    this.names.push(name);
    this.real.push(d.real);
    this.watchers.push([]);
    if (this.searching) {
      this.trail.push({
        undo: () => {
          this.doms.pop();
          this.names.pop();
          this.real.pop();
          this.watchers.pop();
        },
      });
    }
    return v;
  }

  /** Domain of a fixed value (constants are represented as fixed variables). */
  constant(value: number): number {
    const real = !Number.isInteger(value);
    return this.addVar(real ? Dom.range(value, value, true) : Dom.range(value, value), String(value));
  }

  post(p: Propagator): void {
    for (const v of new Set(p.vars)) this.watchers[v].push(p);
    if (this.searching) {
      this.trail.push({
        undo: () => {
          for (const v of new Set(p.vars)) {
            const w = this.watchers[v];
            if (w && w[w.length - 1] === p) w.pop();
            else if (w) w.splice(w.lastIndexOf(p), 1);
          }
        },
      });
    }
    this.enqueue(p);
  }

  private enqueue(p: Propagator): void {
    if (p.queued) return;
    p.queued = true;
    this.queue.push(p);
  }

  /** Runs propagators to a fixpoint. */
  propagate(): boolean {
    if (this.objVar >= 0 && !this.setMax(this.objVar, this.objBound)) return this.failNow();
    while (this.qhead < this.queue.length) {
      const p = this.queue[this.qhead++];
      p.queued = false;
      this.propagations++;
      if (!p.propagate(this)) return this.failNow();
    }
    this.queue = [];
    this.qhead = 0;
    return true;
  }

  private failNow(): false {
    for (let i = this.qhead; i < this.queue.length; i++) this.queue[i].queued = false;
    this.queue = [];
    this.qhead = 0;
    this.fails++;
    return false;
  }

  mark(): number {
    return this.trail.length;
  }

  restore(mark: number): void {
    const t = this.trail;
    while (t.length > mark) {
      const e = t.pop()!;
      if ('v' in e) this.doms[e.v] = e.d;
      else e.undo();
    }
  }

  /** Records an undo action for backtracking. */
  onBacktrack(undo: () => void): void {
    this.trail.push({ undo });
  }

  // ------------------------------------------------------------ queries

  dom(v: number): Dom {
    return this.doms[v];
  }
  min(v: number): number {
    return this.doms[v].min;
  }
  max(v: number): number {
    return this.doms[v].max;
  }
  size(v: number): number {
    return this.doms[v].size;
  }
  isBound(v: number): boolean {
    const d = this.doms[v];
    return d.size === 1 || (d.real && d.max - d.min <= this.precision * Math.max(1, Math.abs(d.min)));
  }
  value(v: number): number {
    const d = this.doms[v];
    return d.size === 1 ? d.min : (d.min + d.max) / 2;
  }

  // ------------------------------------------------------------ updates (false = wipe-out)

  setDom(v: number, d: Dom): boolean {
    const old = this.doms[v];
    if (d === old) return true;
    if (d.size === 0) return false;
    if (d.size === old.size && d.min === old.min && d.max === old.max) return true;
    this.trail.push({ v, d: old });
    this.doms[v] = d;
    for (const p of this.watchers[v]) this.enqueue(p);
    return true;
  }
  setMin(v: number, m: number): boolean {
    return this.setDom(v, this.doms[v].withMin(m));
  }
  setMax(v: number, m: number): boolean {
    return this.setDom(v, this.doms[v].withMax(m));
  }
  remove(v: number, a: number): boolean {
    return this.setDom(v, this.doms[v].without(a));
  }
  assign(v: number, a: number): boolean {
    const d = this.doms[v];
    if (d.real) return this.setDom(v, d.withMin(a).withMax(a));
    return d.contains(a) ? this.setDom(v, Dom.range(a, a)) : false;
  }
  restrict(v: number, d: Dom): boolean {
    return this.setDom(v, this.doms[v].intersect(d));
  }
}

