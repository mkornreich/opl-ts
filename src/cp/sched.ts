/**
 * Scheduling propagators: unary (disjunctive) resources with ranking, discrete
 * (cumulative) resources, state resources and reservoirs.
 */

import type { Propagator, Store } from './store.js';

/** An activity as seen by a resource; presence = -1 when the activity always uses it. */
export interface Task {
  start: number;
  end: number;
  dur: number;
  presence: number;
  /** Demand on a discrete resource / reservoir, or the required state. */
  amount: number;
  /** Activity name, for messages. */
  name: string;
}

function present(s: Store, t: Task): boolean | null {
  if (t.presence < 0) return true;
  if (!s.isBound(t.presence)) return null;
  return s.value(t.presence) === 1;
}

function taskVars(tasks: Task[]): number[] {
  const vs = new Set<number>();
  for (const t of tasks) {
    vs.add(t.start);
    vs.add(t.end);
    vs.add(t.dur);
    if (t.presence >= 0) vs.add(t.presence);
    if (t.amount >= 0) vs.add(t.amount);
  }
  return [...vs];
}

/** A task seen forwards, or mirrored in time (est = -lct, lct = -est) for the latest-end rules. */
function view(s: Store, t: Task, mirror: boolean): { est: number; lct: number; p: number } {
  return mirror ? { est: -s.max(t.end), lct: -s.min(t.start), p: s.min(t.dur) } : { est: s.min(t.start), lct: s.max(t.end), p: s.min(t.dur) };
}

/** est >= e (forwards), or end <= -e (mirrored). */
function pushAfter(s: Store, t: Task, e: number, mirror: boolean): boolean {
  return mirror ? s.setMax(t.end, -e) : s.setMin(t.start, e);
}

/**
 * Edge finding on a unary resource: when task i cannot end before the
 * latest end U of a set Omega (the tasks with lct <= U), it ends after all of
 * Omega, so it starts after Omega's earliest completion time.
 */
const NO_EDGE_FINDING = typeof process !== 'undefined' && !!process.env?.OPL_NO_EDGE_FINDING;

function edgeFindUnary(s: Store, ts: Task[], live: number[], mirror: boolean): boolean {
  if (live.length < 2 || NO_EDGE_FINDING) return true;
  const items = live.map((i) => ({ i, ...view(s, ts[i], mirror) }));
  const byEst = [...items].sort((a, b) => a.est - b.est);
  const lcts = [...new Set(items.map((x) => x.lct))].sort((a, b) => a - b);
  const push = new Map<number, number>();
  for (const U of lcts) {
    const omega = byEst.filter((x) => x.lct <= U);
    const m = omega.length;
    if (m === 0 || m === items.length) continue;
    // v_k = est_k + p of the Omega tasks starting no earlier; ECT(Omega) = max v.
    const suffix = new Float64Array(m + 1);
    for (let k = m - 1; k >= 0; k--) suffix[k] = suffix[k + 1] + omega[k].p;
    const v = omega.map((x, k) => x.est + suffix[k]);
    const pre = new Float64Array(m);
    const post = new Float64Array(m + 1).fill(-Infinity);
    for (let k = 0; k < m; k++) pre[k] = Math.max(k ? pre[k - 1] : -Infinity, v[k]);
    for (let k = m - 1; k >= 0; k--) post[k] = Math.max(post[k + 1], v[k]);
    const ect = pre[m - 1];
    if (ect > U) return false;
    for (const x of items) {
      if (x.lct <= U || x.p <= 0) continue;
      // Omega with x inserted at its est position.
      let lo = 0;
      let hi = m;
      while (lo < hi) {
        const mid = (lo + hi) >> 1;
        if (omega[mid].est <= x.est) lo = mid + 1;
        else hi = mid;
      }
      const withX = Math.max(lo ? pre[lo - 1] + x.p : -Infinity, post[lo], x.est + x.p + suffix[lo]);
      if (withX > U && ect > (push.get(x.i) ?? -Infinity)) push.set(x.i, ect);
    }
  }
  for (const [i, e] of push) if (!pushAfter(s, ts[i], e, mirror)) return false;
  return true;
}

/**
 * Energy-based edge finding on a cumulative resource: for a window [L, U]
 * and the tasks Omega inside it, the energy must fit (overload check); a task
 * i outside whose energy no longer fits with Omega's ends after Omega and
 * starts at least L + ceil(rest / c_i), rest = e(Omega) - (C - c_i)(U - L).
 */
function edgeFindCumulative(s: Store, live: Task[], cap: number, mirror: boolean): boolean {
  if (live.length < 2 || live.length > 60 || NO_EDGE_FINDING) return true;
  const items = live.map((t) => {
    const v = view(s, t, mirror);
    const c = s.min(t.amount);
    return { t, ...v, c, e: c * v.p };
  });
  const ests = [...new Set(items.map((x) => x.est))].sort((a, b) => a - b);
  const lcts = [...new Set(items.map((x) => x.lct))].sort((a, b) => a - b);
  const push = new Map<Task, number>();
  for (const U of lcts) {
    for (const L of ests) {
      if (L >= U) break;
      let E = 0;
      for (const x of items) if (x.est >= L && x.lct <= U) E += x.e;
      if (E === 0) continue;
      if (E > cap * (U - L)) return false;
      for (const x of items) {
        if ((x.est >= L && x.lct <= U) || x.lct <= U || x.e <= 0 || x.c > cap) continue;
        if (E + x.e <= cap * (U - Math.min(L, x.est))) continue;
        const rest = E - (cap - x.c) * (U - L);
        if (rest <= 0) continue;
        const e = L + Math.ceil(rest / x.c);
        if (e > (push.get(x.t) ?? -Infinity)) push.set(x.t, e);
      }
    }
  }
  for (const [t, e] of push) if (!pushAfter(s, t, e, mirror)) return false;
  return true;
}

/**
 * Activities that may not overlap: all pairs on a unary resource, pairs
 * requiring different states on a state resource.
 */
export class Disjunctive implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  /** Tasks ranked so far (indices into tasks), in order. */
  ranked: number[] = [];

  constructor(
    readonly name: string,
    readonly tasks: Task[],
    /** For state resources: only tasks requiring different states conflict. */
    readonly byState = false,
  ) {
    this.vars = taskVars(tasks);
  }

  private conflict(s: Store, i: number, j: number): boolean {
    if (!this.byState) return true;
    const a = this.tasks[i].amount;
    const b = this.tasks[j].amount;
    return !(s.isBound(a) && s.isBound(b) && s.value(a) === s.value(b));
  }

  propagate(s: Store): boolean {
    const ts = this.tasks;
    const live: number[] = [];
    for (let i = 0; i < ts.length; i++) if (present(s, ts[i]) === true) live.push(i);
    // Detectable precedences between pairs.
    for (let x = 0; x < live.length; x++) {
      for (let y = x + 1; y < live.length; y++) {
        const i = live[x];
        const j = live[y];
        if (!this.conflict(s, i, j)) continue;
        const a = ts[i];
        const b = ts[j];
        const aFirst = s.min(a.start) + s.min(a.dur) <= s.max(b.start);
        const bFirst = s.min(b.start) + s.min(b.dur) <= s.max(a.start);
        if (!aFirst && !bFirst) return false;
        if (!aFirst && (!s.setMin(a.start, s.min(b.end)) || !s.setMax(b.end, s.max(a.start)))) return false;
        if (!bFirst && (!s.setMin(b.start, s.min(a.end)) || !s.setMax(a.end, s.max(b.start)))) return false;
      }
    }
    if (this.byState) return true;
    return this.overload(s, live) && edgeFindUnary(s, ts, live, false) && edgeFindUnary(s, ts, live, true);
  }

  /** The tasks inside any window [est, lct] must fit into it. */
  private overload(s: Store, live: number[]): boolean {
    const ts = this.tasks;
    const info = live.map((i) => ({ est: s.min(ts[i].start), lct: s.max(ts[i].end), d: s.min(ts[i].dur) }));
    const byLct = [...info].sort((a, b) => a.lct - b.lct);
    for (const w of info) {
      let work = 0;
      for (const t of byLct) {
        if (t.est < w.est) continue;
        work += t.d;
        if (w.est + work > t.lct) return false;
      }
    }
    return true;
  }

  // ------------------------------------------------------------ ranking (search support)

  unranked(s: Store): number[] {
    const done = new Set(this.ranked);
    const out: number[] = [];
    for (let i = 0; i < this.tasks.length; i++) if (!done.has(i) && present(s, this.tasks[i]) !== false) out.push(i);
    return out;
  }

  isRanked(s: Store): boolean {
    return this.unranked(s).length === 0;
  }

  /** True when task i could come first among the unranked tasks. */
  possibleFirst(s: Store, i: number): boolean {
    const a = this.tasks[i];
    for (const j of this.unranked(s)) {
      if (j === i || present(s, this.tasks[j]) !== true) continue;
      if (s.min(a.start) + s.min(a.dur) > s.max(this.tasks[j].start)) return false;
    }
    return true;
  }
}

/** Discrete resource of fixed capacity: timetable (compulsory part) propagation. */
export class Cumulative implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly name: string,
    readonly tasks: Task[],
    readonly capacity: number,
  ) {
    this.vars = [...taskVars(tasks), capacity];
  }

  propagate(s: Store): boolean {
    const cap = s.max(this.capacity);
    const live = this.tasks.filter((t) => present(s, t) === true);
    // Compulsory parts [lst, ect).
    const events: [number, number][] = [];
    for (const t of live) {
      const lst = s.max(t.start);
      const ect = s.min(t.end);
      if (lst < ect) {
        events.push([lst, s.min(t.amount)], [ect, -s.min(t.amount)]);
      }
    }
    events.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    const segs: { from: number; to: number; h: number }[] = [];
    let h = 0;
    for (let k = 0; k < events.length; k++) {
      h += events[k][1];
      const next = events[k + 1]?.[0];
      if (next !== undefined && next > events[k][0] && h > 0) segs.push({ from: events[k][0], to: next, h });
    }
    for (const seg of segs) if (seg.h > cap) return false;
    if (!edgeFindCumulative(s, live, cap, false) || !edgeFindCumulative(s, live, cap, true)) return false;
    for (const t of live) {
      const q = s.min(t.amount);
      if (q <= 0) continue;
      const own = (seg: { from: number; to: number }) => (s.max(t.start) <= seg.from && seg.to <= s.min(t.end) ? q : 0);
      // Push the earliest start past overloaded segments, then the latest end.
      for (let moved = true; moved; ) {
        moved = false;
        const est = s.min(t.start);
        const d = s.min(t.dur);
        for (const seg of segs) {
          if (seg.h - own(seg) + q > cap && seg.from < est + d && seg.to > est) {
            if (!s.setMin(t.start, seg.to)) return false;
            moved = true;
            break;
          }
        }
      }
      for (let moved = true; moved; ) {
        moved = false;
        const lct = s.max(t.end);
        const d = s.min(t.dur);
        for (const seg of segs) {
          if (seg.h - own(seg) + q > cap && seg.from < lct && seg.to > lct - d) {
            if (!s.setMax(t.end, seg.from)) return false;
            moved = true;
            break;
          }
        }
      }
    }
    return true;
  }
}

/**
 * Reservoir: level = initial + produced - consumed stays in [0, capacity].
 * Consumption happens at the start of an activity, production at its end.
 * The level is checked once the event times are known.
 */
export class Reservoir implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly name: string,
    readonly consumers: Task[],
    readonly producers: Task[],
    readonly capacity: number,
    readonly initial: number,
  ) {
    this.vars = taskVars([...consumers, ...producers]);
  }

  propagate(s: Store): boolean {
    const events: [number, number][] = [];
    let possibleProduction = 0;
    for (const t of this.producers) {
      const p = present(s, t);
      if (p === false) continue;
      possibleProduction += s.max(t.amount);
      if (p === null || !s.isBound(t.end)) continue;
      events.push([s.value(t.end), s.min(t.amount)]);
    }
    let sureConsumption = 0;
    let complete = events.length === this.producers.filter((t) => present(s, t) !== false).length;
    for (const t of this.consumers) {
      const p = present(s, t);
      if (p === false) continue;
      if (p === null || !s.isBound(t.start)) {
        complete = false;
        if (p === true) sureConsumption += s.min(t.amount);
        continue;
      }
      sureConsumption += s.min(t.amount);
      events.push([s.value(t.start), -s.min(t.amount)]);
    }
    if (this.initial + possibleProduction - sureConsumption < 0) return false;
    if (!complete) return true;
    events.sort((a, b) => a[0] - b[0] || b[1] - a[1]);
    let level = this.initial;
    for (const [, delta] of events) {
      level += delta;
      if (level < 0 || level > this.capacity) return false;
    }
    return true;
  }
}

/** start(target) >= min over others of end(other): target is not ranked first. */
export class NotFirst implements Propagator {
  queued?: boolean;
  readonly vars: number[];
  constructor(
    readonly target: Task,
    readonly others: Task[],
  ) {
    this.vars = taskVars([target, ...others]);
  }

  propagate(s: Store): boolean {
    let m = Infinity;
    for (const o of this.others) if (present(s, o) !== false) m = Math.min(m, s.min(o.end));
    if (m === Infinity) return false;
    return s.setMin(this.target.start, m);
  }
}
