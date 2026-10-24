/**
 * Search: OPL search procedures (forall, tryall, select, try, if, while,
 * LDSearch, generate, setTimes, rank, ...) interpreted as depth-first search
 * with continuations, default labelling, and branch and bound for objectives.
 *
 * Every step takes a continuation k; a step returns true to stop the whole
 * search (solution found / limit reached) and false to backtrack.
 */

import type { Expr, Quantifier, SStmt } from '../ast.js';
import { fail, type SourcePos } from '../errors.js';
import { Evaluator, Scope } from '../eval.js';
import { DVar, LinExpr } from '../linear.js';
import { elementsOf, OplArray, OplTuple, RawArray, typeName, type Value } from '../values.js';
import { CPBuilder } from './builder.js';
import { Linear as LinearProp, ReifLinear } from './propagators.js';
import { Disjunctive, NotFirst } from './sched.js';
import { Dom } from './domain.js';
import { SearchLimit } from './store.js';
import { memoryExceeded } from '../solver/memory.js';
import { Activity, CPConstraint, Flattener, Resource, type CPCons, type CPDef, type CPHooks } from './terms.js';

type K = () => boolean;

export interface CPProblem {
  /** All model variables (decision and auxiliary), indexed by id. */
  vars: DVar[];
  /** Variables labelled by the default search, in declaration order. */
  decision: DVar[];
  rows: { expr: LinExpr; lower: number; upper: number }[];
  cons: CPCons[];
  defs: CPDef[];
  objective: LinExpr | null;
  maximize: boolean;
  activities: Activity[];
  selections: Map<Activity, Map<Resource, DVar[]>>;
  search: SStmt[] | null;
  ev: Evaluator;
  scope: Scope;
}

export interface CPOptions {
  timeLimit?: number;
  allSolutions?: boolean;
  /** Stop enumerating after this many solutions. */
  maxSolutions?: number;
}

export interface CPResult {
  status: 'optimal' | 'feasible' | 'infeasible' | 'limit';
  /** Solutions found (values of problem.vars), best last. */
  solutions: Float64Array[];
  objective: number;
  fails: number;
  choicePoints: number;
}

export function solveCP(p: CPProblem, options: CPOptions = {}): CPResult {
  const b = new CPBuilder(p.vars);
  const s = b.store;
  const result: CPResult = { status: 'infeasible', solutions: [], objective: NaN, fails: 0, choicePoints: 0 };
  const finish = (): CPResult => {
    result.fails = s.fails;
    result.choicePoints = s.choicePoints;
    return result;
  };

  for (const row of p.rows) {
    if (row.lower === row.upper) b.post({ k: 'cmp', op: '=', l: row.expr, r: row.lower });
    else {
      if (isFinite(row.lower)) b.post({ k: 'cmp', op: '>=', l: row.expr, r: row.lower });
      if (isFinite(row.upper)) b.post({ k: 'cmp', op: '<=', l: row.expr, r: row.upper });
    }
  }
  for (const def of p.defs) b.define(def);
  for (const c of p.cons) b.post(c);
  b.finishResources();

  let objVar = -1;
  let step = 1;
  if (p.objective) {
    const obj = p.objective.clone();
    if (p.maximize) for (const [id, c] of obj.terms) obj.terms.set(id, -c);
    if (p.maximize) obj.constant = -obj.constant;
    const f = b.lin(obj);
    objVar = b.varOf(obj);
    step = f.integral ? 1 : 0;
    s.objVar = objVar;
  }
  const deadline = options.timeLimit ? performance.now() + options.timeLimit * 1000 : Infinity;
  s.deadline = deadline;
  try {
    if (!b.ok || !s.propagate()) return finish();
  } catch (e) {
    if (!(e instanceof SearchLimit)) throw e;
    result.status = 'limit';
    return finish();
  }

  s.searching = true;
  const onSolution = (): boolean => {
    const values = new Float64Array(p.vars.length);
    for (let i = 0; i < p.vars.length; i++) values[i] = s.value(i);
    result.solutions.push(values);
    if (objVar >= 0) {
      const v = s.value(objVar);
      s.objBound = v - (step || Math.max(1e-9, 1e-6 * Math.abs(v)));
      return false;
    }
    return !options.allSolutions || result.solutions.length >= (options.maxSolutions ?? Infinity);
  };

  const ev = p.ev;
  const savedPhase = ev.phase;
  const savedHooks = ev.cp;
  const search = new Search(b, ev, p, deadline, onSolution);
  ev.phase = 'search';
  ev.cp = search.hooks;
  ev.searchFns = (fn, args, pos) => search.query(fn, args, pos);
  try {
    search.run();
  } catch (e) {
    if (!(e instanceof SearchLimit)) throw e;
    search.limitHit = true;
  } finally {
    ev.phase = savedPhase;
    ev.cp = savedHooks;
    ev.searchFns = null;
  }

  if (result.solutions.length > 0) {
    result.status = search.limitHit ? 'feasible' : 'optimal';
    if (p.objective) {
      const best = result.solutions[result.solutions.length - 1];
      let v = p.objective.constant;
      for (const [id, c] of p.objective.terms) v += c * best[id];
      result.objective = v;
    }
  } else {
    result.status = search.limitHit ? 'limit' : 'infeasible';
  }
  return finish();
}

function buildHooks(b: CPBuilder, selections: Map<Activity, Map<Resource, DVar[]>>): CPHooks {
  const s = b.store;
  return {
    newVar(lo, hi, isInt, name) {
      const v = new DVar(s.numVars, name, isInt, lo, hi);
      b.addDVar(v);
      return v;
    },
    define(def) {
      b.define(def);
    },
    bounds(v) {
      return [s.min(v.id), s.max(v.id)];
    },
    domain(v) {
      return s.dom(v.id);
    },
    dvar(id) {
      return b.dvar(id);
    },
    selections,
  };
}

const SEARCH_BUILTINS = new Set([
  'generate', 'generateSeq', 'setTimes', 'rank', 'tryRankFirst', 'assignAlternatives',
]);

class Search {
  readonly hooks: CPHooks;
  limitHit = false;
  private discrepancies = 0;
  private discrepancyLimit = Infinity;
  private readonly flat: Flattener;

  constructor(
    private readonly b: CPBuilder,
    private readonly ev: Evaluator,
    private readonly p: CPProblem,
    private readonly deadline: number,
    private readonly onSolution: () => boolean,
  ) {
    this.hooks = buildHooks(b, p.selections);
    this.flat = new Flattener(this.hooks);
  }

  private get s() {
    return this.b.store;
  }

  run(): void {
    const finish = () => this.complete(() => this.solution());
    if (this.p.search) this.exec(this.p.search, 0, this.p.scope, finish);
    else finish();
  }

  /** Default search for whatever the user search left unbound. */
  private complete(k: K): boolean {
    const decision = this.p.decision.map((v) => v.id);
    const selections: number[] = [];
    for (const byAlt of this.p.selections.values()) for (const sel of byAlt.values()) selections.push(...sel.map((v) => v.id));
    const rest = () => this.label([...Array(this.s.numVars).keys()], true, k);
    // Scheduling models: choose resources, order the tasks of each unary
    // resource, set start times earliest first, then the rest.
    if (this.p.activities.length) {
      const unary = [...this.b.disjunctives.values()];
      return this.label(selections, false, () =>
        this.rank(unary, () => this.setTimes(this.p.activities, () => this.label(decision, true, rest))));
    }
    return this.label(decision, true, () => this.label(selections, false, rest));
  }

  private solution(): boolean {
    return this.onSolution();
  }

  private timeUp(): boolean {
    if (this.limitHit) return true;
    if ((this.s.choicePoints & 255) === 0 && (performance.now() > this.deadline || memoryExceeded())) this.limitHit = true;
    return this.limitHit;
  }

  /**
   * After backtracking, the objective bound may be better than when this
   * state was propagated: propagate again.  False when the state is dead.
   */
  private reapplyBound(): boolean {
    const s = this.s;
    if (s.objVar < 0 || s.max(s.objVar) <= s.objBound) return true;
    return s.propagate();
  }

  /** Tries alternatives 0..n-1 in order (an OR node). */
  private alternatives(n: number, run: (i: number) => boolean): boolean {
    for (let i = 0; i < n; i++) {
      if (this.timeUp()) return true;
      if (i > 0 && this.discrepancies >= this.discrepancyLimit) return false;
      const mark = this.s.mark();
      const saved = this.discrepancies;
      if (i > 0) this.discrepancies++;
      this.s.choicePoints++;
      if (run(i)) return true;
      this.s.restore(mark);
      this.discrepancies = saved;
    }
    return false;
  }

  // ------------------------------------------------------------ labelling

  private labelVar(v: number, k: K): boolean {
    const s = this.s;
    if (s.isBound(v)) return k();
    if (s.real[v]) {
      const mid = (s.min(v) + s.max(v)) / 2;
      return this.alternatives(2, (i) => (i === 0 ? s.setMax(v, mid) : s.setMin(v, mid)) && s.propagate() && this.labelVar(v, k));
    }
    const values = s.dom(v).values();
    let i = 0;
    for (const val of values) {
      if (this.timeUp()) return true;
      if (i > 0 && !this.reapplyBound()) return false;
      if (val > s.max(v)) break;
      if (!s.dom(v).contains(val)) continue;
      if (i > 0 && this.discrepancies >= this.discrepancyLimit) return false;
      const mark = s.mark();
      const saved = this.discrepancies;
      if (i++ > 0) this.discrepancies++;
      s.choicePoints++;
      if (s.assign(v, val) && s.propagate() && k()) return true;
      s.restore(mark);
      this.discrepancies = saved;
    }
    return false;
  }

  /**
   * Labels vars, smallest domain first (firstFail) or in order, then calls k.
   * An explicit stack instead of recursion: models label thousands of variables.
   */
  private label(vars: number[], firstFail: boolean, k: K): boolean {
    const s = this.s;
    interface Frame {
      v: number;
      /** The values still to try (lazily: domains can be huge), or null for the two halves of a float variable. */
      values: Iterator<number> | null;
      mid: number;
      i: number;
      mark: number;
      saved: number;
    }
    const stack: Frame[] = [];
    let stop = false;
    const pick = (): number => {
      // A float variable is split until it is bound, as before.
      const top = stack[stack.length - 1];
      if (top && top.values === null && !s.isBound(top.v)) return top.v;
      // dom/wdeg: the smallest domain per unit of constraint weight.
      let best = -1;
      let bestScore = Infinity;
      for (const v of vars) {
        if (v >= s.numVars || s.isBound(v)) continue;
        if (!firstFail) return v;
        const score = s.size(v) / s.weight(v);
        if (score < bestScore) {
          bestScore = score;
          best = v;
        }
      }
      return best;
    };
    /** Applies the frame's next alternative; false when none is left (or the search stops). */
    const advance = (f: Frame): boolean => {
      for (;;) {
        if (f.i > 0 && !this.reapplyBound()) return false;
        let val = 0;
        if (f.values) {
          const r = f.values.next();
          if (r.done || r.value > s.max(f.v)) return false;
          val = r.value;
          if (!s.dom(f.v).contains(val)) continue;
        } else if (f.i >= 2) return false;
        if (this.timeUp()) {
          stop = true;
          return false;
        }
        if (f.i > 0 && this.discrepancies >= this.discrepancyLimit) return false;
        f.mark = s.mark();
        f.saved = this.discrepancies;
        if (f.i > 0) this.discrepancies++;
        const i = f.i++;
        s.choicePoints++;
        const ok = f.values ? s.assign(f.v, val) : i === 0 ? s.setMax(f.v, f.mid) : s.setMin(f.v, f.mid);
        if (ok && s.propagate()) return true;
        s.restore(f.mark);
        this.discrepancies = f.saved;
      }
    };
    for (;;) {
      const v = pick();
      let descended = false;
      if (v < 0) {
        if (k()) return true;
      } else {
        const f: Frame = { v, values: s.real[v] ? null : s.dom(v).values(), mid: (s.min(v) + s.max(v)) / 2, i: 0, mark: s.mark(), saved: 0 };
        stack.push(f);
        descended = advance(f);
        if (stop) return true;
        if (!descended) stack.pop();
      }
      if (descended) continue;
      // Backtrack: undo the deepest choice and try its next alternative.
      for (;;) {
        const f = stack[stack.length - 1];
        if (!f) return false;
        s.restore(f.mark);
        this.discrepancies = f.saved;
        if (advance(f)) break;
        if (stop) return true;
        stack.pop();
      }
    }
  }

  /** Schedules activities by start time, earliest start first. */
  private setTimes(acts: Activity[], k: K): boolean {
    const s = this.s;
    const next = (): boolean => {
      let best: Activity | null = null;
      for (const a of acts) {
        if (s.isBound(a.start.id)) continue;
        if (!best || s.min(a.start.id) < s.min(best.start.id) ||
            (s.min(a.start.id) === s.min(best.start.id) && s.max(a.start.id) < s.max(best.start.id))) best = a;
      }
      return best ? this.labelVar(best.start.id, next) : k();
    };
    return next();
  }

  // ------------------------------------------------------------ ranking

  private disjunctive(r: Value, pos: SourcePos): Disjunctive {
    if (!(r instanceof Resource)) fail(`expected a resource, found a ${typeName(r)}`, pos);
    const d = this.b.disjunctives.get(r);
    if (!d) {
      if (r.kind !== 'unary' && r.kind !== 'state') fail(`${r.name} is not a unary or state resource`, pos);
      return new Disjunctive(r.name, []);
    }
    return d;
  }

  private taskIndex(d: Disjunctive, a: Value, pos: SourcePos): number {
    if (!(a instanceof Activity)) fail(`expected an activity, found a ${typeName(a)}`, pos);
    const i = d.tasks.findIndex((t) => t.start === a.start.id && t.presence < 0);
    const j = i >= 0 ? i : d.tasks.findIndex((t) => t.start === a.start.id);
    if (j < 0) fail(`${a.name} does not require ${d.name}`, pos);
    return j;
  }

  private rankFirst(d: Disjunctive, i: number): boolean {
    const s = this.s;
    const t = d.tasks[i];
    for (const j of d.unranked(s)) {
      if (j === i) continue;
      const o = d.tasks[j];
      if (o.presence < 0) s.post(new LinearProp([1, -1], [t.end, o.start], 0, false));
      else {
        const bv = s.addVar(Dom.range(0, 1), 'before');
        s.post(new ReifLinear(bv, [1, -1], [t.end, o.start], 0, 'le', true));
        s.post(new LinearProp([1, -1], [o.presence, bv], 0, false));
      }
    }
    d.ranked.push(i);
    s.onBacktrack(() => d.ranked.pop());
    return s.propagate();
  }

  private tryRankFirst(d: Disjunctive, i: number, k: K): boolean {
    const s = this.s;
    return this.alternatives(2, (alt) => {
      if (alt === 0) return this.rankFirst(d, i) && k();
      const others = d.unranked(s).filter((j) => j !== i).map((j) => d.tasks[j]);
      if (others.length === 0) return false;
      s.post(new NotFirst(d.tasks[i], others));
      return s.propagate() && k();
    });
  }

  private rank(ds: Disjunctive[], k: K): boolean {
    const s = this.s;
    const next = (): boolean => {
      for (const d of ds) {
        // Decide optional activities first.
        const undecided = d.tasks.find((t) => t.presence >= 0 && !s.isBound(t.presence));
        if (undecided) return this.labelVar(undecided.presence, next);
        const unranked = d.unranked(s);
        if (unranked.length === 0) continue;
        const firsts = unranked.filter((i) => d.possibleFirst(s, i));
        if (firsts.length === 0) return false;
        firsts.sort((x, y) => s.min(d.tasks[x].start) - s.min(d.tasks[y].start) || s.max(d.tasks[x].start) - s.max(d.tasks[y].start));
        return this.alternatives(firsts.length, (n) => this.rankFirst(d, firsts[n]) && next());
      }
      return k();
    };
    return next();
  }

  // ------------------------------------------------------------ queries (evaluator call-backs)

  query(fn: string, args: Value[], pos: SourcePos): Value | undefined {
    const s = this.s;
    switch (fn) {
      case 'isRanked': {
        const rs = collect(args[0]);
        return rs.every((r) => this.disjunctive(r, pos).isRanked(s)) ? 1 : 0;
      }
      case 'nbPossibleFirst': {
        const d = this.disjunctive(args[0], pos);
        return d.unranked(s).filter((i) => d.possibleFirst(s, i)).length;
      }
      case 'isPossibleFirst': {
        const d = this.disjunctive(args[0], pos);
        const i = this.taskIndex(d, args[1], pos);
        return d.unranked(s).includes(i) && d.possibleFirst(s, i) ? 1 : 0;
      }
      case 'nbUnranked':
        return this.disjunctive(args[0], pos).unranked(s).length;
    }
    return undefined;
  }

  // ------------------------------------------------------------ statements

  private exec(stmts: SStmt[], i: number, scope: Scope, k: K): boolean {
    if (i === stmts.length) return k();
    const st = stmts[i];
    const rest: K = () => this.exec(stmts, i + 1, scope, k);
    switch (st.k) {
      case 'post':
        return this.post(st.e, scope, rest);
      case 'forall': {
        const loop = (remaining: Scope[]): boolean => {
          if (remaining.length === 0) return rest();
          const idx = st.q.order ? this.best(remaining, st.q) : 0;
          const others = remaining.filter((_, j) => j !== idx);
          return this.exec(st.body, 0, remaining[idx], () => loop(others));
        };
        return loop(this.bindings(st.q, scope));
      }
      case 'tryall': {
        const items = this.bindings(st.q, scope);
        if (st.q.order) {
          const keys = items.map((sc) => this.key(st.q, sc));
          const order = items.map((_, j) => j).sort((x, y) => keys[x] - keys[y] || x - y);
          return this.alternatives(order.length, (n) => this.exec(st.body, 0, items[order[n]], rest));
        }
        return this.alternatives(items.length, (n) => this.exec(st.body, 0, items[n], rest));
      }
      case 'select': {
        const items = this.bindings(st.q, scope);
        if (items.length === 0) return rest();
        const idx = st.q.order ? this.best(items, st.q) : 0;
        return this.exec(st.body, 0, items[idx], rest);
      }
      case 'try':
        return this.alternatives(st.alts.length, (n) => this.exec(st.alts[n], 0, new Scope(scope), rest));
      case 'if':
        return this.exec(this.ev.truthy(st.c, scope) ? st.then : st.else, 0, new Scope(scope), rest);
      case 'while': {
        const loop: K = () => (this.ev.truthy(st.c, scope) ? this.exec(st.body, 0, new Scope(scope), loop) : rest());
        return loop();
      }
      case 'strategy': {
        if (st.name !== 'LDSearch') return this.exec(st.body, 0, scope, rest);
        const limit = st.args[0] ? this.ev.num(st.args[0], scope) : 4;
        const saved = this.discrepancyLimit;
        this.discrepancyLimit = Math.min(saved, this.discrepancies + limit);
        const r = this.exec(st.body, 0, scope, () => {
          const inner = this.discrepancyLimit;
          this.discrepancyLimit = saved;
          const res = rest();
          this.discrepancyLimit = inner;
          return res;
        });
        this.discrepancyLimit = saved;
        return r;
      }
    }
  }

  /** One child scope per assignment of the quantifier (snapshot of the iterators). */
  private bindings(q: Quantifier, scope: Scope): Scope[] {
    const out: Scope[] = [];
    this.ev.forEach({ ...q, order: undefined }, scope, (sc) => {
      const copy = new Scope(scope);
      for (const b of q.binders) for (const n of b.names) copy.define(n, { ...sc.lookup(n)! });
      out.push(copy);
    });
    return out;
  }

  private key(q: Quantifier, sc: Scope): number {
    return q.order!.dir * this.ev.num(q.order!.key, sc);
  }

  private best(items: Scope[], q: Quantifier): number {
    let best = 0;
    let bestKey = Infinity;
    items.forEach((sc, j) => {
      const key = this.key(q, sc);
      if (key < bestKey) {
        bestKey = key;
        best = j;
      }
    });
    return best;
  }

  private post(e: Expr, scope: Scope, k: K): boolean {
    if (e.k === 'call' && SEARCH_BUILTINS.has(e.fn)) return this.builtin(e.fn, e.args, scope, e.pos, k);
    const v = this.ev.eval(e, scope);
    if (typeof v === 'number') return v !== 0 && k();
    if (v instanceof CPConstraint) {
      const mark = this.s.mark();
      if (this.b.post(v.c) && this.s.propagate() && k()) return true;
      this.s.restore(mark);
      return false;
    }
    fail(`a search step must be a constraint or a search instruction, found a ${typeName(v)}`, e.pos);
  }

  private builtin(fn: string, argExprs: Expr[], scope: Scope, pos: SourcePos, k: K): boolean {
    const args = argExprs.map((a) => this.ev.evalRef(a, scope));
    switch (fn) {
      case 'generate':
      case 'generateSeq': {
        const vars = args.flatMap((a) => collect(a)).map((v) => this.varOf(v, pos));
        return this.label(vars, fn === 'generate', k);
      }
      case 'setTimes': {
        const acts = args.flatMap((a) => collect(a));
        for (const a of acts) if (!(a instanceof Activity)) fail(`setTimes needs activities, found a ${typeName(a)}`, pos);
        return this.setTimes(acts as Activity[], k);
      }
      case 'rank':
        return this.rank(args.flatMap((a) => collect(a)).map((r) => this.disjunctive(r, pos)), k);
      case 'tryRankFirst': {
        const d = this.disjunctive(args[0], pos);
        return this.tryRankFirst(d, this.taskIndex(d, args[1], pos), k);
      }
      case 'assignAlternatives': {
        const vars: number[] = [];
        for (const byAlt of this.p.selections.values()) {
          for (const [alt, sel] of byAlt) if (args.length === 0 || args.includes(alt)) vars.push(...sel.map((v) => v.id));
        }
        return this.label(vars, false, k);
      }
    }
    fail(`unknown search instruction ${fn}`, pos);
  }

  private varOf(v: Value, pos: SourcePos): number {
    if (v instanceof DVar) return v.id;
    if (v instanceof Activity) return v.start.id;
    if (typeof v === 'number') return this.b.constant(v);
    if (v instanceof LinExpr) return this.b.varOf(this.flat.atom(v));
    fail(`cannot label a ${typeName(v)}`, pos);
  }
}

/** Leaves of arrays / sets / tuples. */
function collect(v: Value): Value[] {
  if (v instanceof OplArray || v instanceof RawArray) return v.items.flatMap(collect);
  if (v instanceof OplTuple) return v.values.flatMap(collect);
  const elems = typeof v === 'object' && v !== null && !(v instanceof DVar) ? elementsOf(v) : null;
  if (elems) return elems.flatMap(collect);
  return [v];
}
