import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { createRequire } from 'node:module';
import * as os from 'node:os';
import * as path from 'node:path';
import { describe, it } from 'node:test';
import { Activity } from '../src/cp/terms.js';
import { DVar } from '../src/linear.js';
import { ModelInstance, type ModelOptions } from '../src/model.js';
import { parseModel, parseScript } from '../src/parser.js';
import { runFile } from '../src/runner.js';
import { ScriptRunner } from '../src/script.js';
import { OplArray, type Value } from '../src/values.js';

function solve(mod: string, options: Partial<ModelOptions> = {}) {
  const lines: string[] = [];
  const m = new ModelInstance(parseModel(mod, 'test.mod'), [], { baseDir: '.', out: (l) => lines.push(l), warn: () => {}, ...options });
  m.initData();
  const info = m.solve();
  m.postProcess();
  return { m, info, lines };
}

function values(v: Value | undefined): (number | string)[] {
  assert.ok(v instanceof OplArray);
  return v.items.map((x) => (x instanceof DVar ? (x.enumType ? x.enumType.values[x.value] : x.value) : (x as number)));
}

const QUEENS = `
  int n = 8;
  range Domain 1..n;
  var Domain queen[Domain];
  solve {
    alldifferent(queen);
    alldifferent(all(i in Domain) queen[i] + i);
    alldifferent(all(i in Domain) queen[i] - i);
  };`;

const MAP = `
  enum Country {Belgium, Denmark, France, Germany, Netherlands, Luxembourg};
  enum Colors {blue, red, yellow, gray};
  var Colors color[Country];
  solve {
    color[France] <> color[Belgium]; color[France] <> color[Luxembourg];
    color[France] <> color[Germany]; color[Luxembourg] <> color[Germany];
    color[Luxembourg] <> color[Belgium]; color[Belgium] <> color[Netherlands];
    color[Belgium] <> color[Germany]; color[Germany] <> color[Netherlands];
    color[Germany] <> color[Denmark];
  };`;

const WAREHOUSE_DATA = `
  enum Warehouses {Bonn, Bordeaux, London, Paris, Rome};
  range Stores 0..9;
  int fixed = 30;
  int capacity[Warehouses] = [1, 4, 2, 1, 3];
  int supplyCost[Stores, Warehouses] = [
    [20, 24, 11, 25, 30], [28, 27, 82, 83, 74], [74, 97, 71, 96, 70], [2, 55, 73, 69, 61], [46, 96, 59, 83, 4],
    [42, 22, 29, 67, 59], [1, 5, 73, 59, 56], [10, 73, 13, 43, 96], [93, 35, 63, 85, 46], [47, 65, 55, 71, 95]];`;

const JOBSHOP = `
  range Jobs 1..3;
  range Machines 1..3;
  int machine[Jobs, Machines] = [[1, 2, 3], [2, 1, 3], [2, 3, 1]];
  int dur[Jobs, Machines] = [[3, 2, 2], [2, 1, 4], [4, 3, 1]];
  scheduleHorizon = 100;
  Activity task[j in Jobs, m in Machines](dur[j, m]);
  Activity makespan(0);
  UnaryResource tool[Machines];
  minimize makespan.end
  subject to {
    forall(j in Jobs) {
      forall(m in 1..2) task[j, m] precedes task[j, m + 1];
      task[j, 3] precedes makespan;
    };
    forall(j in Jobs, m in Machines) task[j, m] requires tool[machine[j, m]];
  };`;

describe('constraint programming', () => {
  it('solves n-queens with alldifferent and a user search', () => {
    const search = `search {
      forall(i in Domain ordered by increasing dsize(queen[i]))
        tryall(v in Domain) queen[i] = v;
    };`;
    for (const mod of [QUEENS, QUEENS + search]) {
      const { info, m } = solve(mod);
      assert.equal(info.solver, 'CP');
      assert.equal(info.status, 'optimal');
      assert.deepEqual(values(m.getField('queen')?.value), [1, 5, 8, 6, 3, 7, 2, 4]);
    }
  });

  it('supports forall(ordered i, j in S) and <>', () => {
    const { m } = solve(`
      range D 1..6;
      var D q[D];
      solve { forall(ordered i, j in D) { q[i] <> q[j]; q[i] + i <> q[j] + j; q[i] - i <> q[j] - j; }; };`);
    const q = values(m.getField('q')?.value) as number[];
    for (let i = 0; i < 6; i++) for (let j = i + 1; j < 6; j++) {
      assert.ok(q[i] !== q[j] && q[i] + i !== q[j] + j && q[i] - i !== q[j] - j);
    }
  });

  it('enumerates all solutions of a map colouring with enum variables', () => {
    const { m, info } = solve(MAP, { allSolutions: true });
    assert.equal(info.solutions, 144);
    m.loadSolution(0);
    assert.deepEqual(values(m.getField('color')?.value), ['blue', 'blue', 'red', 'yellow', 'red', 'gray']);
  });

  it('solves SEND + MORE = MONEY', () => {
    const { m } = solve(`
      enum Letters {S, E, N, D, M, O, R, Y};
      var int l[Letters] in 0..9;
      solve {
        alldifferent(l);
        l[S] <> 0; l[M] <> 0;
        1000*l[S] + 100*l[E] + 10*l[N] + l[D] + 1000*l[M] + 100*l[O] + 10*l[R] + l[E]
          = 10000*l[M] + 1000*l[O] + 100*l[N] + 10*l[E] + l[Y];
      };`);
    assert.deepEqual(values(m.getField('l')?.value), [9, 5, 6, 7, 1, 0, 8, 2]);
  });

  it('runs try ... endtry, logical and meta-constraints', () => {
    assert.equal(solve(`var int x in 1..5;\nsolve { x <> 1; };\nsearch { try 2*x - 1 = 11 | x*x - 20 = 5 | x = 3 endtry; };`).m.getField('x')?.value instanceof DVar, true);
    const tryModel = solve(`var int x in 1..5;\nsolve { x <> 1; };\nsearch { try 2*x - 1 = 11 | x*x - 20 = 5 | x = 3 endtry; };`);
    assert.equal((tryModel.m.getField('x')!.value as DVar).value, 5);
    const meta = solve(`
      range R 1..5;
      var int x[R] in 0..3;
      maximize sum(i in R) x[i]
      subject to {
        sum(i in R) (x[i] = 3) = 2;
        x[1] < 2 => x[2] = 0;
        x[1] <= 1;
        not (x[3] = 3 & x[4] = 3);
      };`);
    const x = values(meta.m.getField('x')?.value) as number[];
    assert.equal(x.filter((v) => v === 3).length, 2);
    assert.equal(x[1], 0);
    assert.ok(!(x[2] === 3 && x[3] === 3));
    assert.equal(meta.info.objective, 1 + 0 + 3 + 2 + 3);
  });

  it('posts disjunctions, negated conjunctions and equivalences', () => {
    const run = (c: string) => values(solve(`var int x[1..2] in 0..3;\nmaximize 10 * x[1] + x[2] subject to { ${c} };`).m.getField('x')?.value);
    assert.deepEqual(run('x[1] <= 1 \\/ x[2] <= 1; x[1] >= 2;'), [3, 1]);
    assert.deepEqual(run('not (x[1] = 3 & x[2] = 3);'), [3, 2]);
    assert.deepEqual(run('(x[1] = 3) <=> (x[2] = 0);'), [3, 0]);
    assert.deepEqual(run('x[1] >= 1 || x[2] >= 1; x[1] + x[2] <= 1; x[2] >= x[1];'), [0, 1]);
  });

  it('agrees with the MIP on the warehouse model (CP formulation with regretdmin search)', () => {
    const cp = solve(`${WAREHOUSE_DATA}
      int maxCost = max(s in Stores, w in Warehouses) supplyCost[s, w];
      var int open[Warehouses] in 0..1;
      var Warehouses supplier[Stores];
      var int cost[Stores] in 0..maxCost;
      minimize sum(s in Stores) cost[s] + sum(w in Warehouses) fixed * open[w]
      subject to {
        forall(s in Stores) cost[s] = supplyCost[s, supplier[s]];
        forall(s in Stores) open[supplier[s]] = 1;
        forall(w in Warehouses) sum(s in Stores) (supplier[s] = w) <= capacity[w];
      };
      search {
        forall(s in Stores ordered by decreasing regretdmin(cost[s]))
          tryall(w in Warehouses ordered by increasing supplyCost[s, w]) supplier[s] = w;
      };`);
    const mip = solve(`${WAREHOUSE_DATA}
      var int open[Warehouses] in 0..1;
      var int supply[Stores, Warehouses] in 0..1;
      minimize sum(w in Warehouses) fixed * open[w] + sum(w in Warehouses, s in Stores) supplyCost[s, w] * supply[s, w]
      subject to {
        forall(s in Stores) sum(w in Warehouses) supply[s, w] = 1;
        forall(w in Warehouses, s in Stores) supply[s, w] <= open[w];
        forall(w in Warehouses) sum(s in Stores) supply[s, w] <= capacity[w];
      };`);
    assert.equal(cp.info.solver, 'CP');
    assert.equal(mip.info.solver, 'MIP');
    assert.equal(cp.info.objective, 383);
    assert.equal(mip.info.objective, 383);
  });

  it('finds the optimal 6-mark Golomb ruler', () => {
    const { info } = solve(`
      range R 1..6;
      var int mark[R] in 0..36;
      minimize mark[6]
      subject to {
        mark[1] = 0;
        forall(i in 1..5) mark[i] < mark[i + 1];
        alldifferent(all(i in R, j in R : i < j) mark[j] - mark[i]) onDomain;
      };`);
    assert.equal(info.objective, 17);
  });

  it('solves float constraints by interval propagation', () => {
    const { m } = solve('var float x in 0..10;\nsolve { x * x = 2; };');
    assert.ok(Math.abs((m.getField('x')!.value as DVar).value - Math.SQRT2) < 1e-5);
  });

  it('supports element, abs, div, mod, min and max over variables', () => {
    const { m, info } = solve(`
      int price[1..4] = [7, 3, 9, 4];
      var int i in 1..4;
      var int y in -5..5;
      var int z in 0..20;
      minimize z
      subject to {
        z = price[i] + abs(y) + (y div 2) * 0 + (z mod 3) * 0;
        max(y, 1) >= 3;
        min(i, 3) = 3;
      };`);
    assert.equal(info.objective, 4 + 3);
    assert.equal((m.getField('i')!.value as DVar).value, 4);
  });

  it('divides by integer variables without rounding failures (Egyptian fractions)', () => {
    const { info, m } = solve(`
      using CP;
      int m = 4;
      dvar int+ x[1..m];
      minimize x[m];
      subject to { sum(i in 1..m) 1 / x[i] == 1; allDifferent(x); forall(i in 1..m-1) x[i] < x[i+1]; x[m] <= 50; }`);
    assert.equal(info.objective, 12);
    assert.deepEqual(values(m.getField('x')?.value), [2, 4, 6, 12]);
  });

  it('keeps fractional and irrational coefficients inside abs and max', () => {
    const { info } = solve(`
      {float} r = { sqrt(i) | i in {2, 3, 5} };
      dvar int y[r] in -10..10;
      minimize max(i in r) abs(y[i] * i) + abs(1.5 * y[sqrt(5)]);
      subject to { forall(i in r) y[i] == (i < 1.5 ? 3 : 1); }`, { forceCP: true });
    assert.ok(Math.abs(info.objective! - (3 * Math.SQRT2 + 1.5)) < 1e-6);
  });
});

describe('scheduling', () => {
  it('ranks unary resources with a search procedure (job shop)', () => {
    const rankSearch = `search {
      while not isRanked(tool) do
        select(r in Machines : not isRanked(tool[r]) ordered by increasing nbPossibleFirst(tool[r]))
          select(j in Jobs, m in Machines : machine[j, m] = r & isPossibleFirst(tool[r], task[j, m])
                 ordered by increasing dmin(task[j, m].start))
            tryRankFirst(tool[r], task[j, m]);
      forall(j in Jobs, m in Machines) task[j, m].start = dmin(task[j, m].start);
    };`;
    for (const search of ['', rankSearch, 'search { setTimes(task); };', 'search { rank(tool); setTimes(task); };']) {
      const { info, lines } = solve(JOBSHOP + search + '\ndisplay makespan;');
      assert.equal(info.objective, 12, search);
      assert.deepEqual(lines, ['makespan = [12 -- 0 --> 12]']);
    }
  });

  it('schedules a discrete resource', () => {
    const { info } = solve(`
      scheduleHorizon = 50;
      range T 1..5;
      int d[T] = [4, 3, 5, 2, 3];
      int q[T] = [2, 1, 2, 3, 1];
      Activity a[t in T](d[t]);
      DiscreteResource crew(3);
      var int span in 0..50;
      minimize span
      subject to {
        forall(t in T) a[t] requires(q[t]) crew;
        forall(t in T) a[t].end <= span;
      };`);
    assert.equal(info.objective, 11);
  });

  it('assigns alternative resources (house building with workers)', () => {
    const { info, m } = solve(`
      enum Tasks { masonry, carpentry, plumbing, ceiling, roofing, painting, windows, facade, garden, moving };
      int duration[Tasks] = [7, 3, 8, 3, 1, 2, 1, 2, 1, 1];
      int totalDuration = sum(t in Tasks) duration[t];
      scheduleHorizon = totalDuration;
      enum Workers { joe, jack, jim };
      {Workers} cannotperform[Tasks] = #[
        masonry: { jim }, carpentry: { jack }, plumbing: { joe, jim }, ceiling: { jack }, roofing: { jack },
        painting: { joe }, windows: { jack }, facade: { jim }, garden: {}, moving: { jack } ]#;
      Activity task[t in Tasks](duration[t]);
      var int durationWorkers[Workers] in 0..totalDuration;
      Activity attendance[w in Workers](durationWorkers[w]);
      UnaryResource worker[Workers];
      AlternativeResources s(worker);
      minimize max(w in Workers) durationWorkers[w]
      subject to {
        task[masonry] precedes task[carpentry]; task[masonry] precedes task[plumbing];
        task[masonry] precedes task[ceiling]; task[carpentry] precedes task[roofing];
        task[ceiling] precedes task[painting]; task[roofing] precedes task[windows];
        task[roofing] precedes task[facade]; task[plumbing] precedes task[facade];
        task[roofing] precedes task[garden]; task[plumbing] precedes task[garden];
        task[windows] precedes task[moving]; task[facade] precedes task[moving];
        task[garden] precedes task[moving]; task[painting] precedes task[moving];
        forall(t in Tasks) task[t] requires s;
        forall(t in Tasks) forall(w in cannotperform[t]) not activityHasSelectedResource(task[t], s, worker[w]);
        forall(t in Tasks) forall(w in Workers)
          activityHasSelectedResource(task[t], s, worker[w]) =>
            attendance[w].start <= task[t].start & attendance[w].end >= task[t].end;
      };
      {Workers} who[t in Tasks] = { w | w in Workers : activityHasSelectedResource(task[t], s, worker[w]) };`);
    assert.equal(info.objective, 10);
    const who = m.getField('who')!.value as OplArray;
    const cannot = m.getField('cannotperform')!.value as OplArray;
    who.items.forEach((set, i) => {
      const ws = (set as { elems: Value[] }).elems;
      assert.equal(ws.length, 1);
      assert.ok(!(cannot.items[i] as { elems: Value[] }).elems.includes(ws[0]));
    });
  });
});

const SETUP = `
  using CP;
  range J = 1..6;
  int dur[J] = [3, 2, 4, 2, 3, 1];
  int typ[J] = [0, 1, 2, 0, 1, 2];
  int setup[0..2][0..2] = [[0, 2, 5], [3, 0, 2], [4, 3, 0]];
  int cost[0..2][0..2] = [[0, 7, 1], [2, 0, 9], [6, 3, 0]];
  dvar interval job[j in J] size dur[j];
  dvar sequence mach in job types typ;
  dexpr int setupCost = sum(j in J) cost[typ[j]][typeOfNext(mach, job[j], typ[j], typ[j])];
  minimize staticLex(max(j in J) endOf(job[j]), setupCost);
  subject to { noOverlap(mach, setup); EXTRA }`;

describe('CP Optimizer scheduling', () => {
  it('schedules sequences with setup times and typeOfNext (as brute force does)', () => {
    const free = solve(SETUP.replace('EXTRA', ''));
    assert.equal(free.info.objective, 19);
    assert.equal(free.m.fieldValue('setupCost'), 16);
    const ordered = solve(SETUP.replace('EXTRA', 'first(mach, job[3]); prev(mach, job[2], job[5]); before(mach, job[6], job[1]); last(mach, job[4]);'));
    assert.equal(ordered.info.objective, 21);
    assert.equal(ordered.m.fieldValue('setupCost'), 5);
  });

  it('supports alternative, span and synchronize', () => {
    const alt = solve(`
      using CP;
      range J = 1..4; range M = 1..2;
      int d[J] = [4, 3, 3, 2];
      dvar interval job[j in J];
      dvar interval mode[j in J][m in M] optional size d[j] * m;
      minimize max(j in J) endOf(job[j]);
      subject to {
        forall(j in J) alternative(job[j], all(m in M) mode[j][m]);
        forall(m in M) noOverlap(all(j in J) mode[j][m]);
      }`);
    assert.equal(alt.info.objective, 8);
    const span = solve(`
      using CP;
      dvar interval a size 3; dvar interval b size 4; dvar interval c optional size 10;
      dvar interval all;
      minimize endOf(all);
      subject to { span(all, [a, b, c]); endBeforeStart(a, b); startOf(a) >= 2; synchronize(b, [c]); }`);
    assert.equal(span.info.objective, 9);
    assert.equal((span.m.getField('c')!.value as Activity).presence!.value, 0);
  });

  it('follows calendars: intensity, forbidExtent, breakable activities and transition times', () => {
    const cal = solve(`
      using CP;
      stepFunction workdays = stepwise { 100 -> 5; 0 -> 7; 100 -> 12; 0 -> 14; 100 };
      dvar interval t size 6 intensity workdays;
      dvar interval u size 2;
      minimize endOf(u);
      subject to { startOf(t) == 3; forbidExtent(u, workdays); endBeforeStart(t, u); }`);
    assert.equal((cal.m.getField('t')!.value as Activity).end.value, 11);
    assert.equal(cal.info.objective, 16);
    const brk = solve(`
      scheduleHorizon = 60;
      Activity a(8) breakable;
      Activity b(4);
      UnaryResource m;
      minimize b.end
      subject to { addPeriodicBreak(m, 5, 2, 7, 60); a requires m; b requires m; a precedes b; };`);
    assert.equal((brk.m.getField('a')!.value as Activity).end.value, 10);
    assert.equal(brk.info.objective, 18);
    const trans = solve(`
      enum Colours { red, blue };
      int setupTime[Colours, Colours] = [[0, 5], [5, 0]];
      scheduleHorizon = 100;
      Activity p1(3) transitionType red;
      Activity p2(3) transitionType blue;
      Activity p3(3) transitionType red;
      UnaryResource press(setupTime);
      var int makespan in 0..100;
      minimize makespan
      subject to { p1 requires press; p2 requires press; p3 requires press; p1.end <= makespan; p2.end <= makespan; p3.end <= makespan; };`);
    assert.equal(trans.info.objective, 14);
  });

  it('proves the ft06 job shop optimum (55) with interval variables', () => {
    const src = fs.readFileSync(path.join(import.meta.dirname, '..', '..', 'web', 'examples', 'jobshop.mod'), 'utf8');
    const { info } = solve(src, { timeLimit: 30 });
    assert.equal(info.status, 'optimal');
    assert.equal(info.objective, 55);
  });

  it('runs every playground example', () => {
    const dir = path.join(import.meta.dirname, '..', '..', 'web', 'examples');
    const manifest = JSON.parse(fs.readFileSync(path.join(dir, 'manifest.json'), 'utf8')) as { examples: { main: string; files: string[]; data: string[] }[] };
    for (const ex of manifest.examples) {
      const main = ex.files.find((f) => f.endsWith(ex.main));
      if (!main?.startsWith('web/examples/')) continue;
      const root = path.join(import.meta.dirname, '..', '..');
      const result = runFile(path.join(root, main), ex.data.map((d) => path.join(dir, d)), { write: () => {}, warn: () => {}, timeLimit: 30 });
      if (result.solve) assert.ok(['optimal', 'feasible'].includes(result.solve.status), `${ex.main}: ${result.solve.status}`);
    }
  });
});

describe('CP Optimizer functions', () => {
  it('orders sequences by rank, with transition distances between neighbours only for isDirect', () => {
    const seq = (direct: string) => `
      using CP;
      tuple triplet { int s1; int s2; int d; };
      {triplet} D = {<0, 1, 1>, <1, 2, 1>, <0, 2, 10>};
      dvar interval a[1..3] size 1;
      dvar sequence s in a types [0, 1, 2];
      minimize max(i in 1..3) endOf(a[i]);
      subject to { noOverlap(s, D${direct}); first(s, a[1]); last(s, a[3]); }`;
    assert.equal(solve(seq(', true')).info.objective, 5);
    assert.equal(solve(seq('')).info.objective, 12);
    // Without noOverlap the order says nothing about time.
    const free = solve(`
      using CP;
      dvar interval a[1..3] size 2;
      dvar sequence s in a;
      minimize max(i in 1..3) endOf(a[i]);
      subject to { before(s, a[3], a[1]); prev(s, a[1], a[2]); }`);
    assert.equal(free.info.objective, 2);
  });

  it('presolves integer programs (fixed columns, singleton rows)', () => {
    const { info } = solve(`
      dvar int x in 0..10; dvar int y in 0..10; dvar int z in 0..10;
      maximize x + 2 * y + 3 * z;
      subject to { x == 3; 2 * y <= 9; x + y + z <= 12; z <= 7.5; }`);
    assert.equal(info.objective, 28);
  });

  it('bounds cumul functions: steps, variable heights, alwaysIn and heights at start and end', () => {
    const reservoir = solve(`
      using CP;
      dvar interval prod[1..3] size 2;
      dvar interval cons[1..3] size 1;
      cumulFunction level = step(0, 2) + sum(i in 1..3) stepAtEnd(prod[i], 3) - sum(i in 1..3) stepAtStart(cons[i], 3);
      minimize max(i in 1..3) endOf(cons[i]);
      subject to { level <= 6; noOverlap(prod); }`);
    assert.equal(reservoir.info.objective, 7);
    const heights = solve(`
      using CP;
      dvar interval a[1..3] size 4;
      cumulFunction f = sum(i in 1..3) pulse(a[i], 1, 3);
      maximize sum(i in 1..3) heightAtStart(a[i], f);
      subject to { f <= 5; alwaysIn(f, 0, 10, 2, 5); forall(i in 1..3) endOf(a[i]) <= 12; }`);
    assert.equal(heights.info.objective, 9);
    const doc = solve(`
      using CP;
      dvar interval a size 3;
      dvar interval b size 2;
      cumulFunction f = step(0, 100) + pulse(a, 3) + pulse(a, 2) - stepAtEnd(a, 1) + stepAtStart(b, 2) - stepAtEnd(b, 3);
      minimize endOf(b);
      subject to { startOf(a) == 1; startOf(b) == 5; }
      int hs[1..4] = [heightAtStart(a, f), heightAtEnd(a, f), heightAtStart(b, f), heightAtEnd(b, f)];
      int v[t in 0..8] = cumulFunctionValue(f, t);
      int n = numberOfSegments(f);
      int sv[i in 0..n-1] = segmentValue(f, i);
      execute { writeln(hs, v, sv); }`);
    assert.equal(doc.lines.join(''), '[5 -1 2 -1][100 105 105 105 99 101 101 98 98][0 100 105 99 101 98]');
  });

  it('keeps state functions: one segment per window, alignment and transition distances', () => {
    const { info, lines } = solve(`
      using CP;
      tuple triplet { int s1; int s2; int d; };
      {triplet} M = {<0, 1, 2>, <1, 0, 2>};
      dvar interval a size 3;
      dvar interval b size 3;
      dvar interval c size 2;
      stateFunction f with M;
      minimize max(endOf(a), endOf(b), endOf(c));
      subject to { alwaysEqual(f, a, 0, true, true); alwaysEqual(f, b, 1); alwaysEqual(f, c, 0, true, true); alwaysNoState(f, 20, 30); }
      int n = numberOfSegments(f);
      int vals[i in 0..n-1] = segmentValue(f, i);
      int at6 = stateFunctionValue(f, 6);
      execute { writeln(vals, at6); }`);
    // a and c cannot share a segment (both aligned, sizes differ): back to back, then b after the transition.
    assert.equal(info.objective, 10);
    assert.equal(lines.join(''), '[-1 0 0 -1 1 -1]-1');
  });

  it('evaluates functions of intervals, overlap lengths, isomorphism and equal sequences', () => {
    const { info, lines } = solve(`
      using CP;
      pwlFunction cost = piecewise{ 0 -> 4; 2 -> 10; 0 } (4, 0);
      stepFunction speed = stepwise{ 1 -> 3; 2 -> 6; 3 };
      dvar interval a in 0..20 size 3;
      dvar interval b optional in 0..20 size 2;
      dvar interval c in 0..20 size 4;
      dvar interval d[1..2] size 3;
      dvar interval e[1..2] optional size 3;
      dvar int m[1..2] in -1..2;
      dvar sequence s1 in all(i in 1..2) d[i];
      dvar sequence s2 in all(i in 1..2) e[i];
      maximize startEval(a, cost) + 10 * presenceOf(b) - endEval(b, speed, 7) + overlapLength(a, c) + overlapLength(a, 2, 5);
      subject to {
        startOf(c) == 4; presenceOf(b) == 1; startOf(b) >= 1;
        isomorphism(d, e, m, -1); noOverlap(s1); sameSequence(s1, s2); startOf(d[1]) >= 3;
      }
      execute { writeln(m, " ", e[1].start, " ", e[2].start); }`);
    assert.equal(info.objective, 20);
    assert.equal(lines.join(''), '[1 2] 3 6');
  });

  it('solves staticLexFull with priorities, weights and tolerances', () => {
    const { info, lines } = solve(`
      dvar int x in 0..10; dvar int y in 0..10; dvar int z in 0..10;
      dexpr int cost = 3 * x + 2 * y + z;
      dexpr int time = 20 - x - y;
      dexpr int risk = z - y;
      minimize staticLexFull([cost, time, risk], [1, 1, 1], [2, 1, 1], [0, 0, 0], [0.5, 0, 0]);
      subject to { x + y + z >= 6; y <= 4; }
      execute { writeln(cost, " ", time + risk); }`);
    assert.equal(info.objective, 6);
    assert.equal(lines.join(''), '9 17');
  });

  it('constrains lex / strictLex and minimizes a standard deviation', () => {
    const { info } = solve(`
      using CP;
      dvar int x[1..4] in 0..10;
      minimize standardDeviation(x);
      subject to { sum(i in 1..4) x[i] == 10; strictLex(x, [3, 3, 3, 3]); strong(x); }`);
    assert.ok(Math.abs(info.objective - 0.5) < 1e-6);
    const consts = solve(`
      float a = log(100); float b = lg(128); float c = ln(1); float d = distToInt(-2.5);
      int i = intValue("-2"); int m = matchAt("Monday", "day"); float sdv = standardDeviation([2, 4, 4, 4, 5, 5, 7, 9]);
      int lx = lex([1, 2, 3], [1, 2, 4]); int slx = strictLex([1, 2, 3], [1, 2, 3]);
      execute { writeln(a, " ", b, " ", c, " ", d, " ", i, " ", m, " ", sdv, " ", lx, " ", slx); }`);
    assert.equal(consts.lines.join(''), '2 7 0 0.5 -2 3 2 1 0');
  });
});

describe('OPLScript and databases', () => {
  it('enumerates solutions with nextSolution()', () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'opl-cp-'));
    fs.writeFileSync(path.join(dir, 'map.mod'), MAP);
    let out = '';
    const script = 'Model m("map.mod");\nint k := 0;\nif (m.solve()) { k := 1; while (m.nextSolution()) k := k + 1; }\ncout << k << endl;';
    new ScriptRunner(parseScript(script, path.join(dir, 's.osc')), { baseDir: dir, write: (t) => (out += t) }).run();
    assert.equal(out, '144\n');
  });

  it('reads with DBread and writes with DBupdate (sqlite)', () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'opl-db-'));
    const { DatabaseSync } = createRequire(import.meta.url)('node:sqlite') as typeof import('node:sqlite');
    const db = new DatabaseSync(path.join(dir, 'data.db'));
    db.exec("create table ITEMS (name text, w int); insert into ITEMS values ('a', 3), ('b', 5); create table RESULT (name text, qty int)");
    const { info } = solve(
      `DBconnection db("sqlite", "data.db");
      struct Item { string name; int w; };
      {Item} items from DBread(db, "select name, w from ITEMS order by name");
      var int x[items] in 0..10;
      maximize sum(i in items) i.w * x[i] subject to { sum(i in items) x[i] <= 4; };
      struct Out { string name; int qty; };
      {Out} result = { <i.name, x[i]> | i in items };
      DBupdate(db, "insert into RESULT values (?, ?)")(result);`,
      { baseDir: dir },
    );
    assert.equal(info.objective, 20);
    const rows = db.prepare('select name, qty from RESULT order by name').all().map((r) => ({ ...r }));
    assert.deepEqual(rows, [{ name: 'a', qty: 0 }, { name: 'b', qty: 4 }]);
  });
});
