/**
 * Modern OPL (IBM ILOG CPLEX Optimization Studio): dvar, tuple, dexpr,
 * constraints blocks, labels, execute / main scripts, CP Optimizer
 * constraints and the linearization used for the MIP solver.
 */

import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { describe, it } from 'node:test';
import { DVar } from '../src/linear.js';
import { ModelInstance, type ModelOptions } from '../src/model.js';
import { parseModel } from '../src/parser.js';
import { runFile } from '../src/runner.js';
import { OplArray, type Value } from '../src/values.js';

function solve(mod: string, options: Partial<ModelOptions> = {}) {
  let text = '';
  const m = new ModelInstance(parseModel(mod, 'test.mod'), [], {
    baseDir: '.',
    write: (t) => (text += t),
    warn: () => {},
    ...options,
  });
  m.initData();
  const info = m.solve();
  m.postProcess();
  return { m, info, text };
}

/** Runs a model file the way the command line does (including main blocks). */
function run(mod: string, files: Record<string, string> = {}, data: string[] = []) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'opl-modern-'));
  for (const [name, src] of Object.entries(files)) fs.writeFileSync(path.join(dir, name), src);
  fs.writeFileSync(path.join(dir, 'm.mod'), mod);
  let out = '';
  const r = runFile(path.join(dir, 'm.mod'), data.map((d) => path.join(dir, d)), { stats: false, write: (t) => (out += t), warn: () => {} });
  return { ...r, out, dir };
}

function values(v: Value | undefined): number[] {
  assert.ok(v instanceof OplArray);
  return v.items.map((x) => (x instanceof DVar ? x.value : (x as number)));
}

describe('modern OPL declarations', () => {
  it('gives dvar variables non-negative default bounds', () => {
    assert.equal(solve('dvar float x;\nminimize x;\nsubject to { x >= -5; }').info.objective, 0);
    assert.equal(solve('dvar float x in -10..10;\nminimize x;\nsubject to { x >= -5; }').info.objective, -5);
    assert.equal(solve('dvar int x;\nmaximize -x;\nsubject to { }').info.objective, 0);
  });

  it('supports tuples with keys, dexpr, boolean variables and constraints blocks', () => {
    const { info, text } = solve(`
      tuple Item { key string name; int weight; int value; }
      {Item} items = {<"a", 3, 4>, <"b", 4, 5>, <"c", 2, 3>};
      tuple Pair { Item first; Item second; }
      {Pair} conflicts = {<"a", "c">};
      dvar boolean take[items];
      dexpr int weight = sum(i in items) i.weight * take[i];
      maximize sum(i in items) i.value * take[i];
      constraints {
        weight <= 6;
        forall(p in conflicts) take[p.first] + take[p.second] <= 1;
      }
      execute { writeln("weight = ", weight); }
    `);
    assert.equal(info.objective, 8);
    assert.equal(text, 'weight = 6\n');
  });

  it('indexes labels inside and in front of forall', () => {
    const { m } = solve(`
      range R = 1..3;
      dvar float x[R];
      minimize sum(i in R) x[i];
      subject to {
        forall(i in R) lower: x[i] >= i;
        upper: forall(i in R) x[i] <= 10;
      }
    `);
    const lower = m.getField('lower')?.value as OplArray;
    assert.deepEqual(lower.items.map((c) => (c as unknown as { dual: number }).dual), [1, 1, 1]);
    assert.ok(m.getField('upper')?.value instanceof OplArray);
  });

  it('builds arrays from comprehensions, including nested ones', () => {
    const { m } = solve(`
      tuple T { int i; int j; float v; }
      {T} data = {<1, 1, 2.5>, <1, 2, 3>, <2, 2, 4>};
      float a[1..2][1..2] = [t.i : [t.j : t.v] | t in data];
      float b[i in 1..2] = sum(t in data : t.i == i) t.v;
      dvar float x;
      minimize x;
      subject to { x >= a[1][1] + a[1][2] + a[2][1] + a[2][2] + b[1]; }
    `);
    assert.equal(m.lastSolve!.objective, 2.5 + 3 + 0 + 4 + 5.5);
  });

  it('selects tuples by bound iterators and by expressions in patterns', () => {
    const { m } = solve(`
      tuple L { int i; int j; int k; }
      {L} links = {<1, 1, 5>, <1, 1, 6>, <1, 2, 7>};
      int n[i in 1..2][j in 1..2] = card({<i, j, k> | <i, j, k> in links});
      assert n[1][1] == 2;
      assert forall(i in 1..2) n[2][i] == 0;
      dvar int x in 0..10;
      minimize x;
      subject to { forall(<i, 2, k> in links) x >= k; }
    `);
    assert.equal(m.lastSolve!.objective, 7);
  });

  it('reads included files and checks assertions', () => {
    const { solve: info } = run('include "data.mod";\ndvar int x in 0..n;\nmaximize x;\nsubject to { }', { 'data.mod': 'int n = 7;\nassert n > 0;' });
    assert.equal(info?.objective, 7);
    assert.throws(() => run('int n = 3;\nassert n > 5;\ndvar int x;\nminimize x;\nsubject to { }'), /assertion failed/);
  });
});

describe('IBM ILOG Script', () => {
  it('runs execute blocks before and after solving', () => {
    const { text } = solve(`
      int n = 3;
      float c[1..n] = [2, 3, 4];
      dvar float+ x[1..n] in 0..10;
      execute PRE { cplex.tilim = 5; var t = 0; for (var i in c) t += c[i]; writeln("sum c = ", t); }
      maximize sum(i in 1..n) c[i] * x[i];
      subject to { cap: sum(i in 1..n) x[i] <= 12; }
      float total;
      execute POST {
        total = 0;
        for (var i = 1; i <= n; i++) total += x[i];
        writeln("x = ", x, ", total = ", total, ", slack = ", cap.slack);
      }
    `);
    assert.equal(text, 'sum c = 9\nx = [0 2 10], total = 12, slack = 0\n');
  });

  it('runs main blocks that solve, change data and build new models', () => {
    const { out } = run(`
      int cap = ...;
      dvar int x in 0..10;
      dvar int y in 0..10;
      maximize x + 2 * y;
      subject to { c: x + y <= cap; }
      main {
        thisOplModel.generate();
        cplex.solve();
        writeln("objective ", cplex.getObjValue(), " y = ", thisOplModel.y);
        var def = thisOplModel.modelDefinition;
        var data = thisOplModel.dataElements;
        for (var k = 1; k <= 2; k++) {
          data.cap = data.cap + 1;
          var m = new IloOplModel(def, cplex);
          m.addDataSource(data);
          m.generate();
          cplex.solve();
          writeln("cap ", data.cap, " objective ", cplex.getObjValue());
        }
      }
    `, { 'm.dat': 'cap = 4;' }, ['m.dat']);
    assert.equal(out, 'objective 8 y = 4\ncap 5 objective 10\ncap 6 objective 12\n');
  });

  it('compares variables by value and reads solutionValue in scripts', () => {
    const { text } = solve(`
      dvar int x in 0..5;
      dvar int y in 0..5;
      maximize x + y;
      subject to { x == y; x <= 3; }
      execute { writeln(x == y, " ", x.solutionValue + y.solutionValue, " ", x.UB); }
    `);
    assert.equal(text, 'true 6 5\n');
  });

  it('enumerates CP solutions with cp.startNewSearch() / cp.next()', () => {
    const { out } = run(`
      using CP;
      dvar int x[1..3] in 1..3;
      constraints { allDifferent(x); x[1] < x[2]; }
      main {
        thisOplModel.generate();
        cp.startNewSearch();
        var n = 0;
        while (cp.next()) { n++; write(thisOplModel.x, " "); }
        writeln(n);
      }
    `);
    assert.equal(out, '[1 2 3] [1 3 2] [2 3 1] 3\n');
  });
});

describe('CP Optimizer constraints and linearization', () => {
  it('supports allowedAssignments, forbiddenAssignments, count, lex and predicates', () => {
    const { m } = solve(`
      using CP;
      tuple P { int a; int b; }
      {P} ok = {<1, 2>, <2, 3>, <3, 1>};
      dvar int x[1..3] in 1..3;
      maximize x[1] * 100 + x[2] * 10 + x[3];
      constraints {
        allowedAssignments(ok, x[1], x[2]);
        forbiddenAssignments({<3, 1>}, x[2], x[3]);
        count(x, 1) == 1;
        lex(all(i in 1..1) x[3], all(i in 1..1) x[2]);
      }
    `);
    assert.deepEqual(values(m.getField('x')?.value), [1, 2, 2]);
    const pred = solve(`
      struct S { int a; int b; };
      {S} pairs = {<1, 3>, <2, 2>};
      predicate p(int a, int b) in pairs;
      var int x in 0..5;
      var int y in 0..5;
      maximize x;
      subject to { p(x, y); };
    `);
    assert.equal(pred.info.objective, 2);
  });

  it('linearizes abs, max, piecewise and logical constraints for the MIP solver', () => {
    const fit = solve(`
      float px[1..4] = [0, 1, 2, 3];
      float py[1..4] = [1, 3, 4, 8];
      dvar float a in -10..10;
      dvar float b in -10..10;
      minimize sum(i in 1..4) abs(b * px[i] + a - py[i]);
      subject to { }
    `);
    assert.notEqual(fit.info.solver, 'CP');
    assert.ok(Math.abs(fit.info.objective - 2) < 1e-6, String(fit.info.objective));
    // open = 1, x = y = 4 (x = 5 is excluded): 3 + max(4, 4) - 4 = 3
    const logic = solve(`
      dvar int x in 0..10;
      dvar float y in 0..10;
      dvar boolean open;
      minimize 3 * open + maxl(x, y) - x;
      subject to {
        x + y >= 8;
        !open => x <= 2;
        x != 5;
      }
    `);
    assert.equal(logic.info.solver, 'MIP');
    assert.ok(Math.abs(logic.info.objective - 3) < 1e-6, String(logic.info.objective));
    const pwl = solve(`
      dvar float q in 0..30;
      minimize piecewise{2 -> 10; 1 -> 20; 3} q - 2.5 * q;
      subject to { }
    `);
    assert.equal(pwl.info.objective, -20);
  });

  it('solves staticLex objectives lexicographically', () => {
    const { m, info } = solve(`
      dvar float x in 0..10;
      dvar float y in 0..10;
      minimize staticLex(-x - y, x);
      subject to { x + y <= 12; }
    `);
    assert.equal(info.objective, -12);
    assert.ok(Math.abs((m.getField('x')!.value as DVar).value - 2) < 1e-6);
  });
});
