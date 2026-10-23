import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { describe, it } from 'node:test';
import { OplError } from '../src/errors.js';
import { ModelInstance } from '../src/model.js';
import { parseData, parseModel, parseScript } from '../src/parser.js';
import { ScriptRunner } from '../src/script.js';

function solve(mod: string, dat = '') {
  const lines: string[] = [];
  const m = new ModelInstance(parseModel(mod, 'test.mod'), dat ? [parseData(dat, 'test.dat')] : [], {
    baseDir: '.',
    out: (l) => lines.push(l),
    warn: () => {},
  });
  m.initData();
  const info = m.hasObjective ? m.solve() : null;
  m.postProcess();
  return { m, info, lines };
}

function throwsAt(fn: () => unknown, message: RegExp, line: number) {
  assert.throws(fn, (e: unknown) => {
    assert.ok(e instanceof OplError, String(e));
    assert.match(e.message, message);
    assert.equal(e.pos?.line, line);
    return true;
  });
}

describe('data and expressions', () => {
  it('evaluates aggregates, generic arrays and operators', () => {
    const { lines } = solve(`
      range R 1..4;
      int fact = prod(i in R) i;
      int pairs = sum(i, j in R : i < j) 1;
      int dm = 17 div 5 + 17 mod 5;
      float m = max(2.5, minl(7, 3));
      string s = "a" + "b";
      int t = (3 > 2) ? 10 : 20;
      int sq[i in R] = i * i;
      {int} odd = {i | i in R : i mod 2 = 1};
      {int} u = odd union {8};
      display fact, pairs, dm, m, s, t, sq[3], odd, u, card(u), ord(u, 8), last(u);
    `);
    assert.deepEqual(lines, [
      'fact = 24', 'pairs = 6', 'dm = 5', 'm = 3.0000', 's = "ab"', 't = 10', 'sq[3] = 9',
      'odd = {1 3}', 'u = {1 3 8}', 'card(u) = 3', 'ord(u, 8) = 2', 'last(u) = 8',
    ]);
  });

  it('reads enums, structs with array fields and indexed data', () => {
    const { lines, m } = solve(
      `
      enum Nutr ...;
      struct Food { float cost; float content[Nutr]; int maxQty; };
      {string} Names = ...;
      Food food[Names] = ...;
      display food;
      display(n in Nutr) sum(f in Names) food[f].content[n];
    `,
      `
      Nutr = { cal prot };
      Names = { "bread", "milk" };
      food = #[
        "bread": #< cost: 2, content: [ 300 8 ], maxQty: 10 >#
        "milk": < 1.5, [ 150, 8 ], 4 >
      ]#;
    `,
    );
    assert.equal(m.hasObjective, false);
    assert.deepEqual(lines, [
      'food["bread"] = <2.0000, [300.0000 8.0000], 10>',
      'food["milk"] = <1.5000, [150.0000 8.0000], 4>',
      'sum(f in Names) food[f].content[cal] = 450.0000',
      'sum(f in Names) food[f].content[prot] = 16.0000',
    ]);
  });

  it('reports data errors with their position', () => {
    throwsAt(() => solve('int a[1..3] = [1, 2];'), /expected 3 array element/, 1);
    throwsAt(() => solve('\nint a = b;'), /unknown identifier 'b'/, 2);
    throwsAt(() => solve('enum E {x, y};\nE e = z;'), /unknown identifier 'z'/, 2);
    throwsAt(() => solve('enum E ...;\nE e = ...;', 'E = {x y};\ne = w;'), /w is not a value of enum E/, 2);
    throwsAt(() => solve('int+ n = -1;'), /non-negative/, 1);
    throwsAt(() => solve('int n = ...;'), /no data given for 'n'/, 1);
    throwsAt(() => solve('int n = 3\nint m = 4;'), /expected ';'/, 2);
  });
});

describe('models', () => {
  it('solves a sparse transportation model with tuple patterns, labels and if', () => {
    const { info, lines } = solve(
      `
      enum Cities ...;
      {string} Plants = ...;
      struct Route { string p; Cities c; float cost; };
      {Route} routes = ...;
      float supply[Plants] = ...;
      float demand[Cities] = ...;
      {Cities} east = {boston, newyork};
      var float+ ship[routes] in 0..1000;
      var float+ slack;
      constraint cap[Plants];
      minimize sum(r in routes) r.cost * ship[r] + 100 * slack
      subject to {
        forall(p in Plants)
          cap[p]: 0 <= sum(<p2, c, k> in routes : p2 = p) ship[<p2, c, k>] <= supply[p];
        forall(c in Cities)
          if (c in east) sum(r in routes : r.c = c) ship[r] + slack >= demand[c];
          else sum(r in routes : r.c = c) ship[r] >= demand[c];
        total: sum(r in routes) ship[r] = sum(c in Cities) demand[c];
      };
      display(r in routes : ship[r] > 0) ship[r];
      display(p in Plants) cap[p].slack;
    `,
      `
      Cities = { boston newyork chicago };
      Plants = { "p1", "p2" };
      routes = { <"p1", boston, 3.5>, <"p1", chicago, 2>, <"p2", newyork, 4>, <"p2", boston, 5>, <"p2", chicago, 1.25> };
      supply = #[ "p1": 300, "p2": 500 ]#;
      demand = [ 250, 200, 150 ];
    `,
    );
    assert.equal(info?.status, 'optimal');
    assert.equal(info?.objective, 1862.5);
    assert.deepEqual(lines, [
      'ship[<"p1", boston, 3.5>] = 250.0000',
      'ship[<"p2", newyork, 4>] = 200.0000',
      'ship[<"p2", chicago, 1.25>] = 150.0000',
      'cap["p1"].slack = 50.0000',
      'cap["p2"].slack = 150.0000',
    ]);
  });

  it('gives float variables free bounds and float+ variables zero lower bounds', () => {
    assert.equal(solve('var float x;\nminimize x subject to x >= -5;').info?.objective, -5);
    assert.equal(solve('var float+ x;\nminimize x subject to x >= -5;').info?.objective, 0);
    assert.equal(solve('var int x in -3..7;\nmaximize x subject to x <= 100;').info?.objective, 7);
  });

  it('reports infeasible and unbounded models', () => {
    assert.equal(solve('var int x in 0..10;\nminimize x subject to { 2*x = 3; };').info?.status, 'infeasible');
    assert.equal(solve('var float+ x, y;\nmaximize x + y subject to { x - y <= 1; };').info?.status, 'unbounded');
  });

  it('rejects non-linear constraints and unindexed labels in forall', () => {
    throwsAt(() => solve('var float x[1..2];\nminimize x[1]\nsubject to {\n  x[1] * x[2] <= 4;\n};'), /non-linear/, 4);
    throwsAt(() => solve('var float x[1..2];\nminimize x[1] subject to {\n forall(i in 1..2) c: x[i] >= 0;\n};'), /must be indexed/, 3);
    throwsAt(() => solve('var float x;\nminimize x subject to x < 3;'), /not allowed in a linear constraint/, 2);
  });
});

describe('OPLScript', () => {
  it('runs loops, edits model data in editMode and writes files', () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'opl-script-'));
    fs.writeFileSync(path.join(dir, 'm.mod'), 'float cap = ...;\nvar float+ x;\nmaximize 2 * x subject to x <= cap;\n');
    fs.writeFileSync(path.join(dir, 'm.dat'), 'cap = 1;\n');
    const script = `
      Model m("m.mod", "m.dat") editMode;
      ofile f("out.txt");
      int k := 0;
      while (k < 3) {
        m.cap := m.cap + 1;
        if (m.solve()) f << k << " " << m.objectiveValue() << " " << m.x << endl;
        k := k + 1;
      }
      repeat k := k - 1; until k <= 0;
      cout << "k=" << k << endl;
      f.close();
    `;
    let out = '';
    new ScriptRunner(parseScript(script, path.join(dir, 's.osc')), { baseDir: dir, write: (t) => (out += t) }).run();
    assert.equal(out, 'k=0\n');
    assert.equal(fs.readFileSync(path.join(dir, 'out.txt'), 'utf8'), '0 4.000000 2.000000\n1 6.000000 3.000000\n2 8.000000 4.000000\n');

    const locked = 'Model m("m.mod", "m.dat");\nm.cap := 5;\n';
    assert.throws(
      () => new ScriptRunner(parseScript(locked, path.join(dir, 'l.osc')), { baseDir: dir }).run(),
      /must be declared with editMode/,
    );
  });
});
