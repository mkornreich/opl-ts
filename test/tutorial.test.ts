/**
 * Runs the MIT 1.206J OPL Studio tutorial files (on a temporary copy, since
 * the script and SheetWrite write files) and checks the results.
 */

import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { before, describe, it } from 'node:test';
import * as XLSX from 'xlsx';
import { runFile, type RunOptions } from '../src/runner.js';
import { OplArray, OplSet, type Value } from '../src/values.js';
import { DVar } from '../src/linear.js';

const TUTORIAL = path.resolve(import.meta.dirname, '../../tutorial/files');
let dir = '';

function run(file: string, options: RunOptions = {}) {
  let out = '';
  const warnings: string[] = [];
  const result = runFile(path.join(dir, file), [], {
    stats: false,
    write: (t) => (out += t),
    warn: (m) => warnings.push(m),
    ...options,
  });
  return { out, warnings, ...result };
}

function values(v: Value | undefined): number[] {
  assert.ok(v instanceof OplArray);
  return v.items.map((x) => (x instanceof DVar ? x.value : (x as number)));
}

function close(actual: number, expected: number, eps = 1e-6) {
  assert.ok(Math.abs(actual - expected) <= eps, `${actual} != ${expected}`);
}

before(() => {
  dir = fs.mkdtempSync(path.join(os.tmpdir(), 'opl-tutorial-'));
  for (const f of fs.readdirSync(TUTORIAL)) fs.copyFileSync(path.join(TUTORIAL, f), path.join(dir, f));
});

describe('linear programs', () => {
  for (const file of ['simple0.mod', 'simple3.mod', 'simple4.mod', 'simple4-2.mod', 'simple_project1.prj']) {
    it(file, () => {
      const r = run(file);
      assert.equal(r.solve?.status, 'optimal');
      close(r.solve!.objective, 90038.7 / 13);
      const x = values(r.model!.getField('x')?.value);
      close(x[0], 2004.5 / 13);
      close(x[1], 9999.1 / 13);
      assert.match(r.out, /^Optimal Solution with Objective Value: 6926\.0538\nx\[1\] = 154\.1923\nx\[2\] = 769\.1615\n$/);
    });
  }

  it('simple1.mod: duals and reduced costs', () => {
    const r = run('simple1.mod');
    close(r.solve!.objective, 90000 / 13);
    assert.equal(
      r.out,
      [
        'Optimal Solution with Objective Value: 6923.0769',
        'ct[1].dual = 3.3077',
        'ct[2].dual = 0.0769',
        'ct[3].dual = 0.0000',
        '<x[1],x[1].rc> = <153.8462, 0.0000>',
        '<x[2],x[2].rc> = <769.2308, 0.0000>',
        '<x[3],x[3].rc> = <0.0000, 0.0000>',
        '',
      ].join('\n'),
    );
  });

  it('gas.prj', () => {
    const r = run('gas.prj');
    close(r.solve!.objective, 1800);
    const [gas, chloride] = values(r.model!.getField('production')?.value);
    close(30 * gas + 40 * chloride, 1800);
    assert.ok(gas + chloride <= 50 + 1e-9 && 3 * gas + 4 * chloride <= 180 + 1e-9 && chloride <= 40 + 1e-9);
  });

  it('product.prj: display of tuples with reduced costs', () => {
    const r = run('product.prj');
    close(r.solve!.objective, 372);
    assert.deepEqual(values(r.model!.getField('inside')?.value), [40, 0, 0]);
    assert.deepEqual(values(r.model!.getField('outside')?.value), [60, 200, 300]);
    assert.match(r.out, /<inside\[kluski\],inside\[kluski\]\.rc> = <40\.0000, 0\.0000>/);
    assert.match(r.out, /<inside\[capellini\],inside\[capellini\]\.rc> = <0\.0000, 0\.0600>/);
    assert.match(r.out, /<inside\[fettucine\],inside\[fettucine\]\.rc> = <0\.0000, 0\.0200>/);
  });

  it('simple_project1.prj reads A from the spreadsheet and resolves the Windows path', () => {
    const r = run('simple_project1.prj');
    assert.ok(r.warnings.some((w) => w.includes('simple_project1.xls')));
    const A = r.model!.getField('A')?.value as OplArray;
    assert.deepEqual(A.items.map((row) => (row as OplArray).items), [[3, 2], [1, 5], [0, -1]]);
  });
});

describe('integer programs', () => {
  it('simple2.mod', () => {
    const r = run('simple2.mod');
    assert.equal(r.solve?.status, 'optimal');
    close(r.solve!.objective, 6923);
    assert.deepEqual(values(r.model!.getField('x')?.value), [154, 769]);
  });

  it('covering.prj', () => {
    const r = run('covering.prj');
    assert.equal(r.solve!.objective, 14);
    const crew = r.model!.getField('crew')?.value as OplSet;
    assert.ok(crew instanceof OplSet);
    const cost = values(r.model!.getField('cost')?.value);
    assert.equal(crew.elems.reduce((s: number, c) => s + cost[(c as number) - 1], 0), 14);
    const qualified = r.model!.getField('qualified')?.value as OplArray;
    for (const workers of qualified.items) {
      assert.ok((workers as OplSet).elems.some((w) => crew.indexOf(w) >= 0), 'every task is covered');
    }
    assert.match(r.out, /^crew = \{[\d ]+\}$/m);
  });

  for (const nodeSelection of [0, 1]) {
    it(`knapsack.prj (node selection ${nodeSelection})`, () => {
      const r = run('knapsack.prj', { nodeSelection });
      assert.equal(r.solve?.status, 'optimal');
      assert.equal(r.solve!.objective, 261922);
      // hide_zero = 1 in the project: only the non-zero items are listed.
      assert.equal(
        r.out,
        'Optimal Solution with Objective Value: 261922\ntake[4] = 154\ntake[8] = 913\ntake[9] = 333\ntake[11] = 6499\ntake[12] = 1180\n',
      );
    });
  }
});

describe('OPLScript', () => {
  it('script_simple1.osc reproduces ouput.txt and writes the spreadsheet', () => {
    const expected = fs.readFileSync(path.join(TUTORIAL, 'ouput.txt'), 'utf8').replace(/\r\n/g, '\n');
    fs.rmSync(path.join(dir, 'ouput.txt'));
    const r = run('script_simple1.osc');
    assert.equal(fs.readFileSync(path.join(dir, 'ouput.txt'), 'utf8'), expected);
    const objectives = [...r.out.matchAll(/Objective Function: ([\d.]+)/g)].map((m) => Number(m[1]));
    assert.deepEqual(objectives, [6926.053846, 13509, 20181.666667, 26854.333333]);
    const book = XLSX.read(fs.readFileSync(path.join(dir, 'simple_project1.xls')));
    const sheet = book.Sheets[book.SheetNames[0]];
    close(sheet.G10.v as number, 1000.9 / 3);
    assert.equal(sheet.G11.v, 500);
  });
});
