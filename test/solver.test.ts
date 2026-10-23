import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import type { LinearProgram, Row } from '../src/solver/lp.js';
import { solveMIP } from '../src/solver/mip.js';
import { solveLP } from '../src/solver/simplex.js';

const INF = Infinity;

function lp(objective: number[], lower: number[], upper: number[], rows: Row[], integer: number[] = []): LinearProgram {
  return {
    numVars: objective.length,
    objective: Float64Array.from(objective),
    objConstant: 0,
    lower: Float64Array.from(lower),
    upper: Float64Array.from(upper),
    integer: Uint8Array.from(objective.map((_, j) => integer[j] ?? 0)),
    rows,
  };
}

const row = (index: number[], value: number[], lower: number, upper: number): Row => ({ index, value, lower, upper });

function close(a: number, b: number) {
  assert.ok(Math.abs(a - b) < 1e-9, `${a} != ${b}`);
}

describe('simplex', () => {
  it('reports duals as d(objective)/d(bound)', () => {
    // min x + 2y  s.t.  x + y = 10,  x <= 4
    const r = solveLP(lp([1, 2], [0, 0], [INF, INF], [row([0, 1], [1, 1], 10, 10), row([0], [1], -INF, 4)]));
    assert.equal(r.status, 'optimal');
    close(r.objective, 16);
    assert.deepEqual([...r.x], [4, 6]);
    close(r.duals[0], 2);
    close(r.duals[1], -1);
  });

  it('handles free variables and >= rows', () => {
    // min x - y  s.t.  x - y >= -3, y <= 5, x free, y free
    const r = solveLP(lp([1, -1], [-INF, -INF], [INF, INF], [row([0, 1], [1, -1], -3, INF), row([1], [1], -INF, 5)]));
    assert.equal(r.status, 'optimal');
    close(r.objective, -3);
    close(r.duals[0], 1);
  });

  it('detects infeasible and unbounded problems', () => {
    assert.equal(solveLP(lp([1], [0], [INF], [row([0], [1], 5, 3)])).status, 'infeasible');
    assert.equal(solveLP(lp([1, 1], [0, 0], [INF, INF], [row([0, 1], [1, 1], -INF, -1)])).status, 'infeasible');
    assert.equal(solveLP(lp([-1], [0], [INF], [])).status, 'unbounded');
    assert.equal(solveLP(lp([-1, -1], [0, 0], [INF, INF], [row([0, 1], [1, -1], -INF, 1)])).status, 'unbounded');
  });

  it('survives degenerate problems', () => {
    // A classic cycling example for Dantzig's rule without anti-cycling (Beale).
    const r = solveLP(lp(
      [-0.75, 150, -0.02, 6],
      [0, 0, 0, 0],
      [INF, INF, INF, INF],
      [
        row([0, 1, 2, 3], [0.25, -60, -0.04, 9], -INF, 0),
        row([0, 1, 2, 3], [0.5, -90, -0.02, 3], -INF, 0),
        row([2], [1], -INF, 1),
      ],
    ));
    assert.equal(r.status, 'optimal');
    close(r.objective, -0.05);
  });
});

describe('branch and bound', () => {
  it('solves a small knapsack with both node selections', () => {
    // max 5a + 4b + 3c  s.t.  2a + 3b + c <= 5, 4a + b + 2c <= 11, 3a + 4b + 2c <= 8, binaries
    const p = lp([-5, -4, -3], [0, 0, 0], [1, 1, 1], [
      row([0, 1, 2], [2, 3, 1], -INF, 5),
      row([0, 1, 2], [4, 1, 2], -INF, 11),
      row([0, 1, 2], [3, 4, 2], -INF, 8),
    ], [1, 1, 1]);
    for (const nodeSelection of [0, 1]) {
      const r = solveMIP(p, { nodeSelection });
      assert.equal(r.status, 'optimal');
      close(r.objective, -9);
      assert.deepEqual([...r.x], [1, 1, 0]);
    }
  });

  it('proves integer infeasibility', () => {
    const r = solveMIP(lp([1], [0], [10], [row([0], [2], 3, 3)], [1]));
    assert.equal(r.status, 'infeasible');
  });
});
