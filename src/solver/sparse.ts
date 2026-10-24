/**
 * Sparse revised bounded-variable simplex (primal and dual) for large LPs.
 *
 * The column layout is DenseSimplex's: structural columns 0..n-1 and a
 * logical column s_i per row with  a_i . x - s_i = 0  holding the row bounds,
 * so the constraint matrix is A' = [A | -I] and every basic solution has
 * x_B = -B^-1 N x_N.
 *
 * The basis inverse is kept in product form, B^-1 = E_k ... E_1 (-I): the
 * starting basis is the logical one, and every column brought in adds an eta
 * matrix.  Reinversion rebuilds the etas from the basic columns, ordering the
 * row-singleton and column-singleton (triangular) parts so that they cause no
 * fill; only the remaining bump is pivoted numerically.
 *
 * Phase 1 minimises the sum of bound violations of the basic variables (no
 * artificial columns), phase 2 the objective; both price every column
 * (Dantzig) and use a two-pass Harris ratio test.  dual() re-optimises after
 * bound changes from a dual feasible basis, which is what branch and bound
 * does at every node.
 */

import { clean, FEAS_TOL, type SimplexStatus, type Snapshot } from './dense.js';
import { emptyResult, type LinearProgram, type LPResult } from './lp.js';
import { reserve } from './memory.js';

const OPT_TOL = 1e-9;
const PIVOT_TOL = 1e-7;
/** Bound tolerance of the Harris ratio test. */
const HARRIS_TOL = 5e-10;
/** Eta matrices added after a reinversion before the next one. */
const REFACTOR = 100;
const DEGENERATE_LIMIT = 50;
const DROP_TOL = 1e-13;

export class SparseSimplex {
  readonly n: number;
  readonly m: number;
  readonly N: number;
  readonly lb: Float64Array;
  readonly ub: Float64Array;
  readonly x: Float64Array;
  readonly d: Float64Array;
  /** Column at each basis position, and the position of each column (-1 when non-basic). */
  readonly basis: Int32Array;
  private readonly pos: Int32Array;
  private readonly cost: Float64Array;
  iterations = 0;
  /** performance.now() time after which primal / dual stop with 'iteration_limit' (timedOut set). */
  deadline = Infinity;
  timedOut = false;
  /** Infeasible before any pivot (inconsistent bounds). */
  readonly trivial: boolean = false;

  // A by columns and by rows.
  private readonly colStart: Int32Array;
  private readonly colRow: Int32Array;
  private readonly colVal: Float64Array;
  private readonly rowStart: Int32Array;
  private readonly rowCol: Int32Array;
  private readonly rowVal: Float64Array;

  // Eta file: eta k pivots on row etaRow[k] with value etaPiv[k]; its other
  // entries are etaIdx / etaVal[etaStart[k] .. etaStart[k + 1]).
  private etaStart = new Int32Array(1024);
  private etaRow = new Int32Array(1024);
  private etaPiv = new Float64Array(1024);
  private etaIdx: Int32Array;
  private etaVal: Float64Array;
  private numEta = 0;
  /** Etas and their non-zeros right after the last reinversion. */
  private factorEtas = 0;
  private factorNnz = 0;

  /** The real costs while perturbed ones are in use. */
  private savedCost: Float64Array | null = null;
  /** x_B is stale (non-basic values changed). */
  private dirty = false;

  // Work vectors: w (length m) with the list of its non-zeros, a row of B^-1 A' (length N).
  private readonly w: Float64Array;
  private readonly wIdx: Int32Array;
  private wCount = 0;
  private readonly wMark: Uint8Array;
  private readonly y: Float64Array;
  private readonly rowW: Float64Array;
  private readonly rowIdx: Int32Array;
  private readonly rowMark: Uint8Array;
  private rowCount = 0;
  /** Dual steepest-edge weight of each basis position, and work space for its update. */
  private readonly dse: Float64Array;
  private readonly tau: Float64Array;
  /** Ratio-test candidates of the dual simplex. */
  private readonly candJ: Int32Array;
  private readonly candR: Float64Array;

  constructor(
    readonly lp: LinearProgram,
    lower: Float64Array = lp.lower,
    upper: Float64Array = lp.upper,
  ) {
    const n = (this.n = lp.numVars);
    const m = (this.m = lp.rows.length);
    const N = (this.N = n + m);
    let nnz = 0;
    for (const row of lp.rows) nnz += row.index.length;
    reserve(nnz * 24 + N * 64 + m * 48 + 4 * (nnz + m) * 12, `the sparse simplex (${m} rows, ${n} columns, ${nnz} non-zeros)`);

    this.lb = new Float64Array(N);
    this.ub = new Float64Array(N);
    this.x = new Float64Array(N);
    this.d = new Float64Array(N);
    this.cost = new Float64Array(N);
    this.cost.set(lp.objective);
    this.basis = new Int32Array(m);
    this.pos = new Int32Array(N).fill(-1);
    const { lb, ub, x } = this;
    for (let j = 0; j < n; j++) {
      lb[j] = lower[j];
      ub[j] = upper[j];
      if (lower[j] > upper[j] + FEAS_TOL) this.trivial = true;
      x[j] = isFinite(lower[j]) ? lower[j] : isFinite(upper[j]) ? upper[j] : 0;
    }

    this.rowStart = new Int32Array(m + 1);
    this.rowCol = new Int32Array(nnz);
    this.rowVal = new Float64Array(nnz);
    const colCount = new Int32Array(n + 1);
    let k = 0;
    for (let i = 0; i < m; i++) {
      const row = lp.rows[i];
      if (row.lower > row.upper + FEAS_TOL) this.trivial = true;
      lb[n + i] = row.lower;
      ub[n + i] = row.upper;
      this.rowStart[i] = k;
      for (let t = 0; t < row.index.length; t++) {
        if (row.value[t] === 0) continue;
        this.rowCol[k] = row.index[t];
        this.rowVal[k] = row.value[t];
        colCount[row.index[t]]++;
        k++;
      }
    }
    this.rowStart[m] = k;
    this.colStart = new Int32Array(n + 1);
    for (let j = 0; j < n; j++) this.colStart[j + 1] = this.colStart[j] + colCount[j];
    this.colRow = new Int32Array(k);
    this.colVal = new Float64Array(k);
    const fill = this.colStart.slice(0, n);
    for (let i = 0; i < m; i++) {
      for (let t = this.rowStart[i]; t < this.rowStart[i + 1]; t++) {
        const j = this.rowCol[t];
        this.colRow[fill[j]] = i;
        this.colVal[fill[j]++] = this.rowVal[t];
      }
    }

    const cap = Math.max(4 * (k + m), 1 << 16);
    this.etaIdx = new Int32Array(cap);
    this.etaVal = new Float64Array(cap);
    this.w = new Float64Array(m);
    this.wIdx = new Int32Array(m);
    this.wMark = new Uint8Array(m);
    this.y = new Float64Array(m);
    this.rowW = new Float64Array(N);
    this.rowIdx = new Int32Array(N);
    this.rowMark = new Uint8Array(N);
    this.dse = new Float64Array(m).fill(1);
    this.tau = new Float64Array(m);
    this.candJ = new Int32Array(N);
    this.candR = new Float64Array(N);

    for (let i = 0; i < m; i++) {
      this.basis[i] = n + i;
      this.pos[n + i] = i;
    }
    this.computeBasics();
  }

  // ------------------------------------------------------------ basis inverse

  /** Clears w (and its non-zero list). */
  private clearW(): void {
    const { w, wIdx, wMark } = this;
    for (let t = 0; t < this.wCount; t++) {
      w[wIdx[t]] = 0;
      wMark[wIdx[t]] = 0;
    }
    this.wCount = 0;
  }

  private touchW(i: number): void {
    if (!this.wMark[i]) {
      this.wMark[i] = 1;
      this.wIdx[this.wCount++] = i;
    }
  }

  /** Loads column j of A' into w. */
  private loadColumn(j: number): void {
    this.clearW();
    const { w } = this;
    if (j < this.n) {
      for (let t = this.colStart[j]; t < this.colStart[j + 1]; t++) {
        const i = this.colRow[t];
        w[i] = this.colVal[t];
        this.touchW(i);
      }
    } else {
      w[j - this.n] = -1;
      this.touchW(j - this.n);
    }
  }

  /** w += scale * (column j of A'). */
  private addColumn(j: number, scale: number): void {
    const { w } = this;
    if (j < this.n) {
      for (let t = this.colStart[j]; t < this.colStart[j + 1]; t++) {
        const i = this.colRow[t];
        this.touchW(i);
        w[i] += this.colVal[t] * scale;
      }
    } else {
      this.touchW(j - this.n);
      w[j - this.n] -= scale;
    }
  }

  /** w := B^-1 w (keeping the non-zero list). */
  private ftran(): void {
    const { w, etaRow, etaPiv, etaStart, etaIdx, etaVal } = this;
    for (let t = 0; t < this.wCount; t++) w[this.wIdx[t]] = -w[this.wIdx[t]];
    for (let k = 0; k < this.numEta; k++) {
      const p = etaRow[k];
      const wp = w[p];
      if (wp === 0) continue;
      const v = wp / etaPiv[k];
      w[p] = v;
      for (let t = etaStart[k]; t < etaStart[k + 1]; t++) {
        const i = etaIdx[t];
        if (!this.wMark[i]) {
          this.wMark[i] = 1;
          this.wIdx[this.wCount++] = i;
        }
        w[i] -= etaVal[t] * v;
      }
    }
  }

  /** v := B^-1 v for a dense v. */
  private ftranDense(v: Float64Array): void {
    const { etaRow, etaPiv, etaStart, etaIdx, etaVal } = this;
    for (let i = 0; i < this.m; i++) v[i] = -v[i];
    for (let k = 0; k < this.numEta; k++) {
      const p = etaRow[k];
      const vp = v[p];
      if (vp === 0) continue;
      const u = vp / etaPiv[k];
      v[p] = u;
      for (let t = etaStart[k]; t < etaStart[k + 1]; t++) v[etaIdx[t]] -= etaVal[t] * u;
    }
  }

  /** y := B^-T y (y dense, length m). */
  private btran(y: Float64Array): void {
    const { etaRow, etaPiv, etaStart, etaIdx, etaVal } = this;
    for (let k = this.numEta - 1; k >= 0; k--) {
      const p = etaRow[k];
      let s = y[p];
      for (let t = etaStart[k]; t < etaStart[k + 1]; t++) s -= etaVal[t] * y[etaIdx[t]];
      y[p] = s / etaPiv[k];
    }
    for (let i = 0; i < this.m; i++) y[i] = -y[i];
  }

  /** Appends the eta of w (= B^-1 a_q) pivoting on row p. */
  private addEta(p: number): void {
    const { w, wIdx } = this;
    const need = this.etaStart[this.numEta] + this.wCount;
    if (need > this.etaIdx.length) {
      const cap = Math.max(need, this.etaIdx.length * 2);
      reserve(cap * 12, 'the basis factorisation');
      const idx = new Int32Array(cap);
      idx.set(this.etaIdx);
      const val = new Float64Array(cap);
      val.set(this.etaVal);
      this.etaIdx = idx;
      this.etaVal = val;
    }
    if (this.numEta + 2 > this.etaRow.length) {
      const grow = <T extends Int32Array | Float64Array>(a: T): T => {
        const b = new (a.constructor as new (n: number) => T)(a.length * 2);
        b.set(a);
        return b;
      };
      this.etaStart = grow(this.etaStart);
      this.etaRow = grow(this.etaRow);
      this.etaPiv = grow(this.etaPiv);
    }
    const k = this.numEta;
    let at = this.etaStart[k];
    for (let t = 0; t < this.wCount; t++) {
      const i = wIdx[t];
      if (i === p) continue;
      const v = w[i];
      if (v > -DROP_TOL && v < DROP_TOL) continue;
      this.etaIdx[at] = i;
      this.etaVal[at++] = v;
    }
    this.etaRow[k] = p;
    this.etaPiv[k] = w[p];
    this.etaStart[k + 1] = at;
    this.numEta++;
  }

  /**
   * Rebuilds the eta file for the current set of basic columns (positions are
   * reassigned).  Dependent columns are replaced by logical ones and made
   * non-basic; returns false when that happened.
   */
  private reinvert(): boolean {
    const { n, m, basis, pos, colStart, colRow, rowStart, rowCol, dse } = this;
    const weight = new Float64Array(this.N).fill(1);
    for (let i = 0; i < m; i++) weight[basis[i]] = dse[i];
    this.numEta = 0;
    this.etaStart[0] = 0;
    const cols: number[] = [];
    for (let i = 0; i < m; i++) if (basis[i] < n) cols.push(basis[i]);
    // Rows still to be pivoted on: those whose logical column is non-basic.
    const openRow = new Uint8Array(m);
    for (let i = 0; i < m; i++) openRow[i] = pos[n + i] >= 0 ? 0 : 1;
    pos.fill(-1);
    for (let i = 0; i < m; i++) {
      if (!openRow[i]) {
        basis[i] = n + i;
        pos[n + i] = i;
      } else basis[i] = -1;
    }

    // Triangular parts by singleton elimination on the pattern.
    const activeCol = new Uint8Array(n);
    for (const c of cols) activeCol[c] = 1;
    const activeRow = Uint8Array.from(openRow);
    const cCount = new Int32Array(n);
    const rCount = new Int32Array(m);
    for (const c of cols) {
      for (let t = colStart[c]; t < colStart[c + 1]; t++) {
        if (activeRow[colRow[t]]) {
          cCount[c]++;
          rCount[colRow[t]]++;
        }
      }
    }
    const front: number[] = [];
    const frontRow: number[] = [];
    const back: number[] = [];
    const backRow: number[] = [];
    const removeCol = (c: number, queue: number[] | null) => {
      activeCol[c] = 0;
      for (let t = colStart[c]; t < colStart[c + 1]; t++) {
        const r = colRow[t];
        if (activeRow[r] && --rCount[r] === 1 && queue) queue.push(r);
      }
    };
    const removeRow = (r: number, queue: number[] | null) => {
      activeRow[r] = 0;
      for (let t = rowStart[r]; t < rowStart[r + 1]; t++) {
        const c = rowCol[t];
        if (activeCol[c] && --cCount[c] === 1 && queue) queue.push(c);
      }
    };
    const rowQueue: number[] = [];
    for (let i = 0; i < m; i++) if (activeRow[i] && rCount[i] === 1) rowQueue.push(i);
    while (rowQueue.length) {
      const r = rowQueue.pop()!;
      if (!activeRow[r] || rCount[r] !== 1) continue;
      let c = -1;
      for (let t = rowStart[r]; t < rowStart[r + 1]; t++) {
        if (activeCol[rowCol[t]]) {
          c = rowCol[t];
          break;
        }
      }
      if (c < 0) continue;
      front.push(c);
      frontRow.push(r);
      removeCol(c, rowQueue);
      removeRow(r, null);
    }
    const colQueue: number[] = [];
    for (const c of cols) if (activeCol[c] && cCount[c] === 1) colQueue.push(c);
    while (colQueue.length) {
      const c = colQueue.pop()!;
      if (!activeCol[c] || cCount[c] !== 1) continue;
      let r = -1;
      for (let t = colStart[c]; t < colStart[c + 1]; t++) {
        if (activeRow[colRow[t]]) {
          r = colRow[t];
          break;
        }
      }
      if (r < 0) continue;
      back.push(c);
      backRow.push(r);
      removeRow(r, colQueue);
      removeCol(c, null);
    }
    const bump = cols.filter((c) => activeCol[c]).sort((a, b) => cCount[a] - cCount[b]);
    const bumpRow = activeRow;

    const order: number[] = [...front, ...bump];
    const want: number[] = [...frontRow, ...bump.map(() => -1)];
    for (let k = back.length - 1; k >= 0; k--) {
      order.push(back[k]);
      want.push(backRow[k]);
    }
    const dropped: number[] = [];
    const { w } = this;
    for (let k = 0; k < order.length; k++) {
      const c = order[k];
      this.loadColumn(c);
      this.ftran();
      // Triangular columns take their own row unless it is numerically tiny;
      // bump columns (and fallbacks) the largest entry among the bump rows.
      const r = want[k];
      let p = -1;
      let best = 0;
      if (r >= 0 && openRow[r]) {
        let max = 0;
        for (let t = 0; t < this.wCount; t++) {
          const i = this.wIdx[t];
          if (openRow[i] && Math.abs(w[i]) > max) max = Math.abs(w[i]);
        }
        // No fill reaches a triangular column: its entry is the original coefficient.
        if (Math.abs(w[r]) >= 1e-7 * Math.max(1, max)) p = r;
      }
      if (p < 0 && r < 0) {
        // A row outside the bump would break the triangular order of the
        // columns still to come: a bump column without a pivot is dependent.
        for (let t = 0; t < this.wCount; t++) {
          const i = this.wIdx[t];
          if (!openRow[i] || !bumpRow[i]) continue;
          const a = Math.abs(w[i]);
          if (a > best) {
            best = a;
            p = i;
          }
        }
      }
      if (p < 0 || Math.abs(w[p]) < 1e-9) {
        dropped.push(c);
        continue;
      }
      this.addEta(p);
      openRow[p] = 0;
      basis[p] = c;
      pos[c] = p;
    }
    // Rows left open take their logical column: no eta pivots on such a row, so
    // B^-1 (-e_i) = e_i and the column needs no eta of its own.
    for (let i = 0; i < m; i++) {
      if (!openRow[i]) continue;
      basis[i] = n + i;
      pos[n + i] = i;
    }
    this.clearW();
    for (const c of dropped) {
      const { lb, ub, x } = this;
      x[c] = Math.min(Math.max(x[c], lb[c]), ub[c]);
      if (!isFinite(x[c])) x[c] = isFinite(lb[c]) ? lb[c] : isFinite(ub[c]) ? ub[c] : 0;
    }
    for (let i = 0; i < m; i++) dse[i] = weight[basis[i]];
    this.factorEtas = this.numEta;
    this.factorNnz = this.etaStart[this.numEta];
    this.dirty = true;
    return dropped.length === 0;
  }

  private refactorDue(): boolean {
    const k = this.numEta - this.factorEtas;
    return k >= REFACTOR || (k > 10 && this.etaStart[this.numEta] - this.factorNnz > 2 * this.factorNnz + 4 * this.m);
  }

  /** x_B = -B^-1 (N x_N). */
  private computeBasics(): void {
    const { n, m, x, pos, w, colStart, colRow, colVal } = this;
    this.clearW();
    for (let j = 0; j < n; j++) {
      const v = x[j];
      if (v === 0 || pos[j] >= 0) continue;
      for (let t = colStart[j]; t < colStart[j + 1]; t++) {
        const i = colRow[t];
        this.touchW(i);
        w[i] += colVal[t] * v;
      }
    }
    for (let i = 0; i < m; i++) {
      const v = x[n + i];
      if (v === 0 || pos[n + i] >= 0) continue;
      this.touchW(i);
      w[i] -= v;
    }
    this.ftran();
    for (let i = 0; i < m; i++) x[this.basis[i]] = -w[i];
    this.clearW();
    this.dirty = false;
  }

  /** Reduced costs d = c - A'^T y with y = B^-T c_B, for the given costs. */
  private computeReducedCosts(c: Float64Array): void {
    const { n, m, d, y, basis, pos, colStart, colRow, colVal } = this;
    for (let i = 0; i < m; i++) y[i] = c[basis[i]];
    this.btran(y);
    for (let j = 0; j < n; j++) {
      if (pos[j] >= 0) {
        d[j] = 0;
        continue;
      }
      let s = c[j];
      for (let t = colStart[j]; t < colStart[j + 1]; t++) s -= y[colRow[t]] * colVal[t];
      d[j] = s;
    }
    for (let i = 0; i < m; i++) d[n + i] = pos[n + i] >= 0 ? 0 : c[n + i] + y[i];
  }

  /** Row r of B^-1 A' into rowW (non-zeros listed in rowIdx). */
  private computeRow(r: number): void {
    const { n, m, y, rowW, rowIdx, rowMark, rowStart, rowCol, rowVal } = this;
    for (let t = 0; t < this.rowCount; t++) {
      rowW[rowIdx[t]] = 0;
      rowMark[rowIdx[t]] = 0;
    }
    this.rowCount = 0;
    y.fill(0);
    y[r] = 1;
    this.btran(y);
    for (let i = 0; i < m; i++) {
      const v = y[i];
      if (v === 0) continue;
      for (let t = rowStart[i]; t < rowStart[i + 1]; t++) {
        const j = rowCol[t];
        if (!rowMark[j]) {
          rowMark[j] = 1;
          rowIdx[this.rowCount++] = j;
        }
        rowW[j] += v * rowVal[t];
      }
      const s = n + i;
      rowMark[s] = 1;
      rowIdx[this.rowCount++] = s;
      rowW[s] = -v;
    }
  }

  /** Makes column q basic at position r (w holds B^-1 a_q). */
  private pivot(r: number, q: number): void {
    const b = this.basis[r];
    this.addEta(r);
    this.basis[r] = q;
    this.pos[q] = r;
    this.pos[b] = -1;
  }

  /** Checks the clock every 16 iterations. */
  private outOfTime(): boolean {
    if ((this.iterations & 15) !== 0 || performance.now() <= this.deadline) return false;
    this.timedOut = true;
    return true;
  }

  // ------------------------------------------------------------ primal simplex

  private primal(phase1: boolean, maxIterations: number): 'optimal' | 'unbounded' | 'iteration_limit' {
    const { N, m, x, lb, ub, d, basis, pos, w, wIdx } = this;
    const c1 = phase1 ? new Float64Array(N) : this.cost;
    let degenerate = 0;
    let retries = 0;
    for (;;) {
      if (this.iterations >= maxIterations || this.outOfTime()) return 'iteration_limit';
      if (this.refactorDue()) {
        this.reinvert();
        this.computeBasics();
      }
      if (phase1) {
        let any = false;
        for (let i = 0; i < m; i++) {
          const b = basis[i];
          const v = x[b];
          c1[b] = v < lb[b] - FEAS_TOL ? -1 : v > ub[b] + FEAS_TOL ? 1 : 0;
          if (c1[b] !== 0) any = true;
        }
        if (!any) return 'optimal';
      }
      this.computeReducedCosts(c1);
      if (phase1) for (let i = 0; i < m; i++) c1[basis[i]] = 0;
      const bland = degenerate > DEGENERATE_LIMIT;

      let q = -1;
      let dir = 0;
      let best = 0;
      for (let j = 0; j < N; j++) {
        if (pos[j] >= 0 || ub[j] - lb[j] <= FEAS_TOL) continue;
        const dj = d[j];
        let score: number;
        let jdir: number;
        if (dj < -OPT_TOL && x[j] < ub[j] - FEAS_TOL) {
          score = -dj;
          jdir = 1;
        } else if (dj > OPT_TOL && x[j] > lb[j] + FEAS_TOL) {
          score = dj;
          jdir = -1;
        } else continue;
        if (bland) {
          q = j;
          dir = jdir;
          break;
        }
        if (score > best) {
          best = score;
          q = j;
          dir = jdir;
        }
      }
      if (q < 0) return 'optimal';

      this.loadColumn(q);
      this.ftran();
      // Harris pass 1: the largest step with bounds relaxed by HARRIS_TOL.
      const range = dir > 0 ? ub[q] - x[q] : x[q] - lb[q];
      let tMax = range;
      for (let t = 0; t < this.wCount; t++) {
        const i = wIdx[t];
        const a = w[i] * dir;
        if (a > -PIVOT_TOL && a < PIVOT_TOL) continue;
        const b = basis[i];
        const [lo, hi] = this.phaseBounds(b, phase1);
        const ti = a > 0 ? (x[b] - lo + HARRIS_TOL) / a : (hi - x[b] + HARRIS_TOL) / -a;
        if (ti < tMax) tMax = ti;
      }
      // Pass 2: among the rows blocking within that step, the largest pivot.
      let leave = -1;
      let leaveAlpha = 0;
      let leaveValue = 0;
      let step = range;
      if (tMax < range) {
        for (let t = 0; t < this.wCount; t++) {
          const i = wIdx[t];
          const a = w[i] * dir;
          if (a > -PIVOT_TOL && a < PIVOT_TOL) continue;
          const b = basis[i];
          const [lo, hi] = this.phaseBounds(b, phase1);
          let ti = a > 0 ? (x[b] - lo) / a : (hi - x[b]) / -a;
          if (!(ti <= tMax)) continue;
          if (ti < 0) ti = 0;
          const abs = Math.abs(a);
          if (leave < 0 || (bland ? b < basis[leave] : abs > leaveAlpha)) {
            leave = i;
            leaveAlpha = abs;
            leaveValue = a > 0 ? lo : hi;
            step = ti;
          }
        }
      }
      if (!isFinite(step)) {
        if (phase1 && retries++ < 3) {
          // Cannot happen in exact arithmetic: refresh the factorisation.
          this.reinvert();
          this.computeBasics();
          continue;
        }
        this.clearW();
        return 'unbounded';
      }

      this.iterations++;
      degenerate = step <= 1e-12 ? degenerate + 1 : 0;
      if (step > 0) {
        x[q] += dir * step;
        for (let t = 0; t < this.wCount; t++) {
          const i = wIdx[t];
          x[basis[i]] -= w[i] * dir * step;
        }
      }
      if (leave < 0) {
        // Bound flip.
        x[q] = dir > 0 ? ub[q] : lb[q];
        this.clearW();
        continue;
      }
      x[basis[leave]] = leaveValue;
      this.pivot(leave, q);
      this.clearW();
    }
  }

  /** Bounds of basic column b in the ratio test (phase 1 lets violated bounds move towards feasibility). */
  private phaseBounds(b: number, phase1: boolean): [number, number] {
    const { x, lb, ub } = this;
    if (phase1) {
      if (x[b] < lb[b] - FEAS_TOL) return [-Infinity, lb[b]];
      if (x[b] > ub[b] + FEAS_TOL) return [ub[b], Infinity];
    }
    return [lb[b], ub[b]];
  }

  /** Two-phase primal simplex from the current basis. */
  solve(maxIterations = 1000 + 50 * (this.m + this.N)): SimplexStatus {
    if (this.trivial) return 'infeasible';
    if (this.iterations === 0 && this.numEta === 0) {
      const st = this.dualStart(maxIterations);
      if (st) return st;
    }
    if (this.dirty) this.computeBasics();
    const st1 = this.primal(true, maxIterations);
    if (st1 === 'iteration_limit') return st1;
    this.computeBasics();
    if (this.infeasibility() > 1e-7) return 'infeasible';
    const st = this.primal(false, maxIterations);
    if (st === 'optimal') {
      this.computeBasics();
      this.computeReducedCosts(this.cost);
    }
    return st;
  }

  /**
   * From the logical basis, puts every structural column at the bound its
   * cost prefers (a temporary bound of +-BOX when that one is infinite), which
   * makes the basis dual feasible, and runs the dual simplex.  Columns left at
   * a temporary bound are then freed and the primal simplex finishes.  Returns
   * null when the primal two-phase method should be used instead.
   */
  private dualStart(maxIterations: number): SimplexStatus | null {
    const { n, x, lb, ub, cost } = this;
    const BOX = 1e6;
    const boxed: number[] = [];
    const saved: number[] = [];
    for (let j = 0; j < n; j++) {
      const c = cost[j];
      if (c > OPT_TOL) {
        if (!isFinite(lb[j])) {
          boxed.push(j);
          saved.push(lb[j], ub[j]);
          lb[j] = Math.min(-BOX, ub[j]);
        }
        x[j] = lb[j];
      } else if (c < -OPT_TOL) {
        if (!isFinite(ub[j])) {
          boxed.push(j);
          saved.push(lb[j], ub[j]);
          ub[j] = Math.max(BOX, lb[j]);
        }
        x[j] = ub[j];
      }
    }
    const unbox = () => {
      for (let k = 0; k < boxed.length; k++) {
        lb[boxed[k]] = saved[2 * k];
        ub[boxed[k]] = saved[2 * k + 1];
      }
    };
    this.computeBasics();
    this.computeReducedCosts(cost);
    this.perturbCosts();
    const st = this.dualLoop(maxIterations);
    this.unperturbCosts();
    unbox();
    if (st === 'iteration_limit') return st;
    if (st !== 'optimal') {
      // Infeasible with temporary bounds says nothing; start over with the primal.
      if (st === 'infeasible' && boxed.length === 0) return st;
      return null;
    }
    const st2 = this.primal(false, maxIterations);
    if (st2 === 'optimal') {
      this.computeBasics();
      this.computeReducedCosts(cost);
    }
    return st2;
  }

  private infeasibility(): number {
    const { m, x, lb, ub, basis } = this;
    let s = 0;
    for (let i = 0; i < m; i++) {
      const b = basis[i];
      if (x[b] < lb[b]) s += lb[b] - x[b];
      else if (x[b] > ub[b]) s += x[b] - ub[b];
    }
    return s;
  }

  // ------------------------------------------------------------ warm starts

  /** Changes the bounds of structural column j (keeping the basis). */
  setBounds(j: number, lo: number, hi: number): void {
    const { lb, ub, x, d } = this;
    lb[j] = lo;
    ub[j] = hi;
    if (this.pos[j] >= 0) return;
    const old = x[j];
    let v: number;
    if (lo === hi) v = lo;
    else if (d[j] > 0 && isFinite(lo)) v = lo;
    else if (d[j] < 0 && isFinite(hi)) v = hi;
    else v = Math.min(Math.max(old, lo), hi);
    if (!isFinite(v)) v = isFinite(lo) ? lo : isFinite(hi) ? hi : 0;
    if (v === old) return;
    x[j] = v;
    this.dirty = true;
  }

  /**
   * Perturbs the costs of the non-basic columns (towards dual feasibility, so
   * the reduced costs move by the same amounts): dual degenerate problems,
   * where most costs are zero, otherwise stall.
   */
  private perturbCosts(): void {
    const { n, x, lb, ub, d, pos, cost } = this;
    this.savedCost = Float64Array.from(cost);
    let seed = 12345;
    for (let j = 0; j < n; j++) {
      if (pos[j] >= 0 || lb[j] === ub[j]) continue;
      seed = (seed * 1103515245 + 12345) % 2147483648;
      const e = 1e-7 * (1 + Math.abs(cost[j])) * (1 + seed / 2147483648);
      if (x[j] === lb[j]) {
        cost[j] += e;
        d[j] += e;
      } else if (x[j] === ub[j]) {
        cost[j] -= e;
        d[j] -= e;
      }
    }
  }

  private unperturbCosts(): void {
    if (!this.savedCost) return;
    this.cost.set(this.savedCost);
    this.savedCost = null;
    this.computeReducedCosts(this.cost);
  }

  /**
   * Dual simplex: re-optimises after bound changes, starting from a dual
   * feasible basis.  Returns null when the basis is not dual feasible.
   */
  dual(maxIterations = this.iterations + 1000 + 20 * (this.m + this.N)): SimplexStatus | null {
    const st = this.dualLoop(maxIterations);
    if (!this.savedCost) return st;
    // The costs were perturbed: the primal simplex removes what is left.
    this.unperturbCosts();
    if (st !== 'optimal') return st;
    const st2 = this.primal(false, maxIterations);
    if (st2 === 'optimal') {
      this.computeBasics();
      this.computeReducedCosts(this.cost);
    }
    return st2;
  }

  private dualLoop(maxIterations: number): SimplexStatus | null {
    const { N, m, x, lb, ub, d, basis, pos, w, wIdx, rowW, rowIdx, dse } = this;
    if (this.dirty) this.computeBasics();
    for (let j = 0; j < N; j++) {
      if (pos[j] >= 0 || ub[j] - lb[j] <= FEAS_TOL) continue;
      const atLb = x[j] <= lb[j] + FEAS_TOL;
      const atUb = x[j] >= ub[j] - FEAS_TOL;
      if (atLb && d[j] < -1e-7) return null;
      if (atUb && d[j] > 1e-7) return null;
      if (!atLb && !atUb && Math.abs(d[j]) > 1e-7) return null;
    }
    let stall = 0;
    for (;;) {
      if (this.iterations >= maxIterations || this.outOfTime()) return 'iteration_limit';
      if (this.refactorDue()) {
        if (!this.reinvert()) return null;
        this.computeBasics();
        this.computeReducedCosts(this.cost);
      }
      // Leaving row: dual steepest edge (infeasibility^2 / weight).
      let r = -1;
      let worst = 0;
      for (let i = 0; i < m; i++) {
        const b = basis[i];
        const v = x[b];
        const inf = v < lb[b] ? lb[b] - v : v > ub[b] ? v - ub[b] : 0;
        if (inf <= FEAS_TOL * 10 * Math.max(1, Math.abs(v))) continue;
        const score = (inf * inf) / dse[i];
        if (score > worst) {
          worst = score;
          r = i;
        }
      }
      if (r < 0) {
        this.computeBasics();
        return 'optimal';
      }
      const b = basis[r];
      const increase = x[b] < lb[b];
      const target = increase ? lb[b] : ub[b];
      this.computeRow(r);
      // Bound-flipping ratio test: walk the breakpoints |d_j / alpha_j| in
      // increasing order; boxed columns passed on the way flip to their other
      // bound while x_b stays infeasible, the column at the last one enters.
      const { candJ, candR } = this;
      let nc = 0;
      for (let t = 0; t < this.rowCount; t++) {
        const j = rowIdx[t];
        if (pos[j] >= 0 || ub[j] - lb[j] <= FEAS_TOL) continue;
        const a = rowW[j];
        if (a > -PIVOT_TOL && a < PIVOT_TOL) continue;
        const dir = increase ? (a < 0 ? 1 : -1) : a > 0 ? 1 : -1;
        if (dir > 0 && !(x[j] < ub[j] - FEAS_TOL)) continue;
        if (dir < 0 && !(x[j] > lb[j] + FEAS_TOL)) continue;
        candJ[nc] = j;
        candR[nc++] = Math.abs(d[j]) / Math.abs(a);
      }
      if (nc === 0) return 'infeasible';
      if (stall > 30 && !this.savedCost) {
        this.perturbCosts();
        stall = 0;
      }
      const bland = stall > 200;
      let q = -1;
      let bestRatio = Infinity;
      let flips = 0;
      let order: number[] = [];
      if (bland) {
        for (let k = 0; k < nc; k++) {
          if (candR[k] < bestRatio - 1e-12 || (candR[k] <= bestRatio + 1e-12 && candJ[k] < q)) {
            bestRatio = candR[k];
            q = candJ[k];
          }
        }
      } else {
        order = Array.from({ length: nc }, (_, k) => k).sort((u, v) => candR[u] - candR[v]);
        let slope = increase ? lb[b] - x[b] : x[b] - ub[b];
        let at = nc - 1;
        for (let k = 0; k < nc; k++) {
          const j = candJ[order[k]];
          const reduce = Math.abs(rowW[j]) * (ub[j] - lb[j]);
          if (!(slope - reduce >= 0)) {
            at = k;
            break;
          }
          slope -= reduce;
        }
        // Harris: from that breakpoint on, the largest pivot among the ratios
        // within the step allowed by a small reduced-cost tolerance.
        flips = at;
        let bound = Infinity;
        for (let k = at; k < nc && candR[order[k]] <= bound; k++) {
          const j = candJ[order[k]];
          bound = Math.min(bound, (Math.abs(d[j]) + 1e-9) / Math.abs(rowW[j]));
        }
        bestRatio = candR[order[at]];
        q = candJ[order[at]];
        for (let k = at + 1; k < nc && candR[order[k]] <= bound; k++) {
          const j = candJ[order[k]];
          if (Math.abs(rowW[j]) > Math.abs(rowW[q])) {
            q = j;
            bestRatio = candR[order[k]];
          }
        }
      }
      if (flips > 0) {
        this.clearW();
        for (let k = 0; k < flips; k++) {
          const j = candJ[order[k]];
          const to = x[j] <= lb[j] + FEAS_TOL ? ub[j] : lb[j];
          this.addColumn(j, to - x[j]);
          x[j] = to;
        }
        this.ftran();
        for (let t = 0; t < this.wCount; t++) x[basis[wIdx[t]]] -= w[wIdx[t]];
        this.clearW();
      }
      this.loadColumn(q);
      this.ftran();
      const piv = w[r];
      if (Math.abs(piv - rowW[q]) > 1e-7 * Math.max(1, Math.abs(piv)) || Math.abs(piv) < PIVOT_TOL) {
        // The row and the column disagree: refresh the factorisation.
        this.clearW();
        if (this.numEta === this.factorEtas) return null;
        if (!this.reinvert()) return null;
        this.computeBasics();
        this.computeReducedCosts(this.cost);
        continue;
      }
      // Steepest-edge weights: rho_r is still in y; tau = B^-1 rho_r.
      const { y, tau } = this;
      let betaR = 0;
      for (let i = 0; i < m; i++) betaR += y[i] * y[i];
      tau.set(y);
      this.ftranDense(tau);
      for (let t = 0; t < this.wCount; t++) {
        const i = wIdx[t];
        if (i === r) continue;
        const ratio = w[i] / piv;
        if (ratio !== 0) dse[i] = Math.max(dse[i] + ratio * (ratio * betaR - 2 * tau[i]), 1e-8);
      }
      dse[r] = Math.max(betaR / (piv * piv), 1e-8);
      this.iterations++;
      stall = bestRatio <= 1e-12 ? stall + 1 : 0;
      const delta = (target - x[b]) / -piv;
      x[q] += delta;
      for (let t = 0; t < this.wCount; t++) {
        const i = wIdx[t];
        x[basis[i]] -= w[i] * delta;
      }
      x[b] = target;
      const theta = d[q] / rowW[q];
      if (theta !== 0) {
        for (let t = 0; t < this.rowCount; t++) {
          const j = rowIdx[t];
          if (pos[j] < 0) d[j] -= theta * rowW[j];
        }
      }
      d[q] = 0;
      d[b] = -theta;
      this.pivot(r, q);
      this.clearW();
    }
  }

  snapshot(): Snapshot {
    const { N, x, lb, ub, pos } = this;
    const status = new Uint8Array(N);
    const other = new Map<number, number>();
    for (let j = 0; j < N; j++) {
      if (pos[j] >= 0 || x[j] === lb[j]) continue;
      if (x[j] === ub[j]) status[j] = 1;
      else {
        status[j] = 2;
        other.set(j, x[j]);
      }
    }
    return { basis: Int32Array.from(this.basis), status, other };
  }

  /** Re-factorises a saved basis; bounds are kept as they are.  False when it was singular. */
  restore(snap: Snapshot): boolean {
    const { N, x, lb, ub, pos, basis } = this;
    pos.fill(-1);
    basis.set(snap.basis);
    for (let i = 0; i < this.m; i++) pos[basis[i]] = i;
    for (let j = 0; j < N; j++) {
      if (pos[j] >= 0) continue;
      const st = snap.status[j];
      let v = st === 0 ? lb[j] : st === 1 ? ub[j] : (snap.other.get(j) ?? 0);
      if (v < lb[j]) v = lb[j];
      if (v > ub[j]) v = ub[j];
      if (!isFinite(v)) v = isFinite(lb[j]) ? lb[j] : isFinite(ub[j]) ? ub[j] : 0;
      x[j] = v;
    }
    const ok = this.reinvert();
    this.dse.fill(1);
    this.computeBasics();
    this.computeReducedCosts(this.cost);
    return ok;
  }

  objective(): number {
    let obj = this.lp.objConstant;
    for (let j = 0; j < this.n; j++) obj += this.lp.objective[j] * this.x[j];
    return obj;
  }

  result(status: SimplexStatus): LPResult {
    const { lp, n, m, x, d } = this;
    if (status !== 'optimal') return emptyResult(lp, status, this.iterations);
    const xs = new Float64Array(n);
    let obj = lp.objConstant;
    for (let j = 0; j < n; j++) {
      xs[j] = clean(x[j]);
      obj += lp.objective[j] * xs[j];
    }
    const duals = new Float64Array(m);
    for (let i = 0; i < m; i++) duals[i] = clean(d[n + i]);
    const rc = new Float64Array(n);
    for (let j = 0; j < n; j++) rc[j] = clean(d[j]);
    return { status, objective: obj, x: xs, duals, reducedCosts: rc, iterations: this.iterations };
  }
}
