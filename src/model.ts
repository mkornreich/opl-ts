/**
 * A model instance: model AST + data, instantiated, generated into a linear
 * program, solved, and post-processed (post-solve declarations, display,
 * SheetWrite).
 */

import * as fs from 'node:fs';
import * as path from 'node:path';
import type { CStmt, DataAst, Expr, ModelAst, Stmt } from './ast.js';
import { fail } from './errors.js';
import { Evaluator, MAXINT, Scope } from './eval.js';
import { resolveInput, type Warn } from './files.js';
import { ConstraintRef, DVar, LinExpr } from './linear.js';
import { parseDataValue } from './parser.js';
import { printExpr } from './print.js';
import { SheetConnection } from './sheet.js';
import { solveMIP } from './solver/mip.js';
import type { LinearProgram, MIPStatus } from './solver/lp.js';
import { toLpFormat } from './solver/lpformat.js';
import { clean } from './solver/simplex.js';
import {
  arrayType, EnumType, formatValue, indexType, OplArray, OplRange, OplSet, OplTuple, RawArray, StructType,
  typeName, UNKNOWN, type Binding, type HostObject, type Type, type Value,
} from './values.js';

export interface ModelOptions {
  /** Directory relative file names are resolved against. */
  baseDir: string;
  /** Receives display output, one line per call. */
  out?: (line: string) => void;
  warn?: Warn;
  /** Answers `float c << "prompt";` declarations. */
  input?: (prompt: string) => string | null;
  /** CPLEX nodeSel: 0 = depth-first, 1 = best-bound. */
  nodeSelection?: number;
  timeLimit?: number;
}

export type SolveStatus = MIPStatus | 'none';

export interface SolveInfo {
  status: SolveStatus;
  sense: 'minimize' | 'maximize' | null;
  objective: number;
  objectiveType: Type;
  numVars: number;
  numIntVars: number;
  numConstraints: number;
  iterations: number;
  nodes: number;
  /** Seconds spent in the solver. */
  time: number;
}

type ObjectiveStmt = Extract<Stmt, { k: 'objective' }>;

interface GeneratedRow {
  expr: LinExpr;
  lower: number;
  upper: number;
  ref: ConstraintRef | null;
}

export class ModelInstance implements HostObject {
  readonly hostKind = 'Model';
  readonly ev = new Evaluator();
  readonly global = new Scope();
  private readonly data = new Map<string, Expr>();
  private readonly pre: Stmt[] = [];
  private readonly post: Stmt[] = [];
  private readonly objective: ObjectiveStmt | null = null;
  private readonly sheets: SheetConnection[] = [];
  private initialized = false;
  private vars: DVar[] = [];
  private varNames: string[] = [];
  private rows: GeneratedRow[] = [];
  private readonly out: (line: string) => void;
  private readonly warn: Warn;
  lastSolve: SolveInfo | null = null;

  constructor(
    readonly ast: ModelAst,
    dataFiles: DataAst[],
    readonly options: ModelOptions,
  ) {
    this.out = options.out ?? ((line) => console.log(line));
    this.warn = options.warn ?? ((msg) => console.error(`warning: ${msg}`));
    for (const d of dataFiles) for (const entry of d.entries) this.data.set(entry.name, entry.value);
    for (const st of ast.stmts) {
      if (st.k === 'objective') {
        if (this.objective) fail('a model can only have one objective / subject to block', st.pos);
        this.objective = st;
      } else if (this.objective || st.k === 'sheetWrite') {
        this.post.push(st);
      } else {
        this.pre.push(st);
      }
    }
  }

  get hasObjective(): boolean {
    return this.objective !== null;
  }

  /** True when the model prints its own results with display / SheetWrite. */
  get hasOutputStatements(): boolean {
    return this.ast.stmts.some((s) => s.k === 'display');
  }

  // ------------------------------------------------------------ data

  /** Evaluates the declarations before the objective (except variables). */
  initData(): void {
    if (this.initialized) return;
    this.initialized = true;
    this.ev.phase = 'data';
    for (const st of this.pre) this.exec(st);
  }

  private exec(st: Stmt): void {
    const ev = this.ev;
    switch (st.k) {
      case 'range': {
        const v = ev.eval(st.e, this.global);
        if (!(v instanceof OplRange)) fail(`range ${st.name} must be a range lo..hi`, st.pos);
        this.global.define(st.name, { value: v, type: { k: 'range' } });
        return;
      }
      case 'enum': {
        let values = st.values;
        if (!values) {
          const d = this.data.get(st.name);
          if (!d) fail(`no data for enum ${st.name}`, st.pos);
          if (d.k !== 'setLit' && d.k !== 'arrayLit') fail(`enum ${st.name} needs a set of names`, d.pos);
          values = d.items.map((x) => {
            if (x.k === 'sym' || x.k === 'str') return x.k === 'sym' ? x.name : x.value;
            fail(`enum ${st.name}: expected a name`, x.pos);
          });
        }
        const e = new EnumType(st.name, values);
        this.global.define(st.name, { value: e, type: { k: 'enumType', e } });
        for (const v of values) this.global.define(v, { value: v, type: { k: 'enum', e } });
        return;
      }
      case 'struct': {
        const fields = st.fields.map((f) => ({
          name: f.name,
          type: arrayType(ev.resolveType(f.type, this.global), ev.indexSets(f.dims, this.global)),
        }));
        ev.structs.set(st.name, new StructType(st.name, fields));
        return;
      }
      case 'data':
        this.execData(st);
        return;
      case 'sheetConnection': {
        const file = ev.eval(st.args[0], this.global);
        if (typeof file !== 'string') fail('SheetConnection needs a file name', st.pos);
        const conn = new SheetConnection(resolveInput(file, this.options.baseDir, this.warn, st.pos));
        this.sheets.push(conn);
        this.global.define(st.name, { value: conn, type: { k: 'host' } });
        return;
      }
      case 'display':
        this.display(st);
        return;
      case 'sheetWrite': {
        const conn = this.global.lookup(st.conn)?.value;
        if (!(conn instanceof SheetConnection)) fail(`${st.conn} is not a SheetConnection`, st.pos);
        const range = ev.eval(st.range, this.global);
        if (typeof range !== 'string') fail('SheetWrite needs a range string', st.pos);
        conn.write(range, this.flatten(ev.eval(st.e, this.global)), st.pos);
        return;
      }
      case 'var':
      case 'constraintDecl':
        if (ev.phase === 'post') fail(`${st.k === 'var' ? 'variables' : 'constraints'} must be declared before the objective`, st.pos);
        return;
      case 'objective':
        return;
    }
  }

  private execData(st: Extract<Stmt, { k: 'data' }>): void {
    const ev = this.ev;
    const base = ev.resolveType(st.type, this.global);
    const sets = ev.indexSets(st.dims, this.global);
    const type = arrayType(base, sets);
    const init = st.init;
    let value: Value;
    if (!init) {
      value = ev.defaultValue(type);
    } else {
      switch (init.k) {
        case 'expr':
          value = st.dims.some((d) => d.name)
            ? ev.buildArray(st.dims, sets, this.global, (sc) => ev.shape(ev.eval(init.e, sc), base, init.e.pos))
            : ev.shape(ev.eval(init.e, this.global), type, init.e.pos);
          break;
        case 'external': {
          const d = this.data.get(st.name);
          if (!d) fail(`no data given for '${st.name}' (declared with ...)`, st.pos);
          value = ev.shape(ev.eval(d, this.global), type, d.pos);
          break;
        }
        case 'sheet': {
          const conn = this.global.lookup(init.conn)?.value;
          if (!(conn instanceof SheetConnection)) fail(`${init.conn} is not a SheetConnection`, st.pos);
          const range = ev.eval(init.range, this.global);
          if (typeof range !== 'string') fail('SheetRead needs a range string', st.pos);
          value = ev.shapeFlat(conn.read(range, st.pos), type, st.pos);
          break;
        }
        case 'file': {
          const file = resolveInput(init.path, this.options.baseDir, this.warn, st.pos);
          const e = parseDataValue(fs.readFileSync(file, 'utf8'), file);
          value = ev.shape(ev.eval(e, this.global), type, st.pos);
          break;
        }
        case 'prompt': {
          const answer = this.options.input?.(init.text);
          if (answer === null || answer === undefined) fail(`no input for '${st.name}'`, st.pos);
          const n = Number(answer.trim());
          value = ev.shape(answer.trim() !== '' && !Number.isNaN(n) ? n : answer.trim(), type, st.pos);
          break;
        }
      }
    }
    this.global.define(st.name, { value, type });
  }

  // ------------------------------------------------------------ generation

  private generate(): { lp: LinearProgram; sense: ObjectiveStmt['sense'] } {
    this.initData();
    const ev = this.ev;
    ev.phase = 'model';
    this.vars = [];
    this.varNames = [];
    this.rows = [];
    for (const st of this.pre) {
      if (st.k === 'var') this.declareVar(st);
      else if (st.k === 'constraintDecl') {
        const sets = ev.indexSets(st.dims, this.global);
        const name = (path: Value[]) => st.name + path.map((p) => `[${formatValue(p, UNKNOWN, 'key')}]`).join('');
        const value = st.dims.length
          ? ev.buildArray(st.dims, sets, this.global, (_, path) => new ConstraintRef(name(path)))
          : new ConstraintRef(st.name);
        this.global.define(st.name, { value, type: arrayType({ k: 'constraint' }, sets) });
      }
    }

    const objective = this.objective;
    let obj = new LinExpr();
    if (objective?.e) {
      obj = LinExpr.of(ev.linear(ev.eval(objective.e, this.global), objective.e.pos));
    }
    if (objective) this.walk(objective.constraints, this.global);

    const n = this.vars.length;
    const sign = objective?.sense === 'maximize' ? -1 : 1;
    const lp: LinearProgram = {
      numVars: n,
      objective: new Float64Array(n),
      objConstant: sign * obj.constant,
      lower: new Float64Array(n),
      upper: new Float64Array(n),
      integer: new Uint8Array(n),
      rows: [],
    };
    for (const [id, c] of obj.terms) lp.objective[id] += sign * c;
    this.vars.forEach((v, j) => {
      lp.lower[j] = v.lb;
      lp.upper[j] = v.ub;
      lp.integer[j] = v.isInt ? 1 : 0;
    });
    for (const row of this.rows) {
      const index: number[] = [];
      const value: number[] = [];
      for (const [id, c] of row.expr.terms) {
        if (c === 0) continue;
        index.push(id);
        value.push(c);
      }
      lp.rows.push({ index, value, lower: row.lower, upper: row.upper });
    }
    return { lp, sense: objective?.sense ?? null };
  }

  private declareVar(st: Extract<Stmt, { k: 'var' }>): void {
    const ev = this.ev;
    const base = ev.resolveType(st.type, this.global);
    let isInt: boolean;
    let lb: number;
    let ub: number;
    if (base.k === 'int') {
      isInt = true;
      lb = base.range ? base.range.lo : base.nonneg ? 0 : -Infinity;
      ub = base.range ? base.range.hi : Infinity;
    } else if (base.k === 'float') {
      isInt = false;
      lb = base.nonneg ? 0 : -Infinity;
      ub = Infinity;
    } else {
      fail(`decision variables must be int or float (found ${st.type.k === 'named' ? st.type.name : st.type.k})`, st.pos);
    }
    const sets = ev.indexSets(st.dims, this.global);
    const make = (scope: Scope, path: Value[]): DVar => {
      let lo = lb;
      let hi = ub;
      if (st.domain) {
        const [dlo, dhi] = this.domainBounds(st.domain, scope);
        lo = Math.max(lo, dlo);
        hi = Math.min(hi, dhi);
      }
      const name = st.name + path.map((p) => `[${formatValue(p, UNKNOWN, 'key')}]`).join('');
      const v = new DVar(this.vars.length, name, isInt, lo, hi);
      this.vars.push(v);
      return v;
    };
    const value = st.dims.length ? ev.buildArray(st.dims, sets, this.global, make) : make(this.global, []);
    this.global.define(st.name, { value, type: arrayType({ k: 'var', of: isInt ? 'int' : 'float' }, sets) });
    this.varNames.push(st.name);
  }

  private domainBounds(e: Expr, s: Scope): [number, number] {
    let lo: number;
    let hi: number;
    if (e.k === 'range') {
      lo = this.ev.num(e.lo, s);
      hi = this.ev.num(e.hi, s);
    } else {
      const v = this.ev.eval(e, s);
      if (!(v instanceof OplRange)) fail('a variable domain must be a range lo..hi', e.pos);
      lo = v.lo;
      hi = v.hi;
    }
    // maxint is the "unbounded" integer of OPL; treat it as infinite.
    return [lo <= -MAXINT ? -Infinity : lo, hi >= MAXINT ? Infinity : hi];
  }

  private walk(stmts: CStmt[], s: Scope, inForall = false): void {
    for (const c of stmts) {
      switch (c.k) {
        case 'forall':
          this.ev.forEach(c.q, s, (sc) => this.walk(c.body, sc, true));
          break;
        case 'if':
          this.walk(this.ev.truthy(c.c, s) ? c.then : c.else, s, inForall);
          break;
        case 'constraint':
          this.addConstraint(c, s, inForall);
          break;
      }
    }
  }

  private addConstraint(c: Extract<CStmt, { k: 'constraint' }>, s: Scope, inForall: boolean): void {
    const ev = this.ev;
    let ref: ConstraintRef | null = null;
    if (c.label) {
      if (c.label.k === 'id' && !s.lookup(c.label.name)) {
        if (inForall) {
          fail(`a constraint label inside forall must be indexed: declare 'constraint ${c.label.name}[...];' and write ${c.label.name}[i]: ...`, c.label.pos);
        }
        ref = new ConstraintRef(c.label.name);
        this.global.define(c.label.name, { value: ref, type: { k: 'constraint' } });
      } else {
        const r = ev.evalRef(c.label, s);
        if (!(r instanceof ConstraintRef)) fail(`constraint label must name a constraint, found a ${typeName(r)}`, c.label.pos);
        ref = r;
      }
      if (this.rows.some((row) => row.ref === ref)) fail(`constraint ${ref.name} is defined twice`, c.pos);
    }

    const e = c.e;
    const lin = (x: Expr) => LinExpr.of(ev.linear(ev.eval(x, s), x.pos));
    let expr: LinExpr;
    let lower = -Infinity;
    let upper = Infinity;
    if (e.k === 'bin' && ['<=', '>=', '=', '<', '>', '!='].includes(e.op)) {
      if (e.op === '<' || e.op === '>' || e.op === '!=') {
        fail(`'${e.op}' is not allowed in a linear constraint (use <=, >= or =)`, e.pos);
      }
      expr = lin(e.l).clone().addScaled(lin(e.r), -1);
      const k = -expr.constant;
      expr.constant = 0;
      if (e.op !== '>=') upper = k;
      if (e.op !== '<=') lower = k;
    } else if (e.k === 'chain' && e.ops.length === 2 && e.ops[0] === e.ops[1] && (e.ops[0] === '<=' || e.ops[0] === '>=')) {
      const a = ev.eval(e.exprs[0], s);
      const b = ev.eval(e.exprs[2], s);
      if (typeof a !== 'number' || typeof b !== 'number') fail('the bounds of a range constraint must be constants', e.pos);
      expr = lin(e.exprs[1]).clone();
      const k = expr.constant;
      expr.constant = 0;
      [lower, upper] = e.ops[0] === '<=' ? [a - k, b - k] : [b - k, a - k];
    } else {
      const v = ev.eval(e, s);
      if (typeof v !== 'number') fail('a constraint must be a comparison (<=, >= or =)', e.pos);
      // A constant condition: always satisfied, or an infeasible empty row.
      expr = new LinExpr();
      if (v === 0) lower = upper = 1;
      else lower = upper = 0;
    }
    this.rows.push({ expr, lower, upper, ref });
  }

  // ------------------------------------------------------------ solving

  /** Generates and solves the model; solution values are stored on variables and constraints. */
  solve(): SolveInfo {
    const { lp, sense } = this.generate();
    const t0 = performance.now();
    const res = solveMIP(lp, { nodeSelection: this.options.nodeSelection, timeLimit: this.options.timeLimit });
    const time = (performance.now() - t0) / 1000;
    const sign = sense === 'maximize' ? -1 : 1;
    const ok = res.status === 'optimal' || res.status === 'feasible';
    if (ok) {
      this.vars.forEach((v, j) => {
        v.value = clean(res.x[j]) + 0;
        v.rc = clean(sign * res.reducedCosts[j]) + 0;
      });
      this.rows.forEach((row, i) => {
        if (!row.ref) return;
        let act = 0;
        for (const [id, c] of row.expr.terms) act += c * this.vars[id].value;
        row.ref.activity = clean(act) + 0;
        row.ref.dual = clean(sign * res.duals[i]) + 0;
        row.ref.slack = clean(isFinite(row.upper) ? row.upper - act : act - row.lower) + 0;
      });
    }
    const objectiveType = this.objective?.e ? this.ev.typeOf(this.objective.e, this.global) : UNKNOWN;
    this.lastSolve = {
      status: this.objective ? res.status : 'none',
      sense,
      objective: ok ? clean(sign * res.objective) + 0 : NaN,
      objectiveType,
      numVars: lp.numVars,
      numIntVars: lp.integer.reduce((a, b) => a + b, 0),
      numConstraints: lp.rows.length,
      iterations: res.iterations,
      nodes: res.nodes,
      time,
    };
    return this.lastSolve;
  }

  /** The generated linear program in CPLEX LP format. */
  exportLP(): string {
    const { lp, sense } = this.generate();
    const rowNames = this.rows.map((r, i) => r.ref?.name ?? `c${i + 1}`);
    const title = `generated by opl-ts from ${path.basename(this.ast.file)}`;
    return toLpFormat(lp, sense === 'maximize', this.vars.map((v) => v.name), rowNames, title);
  }

  get solved(): boolean {
    const st = this.lastSolve?.status;
    return st === 'optimal' || st === 'feasible';
  }

  /** Runs the statements after the objective (only when a solution exists). */
  postProcess(): void {
    if (this.objective && !this.solved) return;
    this.ev.phase = 'post';
    for (const st of this.post) this.exec(st);
    for (const sheet of this.sheets) sheet.save();
  }

  reset(): void {
    this.lastSolve = null;
    for (const v of this.vars) {
      v.value = NaN;
      v.rc = NaN;
    }
    for (const row of this.rows) {
      if (row.ref) row.ref.dual = row.ref.slack = row.ref.activity = NaN;
    }
    this.ev.phase = 'data';
  }

  // ------------------------------------------------------------ output

  private display(st: Extract<Stmt, { k: 'display' }>): void {
    const emit = (scope: Scope) => {
      const value = this.ev.eval(st.e, scope);
      const type = this.ev.typeOf(st.e, scope);
      const names = new Set(st.q?.binders.flatMap((b) => b.names) ?? []);
      const label = printExpr(st.e, (name) => {
        if (!names.has(name)) return null;
        const b = scope.lookup(name)!;
        return formatValue(b.value, b.type, 'key');
      });
      this.printValue(label, value, type, false);
    };
    if (st.q) this.ev.forEach(st.q, this.global, emit);
    else emit(this.global);
  }

  private printValue(label: string, value: Value, type: Type, hideZero: boolean): void {
    if (value instanceof OplArray) {
      const inner = indexType(type, 1);
      value.items.forEach((item, i) => {
        this.printValue(`${label}[${formatValue(value.index.at(i), indexKeyType(value.index), 'key')}]`, item, inner, hideZero);
      });
      return;
    }
    if (hideZero) {
      const v = value instanceof DVar ? value.value : value;
      if (typeof v === 'number' && Math.abs(v) < 1e-9) return;
    }
    this.out(`${label} = ${formatValue(value, type, 'display')}`);
  }

  /** Prints every decision variable (what OPL Studio shows when there is no display). */
  printVariables(hideZero: boolean): void {
    for (const name of this.varNames) {
      const b = this.global.lookup(name)!;
      this.printValue(name, b.value, b.type, hideZero);
    }
  }

  private flatten(v: Value): Value[] {
    if (v instanceof DVar) return [v.value];
    if (v instanceof OplArray || v instanceof RawArray) return v.items.flatMap((x) => this.flatten(x));
    if (v instanceof OplTuple) return v.values.flatMap((x) => this.flatten(x));
    if (v instanceof OplSet) return v.elems.flatMap((x) => this.flatten(x));
    if (typeof v === 'number' || typeof v === 'string') return [v];
    fail(`cannot write a ${typeName(v)} to a sheet`);
  }

  // ------------------------------------------------------------ HostObject (OPLScript access)

  getField(name: string): Binding | undefined {
    this.initData();
    return this.global.lookup(name);
  }
}

function indexKeyType(set: OplArray['index']): Type {
  return set instanceof OplSet && set.elemType ? set.elemType : UNKNOWN;
}
