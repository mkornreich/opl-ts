/**
 * A model instance: model AST + data, instantiated, generated, solved, and
 * post-processed (post-solve declarations, display, SheetWrite, DBupdate).
 *
 * Linear models go to the simplex / branch-and-bound solver; models using
 * constraint-programming features (non-linear or logical constraints, global
 * constraints, scheduling, enum or set domains, a search procedure) go to the
 * finite-domain solver.
 */

import * as fs from 'node:fs';
import * as path from 'node:path';
import type { CStmt, DataAst, Expr, ModelAst, SStmt, Stmt } from './ast.js';
import { IlogRuntime } from './ilog.js';
import { clampBounds } from './cp/builder.js';
import { linearize, type QuadTerm } from './cp/linearize.js';
import { solveCP } from './cp/search.js';
import { Activity, CP_MAXINT, CPConstraint, Flattener, Resource, type CPCons, type CPDef, type CPHooks } from './cp/terms.js';
import { DBConnection } from './db.js';
import { fail, type SourcePos } from './errors.js';
import { DExpr, dvarValue, Evaluator, MAXINT, Predicate, Scope } from './eval.js';
import { resolveInput, type Warn } from './files.js';
import { ConstraintRef, DVar, isLinear, LinExpr } from './linear.js';
import { parseDataValue } from './parser.js';
import { printExpr } from './print.js';
import { SheetConnection } from './sheet.js';
import { solveMIP } from './solver/mip.js';
import type { LinearProgram, MIPStatus } from './solver/lp.js';
import { toLpFormat } from './solver/lpformat.js';
import { isConvex, solveMIQP, type Hessian } from './solver/qp.js';
import { clean } from './solver/simplex.js';
import {
  arrayType, elementsOf, EnumType, formatValue, indexType, keyOf, OplArray, OplRange, OplSet, OplTuple, RawArray,
  StructType, typeName, UNKNOWN, type Binding, type HostObject, type Type, type Value,
} from './values.js';

export interface ModelOptions {
  /** Directory relative file names are resolved against. */
  baseDir: string;
  /** Receives display output, one line per call. */
  out?: (line: string) => void;
  /** Receives script output (writeln / write); defaults to out. */
  write?: (text: string) => void;
  warn?: Warn;
  /** Answers `float c << "prompt";` declarations. */
  input?: (prompt: string) => string | null;
  /** CPLEX nodeSel: 0 = depth-first, 1 = best-bound. */
  nodeSelection?: number;
  /** Allow IloOplExec in scripts to run shell commands. */
  allowExec?: boolean;
  /** Seconds per solve (CPLEX tilim). */
  timeLimit?: number;
  /** performance.now() time that bounds every solve of the run (--time-limit). */
  deadline?: number;
  /** Solve with constraint programming even when the model is linear. */
  forceCP?: boolean;
  /** Constraint programming without objective: enumerate every solution. */
  allSolutions?: boolean;
}

export type SolveStatus = MIPStatus | 'none';

export interface SolveInfo {
  status: SolveStatus;
  solver: 'LP' | 'MIP' | 'QP' | 'MIQP' | 'CP';
  sense: 'minimize' | 'maximize' | null;
  objective: number;
  objectiveType: Type;
  numVars: number;
  numIntVars: number;
  numConstraints: number;
  iterations: number;
  nodes: number;
  /** Constraint programming: failures and choice points. */
  fails: number;
  choicePoints: number;
  /** Number of solutions found (all of them with allSolutions). */
  solutions: number;
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
  private search: SStmt[] | null = null;
  private readonly sheets: SheetConnection[] = [];
  private initialized = false;
  private vars: DVar[] = [];
  /** Declared decision variables and activities, for listing and default search. */
  private varNames: string[] = [];
  private decision: DVar[] = [];
  private rows: GeneratedRow[] = [];
  /** Products z = x * y of a quadratic objective (z is a placeholder column). */
  private quad: QuadTerm[] = [];
  private cpCons: CPCons[] = [];
  private cpDefs: CPDef[] = [];
  private cpRefs: ConstraintRef[] = [];
  private activities: Activity[] = [];
  private selections = new Map<Activity, Map<Resource, DVar[]>>();
  private usesCP = false;
  private horizon: number | null = null;
  private origin = 0;
  private solutions: Float64Array[] = [];
  private main: Extract<Stmt, { k: 'script' }> | null = null;
  private usingCP = false;
  private runtime: IlogRuntime | null = null;
  /** Data given by scripts (IloOplDataElements) for `...` declarations. */
  private readonly overrides = new Map<string, Value>();
  /** Variable bounds changed by scripts (x.LB = ...), by variable name. */
  private readonly bounds = new Map<string, { lb?: number; ub?: number }>();
  private relaxed = false;
  private readonly dataConnections = new Map<string, { decl: NonNullable<DataAst['connections']>[number]; conn: SheetConnection | DBConnection | null }>();
  private readonly dataWrites: NonNullable<DataAst['writes']> = [];
  private lastObjective: LinExpr | null = null;
  /** Labels inside forall (`forall(i in I) ct: ...`) become arrays indexed by the iterators. */
  private labels = new Map<string, { path: Value[]; ref: ConstraintRef }[]>();
  private readonly out: (line: string) => void;
  private readonly write: (text: string) => void;
  readonly warn: Warn;
  lastSolve: SolveInfo | null = null;

  constructor(
    readonly ast: ModelAst,
    dataFiles: DataAst[],
    readonly options: ModelOptions,
  ) {
    this.out = options.out ?? ((line) => console.log(line));
    const out = this.out;
    this.write = options.write ?? ((text) => {
      const lines = text.split('\n');
      if (lines[lines.length - 1] === '') lines.pop();
      for (const l of lines) out(l);
    });
    this.warn = options.warn ?? ((msg) => console.error(`warning: ${msg}`));
    for (const d of dataFiles) this.addData(d);
    // Modern OPL may give the objective (`minimize e;`) and the constraints
    // (`subject to { ... }` / `constraints { ... }`) as separate statements.
    let lastModelStmt = -1;
    ast.stmts.forEach((st, i) => {
      if (st.k === 'objective') lastModelStmt = i;
    });
    let objective: ObjectiveStmt | null = null;
    ast.stmts.forEach((st, i) => {
      if (st.k === 'objective') {
        if (!objective) objective = { ...st, constraints: [...st.constraints] };
        else {
          if (st.e && objective.e) fail('a model can only have one objective', st.pos);
          if (st.e) {
            objective.e = st.e;
            objective.sense = st.sense;
          }
          objective.constraints.push(...st.constraints);
        }
      } else if (st.k === 'search') {
        if (lastModelStmt < 0) fail('search must follow the objective / solve block', st.pos);
        if (this.search) fail('a model can only have one search procedure', st.pos);
        this.search = st.body;
      } else if (st.k === 'script' && st.kind === 'main') {
        if (this.main) fail('a model can only have one main block', st.pos);
        this.main = st;
      } else if (st.k === 'using') {
        this.usingCP = /^CP$/i.test(st.solver);
      } else if ((lastModelStmt >= 0 && i > lastModelStmt) || st.k === 'sheetWrite' || st.k === 'dbUpdate') {
        this.post.push(st);
      } else {
        this.pre.push(st);
      }
    });
    this.objective = objective;
  }

  addData(d: DataAst): void {
    for (const entry of d.entries) this.data.set(entry.name, entry.value);
    for (const c of d.connections ?? []) this.dataConnections.set(c.name, { decl: c, conn: null });
    this.dataWrites.push(...(d.writes ?? []));
  }

  /** A SheetConnection / DBConnection declared in a data file (opened on first use). */
  private dataConnection(name: string, pos: SourcePos): SheetConnection | DBConnection {
    const c = this.dataConnections.get(name);
    if (!c) fail(`unknown connection '${name}'`, pos);
    if (!c.conn) {
      const args = c.decl.args.map((a) => this.ev.eval(a, this.global));
      if (c.decl.kind === 'sheet') {
        if (typeof args[0] !== 'string') fail('SheetConnection needs a file name', c.decl.pos);
        const conn = new SheetConnection(resolveInput(args[0], this.options.baseDir, this.warn, c.decl.pos));
        this.sheets.push(conn);
        c.conn = conn;
      } else {
        const [driver, file] = args;
        if (typeof driver !== 'string' || typeof file !== 'string') fail('DBConnection needs a driver and a database name', c.decl.pos);
        c.conn = new DBConnection(driver, file === ':memory:' ? file : path.resolve(this.options.baseDir, file), c.decl.pos);
      }
    }
    return c.conn;
  }

  /** `name from SheetRead(conn, "range")` / `DBRead(conn, "sql")` in a data file. */
  private readFromSource(e: Extract<Expr, { k: 'call' }>, type: Type, pos: SourcePos): Value {
    if (e.args[0]?.k !== 'id') fail(`${e.fn} needs a connection name`, e.pos);
    const conn = this.dataConnection(e.args[0].name, e.pos);
    const what = this.ev.eval(e.args[1], this.global);
    if (typeof what !== 'string') fail(`${e.fn} needs a string argument`, e.pos);
    const cells = conn instanceof SheetConnection ? conn.read(what, e.pos) : conn.read(what, e.pos);
    return this.ev.shapeFlat(cells, type, pos);
  }

  /** `name to SheetWrite(conn, "range")` / `DBUpdate(conn, "sql")` after solving. */
  private writeToSinks(): void {
    for (const w of this.dataWrites) {
      if (w.call.k !== 'call' || w.call.args[0]?.k !== 'id') fail('expected SheetWrite(conn, ...) or DBUpdate(conn, ...)', w.pos);
      const conn = this.dataConnection(w.call.args[0].name, w.pos);
      const what = this.ev.eval(w.call.args[1], this.global);
      if (typeof what !== 'string') fail(`${w.call.fn} needs a string argument`, w.pos);
      const v = this.fieldValue(w.name);
      if (v === undefined) fail(`unknown model element '${w.name}'`, w.pos);
      if (conn instanceof SheetConnection) conn.write(what, this.flatten(v), w.pos);
      else conn.update(what, (elementsOf(v) ?? (v instanceof OplArray ? v.items : [v])).map((x) => this.flatten(x)), w.pos);
    }
  }

  addOverrides(values: Map<string, Value>): void {
    for (const [k, v] of values) this.overrides.set(k, v);
  }

  /** True for variables, dexprs and other model elements that exist only after generation. */
  isGeneratedElement(name: string): boolean {
    return this.pre.some((st) => (st.k === 'var' || st.k === 'dexpr' || st.k === 'activity' || st.k === 'resource' || st.k === 'constraintDecl') && st.name === name);
  }

  get hasMain(): boolean {
    return this.main !== null;
  }

  /** Runs the main { ... } block (the script then drives generation and solving). */
  runMain(): void {
    if (!this.main) return;
    this.scriptRuntime().run(this.main.code, this.ast.file, this.main.pos);
  }

  scriptRuntime(write = this.write): IlogRuntime {
    this.runtime ??= new IlogRuntime(this, write);
    return this.runtime;
  }

  /** A new model sharing this one's options (IloOplModel in scripts). */
  childModel(ast: ModelAst): ModelInstance {
    return new ModelInstance(ast, [], { ...this.options, write: this.write, out: this.out, warn: this.warn });
  }

  /**
   * thisOplModel.generate(): the model is generated once and kept, so that
   * scripts can change it (ct.setCoef, ct.LB, cplex.setObjCoef) between solves.
   */
  scriptGenerate(): void {
    this.initData();
    this.generate();
    const obj = this.objectiveExpr();
    this.tryLinearize(obj);
    this.kept = { obj };
  }

  private kept: { obj: LinExpr } | null = null;

  private rowOf(ref: ConstraintRef): GeneratedRow {
    const row = this.rows.find((r) => r.ref === ref);
    if (!row) fail(`${ref.name} is not a linear constraint of the generated model`);
    return row;
  }

  /** ct.setCoef(x, c) */
  setRowCoef(ref: ConstraintRef, v: DVar, c: number): void {
    this.rowOf(ref).expr.terms.set(v.id, c);
  }

  /** Bounds of a constraint row (its constant moved to the bounds, as ct.LB / ct.UB). */
  rowBounds(ref: ConstraintRef): { lb: number; ub: number } {
    const row = this.rowOf(ref);
    return { lb: row.lower, ub: row.upper };
  }

  setRowBound(ref: ConstraintRef, which: 'lb' | 'ub', value: number): void {
    const row = this.rowOf(ref);
    if (which === 'lb') row.lower = value;
    else row.upper = value;
  }

  /** cplex.setObjCoef(x, c) */
  setObjCoef(v: DVar, c: number): void {
    if (!this.kept) fail('setObjCoef needs a generated model (thisOplModel.generate())');
    this.kept.obj.terms.set(v.id, c);
  }

  solveForScript(allSolutions: boolean): void {
    this.options.allSolutions = allSolutions;
    this.reset();
    this.solve();
  }

  setRelaxation(relaxed: boolean): void {
    this.relaxed = relaxed;
  }

  setBound(name: string, which: 'lb' | 'ub', value: number): void {
    const b = this.bounds.get(name) ?? {};
    b[which] = value;
    this.bounds.set(name, b);
    const v = this.vars.find((x) => x.name === name);
    if (v) v[which] = value;
  }

  /** The value of a model element for scripts (dexprs evaluated). */
  fieldValue(name: string): Value | undefined {
    const b = this.getField(name);
    if (!b) return undefined;
    return this.resolveDExprs(b.value);
  }

  resolveDExprs(v: Value): Value {
    if (v instanceof DExpr) {
      const saved = this.ev.phase;
      this.ev.phase = 'post';
      try {
        return this.ev.eval(v.e, v.scope);
      } finally {
        this.ev.phase = saved;
      }
    }
    if (v instanceof OplArray && v.items.some((x) => x instanceof DExpr || x instanceof OplArray)) {
      return new OplArray(v.index, v.items.map((x) => this.resolveDExprs(x)));
    }
    return v;
  }

  /** A copy of a data element (for IloOplDataElements). */
  copyData(name: string): Value | undefined {
    const copy = (v: Value): Value => {
      if (v instanceof OplArray) return new OplArray(v.index, v.items.map(copy));
      if (v instanceof OplSet) return new OplSet(v.elems, v.elemType);
      return v;
    };
    const b = this.getField(name);
    return b && !(b.value instanceof DVar) ? copy(b.value) : undefined;
  }

  /** Objective value of the k-th solution of a constraint-programming solve. */
  objectiveOf(k: number): number {
    const sol = this.solutions[k];
    const obj = this.lastObjective;
    if (!sol || !obj) return NaN;
    let v = obj.constant;
    for (const [id, c] of obj.terms) v += c * sol[id];
    return clean(v) + 0;
  }

  get hasObjective(): boolean {
    return this.objective !== null;
  }

  /** True when the model prints its own results with display. */
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
          key: f.key,
        }));
        ev.structs.set(st.name, new StructType(st.name, fields));
        return;
      }
      case 'data':
        // cumulFunction f = sum(...) pulse(...): built with the intervals, at generation
        if (!isCumulDecl(st)) this.execData(st);
        return;
      case 'sheetConnection': {
        const file = ev.eval(st.args[0], this.global);
        if (typeof file !== 'string') fail('SheetConnection needs a file name', st.pos);
        const conn = new SheetConnection(resolveInput(file, this.options.baseDir, this.warn, st.pos));
        this.sheets.push(conn);
        this.global.define(st.name, { value: conn, type: { k: 'host' } });
        return;
      }
      case 'dbConnection': {
        const [driver, file] = st.args.map((a) => ev.eval(a, this.global));
        if (typeof driver !== 'string' || typeof file !== 'string') fail('DBconnection needs a driver and a database name', st.pos);
        const target = file === ':memory:' ? file : path.resolve(this.options.baseDir, file);
        this.global.define(st.name, { value: new DBConnection(driver, target, st.pos), type: { k: 'host' } });
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
      case 'dbUpdate': {
        const conn = this.global.lookup(st.conn)?.value;
        if (!(conn instanceof DBConnection)) fail(`${st.conn} is not a DBconnection`, st.pos);
        const sql = ev.eval(st.sql, this.global);
        if (typeof sql !== 'string') fail('the SQL statement must be a string', st.pos);
        if (!st.e) {
          conn.execute(sql, st.pos);
          return;
        }
        const v = ev.eval(st.e, this.global);
        const rows = (elementsOf(v) ?? (v instanceof OplArray || v instanceof RawArray ? v.items : [v])).map((x) => this.flatten(x));
        conn.update(sql, rows, st.pos);
        return;
      }
      case 'script':
        this.scriptRuntime().run(st.code, this.ast.file, st.pos, true);
        return;
      case 'assert': {
        const check = (sc: Scope) => {
          if (!ev.truthy(st.e, sc)) fail(`assertion ${st.label ? `${st.label} ` : ''}failed`, st.pos);
        };
        if (st.q) ev.forEach(st.q, this.global, check);
        else check(this.global);
        return;
      }
      case 'dexpr':
        if (ev.phase === 'post') fail('dexpr must be declared before the objective', st.pos);
        return;
      case 'using':
      case 'include':
        return;
      case 'predicate': {
        const set = ev.eval(st.set, this.global);
        if (!(set instanceof OplSet)) fail(`predicate ${st.name} needs a set of tuples`, st.pos);
        this.global.define(st.name, { value: new Predicate(st.name, st.arity, set), type: { k: 'unknown' } });
        return;
      }
      case 'horizon': {
        const v = ev.num(st.e, this.global);
        if (st.which === 'horizon') this.horizon = v;
        else this.origin = v;
        return;
      }
      case 'var':
      case 'constraintDecl':
      case 'activity':
      case 'resource':
        if (ev.phase === 'post') fail('decision variables, activities and resources must be declared before the objective', st.pos);
        return;
      case 'objective':
      case 'search':
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
          const o = this.overrides.get(st.name);
          if (o !== undefined) {
            value = ev.shape(o, type, st.pos);
            break;
          }
          const d = this.data.get(st.name);
          if (!d) fail(`no data given for '${st.name}' (declared with ...)`, st.pos);
          if (d.k === 'call' && /^(SheetRead|DBRead|DBread)$/.test(d.fn)) {
            value = this.readFromSource(d, type, st.pos);
            break;
          }
          value = ev.shape(ev.eval(d, this.global), type, d.pos, true);
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
        case 'db': {
          const conn = this.global.lookup(init.conn)?.value;
          if (!(conn instanceof DBConnection)) fail(`${init.conn} is not a DBconnection`, st.pos);
          const sql = ev.eval(init.sql, this.global);
          if (typeof sql !== 'string') fail('DBread needs an SQL query string', st.pos);
          value = ev.shapeFlat(conn.read(sql, st.pos), type, st.pos);
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

  private hooks(): CPHooks {
    return {
      newVar: (lo, hi, isInt, name) => {
        const v = new DVar(this.vars.length, name, isInt, lo, hi);
        v.aux = true;
        this.vars.push(v);
        this.usesCP = true;
        return v;
      },
      define: (def) => {
        this.cpDefs.push(def);
        this.usesCP = true;
      },
      bounds: (v) => clampBounds(v.lb, v.ub, v.isInt),
      domain: () => null,
      dvar: (id) => this.vars[id],
      selections: this.selections,
    };
  }

  private generate(): void {
    this.initData();
    const ev = this.ev;
    ev.phase = 'model';
    this.vars = [];
    this.varNames = [];
    this.decision = [];
    this.rows = [];
    this.cpCons = [];
    this.cpDefs = [];
    this.quad = [];
    this.cpRefs = [];
    this.activities = [];
    this.selections = new Map();
    this.labels = new Map();
    ev.selections = this.selections;
    this.usesCP = this.search !== null || !!this.options.forceCP || this.usingCP;
    ev.cp = this.hooks();
    try {
      for (const st of this.pre) {
        if (st.k === 'var') this.declareVar(st);
        else if (st.k === 'dexpr') this.declareDExpr(st);
        else if (st.k === 'data' && isCumulDecl(st)) this.declareDExpr({ k: 'dexpr', type: st.type, name: st.name, dims: st.dims, e: (st.init as { e: Expr }).e, pos: st.pos });
        else if (st.k === 'constraintDecl') {
          const sets = ev.indexSets(st.dims, this.global);
          const value = st.dims.length
            ? ev.buildArray(st.dims, sets, this.global, (_, p) => new ConstraintRef(st.name + keyPath(p)))
            : new ConstraintRef(st.name);
          this.global.define(st.name, { value, type: arrayType({ k: 'constraint' }, sets) });
        } else if (st.k === 'activity') this.declareActivity(st);
        else if (st.k === 'resource') this.declareResource(st);
      }
      if (this.objective) this.walk(this.objective.constraints, this.global);
      for (const [name, entries] of this.labels) {
        this.global.define(name, { value: labelArray(entries, 0), type: { k: 'unknown' } });
      }
    } finally {
      ev.cp = null;
    }
  }

  private declareDExpr(st: Extract<Stmt, { k: 'dexpr' }>): void {
    const ev = this.ev;
    const base = ev.resolveType(st.type, this.global);
    const sets = ev.indexSets(st.dims, this.global);
    const make = (scope: Scope): DExpr => {
      // Snapshot the iterators: the array cells are evaluated later.
      const snap = new Scope(this.global);
      for (const d of st.dims) if (d.name) snap.define(d.name, { ...scope.lookup(d.name)! });
      return new DExpr(st.name, st.e, snap);
    };
    // Large dexpr arrays are only computed where they are used.
    const cells = sets.reduce((a, set) => a * set.size, 1);
    const value = !st.dims.length
      ? new DExpr(st.name, st.e, this.global)
      : cells > 100_000
        ? ev.buildLazyArray(st.dims, sets, this.global, make)
        : ev.buildArray(st.dims, sets, this.global, make);
    this.global.define(st.name, { value, type: arrayType(base, sets) });
  }

  private objectiveExpr(): LinExpr {
    const e = this.objective?.e;
    return e ? this.linearOf(e) : new LinExpr();
  }

  /** An expression over decision variables as a linear expression (CP terms become auxiliary variables). */
  private linearOf(e: Expr): LinExpr {
    this.ev.phase = 'model';
    this.ev.cp = this.hooks();
    try {
      return LinExpr.of(this.ev.linear(this.ev.eval(e, this.global), e.pos));
    } finally {
      this.ev.cp = null;
    }
  }

  private linearProgram(obj: LinExpr): LinearProgram {
    const n = this.vars.length;
    const sign = this.objective?.sense === 'maximize' ? -1 : 1;
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
    // Products of a quadratic objective: the Hessian holds them, their linear parts go here.
    if (this.quad.length) {
      // (the placeholder columns themselves are pinned at 0; their values are set after solving)
      for (const { z } of this.quad) {
        lp.objective[z.id] = 0;
        lp.lower[z.id] = lp.upper[z.id] = 0;
      }
      const q = this.quadraticPart(obj, this.quad);
      for (const [id, c] of q.linear) lp.objective[id] += c;
      lp.objConstant += q.constant;
    }
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
    return lp;
  }

  private declareVar(st: Extract<Stmt, { k: 'var' }>): void {
    if (st.interval) return this.declareInterval(st);
    const ev = this.ev;
    if (st.alias) {
      // dvar int x[1..3] = [a, b, c]: an array of variables declared before.
      const sets = ev.indexSets(st.dims, this.global);
      const base = ev.resolveType(st.type, this.global);
      const elem: Type = base.k === 'enum' ? base : { k: 'var', of: base.k === 'float' ? 'float' : 'int' };
      const type = arrayType(elem, sets);
      this.global.define(st.name, { value: ev.shape(ev.eval(st.alias, this.global), type, st.alias.pos), type });
      this.varNames.push(st.name);
      return;
    }
    const base = ev.resolveType(st.type, this.global);
    let isInt: boolean;
    let lb: number;
    let ub: number;
    let enumType: EnumType | undefined;
    // OPL 3 `var float x` is free; modern `dvar` variables are non-negative by default.
    const nonneg = (base.k === 'int' || base.k === 'float') && (!!base.nonneg || !!st.modern);
    if (base.k === 'int') {
      isInt = true;
      lb = base.range ? base.range.lo : nonneg ? 0 : -Infinity;
      ub = base.range ? base.range.hi : Infinity;
    } else if (base.k === 'float') {
      isInt = false;
      lb = nonneg ? 0 : -Infinity;
      ub = Infinity;
    } else if (base.k === 'enum') {
      isInt = true;
      enumType = base.e;
      lb = 0;
      ub = base.e.size - 1;
      this.usesCP = true;
    } else {
      fail(`decision variables must be int, float or an enum (found ${st.type.k === 'named' ? st.type.name : st.type.k})`, st.pos);
    }
    const sets = ev.indexSets(st.dims, this.global);
    const make = (scope: Scope, p: Value[]): DVar => {
      let lo = lb;
      let hi = ub;
      let values: number[] | undefined;
      if (st.domain) {
        const d = this.domain(st.domain, scope, enumType);
        // An explicit domain replaces the default bounds of a dvar.
        const explicitLo = st.modern && !(base.k !== 'enum' && 'nonneg' in base && base.nonneg) && !('range' in base && base.range);
        lo = explicitLo ? d.lo : Math.max(lo, d.lo);
        hi = Math.min(hi, d.hi);
        values = d.values;
      }
      const name = st.name + keyPath(p);
      const override = this.bounds.get(name);
      if (override?.lb !== undefined) lo = override.lb;
      if (override?.ub !== undefined) hi = override.ub;
      const v = new DVar(this.vars.length, name, isInt, lo, hi);
      if (enumType) v.enumType = enumType;
      if (values) {
        v.domain = values;
        this.usesCP = true;
      }
      this.vars.push(v);
      this.decision.push(v);
      return v;
    };
    const value = st.dims.length ? ev.buildArray(st.dims, sets, this.global, make) : make(this.global, []);
    const elem: Type = enumType ? { k: 'enum', e: enumType } : { k: 'var', of: isInt ? 'int' : 'float' };
    this.global.define(st.name, { value, type: arrayType(elem, sets) });
    this.varNames.push(st.name);
  }

  /** dvar interval a [optional] [in lo..hi] [size s]  (CP Optimizer interval variables). */
  private declareInterval(st: Extract<Stmt, { k: 'var' }>): void {
    const ev = this.ev;
    const spec = st.interval!;
    this.usesCP = true;
    const sets = ev.indexSets(st.dims, this.global);
    const flat = new Flattener(this.hooks());
    const make = (scope: Scope, p: Value[]): Activity => {
      const name = st.name + keyPath(p);
      let lo = 0;
      let hi = this.horizon ?? CP_MAXINT >> 1;
      if (spec.window) {
        const d = this.domain(spec.window, scope);
        lo = d.lo;
        hi = Math.min(hi, d.hi);
      }
      let dur: DVar | number = 0;
      if (spec.size) {
        if (spec.size.k === 'range') {
          const a = ev.num(spec.size.lo, scope);
          const b = ev.num(spec.size.hi, scope);
          dur = flat.h.newVar(a, b, true, `${name}.size`);
        } else {
          dur = flat.atom(ev.linear(ev.eval(spec.size, scope), spec.size.pos), `${name}.size`);
        }
      }
      const dlo = typeof dur === 'number' ? dur : dur.lb;
      const start = new DVar(this.vars.length, `${name}.start`, true, lo, hi - dlo);
      this.vars.push(start);
      const end = new DVar(this.vars.length, `${name}.end`, true, lo + dlo, hi);
      this.vars.push(end);
      start.aux = end.aux = true;
      let presence: DVar | null = null;
      if (spec.optional) {
        presence = new DVar(this.vars.length, `presenceOf(${name})`, true, 0, 1);
        this.vars.push(presence);
        this.decision.push(presence);
      }
      this.cpDefs.push({ k: 'post', cons: { k: 'cmp', op: '=', l: end, r: LinExpr.of(start).clone().addScaled(dur, 1) } });
      const act = new Activity(name, start, end, dur, false, presence);
      this.activities.push(act);
      return act;
    };
    const value = st.dims.length ? ev.buildArray(st.dims, sets, this.global, make) : make(this.global, []);
    this.global.define(st.name, { value, type: arrayType(UNKNOWN, sets) });
    this.varNames.push(st.name);
  }

  /** `in lo..hi` (int or float bounds) or `in S` (a set of values). */
  private domain(e: Expr, s: Scope, enumType?: EnumType): { lo: number; hi: number; values?: number[] } {
    let lo: number;
    let hi: number;
    if (e.k === 'range') {
      lo = this.ev.num(e.lo, s);
      hi = this.ev.num(e.hi, s);
    } else {
      const v = this.ev.eval(e, s);
      if (v instanceof OplRange) {
        lo = v.lo;
        hi = v.hi;
      } else {
        const elems = elementsOf(v);
        if (!elems) fail(`a variable domain must be a range or a set, found a ${typeName(v)}`, e.pos);
        const values = elems.map((x) => {
          if (typeof x === 'number') return x;
          if (typeof x === 'string' && enumType && enumType.indexOf(x) >= 0) return enumType.indexOf(x);
          fail('a variable domain set must contain integers', e.pos);
        });
        return { lo: Math.min(...values), hi: Math.max(...values), values };
      }
    }
    // maxint is the "unbounded" integer of OPL; treat it as infinite.
    return { lo: lo <= -MAXINT ? -Infinity : lo, hi: hi >= MAXINT ? Infinity : hi };
  }

  private declareActivity(st: Extract<Stmt, { k: 'activity' }>): void {
    const ev = this.ev;
    this.usesCP = true;
    const sets = ev.indexSets(st.dims, this.global);
    const horizon = this.horizon ?? CP_MAXINT >> 1;
    const flat = new Flattener(this.hooks());
    const make = (scope: Scope, p: Value[]): Activity => {
      const name = st.name + keyPath(p);
      let dur: DVar | number = 0;
      if (st.duration) {
        const d = ev.eval(st.duration, scope);
        const a = flat.atom(ev.linear(d, st.duration.pos), `${name}.duration`);
        dur = a;
      }
      const [dlo] = typeof dur === 'number' ? [dur] : clampBounds(dur.lb, dur.ub, true);
      const start = new DVar(this.vars.length, `${name}.start`, true, this.origin, horizon - dlo);
      this.vars.push(start);
      const end = new DVar(this.vars.length, `${name}.end`, true, this.origin + dlo, horizon);
      this.vars.push(end);
      start.aux = end.aux = true;
      this.cpDefs.push({ k: 'post', cons: { k: 'cmp', op: '=', l: end, r: LinExpr.of(start).clone().addScaled(dur, 1) } });
      const act = new Activity(name, start, end, dur, st.breakable);
      this.activities.push(act);
      return act;
    };
    const value = st.dims.length ? ev.buildArray(st.dims, sets, this.global, make) : make(this.global, []);
    this.global.define(st.name, { value, type: arrayType(UNKNOWN, sets) });
    this.varNames.push(st.name);
  }

  private declareResource(st: Extract<Stmt, { k: 'resource' }>): void {
    const ev = this.ev;
    this.usesCP = true;
    const sets = ev.indexSets(st.dims, this.global);
    const make = (scope: Scope, p: Value[]): Resource => {
      const name = st.name + keyPath(p);
      const args = st.args.map((a) => ev.eval(a, scope));
      const num = (i: number, dflt: number) => {
        const v = args[i];
        if (v === undefined) return dflt;
        if (typeof v !== 'number') fail(`${st.kind}: argument ${i + 1} must be a number`, st.pos);
        return v;
      };
      switch (st.kind) {
        case 'UnaryResource':
          return new Resource(name, 'unary', 1, 0);
        case 'DiscreteResource':
          return new Resource(name, 'discrete', num(0, 1), 0);
        case 'Reservoir':
          return new Resource(name, 'reservoir', num(0, CP_MAXINT), num(1, 0));
        case 'StateResource': {
          const states = args[0];
          if (!(states instanceof EnumType)) fail('StateResource needs an enum of states', st.pos);
          return new Resource(name, 'state', 1, 0, [], states.values);
        }
        case 'AlternativeResources': {
          const members = args.flatMap((a) => leaves(a));
          if (members.length === 0 || members.some((m) => !(m instanceof Resource))) {
            fail('AlternativeResources needs an array of resources', st.pos);
          }
          return new Resource(name, 'alternative', 0, 0, members as Resource[]);
        }
      }
    };
    const value = st.dims.length ? ev.buildArray(st.dims, sets, this.global, make) : make(this.global, []);
    this.global.define(st.name, { value, type: { k: 'host' } });
  }

  /** path: values of the enclosing forall iterators (null outside forall). */
  private walk(stmts: CStmt[], s: Scope, path: Value[] | null = null, label?: Expr): void {
    for (const c of stmts) {
      switch (c.k) {
        case 'forall':
          this.ev.forEach(c.q, s, (sc) => {
            const values = c.q.binders.flatMap((b) => b.names.map((n) => sc.lookup(n)!.value));
            this.walk(c.body, sc, [...(path ?? []), ...values], c.label ?? label);
          });
          break;
        case 'if':
          this.walk(this.ev.truthy(c.c, s) ? c.then : c.else, s, path, label);
          break;
        case 'constraint':
          this.addConstraint(c.label || !label ? c : { ...c, label }, s, path);
          break;
      }
    }
  }

  private addConstraint(c: Extract<CStmt, { k: 'constraint' }>, s: Scope, path: Value[] | null): void {
    const ev = this.ev;
    let ref: ConstraintRef | null = null;
    if (c.label) {
      const existing = c.label.k === 'id' ? s.lookup(c.label.name)?.value : undefined;
      // Labels have their own namespace: a label may reuse the name of a data element.
      // A plain label inside forall always names an array indexed by the iterators.
      const fresh = c.label.k === 'id' && (existing === undefined || this.labels.has(c.label.name) || !!path ||
        !(existing instanceof ConstraintRef || (existing instanceof OplArray && holdsConstraints(existing))));
      if (fresh && c.label.k === 'id') {
        if (path) {
          // Modern OPL: a label inside forall names an array indexed by the iterators.
          let entries = this.labels.get(c.label.name);
          if (!entries) this.labels.set(c.label.name, (entries = []));
          ref = new ConstraintRef(c.label.name + keyPath(path));
          entries.push({ path, ref });
        } else {
          ref = new ConstraintRef(c.label.name);
          this.global.define(c.label.name, { value: ref, type: { k: 'constraint' } });
        }
      } else {
        const r = ev.evalRef(c.label, s);
        if (!(r instanceof ConstraintRef)) fail(`constraint label must name a constraint, found a ${typeName(r)}`, c.label.pos);
        ref = r;
      }
      if (this.rows.some((row) => row.ref === ref) || this.cpRefs.includes(ref)) fail(`constraint ${ref.name} is defined twice`, c.pos);
    }

    const e = c.e;
    // lo <= linear <= hi: one ranged row.
    if (e.k === 'chain' && e.ops.length === 2 && e.ops[0] === e.ops[1] && (e.ops[0] === '<=' || e.ops[0] === '>=')) {
      const a = ev.eval(e.exprs[0], s);
      const b = ev.eval(e.exprs[2], s);
      const m = ev.eval(e.exprs[1], s);
      if (typeof a === 'number' && typeof b === 'number' && isLinear(m)) {
        const expr = LinExpr.of(m).clone();
        const k = expr.constant;
        expr.constant = 0;
        const [lower, upper] = e.ops[0] === '<=' ? [a - k, b - k] : [b - k, a - k];
        this.rows.push({ expr, lower, upper, ref });
        return;
      }
    }
    const v = ev.eval(e, s);
    if (typeof v === 'number') {
      // A constant condition: always satisfied, or an infeasible empty row.
      this.rows.push({ expr: new LinExpr(), lower: v === 0 ? 1 : 0, upper: v === 0 ? 1 : 0, ref });
      return;
    }
    if (!(v instanceof CPConstraint)) fail(`a constraint must be a comparison or a constraint, found a ${typeName(v)}`, e.pos);
    const cc = v.c;
    if (cc.k === 'cmp' && (cc.op === '<=' || cc.op === '>=' || cc.op === '=')) {
      const expr = LinExpr.of(cc.l).clone().addScaled(cc.r, -1);
      const k = -expr.constant;
      expr.constant = 0;
      this.rows.push({ expr, lower: cc.op === '<=' ? -Infinity : k, upper: cc.op === '>=' ? Infinity : k, ref });
      return;
    }
    this.usesCP = true;
    this.cpCons.push(cc.k === 'alldiff' && c.level ? { ...cc, level: c.level } : cc);
    if (ref) this.cpRefs.push(ref);
  }

  // ------------------------------------------------------------ solving

  /** Generates and solves the model; solution values are stored on variables and constraints. */
  solve(): SolveInfo {
    const e = this.objective?.e;
    if (e?.k === 'call' && e.fn === 'staticLex') return this.solveLexicographic(e.args);
    if (this.kept) {
      // Generated by a script (and possibly changed since): solve it as it is.
      const obj = this.kept.obj;
      this.lastObjective = obj;
      return this.usesCP ? this.solveWithCP(obj) : this.solveLinear(obj);
    }
    this.generate();
    const obj = this.objectiveExpr();
    this.lastObjective = obj;
    this.tryLinearize(obj);
    return this.usesCP ? this.solveWithCP(obj) : this.solveLinear(obj);
  }

  /** Float variables v with an equation  v = integer combination of integer variables  (implied integers). */
  private impliedIntegers(): Set<number> {
    const implied = new Set<number>();
    const isInt = (id: number) => this.vars[id].isInt || implied.has(id);
    for (let changed = true; changed; ) {
      changed = false;
      for (const row of this.rows) {
        if (row.lower !== row.upper || !Number.isInteger(row.lower - row.expr.constant)) continue;
        let free = -1;
        let ok = true;
        for (const [id, c] of row.expr.terms) {
          if (c === 0) continue;
          if (isInt(id)) ok = Number.isInteger(c);
          else if (free < 0 && Math.abs(c) === 1) free = id;
          else ok = false;
          if (!ok) break;
        }
        if (ok && free >= 0) {
          implied.add(free);
          changed = true;
        }
      }
    }
    return implied;
  }

  /**
   * Models that use logical constraints, abs, min, max, piecewise-linear
   * functions, ... but nothing that needs constraint programming are
   * linearized for the MIP solver, as CPLEX does.
   */
  private tryLinearize(obj: LinExpr): void {
    // Enumerating solutions needs the CP search, so does an explicit search procedure or `using CP`.
    if (!this.usesCP || this.search || this.options.forceCP || this.usingCP || this.activities.length || this.options.allSolutions) return;
    // Integer models with moderate domains are better served by the CP solver,
    // which handles logical constraints natively; continuous ones need the MIP.
    // Float variables defined by an integer equation count as integers.
    const implied = this.impliedIntegers();
    const smallIntegers = this.decision.every(
      (v) => implied.has(v.id) || (v.isInt && isFinite(v.lb) && isFinite(v.ub) && Math.abs(v.lb) <= 1e6 && Math.abs(v.ub) <= 1e6),
    );
    if (smallIntegers && this.decision.length > 0) return;
    const before = this.vars.length;
    const hooks = this.hooks();
    const quadratic: QuadTerm[] = [];
    const extra = linearize({
      vars: this.vars,
      rows: this.rows,
      defs: this.cpDefs,
      cons: this.cpCons,
      objective: obj,
      sense: this.objective?.sense ?? null,
      newVar: (lo, hi, isInt, name) => hooks.newVar(lo, hi, isInt, name),
      quadratic,
    });
    // A non-convex quadratic objective stays with the CP solver.
    if (!extra || (quadratic.length && !isConvex(this.quadraticPart(obj, quadratic).h))) {
      this.vars.length = before;
      return;
    }
    this.rows.push(...extra);
    this.quad = quadratic;
    this.cpDefs = [];
    this.cpCons = [];
    this.usesCP = false;
  }

  /**
   * staticLex(c1, c2, ...): optimise c1, then c2 with c1 held at its optimum, and so on.
   * The reported objective is the value of the first criterion.
   */
  private solveLexicographic(criteria: Expr[]): SolveInfo {
    const max = this.objective?.sense === 'maximize';
    const fixed: { e: Expr; value: number }[] = [];
    let info: SolveInfo | null = null;
    for (const c of criteria) {
      this.generate();
      for (const f of fixed) {
        const lin = this.linearOf(f.e).clone();
        const k = lin.constant;
        lin.constant = 0;
        const tol = 1e-9 * Math.max(1, Math.abs(f.value));
        this.rows.push({ expr: lin, lower: max ? f.value - tol - k : -Infinity, upper: max ? Infinity : f.value + tol - k, ref: null });
      }
      const obj = this.linearOf(c);
      this.lastObjective = obj;
      this.tryLinearize(obj);
      info = this.usesCP ? this.solveWithCP(obj) : this.solveLinear(obj);
      if (!this.solved) return info;
      fixed.push({ e: c, value: info.objective });
    }
    if (info && fixed.length) info.objective = fixed[0].value;
    return info!;
  }

  /** The time limit of the next solve: its own limit, cut to what is left of the run's. */
  private solveSeconds(): number | undefined {
    const own = this.options.timeLimit;
    const d = this.options.deadline;
    if (d === undefined) return own;
    const left = Math.max(0.001, (d - performance.now()) / 1000);
    return own === undefined ? left : Math.min(own, left);
  }

  /**
   * The products of a quadratic objective, minimised: the Hessian (upper
   * triangle) and the linear and constant parts of the expanded products.
   */
  private quadraticPart(obj: LinExpr, quad: QuadTerm[]): { h: Hessian; linear: Map<number, number>; constant: number } {
    const sign = this.objective?.sense === 'maximize' ? -1 : 1;
    const entries = new Map<number, number>();
    const n = this.vars.length;
    const linear = new Map<number, number>();
    let constant = 0;
    const addLinear = (id: number, v: number) => linear.set(id, (linear.get(id) ?? 0) + v);
    for (const { z, a, b } of quad) {
      const c = sign * (obj.terms.get(z.id) ?? 0);
      if (c === 0) continue;
      for (const [i, ci] of a.terms) {
        for (const [j, cj] of b.terms) {
          const v = c * ci * cj;
          if (v === 0) continue;
          const key = Math.min(i, j) * n + Math.max(i, j);
          entries.set(key, (entries.get(key) ?? 0) + (i === j ? 2 * v : v));
        }
        if (b.constant) addLinear(i, c * ci * b.constant);
      }
      if (a.constant) for (const [j, cj] of b.terms) addLinear(j, c * a.constant * cj);
      constant += c * a.constant * b.constant;
    }
    const h: Hessian = { i: [], j: [], v: [] };
    for (const [key, v] of entries) {
      if (v === 0) continue;
      h.i.push(Math.floor(key / n));
      h.j.push(key % n);
      h.v.push(v);
    }
    return { h, linear, constant };
  }

  private solveLinear(obj: LinExpr): SolveInfo {
    const lp = this.linearProgram(obj);
    if (this.relaxed) lp.integer.fill(0);
    const sense = this.objective?.sense ?? null;
    const t0 = performance.now();
    const h = this.quad.length ? this.quadraticPart(obj, this.quad).h : null;
    const res = h
      ? solveMIQP(lp, h, { timeLimit: this.solveSeconds() })
      : solveMIP(lp, { nodeSelection: this.options.nodeSelection, timeLimit: this.solveSeconds() });
    const time = (performance.now() - t0) / 1000;
    const sign = sense === 'maximize' ? -1 : 1;
    const ok = res.status === 'optimal' || res.status === 'feasible';
    if (ok) {
      this.vars.forEach((v, j) => {
        v.value = clean(res.x[j]) + 0;
        v.rc = clean(sign * res.reducedCosts[j]) + 0;
      });
      const valueOf = (e: LinExpr) => {
        let s = e.constant;
        for (const [id, c] of e.terms) s += c * this.vars[id].value;
        return s;
      };
      for (const { z, a, b } of this.quad) z.value = clean(valueOf(a) * valueOf(b)) + 0;
      this.rows.forEach((row, i) => {
        if (!row.ref) return;
        let act = 0;
        for (const [id, c] of row.expr.terms) act += c * this.vars[id].value;
        row.ref.activity = clean(act) + 0;
        row.ref.dual = clean(sign * res.duals[i]) + 0;
        row.ref.slack = clean(isFinite(row.upper) ? row.upper - act : act - row.lower) + 0;
      });
    }
    const numIntVars = lp.integer.reduce((a, b) => a + b, 0);
    this.lastSolve = {
      status: this.objective ? res.status : 'none',
      solver: h ? (numIntVars > 0 ? 'MIQP' : 'QP') : numIntVars > 0 ? 'MIP' : 'LP',
      sense,
      objective: ok ? clean(sign * res.objective) + 0 : NaN,
      objectiveType: this.objectiveType(),
      numVars: lp.numVars,
      numIntVars,
      numConstraints: lp.rows.length,
      iterations: res.iterations,
      nodes: res.nodes,
      fails: 0,
      choicePoints: 0,
      solutions: ok ? 1 : 0,
      time,
    };
    return this.lastSolve;
  }

  /**
   * CPLEX populate: solves, then fills the solution pool with the optimum and,
   * when every variable is an integer, further feasible solutions found by
   * enumeration (up to limit).  Returns the pool size.
   */
  populate(limit: number): number {
    const info = this.solve();
    if (!this.solved) return 0;
    const best = Float64Array.from(this.vars, (v) => v.value);
    let pool: Float64Array[] = [best];
    const implied = this.impliedIntegers();
    if (limit > 1 && this.vars.every((v) => v.isInt || implied.has(v.id))) {
      const res = solveCP(
        {
          vars: this.vars,
          decision: this.decision,
          rows: this.rows,
          cons: this.cpCons,
          defs: this.cpDefs,
          objective: null,
          maximize: false,
          activities: this.activities,
          selections: this.selections,
          search: null,
          ev: this.ev,
          scope: this.global,
        },
        { timeLimit: this.solveSeconds(), allSolutions: true, maxSolutions: limit },
      );
      const ids = this.decision.map((v) => v.id);
      const same = (a: Float64Array) => ids.every((i) => Math.abs(a[i] - best[i]) < 1e-9);
      pool = [best, ...res.solutions.filter((s) => !same(s))].slice(0, limit);
    }
    // The optimum (with its duals) stays loaded; setPoolSolution switches.
    this.solutions = pool;
    this.lastSolve = { ...info, solutions: pool.length };
    return pool.length;
  }

  private solveWithCP(obj: LinExpr): SolveInfo {
    const implied = this.impliedIntegers();
    for (const v of this.vars) {
      if (!v.isInt && !v.aux && !implied.has(v.id) && this.decision.includes(v) && (!isFinite(v.lb) || !isFinite(v.ub))) {
        this.warn(`float variable ${v.name} has no finite bounds; constraint programming limits it to +-1e9`);
        break;
      }
    }
    const sense = this.objective?.sense ?? null;
    const t0 = performance.now();
    const res = solveCP(
      {
        vars: this.vars,
        decision: this.decision,
        rows: this.rows,
        cons: this.cpCons,
        defs: this.cpDefs,
        objective: sense ? obj : null,
        maximize: sense === 'maximize',
        activities: this.activities,
        selections: this.selections,
        search: this.search,
        ev: this.ev,
        scope: this.global,
      },
      { timeLimit: this.solveSeconds(), allSolutions: this.options.allSolutions && !sense },
    );
    const time = (performance.now() - t0) / 1000;
    this.solutions = res.solutions;
    // The best solution is the last one found; when enumerating, start with the first.
    const enumerating = this.options.allSolutions && !sense;
    if (res.solutions.length) this.loadSolution(enumerating ? 0 : res.solutions.length - 1);
    const status: MIPStatus = res.status === 'limit' ? 'limit' : res.status;
    this.lastSolve = {
      status: this.objective ? status : 'none',
      solver: 'CP',
      sense,
      objective: sense && res.solutions.length ? clean(res.objective) + 0 : NaN,
      objectiveType: this.objectiveType(),
      numVars: this.vars.length,
      numIntVars: this.vars.filter((v) => v.isInt).length,
      numConstraints: this.rows.length + this.cpCons.length,
      iterations: 0,
      nodes: 0,
      fails: res.fails,
      choicePoints: res.choicePoints,
      solutions: res.solutions.length,
      time,
    };
    return this.lastSolve;
  }

  /** Makes solution k (of a constraint-programming solve) the current one. */
  loadSolution(k: number): void {
    const sol = this.solutions[k];
    if (!sol) fail(`there is no solution ${k + 1}`);
    this.vars.forEach((v, i) => {
      v.value = clean(sol[i]) + 0;
      v.rc = NaN;
    });
    for (const row of this.rows) {
      if (!row.ref) continue;
      let act = 0;
      for (const [id, c] of row.expr.terms) act += c * this.vars[id].value;
      row.ref.activity = clean(act) + 0;
      row.ref.slack = clean(isFinite(row.upper) ? row.upper - act : act - row.lower) + 0;
      row.ref.dual = NaN;
    }
  }

  get solutionCount(): number {
    return this.solutions.length;
  }

  private objectiveType(): Type {
    return this.objective?.e ? this.ev.typeOf(this.objective.e, this.global) : UNKNOWN;
  }

  /** The generated linear program in CPLEX LP format. */
  exportLP(): string {
    this.generate();
    const obj = this.objectiveExpr();
    this.tryLinearize(obj);
    if (this.usesCP) fail('this model uses constraint programming and has no LP form');
    const lp = this.linearProgram(obj);
    const rowNames = this.rows.map((r, i) => r.ref?.name ?? `c${i + 1}`);
    const title = `generated by opl-ts from ${path.basename(this.ast.file)}`;
    const h = this.quad.length ? this.quadraticPart(obj, this.quad).h : null;
    return toLpFormat(lp, this.objective?.sense === 'maximize', this.vars.map((v) => v.name), rowNames, title, h);
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
    this.writeToSinks();
    for (const sheet of this.sheets) sheet.save();
  }

  reset(): void {
    this.lastSolve = null;
    this.solutions = [];
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

  /** Prints every decision variable and activity (what OPL Studio shows when there is no display). */
  printVariables(hideZero: boolean): void {
    for (const name of this.varNames) {
      const b = this.global.lookup(name)!;
      this.printValue(name, b.value, b.type, hideZero);
    }
  }

  private flatten(v: Value): Value[] {
    if (v instanceof DVar) return [dvarValue(v)];
    if (v instanceof OplArray || v instanceof RawArray) return v.items.flatMap((x) => this.flatten(x));
    if (v instanceof OplTuple) return v.values.flatMap((x) => this.flatten(x));
    if (v instanceof OplSet) return v.elems.flatMap((x) => this.flatten(x));
    if (v instanceof Activity) return [v.start.value, typeof v.duration === 'number' ? v.duration : v.duration.value, v.end.value];
    if (typeof v === 'number' || typeof v === 'string') return [v];
    fail(`cannot write a ${typeName(v)}`);
  }

  /**
   * The current solution for display: declared decision variables and the
   * scheduled activities, with the resources each one uses.
   */
  solutionSummary(): {
    variables: { name: string; value: number; isInt: boolean }[];
    activities: { name: string; start: number; end: number; resources: string[] }[];
  } {
    const variables = this.decision.filter((v) => !v.aux).map((v) => ({ name: v.name, value: v.value, isInt: v.isInt }));
    const uses = new Map<Activity, string[]>();
    const walk = (c: unknown): void => {
      if (!c || typeof c !== 'object') return;
      if (Array.isArray(c)) return c.forEach(walk);
      const o = c as Record<string, unknown>;
      if (o.k === 'uses' && o.act instanceof Activity && o.res instanceof Resource) {
        // Alternative resources: only the selected one.
        if (o.presence instanceof DVar && o.presence.value !== 1) return;
        const list = uses.get(o.act) ?? [];
        if (!list.includes(o.res.name)) list.push(o.res.name);
        uses.set(o.act, list);
        return;
      }
      if (typeof o.k === 'string') for (const v of Object.values(o)) if (v && typeof v === 'object' && !(v instanceof DVar) && !(v instanceof LinExpr)) walk(v);
    };
    walk(this.cpCons);
    const activities = this.activities
      .filter((a) => !a.presence || a.presence.value === 1)
      .map((a) => ({ name: a.name, start: a.start.value, end: a.end.value, resources: uses.get(a) ?? [] }));
    return { variables, activities };
  }

  // ------------------------------------------------------------ HostObject (OPLScript access)

  getField(name: string): Binding | undefined {
    this.initData();
    return this.global.lookup(name);
  }
}

/** Nested arrays of constraint references from labelled constraints inside forall. */
function labelArray(entries: { path: Value[]; ref: ConstraintRef }[], depth: number): Value {
  if (entries[0].path.length <= depth) return entries[0].ref;
  const keys = new OplSet();
  const groups = new Map<string, { path: Value[]; ref: ConstraintRef }[]>();
  for (const e of entries) {
    const k = keyOf(e.path[depth]);
    if (!groups.has(k)) {
      groups.set(k, []);
      keys.add(e.path[depth]);
    }
    groups.get(k)!.push(e);
  }
  return new OplArray(keys, keys.elems.map((k) => labelArray(groups.get(keyOf(k))!, depth + 1)));
}

function isCumulDecl(st: Extract<Stmt, { k: 'data' }>): boolean {
  return st.type.k === 'named' && st.type.name === 'cumulFunction' && st.init?.k === 'expr';
}

function holdsConstraints(a: OplArray): boolean {
  const first = a.items[0];
  return first instanceof ConstraintRef || (first instanceof OplArray && holdsConstraints(first));
}

function keyPath(p: Value[]): string {
  return p.map((x) => `[${formatValue(x, UNKNOWN, 'key')}]`).join('');
}

function leaves(v: Value): Value[] {
  if (v instanceof OplArray || v instanceof RawArray) return v.items.flatMap(leaves);
  return [v];
}

function indexKeyType(set: OplArray['index']): Type {
  return set instanceof OplSet && set.elemType ? set.elemType : UNKNOWN;
}
