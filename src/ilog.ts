/**
 * IBM ILOG Script, the JavaScript dialect of `execute { ... }` and
 * `main { ... }` blocks, run with node:vm.
 *
 * Model data is exposed through proxies: arrays are indexed by their OPL
 * keys, sets and ranges have size / first() / next() ..., tuples have their
 * fields, and decision variables read as their solution value (a Number
 * carrying solutionValue, reducedCost, LB and UB).  ILOG Script's
 * `for (x in S)`, which iterates over the elements of S, is rewritten.
 */

import { execSync, spawn } from 'node:child_process';
import * as fs from 'node:fs';
import * as path from 'node:path';
import * as vm from 'node:vm';
import type { DataAst, ModelAst } from './ast.js';
import { Activity } from './cp/terms.js';
import { fail, OplError, type SourcePos } from './errors.js';
import { DExpr, dvarValue } from './eval.js';
import { resolveOutput } from './files.js';
import { ConstraintRef, DVar } from './linear.js';
import type { ModelInstance } from './model.js';
import { parseData, parseModel } from './parser.js';
import {
  EnumType, formatNumber, keyOf, OplArray, OplRange, OplSet, OplTuple, RawArray,
  type IndexSet, type Value,
} from './values.js';

const OPL = Symbol('opl');

type Wrapped = { [OPL]: Value };

function isWrapped(v: unknown): v is Wrapped {
  return (typeof v === 'object' || typeof v === 'function') && v !== null && OPL in (v as object);
}

/** Formats a value the way writeln does. */
export function scriptString(v: unknown): string {
  if (v === undefined) return 'undefined';
  if (v === null) return 'null';
  if (isWrapped(v)) return oplString(v[OPL], false);
  if (v instanceof Number) return String(v.valueOf());
  if (typeof v === 'number') return formatNumber(v, Number.isInteger(v), 'key');
  if (Array.isArray(v)) return '[' + v.map((x) => scriptString(x)).join(' ') + ']';
  return String(v);
}

function oplString(v: Value, inner: boolean): string {
  if (typeof v === 'number') return formatNumber(v, Number.isInteger(v), 'key');
  if (typeof v === 'string') return inner ? JSON.stringify(v) : v;
  if (v instanceof DVar) {
    const x = dvarValue(v);
    return typeof x === 'number' && Number.isNaN(x) ? v.name : oplString(x, inner);
  }
  if (v instanceof OplArray || v instanceof RawArray) return '[' + v.items.map((x) => oplString(x, true)).join(' ') + ']';
  if (v instanceof OplSet) return '{' + v.elems.map((x) => oplString(x, true)).join(' ') + '}';
  if (v instanceof EnumType) return '{' + v.values.join(' ') + '}';
  if (v instanceof OplRange) return `${v.lo}..${v.hi}`;
  if (v instanceof OplTuple) return '<' + v.values.map((x) => oplString(x, true)).join(' ') + '>';
  if (v instanceof Activity) {
    const n = (x: DVar | number) => (typeof x === 'number' ? x : x.value);
    return `<1 ${n(v.start)} ${n(v.end)} ${n(v.duration)}>`;
  }
  if (v instanceof ConstraintRef) return v.name;
  return String(v);
}

/** Rewrites `for (var x in e)` to iterate like ILOG Script (over OPL elements). */
export function rewriteForIn(code: string): string {
  const re = /\bfor\s*\(\s*((?:var|let|const)\s+)?([A-Za-z_$][\w$]*)\s+in\s+/g;
  let out = '';
  let last = 0;
  for (let m = re.exec(code); m; m = re.exec(code)) {
    // Find the parenthesis closing the for header.
    let depth = 1;
    let i = code.indexOf('(', m.index) + 1;
    for (; i < code.length && depth > 0; i++) {
      const c = code[i];
      if (c === '"' || c === "'") {
        for (i++; i < code.length && code[i] !== c; i++) if (code[i] === '\\') i++;
      } else if (c === '(') depth++;
      else if (c === ')') depth--;
    }
    const close = i - 1;
    const iterable = code.slice(m.index + m[0].length, close);
    out += code.slice(last, m.index) + `for (${m[1] ?? ''}${m[2]} of __in(${iterable}))`;
    last = close + 1;
    re.lastIndex = close + 1;
  }
  return out + code.slice(last);
}

/** The ILOG Script environment of one model (shared by its execute and main blocks). */
export class IlogRuntime {
  private readonly context: vm.Context;
  readonly cplexParams: Record<string, unknown> = {};
  readonly cpParams: Record<string, unknown> = {};

  constructor(
    readonly model: ModelInstance,
    readonly write: (text: string) => void,
  ) {
    const rt = this;
    const g: Record<string, unknown> = {
      writeln: (...a: unknown[]) => write(a.map(scriptString).join('') + '\n'),
      write: (...a: unknown[]) => write(a.map(scriptString).join('')),
      __in: (x: unknown) => rt.iterate(x),
      Opl: this.oplNamespace(),
      fail: () => fail('the script called fail()'),
      IloOplExec: (command: string, wait = true) => {
        if (!rt.model.options.allowExec) fail('IloOplExec runs shell commands; allow it with --allow-exec');
        if (!wait) {
          spawn(command, { shell: true, detached: true, stdio: 'ignore' }).unref();
          return 0;
        }
        try {
          write(execSync(command, { cwd: rt.model.options.baseDir, encoding: 'utf8' }));
          return 0;
        } catch (e) {
          return (e as { status?: number }).status ?? 1;
        }
      },
      thisOplModel: this.modelObject(model),
      IloOplModelSource: function (this: { file: string }, file: string) {
        this.file = rt.resolve(file);
      },
      IloOplModelDefinition: function (this: { ast: ModelAst }, src: { file: string }) {
        this.ast = parseModel(fs.readFileSync(src.file, 'utf8'), src.file);
      },
      IloOplDataSource: function (this: { ast: DataAst }, file: string) {
        const f = rt.resolve(file);
        this.ast = parseData(fs.readFileSync(f, 'utf8'), f);
      },
      // Data elements set on it (`data.n = 5`) override a model's data in addDataSource.
      IloOplDataElements: function () {
        const overrides = new Map<string, Value>();
        return new Proxy({} as Record<string | symbol, unknown>, {
          get: (_, p) => (p === OPL ? overrides : typeof p === 'string' && overrides.has(p) ? rt.toJS(overrides.get(p)!) : undefined),
          set: (_, p, v) => {
            if (typeof p === 'string') overrides.set(p, rt.fromJS(v));
            return true;
          },
          has: (_, p) => p === OPL || (typeof p === 'string' && overrides.has(p)),
        });
      },
      IloOplSettings: function () {},
      IloOplErrorHandler: function () {},
      IloCplex: function (this: object) {
        return rt.solverObject('cplex', rt.cplexParams);
      },
      IloCP: function (this: object) {
        return rt.solverObject('cp', rt.cpParams);
      },
      IloOplModel: function (def: { ast: ModelAst }, solver?: SolverObject) {
        const m = rt.model.childModel(def?.ast ?? rt.model.ast);
        const obj = m.scriptRuntime(write).modelObject(m);
        solver?.attach(m);
        return obj;
      },
      IloOplInputFile: function (this: Record<string, unknown>, file: string) {
        const lines = fs.readFileSync(rt.resolve(file), 'utf8').split(/\r?\n/);
        if (lines[lines.length - 1] === '') lines.pop();
        let i = 0;
        Object.defineProperty(this, 'eof', { get: () => i >= lines.length });
        this.readline = () => (i < lines.length ? lines[i++] : null);
        this.close = () => {};
      },
      IloOplOutputFile: function (this: Record<string, unknown>, file: string, append?: boolean) {
        const f = resolveOutput(file, rt.model.options.baseDir, rt.model.warn);
        const fd = fs.openSync(f, append ? 'a' : 'w');
        this.writeln = (...a: unknown[]) => fs.writeSync(fd, a.map(scriptString).join('') + '\n');
        this.write = (...a: unknown[]) => fs.writeSync(fd, a.map(scriptString).join(''));
        this.close = () => fs.closeSync(fd);
      },
    };
    this.context = vm.createContext(g);
    this.installVariableProperties();
    g.cplex = this.solverObject('cplex', this.cplexParams);
    g.cp = this.solverObject('cp', this.cpParams);
    (g.cplex as SolverObject).attach(model);
    (g.cp as SolverObject).attach(model);
  }

  private resolve(file: string): string {
    return path.resolve(this.model.options.baseDir, file);
  }

  /**
   * Runs a script.  In execute blocks the model's elements are visible by
   * name (`writeln(x)`); in main blocks they are reached through thisOplModel.
   */
  run(code: string, file: string, pos: SourcePos, execute = false): void {
    let src = rewriteForIn(code);
    if (execute) {
      (this.context as Record<string, unknown>).__elements = this.elementScope();
      src = `with (__elements) {${src}\n}`;
    }
    try {
      vm.runInContext(src, this.context, { filename: file, lineOffset: pos.line - 1 });
    } catch (e) {
      if (e instanceof OplError) throw e;
      const err = e as Error;
      const where = /:(\d+)/.exec(err.stack?.split('\n').find((l) => l.includes(file)) ?? '');
      fail(`script error: ${err.message}`, { ...pos, line: where ? Number(where[1]) : pos.line });
    }
  }

  /** The `with` scope of an execute block: model elements, with script assignments shadowing them. */
  private elementScope(): object {
    const m = this.model;
    const shadow = new Map<string, unknown>();
    const ctx = this.context as Record<string, unknown>;
    return new Proxy({} as Record<string | symbol, unknown>, {
      // Script globals shadow model elements (checked last: it is slow on the vm context).
      has: (_, prop) => typeof prop === 'string' && (shadow.has(prop) || !!m.getField(prop) || m.isGeneratedElement(prop)) && !(prop in ctx),
      get: (_, prop) => {
        if (typeof prop !== 'string') return undefined;
        if (shadow.has(prop)) return shadow.get(prop);
        const b = m.getField(prop);
        if (!b && m.isGeneratedElement(prop)) return this.placeholder(prop);
        return b ? this.toJS(m.fieldValue(prop) ?? b.value) : undefined;
      },
      set: (_, prop, value) => {
        if (typeof prop !== 'string') return true;
        // Assigning a scalar data element (`res = v[1]`) changes the model's data.
        const b = !shadow.has(prop) ? m.getField(prop) : undefined;
        const primitive = typeof value === 'number' || typeof value === 'string' || value instanceof Number;
        if (b && primitive && (typeof b.value === 'number' || typeof b.value === 'string') && b.type.k !== 'var') {
          b.value = this.fromJS(value);
          return true;
        }
        shadow.set(prop, value);
        return true;
      },
    });
  }

  /** A variable before generation (pre-processing): records x.LB / x.UB changes. */
  placeholderFor(name: string): unknown {
    return this.placeholder(name);
  }

  private placeholder(name: string): unknown {
    return new Proxy(function () {} as unknown as Record<string | symbol, unknown>, {
      get: (_, prop) => {
        if (prop === 'toString' || prop === Symbol.toPrimitive) return () => name;
        if (prop === 'name') return name;
        if (typeof prop !== 'string' || prop === 'LB' || prop === 'UB') return undefined;
        return this.placeholder(`${name}[${prop}]`);
      },
      set: (_, prop, value) => {
        if (prop === 'LB' || prop === 'UB') this.model.setBound(name, prop === 'LB' ? 'lb' : 'ub', Number(value));
        return true;
      },
    });
  }

  // ------------------------------------------------------------ conversions

  private readonly wrappers = new WeakMap<object, unknown>();

  toJS(v: Value): unknown {
    if (typeof v === 'number' || typeof v === 'string') return v;
    if (v instanceof DExpr) return this.toJS(this.model.resolveDExprs(v));
    if (v instanceof DVar) return this.dvar(v);
    if (v instanceof OplArray || v instanceof OplSet || v instanceof OplRange || v instanceof EnumType || v instanceof OplTuple) {
      // One wrapper per value: scripts read the same elements over and over.
      let w = this.wrappers.get(v);
      if (w === undefined) {
        w = v instanceof OplArray ? this.arrayProxy(v) : v instanceof OplTuple ? this.tupleProxy(v) : this.setObject(v);
        this.wrappers.set(v, w);
      }
      return w;
    }
    if (v instanceof ConstraintRef) {
      const m = this.model;
      const rt = this;
      return {
        [OPL]: v,
        name: v.name,
        get dual() { return v.dual; },
        get slack() { return v.slack; },
        get value() { return v.activity; },
        get LB() { return m.rowBounds(v).lb; },
        set LB(x: number) { m.setRowBound(v, 'lb', Number(x)); },
        get UB() { return m.rowBounds(v).ub; },
        set UB(x: number) { m.setRowBound(v, 'ub', Number(x)); },
        setCoef(x: unknown, c: number) { m.setRowCoef(v, rt.varArg(x), Number(c)); },
        setBounds(lb: number, ub: number) { m.setRowBound(v, 'lb', Number(lb)); m.setRowBound(v, 'ub', Number(ub)); },
      };
    }
    if (v instanceof Activity) {
      const n = (x: DVar | number) => (typeof x === 'number' ? x : x.value);
      return { [OPL]: v, get start() { return n(v.start); }, get end() { return n(v.end); }, get size() { return n(v.duration); }, present: 1 };
    }
    if (v instanceof RawArray) return v.items.map((x) => this.toJS(x));
    return v;
  }

  fromJS(v: unknown): Value {
    if (isWrapped(v)) {
      const x = v[OPL];
      return x instanceof DVar ? dvarValue(x) : x;
    }
    if (v instanceof Number) return v.valueOf();
    if (typeof v === 'number' || typeof v === 'string') return v;
    if (typeof v === 'boolean') return v ? 1 : 0;
    if (Array.isArray(v)) return new RawArray(v.map((x) => this.fromJS(x)));
    fail(`cannot use the script value ${String(v)} as OPL data`);
  }

  /**
   * A decision variable reads as its value, a plain number, so that `x[i] == y[j]`
   * compares values.  x[i].solutionValue / .reducedCost / .LB / .UB are served by
   * getters on the context's Number.prototype for the variable read last.
   */
  private dvar(v: DVar): unknown {
    const value = dvarValue(v);
    if (typeof value === 'string') return value;
    this.lastVar = v;
    return Number.isNaN(value) ? 0 : value;
  }

  private lastVar: DVar | null = null;

  /** A decision variable passed to a script method (ct.setCoef(x, ...)). */
  varArg(x: unknown): DVar {
    if (isWrapped(x) && x[OPL] instanceof DVar) return x[OPL] as DVar;
    if (this.lastVar) return this.lastVar;
    fail('script: expected a decision variable');
  }

  private installVariableProperties(): void {
    const proto = vm.runInContext('Number.prototype', this.context) as object;
    const rt = this;
    const current = (n: unknown): DVar | null => {
      const v = rt.lastVar;
      if (!v) return null;
      const value = dvarValue(v);
      return typeof value === 'number' && (Number(n) === value || (Number.isNaN(value) && Number(n) === 0)) ? v : null;
    };
    const prop = (get: (v: DVar) => unknown, set?: (v: DVar, x: number) => void) => ({
      configurable: true,
      get(this: unknown) {
        const v = current(this);
        return v ? get(v) : undefined;
      },
      set(this: unknown, x: number) {
        const v = current(this);
        if (v && set) set(v, x);
      },
    });
    Object.defineProperties(proto, {
      solutionValue: prop((v) => dvarValue(v)),
      reducedCost: prop((v) => v.rc),
      LB: prop((v) => v.lb, (v, x) => rt.model.setBound(v.name, 'lb', x)),
      UB: prop((v) => v.ub, (v, x) => rt.model.setBound(v.name, 'ub', x)),
      lb: prop((v) => v.lb),
      ub: prop((v) => v.ub),
    });
  }

  private keyFor(index: IndexSet, prop: string | symbol): Value | undefined {
    if (typeof prop !== 'string') return undefined;
    if (index instanceof OplRange) return Number(prop);
    if (index instanceof EnumType) return prop;
    const sample = index.size > 0 ? index.at(0) : undefined;
    if (typeof sample === 'number') return Number(prop);
    if (typeof sample === 'string' || sample === undefined) return prop;
    for (let i = 0; i < index.size; i++) if (keyOf(index.at(i)) === prop) return index.at(i);
    return undefined;
  }

  private arrayProxy(arr: OplArray): unknown {
    const rt = this;
    const target = function () {} as unknown as Record<string | symbol, unknown>;
    return new Proxy(target, {
      get(_, prop) {
        if (prop === OPL) return arr;
        if (prop === Symbol.iterator) return function* () { for (const x of arr.items) yield rt.toJS(x); };
        if (prop === 'toString' || prop === Symbol.toPrimitive) return () => oplString(arr, false);
        if (prop === 'size' || prop === 'length') return arr.items.length;
        const key = rt.keyFor(arr.index, prop);
        if (key === undefined) return undefined;
        const i = arr.index.indexOf(key);
        return i < 0 ? undefined : rt.toJS(arr.items[i]);
      },
      set(_, prop, value) {
        const key = rt.keyFor(arr.index, prop);
        const i = key === undefined ? -1 : arr.index.indexOf(key);
        if (i < 0) fail(`script: index ${String(prop)} is out of bounds`);
        arr.items[i] = rt.fromJS(value);
        return true;
      },
      has(_, prop) {
        if (prop === OPL) return true;
        const key = rt.keyFor(arr.index, prop);
        return key !== undefined && arr.index.indexOf(key) >= 0;
      },
    });
  }

  private tupleProxy(t: OplTuple): unknown {
    const rt = this;
    return new Proxy({} as Record<string | symbol, unknown>, {
      get(_, prop) {
        if (prop === OPL) return t;
        if (prop === 'toString' || prop === Symbol.toPrimitive) return () => keyOf(t);
        if (typeof prop !== 'string') return undefined;
        const i = t.struct?.index.get(prop) ?? (/^\d+$/.test(prop) ? Number(prop) : undefined);
        return i === undefined ? undefined : rt.toJS(t.values[i]);
      },
      set(_, prop) {
        fail(`script: tuple fields are read-only (${String(prop)})`);
      },
      has(_, prop) {
        return prop === OPL || (typeof prop === 'string' && !!t.struct?.index.has(prop));
      },
    });
  }

  private setObject(set: OplSet | OplRange | EnumType): unknown {
    const rt = this;
    const at = (i: number) => rt.toJS(set.at(i));
    const pos = (e: unknown) => set.indexOf(rt.fromJS(e));
    const obj: Record<string | symbol, unknown> = {
      [OPL]: set,
      get size() {
        return set.size;
      },
      first: () => at(0),
      last: () => at(set.size - 1),
      next: (e: unknown) => at(pos(e) + 1),
      prev: (e: unknown) => at(pos(e) - 1),
      nextc: (e: unknown) => at((pos(e) + 1) % set.size),
      prevc: (e: unknown) => at((pos(e) - 1 + set.size) % set.size),
      item: (i: number) => at(i),
      ord: (e: unknown) => pos(e),
      contains: (e: unknown) => pos(e) >= 0,
      clear: () => {
        if (!(set instanceof OplSet)) fail('script: only sets can be cleared');
        set.clear();
      },
      add: (...e: unknown[]) => {
        if (!(set instanceof OplSet)) fail('script: only sets can be extended');
        const v = e.length > 1 ? new OplTuple(set.elemType?.k === 'struct' ? set.elemType.s : null, e.map((x) => rt.fromJS(x))) : rt.fromJS(e[0]);
        set.add(v);
      },
      [Symbol.iterator]: function* () {
        for (let i = 0; i < set.size; i++) yield at(i);
      },
      toString: () => oplString(set, false),
    };
    obj.addOnly = obj.add;
    if (set instanceof OplRange) {
      obj.lb = set.lo;
      obj.ub = set.hi;
      obj.LB = set.lo;
      obj.UB = set.hi;
    }
    return obj;
  }

  /** `for (x in e)`: OPL arrays give their keys, sets their elements, other objects their keys. */
  *iterate(x: unknown): Generator<unknown> {
    if (isWrapped(x)) {
      const v = x[OPL];
      if (v instanceof OplArray) {
        for (let i = 0; i < v.index.size; i++) yield this.toJS(v.index.at(i));
        return;
      }
      if (v instanceof OplSet || v instanceof OplRange || v instanceof EnumType) {
        for (let i = 0; i < v.size; i++) yield this.toJS(v.at(i));
        return;
      }
    }
    if (x && typeof x === 'object') for (const k in x as object) yield k;
  }

  // ------------------------------------------------------------ objects

  private oplNamespace(): Record<string, unknown> {
    const rt = this;
    const set = (s: unknown) => (isWrapped(s) ? (s[OPL] as IndexSet) : fail('Opl: expected a set'));
    return {
      abs: Math.abs,
      ceil: Math.ceil,
      floor: Math.floor,
      round: Math.round,
      ftoi: Math.trunc,
      trunc: Math.trunc,
      sqrt: Math.sqrt,
      exp: Math.exp,
      log: Math.log,
      pow: Math.pow,
      minl: (...a: number[]) => Math.min(...a.map(Number)),
      maxl: (...a: number[]) => Math.max(...a.map(Number)),
      rand: (n: number) => Math.floor(Math.random() * n),
      srand: () => {},
      card: (s: unknown) => set(s).size,
      ord: (s: unknown, e: unknown) => set(s).indexOf(rt.fromJS(e)),
      first: (s: unknown) => rt.toJS(set(s).at(0)),
      last: (s: unknown) => rt.toJS(set(s).at(set(s).size - 1)),
      item: (s: unknown, i: number) => rt.toJS(set(s).at(i)),
      next: (s: unknown, e: unknown) => rt.toJS(set(s).at(set(s).indexOf(rt.fromJS(e)) + 1)),
      prev: (s: unknown, e: unknown) => rt.toJS(set(s).at(set(s).indexOf(rt.fromJS(e)) - 1)),
      typeof: (x: unknown) => typeof x,
    };
  }

  /** thisOplModel / IloOplModel objects. */
  modelObject(m: ModelInstance): unknown {
    const rt = m === this.model ? this : m.scriptRuntime(this.write);
    const methods: Record<string, unknown> = {
      generate: () => m.scriptGenerate(),
      postProcess: () => m.postProcess(),
      setPoolSolution: (k: number) => m.loadSolution(Number(k)),
      end: () => {},
      addDataSource: (ds: { ast?: DataAst } & Record<string, unknown>) => {
        if (ds?.ast) m.addData(ds.ast);
        else if (ds && (ds as Wrapped)[OPL] instanceof Map) m.addOverrides((ds as Wrapped)[OPL] as unknown as Map<string, Value>);
      },
      addSettings: () => {},
      applyOpsSettings: () => {},
      convertAllIntVars: () => m.setRelaxation(true),
      unconvertAllIntVars: () => m.setRelaxation(false),
      printSolution: () => m.printVariables(false),
      printConflict: () => {},
      get modelDefinition() {
        return { ast: m.ast };
      },
      get dataElements() {
        return rt.dataElements(m);
      },
      get settings() {
        return { mainEndEnabled: true, displayPrecision: 4 };
      },
      get name() {
        return path.basename(m.ast.file, '.mod');
      },
    };
    return new Proxy({} as Record<string | symbol, unknown>, {
      get(_, prop) {
        if (typeof prop !== 'string') return undefined;
        if (prop in methods) return methods[prop];
        const b = m.getField(prop);
        if (!b && m.isGeneratedElement(prop)) return rt.placeholderFor(prop);
        return b ? rt.toJS(m.fieldValue(prop) ?? b.value) : undefined;
      },
      has(_, prop) {
        return typeof prop === 'string' && (prop in methods || !!m.getField(prop));
      },
    });
  }

  /** thisOplModel.dataElements: data that can be changed and passed to a new model. */
  dataElements(m: ModelInstance): unknown {
    const rt = this;
    const overrides = new Map<string, Value>();
    return new Proxy({} as Record<string | symbol, unknown>, {
      get(_, prop) {
        if (prop === OPL) return overrides;
        if (typeof prop !== 'string') return undefined;
        if (overrides.has(prop)) return rt.toJS(overrides.get(prop)!);
        const b = m.getField(prop);
        if (!b) return undefined;
        const copy = m.copyData(prop);
        if (copy !== undefined) overrides.set(prop, copy);
        return rt.toJS(copy ?? b.value);
      },
      set(_, prop, value) {
        if (typeof prop === 'string') overrides.set(prop, rt.fromJS(value));
        return true;
      },
      has(_, prop) {
        return prop === OPL || (typeof prop === 'string' && !!m.getField(prop));
      },
    });
  }

  solverObject(kind: 'cplex' | 'cp', params: Record<string, unknown>): SolverObject {
    return new SolverObject(kind, params, this);
  }
}

/** The cplex / cp objects. */
export class SolverObject {
  private model: ModelInstance | null = null;
  private cursor = -1;
  readonly param: Record<string, unknown>;
  readonly factory: Record<string, unknown>;

  constructor(
    readonly kind: 'cplex' | 'cp',
    params: Record<string, unknown>,
    readonly rt: IlogRuntime,
  ) {
    this.param = new Proxy(params, {
      set: (t, p, v) => {
        t[p as string] = v;
        if (p === 'TimeLimit' && this.model) this.model.options.timeLimit = Number(v);
        return true;
      },
    });
    // Search phases are accepted; the solver uses its own (first-fail) labelling.
    this.factory = new Proxy({}, {
      get: (_, p) => (typeof p === 'string' && p !== 'toString' ? (...args: unknown[]) => ({ phase: [p, ...args] }) : undefined),
    });
    return new Proxy(this, {
      get: (t, p) => {
        if (typeof p === 'string' && p in t) {
          const v = (t as unknown as Record<string, unknown>)[p];
          return typeof v === 'function' ? (v as (...a: unknown[]) => unknown).bind(t) : v;
        }
        return typeof p === 'string' ? params[p] : undefined;
      },
      set: (t, p, v) => {
        params[p as string] = v;
        if ((p === 'tilim' || p === 'TimeLimit') && t.model) t.model.options.timeLimit = Number(v);
        return true;
      },
    });
  }

  attach(m: ModelInstance): void {
    this.model = m;
  }

  private current(): ModelInstance {
    if (!this.model) fail(`${this.kind}: no model was generated`);
    return this.model;
  }

  solve(): boolean {
    const m = this.current();
    m.solveForScript(false);
    this.cursor = m.solved ? 0 : -1;
    return m.solved;
  }

  startNewSearch(): void {
    const m = this.current();
    m.solveForScript(true);
    this.cursor = -1;
  }

  next(): boolean {
    const m = this.current();
    if (this.cursor + 1 >= m.solutionCount) return false;
    m.loadSolution(++this.cursor);
    return true;
  }

  /** Fills the solution pool (CPLEX populatelim, default 20). */
  populate(): boolean {
    const m = this.current();
    const limit = Number(this.param.populatelim ?? this.param.PopulateLim ?? 20);
    const n = m.populate(Number.isFinite(limit) && limit > 0 ? limit : 20);
    this.cursor = n ? 0 : -1;
    return n > 0;
  }

  get solnPoolNsolns(): number {
    return this.model?.solutionCount ?? 0;
  }
  solveFixed(): boolean {
    return this.model?.solved ?? false;
  }
  endSearch(): void {}
  end(): void {}
  setSearchPhases(): void {}
  setStartingPoint(): void {}
  setParam(): void {}
  setObjCoef(x: unknown, c: number): void {
    this.current().setObjCoef(this.rt.varArg(x), Number(c));
  }
  clearModel(): void {}
  printInformation(): void {}

  getObjValue(): number {
    const m = this.current();
    if (!m.lastSolve) fail(`${this.kind}.getObjValue(): no solution`);
    if (m.lastSolve.solver === 'CP' && m.solutionCount > 0 && this.cursor >= 0) return m.objectiveOf(this.cursor);
    return m.lastSolve.objective;
  }
  getBestObjValue(): number {
    return this.getObjValue();
  }
  getObjBound(): number {
    return this.getObjValue();
  }
  getMIPRelativeGap(): number {
    return 0;
  }
  getCplexStatus(): number {
    return this.model?.solved ? 1 : 3;
  }
  getStatus(): number {
    return this.getCplexStatus();
  }
  getSolvedStatus(): string {
    return this.model?.lastSolve?.status ?? 'unknown';
  }
  getCplexTime(): number {
    return performance.now() / 1000;
  }
  getNiterations(): number {
    return this.model?.lastSolve?.iterations ?? 0;
  }
  getNnodes(): number {
    return this.model?.lastSolve?.nodes ?? 0;
  }
  getValue(v: unknown): unknown {
    return v instanceof Number ? v.valueOf() : v;
  }
  exportModel(file: string): void {
    const m = this.current();
    // Only linear models have an LP form; CP models (.cpo) are not exported.
    if (m.lastSolve?.solver === 'CP' || this.kind === 'cp') return;
    fs.writeFileSync(path.resolve(m.options.baseDir, file), m.exportLP());
  }
  getInfo(name: string): number {
    return (this.info as Record<string, number>)[name] ?? 0;
  }

  get info(): Record<string, number> {
    const s = this.model?.lastSolve;
    return {
      NumberOfModelVariables: s?.numVars ?? 0,
      NumberOfVariables: s?.numVars ?? 0,
      NumberOfConstraints: s?.numConstraints ?? 0,
      NumberOfChoicePoints: s?.choicePoints ?? 0,
      NumberOfFails: s?.fails ?? 0,
      NumberOfBranches: s?.choicePoints ?? 0,
      NumberOfSolutions: s?.solutions ?? 0,
      SolveTime: s?.time ?? 0,
      TotalTime: s?.time ?? 0,
    };
  }
}
