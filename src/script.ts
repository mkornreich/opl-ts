/**
 * OPLScript (.osc): solves sequences of models, changes their data in
 * editMode, and writes results with `cout << ...` or to `ofile`s.
 */

import * as fs from 'node:fs';
import * as path from 'node:path';
import type { Expr, ScriptAst, ScriptStmt } from './ast.js';
import { fail } from './errors.js';
import { Evaluator, Scope } from './eval.js';
import { resolveInput, resolveOutput, type Warn } from './files.js';
import type { ModelInstance } from './model.js';
import { printExpr } from './print.js';
import { loadModel, readProject } from './project.js';
import {
  FLOAT, formatValue, INT, indexType, OplArray, OplRange, UNKNOWN,
  type Binding, type HostObject, type Type, type Value,
} from './values.js';

export interface ScriptOptions {
  /** Directory the script's file names are resolved against. */
  baseDir: string;
  /** Receives everything written to cout (and display output). */
  write?: (text: string) => void;
  warn?: Warn;
  nodeSelection?: number;
}

class ScriptModel implements HostObject {
  readonly hostKind = 'Model';
  constructor(
    readonly name: string,
    readonly instance: ModelInstance,
    readonly editMode: boolean,
  ) {}

  getField(name: string): Binding | undefined {
    return this.instance.getField(name);
  }

  callMethod(name: string, args: Value[]): Binding {
    const inst = this.instance;
    const noArgs = () => {
      if (args.length) fail(`${this.name}.${name}() takes no arguments`);
    };
    switch (name) {
      case 'solve': {
        noArgs();
        inst.reset();
        inst.solve();
        inst.postProcess();
        return { value: inst.solved ? 1 : 0, type: INT };
      }
      case 'objectiveValue':
      case 'getObjValue':
        noArgs();
        if (!inst.solved) fail(`${this.name}.${name}(): the model has no solution`);
        return { value: inst.lastSolve!.objective, type: FLOAT };
      case 'getTime':
        noArgs();
        return { value: inst.lastSolve?.time ?? 0, type: FLOAT };
      case 'getNumberOfIterations':
        noArgs();
        return { value: inst.lastSolve?.iterations ?? 0, type: INT };
      case 'getNumberOfNodes':
        noArgs();
        return { value: inst.lastSolve?.nodes ?? 0, type: INT };
      case 'reset':
      case 'restore':
        noArgs();
        inst.reset();
        return { value: 0, type: INT };
    }
    fail(`Model has no method '${name}'`);
  }
}

class OutputFile implements HostObject {
  readonly hostKind = 'ofile';
  private fd: number | null;
  constructor(readonly file: string) {
    this.fd = fs.openSync(file, 'w');
  }
  write(text: string): void {
    if (this.fd === null) fail(`${this.file} is closed`);
    fs.writeSync(this.fd, text);
  }
  close(): void {
    if (this.fd !== null) fs.closeSync(this.fd);
    this.fd = null;
  }
  callMethod(name: string): Binding {
    if (name !== 'close') fail(`ofile has no method '${name}'`);
    this.close();
    return { value: 0, type: INT };
  }
}

class ConsoleStream implements HostObject {
  readonly hostKind = 'ostream';
  constructor(readonly write: (text: string) => void) {}
}

export class ScriptRunner {
  private readonly ev = new Evaluator();
  private readonly global = new Scope();
  private readonly files: OutputFile[] = [];
  private readonly models: ScriptModel[] = [];
  private readonly write: (text: string) => void;
  private readonly warn: Warn;

  constructor(
    private readonly ast: ScriptAst,
    private readonly options: ScriptOptions,
  ) {
    this.ev.phase = 'post';
    this.write = options.write ?? ((t) => process.stdout.write(t));
    this.warn = options.warn ?? ((m) => console.error(`warning: ${m}`));
    // Enum values of the script's models (e.g. m.need[cal]) are visible in the script.
    this.global.fallback = (name) => {
      for (const model of this.models) {
        const b = model.instance.getField(name);
        if (b?.type.k === 'enum') return b;
      }
      return undefined;
    };
    const cout = new ConsoleStream(this.write);
    this.global.define('cout', { value: cout, type: { k: 'host' } });
    this.global.define('cerr', { value: new ConsoleStream((t) => process.stderr.write(t)), type: { k: 'host' } });
  }

  run(): void {
    try {
      this.block(this.ast.stmts, this.global);
    } finally {
      for (const f of this.files) f.close();
    }
  }

  private block(stmts: ScriptStmt[], s: Scope): void {
    for (const st of stmts) this.exec(st, s);
  }

  private exec(st: ScriptStmt, s: Scope): void {
    const ev = this.ev;
    switch (st.k) {
      case 'model': {
        const dir = this.options.baseDir;
        const [first, ...rest] = st.files.map((f) => resolveInput(f, dir, this.warn, st.pos));
        const opts = { baseDir: dir, warn: this.warn, nodeSelection: this.options.nodeSelection, out: (l: string) => this.write(l + '\n') };
        let instance: ModelInstance;
        if (first.toLowerCase().endsWith('.prj')) {
          const prj = readProject(first, this.warn);
          instance = loadModel(prj.model, [...prj.data, ...rest], { ...opts, baseDir: path.dirname(prj.model) });
        } else {
          instance = loadModel(first, rest, opts);
        }
        const model = new ScriptModel(st.name, instance, st.editMode);
        this.models.push(model);
        s.define(st.name, { value: model, type: { k: 'host' } });
        return;
      }
      case 'ofile': {
        const p = ev.eval(st.path, s);
        if (typeof p !== 'string') fail('ofile needs a file name', st.pos);
        const f = new OutputFile(resolveOutput(p, this.options.baseDir, this.warn));
        this.files.push(f);
        s.define(st.name, { value: f, type: { k: 'host' } });
        return;
      }
      case 'decl': {
        const base = ev.resolveType(st.type, s);
        const sets = ev.indexSets(st.dims, s);
        const type: Type = sets.length ? { k: 'array', of: base, dims: sets } : base;
        const value = st.init ? ev.shape(ev.eval(st.init, s), type, st.init.pos) : ev.defaultValue(type);
        s.define(st.name, { value, type });
        return;
      }
      case 'range': {
        const v = ev.eval(st.e, s);
        if (!(v instanceof OplRange)) fail(`range ${st.name} must be a range lo..hi`, st.pos);
        s.define(st.name, { value: v, type: { k: 'range' } });
        return;
      }
      case 'assign':
        this.assign(st.target, ev.eval(st.e, s), s);
        return;
      case 'output': {
        const target = ev.evalRef(st.target, s);
        let text = '';
        for (const item of st.items) {
          if (item === 'endl') {
            text += '\n';
            continue;
          }
          const { value, type } = ev.evalTyped(item, s);
          text += formatValue(value, type, 'stream');
        }
        if (target instanceof ConsoleStream || target instanceof OutputFile) target.write(text);
        else fail(`cannot write to ${printExpr(st.target)}`, st.pos);
        return;
      }
      case 'expr':
        ev.evalTyped(st.e, s);
        return;
      case 'forall':
        ev.forEach(st.q, s, (sc) => this.block(st.body, sc));
        return;
      case 'while':
        while (ev.truthy(st.c, s)) this.block(st.body, new Scope(s));
        return;
      case 'repeat':
        do this.block(st.body, new Scope(s));
        while (!ev.truthy(st.c, s));
        return;
      case 'if':
        this.block(ev.truthy(st.c, s) ? st.then : st.else, new Scope(s));
        return;
      case 'display': {
        const emit = (sc: Scope) => {
          const { value, type } = ev.evalTyped(st.e, sc);
          this.write(`${printExpr(st.e)} = ${formatValue(value, type, 'display')}\n`);
        };
        if (st.q) ev.forEach(st.q, s, emit);
        else emit(s);
        return;
      }
    }
  }

  /** target := value, for script variables and (in editMode) model data. */
  private assign(target: Expr, value: Value, s: Scope): void {
    const ev = this.ev;
    const root = rootOf(target);
    const rootValue = root ? s.lookup(root)?.value : undefined;
    if (rootValue instanceof ScriptModel && !rootValue.editMode) {
      fail(`model ${rootValue.name} must be declared with editMode to change its data`, target.pos);
    }
    if (target.k === 'id') {
      const b = s.lookup(target.name);
      if (!b) fail(`unknown identifier '${target.name}'`, target.pos);
      b.value = ev.shape(value, b.type, target.pos);
      return;
    }
    if (target.k === 'field') {
      const obj = ev.evalRef(target.target, s);
      const b = obj instanceof ScriptModel ? obj.getField(target.name) : undefined;
      if (!b) fail(`cannot assign to ${printExpr(target)}`, target.pos);
      b.value = ev.shape(value, b.type, target.pos);
      return;
    }
    if (target.k === 'index') {
      let container = ev.evalRef(target.target, s);
      const keys = target.args.map((a) => ev.eval(a, s));
      for (const k of keys.slice(0, -1)) container = ev.indexInto(container, k, target.pos);
      if (!(container instanceof OplArray)) fail(`cannot assign to ${printExpr(target)}`, target.pos);
      const i = container.index.indexOf(keys[keys.length - 1]);
      if (i < 0) fail(`index ${formatValue(keys[keys.length - 1], UNKNOWN, 'display')} is out of bounds`, target.pos);
      const t = indexType(ev.typeOf(target.target, s), target.args.length);
      container.items[i] = ev.shape(value, t, target.pos);
      return;
    }
    fail(`cannot assign to ${printExpr(target)}`, target.pos);
  }
}

function rootOf(e: Expr): string | null {
  switch (e.k) {
    case 'id':
      return e.name;
    case 'index':
    case 'field':
      return rootOf(e.target);
  }
  return null;
}
