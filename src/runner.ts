/**
 * Runs a project, model or script file the way OPL Studio would, printing
 * the solution window contents.
 */

import * as fs from 'node:fs';
import * as path from 'node:path';
import type { Warn } from './files.js';
import type { ModelInstance, SolveInfo } from './model.js';
import { loadModel, readProject } from './project.js';
import { parseScript } from './parser.js';
import { ScriptRunner } from './script.js';
import { formatValue } from './values.js';

export interface RunOptions {
  /** Output sink for solution text. */
  write?: (text: string) => void;
  warn?: Warn;
  /** Print solver statistics. */
  stats?: boolean;
  /** List all variables even when the model has display statements. */
  listVariables?: boolean;
  hideZero?: boolean;
  nodeSelection?: number;
  timeLimit?: number;
  input?: (prompt: string) => string | null;
  /** Also write the generated problem to this file in CPLEX LP format. */
  exportLp?: string;
  /** Solve with constraint programming even when the model is linear. */
  forceCP?: boolean;
  /** Constraint programming without objective: print every solution. */
  allSolutions?: boolean;
  /** Allow IloOplExec in scripts. */
  allowExec?: boolean;
}

export interface RunResult {
  kind: 'model' | 'script';
  model?: ModelInstance;
  solve?: SolveInfo | null;
}

/** Runs a .prj, .mod (with optional .dat files) or .osc file. */
export function runFile(file: string, dataFiles: string[], options: RunOptions = {}): RunResult {
  const write = options.write ?? ((t) => process.stdout.write(t));
  const warn = options.warn ?? ((m) => console.error(`warning: ${m}`));
  const ext = path.extname(file).toLowerCase();
  // The time limit covers the whole run, however many solves a script makes.
  const deadline = options.timeLimit ? performance.now() + options.timeLimit * 1000 : undefined;

  if (ext === '.osc') {
    const ast = parseScript(fs.readFileSync(file, 'utf8'), file);
    new ScriptRunner(ast, {
      baseDir: path.dirname(path.resolve(file)),
      write,
      warn,
      nodeSelection: options.nodeSelection,
      deadline,
    }).run();
    return { kind: 'script' };
  }

  let modelFile = file;
  let data = dataFiles;
  let hideZero = options.hideZero ?? false;
  let nodeSelection = options.nodeSelection;
  if (ext === '.prj') {
    const prj = readProject(file, warn);
    modelFile = prj.model;
    data = [...prj.data, ...dataFiles];
    if (options.hideZero === undefined) hideZero = prj.settings.get('hide_zero') === '1';
    if (nodeSelection === undefined && prj.settings.has('nodeSel')) nodeSelection = Number(prj.settings.get('nodeSel'));
  }

  const model = loadModel(modelFile, data, {
    out: (line) => write(line + '\n'),
    write,
    warn,
    input: options.input,
    nodeSelection,
    deadline,
    forceCP: options.forceCP,
    allSolutions: options.allSolutions,
    allowExec: options.allowExec,
  });
  if (model.hasMain) {
    // The main block drives generation, solving and output.
    model.runMain();
    return { kind: 'model', model, solve: model.lastSolve };
  }
  model.initData();
  if (options.exportLp && model.hasObjective) fs.writeFileSync(options.exportLp, model.exportLP());
  if (!model.hasObjective) {
    model.postProcess();
    return { kind: 'model', model, solve: null };
  }
  const info = model.solve();
  const listVars = options.listVariables || !model.hasOutputStatements;
  if (options.allSolutions && info.solver === 'CP' && !info.sense) {
    write(`${info.solutions} solution${info.solutions === 1 ? '' : 's'} found\n`);
    for (let k = 0; k < model.solutionCount; k++) {
      model.loadSolution(k);
      write(`Solution [${k + 1}]\n`);
      model.postProcess();
      if (listVars) model.printVariables(hideZero);
    }
  } else {
    write(statusLine(info) + '\n');
    model.postProcess();
    if (model.solved && listVars) model.printVariables(hideZero);
  }
  if (options.stats ?? true) write(statsLine(info) + '\n');
  return { kind: 'model', model, solve: info };
}

export function statusLine(info: SolveInfo): string {
  const obj = formatValue(info.objective, info.objectiveType, 'display');
  switch (info.status) {
    case 'optimal':
      return info.sense ? `Optimal Solution with Objective Value: ${obj}` : 'Solution found';
    case 'feasible':
      return `Feasible Solution (limit reached) with Objective Value: ${obj}`;
    case 'infeasible':
      return 'No solution (the model is infeasible)';
    case 'unbounded':
      return 'No solution (the model is unbounded)';
    case 'limit':
      return 'No solution found within the limits';
    case 'none':
      return '';
  }
}

export function statsLine(info: SolveInfo): string {
  if (info.solver === 'CP') {
    return `[CP: ${info.numVars} variables, ${info.numConstraints} constraints; ` +
      `${info.choicePoints} choice points, ${info.fails} fails; ${info.time.toFixed(3)} s]`;
  }
  const ints = info.numIntVars > 0 ? ` (${info.numIntVars} integer)` : '';
  const nodes = info.numIntVars > 0 ? `, ${info.nodes} branch-and-bound nodes` : '';
  const what = info.solver === 'QP' || info.solver === 'MIQP' ? 'iterations' : 'simplex iterations';
  return `[${info.solver}: ${info.numVars} variables${ints}, ${info.numConstraints} constraints; ` +
    `${info.iterations} ${what}${nodes}; ${info.time.toFixed(3)} s]`;
}
