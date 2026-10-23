/**
 * OPL Studio project files (.prj): `MODEL = "x.mod"`, `DATA = "x.dat"` plus
 * IDE / solver settings such as `hide_zero = 1` or `nodeSel = 0`.
 */

import * as fs from 'node:fs';
import * as path from 'node:path';
import type { Warn } from './files.js';
import { resolveInput } from './files.js';
import { ModelInstance, type ModelOptions } from './model.js';
import { parseData, parseModel } from './parser.js';

export interface Project {
  file: string;
  model: string;
  data: string[];
  settings: Map<string, string>;
}

export function readProject(file: string, warn: Warn): Project {
  const dir = path.dirname(path.resolve(file));
  const settings = new Map<string, string>();
  let model: string | null = null;
  const data: string[] = [];
  for (const raw of fs.readFileSync(file, 'utf8').split(/\r?\n/)) {
    const m = /^\s*([A-Za-z_][\w]*)\s*=\s*(.*?)\s*$/.exec(raw);
    if (!m) continue;
    let value = m[2];
    // Quoted values; a trailing backslash before the quote is part of a Windows path.
    if (value.startsWith('"') && value.endsWith('"') && value.length >= 2) value = value.slice(1, -1);
    if (m[1] === 'MODEL') model = resolveInput(value, dir, warn);
    else if (m[1] === 'DATA') data.push(resolveInput(value, dir, warn));
    else settings.set(m[1], value);
  }
  if (!model) throw new Error(`${file}: project has no MODEL entry`);
  return { file, model, data, settings };
}

/** Parses a model and its data files into a ModelInstance. */
export function loadModel(modelFile: string, dataFiles: string[], options: Omit<ModelOptions, 'baseDir'> & { baseDir?: string }): ModelInstance {
  const ast = parseModel(fs.readFileSync(modelFile, 'utf8'), modelFile);
  const data = dataFiles.map((f) => parseData(fs.readFileSync(f, 'utf8'), f));
  return new ModelInstance(ast, data, { ...options, baseDir: options.baseDir ?? path.dirname(path.resolve(modelFile)) });
}
