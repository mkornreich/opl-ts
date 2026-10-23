#!/usr/bin/env node
/**
 * opl: run OPL 3.x projects (.prj), models (.mod + .dat) and scripts (.osc).
 */

import * as fs from 'node:fs';
import { OplError } from './errors.js';
import { runFile, type RunOptions } from './runner.js';

const USAGE = `usage: opl [options] <project.prj | model.mod [data.dat ...] | script.osc>

options:
  -q, --quiet         do not print solver statistics
  -a, --all-vars      list all decision variables, even when the model has display statements
  -z, --hide-zero     do not list variables whose value is zero
      --node-sel N    branch-and-bound node selection: 0 = depth-first, 1 = best-bound
      --time-limit S  stop branch and bound after S seconds
      --export-lp F   also write the generated problem to F in CPLEX LP format
  -h, --help          show this help
`;

function readLineSync(prompt: string): string | null {
  process.stdout.write(prompt + ' ');
  const buf = Buffer.alloc(1);
  let line = '';
  for (;;) {
    let n: number;
    try {
      n = fs.readSync(0, buf, 0, 1, null);
    } catch {
      return line || null;
    }
    if (n === 0) return line || null;
    const c = buf.toString('utf8');
    if (c === '\n') return line;
    line += c;
  }
}

function main(argv: string[]): number {
  const options: RunOptions = { input: readLineSync };
  const files: string[] = [];
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    const value = () => {
      const v = argv[++i];
      if (v === undefined) throw new OplError(`${a} needs a value`);
      return Number(v);
    };
    switch (a) {
      case '-h':
      case '--help':
        process.stdout.write(USAGE);
        return 0;
      case '-q':
      case '--quiet':
        options.stats = false;
        break;
      case '-a':
      case '--all-vars':
        options.listVariables = true;
        break;
      case '-z':
      case '--hide-zero':
        options.hideZero = true;
        break;
      case '--node-sel':
        options.nodeSelection = value();
        break;
      case '--time-limit':
        options.timeLimit = value();
        break;
      case '--export-lp':
        options.exportLp = argv[++i];
        if (!options.exportLp) throw new OplError(`${a} needs a file name`);
        break;
      default:
        if (a.startsWith('-')) throw new OplError(`unknown option ${a}\n\n${USAGE}`);
        files.push(a);
    }
  }
  if (files.length === 0) {
    process.stderr.write(USAGE);
    return 2;
  }
  const [file, ...data] = files;
  runFile(file, data, options);
  return 0;
}

try {
  process.exitCode = main(process.argv.slice(2));
} catch (e) {
  if (e instanceof OplError) {
    console.error(`error: ${e.message}`);
    process.exitCode = 1;
  } else {
    throw e;
  }
}
