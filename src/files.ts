/**
 * File-name resolution.  The tutorial files refer to absolute Windows paths
 * such as "E:\Program Files\examples\opl\Tutorial-1.203J\simple_project1.xls";
 * when such a path does not exist here, the file of the same name next to the
 * referencing file is used instead.
 */

import * as fs from 'node:fs';
import * as path from 'node:path';
import { fail, type SourcePos } from './errors.js';

export type Warn = (message: string) => void;

const WINDOWS_ABSOLUTE = /^[A-Za-z]:[\\/]|^\\\\/;

/** A path for messages: relative to the working directory when that is shorter. */
function show(p: string): string {
  const rel = path.relative(process.cwd(), p);
  return rel && !rel.startsWith('..') ? rel : p;
}

function baseName(p: string): string {
  return p.split(/[\\/]/).pop() ?? p;
}

export function resolveInput(p: string, baseDir: string, warn: Warn, pos?: SourcePos): string {
  if (!WINDOWS_ABSOLUTE.test(p)) {
    const direct = path.resolve(baseDir, p);
    if (fs.existsSync(direct)) return direct;
  }
  const local = path.join(baseDir, baseName(p));
  if (fs.existsSync(local)) {
    warn(`"${p}" not found, using ${show(local)}`);
    return local;
  }
  fail(`file not found: ${p}`, pos);
}

export function resolveOutput(p: string, baseDir: string, warn: Warn): string {
  if (!WINDOWS_ABSOLUTE.test(p)) {
    const direct = path.resolve(baseDir, p);
    if (fs.existsSync(path.dirname(direct))) return direct;
  }
  const local = path.join(baseDir, baseName(p));
  warn(`cannot write "${p}" here, writing ${show(local)}`);
  return local;
}
