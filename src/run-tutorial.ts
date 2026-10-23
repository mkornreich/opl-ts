/**
 * Runs every file of the OPL Studio tutorial folder: the stand-alone models,
 * the projects and the scripts.
 *
 * usage: run-tutorial [source-dir] [work-dir]
 *
 * The files are copied to work-dir first (default: source-dir/../run), because
 * the script and SheetWrite overwrite ouput.txt and the spreadsheet, just as
 * OPL Studio did; pass the same directory twice to run them in place.
 */

import * as fs from 'node:fs';
import * as path from 'node:path';
import { OplError } from './errors.js';
import { readProject } from './project.js';
import { runFile } from './runner.js';

const source = path.resolve(process.argv[2] ?? 'tutorial/files');
const dir = path.resolve(process.argv[3] ?? path.join(source, '..', 'run'));
if (dir !== source) {
  fs.mkdirSync(dir, { recursive: true });
  for (const f of fs.readdirSync(source)) fs.copyFileSync(path.join(source, f), path.join(dir, f));
  console.log(`Running a copy of ${path.relative(process.cwd(), source) || source} in ${path.relative(process.cwd(), dir) || dir}`);
}

const ls = (ext: string) =>
  fs.readdirSync(dir).filter((f) => f.toLowerCase().endsWith(ext)).sort((a, b) => a.localeCompare(b, 'en', { numeric: true }));

const warn = (m: string) => console.log(`  (note: ${m})`);
const projects = ls('.prj');
const projectModels = new Set(projects.map((p) => path.basename(readProject(path.join(dir, p), () => {}).model)));
const runs = [...ls('.mod').filter((m) => !projectModels.has(m)), ...projects, ...ls('.osc')];

let failures = 0;
for (const f of runs) {
  console.log(`\n=== ${f} ===`);
  try {
    runFile(path.join(dir, f), [], { warn });
  } catch (e) {
    if (!(e instanceof OplError)) throw e;
    failures++;
    console.log(`error: ${e.message}`);
  }
}
console.log(`\n${runs.length - failures}/${runs.length} tutorial files ran successfully.`);
process.exitCode = failures ? 1 : 0;
