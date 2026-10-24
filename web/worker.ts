/**
 * Web worker that runs OPL models with opl-ts: the page posts the files of a
 * model, the worker loads them into the in-memory file system, runs the model
 * the way the command line does and posts back the output and the solution.
 */

import { OplError } from '../src/errors.js';
import { runFile, statsLine } from '../src/runner.js';
import { reset, writtenFiles } from './shims/fs.js';

export interface RunRequest {
  files: Record<string, string>;
  main: string;
  data: string[];
  timeLimit: number;
  forceCP: boolean;
}

export interface RunReply {
  output: string;
  error: string | null;
  solve: {
    status: string;
    solver: string;
    sense: string | null;
    objective: number;
    stats: string;
  } | null;
  variables: { name: string; value: number; isInt: boolean }[];
  activities: { name: string; start: number; end: number; resources: string[] }[];
  written: Record<string, string>;
  ms: number;
}

const WORK = '/work/';

self.onmessage = (e: MessageEvent<RunRequest>) => {
  const req = e.data;
  const t0 = performance.now();
  reset(Object.fromEntries(Object.entries(req.files).map(([name, text]) => [WORK + name, text])));
  let output = '';
  const reply: RunReply = { output: '', error: null, solve: null, variables: [], activities: [], written: {}, ms: 0 };
  try {
    const r = runFile(WORK + req.main, req.data.map((d) => WORK + d), {
      write: (t) => (output += t),
      warn: (m) => (output += `warning: ${m}\n`),
      timeLimit: req.timeLimit,
      forceCP: req.forceCP,
      stats: true,
    });
    if (r.solve) {
      reply.solve = {
        status: r.solve.status,
        solver: r.solve.solver,
        sense: r.solve.sense,
        objective: r.solve.objective,
        stats: statsLine(r.solve),
      };
    }
    if (r.model) {
      const s = r.model.solutionSummary();
      reply.variables = s.variables;
      reply.activities = s.activities;
    }
  } catch (err) {
    reply.error = (err instanceof OplError ? err.message : err instanceof Error ? `${err.name}: ${err.message}` : String(err)).split(WORK).join('');
  }
  reply.output = output.split(WORK).join('');
  for (const [p, text] of Object.entries(writtenFiles())) {
    const name = p.startsWith(WORK) ? p.slice(WORK.length) : p;
    if (req.files[name] !== text) reply.written[name] = text;
  }
  reply.ms = performance.now() - t0;
  postMessage(reply);
};
