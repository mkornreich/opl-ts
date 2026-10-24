/**
 * Memory budget of the solvers, so a large model fails cleanly instead of
 * exhausting the machine.  The limit (in MB) comes from --memory-limit or the
 * OPL_MEMORY_LIMIT_MB environment variable; the default is 2048 MB.
 */

import { OplError } from '../errors.js';

export function memoryLimitBytes(): number {
  const mb = Number(process.env.OPL_MEMORY_LIMIT_MB);
  return (Number.isFinite(mb) && mb > 0 ? mb : 2048) * 1024 * 1024;
}

/** Memory in use: the V8 heap plus typed-array buffers. */
export function memoryInUse(): number {
  const m = process.memoryUsage();
  return m.heapUsed + m.arrayBuffers;
}

/** Throws when allocating `bytes` more would exceed the budget. */
export function reserve(bytes: number, what: string): void {
  const limit = memoryLimitBytes();
  if (memoryInUse() + bytes > limit) {
    const mb = (x: number) => Math.ceil(x / 1024 / 1024);
    throw new OplError(`${what} needs about ${mb(bytes)} MB, more than the memory limit of ${mb(limit)} MB allows (raise it with --memory-limit)`);
  }
}

/** True when allocating `bytes` more stays within the budget (for optional work such as a presolve). */
export function fits(bytes: number): boolean {
  return memoryInUse() + bytes <= memoryLimitBytes();
}

let warned = false;

/** True when the process is over its budget (long searches then stop with a limit status). */
export function memoryExceeded(): boolean {
  const over = memoryInUse() > memoryLimitBytes();
  if (over && !warned) {
    warned = true;
    console.error('warning: memory limit reached, stopping the search (raise it with --memory-limit)');
  }
  return over;
}

let ticks = 0;

/**
 * Called once per generated item (array cell, loop iteration): every 65536
 * calls, throws when the process is over its budget, so building a huge
 * model stops with an error instead of exhausting the machine.
 */
export function checkMemory(): void {
  if ((++ticks & 0xffff) !== 0) return;
  const limit = memoryLimitBytes();
  if (memoryInUse() > limit) {
    throw new OplError(`the model is too large: generating it needs more than the memory limit of ${Math.ceil(limit / 1024 / 1024)} MB (raise it with --memory-limit)`);
  }
}
