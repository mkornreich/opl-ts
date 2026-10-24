/**
 * An in-memory file system standing in for node:fs in the browser build:
 * the worker loads the example's files under /work and reads back what the
 * model wrote.
 */

const files = new Map<string, string>();
const written = new Set<string>();
const open = new Map<number, string>();
let nextFd = 3;

function key(p: string | URL): string {
  return String(p).replace(/\\/g, '/');
}

function enoent(p: string): Error {
  const e = new Error(`ENOENT: no such file or directory, open '${p}'`) as Error & { code: string };
  e.code = 'ENOENT';
  return e;
}

/** Replaces the whole file system. */
export function reset(contents: Record<string, string>): void {
  files.clear();
  written.clear();
  open.clear();
  for (const [p, text] of Object.entries(contents)) files.set(key(p), text);
}

/** Files written since the last reset. */
export function writtenFiles(): Record<string, string> {
  const out: Record<string, string> = {};
  for (const p of written) out[p] = files.get(p) ?? '';
  return out;
}

export function readFileSync(p: string, _enc?: unknown): string {
  const f = files.get(key(p));
  if (f === undefined) throw enoent(String(p));
  return f;
}

export function writeFileSync(p: string, data: string | Uint8Array): void {
  const k = key(p);
  files.set(k, typeof data === 'string' ? data : new TextDecoder().decode(data));
  written.add(k);
}

export function existsSync(p: string): boolean {
  const k = key(p).replace(/\/+$/, '');
  if (files.has(k)) return true;
  for (const f of files.keys()) if (f.startsWith(k + '/')) return true;
  return false;
}

export function openSync(p: string, flags = 'r'): number {
  const k = key(p);
  if (flags.startsWith('r')) {
    if (!files.has(k)) throw enoent(k);
  } else if (flags.startsWith('w') || !files.has(k)) {
    files.set(k, '');
    written.add(k);
  }
  const fd = nextFd++;
  open.set(fd, k);
  return fd;
}

export function writeSync(fd: number, text: string): number {
  const k = open.get(fd);
  if (k === undefined) throw new Error('EBADF: bad file descriptor');
  files.set(k, (files.get(k) ?? '') + text);
  written.add(k);
  return text.length;
}

export function closeSync(fd: number): void {
  open.delete(fd);
}

export function mkdirSync(): void {}
