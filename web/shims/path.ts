/** POSIX path functions for the browser build (the working directory is /work). */

export const sep = '/';

function normalizeParts(parts: string[]): string[] {
  const out: string[] = [];
  for (const p of parts) {
    if (p === '' || p === '.') continue;
    if (p === '..') out.pop();
    else out.push(p);
  }
  return out;
}

export function normalize(p: string): string {
  const abs = p.startsWith('/');
  const s = normalizeParts(p.replace(/\\/g, '/').split('/')).join('/');
  return abs ? '/' + s : s || '.';
}

export function isAbsolute(p: string): boolean {
  return p.startsWith('/');
}

export function resolve(...parts: string[]): string {
  let p = '';
  for (let i = parts.length - 1; i >= 0 && !p.startsWith('/'); i--) {
    if (parts[i]) p = p ? `${parts[i]}/${p}` : parts[i];
  }
  if (!p.startsWith('/')) p = `/work/${p}`;
  return normalize(p);
}

export function join(...parts: string[]): string {
  return normalize(parts.filter(Boolean).join('/'));
}

export function dirname(p: string): string {
  const s = p.replace(/\/+$/, '');
  const i = s.lastIndexOf('/');
  return i < 0 ? '.' : i === 0 ? '/' : s.slice(0, i);
}

export function basename(p: string, ext?: string): string {
  const b = p.replace(/\/+$/, '').split('/').pop() ?? '';
  return ext && b.endsWith(ext) ? b.slice(0, -ext.length) : b;
}

export function extname(p: string): string {
  const b = basename(p);
  const i = b.lastIndexOf('.');
  return i > 0 ? b.slice(i) : '';
}

export function relative(from: string, to: string): string {
  const a = resolve(from).split('/').filter(Boolean);
  const b = resolve(to).split('/').filter(Boolean);
  let i = 0;
  while (i < a.length && i < b.length && a[i] === b[i]) i++;
  return [...a.slice(i).map(() => '..'), ...b.slice(i)].join('/');
}

export default { sep, normalize, isAbsolute, resolve, join, dirname, basename, extname, relative };
