/**
 * Writes a LinearProgram in CPLEX LP format.
 */

import type { LinearProgram } from './lp.js';
import type { Hessian } from './qp.js';

/** LP-format safe, unique names. */
function sanitize(names: string[], prefix: string): string[] {
  const seen = new Set<string>();
  return names.map((n, i) => {
    let s = n.replace(/\]\[/g, '_').replace(/[^A-Za-z0-9_.]/g, (c) => (c === ']' ? '' : '_')) || `${prefix}${i + 1}`;
    if (/^[0-9.eE]/.test(s)) s = `${prefix}${s}`;
    // Section keywords of the LP format cannot be names.
    if (/^(max|min|maximize|minimize|maximum|minimum|st|subject|such|bounds?|generals?|gen|binary|binaries|bin|semi|semis|end|free|inf|infinity)$/i.test(s)) s = `${s}_`;
    let u = s;
    for (let k = 2; seen.has(u); k++) u = `${s}_${k}`;
    seen.add(u);
    return u;
  });
}

function num(v: number): string {
  return Number.isInteger(v) ? String(v) : String(+v.toPrecision(15));
}

function linear(index: number[], value: number[], names: string[]): string {
  const parts: string[] = [];
  index.forEach((j, k) => {
    const c = value[k];
    if (c === 0) return;
    const sign = c < 0 ? '-' : '+';
    parts.push(`${parts.length === 0 && sign === '+' ? '' : sign + ' '}${num(Math.abs(c))} ${names[j]}`);
  });
  return parts.length ? parts.join(' ') : `0 ${names[0] ?? ''}`.trim();
}

export function toLpFormat(
  lp: LinearProgram,
  maximize: boolean,
  varNames: string[],
  rowNames: string[],
  title = '',
  hessian: Hessian | null = null,
): string {
  const names = sanitize(varNames, 'x');
  const rows = sanitize(rowNames, 'c');
  const out: string[] = [];
  if (title) out.push(`\\ ${title}`);
  out.push(maximize ? 'Maximize' : 'Minimize');
  // The LinearProgram is stored as a minimisation; undo the negation for Maximize.
  const s = maximize ? -1 : 1;
  const objIdx: number[] = [];
  const objVal: number[] = [];
  lp.objective.forEach((c, j) => {
    if (c !== 0) {
      objIdx.push(j);
      objVal.push(s * c);
    }
  });
  const constant = s * lp.objConstant;
  // Quadratic part: [ sum of h x_i x_j ] / 2 with the full (doubled) off-diagonal coefficients.
  let quad = '';
  if (hessian && hessian.v.length) {
    const terms: string[] = [];
    for (let k = 0; k < hessian.v.length; k++) {
      const [i, j] = [hessian.i[k], hessian.j[k]];
      const c = s * hessian.v[k] * (i === j ? 1 : 2);
      if (c === 0) continue;
      const t = i === j ? `${names[i]} ^ 2` : `${names[i]} * ${names[j]}`;
      terms.push(`${terms.length === 0 && c > 0 ? '' : c < 0 ? '- ' : '+ '}${num(Math.abs(c))} ${t}`);
    }
    if (terms.length) quad = ` + [ ${terms.join(' ')} ] / 2`;
  }
  out.push(` obj: ${objIdx.length ? linear(objIdx, objVal, names) : ''}${quad}${constant ? ` ${constant < 0 ? '-' : '+'} ${num(Math.abs(constant))}` : ''}`.trimEnd());
  out.push('Subject To');
  lp.rows.forEach((r, i) => {
    const body = linear(r.index, r.value, names);
    if (r.lower === r.upper) out.push(` ${rows[i]}: ${body} = ${num(r.upper)}`);
    else if (isFinite(r.lower) && isFinite(r.upper)) {
      // Ranged row as two one-sided rows: readers disagree on `lo <= expr <= hi`.
      out.push(` ${rows[i]}_lo: ${body} >= ${num(r.lower)}`);
      out.push(` ${rows[i]}_hi: ${body} <= ${num(r.upper)}`);
    }
    else if (isFinite(r.upper)) out.push(` ${rows[i]}: ${body} <= ${num(r.upper)}`);
    else if (isFinite(r.lower)) out.push(` ${rows[i]}: ${body} >= ${num(r.lower)}`);
  });
  out.push('Bounds');
  for (let j = 0; j < lp.numVars; j++) {
    const lo = lp.lower[j];
    const hi = lp.upper[j];
    if (lo === 0 && hi === Infinity) continue;
    if (lo === -Infinity && hi === Infinity) out.push(` ${names[j]} free`);
    else if (lo === hi) out.push(` ${names[j]} = ${num(lo)}`);
    else out.push(` ${lo === -Infinity ? '-inf' : num(lo)} <= ${names[j]} <= ${hi === Infinity ? '+inf' : num(hi)}`);
  }
  const ints = names.filter((_, j) => lp.integer[j]);
  if (ints.length) {
    out.push('General');
    for (let k = 0; k < ints.length; k += 8) out.push(' ' + ints.slice(k, k + 8).join(' '));
  }
  out.push('End');
  return out.join('\n') + '\n';
}
