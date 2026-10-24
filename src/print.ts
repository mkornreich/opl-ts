/**
 * Prints expressions back as OPL source, used for `display` labels.
 * `subst` replaces identifiers (display iterators) by their current values.
 */

import type { Expr, Quantifier } from './ast.js';

const PREC: Record<string, number> = {
  '||': 1, '&&': 2,
  '=': 4, '!=': 4, '<': 4, '<=': 4, '>': 4, '>=': 4, in: 4, 'not in': 4,
  '+': 6, '-': 6, union: 6, diff: 6, symdiff: 6,
  '*': 7, '/': 7, div: 7, mod: 7, inter: 7,
  '^': 9,
};

export function printExpr(e: Expr, subst: (name: string) => string | null = () => null): string {
  const p = (x: Expr, ctx = 0): string => {
    switch (x.k) {
      case 'num':
        return String(x.value);
      case 'str':
        return JSON.stringify(x.value);
      case 'sym':
        return x.name;
      case 'id':
        return subst(x.name) ?? x.name;
      case 'index':
        return `${p(x.target, 10)}[${x.args.map((a) => p(a)).join(',')}]`;
      case 'field':
        return `${p(x.target, 10)}.${x.name}`;
      case 'call':
        return `${x.fn}(${x.args.map((a) => p(a)).join(', ')})`;
      case 'method':
        return `${p(x.target, 10)}.${x.name}(${x.args.map((a) => p(a)).join(', ')})`;
      case 'unary':
        return wrap(`${x.op}${p(x.e, 8)}`, 8, ctx);
      case 'bin': {
        const pr = PREC[x.op] ?? 5;
        const op = /^[a-z]/.test(x.op) ? ` ${x.op} ` : x.op === '*' || x.op === '/' || x.op === '^' ? x.op : ` ${x.op} `;
        return wrap(`${p(x.l, pr)}${op}${p(x.r, pr + 1)}`, pr, ctx);
      }
      case 'chain':
        return wrap(x.exprs.map((y, i) => (i ? ` ${x.ops[i - 1]} ` : '') + p(y, 5)).join(''), 4, ctx);
      case 'agg':
        return wrap(`${x.op}(${printQuantifier(x.q, p)}) ${p(x.body, 7)}`, 7, ctx);
      case 'range':
        return wrap(`${p(x.lo, 6)}..${p(x.hi, 6)}`, 5, ctx);
      case 'setLit':
        return `{${x.items.map((a) => p(a)).join(', ')}}`;
      case 'setComp':
        return `{${p(x.head)} | ${printQuantifier(x.q, p)}}`;
      case 'arrayComp':
        return `[${x.key ? `${p(x.key)} : ` : ''}${p(x.value)} | ${printQuantifier(x.q, p)}]`;
      case 'arrayLit':
        return `[${x.items.map((a) => p(a)).join(', ')}]`;
      case 'indexedLit':
        return `#[${x.entries.map((en) => `${p(en.key)}: ${p(en.value)}`).join(', ')}]#`;
      case 'tuple':
        return `<${x.items.map((a) => p(a, 5)).join(',')}>`;
      case 'namedTuple':
        return `#<${x.fields.map((f) => `${f.name}: ${p(f.value)}`).join(', ')}>#`;
      case 'cond':
        return wrap(`${p(x.c, 1)} ? ${p(x.a)} : ${p(x.b)}`, 0, ctx);
      case 'stepwise':
        return `stepwise{${x.items.map((it) => `${p(it.slope)} -> ${p(it.bp)}; `).join('')}${p(x.last)}}`;
      case 'piecewise':
        return `piecewise{${x.items.map((it) => `${p(it.slope)} -> ${p(it.bp)}; `).join('')}${p(x.last)}}${x.operand ? ` ${p(x.operand, 8)}` : ''}`;
    }
  };
  return p(e);
}

function printQuantifier(q: Quantifier, p: (x: Expr, ctx?: number) => string): string {
  return q.binders
    .map((b) => {
      const names = b.pattern ? `<${b.names.join(',')}>` : b.names.join(',');
      return `${names} in ${p(b.domain, 5)}${b.filter ? ` : ${p(b.filter)}` : ''}`;
    })
    .join(', ');
}

function wrap(s: string, prec: number, ctx: number): string {
  return prec < ctx ? `(${s})` : s;
}
