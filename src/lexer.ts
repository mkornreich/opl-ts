/**
 * Tokenizer shared by models (.mod), data files (.dat) and OPLScript (.osc).
 */

import { fail, type SourcePos } from './errors.js';

export type TokenKind = 'ident' | 'int' | 'float' | 'string' | 'punct' | 'eof';

export interface Token {
  kind: TokenKind;
  text: string;
  /** Numeric value for int/float tokens, decoded text for strings. */
  value?: number | string;
  pos: SourcePos;
}

// Longest first.
const PUNCTUATION = [
  '...', '#[', ']#', '#<', '>#', '..', ':=', '<=', '>=', '==', '!=', '<>', '<<',
  '&&', '||', '\\/', '/\\', '=>',
  '+', '-', '*', '/', '%', '^', '(', ')', '[', ']', '{', '}', '<', '>', '=', ',', ';',
  ':', '.', '|', '&', '!', '?',
];

export function tokenize(src: string, file: string): Token[] {
  const tokens: Token[] = [];
  let i = 0;
  let line = 1;
  let lineStart = 0;
  const pos = (at: number): SourcePos => ({ file, line, col: at - lineStart + 1 });

  while (i < src.length) {
    const c = src[i];
    if (c === '\n') {
      i++;
      line++;
      lineStart = i;
      continue;
    }
    if (c === ' ' || c === '\t' || c === '\r' || c === '\f' || c === '\v') {
      i++;
      continue;
    }
    if (c === '/' && src[i + 1] === '/') {
      while (i < src.length && src[i] !== '\n') i++;
      continue;
    }
    if (c === '/' && src[i + 1] === '*') {
      const start = pos(i);
      i += 2;
      while (i < src.length && !(src[i] === '*' && src[i + 1] === '/')) {
        if (src[i] === '\n') {
          line++;
          lineStart = i + 1;
        }
        i++;
      }
      if (i >= src.length) fail('unterminated comment', start);
      i += 2;
      continue;
    }

    const start = i;
    if (isIdentStart(c)) {
      while (i < src.length && isIdentPart(src[i])) i++;
      tokens.push({ kind: 'ident', text: src.slice(start, i), pos: pos(start) });
      continue;
    }

    if (isDigit(c) || (c === '.' && isDigit(src[i + 1] ?? ''))) {
      let isFloat = false;
      while (isDigit(src[i] ?? '')) i++;
      // "1..3" is a range, not the float "1." followed by ".3".
      if (src[i] === '.' && src[i + 1] !== '.') {
        isFloat = true;
        i++;
        while (isDigit(src[i] ?? '')) i++;
      }
      if ((src[i] === 'e' || src[i] === 'E') &&
          (isDigit(src[i + 1] ?? '') || ((src[i + 1] === '+' || src[i + 1] === '-') && isDigit(src[i + 2] ?? '')))) {
        isFloat = true;
        i += 2;
        while (isDigit(src[i] ?? '')) i++;
      }
      const text = src.slice(start, i);
      tokens.push({ kind: isFloat ? 'float' : 'int', text, value: Number(text), pos: pos(start) });
      continue;
    }

    if (c === '"') {
      const p = pos(start);
      i++;
      let s = '';
      while (i < src.length && src[i] !== '"') {
        if (src[i] === '\n') fail('unterminated string', p);
        // Only \" and \\ are escapes, so Windows paths such as "E:\Program Files\x.xls"
        // keep their backslashes, as they did in OPL Studio.
        if (src[i] === '\\' && (src[i + 1] === '"' || src[i + 1] === '\\')) {
          s += src[i + 1];
          i += 2;
          continue;
        }
        s += src[i++];
      }
      if (i >= src.length) fail('unterminated string', p);
      i++;
      tokens.push({ kind: 'string', text: src.slice(start, i), value: s, pos: p });
      continue;
    }

    const punct = PUNCTUATION.find((p) => src.startsWith(p, i));
    if (!punct) fail(`unexpected character '${c}'`, pos(i));
    tokens.push({ kind: 'punct', text: punct, pos: pos(i) });
    i += punct.length;
  }
  tokens.push({ kind: 'eof', text: '<end of file>', pos: pos(i) });
  return tokens;
}

function isDigit(c: string): boolean {
  return c >= '0' && c <= '9';
}

function isIdentStart(c: string): boolean {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c === '_';
}

function isIdentPart(c: string): boolean {
  return isIdentStart(c) || isDigit(c);
}
