/**
 * Runtime values and types of the OPL interpreter.
 *
 * Numbers are plain JS numbers (booleans are 0/1); whether a number is an int
 * or a float is static type information (see Type), used for formatting.
 * Enum values and strings are JS strings.
 */

import { Activity, CPConstraint, Resource } from './cp/terms.js';
import { ConstraintRef, DVar, LinExpr } from './linear.js';

// ---------------------------------------------------------------- collections

export interface IndexSet {
  readonly size: number;
  indexOf(v: Value): number;
  at(i: number): Value;
}

export class OplRange implements IndexSet {
  constructor(
    readonly lo: number,
    readonly hi: number,
  ) {}
  get size(): number {
    return Math.max(0, this.hi - this.lo + 1);
  }
  indexOf(v: Value): number {
    return typeof v === 'number' && Number.isInteger(v) && v >= this.lo && v <= this.hi ? v - this.lo : -1;
  }
  at(i: number): Value {
    return this.lo + i;
  }
}

export class EnumType implements IndexSet {
  readonly index = new Map<string, number>();
  constructor(
    readonly name: string,
    readonly values: string[],
  ) {
    values.forEach((v, i) => this.index.set(v, i));
  }
  get size(): number {
    return this.values.length;
  }
  indexOf(v: Value): number {
    return typeof v === 'string' ? (this.index.get(v) ?? -1) : -1;
  }
  at(i: number): Value {
    return this.values[i];
  }
}

/** Ordered set (insertion order), elements compared structurally. */
export class OplSet implements IndexSet {
  readonly elems: Value[] = [];
  private readonly keys = new Map<string, number>();
  constructor(
    elems: Iterable<Value> = [],
    public elemType: Type | null = null,
  ) {
    for (const e of elems) this.add(e);
  }
  add(v: Value): void {
    const k = keyOf(v);
    if (this.keys.has(k)) return;
    this.keys.set(k, this.elems.length);
    this.elems.push(v);
  }
  get size(): number {
    return this.elems.length;
  }
  clear(): void {
    this.elems.length = 0;
    this.keys.clear();
  }
  indexOf(v: Value): number {
    const i = this.keys.get(keyOf(v));
    if (i !== undefined) return i;
    // A tuple of key values selects the element with those keys: <o,d> in S, x[<o,d>].
    const t = this.elemType;
    if (v instanceof OplTuple && t?.k === 'struct' && t.s.keyFields.length === v.values.length && t.s.keyFields.length < t.s.fields.length) {
      const found = t.s.byKey.get(t.s.keyOfValues(v.values));
      if (found) return this.keys.get(keyOf(found)) ?? -1;
    }
    if ((typeof v === 'string' || typeof v === 'number') && t?.k === 'struct' && t.s.keyFields.length === 1) {
      const found = t.s.byKey.get(t.s.keyOfValues([v]));
      if (found) return this.keys.get(keyOf(found)) ?? -1;
    }
    return -1;
  }
  at(i: number): Value {
    return this.elems[i];
  }
}

export interface StructField {
  name: string;
  type: Type;
  key?: boolean;
}

export class StructType {
  readonly index = new Map<string, number>();
  /** Positions of the key fields (modern OPL `key`). */
  readonly keyFields: number[];
  /** Tuples of this type seen in sets, by key: data may refer to a tuple by its key. */
  readonly byKey = new Map<string, OplTuple>();
  constructor(
    readonly name: string,
    readonly fields: StructField[],
  ) {
    fields.forEach((f, i) => this.index.set(f.name, i));
    this.keyFields = fields.flatMap((f, i) => (f.key ? [i] : []));
  }

  keyOfValues(values: Value[]): string {
    return this.keyFields.length === 1 ? keyOf(values[0]) : keyOf(new OplTuple(null, values));
  }

  register(t: OplTuple): void {
    if (this.keyFields.length) this.byKey.set(this.keyOfValues(this.keyFields.map((i) => t.values[i])), t);
  }
}

export class OplTuple {
  constructor(
    readonly struct: StructType | null,
    readonly values: Value[],
  ) {}
}

/** Array indexed by an index set; multi-dimensional arrays nest. */
export class OplArray {
  constructor(
    readonly index: IndexSet,
    readonly items: Value[],
  ) {}
}

/** `[a, b, c]` before it has been shaped by a declared type. */
export class RawArray {
  constructor(readonly items: Value[]) {}
}

/** `#[k: v, ...]#` before it has been shaped by a declared type. */
export class RawIndexed {
  constructor(readonly entries: [Value, Value][]) {}
}

/** `#<field: v, ...>#` before it has been shaped by a declared struct. */
export class NamedTuple {
  constructor(readonly fields: Map<string, Value>) {}
}

/** Objects provided by the host (models in scripts, output files, sheets). */
export interface HostObject {
  readonly hostKind: string;
  getField?(name: string): Binding | undefined;
  callMethod?(name: string, args: Value[]): { value: Value; type: Type };
}

export type Value =
  | number
  | string
  | OplRange
  | EnumType
  | OplSet
  | OplTuple
  | OplArray
  | RawArray
  | RawIndexed
  | NamedTuple
  | DVar
  | LinExpr
  | ConstraintRef
  | CPConstraint
  | Activity
  | Resource
  | import('./eval.js').DExpr
  | import('./eval.js').VarIndexed
  | import('./eval.js').Predicate
  | import('./eval.js').PwlFunction
  | import('./eval.js').CumulExpr
  | HostObject;

// ---------------------------------------------------------------- types

export type Type =
  | { k: 'int'; nonneg?: boolean; range?: OplRange }
  | { k: 'float'; nonneg?: boolean }
  | { k: 'string' }
  | { k: 'enum'; e: EnumType }
  | { k: 'struct'; s: StructType }
  | { k: 'set'; of: Type }
  | { k: 'array'; of: Type; dims: IndexSet[] }
  | { k: 'tuple'; items: Type[] }
  | { k: 'range' }
  | { k: 'enumType'; e: EnumType }
  | { k: 'var'; of: 'int' | 'float' }
  | { k: 'constraint' }
  | { k: 'host' }
  | { k: 'unknown' };

export interface Binding {
  value: Value;
  type: Type;
  /** Bound by a quantifier or a generic array index (not a declaration). */
  iterator?: boolean;
}

export const INT: Type = { k: 'int' };
export const FLOAT: Type = { k: 'float' };
export const STRING: Type = { k: 'string' };
export const UNKNOWN: Type = { k: 'unknown' };

export function arrayType(of: Type, dims: IndexSet[]): Type {
  return dims.length === 0 ? of : { k: 'array', of, dims };
}

/** Element type after indexing `n` dimensions of an array type. */
export function indexType(t: Type, n: number): Type {
  if (t.k !== 'array') return UNKNOWN;
  if (n >= t.dims.length) return t.of;
  return { k: 'array', of: t.of, dims: t.dims.slice(n) };
}

/** Type of the elements obtained by iterating over a value of type t. */
export function elementType(t: Type, v?: Value): Type {
  switch (t.k) {
    case 'range':
      return INT;
    case 'enumType':
      return { k: 'enum', e: t.e };
    case 'set':
      return t.of;
  }
  if (v instanceof OplRange) return INT;
  if (v instanceof EnumType) return { k: 'enum', e: v };
  if (v instanceof OplSet && v.elemType) return v.elemType;
  return UNKNOWN;
}

export function isNumericType(t: Type): boolean {
  return t.k === 'int' || t.k === 'float' || t.k === 'var';
}

export function isIntType(t: Type): boolean {
  return t.k === 'int' || (t.k === 'var' && t.of === 'int');
}

// ---------------------------------------------------------------- keys / equality

export function keyOf(v: Value): string {
  if (typeof v === 'number') return Object.is(v, -0) ? '0' : String(v);
  if (typeof v === 'string') return JSON.stringify(v);
  if (v instanceof OplTuple) return '<' + v.values.map(keyOf).join(',') + '>';
  if (v instanceof OplSet) return '{' + v.elems.map(keyOf).join(',') + '}';
  if (v instanceof OplRange) return `${v.lo}..${v.hi}`;
  return '#' + typeName(v);
}

export function valuesEqual(a: Value, b: Value): boolean {
  if (typeof a === 'number' && typeof b === 'number') return a === b;
  return keyOf(a) === keyOf(b);
}

export function typeName(v: Value): string {
  if (typeof v === 'number') return 'number';
  if (typeof v === 'string') return 'string';
  if (v instanceof OplRange) return 'range';
  if (v instanceof EnumType) return 'enum';
  if (v instanceof OplSet) return 'set';
  if (v instanceof OplTuple) return 'tuple';
  if (v instanceof OplArray || v instanceof RawArray || v instanceof RawIndexed) return 'array';
  if (v instanceof NamedTuple) return 'tuple';
  if (v instanceof DVar) return 'decision variable';
  if (v instanceof LinExpr) return 'linear expression';
  if (v instanceof ConstraintRef) return 'constraint';
  if (v instanceof CPConstraint) return 'constraint';
  if (v instanceof Activity) return 'activity';
  if (v instanceof Resource) return 'resource';
  return 'hostKind' in v ? v.hostKind : 'dexpr';
}

/** Elements of a set-like value, or null when v cannot be iterated. */
export function elementsOf(v: Value): Value[] | null {
  if (v instanceof OplRange) {
    const out: number[] = [];
    for (let i = v.lo; i <= v.hi; i++) out.push(i);
    return out;
  }
  if (v instanceof EnumType) return v.values;
  if (v instanceof OplSet) return v.elems;
  return null;
}

export function asIndexSet(v: Value): IndexSet | null {
  if (v instanceof OplRange || v instanceof EnumType || v instanceof OplSet) return v;
  return null;
}

// ---------------------------------------------------------------- formatting

/**
 * 'display' mimics the OPL Studio solution window (floats with 4 decimals);
 * 'stream' mimics OPLScript `<<` output (floats like printf("%f"));
 * 'key' is for array indices in labels (shortest number form).
 */
export type FormatStyle = 'display' | 'stream' | 'key';

export function formatNumber(v: number, isInt: boolean, style: FormatStyle): string {
  if (v === Infinity) return 'infinity';
  if (v === -Infinity) return '-infinity';
  if (Number.isNaN(v)) return 'NaN';
  if (style === 'key') return String(v + 0);
  if (isInt && Number.isInteger(Math.round(v * 1e9) / 1e9)) return String(Math.round(v) + 0);
  const s = v.toFixed(style === 'display' ? 4 : 6);
  return /^-0\.0*$/.test(s) ? s.slice(1) : s;
}

export function formatValue(v: Value, t: Type, style: FormatStyle): string {
  if (v instanceof DVar) {
    if (v.enumType && !Number.isNaN(v.value)) return v.enumType.values[v.value];
    return formatNumber(v.value, v.isInt, style);
  }
  if (v instanceof Activity) {
    const n = (x: DVar | number) => formatNumber(typeof x === 'number' ? x : x.value, true, style);
    return `[${n(v.start)} -- ${n(v.duration)} --> ${n(v.end)}]`;
  }
  if (v instanceof Resource) return v.name;
  if (v instanceof CPConstraint) return 'constraint';
  if (typeof v === 'number') {
    const isInt = t.k === 'unknown' ? Number.isInteger(v) : isIntType(t);
    return formatNumber(v, isInt, style);
  }
  if (typeof v === 'string') return t.k === 'string' && style !== 'stream' ? JSON.stringify(v) : v;
  if (v instanceof OplRange) return `${v.lo}..${v.hi}`;
  if (v instanceof EnumType) return '{' + v.values.join(' ') + '}';
  if (v instanceof OplSet) {
    const et = t.k === 'set' ? t.of : (v.elemType ?? UNKNOWN);
    return '{' + v.elems.map((e) => formatValue(e, et, style)).join(' ') + '}';
  }
  if (v instanceof OplTuple) {
    const types = v.struct
      ? v.struct.fields.map((f) => f.type)
      : t.k === 'tuple' ? t.items : t.k === 'struct' ? t.s.fields.map((f) => f.type) : [];
    return '<' + v.values.map((x, i) => formatValue(x, types[i] ?? UNKNOWN, style)).join(', ') + '>';
  }
  if (v instanceof OplArray) {
    const et = indexType(t, 1);
    return '[' + v.items.map((x) => formatValue(x, et, style)).join(' ') + ']';
  }
  if (v instanceof RawArray) return '[' + v.items.map((x) => formatValue(x, UNKNOWN, style)).join(' ') + ']';
  if (v instanceof RawIndexed) {
    return '#[' + v.entries.map(([k, x]) => `${formatValue(k, UNKNOWN, style)}: ${formatValue(x, UNKNOWN, style)}`).join(' ') + ']#';
  }
  if (v instanceof NamedTuple) {
    return '#<' + [...v.fields].map(([k, x]) => `${k}: ${formatValue(x, UNKNOWN, style)}`).join(', ') + '>#';
  }
  if (v instanceof LinExpr) return formatLinExpr(v);
  if (v instanceof ConstraintRef) return v.name;
  return 'hostKind' in v ? `<${v.hostKind}>` : 'dexpr';
}

function formatLinExpr(e: LinExpr): string {
  const parts = [...e.terms].filter(([, c]) => c !== 0).map(([id, c]) => `${c}*#${id}`);
  if (e.constant !== 0 || parts.length === 0) parts.push(String(e.constant));
  return parts.join(' + ');
}
