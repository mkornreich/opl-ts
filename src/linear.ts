/**
 * Decision variables, linear expressions and constraint references.
 */

import { fail, type SourcePos } from './errors.js';

export class DVar {
  /** Solution value, reduced cost (NaN until solved). */
  value = NaN;
  rc = NaN;
  /** For `var Enum x`: values are the enum's ordinals. */
  enumType?: import('./values.js').EnumType;
  /** For `var int x in S`: the allowed values. */
  domain?: number[];
  /** Introduced by flattening, not declared by the model. */
  aux = false;
  constructor(
    readonly id: number,
    readonly name: string,
    readonly isInt: boolean,
    public lb: number,
    public ub: number,
  ) {}
}

export class ConstraintRef {
  dual = NaN;
  slack = NaN;
  /** Row activity at the solution. */
  activity = NaN;
  bound = false;
  constructor(readonly name: string) {}
}

export class LinExpr {
  constructor(
    readonly terms: Map<number, number> = new Map(),
    public constant = 0,
  ) {}

  static of(v: number | DVar | LinExpr): LinExpr {
    if (v instanceof LinExpr) return v;
    if (v instanceof DVar) return new LinExpr(new Map([[v.id, 1]]), 0);
    return new LinExpr(new Map(), v);
  }

  clone(): LinExpr {
    return new LinExpr(new Map(this.terms), this.constant);
  }

  isConstant(): boolean {
    for (const c of this.terms.values()) if (c !== 0) return false;
    return true;
  }

  /** this += k * other (in place). */
  addScaled(other: number | DVar | LinExpr, k: number): this {
    if (typeof other === 'number') {
      this.constant += k * other;
    } else if (other instanceof DVar) {
      this.terms.set(other.id, (this.terms.get(other.id) ?? 0) + k);
    } else {
      this.constant += k * other.constant;
      for (const [id, c] of other.terms) this.terms.set(id, (this.terms.get(id) ?? 0) + k * c);
    }
    return this;
  }
}

export type Linear = number | DVar | LinExpr;

export function isLinear(v: unknown): v is DVar | LinExpr {
  return v instanceof DVar || v instanceof LinExpr;
}

export function linAdd(a: Linear, b: Linear, sign: 1 | -1): Linear {
  if (typeof a === 'number' && typeof b === 'number') return a + sign * b;
  return LinExpr.of(a).clone().addScaled(b, sign);
}

export function linMul(a: Linear, b: Linear, pos: SourcePos): Linear {
  if (typeof a === 'number' && typeof b === 'number') return a * b;
  if (typeof a === 'number') return new LinExpr().addScaled(b, a);
  if (typeof b === 'number') return new LinExpr().addScaled(a, b);
  const la = LinExpr.of(a);
  const lb = LinExpr.of(b);
  if (la.isConstant()) return new LinExpr().addScaled(lb, la.constant);
  if (lb.isConstant()) return new LinExpr().addScaled(la, lb.constant);
  fail('non-linear expression: product of two decision-variable expressions', pos);
}
