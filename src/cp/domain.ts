/**
 * Immutable variable domains.
 *
 * Integer domains are sorted lists of disjoint inclusive intervals
 * [a0, b0, a1, b1, ...]; real (float) domains are a single interval.
 * Every operation returns `this` when nothing changes.
 */

export class Dom {
  private constructor(
    /** Interval bounds; for real domains exactly [lo, hi]. */
    readonly iv: readonly number[],
    readonly size: number,
    readonly real: boolean,
  ) {}

  static readonly EMPTY = new Dom([], 0, false);

  static range(lo: number, hi: number, real = false): Dom {
    if (!real) {
      lo = Math.ceil(lo);
      hi = Math.floor(hi);
    }
    if (lo > hi) return Dom.EMPTY;
    return new Dom([lo, hi], real ? (lo === hi ? 1 : Infinity) : hi - lo + 1, real);
  }

  /** Integer domain from values (any order, duplicates allowed). */
  static values(values: Iterable<number>): Dom {
    const sorted = [...new Set(values)].filter((v) => Number.isInteger(v)).sort((a, b) => a - b);
    const iv: number[] = [];
    for (const v of sorted) {
      if (iv.length && iv[iv.length - 1] === v - 1) iv[iv.length - 1] = v;
      else iv.push(v, v);
    }
    return Dom.fromIntervals(iv);
  }

  private static fromIntervals(iv: number[]): Dom {
    if (iv.length === 0) return Dom.EMPTY;
    let size = 0;
    for (let k = 0; k < iv.length; k += 2) size += iv[k + 1] - iv[k] + 1;
    return new Dom(iv, size, false);
  }

  get empty(): boolean {
    return this.size === 0;
  }
  get min(): number {
    return this.iv[0];
  }
  get max(): number {
    return this.iv[this.iv.length - 1];
  }
  get bound(): boolean {
    return this.size === 1;
  }

  contains(v: number): boolean {
    const iv = this.iv;
    if (this.size === 0 || v < iv[0] || v > iv[iv.length - 1]) return false;
    if (this.real) return true;
    if (!Number.isInteger(v)) return false;
    let lo = 0;
    let hi = iv.length / 2 - 1;
    while (lo <= hi) {
      const mid = (lo + hi) >> 1;
      if (v < iv[2 * mid]) hi = mid - 1;
      else if (v > iv[2 * mid + 1]) lo = mid + 1;
      else return true;
    }
    return false;
  }

  withMin(m: number): Dom {
    if (this.size === 0 || m <= this.min) return this;
    if (this.real) return Dom.range(m > this.max && m - this.max <= realTol(m) ? this.max : m, this.max, true);
    m = Math.ceil(m);
    if (m > this.max) return Dom.EMPTY;
    const iv = this.iv;
    let k = 0;
    while (iv[k + 1] < m) k += 2;
    const out = iv.slice(k);
    if (out[0] < m) out[0] = m;
    return Dom.fromIntervals(out);
  }

  withMax(m: number): Dom {
    if (this.size === 0 || m >= this.max) return this;
    if (this.real) return Dom.range(this.min, m < this.min && this.min - m <= realTol(m) ? this.min : m, true);
    m = Math.floor(m);
    if (m < this.min) return Dom.EMPTY;
    const iv = this.iv;
    let k = iv.length - 2;
    while (iv[k] > m) k -= 2;
    const out = iv.slice(0, k + 2);
    if (out[out.length - 1] > m) out[out.length - 1] = m;
    return Dom.fromIntervals(out);
  }

  without(v: number): Dom {
    if (!this.contains(v)) return this;
    if (this.real) return this.min === v && this.max === v ? Dom.EMPTY : this;
    const iv = this.iv;
    const out: number[] = [];
    for (let k = 0; k < iv.length; k += 2) {
      const a = iv[k];
      const b = iv[k + 1];
      if (v < a || v > b) out.push(a, b);
      else {
        if (a <= v - 1) out.push(a, v - 1);
        if (v + 1 <= b) out.push(v + 1, b);
      }
    }
    return Dom.fromIntervals(out);
  }

  intersect(other: Dom): Dom {
    if (this.size === 0) return this;
    if (other.size === 0) return Dom.EMPTY;
    if (this.real) {
      const r = Dom.range(Math.max(this.min, other.min), Math.min(this.max, other.max), true);
      return r.min === this.min && r.max === this.max ? this : r;
    }
    if (other.real) return this.withMin(other.min).withMax(other.max);
    const a = this.iv;
    const b = other.iv;
    const out: number[] = [];
    let i = 0;
    let j = 0;
    while (i < a.length && j < b.length) {
      const lo = Math.max(a[i], b[j]);
      const hi = Math.min(a[i + 1], b[j + 1]);
      if (lo <= hi) out.push(lo, hi);
      if (a[i + 1] < b[j + 1]) i += 2;
      else j += 2;
    }
    const r = Dom.fromIntervals(out);
    return r.size === this.size ? this : r;
  }

  /** Values of this domain not in `other`. */
  minus(other: Dom): Dom {
    if (this.real) return this;
    let d: Dom = this;
    if (other.size > 64) {
      const inter = this.intersect(other);
      if (inter.size === 0) return this;
      for (const v of inter.values()) d = d.without(v);
      return d;
    }
    for (const v of other.values()) d = d.without(v);
    return d;
  }

  intersects(other: Dom): boolean {
    return this.intersect(other).size > 0;
  }

  /** Smallest value > v, or null. */
  next(v: number): number | null {
    const iv = this.iv;
    for (let k = 0; k < iv.length; k += 2) {
      if (iv[k + 1] > v) return Math.max(iv[k], Math.floor(v) + 1);
    }
    return null;
  }

  /** Largest value < v, or null. */
  prev(v: number): number | null {
    const iv = this.iv;
    for (let k = iv.length - 2; k >= 0; k -= 2) {
      if (iv[k] < v) return Math.min(iv[k + 1], Math.ceil(v) - 1);
    }
    return null;
  }

  *values(): Generator<number> {
    if (this.real) {
      if (this.size === 1) yield this.min;
      return;
    }
    const iv = this.iv;
    for (let k = 0; k < iv.length; k += 2) for (let v = iv[k]; v <= iv[k + 1]; v++) yield v;
  }

  toString(): string {
    if (this.size === 0) return '{}';
    if (this.real) return `[${this.min}, ${this.max}]`;
    const parts: string[] = [];
    for (let k = 0; k < this.iv.length; k += 2) {
      parts.push(this.iv[k] === this.iv[k + 1] ? `${this.iv[k]}` : `${this.iv[k]}..${this.iv[k + 1]}`);
    }
    return `{${parts.join(' ')}}`;
  }
}

/** Rounding noise tolerated when a bound of a real variable crosses the other bound. */
function realTol(m: number): number {
  return 1e-9 * Math.max(1, Math.abs(m));
}
