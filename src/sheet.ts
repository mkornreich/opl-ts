/**
 * SheetConnection / SheetRead / SheetWrite on Excel workbooks (via SheetJS).
 */

import * as fs from 'node:fs';
import * as XLSX from 'xlsx';
import { fail, type SourcePos } from './errors.js';
import type { HostObject, Value } from './values.js';

export class SheetConnection implements HostObject {
  readonly hostKind = 'SheetConnection';
  private readonly workbook: XLSX.WorkBook;
  private dirty = false;

  constructor(readonly file: string) {
    this.workbook = XLSX.read(fs.readFileSync(file), { type: 'buffer', cellStyles: true });
  }

  private locate(range: string, pos: SourcePos): { sheet: XLSX.WorkSheet; range: XLSX.Range } {
    let sheetName = this.workbook.SheetNames[0];
    let ref = range;
    const bang = range.lastIndexOf('!');
    if (bang >= 0) {
      sheetName = range.slice(0, bang).replace(/^'|'$/g, '');
      ref = range.slice(bang + 1);
    }
    const sheet = this.workbook.Sheets[sheetName];
    if (!sheet) fail(`no sheet named '${sheetName}' in ${this.file}`, pos);
    if (!/^\$?[A-Za-z]+\$?\d+(:\$?[A-Za-z]+\$?\d+)?$/.test(ref)) fail(`invalid sheet range '${range}'`, pos);
    return { sheet, range: XLSX.utils.decode_range(ref.replace(/\$/g, '')) };
  }

  /** Cell values of the range in row-major order. */
  read(range: string, pos: SourcePos): Value[] {
    const { sheet, range: r } = this.locate(range, pos);
    const out: Value[] = [];
    for (let row = r.s.r; row <= r.e.r; row++) {
      for (let col = r.s.c; col <= r.e.c; col++) {
        const cell = sheet[XLSX.utils.encode_cell({ r: row, c: col })] as XLSX.CellObject | undefined;
        if (!cell || cell.v === undefined || cell.v === null || cell.v === '') out.push(0);
        else if (typeof cell.v === 'number') out.push(cell.v);
        else if (typeof cell.v === 'boolean') out.push(cell.v ? 1 : 0);
        else out.push(String(cell.v));
      }
    }
    return out;
  }

  /** Writes values into the range in row-major order. */
  write(range: string, values: Value[], pos: SourcePos): void {
    const { sheet, range: r } = this.locate(range, pos);
    const size = (r.e.r - r.s.r + 1) * (r.e.c - r.s.c + 1);
    if (size !== values.length) fail(`SheetWrite: range ${range} has ${size} cell(s) but ${values.length} value(s) were given`, pos);
    let i = 0;
    for (let row = r.s.r; row <= r.e.r; row++) {
      for (let col = r.s.c; col <= r.e.c; col++) {
        const v = values[i++];
        const addr = XLSX.utils.encode_cell({ r: row, c: col });
        const old = sheet[addr] as XLSX.CellObject | undefined;
        sheet[addr] = typeof v === 'number' ? { ...old, t: 'n', v, f: undefined, w: undefined } : { ...old, t: 's', v: String(v), f: undefined, w: undefined };
      }
    }
    const used = XLSX.utils.decode_range(sheet['!ref'] ?? 'A1');
    used.s.r = Math.min(used.s.r, r.s.r);
    used.s.c = Math.min(used.s.c, r.s.c);
    used.e.r = Math.max(used.e.r, r.e.r);
    used.e.c = Math.max(used.e.c, r.e.c);
    sheet['!ref'] = XLSX.utils.encode_range(used);
    this.dirty = true;
  }

  save(): void {
    if (!this.dirty) return;
    const ext = this.file.toLowerCase().split('.').pop();
    const bookType: XLSX.BookType = ext === 'xlsx' ? 'xlsx' : ext === 'ods' ? 'ods' : ext === 'csv' ? 'csv' : 'biff8';
    fs.writeFileSync(this.file, XLSX.write(this.workbook, { type: 'buffer', bookType }));
    this.dirty = false;
  }
}
