/**
 * DBconnection / DBread / DBupdate / DBexecute.  OPL Studio reached databases
 * through ODBC and vendor drivers; here the "sqlite" driver (Node's built-in
 * node:sqlite) is supported:  DBconnection db("sqlite", "file.db");
 */

import { createRequire } from 'node:module';
import { fail, type SourcePos } from './errors.js';
import type { HostObject, Value } from './values.js';

interface SqliteDatabase {
  prepare(sql: string): { all(...params: unknown[]): Record<string, unknown>[]; run(...params: unknown[]): unknown };
  exec(sql: string): void;
  close(): void;
}

function openSqlite(file: string): SqliteDatabase {
  const require = createRequire(import.meta.url);
  // node:sqlite prints an ExperimentalWarning on load; keep the output clean.
  const emit = process.emitWarning;
  process.emitWarning = (() => {}) as typeof process.emitWarning;
  try {
    const { DatabaseSync } = require('node:sqlite') as { DatabaseSync: new (f: string) => SqliteDatabase };
    return new DatabaseSync(file);
  } finally {
    process.emitWarning = emit;
  }
}

export class DBConnection implements HostObject {
  readonly hostKind = 'DBconnection';
  private readonly db: SqliteDatabase;

  constructor(driver: string, file: string, pos: SourcePos) {
    if (driver.toLowerCase() !== 'sqlite') {
      fail(`database driver '${driver}' is not available; use DBconnection db("sqlite", "file.db")`, pos);
    }
    try {
      this.db = openSqlite(file);
    } catch (e) {
      fail(`cannot open database ${file}: ${(e as Error).message}`, pos);
    }
  }

  /** Cells of the result rows, row by row (columns in select order). */
  read(sql: string, pos: SourcePos): Value[] {
    try {
      return this.db.prepare(sql).all().flatMap((row) => Object.values(row).map((v) => toValue(v)));
    } catch (e) {
      fail(`DBread: ${(e as Error).message}`, pos);
    }
  }

  /** Runs a parameterised statement once per row of values. */
  update(sql: string, rows: Value[][], pos: SourcePos): void {
    try {
      const stmt = this.db.prepare(sql);
      for (const row of rows) stmt.run(...row.map((v) => (typeof v === 'number' || typeof v === 'string' ? v : String(v))));
    } catch (e) {
      fail(`DBupdate: ${(e as Error).message}`, pos);
    }
  }

  execute(sql: string, pos: SourcePos): void {
    try {
      this.db.exec(sql);
    } catch (e) {
      fail(`DBexecute: ${(e as Error).message}`, pos);
    }
  }

  close(): void {
    this.db.close();
  }
}

function toValue(v: unknown): Value {
  if (typeof v === 'number') return v;
  if (typeof v === 'bigint') return Number(v);
  if (v === null || v === undefined) return 0;
  return String(v);
}
