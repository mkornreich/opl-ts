import type { SourcePos } from './errors.js';

// ---------------------------------------------------------------- expressions

export type Expr =
  | { k: 'num'; value: number; isInt: boolean; pos: SourcePos }
  | { k: 'str'; value: string; pos: SourcePos }
  /** A bare identifier inside a .dat file: an enum value or a string. */
  | { k: 'sym'; name: string; pos: SourcePos }
  | { k: 'id'; name: string; pos: SourcePos }
  | { k: 'index'; target: Expr; args: Expr[]; pos: SourcePos }
  | { k: 'field'; target: Expr; name: string; pos: SourcePos }
  | { k: 'call'; fn: string; args: Expr[]; pos: SourcePos }
  | { k: 'method'; target: Expr; name: string; args: Expr[]; pos: SourcePos }
  | { k: 'unary'; op: '-' | '+' | '!'; e: Expr; pos: SourcePos }
  | { k: 'bin'; op: string; l: Expr; r: Expr; pos: SourcePos }
  /** a <= b <= c */
  | { k: 'chain'; ops: string[]; exprs: Expr[]; pos: SourcePos }
  | { k: 'agg'; op: string; q: Quantifier; body: Expr; pos: SourcePos }
  | { k: 'range'; lo: Expr; hi: Expr; pos: SourcePos }
  | { k: 'setLit'; items: Expr[]; pos: SourcePos }
  | { k: 'setComp'; head: Expr; q: Quantifier; pos: SourcePos }
  | { k: 'arrayLit'; items: Expr[]; pos: SourcePos }
  | { k: 'indexedLit'; entries: { key: Expr; value: Expr }[]; pos: SourcePos }
  | { k: 'tuple'; items: Expr[]; pos: SourcePos }
  | { k: 'namedTuple'; fields: { name: string; value: Expr }[]; pos: SourcePos }
  | { k: 'cond'; c: Expr; a: Expr; b: Expr; pos: SourcePos };

export interface Binder {
  /** Iterator names; for a tuple pattern <a,b> in S these are the components. */
  names: string[];
  pattern: boolean;
  domain: Expr;
  filter?: Expr;
  pos: SourcePos;
}

export interface Quantifier {
  binders: Binder[];
  pos: SourcePos;
}

// ---------------------------------------------------------------- types

export type TypeExpr =
  | { k: 'int'; nonneg: boolean }
  | { k: 'float'; nonneg: boolean }
  | { k: 'string' }
  | { k: 'named'; name: string; pos: SourcePos }
  | { k: 'set'; of: TypeExpr };

/** One array dimension: an index set expression, optionally binding an iterator. */
export interface Dim {
  name?: string;
  domain: Expr;
}

export type DataInit =
  | { k: 'expr'; e: Expr }
  | { k: 'external' }
  | { k: 'sheet'; conn: string; range: Expr }
  | { k: 'file'; path: string }
  | { k: 'prompt'; text: string };

// ---------------------------------------------------------------- statements

export interface FieldDecl {
  type: TypeExpr;
  name: string;
  dims: Dim[];
  pos: SourcePos;
}

export type Stmt =
  | { k: 'range'; name: string; e: Expr; pos: SourcePos }
  | { k: 'enum'; name: string; values: string[] | null; pos: SourcePos }
  | { k: 'struct'; name: string; fields: FieldDecl[]; pos: SourcePos }
  | { k: 'data'; type: TypeExpr; name: string; dims: Dim[]; init: DataInit | null; pos: SourcePos }
  | { k: 'var'; type: TypeExpr; name: string; dims: Dim[]; domain: Expr | null; pos: SourcePos }
  | { k: 'constraintDecl'; name: string; dims: Dim[]; pos: SourcePos }
  | { k: 'objective'; sense: 'minimize' | 'maximize' | null; e: Expr | null; constraints: CStmt[]; pos: SourcePos }
  | { k: 'display'; q: Quantifier | null; e: Expr; pos: SourcePos }
  | { k: 'sheetConnection'; name: string; args: Expr[]; pos: SourcePos }
  | { k: 'sheetWrite'; conn: string; range: Expr; e: Expr; pos: SourcePos };

export type CStmt =
  | { k: 'forall'; q: Quantifier; body: CStmt[]; pos: SourcePos }
  | { k: 'if'; c: Expr; then: CStmt[]; else: CStmt[]; pos: SourcePos }
  | { k: 'constraint'; label: Expr | null; e: Expr; pos: SourcePos };

export interface ModelAst {
  file: string;
  stmts: Stmt[];
}

export interface DataAst {
  file: string;
  entries: { name: string; value: Expr; pos: SourcePos }[];
}

// ---------------------------------------------------------------- OPLScript

export type ScriptStmt =
  | { k: 'model'; name: string; files: string[]; editMode: boolean; pos: SourcePos }
  | { k: 'ofile'; name: string; path: Expr; pos: SourcePos }
  | { k: 'decl'; type: TypeExpr; name: string; dims: Dim[]; init: Expr | null; pos: SourcePos }
  | { k: 'range'; name: string; e: Expr; pos: SourcePos }
  | { k: 'assign'; target: Expr; e: Expr; pos: SourcePos }
  | { k: 'output'; target: Expr; items: (Expr | 'endl')[]; pos: SourcePos }
  | { k: 'expr'; e: Expr; pos: SourcePos }
  | { k: 'forall'; q: Quantifier; body: ScriptStmt[]; pos: SourcePos }
  | { k: 'while'; c: Expr; body: ScriptStmt[]; pos: SourcePos }
  | { k: 'repeat'; body: ScriptStmt[]; c: Expr; pos: SourcePos }
  | { k: 'if'; c: Expr; then: ScriptStmt[]; else: ScriptStmt[]; pos: SourcePos }
  | { k: 'display'; q: Quantifier | null; e: Expr; pos: SourcePos };

export interface ScriptAst {
  file: string;
  stmts: ScriptStmt[];
}
