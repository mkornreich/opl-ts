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
  /** [key : value | quantifier] or [value | quantifier] (generic array initialisation) */
  | { k: 'arrayComp'; key: Expr | null; value: Expr; q: Quantifier; pos: SourcePos }
  | { k: 'indexedLit'; entries: { key: Expr; value: Expr }[]; pos: SourcePos }
  | { k: 'tuple'; items: Expr[]; pos: SourcePos }
  | { k: 'namedTuple'; fields: { name: string; value: Expr }[]; pos: SourcePos }
  | { k: 'cond'; c: Expr; a: Expr; b: Expr; pos: SourcePos }
  /** piecewise[(q)]{ slope -> breakpoint; ...; lastSlope } [(x0, y0)] [operand] */
  | { k: 'stepwise'; q: Quantifier | null; items: { slope: Expr; bp: Expr }[]; last: Expr; pos: SourcePos }
  | { k: 'piecewise'; q: Quantifier | null; items: { slope: Expr; bp: Expr }[]; last: Expr; origin: [Expr, Expr] | null; operand: Expr | null; pos: SourcePos };

export interface Binder {
  /** Iterator names; for a tuple pattern <a,b> in S these are the components. */
  names: string[];
  pattern: boolean;
  domain: Expr;
  filter?: Expr;
  /** `ordered i, j in S`: the iterators take strictly increasing positions of S. */
  ordered?: boolean;
  /** Tuple pattern components that are expressions (`<n, s.dept> in S`): matched, not bound. */
  patternExprs?: (Expr | null)[];
  pos: SourcePos;
}

export interface Quantifier {
  binders: Binder[];
  /** `ordered by increasing|decreasing expr` */
  order?: { dir: 1 | -1; key: Expr };
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
  | { k: 'prompt'; text: string }
  | { k: 'db'; conn: string; sql: Expr };

// ---------------------------------------------------------------- statements

export interface FieldDecl {
  type: TypeExpr;
  name: string;
  dims: Dim[];
  /** A key field: tuples can be referred to by their key values. */
  key?: boolean;
  pos: SourcePos;
}

export type Stmt =
  | { k: 'range'; name: string; e: Expr; pos: SourcePos }
  | { k: 'enum'; name: string; values: string[] | null; pos: SourcePos }
  | { k: 'struct'; name: string; fields: FieldDecl[]; pos: SourcePos }
  | { k: 'data'; type: TypeExpr; name: string; dims: Dim[]; init: DataInit | null; pos: SourcePos }
  /** modern: declared with `dvar` (non-negative by default) rather than OPL 3 `var`. */
  | { k: 'var'; type: TypeExpr; name: string; dims: Dim[]; domain: Expr | null; modern?: boolean; interval?: IntervalSpec; alias?: Expr; pos: SourcePos }
  /** dexpr T name[dims] = expr; (a named expression over decision variables) */
  | { k: 'dexpr'; type: TypeExpr; name: string; dims: Dim[]; e: Expr; pos: SourcePos }
  | { k: 'script'; kind: 'execute' | 'main'; name: string | null; code: string; pos: SourcePos }
  | { k: 'using'; solver: string; pos: SourcePos }
  | { k: 'assert'; label: string | null; q: Quantifier | null; e: Expr; pos: SourcePos }
  | { k: 'include'; file: string; pos: SourcePos }
  | { k: 'predicate'; name: string; arity: number; set: Expr; pos: SourcePos }
  | { k: 'constraintDecl'; name: string; dims: Dim[]; pos: SourcePos }
  | { k: 'objective'; sense: 'minimize' | 'maximize' | null; e: Expr | null; constraints: CStmt[]; pos: SourcePos }
  | { k: 'display'; q: Quantifier | null; e: Expr; pos: SourcePos }
  | { k: 'sheetConnection'; name: string; args: Expr[]; pos: SourcePos }
  | { k: 'sheetWrite'; conn: string; range: Expr; e: Expr; pos: SourcePos }
  | { k: 'dbConnection'; name: string; args: Expr[]; pos: SourcePos }
  | { k: 'dbUpdate'; conn: string; sql: Expr; e: Expr | null; pos: SourcePos }
  | { k: 'search'; body: SStmt[]; pos: SourcePos }
  | { k: 'horizon'; which: 'horizon' | 'origin'; e: Expr; pos: SourcePos }
  | { k: 'activity'; name: string; dims: Dim[]; duration: Expr | null; breakable: boolean; transitionType?: Expr | null; pos: SourcePos }
  /** dvar sequence s[dims] in intervals [types t]; (CP Optimizer) */
  | { k: 'sequence'; name: string; dims: Dim[]; intervals: Expr; types: Expr | null; pos: SourcePos }
  /** stateFunction f[dims] [with M]; (CP Optimizer) */
  | { k: 'stateFunction'; name: string; dims: Dim[]; matrix: Expr | null; pos: SourcePos }
  | { k: 'resource'; kind: ResourceDeclKind; name: string; dims: Dim[]; args: Expr[]; pos: SourcePos };

/** dvar interval a [optional] [in lo..hi] [size s] */
export interface IntervalSpec {
  optional: boolean;
  window: Expr | null;
  size: Expr | null;
  /** intensity F: a step function (CP Optimizer calendars). */
  intensity?: Expr | null;
}

export type ResourceDeclKind = 'UnaryResource' | 'DiscreteResource' | 'Reservoir' | 'StateResource' | 'AlternativeResources';

export type CStmt =
  /** label: a label written before the forall, applied to the constraints inside. */
  | { k: 'forall'; q: Quantifier; body: CStmt[]; label?: Expr; pos: SourcePos }
  | { k: 'if'; c: Expr; then: CStmt[]; else: CStmt[]; pos: SourcePos }
  /** level: onValue / onDomain / onRange / onBounds propagation strength. */
  | { k: 'constraint'; label: Expr | null; e: Expr; level?: string; pos: SourcePos };

/** Statements of a search procedure. */
export type SStmt =
  | { k: 'forall' | 'tryall' | 'select'; q: Quantifier; body: SStmt[]; pos: SourcePos }
  | { k: 'try'; alts: SStmt[][]; pos: SourcePos }
  | { k: 'if'; c: Expr; then: SStmt[]; else: SStmt[]; pos: SourcePos }
  | { k: 'while'; c: Expr; body: SStmt[]; pos: SourcePos }
  | { k: 'strategy'; name: string; args: Expr[]; body: SStmt[]; pos: SourcePos }
  /** A constraint to post, or a search built-in such as generate(x). */
  | { k: 'post'; e: Expr; pos: SourcePos };

export interface ModelAst {
  file: string;
  stmts: Stmt[];
}

export interface DataAst {
  file: string;
  /** name = value;  or  name from SheetRead(conn, "range"); (value is then a call) */
  entries: { name: string; value: Expr; pos: SourcePos }[];
  /** SheetConnection / DBConnection declared in the data file. */
  connections?: { kind: 'sheet' | 'db'; name: string; args: Expr[]; pos: SourcePos }[];
  /** name to SheetWrite(conn, "range");  name to DBUpdate(conn, "sql"); */
  writes?: { name: string; call: Expr; pos: SourcePos }[];
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
  | { k: 'display'; q: Quantifier | null; e: Expr; pos: SourcePos }
  /** import enum E m.E;  (the name is taken from a model) */
  | { k: 'import'; kind: string; name: string; from: Expr; pos: SourcePos }
  /** Other objects, e.g. `Basis b(m);` */
  | { k: 'object'; type: string; name: string; args: Expr[]; pos: SourcePos }
  | { k: 'enum'; name: string; values: string[]; pos: SourcePos };

export interface ScriptAst {
  file: string;
  stmts: ScriptStmt[];
}
