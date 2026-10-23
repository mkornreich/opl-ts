# opl-ts

An implementation of **ILOG OPL 3.x** (the Optimization Programming Language of OPL Studio) in TypeScript, with its own simplex and branch-and-bound solver, so no CPLEX is needed.

It runs the material from the OPL Studio tutorial of MIT OpenCourseWare
[1.206J Airline Schedule Planning (Spring 2003), Study Materials](https://ocw.mit.edu/courses/1-206j-airline-schedule-planning-spring-2003/pages/study-materials/).

## Quick start

```bash
npm install
npm test            # builds, then runs the test suite (includes every tutorial file)
npm run tutorial    # runs all tutorial models, projects and the script
```

Run a single file:

```bash
node dist/src/cli.js tutorial/files/covering.prj
node dist/src/cli.js tutorial/files/simple1.mod
node dist/src/cli.js model.mod data1.dat data2.dat
node dist/src/cli.js tutorial/files/script_simple1.osc
```

(`npm link` installs the same thing as an `opl` command.)

| Option | |
| --- | --- |
| `-q`, `--quiet` | do not print the solver statistics line |
| `-a`, `--all-vars` | list all decision variables, even when the model has `display` statements |
| `-z`, `--hide-zero` | hide zero-valued variables (the `hide_zero = 1` project setting) |
| `--node-sel N` | branch-and-bound node selection: `0` depth-first, `1` best-bound (the CPLEX `nodeSel` project setting) |
| `--time-limit S` | stop branch and bound after S seconds |
| `--export-lp F` | also write the generated problem to `F` in CPLEX LP format |

## The tutorial files

`tutorial/` holds the downloads, unchanged:

- `opl_studio.pdf`: the OPL Studio tutorial handout
- `opl_tutorial_files.zip`: the supporting files, extracted into `tutorial/files/`

| File | What it shows | Result |
| --- | --- | --- |
| `simple0.mod` … `simple4-2.mod` | declarations, ranges, arrays, `#[ ]#`, sparse structs | 6926.0538 (`simple2`, integer: 6923) |
| `simple1.mod` | duals `ct[t].dual`, reduced costs `x[d].rc` | 6923.0769 |
| `gas.prj` | enums, `float+` data | 1800 |
| `covering.prj` | set-covering MIP, set comprehension | 14, crew {23 25 26} |
| `product.prj` | structs, `display` of tuples | 372 |
| `knapsack.prj` | integer knapsack, branch and bound | 261922 |
| `simple_project1.prj` | `SheetConnection`, `SheetRead`, `SheetWrite` with `simple_project1.xls` | 6926.0538 |
| `script_simple1.osc` | OPLScript sensitivity loop writing `ouput.txt` | reproduces `ouput.txt` exactly |

All results were cross-checked against the HiGHS solver.

The files refer to `E:\Program Files\examples\opl\Tutorial-1.203J\...`. When such a path does not exist, the file with the same name next to the model is used, and a note is printed. The originals therefore run unmodified.

`npm run tutorial` works on a copy in `tutorial/run/` because the script and `SheetWrite` overwrite `ouput.txt` and `simple_project1.xls`, as OPL Studio did. Running `cli.js` directly on `tutorial/files/` modifies them in place. Spreadsheets are rewritten with [SheetJS](https://sheetjs.com), which keeps the cell values but not the formatting.

## What is implemented

**Models (.mod)**
- data: `int`, `int+`, `float`, `float+`, `string`, `range`, `enum` (inline or `...`), `struct`/`tuple`, sets `{T}` / `setof(T)`, multi-dimensional arrays indexed by ranges, enums or sets, generic arrays `int a[i in R] = i*i;`
- initialisation: `= expr`, `= ...` (from .dat files), `from SheetRead(sh, "B3:C5")`, `< "file"`, `<< "prompt"`
- literals: `[ ]`, `#[ key: value ]#`, `{ }`, `{ e | i in S : cond }`, `< >`, `#< field: value >#`
- expressions: arithmetic, `div`, `mod`, `^`, comparisons (`=`/`==`, `<>`/`!=`), `&`/`&&`, `\/`/`||`, `!`/`not`, `in`/`not in`, `union`, `inter`, `diff`, `symdiff`, `c ? a : b`, `sum`/`prod`/`min`/`max` aggregates with filters, tuple patterns `<a,b> in S`, and the functions `abs floor ceil round trunc ftoi frac sqrt exp log pow min max minl maxl card ord first last next prev nextc prevc item`
- variables: `var int|int+|float|float+|RangeName x[...] in lo..hi;`
- `minimize`/`maximize ... subject to { ... }`, `forall`, `if`/`else`, labelled constraints with `constraint ct[...]`, range constraints `lo <= e <= hi`
- after the objective: post-solve declarations, `display [(q)] expr`, `.dual`, `.slack`, `.rc`, `.lb`, `.ub`, and `SheetWrite(sh, "G10:G11")(x);`

**Data files (.dat)**: `name = value;` with optional commas, and enum values as bare names.

**Projects (.prj)**: `MODEL`, one or more `DATA`, `hide_zero`, `nodeSel`.

**OPLScript (.osc)**: `Model m("x.mod", "x.dat") [editMode];`, `ofile`, declarations with `:=`, assignment to script variables and (in editMode) model data, `forall`, `while`, `repeat … until`, `if … else`, `cout << … << endl`, `m.solve()`, `m.objectiveValue()`, `m.getTime()`, `m.reset()`, and reading model data and solution values such as `m.x[i]` or `m.ct[i].dual`.

### Semantics worth knowing

- `var float x` is free and `var float+ x` is non-negative. `var int x` without a domain is a free integer. A bound of `maxint` counts as infinite.
- `display` prints floats with 4 decimals. OPLScript `<<` prints them like `printf("%f")`, which is the format of the original `ouput.txt`.
- Duals and reduced costs follow the CPLEX convention, d(objective)/d(rhs) in the model's own sense. For MIPs they come from the LP with the integer variables fixed at their optimal values.
- When a problem has several optimal solutions, the solver may return a different one from CPLEX. For example, `gas.prj` gives gas = 6.67 and chloride = 40, while the OPL book shows 20 and 30; both have objective 1800.

### Not implemented

Constraint programming (search, `solve` with non-linear or logical constraints, `var` over sets), database connections, and non-linear objectives. The solver is a dense simplex with plain branch and bound: no presolve, no cuts. That is fine for course-size models (the OPL Studio trial version was limited to 300 × 300), but it is not a substitute for CPLEX on large MIPs.

## Layout

```
src/
  lexer.ts parser.ts ast.ts   tokens and parser for .mod, .dat and .osc
  eval.ts values.ts linear.ts evaluator, runtime values and types, linear expressions
  model.ts                    instantiation, constraint generation, solving, display
  script.ts project.ts        OPLScript and .prj files
  sheet.ts files.ts           spreadsheets and file-name resolution
  solver/                     bounded two-phase simplex, branch and bound, LP-format export
  runner.ts cli.ts            command line
  run-tutorial.ts             runs every tutorial file
test/                         node:test suites
tutorial/                     the MIT OCW downloads
```
