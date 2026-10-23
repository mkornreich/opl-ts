# opl-ts

An implementation of **OPL**, the Optimization Programming Language of ILOG OPL Studio and IBM ILOG CPLEX Optimization Studio, in TypeScript. It has its own solvers, so neither CPLEX nor CP Optimizer is needed:

- a bounded two-phase **simplex** with duals and reduced costs, and **branch and bound** for MIPs;
- a **finite-domain constraint-programming** solver with propagation, search procedures, scheduling resources and float intervals.

It covers both dialects: OPL 3.x (`var`, `solve`, `search`, OPLScript `.osc`, `Activity` / `UnaryResource`) and modern OPL (`dvar`, `tuple`, `dexpr`, `constraints`, `using CP`, `execute` / `main` blocks in IBM ILOG Script).

It runs the material from the OPL Studio tutorial of MIT OpenCourseWare
[1.206J Airline Schedule Planning (Spring 2003), Study Materials](https://ocw.mit.edu/courses/1-206j-airline-schedule-planning-spring-2003/pages/study-materials/), and it was checked against OPL models published on GitHub (see [Verification](#verification)).

## Quick start

```bash
npm install
npm test            # builds, then runs the test suite (includes every tutorial file)
npm run tutorial    # runs all tutorial models, projects and the script
```

Run a single file:

```bash
node dist/src/cli.js tutorial/files/covering.prj
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
| `--time-limit S` | stop the search after S seconds and report the best solution found |
| `--export-lp F` | also write the generated problem to `F` in CPLEX LP format |
| `--cp` | solve with constraint programming even when the model is linear |
| `--all-solutions` | constraint programming without objective: print every solution |

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

The files refer to `E:\Program Files\examples\opl\Tutorial-1.203J\...`. When such a path does not exist, the file with the same name next to the model is used, and a note is printed, so the originals run unmodified. `npm run tutorial` works on a copy in `tutorial/run/` because the script and `SheetWrite` overwrite `ouput.txt` and `simple_project1.xls`, as OPL Studio did. Spreadsheets are rewritten with [SheetJS](https://sheetjs.com), which keeps the cell values but not the formatting.

## The language

**Data**: `int`, `int+`, `float`, `float+`, `string`, `boolean`, `range`, `enum`, `struct` / `tuple` (with `key` fields, so data can refer to a tuple by its key), sets `{T}` / `setof(T)` / `sorted {T}`, multi-dimensional and generic arrays (`int a[i in R] = i*i;`), array comprehensions (`[i : v | <i,v> in S]`, nested), set comprehensions, `#[ ]#`, `#< >#`, `union` / `inter` aggregates, `with` clauses, `assert [forall(...)]`, `include "file";`. Initialisation from `.dat` files (`= ...`), spreadsheets (`from SheetRead`), databases (`from DBread`), files (`< "file"`) and prompts (`<< "text"`).

**Variables and expressions**: `var` (OPL 3, `var float` is free) and `dvar` (modern, non-negative by default), `int`, `float`, `boolean`, enum and set domains (`var Colors c; var int x in {1, 3, 5};`), `dexpr`, dvar alias arrays (`dvar int x[1..3] = [a, b, c];`). Linear and non-linear arithmetic (`*`, `/`, `div`, `mod`, `^`, `abs`, `min`, `max`, `floor`, `sqrt`, `exp`, `log`, ...), `x[y]` element expressions (also on multi-dimensional arrays), `piecewise{...}` linear functions and `pwlFunction`, `sum` / `prod` / `min` / `max` / `and` / `or` / `all` aggregates, tuple patterns that bind, filter on bound iterators, or match expressions (`<n, s.dept> in S`), `forall(ordered i, j in S)`, and `ordered by increasing|decreasing expr`.

**Constraints**: linear (`<=`, `>=`, `==`, ranges `lo <= e <= hi`), strict and `!=`, logical (`&&`, `||`, `!`, `=>`, `<=>`, `ifThen`) and meta-constraints (`sum(i in R) (x[i] == 3) == 2`), labels (`ct:`, `ct[i]:`, labels inside or in front of `forall`, with `.dual` / `.slack`), and global constraints: `alldifferent` / `allDifferent` (with `onDomain`), `distribute`, `atmost`, `atleast`, `count`, `circuit`, `subCircuit`, `allowedAssignments`, `forbiddenAssignments`, OPL 3 `predicate`s, `lex`, `inverse`, `pack`, `allMinDistance`.

**Objectives**: `minimize` / `maximize`, `staticLex(c1, c2, ...)` (solved lexicographically), or none (`solve { }` / `constraints { }`).

**Search** (OPL 3): `search { ... }` with `forall`, `tryall`, `select`, `try ... | ... endtry`, `if ... then ... else ... endif`, `while ... do`, `generate`, `generateSeq`, `LDSearch(k)`, and `dsize`, `dmin`, `dmax`, `bound`, `regretdmin`, `regretdmax`, `dnext`, `dprev`.

**Scheduling**: OPL 3 `scheduleHorizon`, `Activity a(d)` (variable durations), `UnaryResource`, `DiscreteResource`, `Reservoir`, `StateResource`, `AlternativeResources`, `precedes`, `requires(k)`, `consumes`, `produces`, `startsAfterEnd` and the other precedence functions, `activityHasSelectedResource`, and the search instructions `setTimes`, `rank`, `tryRankFirst`, `isRanked`, `nbPossibleFirst`, `isPossibleFirst`, `assignAlternatives`. CP Optimizer `dvar interval a [optional] [in lo..hi] size s`, `startOf` / `endOf` / `sizeOf` / `presenceOf`, `endBeforeStart` and the other precedences, `noOverlap`, and `cumulFunction` / `pulse` with `f <= C`.

**Output**: `display [(q)] expr`, `SheetWrite`, `DBupdate` / `DBexecute`, and in `.dat` files `SheetConnection`, `x from SheetRead(...)`, `x to SheetWrite(...)`.

**Scripts**: OPLScript `.osc` files (OPL 3: `Model m(...) editMode`, `ofile`, `cout <<`, `forall`, `while`, `repeat ... until`, `m.solve()`, `m.nextSolution()`, `import enum`, `Basis`), and IBM ILOG Script in `execute { }` and `main { }` blocks, run as JavaScript: model elements by name, `thisOplModel`, `cplex` and `cp` (parameters, `solve`, `getObjValue`, `startNewSearch` / `next`, `info`, `exportModel`), `writeln`, `Opl.*`, `IloOplModel` / `IloOplModelDefinition` / `IloOplDataSource` / `dataElements` for models that change data and solve again, `IloOplOutputFile`, `IloOplInputFile`.

**Projects** (`.prj`): `MODEL`, one or more `DATA`, `hide_zero`, `nodeSel`. **Databases**: the `sqlite` driver of `DBconnection` (Node's built-in SQLite).

### Which solver

A model is solved as an LP / MIP unless it needs constraint programming. Logical constraints, meta-constraints, `abs`, `min`, `max`, `piecewise`, element expressions, `!=` and strict inequalities are linearized, as CPLEX does: `abs` / `max` in a convex position become plain rows, otherwise a big-M formulation with binaries. A model goes to the CP solver when it has `using CP`, a `search` block, `alldifferent` or another global constraint, scheduling, products of non-binary variables, or unbounded terms that cannot be linearized, or when `--cp` or `--all-solutions` is given.

### Semantics worth knowing

- `var float x` (OPL 3) is free; `dvar float x` (modern) is non-negative. A bound of `maxint` counts as infinite.
- `display` prints floats with 4 decimals. OPLScript `<<` prints them like `printf("%f")`, which is the format of the original `ouput.txt`.
- Duals and reduced costs follow the CPLEX convention, d(objective)/d(rhs) in the model's own sense. For MIPs they come from the LP with the integer variables fixed at their optimal values.
- When a problem has several optimal solutions, the solver may return a different one from CPLEX or CP Optimizer.
- Arrays in `.dat` files that are shorter than declared are padded with zeros, and sparse comprehensions leave unset elements at zero.

### Not implemented

- Quadratic programming: products of continuous variables go to the CP solver, which only approximates continuous optima.
- CPLEX model-modification APIs in scripts (`setCoef`, `setObjCoef`), `IloOplExec`, CP Optimizer `dvar sequence` with transition types, `alternative` / `span` intervals, breakable activities, transition times.
- Solver performance: the simplex is dense and branch and bound has no presolve or cuts, and the CP solver is a plain propagation engine. That is fine for course-size models (the OPL Studio trial version was limited to 300 × 300) and the published examples, but not a substitute for CPLEX on large problems.

## Verification

- The test suite (`npm test`) covers the tutorial, the language, the solvers, CP, scheduling, scripts and databases.
- The simplex and branch and bound were compared with HiGHS on 400 random LPs and MIPs, the CP solver with brute-force enumeration on 600 random logical / non-linear models, and the MIP linearization (and CP) with brute force on 500 more.
- **OPL models from GitHub**: 316 models from 55 repositories (IBM's samples, Alex Fleischer's *how to with OPL* and Ponder This models, Håkan Kjellerstrand's CP models, course and research code), found with GitHub code search. 229 run. 72 cannot run anywhere because their data or included files are not in the repository (sub-models fed by a driver, data generated by Python, ...), 8 are large puzzles that exceed a 20-second limit, and 7 use the unsupported features listed above or are invalid. That is 229 of the 244 runnable models (94%). All 44 LP/MIP models with an objective to compare give the same optimum as HiGHS, and spot checks of CP puzzles (zebra, SEND+MORE, sudoku, map colouring) give the known solutions.

  To repeat it (the corpus is third-party code, kept in the git-ignored `corpus/` folder):

  ```bash
  scripts/corpus/search.sh corpus
  python3 scripts/corpus/fetch.py corpus
  npm run build && python3 scripts/corpus/run.py corpus results.json
  ```

## Layout

```
src/
  lexer.ts parser.ts ast.ts   tokens and parser for .mod, .dat and .osc
  eval.ts values.ts linear.ts evaluator, runtime values and types, linear expressions
  model.ts                    instantiation, generation, solver choice, display
  ilog.ts                     IBM ILOG Script (execute / main blocks)
  script.ts project.ts        OPLScript and .prj files
  sheet.ts db.ts files.ts     spreadsheets, databases and file-name resolution
  solver/                     bounded two-phase simplex, branch and bound, LP-format export
  cp/                         domains, propagators, scheduling, search, CP flattening, linearization
  runner.ts cli.ts            command line
  run-tutorial.ts             runs every tutorial file
test/                         node:test suites
scripts/corpus/               fetches and runs OPL models published on GitHub
tutorial/                     the MIT OCW downloads
```
