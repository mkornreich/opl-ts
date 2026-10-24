// Sudoku: fill the grid so that every row, column and 3x3 box holds 1..9.
// Zeros in the puzzle are blanks.

using CP;
range R = 1..9;
int puzzle[R][R] = [
  [5, 3, 0, 0, 7, 0, 0, 0, 0],
  [6, 0, 0, 1, 9, 5, 0, 0, 0],
  [0, 9, 8, 0, 0, 0, 0, 6, 0],
  [8, 0, 0, 0, 6, 0, 0, 0, 3],
  [4, 0, 0, 8, 0, 3, 0, 0, 1],
  [7, 0, 0, 0, 2, 0, 0, 0, 6],
  [0, 6, 0, 0, 0, 0, 2, 8, 0],
  [0, 0, 0, 4, 1, 9, 0, 0, 5],
  [0, 0, 0, 0, 8, 0, 0, 7, 9]
];
dvar int cell[R][R] in R;

subject to {
  forall(i, j in R : puzzle[i][j] > 0) cell[i][j] == puzzle[i][j];
  forall(i in R) allDifferent(all(j in R) cell[i][j]);
  forall(j in R) allDifferent(all(i in R) cell[i][j]);
  forall(bi, bj in 0..2) allDifferent(all(i, j in 1..3) cell[3 * bi + i][3 * bj + j]);
}

execute {
  for (var i in R) {
    var line = "";
    for (var j in R) line += " " + cell[i][j] + (j % 3 == 0 && j < 9 ? " |" : "");
    writeln(line);
    if (i % 3 == 0 && i < 9) writeln("-------+-------+-------");
  }
}
