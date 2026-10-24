// N queens with constraint programming: no two queens share a row, a
// column or a diagonal.

using CP;
int n = 12;
range R = 1..n;
dvar int queen[R] in R;   // queen[c] is the row of the queen in column c

subject to {
  allDifferent(queen);
  allDifferent(all(c in R) queen[c] + c);
  allDifferent(all(c in R) queen[c] - c);
}

execute {
  for (var r = 1; r <= n; r++) {
    var line = "";
    for (var c = 1; c <= n; c++) line += queen[c] == r ? " Q" : " .";
    writeln(line);
  }
}
