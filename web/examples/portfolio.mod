// Markowitz portfolio: the minimum-variance mix of assets that reaches a
// target expected return (a convex quadratic program).

{string} Assets = {"Bonds", "Stocks", "Gold", "Cash", "Property"};
float expected[Assets] = [0.045, 0.095, 0.06, 0.02, 0.075];
float cov[Assets][Assets] = [
  [0.0040, 0.0010, 0.0002, 0.0000, 0.0012],
  [0.0010, 0.0400, 0.0020, 0.0000, 0.0110],
  [0.0002, 0.0020, 0.0250, 0.0000, 0.0010],
  [0.0000, 0.0000, 0.0000, 0.0001, 0.0000],
  [0.0012, 0.0110, 0.0010, 0.0000, 0.0225]
];
float target = 0.065;

dvar float+ share[Assets];

minimize sum(i, j in Assets) cov[i][j] * share[i] * share[j];

subject to {
  budget: sum(a in Assets) share[a] == 1;
  yield: sum(a in Assets) expected[a] * share[a] >= target;
}

execute {
  writeln("risk (standard deviation): ", Math.sqrt(cplex.getObjValue()));
}
