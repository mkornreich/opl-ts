// A main block (IBM ILOG Script) that re-solves a model: the efficient
// frontier of a three-asset portfolio, one QP per target return.

{string} Assets = {"Bonds", "Stocks", "Gold"};
float expected[Assets] = [0.045, 0.095, 0.06];
float cov[Assets][Assets] = [[0.004, 0.001, 0.0002], [0.001, 0.04, 0.002], [0.0002, 0.002, 0.025]];
float target = ...;

dvar float+ share[Assets];
minimize sum(i, j in Assets) cov[i][j] * share[i] * share[j];
subject to {
  sum(a in Assets) share[a] == 1;
  sum(a in Assets) expected[a] * share[a] >= target;
}

main {
  var def = thisOplModel.modelDefinition;
  writeln("target  risk    bonds  stocks gold");
  for (var t = 0.045; t <= 0.0951; t += 0.005) {
    var data = new IloOplDataElements();
    data.target = t;
    var m = new IloOplModel(def, cplex);
    m.addDataSource(data);
    m.generate();
    if (cplex.solve()) {
      var sd = Math.sqrt(cplex.getObjValue());
      writeln(Opl.round(t * 1000) / 1000, "   ", Opl.round(sd * 10000) / 10000, "  ",
              Opl.round(m.share["Bonds"] * 100), "%    ", Opl.round(m.share["Stocks"] * 100), "%    ",
              Opl.round(m.share["Gold"] * 100), "%");
    }
    m.end();
  }
}
