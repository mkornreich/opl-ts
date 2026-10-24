// The CPLEX solution pool: populate() keeps the optimum and enumerates more
// feasible solutions, here every way to choose a 3-item basket within budget.

{string} Items = {"apple", "bread", "cheese", "dates", "eggs"};
int price[Items] = [2, 3, 5, 4, 3];
int value[Items] = [3, 4, 8, 6, 5];
int budget = 11;

dvar boolean take[Items];
maximize sum(i in Items) value[i] * take[i];
subject to {
  sum(i in Items) take[i] == 3;
  sum(i in Items) price[i] * take[i] <= budget;
}

main {
  thisOplModel.generate();
  cplex.populatelim = 20;
  if (cplex.populate()) {
    writeln(cplex.solnPoolNsolns, " baskets:");
    for (var s = 0; s < cplex.solnPoolNsolns; s++) {
      thisOplModel.setPoolSolution(s);
      var line = "";
      var v = 0;
      for (var i in thisOplModel.Items) if (thisOplModel.take[i] == 1) {
        line += " " + i;
        v += thisOplModel.value[i];
      }
      writeln("  value ", v, ":", line);
    }
  }
}
