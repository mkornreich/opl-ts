// Transportation problem (Dantzig): ship cases from canning plants to markets
// at least freight cost.  The duals of the demand rows are the marginal cost
// of one more case delivered to each market.

{string} Plants = {"Seattle", "San Diego"};
{string} Markets = {"New York", "Chicago", "Topeka"};

float supply[Plants] = [350, 600];
float demand[Markets] = [325, 300, 275];
// thousands of miles
float distance[Plants][Markets] = [[2.5, 1.7, 1.8], [2.5, 1.8, 1.4]];
float freight = 90;  // dollars per case per thousand miles

dvar float+ ship[Plants][Markets];

minimize sum(p in Plants, m in Markets) freight * distance[p][m] * ship[p][m] / 1000;

subject to {
  forall(p in Plants)
    capacity: sum(m in Markets) ship[p][m] <= supply[p];
  forall(m in Markets)
    need: sum(p in Plants) ship[p][m] >= demand[m];
}

execute {
  for (var m in Markets)
    writeln("marginal cost in ", m, ": ", Opl.round(need[m].dual * 1e6) / 1e6);
}
