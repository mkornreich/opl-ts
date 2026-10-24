// One machine with setup times between job families (CP Optimizer
// sequence variable with types): minimise the makespan, then the setup cost
// read through typeOfNext.

using CP;
range Jobs = 1..8;
int duration[Jobs] = [3, 2, 4, 2, 3, 1, 2, 3];
int family[Jobs]   = [0, 1, 2, 0, 1, 2, 0, 1];
int setupTime[0..2][0..2] = [[0, 2, 5], [3, 0, 2], [4, 3, 0]];
int setupCost[0..2][0..2] = [[0, 7, 1], [2, 0, 9], [6, 3, 0]];

dvar interval job[j in Jobs] size duration[j];
dvar sequence machine in job types family;

dexpr int cost = sum(j in Jobs) setupCost[family[j]][typeOfNext(machine, job[j], family[j], family[j])];

minimize staticLex(max(j in Jobs) endOf(job[j]), cost);
subject to {
  noOverlap(machine, setupTime);
}

execute {
  var order = [];
  for (var j in Jobs) order.push(j);
  order.sort(function (a, b) { return job[a].start - job[b].start; });
  writeln("order: ", order.join(" "), "   setup cost: ", cost);
}
