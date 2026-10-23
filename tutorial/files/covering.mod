
range Boolean 0..1;
int nbWorkers = ...;
range Workers 1..nbWorkers;
enum Tasks ...;

{Workers} qualified[Tasks] = ...;
int cost[Workers] = ...;

var Boolean hire[Workers];

minimize 
   sum(c in Workers) cost[c]*hire[c]
subject to
{
   forall(j in Tasks)
      sum(c in qualified[j]) hire[c] >= 1;
};

{Workers} crew = { c | c in Workers : hire[c] = 1 };

display crew;



