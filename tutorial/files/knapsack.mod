
int nbItems = ...;
int nbResources = ...;
range Items 1..nbItems;
range Resources 1..nbResources;
int capacity[Resources] = ...;
int value[Items] = ...;
int use[Resources, Items] = ...;
int maxValue = max(r in Resources) capacity[r]; 

//var int take[Items] in 0..maxValue;

var int take[Items] in 0..maxint;

maximize
  sum(i in Items) value[i] * take[i]
subject to
  forall(r in Resources)
    sum(i in Items) use[r, i] * take[i] <= capacity[r];

