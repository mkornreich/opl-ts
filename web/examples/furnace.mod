// Heat treatment in one furnace (CP Optimizer state function): each part
// needs its temperature for its whole treatment, parts at one temperature
// can be treated together as a batch (aligned starts and ends, at most three
// at a time), and changing the temperature takes 2 time units per step.

using CP;
range Parts = 1..8;
int temp[Parts] = [1, 2, 1, 3, 2, 1, 3, 2];
int dur[Parts]  = [4, 3, 4, 5, 3, 4, 5, 3];
tuple change { int from; int to; int time; };
{change} heating = { <f, t, 2 * abs(t - f)> | f in 1..3, t in 1..3 };

dvar interval treat[p in Parts] size dur[p];
stateFunction furnace with heating;
cumulFunction load = sum(p in Parts) pulse(treat[p], 1);

minimize max(p in Parts) endOf(treat[p]);
subject to {
  forall(p in Parts) alwaysEqual(furnace, treat[p], temp[p], true, true);
  load <= 3;
}

tuple batch { int start; int end; int temperature; };
{batch} batches = { <segmentStart(furnace, i), segmentEnd(furnace, i), segmentValue(furnace, i)>
                    | i in 0..numberOfSegments(furnace) - 1 : segmentValue(furnace, i) >= 0 };
execute {
  writeln("batches <start, end, temperature>: ", batches);
}
