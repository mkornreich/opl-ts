// Tasks on a calendar (CP Optimizer intensity): work stops on weekends, so
// a task's length can exceed its size; inspections may not touch a weekend.

using CP;
// Days 5-6, 12-13 and 19-20 are weekends.
stepFunction workdays = stepwise { 100 -> 5; 0 -> 7; 100 -> 12; 0 -> 14; 100 -> 19; 0 -> 21; 100 };
range Tasks = 1..4;
int size[Tasks] = [4, 6, 3, 5];

dvar interval task[t in Tasks] size size[t] intensity workdays;
dvar interval inspect[t in Tasks] size 1;

minimize max(t in Tasks) endOf(inspect[t]);
subject to {
  noOverlap(task);
  forall(t in Tasks) {
    endBeforeStart(task[t], inspect[t]);
    forbidExtent(inspect[t], workdays);
  }
}
