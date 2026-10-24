// Job shop ft06 (Fisher & Thompson, 1963): six jobs visit six machines in
// their own order; a machine does one operation at a time.  Minimise the
// makespan with CP Optimizer interval variables.  The optimum is 55.

using CP;
int nbJobs = 6;
int nbMchs = 6;
range Jobs = 0..nbJobs-1;
range Steps = 0..nbMchs-1;
tuple Op { int mch; int pt; };
Op ops[Jobs][Steps] = [
  [<2, 1>, <0, 3>, <1, 6>, <3, 7>, <5, 3>, <4, 6>],
  [<1, 8>, <2, 5>, <4, 10>, <5, 10>, <0, 10>, <3, 4>],
  [<2, 5>, <3, 4>, <5, 8>, <0, 9>, <1, 1>, <4, 7>],
  [<1, 5>, <0, 5>, <2, 5>, <3, 3>, <4, 8>, <5, 9>],
  [<2, 9>, <1, 3>, <4, 5>, <5, 4>, <0, 3>, <3, 1>],
  [<1, 3>, <3, 3>, <5, 9>, <0, 10>, <4, 4>, <2, 1>]
];
dvar interval task[j in Jobs][s in Steps] size ops[j][s].pt;
minimize max(j in Jobs) endOf(task[j][nbMchs-1]);
subject to {
  forall(m in 0..nbMchs-1) noOverlap(all(j in Jobs, s in Steps : ops[j][s].mch == m) task[j][s]);
  forall(j in Jobs, s in 0..nbMchs-2) endBeforeStart(task[j][s], task[j][s+1]);
}
