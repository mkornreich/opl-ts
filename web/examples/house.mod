// House building with three workers (OPL 3 scheduling): each task needs one
// worker who is able to do it; minimise the longest time a worker is on
// site.  AlternativeResources choose the worker of each task.

enum Tasks { masonry, carpentry, plumbing, ceiling, roofing, painting, windows, facade, garden, moving };
int duration[Tasks] = [7, 3, 8, 3, 1, 2, 1, 2, 1, 1];
int totalDuration = sum(t in Tasks) duration[t];
scheduleHorizon = totalDuration;
enum Workers { joe, jack, jim };
{Workers} cannotDo[Tasks] = #[
  masonry: { jim }, carpentry: { jack }, plumbing: { joe, jim }, ceiling: { jack },
  roofing: { jack }, painting: { joe }, windows: { jack }, facade: { jim },
  garden: {}, moving: { jack } ]#;

Activity task[t in Tasks](duration[t]);
var int onSite[Workers] in 0..totalDuration;
Activity attendance[w in Workers](onSite[w]);
UnaryResource worker[Workers];
AlternativeResources crew(worker);

minimize max(w in Workers) onSite[w]
subject to {
  task[masonry] precedes task[carpentry];  task[masonry] precedes task[plumbing];
  task[masonry] precedes task[ceiling];    task[carpentry] precedes task[roofing];
  task[ceiling] precedes task[painting];   task[roofing] precedes task[windows];
  task[roofing] precedes task[facade];     task[plumbing] precedes task[facade];
  task[roofing] precedes task[garden];     task[plumbing] precedes task[garden];
  task[windows] precedes task[moving];     task[facade] precedes task[moving];
  task[garden] precedes task[moving];      task[painting] precedes task[moving];
  forall(t in Tasks) task[t] requires crew;
  forall(t in Tasks, w in cannotDo[t]) not activityHasSelectedResource(task[t], crew, worker[w]);
  forall(t in Tasks, w in Workers)
    activityHasSelectedResource(task[t], crew, worker[w]) =>
      attendance[w].start <= task[t].start & attendance[w].end >= task[t].end;
};

{Workers} who[t in Tasks] = { w | w in Workers : activityHasSelectedResource(task[t], crew, worker[w]) };
display who;
