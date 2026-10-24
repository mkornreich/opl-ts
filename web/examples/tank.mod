// A storage tank (CP Optimizer cumul function): production batches fill it
// when they end, deliveries empty it when they start.  The tank starts with
// 5 m³, holds at most 20 m³ and can never run dry.  Minimise late deliveries.

using CP;
range Batches = 1..4;
range Orders = 1..5;
int batchTime = 3;
int batchSize[Batches] = [8, 8, 6, 6];
int orderSize[Orders] = [6, 4, 7, 5, 9];
int due[Orders] = [3, 2, 6, 8, 11];

dvar interval batch[Batches] size batchTime;
dvar interval delivery[Orders] size 1;

cumulFunction level = step(0, 5)
  + sum(b in Batches) stepAtEnd(batch[b], batchSize[b])
  - sum(o in Orders) stepAtStart(delivery[o], orderSize[o]);

dexpr int lateness = sum(o in Orders) maxl(0, endOf(delivery[o]) - due[o]);

minimize lateness;
subject to {
  level <= 20;
  noOverlap(batch);    // one reactor
}

int levelAt[t in 0..16] = cumulFunctionValue(level, t);
execute {
  writeln("tank level at t = 0..16: ", levelAt);
}
