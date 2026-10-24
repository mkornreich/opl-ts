// Warehouse location: which warehouses to open, and which open warehouse
// supplies each store, to minimise fixed plus supply costs.

int Fixed = 30;
{string} Warehouses = {"Bonn", "Bordeaux", "London", "Paris", "Rome"};
int NbStores = ...;
range Stores = 0..NbStores-1;
int Capacity[Warehouses] = ...;
int SupplyCost[Stores][Warehouses] = ...;

dvar boolean Open[Warehouses];
dvar boolean Supply[Stores][Warehouses];

minimize
  sum(w in Warehouses) Fixed * Open[w] +
  sum(w in Warehouses, s in Stores) SupplyCost[s][w] * Supply[s][w];

subject to {
  forall(s in Stores)
    oneWarehouse: sum(w in Warehouses) Supply[s][w] == 1;
  forall(w in Warehouses, s in Stores)
    onlyOpen: Supply[s][w] <= Open[w];
  forall(w in Warehouses)
    capacity: sum(s in Stores) Supply[s][w] <= Capacity[w];
}

execute {
  for (var w in Warehouses) if (Open[w] == 1) {
    write(w, " supplies stores");
    for (var s in Stores) if (Supply[s][w] == 1) write(" ", s);
    writeln();
  }
}
