
enum Products ...;
enum Resources ...;

struct ProductData {
   float+ demand;
   float+ insideCost;
   float+ outsideCost;
   float+ consumption[Resources];
};

ProductData product[Products] = ...;
float+ capacity[Resources] = ...;

var float+ inside[Products];
var float+ outside[Products];

minimize
   sum(p in Products) (product[p].insideCost*inside[p] + 
                       product[p].outsideCost*outside[p])
subject to {
   forall(r in Resources)
      sum(p in Products) product[p].consumption[r] * inside[p] <= capacity[r];

   forall(p in Products)
      inside[p] + outside[p] >= product[p].demand;
};

display(p in Products) <inside[p],inside[p].rc>;

