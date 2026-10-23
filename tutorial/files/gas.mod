
enum Products ...;
enum Components ...;

float+ demand[Products, Components] = ...;
float+ profit[Products] = ...;
float+ stock[Components] = ...;

var float+ production[Products];
maximize
  sum (p in Products) profit[p] * production[p]
subject to {
  forall (c in Components)
    sum (p in Products) demand[p, c] * production[p] <= stock[c]
};







