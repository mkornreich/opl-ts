
/* A simple model */

var float x[1..2];  // variable declaration 

maximize 10*x[1] + 7*x[2]

subject to{
   3*x[1] + 2*x[2] <=2000.9;
   x[1] + 5*x[2] <= 4000;
   x[2] >= 500;
};
 
