
/* A simple model: duals and reduced costs */


constraint ct[1..3];

var float+ x[1..3];

maximize 10*x[1] + 7*x[2]

subject to{
   ct[1]: 3*x[1] + 2*x[2] <=2000;
   ct[2]: x[1] + 5*x[2] <= 4000;
   ct[3]: x[2] >= 500;
};
 

display (t in 1..3) ct[t].dual;
display(d in 1..3) <x[d], x[d].rc>; 
