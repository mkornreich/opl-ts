
/* A simple model: matrix declaration */

range ri [1..3];
range rj [1..2];

struct  Element {
int col;
int value;
};

{Element} A[ri] = [{<1,3>, <2,2>}, {<1,1>, <2,5>}, {<2,-1>}];


float b[ri] = [2000.9, 4000, -500];
float+ c[rj] = [10, 7];

var float x[rj];

maximize sum(j in rj) c[j]*x[j]
subject to{
   forall (i in ri)
/*      sum(j in rj) A[i,j]*x[j] <= b[i]; */
      sum(el in A[i]) (el.value*x[el.col]) <= b[i];
};
 
