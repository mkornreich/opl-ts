
/* A simple model: matrix declaration */

range ri [1..3];
range rj [1..2];

int A[ri, rj] = #[
   2: [1, 5], 
   1: [3, 2], 
   3: [0, -1]]#;

float b[ri] = [2000.9, 4000, -500];
float+ c[rj] = [10, 7];

var float x[rj];

maximize sum(j in rj) c[j]*x[j]
subject to{
   forall (i in ri)
      sum(j in rj) A[i,j]*x[j] <= b[i]; 
};
 
