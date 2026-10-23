
/* A simple model: illustration of formalization */


int A[1..3, 1..2] = [[3, 2], [1, 5], [0, -1]];
float b[1..3] = [2000.9, 4000, -500];     // inputs declaration
float+ c[1..2] = [10, 7];

var int x[1..2] in 0..maxint;         // variable declaration

maximize sum(j in 1..2) c[j]*x[j]      // optimization model 
subject to{
   forall (i in 1..3)
      sum(j in 1..2) A[i,j]*x[j] <= b[i];
};
 
