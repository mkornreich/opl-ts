
/* A simple model: matrix declaration */

SheetConnection sh("E:\Program Files\examples\opl\Tutorial-1.203J\simple_project1.xls", 0); 


range ri [1..3];
range rj [1..2];

int A[ri, rj] from SheetRead(sh,"B3:C5") ;
float b[ri] = ...;
float+ c[rj] = ...;

var float x[rj];

maximize sum(j in rj) c[j]*x[j]
subject to{
   forall (i in ri)
      sum(j in rj) A[i,j]*x[j] <= b[i];
};
 
SheetWrite(sh, "G10:G11") (x);