// Haverly's pooling problem: crudes A and B are mixed in a pool, then blended
// with crude C into products X and Y with sulphur limits.  The pool quality
// p multiplies the flows out of the pool, which makes the constraints
// bilinear (non-convex).  The global optimum is a profit of 400.

dvar float+ fromA;    // crude A into the pool
dvar float+ fromB;    // crude B into the pool
dvar float+ poolX;    // pool to product X
dvar float+ poolY;    // pool to product Y
dvar float+ cX;       // crude C straight to X
dvar float+ cY;       // crude C straight to Y
dvar float p in 1..3; // sulphur content of the pool (%)

maximize 9 * (poolX + cX) + 15 * (poolY + cY) - 6 * fromA - 16 * fromB - 10 * (cX + cY);

subject to {
  balance: fromA + fromB == poolX + poolY;
  quality: p * (poolX + poolY) == 3 * fromA + 1 * fromB;
  sulphurX: p * poolX + 2 * cX <= 2.5 * (poolX + cX);
  sulphurY: p * poolY + 2 * cY <= 1.5 * (poolY + cY);
  demandX: poolX + cX <= 100;
  demandY: poolY + cY <= 200;
}
