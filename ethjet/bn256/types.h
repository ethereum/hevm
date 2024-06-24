#include <gmp.h>

// gfP2 implements a field of size p² as a quadratic extension of the base
// field where i²=-1.
typedef struct gfp2 {
  mpz_t x, y; // value is xi+y.
} gfp2;

// gfP6 implements the field of size p⁶ as a cubic extension of gfP2 where τ³=ξ
// and ξ=i+9.
typedef struct gfp6 {
  gfp2 x, y, z; // value is xτ² + yτ + z
} gfp6;
