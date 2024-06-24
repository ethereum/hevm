#ifndef BN256_CURVE_H
#define BN256_CURVE_H

#include <gmp.h>

// curvePoint implements the elliptic curve y²=x³+3. Points are kept in
// Jacobian form and t=z² when valid. G₁ is the set of points of this curve on
// GF(p).
typedef struct curve_point {
  mpz_t x, y, z, t;
} curve_point;

void curve_point_new(curve_point* c);

void curve_point_clear(curve_point* c);

void curve_point_set(curve_point* c, curve_point* a);

// IsOnCurve returns true iff c is on the curve where c must be in affine form.
int curve_point_is_on_curve(curve_point* c);

void curve_point_set_infinity(curve_point* c);

int curve_point_is_infinity(curve_point* c);

void curve_point_add(curve_point* c, curve_point* a, curve_point* b);

void curve_point_double(curve_point* c, curve_point* a);

void curve_point_mul(curve_point* c, curve_point* a, mpz_t scalar);

// MakeAffine converts c to affine form and returns c. If c is ∞, then it sets
// c to 0 : 1 : 0.
void curve_point_make_affine(curve_point* c);

void curve_point_negative(curve_point* c, curve_point* a);

#endif
