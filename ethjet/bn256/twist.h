#ifndef BN256_TWIST_H
#define BN256_TWIST_H

#include "gfp2.h"

// twistPoint implements the elliptic curve y²=x³+3/ξ over GF(p²). Points are
// kept in Jacobian form and t=z² when valid. The group G₂ is the set of
// n-torsion points of this curve over GF(p²) (where n = Order)
typedef struct twist_point {
  gfp2 x, y, z, t;
} twist_point;

void twist_point_new(twist_point* c);

void twist_point_clear(twist_point* c);

void twist_point_set(twist_point* c, twist_point* a);

// IsOnCurve returns true iff c is on the curve where c must be in affine form.
int twist_point_is_on_curve(twist_point* c);

void twist_point_set_infinity(twist_point* c);

int twist_point_is_infinity(twist_point* c);

void twist_point_add(twist_point* c, twist_point* a, twist_point* b);

void twist_point_double(twist_point* c, twist_point* a);

void twist_point_mul(twist_point* c, twist_point* a, mpz_t scalar);

void twist_point_make_affine(twist_point* c);

void twist_point_negative(twist_point* c, twist_point* a);

#endif
