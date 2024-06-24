// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#include <gmp.h>
#include "constants.h"
#include "curve.h"
#include "stdio.h"

// var curveB = new(big.Int).SetInt64(3)

// curveGen is the generator of G₁.
/*var curveGen = &curvePoint{
  new(big.Int).SetInt64(1),
  new(big.Int).SetInt64(2),
  new(big.Int).SetInt64(1),
  new(big.Int).SetInt64(1),
}*/

void curve_point_new(curve_point* c) {
  mpz_init(c->x);
  mpz_init(c->y);
  mpz_init(c->z);
  mpz_init(c->t);
}

void curve_point_clear(curve_point* c) {
  mpz_clear(c->x);
  mpz_clear(c->y);
  mpz_clear(c->z);
  mpz_clear(c->t);
}

void curve_point_set(curve_point* c, curve_point* a) {
  mpz_set(c->x, a->x);
  mpz_set(c->y, a->y);
  mpz_set(c->z, a->z);
  mpz_set(c->t, a->t);
}

// IsOnCurve returns true iff c is on the curve where c must be in affine form.
int curve_point_is_on_curve(curve_point* c) {
  static unsigned curveB = 3;
  mpz_t yy;
  mpz_init(yy);
  mpz_mul(yy, c->y, c->y);
  mpz_t xxx;
  mpz_init(xxx);
  mpz_mul(xxx, c->x, c->x);
  mpz_mul(xxx, xxx, c->x);
  mpz_sub(yy, yy, xxx);
  mpz_sub_ui(yy, yy, curveB);
  if (mpz_sgn(yy) < 0 || mpz_cmp(yy, P) >= 0) {
    mpz_mod(yy, yy, P);
  }
  return mpz_sgn(yy) == 0;
}

void curve_point_set_infinity(curve_point* c) {
  mpz_set_ui(c->z, 0);
}

int curve_point_is_infinity(curve_point* c) {
  return mpz_sgn(c->z) == 0;
}

void curve_point_double(curve_point* c, curve_point* a);
void curve_point_add(curve_point* c, curve_point* a, curve_point* b) {
  if (curve_point_is_infinity(a)) {
    curve_point_set(c, b);
    return;
  }
  if (curve_point_is_infinity(b)) {
    curve_point_set(c, a);
    return;
  }

  // See http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-0/addition/add-2007-bl.op3

  // Normalize the points by replacing a = [x1:y1:z1] and b = [x2:y2:z2]
  // by [u1:s1:z1·z2] and [u2:s2:z1·z2]
  // where u1 = x1·z2², s1 = y1·z2³ and u1 = x2·z1², s2 = y2·z1³
  mpz_t z1z1;
  mpz_init(z1z1);
  mpz_mul(z1z1, a->z, a->z);
  mpz_mod(z1z1, z1z1, P);
  mpz_t z2z2;
  mpz_init(z2z2);
  mpz_mul(z2z2, b->z, b->z);
  mpz_mod(z2z2, z2z2, P);
  mpz_t u1;
  mpz_init(u1);
  mpz_mul(u1, a->x, z2z2);
  mpz_mod(u1, u1, P);
  mpz_t u2;
  mpz_init(u2);
  mpz_mul(u2, b->x, z1z1);
  mpz_mod(u2, u2, P);

  mpz_t t;
  mpz_init(t);
  mpz_mul(t, b->z, z2z2);
  mpz_mod(t, t, P);
  mpz_t s1;
  mpz_init(s1);
  mpz_mul(s1, a->y, t);
  mpz_mod(s1, s1, P);

  mpz_mul(t, a->z, z1z1);
  mpz_mod(t, t, P);
  mpz_t s2;
  mpz_init(s2);
  mpz_mul(s2, b->y, t);
  mpz_mod(s2, s2, P);

  // Compute x = (2h)²(s²-u1-u2)
  // where s = (s2-s1)/(u2-u1) is the slope of the line through
  // (u1,s1) and (u2,s2). The extra factor 2h = 2(u2-u1) comes from the value of z below.
  // This is also:
  // 4(s2-s1)² - 4h²(u1+u2) = 4(s2-s1)² - 4h³ - 4h²(2u1)
  //                        = r² - j - 2v
  // with the notations below.
  mpz_t h;
  mpz_init(h);
  mpz_sub(h, u2, u1);
  int xEqual = mpz_sgn(h) == 0;

  mpz_add(t, h, h);
  // i = 4h²
  mpz_t i;
  mpz_init(i);
  mpz_mul(i, t, t);
  mpz_mod(i, i, P);
  // j = 4h³
  mpz_t j;
  mpz_init(j);
  mpz_mul(j, h, i);
  mpz_mod(j, j, P);

  mpz_sub(t, s2, s1);
  int yEqual = mpz_sgn(t) == 0;
  if (xEqual && yEqual) {
    curve_point_double(c, a);
    return;
  }
  mpz_t r;
  mpz_init(r);
  mpz_add(r, t, t);

  mpz_t v;
  mpz_init(v);
  mpz_mul(v, u1, i);
  mpz_mod(v, v, P);

  // t4 = 4(s2-s1)²
  mpz_t t4;
  mpz_init(t4);
  mpz_mul(t4, r, r);
  mpz_mod(t4, t4, P);
  mpz_add(t, v, v);
  mpz_t t6;
  mpz_init(t6);
  mpz_sub(t6, t4, j);
  mpz_sub(c->x, t6, t);

  // Set y = -(2h)³(s1 + s*(x/4h²-u1))
  // This is also
  // y = - 2·s1·j - (s2-s1)(2x - 2i·u1) = r(v-x) - 2·s1·j
  mpz_sub(t, v, c->x); // t7
  mpz_mul(t4, s1, j); // t8
  mpz_mod(t4, t4, P);
  mpz_add(t6, t4, t4); // t9
  mpz_mul(t4, r, t);   // t10
  mpz_mod(t4, t4, P);
  mpz_sub(c->y, t4, t6);

  // Set z = 2(u2-u1)·z1·z2 = 2h·z1·z2
  mpz_add(t, a->z, b->z); // t11
  mpz_mul(t4, t, t);    // t12
  mpz_mod(t4, t4, P);
  mpz_sub(t, t4, z1z1); // t13
  mpz_sub(t4, t, z2z2); // t14
  mpz_mul(c->z, t4, h);
  mpz_mod(c->z, c->z, P);

  mpz_clear(z1z1);
  mpz_clear(z2z2);
  mpz_clear(u1);
  mpz_clear(u2);
  mpz_clear(t);
  mpz_clear(s1);
  mpz_clear(s2);
  mpz_clear(h);
  mpz_clear(i);
  mpz_clear(j);
  mpz_clear(r);
  mpz_clear(v);
  mpz_clear(t4);
  mpz_clear(t6);
}

void curve_point_double(curve_point* c, curve_point* a) {
  // See http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-0/doubling/dbl-2009-l.op3
  mpz_t A;
  mpz_init(A);
  mpz_mul(A, a->x, a->x);
  mpz_mod(A, A, P);
  mpz_t B;
  mpz_init(B);
  mpz_mul(B, a->y, a->y);
  mpz_mod(B, B, P);
  mpz_t C_;
  mpz_init(C_);
  mpz_mul(C_, B, B);
  mpz_mod(C_, C_, P);

  mpz_t t;
  mpz_init(t);
  mpz_add(t, a->x, B);
  mpz_t t2;
  mpz_init(t2);
  mpz_mul(t2, t, t);
  mpz_mod(t2, t2, P);
  mpz_sub(t, t2, A);
  mpz_sub(t2, t, C_);
  mpz_t d;
  mpz_init(d);
  mpz_add(d, t2, t2);
  mpz_add(t, A, A);
  mpz_t e;
  mpz_init(e);
  mpz_add(e, t, A);
  mpz_t f;
  mpz_init(f);
  mpz_mul(f, e, e);
  mpz_mod(f, f, P);

  mpz_add(t, d, d);
  mpz_sub(c->x, f, t);

  mpz_add(t, C_, C_);
  mpz_add(t2, t, t);
  mpz_add(t, t2, t2);
  mpz_sub(c->y, d, c->x);
  mpz_mul(t2, e, c->y);
  mpz_mod(t2, t2, P);
  mpz_sub(c->y, t2, t);

  mpz_mul(t, a->y, a->z);
  mpz_mod(t, t, P);
  mpz_add(c->z, t, t);

  mpz_clear(A);
  mpz_clear(B);
  mpz_clear(C_);
  mpz_clear(t);
  mpz_clear(t2);
  mpz_clear(d);
  mpz_clear(e);
  mpz_clear(f);
}

void curve_point_mul(curve_point* c, curve_point* a, mpz_t scalar) {
  curve_point sum;
  curve_point_new(&sum);
  curve_point_set_infinity(&sum);
  curve_point t;
  curve_point_new(&t);

  for (int i = mpz_sizeinbase(scalar, 2); i >= 0; i--) {
    curve_point_double(&t, &sum);
    if (mpz_tstbit(scalar, i) != 0) {
      curve_point_add(&sum, &t, a);
    } else {
      curve_point_set(&sum, &t);
    }
  }

  curve_point_set(c, &sum);
  curve_point_clear(&sum);
  curve_point_clear(&t);
}

// MakeAffine converts c to affine form and returns c. If c is ∞, then it sets
// c to 0 : 1 : 0.
void curve_point_make_affine(curve_point* c) {
  if (mpz_sizeinbase(c->z, 2) == 1 && mpz_tstbit(c->z, 0) == 1) {
    return;
  }
  if (curve_point_is_infinity(c)) {
    mpz_set_ui(c->x, 0);
    mpz_set_ui(c->y, 1);
    mpz_set_ui(c->z, 0);
    mpz_set_ui(c->t, 0);
    return;
  }
  mpz_t zInv;
  mpz_init(zInv);
  mpz_invert(zInv, c->z, P);
  mpz_t t;
  mpz_init(t);
  mpz_mul(t, c->y, zInv);
  mpz_mod(t, t, P);
  mpz_t zInv2;
  mpz_init(zInv2);
  mpz_mul(zInv2, zInv, zInv);
  mpz_mod(zInv2, zInv2, P);
  mpz_mul(c->y, t, zInv2);
  mpz_mod(c->y, c->y, P);
  mpz_mul(t, c->x, zInv2);
  mpz_mod(t, t, P);
  mpz_set(c->x, t);
  mpz_set_ui(c->z, 1);
  mpz_set_ui(c->t, 1);

  mpz_clear(zInv);
  mpz_clear(t);
  mpz_clear(zInv2);
}

void curve_point_negative(curve_point* c, curve_point* a) {
  mpz_set(c->x, a->x);
  mpz_neg(c->y, a->y);
  mpz_set(c->z, a->z);
  mpz_set_ui(c->t, 0);
}
