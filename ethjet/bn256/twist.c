// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#include "gfp2.h"
#include "constants.h"
#include "twist.h"

/*
var twistB = &gfP2{
  bigFromBase10("266929791119991161246907387137283842545076965332900288569378510910307636690"),
  bigFromBase10("19485874751759354771024239261021720505790618469301721065564631296452457478373"),
}

// twistGen is the generator of group G₂.
var twistGen = &twistPoint{
  &gfP2{
    bigFromBase10("11559732032986387107991004021392285783925812861821192530917403151452391805634"),
    bigFromBase10("10857046999023057135944570762232829481370756359578518086990519993285655852781"),
  },
  &gfP2{
    bigFromBase10("4082367875863433681332203403145435568316851327593401208105741076214120093531"),
    bigFromBase10("8495653923123431417604973247489272438418190587263600148770280649306958101930"),
  },
  &gfP2{
    bigFromBase10("0"),
    bigFromBase10("1"),
  },
  &gfP2{
    bigFromBase10("0"),
    bigFromBase10("1"),
  },
}
*/

void twist_point_new(twist_point* c) {
  gfp2_new(&c->x);
  gfp2_new(&c->y);
  gfp2_new(&c->z);
  gfp2_new(&c->t);
}

void twist_point_clear(twist_point* c) {
  gfp2_clear(&c->x);
  gfp2_clear(&c->y);
  gfp2_clear(&c->z);
  gfp2_clear(&c->t);
}

void twist_point_set(twist_point* c, twist_point* a) {
  gfp2_set(&c->x, &a->x);
  gfp2_set(&c->y, &a->y);
  gfp2_set(&c->z, &a->z);
  gfp2_set(&c->t, &a->t);
}

gfp2 twistB;

// IsOnCurve returns true iff c is on the curve where c must be in affine form.
int twist_point_is_on_curve(twist_point* c) {
  static int twistB_initialized = 0;
  if (!twistB_initialized) {
    mpz_set_str(twistB.x, "266929791119991161246907387137283842545076965332900288569378510910307636690", 10);
    mpz_set_str(twistB.y, "19485874751759354771024239261021720505790618469301721065564631296452457478373", 10);
    twistB_initialized = 1;
  }

  gfp2 yy;
  gfp2_new(&yy);
  gfp2_square(&yy, &c->y);
  gfp2 xxx;
  gfp2_new(&xxx);
  gfp2_square(&xxx, &c->x);
  gfp2_mul(&xxx, &xxx, &c->x);
  gfp2_sub(&yy, &yy, &xxx);
  gfp2_sub(&yy, &yy, &twistB);
  gfp2_minimal(&yy);

  if (mpz_sgn(yy.x) != 0 || mpz_sgn(yy.y) != 0) {
    gfp2_clear(&yy);
    gfp2_clear(&xxx);
    return 0;
  }
  twist_point cneg;
  twist_point_new(&cneg);
  twist_point_mul(&cneg, c, order);

  gfp2_clear(&yy);
  gfp2_clear(&xxx);
  int cneg_is_zero = gfp2_is_zero(&cneg.z);
  twist_point_clear(&cneg);
  return cneg_is_zero;
}

void twist_point_set_infinity(twist_point* c) {
  gfp2_set_zero(&c->z);
}

int twist_point_is_infinity(twist_point* c) {
  return gfp2_is_zero(&c->z);
}

void twist_point_add(twist_point* c, twist_point* a, twist_point* b) {
  // For additional comments, see the same function in curve.go.

  if (twist_point_is_infinity(a)) {
    twist_point_set(c, b);
    return;
  }
  if (twist_point_is_infinity(b)) {
    twist_point_set(c, a);
    return;
  }

  // See http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-0/addition/add-2007-bl.op3
  gfp2 z1z1;
  gfp2_new(&z1z1);
  gfp2_square(&z1z1, &a->z);
  gfp2 z2z2;
  gfp2_new(&z2z2);
  gfp2_square(&z2z2, &b->z);
  gfp2 u1;
  gfp2_new(&u1);
  gfp2_mul(&u1, &a->x, &z2z2);
  gfp2 u2;
  gfp2_new(&u2);
  gfp2_mul(&u2, &b->x, &z1z1);

  gfp2 t;
  gfp2_new(&t);
  gfp2_mul(&t, &b->z, &z2z2);
  gfp2 s1;
  gfp2_new(&s1);
  gfp2_mul(&s1, &a->y, &t);

  gfp2_mul(&t, &a->z, &z1z1);
  gfp2 s2;
  gfp2_new(&s2);
  gfp2_mul(&s2, &b->y, &t);

  gfp2 h;
  gfp2_new(&h);
  gfp2_sub(&h, &u2, &u1);
  int xEqual = gfp2_is_zero(&h);

  gfp2_add(&t, &h, &h);
  gfp2 i;
  gfp2_new(&i);
  gfp2_square(&i, &t);
  gfp2 j;
  gfp2_new(&i);
  gfp2_mul(&i, &h, &i);

  gfp2_sub(&t, &s2, &s1);
  int yEqual = gfp2_is_zero(&t);
  if (xEqual && yEqual) {
    twist_point_double(c, a);
    return;
  }
  gfp2 r;
  gfp2_new(&r);
  gfp2_add(&r, &t, &t);

  gfp2 v;
  gfp2_new(&v);
  gfp2_mul(&v, &u1, &i);

  gfp2 t4;
  gfp2_new(&t4);
  gfp2_square(&t4, &r);
  gfp2_add(&t, &v, &v);
  gfp2 t6;
  gfp2_new(&t6);
  gfp2_sub(&t6, &t4, &j);
  gfp2_sub(&c->x, &t6, &t);

  gfp2_sub(&t, &v, &c->x);  // t7
  gfp2_mul(&t4, &s1, &j);   // t8
  gfp2_add(&t6, &t4, &t4);  // t9
  gfp2_mul(&t4, &r, &t);    // t10
  gfp2_sub(&c->y, &t4, &t6);

  gfp2_add(&t, &a->z, &b->z); // t11
  gfp2_square(&t4, &t);       // t12
  gfp2_sub(&t, &t4, &z1z1);   // t13
  gfp2_sub(&t4, &t, &z2z2);   // t14
  gfp2_mul(&c->z, &t4, &h);

  gfp2_clear(&z1z1);
  gfp2_clear(&z2z2);
  gfp2_clear(&u1);
  gfp2_clear(&u2);
  gfp2_clear(&t);
  gfp2_clear(&s1);
  gfp2_clear(&s2);
  gfp2_clear(&h);
  gfp2_clear(&i);
  gfp2_clear(&j);
  gfp2_clear(&r);
  gfp2_clear(&v);
  gfp2_clear(&t4);
  gfp2_clear(&t6);
}

void twist_point_double(twist_point* c, twist_point* a) {
  // See http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-0/doubling/dbl-2009-l.op3
  gfp2 A;
  gfp2_new(&A);
  gfp2_square(&A, &a->x);
  gfp2 B;
  gfp2_new(&B);
  gfp2_square(&B, &a->y);
  gfp2 C_;
  gfp2_new(&C_);
  gfp2_square(&C_, &B);

  gfp2 t;
  gfp2_new(&t);
  gfp2_add(&t, &a->x, &B);
  gfp2 t2;
  gfp2_new(&t2);
  gfp2_square(&t2, &t);
  gfp2_sub(&t, &t2, &A);
  gfp2_sub(&t2, &t, &C_);
  gfp2 d;
  gfp2_new(&d);
  gfp2_add(&d, &t2, &t2);
  gfp2_add(&t, &A, &A);
  gfp2 e;
  gfp2_new(&e);
  gfp2_add(&e, &t, &A);
  gfp2 f;
  gfp2_new(&f);
  gfp2_square(&f, &e);

  gfp2_add(&t, &d, &d);
  gfp2_sub(&c->x, &f, &t);

  gfp2_add(&t, &C_, &C_);
  gfp2_add(&t2, &t, &t);
  gfp2_add(&t, &t2, &t2);
  gfp2_sub(&c->y, &d, &c->x);
  gfp2_mul(&t2, &e, &c->y);
  gfp2_sub(&c->y, &t2, &t);

  gfp2_mul(&t, &a->y, &a->z);
  gfp2_add(&c->z, &t, &t);

  gfp2_clear(&A);
  gfp2_clear(&B);
  gfp2_clear(&C_);
  gfp2_clear(&t);
  gfp2_clear(&t2);
  gfp2_clear(&d);
  gfp2_clear(&e);
  gfp2_clear(&f);
}

void twist_point_mul(twist_point* c, twist_point* a, mpz_t scalar) {
  twist_point sum;
  twist_point_new(&sum);
  twist_point_set_infinity(&sum);
  twist_point t;
  twist_point_new(&t);

  for (int i = mpz_sizeinbase(scalar, 2); i >= 0; i--) {
    twist_point_double(&t, &sum);
    if (mpz_tstbit(scalar, i) != 0) {
      twist_point_add(&sum, &t, a);
    } else {
      twist_point_set(&sum, &t);
    }
  }

  twist_point_set(c, &sum);
  twist_point_clear(&sum);
  twist_point_clear(&t);
}

// MakeAffine converts c to affine form and returns c. If c is ∞, then it sets
// c to 0 : 1 : 0.
void twist_point_make_affine(twist_point* c) {
  if (gfp2_is_one(&c->z)) {
    return;
  }
  if (twist_point_is_infinity(c)) {
    gfp2_set_zero(&c->x);
    gfp2_set_one(&c->y);
    gfp2_set_zero(&c->z);
    gfp2_set_zero(&c->t);
    return;
  }
  gfp2 zInv;
  gfp2_new(&zInv);
  gfp2_invert(&zInv, &c->z);
  gfp2 t;
  gfp2_new(&t);
  gfp2_mul(&t, &c->y, &zInv);
  gfp2 zInv2;
  gfp2_new(&zInv2);
  gfp2_square(&zInv2, &zInv);
  gfp2_mul(&c->y, &t, &zInv2);
  gfp2_mul(&t, &c->x, &zInv2);
  gfp2_set(&c->x, &t);
  gfp2_set_one(&c->z);
  gfp2_set_one(&c->t);

  gfp2_clear(&zInv);
  gfp2_clear(&t);
  gfp2_clear(&zInv2);
}

void twist_point_negative(twist_point* c, twist_point* a) {
  gfp2_set(&c->x, &a->x);
  gfp2_set_zero(&c->y);
  gfp2_sub(&c->y, &c->y, &a->y);
  gfp2_set(&c->z, &a->z);
  gfp2_set_zero(&c->t);
}
