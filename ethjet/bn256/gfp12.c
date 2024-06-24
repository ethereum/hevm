// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// For details of the algorithms used, see "Multiplication and Squaring on
// Pairing-Friendly Fields, Devegili et al.
// http://eprint.iacr.org/2006/471.pdf.

#include "gfp6.h"
#include "gfp12.h"
#include <stdio.h>

void gfp12_new(gfp12* e) {
  gfp6_new(&e->x);
  gfp6_new(&e->y);
}

void gfp12_clear(gfp12* e) {
  gfp6_clear(&e->x);
  gfp6_clear(&e->y);
}

void gfp12_set(gfp12* e, gfp12* a) {
  gfp6_set(&e->x, &a->x);
  gfp6_set(&e->y, &a->y);
}

void gfp12_set_zero(gfp12* e) {
  gfp6_set_zero(&e->x);
  gfp6_set_zero(&e->y);
}

void gfp12_set_one(gfp12* e) {
  gfp6_set_zero(&e->x);
  gfp6_set_one(&e->y);
}

void gfp12_minimal(gfp12* e) {
  gfp6_minimal(&e->x);
  gfp6_minimal(&e->y);
}

int gfp12_is_zero(gfp12* e) {
  gfp12_minimal(e);
  return gfp6_is_zero(&e->x) && gfp6_is_zero(&e->y);
}

int gfp12_is_one(gfp12* e) {
  gfp12_minimal(e);
  return gfp6_is_zero(&e->x) && gfp6_is_one(&e->y);
}

void gfp12_conjugate(gfp12* e, gfp12* a) {
  gfp6_negative(&e->x, &a->x);
  gfp6_set(&e->y, &a->y);
}

void gfp12_negative(gfp12* e, gfp12* a) {
  gfp6_negative(&e->x, &a->x);
  gfp6_negative(&e->y, &a->y);
}

// Frobenius computes (xω+y)^p = x^p ω·ξ^((p-1)/6) + y^p
void gfp12_frobenius(gfp12* e, gfp12* a) {
  gfp6_frobenius(&e->x, &a->x);
  gfp6_frobenius(&e->y, &a->y);
  gfp6_mul_scalar(&e->x, &e->x, &xiToPMinus1Over6);
}

// FrobeniusP2 computes (xω+y)^p² = x^p² ω·ξ^((p²-1)/6) + y^p²
void gfp12_frobenius_p2(gfp12* e, gfp12* a) {
  gfp6_frobenius_p2(&e->x, &a->x);
  gfp6_mul_gfp(&e->x, &e->x, xiToPSquaredMinus1Over6);
  gfp6_frobenius_p2(&e->y, &a->y);
}

void gfp12_add(gfp12* e, gfp12* a, gfp12* b) {
  gfp6_add(&e->x, &a->x, &b->x);
  gfp6_add(&e->y, &a->y, &b->y);
}

void gfp12_sub(gfp12* e, gfp12* a, gfp12* b) {
  gfp6_sub(&e->x, &a->x, &b->x);
  gfp6_sub(&e->y, &a->y, &b->y);
}

void gfp12_mul(gfp12* e, gfp12* a, gfp12* b) {
  gfp6 tx;
  gfp6_new(&tx);
  gfp6_mul(&tx, &a->x, &b->y);
  gfp6 t;
  gfp6_new(&t);
  gfp6_mul(&t, &b->x, &a->y);
  gfp6_add(&tx, &tx, &t);

  gfp6 ty;
  gfp6_new(&ty);
  gfp6_mul(&ty, &a->y, &b->y);
  gfp6_mul(&t, &a->x, &b->x);
  gfp6_mul_tau(&t, &t);
  gfp6_add(&e->y, &ty, &t);
  gfp6_set(&e->x, &tx);

  gfp6_clear(&tx);
  gfp6_clear(&t);
  gfp6_clear(&ty);
}

void gfp12_mul_scalar(gfp12* e, gfp12* a, gfp6* b) {
  gfp6_mul(&e->x, &e->x, b);
  gfp6_mul(&e->y, &e->y, b);
}

void gfp12_exp(gfp12* c, gfp12* a, mpz_t power) {
  gfp12 sum;
  gfp12_new(&sum);
  gfp12_set_one(&sum);
  gfp12 t;
  gfp12_new(&t);

  for (int i = mpz_sizeinbase(power, 2) - 1; i >= 0; i--) {
    gfp12_square(&t, &sum);
    if (mpz_tstbit(power, i) != 0) {
      gfp12_mul(&sum, &t, a);
    } else {
      gfp12_set(&sum, &t);
    }
  }

  gfp12_set(c, &sum);

  gfp12_clear(&sum);
  gfp12_clear(&t);
}

void gfp12_square(gfp12* e, gfp12* a) {
  // Complex squaring algorithm
  gfp6 v0;
  gfp6_new(&v0);
  gfp6_mul(&v0, &a->x, &a->y);

  gfp6 t;
  gfp6_new(&t);
  gfp6_mul_tau(&t, &a->x);
  gfp6_add(&t, &a->y, &t);
  gfp6 ty;
  gfp6_new(&ty);
  gfp6_add(&ty, &a->x, &a->y);
  gfp6_mul(&ty, &ty, &t);
  gfp6_sub(&ty, &ty, &v0);
  gfp6_mul_tau(&t, &v0);
  gfp6_sub(&ty, &ty, &t);

  gfp6_set(&e->y, &ty);
  gfp6_double(&e->x, &v0);

  gfp6_clear(&v0);
  gfp6_clear(&t);
  gfp6_clear(&ty);
}

void gfp12_invert(gfp12* e, gfp12* a) {
  // See "Implementing cryptographic pairings", M. Scott, section 3.2.
  // ftp://136.206.11.249/pub/crypto/pairings.pdf
  gfp6 t1;
  gfp6_new(&t1);
  gfp6 t2;
  gfp6_new(&t2);

  gfp6_square(&t1, &a->x);
  gfp6_square(&t2, &a->y);
  gfp6_mul_tau(&t1, &t1);
  gfp6_sub(&t1, &t2, &t1);
  gfp6_invert(&t2, &t1);

  gfp6_negative(&e->x, &a->x);
  gfp6_set(&e->y, &a->y);
  gfp12_mul_scalar(e, e, &t2);

  gfp6_clear(&t1);
  gfp6_clear(&t2);
}
