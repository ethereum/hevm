// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// For details of the algorithms used, see "Multiplication and Squaring on
// Pairing-Friendly Fields, Devegili et al.
// http://eprint.iacr.org/2006/471.pdf.

#include <gmp.h>
#include "gfp2.h"
#include "gfp6.h"
#include "constants.h"

void gfp6_new(gfp6* e) {
  gfp2_new(&e->x);
  gfp2_new(&e->y);
  gfp2_new(&e->z);
}

void gfp6_clear(gfp6* e) {
  gfp2_clear(&e->x);
  gfp2_clear(&e->y);
  gfp2_clear(&e->z);
}

void gfp6_set(gfp6* e, gfp6* a) {
  gfp2_set(&e->x, &a->x);
  gfp2_set(&e->y, &a->y);
  gfp2_set(&e->z, &a->z);
}

void gfp6_set_zero(gfp6* e) {
  gfp2_set_zero(&e->x);
  gfp2_set_zero(&e->y);
  gfp2_set_zero(&e->z);
}

void gfp6_set_one(gfp6* e) {
  gfp2_set_zero(&e->x);
  gfp2_set_zero(&e->y);
  gfp2_set_one(&e->z);
}

void gfp6_minimal(gfp6* e) {
  gfp2_minimal(&e->x);
  gfp2_minimal(&e->y);
  gfp2_minimal(&e->z);
}

int gfp6_is_zero(gfp6* e) {
  return gfp2_is_zero(&e->x) && gfp2_is_zero(&e->y) && gfp2_is_zero(&e->z);
}

int gfp6_is_one(gfp6* e) {
  return gfp2_is_zero(&e->x) && gfp2_is_zero(&e->y) && gfp2_is_one(&e->z);
}

void gfp6_negative(gfp6* e, gfp6* a) {
  gfp2_negative(&e->x, &a->x);
  gfp2_negative(&e->y, &a->y);
  gfp2_negative(&e->z, &a->z);
}

void gfp6_frobenius(gfp6* e, gfp6* a) {
  gfp2_conjugate(&e->x, &a->x);
  gfp2_conjugate(&e->y, &a->y);
  gfp2_conjugate(&e->z, &a->z);

  gfp2_mul(&e->x, &e->x, &xiTo2PMinus2Over3);
  gfp2_mul(&e->y, &e->y, &xiToPMinus1Over3);
}

// FrobeniusP2 computes (xτ²+yτ+z)^(p²) = xτ^(2p²) + yτ^(p²) + z
void gfp6_frobenius_p2(gfp6* e, gfp6* a) {
  // τ^(2p²) = τ²τ^(2p²-2) = τ²ξ^((2p²-2)/3)
  gfp2_mul_scalar(&e->x, &a->x, xiTo2PSquaredMinus2Over3);
  // τ^(p²) = ττ^(p²-1) = τξ^((p²-1)/3)
  gfp2_mul_scalar(&e->y, &a->y, xiToPSquaredMinus1Over3);
  gfp2_set(&e->z, &a->z);
}

void gfp6_add(gfp6* e, gfp6* a, gfp6* b) {
  gfp2_add(&e->x, &a->x, &b->x);
  gfp2_add(&e->y, &a->y, &b->y);
  gfp2_add(&e->z, &a->z, &b->z);
}

void gfp6_sub(gfp6* e, gfp6* a, gfp6* b) {
  gfp2_sub(&e->x, &a->x, &b->x);
  gfp2_sub(&e->y, &a->y, &b->y);
  gfp2_sub(&e->z, &a->z, &b->z);
}

void gfp6_double(gfp6* e, gfp6* a) {
  gfp2_double(&e->x, &a->x);
  gfp2_double(&e->y, &a->y);
  gfp2_double(&e->z, &a->z);
}

void gfp6_mul(gfp6* e, gfp6* a, gfp6* b) {
  // "Multiplication and Squaring on Pairing-Friendly Fields"
  // Section 4, Karatsuba method.
  // http://eprint.iacr.org/2006/471.pdf

  gfp2 v0;
  gfp2_new(&v0);
  gfp2_mul(&v0, &a->z, &b->z);
  gfp2 v1;
  gfp2_new(&v1);
  gfp2_mul(&v1, &a->y, &b->y);
  gfp2 v2;
  gfp2_new(&v2);
  gfp2_mul(&v2, &a->x, &b->x);

  gfp2 t0;
  gfp2_new(&t0);
  gfp2_add(&t0, &a->x, &a->y);
  gfp2 t1;
  gfp2_new(&t1);
  gfp2_add(&t1, &b->x, &b->y);
  gfp2 tz;
  gfp2_new(&tz);
  gfp2_mul(&tz, &t0, &t1);

  gfp2_sub(&tz, &tz, &v1);
  gfp2_sub(&tz, &tz, &v2);
  gfp2_mul_xi(&tz, &tz);
  gfp2_add(&tz, &tz, &v0);

  gfp2_add(&t0, &a->y, &a->z);
  gfp2_add(&t1, &b->y, &b->z);
  gfp2 ty;
  gfp2_new(&ty);
  gfp2_mul(&ty, &t0, &t1);
  gfp2_sub(&ty, &ty, &v0);
  gfp2_sub(&ty, &ty, &v1);
  gfp2_mul_xi(&t0, &v2);
  gfp2_add(&ty, &ty, &t0);

  gfp2_add(&t0, &a->x, &a->z);
  gfp2_add(&t1, &b->x, &b->z);
  gfp2 tx;
  gfp2_new(&tx);
  gfp2_mul(&tx, &t0, &t1);
  gfp2_sub(&tx, &tx, &v0);
  gfp2_add(&tx, &tx, &v1);
  gfp2_sub(&tx, &tx, &v2);

  gfp2_set(&e->x, &tx);
  gfp2_set(&e->y, &ty);
  gfp2_set(&e->z, &tz);

  gfp2_clear(&v0);
  gfp2_clear(&v1);
  gfp2_clear(&v2);
  gfp2_clear(&t0);
  gfp2_clear(&t1);
  gfp2_clear(&tz);
  gfp2_clear(&ty);
  gfp2_clear(&tx);
}

void gfp6_mul_scalar(gfp6* e, gfp6* a, gfp2* b) {
  gfp2_mul(&e->x, &a->x, b);
  gfp2_mul(&e->y, &a->y, b);
  gfp2_mul(&e->z, &a->z, b);
}

void gfp6_mul_gfp(gfp6* e, gfp6* a, mpz_t b) {
  gfp2_mul_scalar(&e->x, &a->x, b);
  gfp2_mul_scalar(&e->y, &a->y, b);
  gfp2_mul_scalar(&e->z, &a->z, b);
}

// MulTau computes τ·(aτ²+bτ+c) = bτ²+cτ+aξ
void gfp6_mul_tau(gfp6* e, gfp6* a) {
  gfp2 tz;
  gfp2_new(&tz);
  gfp2_mul_xi(&tz, &a->x);
  gfp2 ty;
  gfp2_new(&ty);
  gfp2_set(&ty, &a->y);
  gfp2_set(&e->y, &a->z);
  gfp2_set(&e->x, &ty);
  gfp2_set(&e->z, &tz);

  gfp2_clear(&tz);
  gfp2_clear(&ty);
}

void gfp6_square(gfp6* e, gfp6* a) {
  gfp2 v0;
  gfp2_new(&v0);
  gfp2_square(&v0, &a->z);
  gfp2 v1;
  gfp2_new(&v1);
  gfp2_square(&v1, &a->y);
  gfp2 v2;
  gfp2_new(&v2);
  gfp2_square(&v2, &a->x);

  gfp2 c0;
  gfp2_new(&c0);
  gfp2_add(&c0, &a->x, &a->y);
  gfp2_square(&c0, &c0);
  gfp2_sub(&c0, &c0, &v1);
  gfp2_sub(&c0, &c0, &v2);
  gfp2_mul_xi(&c0, &c0);
  gfp2_add(&c0, &c0, &v0);

  gfp2 c1;
  gfp2_new(&c1);
  gfp2_add(&c1, &a->y, &a->z);
  gfp2_square(&c1, &c1);
  gfp2_sub(&c1, &c1, &v0);
  gfp2_sub(&c1, &c1, &v1);
  gfp2 xiV2;
  gfp2_new(&xiV2);
  gfp2_mul_xi(&xiV2, &v2);
  gfp2_add(&c1, &c1, &xiV2);

  gfp2 c2;
  gfp2_new(&c2);
  gfp2_add(&c2, &a->x, &a->z);
  gfp2_square(&c2, &c2);
  gfp2_sub(&c2, &c2, &v0);
  gfp2_add(&c2, &c2, &v1);
  gfp2_sub(&c2, &c2, &v2);

  gfp2_set(&e->x, &c2);
  gfp2_set(&e->y, &c1);
  gfp2_set(&e->z, &c0);

  gfp2_clear(&v0);
  gfp2_clear(&v1);
  gfp2_clear(&v2);
  gfp2_clear(&c0);
  gfp2_clear(&c1);
  gfp2_clear(&xiV2);
  gfp2_clear(&c2);
}

void gfp6_invert(gfp6* e, gfp6* a) {
  // See "Implementing cryptographic pairings", M. Scott, section 3.2.
  // ftp://136.206.11.249/pub/crypto/pairings.pdf

  // Here we can give a short explanation of how it works: let j be a cubic root of
  // unity in GF(p²) so that 1+j+j²=0.
  // Then (xτ² + yτ + z)(xj²τ² + yjτ + z)(xjτ² + yj²τ + z)
  // = (xτ² + yτ + z)(Cτ²+Bτ+A)
  // = (x³ξ²+y³ξ+z³-3ξxyz) = F is an element of the base field (the norm).
  //
  // On the other hand (xj²τ² + yjτ + z)(xjτ² + yj²τ + z)
  // = τ²(y²-ξxz) + τ(ξx²-yz) + (z²-ξxy)
  //
  // So that's why A = (z²-ξxy), B = (ξx²-yz), C = (y²-ξxz)
  gfp2 t1;
  gfp2_new(&t1);

  gfp2 A;
  gfp2_new(&A);
  gfp2_square(&A, &a->z);
  gfp2_mul(&t1, &a->x, &a->y);
  gfp2_mul_xi(&t1, &t1);
  gfp2_sub(&A, &A, &t1);

  gfp2 B;
  gfp2_new(&B);
  gfp2_square(&B, &a->x);
  gfp2_mul_xi(&B, &B);
  gfp2_mul(&t1, &a->y, &a->z);
  gfp2_sub(&B, &B, &t1);

  gfp2 C_;
  gfp2_new(&C_);
  gfp2_square(&C_, &a->y);
  gfp2_mul(&t1, &a->x, &a->z);
  gfp2_sub(&C_, &C_, &t1);

  gfp2 F;
  gfp2_new(&F);
  gfp2_mul(&F, &C_, &a->y);
  gfp2_mul_xi(&F, &F);
  gfp2_mul(&t1, &A, &a->z);
  gfp2_add(&F, &F, &t1);
  gfp2_mul(&t1, &B, &a->x);
  gfp2_mul_xi(&t1, &t1);
  gfp2_add(&F, &F, &t1);

  gfp2_invert(&F, &F);

  gfp2_mul(&e->x, &C_, &F);
  gfp2_mul(&e->y, &B, &F);
  gfp2_mul(&e->z, &A, &F);

  gfp2_clear(&t1);
  gfp2_clear(&A);
  gfp2_clear(&B);
  gfp2_clear(&C_);
  gfp2_clear(&F);
}
