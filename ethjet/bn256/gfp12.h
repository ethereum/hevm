// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// For details of the algorithms used, see "Multiplication and Squaring on
// Pairing-Friendly Fields, Devegili et al.
// http://eprint.iacr.org/2006/471.pdf.

#ifndef BN256_GFP12_H
#define BN256_GFP12_H

#include "gfp6.h"
#include <stdio.h>

// gfP12 implements the field of size p¹² as a quadratic extension of gfP6
// where ω²=τ.
typedef struct gfp12 {
  gfp6 x, y; // value is xω + y
} gfp12;

void gfp12_new(gfp12* e);

void gfp12_clear(gfp12* e);

void gfp12_set(gfp12* e, gfp12* a);

void gfp12_set_zero(gfp12* e);

void gfp12_set_one(gfp12* e);

void gfp12_minimal(gfp12* e);

int gfp12_is_zero(gfp12* e);

int gfp12_is_one(gfp12* e);

void gfp12_conjugate(gfp12* e, gfp12* a);

void gfp12_negative(gfp12* e, gfp12* a);

// Frobenius computes (xω+y)^p = x^p ω·ξ^((p-1)/6) + y^p
void gfp12_frobenius(gfp12* e, gfp12* a);

// FrobeniusP2 computes (xω+y)^p² = x^p² ω·ξ^((p²-1)/6) + y^p²
void gfp12_frobenius_p2(gfp12* e, gfp12* a);

void gfp12_add(gfp12* e, gfp12* a, gfp12* b);

void gfp12_sub(gfp12* e, gfp12* a, gfp12* b);

void gfp12_mul(gfp12* e, gfp12* a, gfp12* b);

void gfp12_mul_scalar(gfp12* e, gfp12* a, gfp6* b);

void gfp12_exp(gfp12* c, gfp12* a, mpz_t power);

void gfp12_square(gfp12* e, gfp12* a);

void gfp12_invert(gfp12* e, gfp12* a);

#endif
