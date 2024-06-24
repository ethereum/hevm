// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// For details of the algorithms used, see "Multiplication and Squaring on
// Pairing-Friendly Fields, Devegili et al.
// http://eprint.iacr.org/2006/471.pdf.

#ifndef BN256_GFP2_H
#define BN256_GFP2_H

#include <gmp.h>

// gfP2 implements a field of size p² as a quadratic extension of the base
// field where i²=-1.
typedef struct gfp2 {
  mpz_t x, y; // value is xi+y.
} gfp2;

void gfp2_new(gfp2* p);

void gfp2_clear(gfp2* p);

void gfp2_set(gfp2* a, gfp2* b);

void gfp2_set_zero(gfp2* p);

void gfp2_set_one(gfp2* p);

void gfp2_minimal(gfp2* e);

int gfp2_is_zero(gfp2* e);

int gfp2_is_one(gfp2* e);

void gfp2_conjugate(gfp2* e, gfp2* a);

void gfp2_negative(gfp2* e, gfp2* a);

void gfp2_add(gfp2* e, gfp2* a, gfp2* b);

void gfp2_sub(gfp2* e, gfp2* a, gfp2* b);

void gfp2_double(gfp2* e, gfp2* a);

void gfp2_exp(gfp2* c, gfp2* a, mpz_t power);

// See "Multiplication and Squaring in Pairing-Friendly Fields",
// http://eprint.iacr.org/2006/471.pdf
void gfp2_mul(gfp2* e, gfp2* a, gfp2* b);

void gfp2_mul_scalar(gfp2* e, gfp2* a, mpz_t b);

// MulXi sets e=ξa where ξ=i+9 and then returns e.
void gfp2_mul_xi(gfp2* e, gfp2* a);

void gfp2_square(gfp2* e, gfp2* a);

void gfp2_invert(gfp2* e, gfp2* a);

void gfp2_real(mpz_t r, gfp2* e);

void gfp2_imag(mpz_t i, gfp2* e);

#endif
