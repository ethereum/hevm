// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// For details of the algorithms used, see "Multiplication and Squaring on
// Pairing-Friendly Fields, Devegili et al.
// http://eprint.iacr.org/2006/471.pdf.

#ifndef BN256_GFP6_H
#define BN256_GFP6_H

#include <gmp.h>
#include "gfp2.h"
#include "constants.h"

// gfP6 implements the field of size p⁶ as a cubic extension of gfP2 where τ³=ξ
// and ξ=i+9.
typedef struct gfp6 {
  gfp2 x, y, z; // value is xτ² + yτ + z
} gfp6;

void gfp6_new(gfp6* e);

void gfp6_clear(gfp6* e);

void gfp6_set(gfp6* e, gfp6* a);

void gfp6_set_zero(gfp6* e);

void gfp6_set_one(gfp6* e);

void gfp6_minimal(gfp6* e);

int gfp6_is_zero(gfp6* e);

int gfp6_is_one(gfp6* e);

void gfp6_negative(gfp6* e, gfp6* a);

void gfp6_frobenius(gfp6* e, gfp6* a);

// FrobeniusP2 computes (xτ²+yτ+z)^(p²) = xτ^(2p²) + yτ^(p²) + z
void gfp6_frobenius_p2(gfp6* e, gfp6* a);

void gfp6_add(gfp6* e, gfp6* a, gfp6* b);

void gfp6_sub(gfp6* e, gfp6* a, gfp6* b);

void gfp6_double(gfp6* e, gfp6* a);

void gfp6_mul(gfp6* e, gfp6* a, gfp6* b);

void gfp6_mul_scalar(gfp6* e, gfp6* a, gfp2* b);

void gfp6_mul_gfp(gfp6* e, gfp6* a, mpz_t b);

// MulTau computes τ·(aτ²+bτ+c) = bτ²+cτ+aξ
void gfp6_mul_tau(gfp6* e, gfp6* a);

void gfp6_square(gfp6* e, gfp6* a);

void gfp6_invert(gfp6* e, gfp6* a);

#endif
