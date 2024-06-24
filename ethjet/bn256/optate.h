// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#ifndef BN256_OPTATE_H
#define BN256_OPTATE_H

#include "gfp2.h"
#include "gfp6.h"
#include "gfp12.h"
#include "curve.h"
#include "twist.h"
#include "constants.h"

// a, b, c, rOut - returned values
void optate_line_function_add(twist_point* r, twist_point* p, curve_point* q, gfp2* r2, gfp2* a, gfp2* b, gfp2* c, twist_point* rOut);

// a, b, c, rOut - returned values
void optate_line_function_double(twist_point* r, curve_point* q, gfp2* a, gfp2* b, gfp2* c, twist_point* rOut);

void optate_mul_line(gfp12* ret, gfp2* a, gfp2* b, gfp2* c);

// miller implements the Miller loop for calculating the Optimal Ate pairing.
// See algorithm 1 from http://cryptojedi.org/papers/dclxvi-20100714.pdf
void optate_miller(twist_point* q, curve_point* p, gfp12* ret);

// finalExponentiation computes the (p¹²-1)/Order-th power of an element of
// GF(p¹²) to obtain an element of GT (steps 13-15 of algorithm 1 from
// http://cryptojedi.org/papers/dclxvi-20100714.pdf)
void optate_final_exponentiation(gfp12* in, gfp12* t0);

void optate_optimal_ate(twist_point* a, curve_point* b, gfp12* ret);

#endif
