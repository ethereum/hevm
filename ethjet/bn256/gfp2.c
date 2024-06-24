// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// For details of the algorithms used, see "Multiplication and Squaring on
// Pairing-Friendly Fields, Devegili et al.
// http://eprint.iacr.org/2006/471.pdf.

#include "constants.h"
#include "gfp2.h"
#include <gmp.h>

void gfp2_new(gfp2* p) {
  mpz_init(p->x);
  mpz_init(p->y);
}

void gfp2_clear(gfp2* p) {
  mpz_clear(p->x);
  mpz_clear(p->y);
}

void gfp2_set(gfp2* a, gfp2* b) {
  mpz_set(a->x, b->x);
  mpz_set(a->y, b->y);
}

void gfp2_set_zero(gfp2* p) {
  mpz_set_ui(p->x, 0);
  mpz_set_ui(p->y, 0);
}

void gfp2_set_one(gfp2* p) {
  mpz_set_ui(p->x, 0);
  mpz_set_ui(p->y, 1);
}

void gfp2_minimal(gfp2* e) {
  if (mpz_sgn(e->x) < 0 || mpz_cmp(e->x, P) >= 0) {
    mpz_mod(e->x, e->x, P);
  }
  if (mpz_sgn(e->y) < 0 || mpz_cmp(e->y, P) >= 0) {
    mpz_mod(e->y, e->y, P);
  }
}

int gfp2_is_zero(gfp2* e) {
  return mpz_sgn(e->x) == 0 && mpz_sgn(e->y) == 0;
}

int gfp2_is_one(gfp2* e) {
  if (mpz_sgn(e->x) != 0) {
    return 0;
  }
  // TODO: is this the same?
  //words := e.y.Bits()
  //return len(words) == 1 && words[0] == 1
  return mpz_cmp_ui(e->y, 1);
}

void gfp2_conjugate(gfp2* e, gfp2* a) {
  mpz_set(e->y, a->y);
  mpz_set(e->x, a->x);
}

void gfp2_negative(gfp2* e, gfp2* a) {
  mpz_neg(e->x, a->x);
  mpz_neg(e->y, a->y);
}

void gfp2_add(gfp2* e, gfp2* a, gfp2* b) {
  mpz_add(e->x, a->x, b->x);
  mpz_add(e->y, a->y, b->y);
}

void gfp2_sub(gfp2* e, gfp2* a, gfp2* b) {
  mpz_sub(e->x, a->x, b->x);
  mpz_sub(e->y, a->y, b->y);
}

void gfp2_double(gfp2* e, gfp2* a) {
  mpz_mul_2exp(e->x, a->x, 1);
  mpz_mul_2exp(e->y, a->y, 1);
}

void gfp2_exp(gfp2* c, gfp2* a, mpz_t power) {
  gfp2 sum;
  gfp2_new(&sum);
  gfp2_set_one(&sum);
  gfp2 t;
  gfp2_new(&t);

  for (int i = mpz_sizeinbase(power, 2) - 1; i >= 0; i--) {
    gfp2_square(&t, &sum);
    if (mpz_tstbit(power, i) != 0) {
      gfp2_mul(&sum, &t, a);
    } else {
      gfp2_set(&sum, &t);
    }
  }

  gfp2_set(c, &sum);

  gfp2_clear(&sum);
  gfp2_clear(&t);
}

// See "Multiplication and Squaring in Pairing-Friendly Fields",
// http://eprint.iacr.org/2006/471.pdf
void gfp2_mul(gfp2* e, gfp2* a, gfp2* b) {
  mpz_t tx;
  mpz_init(tx);
  mpz_mul(tx, a->x, b->y);
  mpz_t t;
  mpz_init(t);
  mpz_mul(t, b->x, a->y);
  mpz_add(tx, tx, t);
  mpz_mod(tx, tx, P);

  mpz_t ty;
  mpz_init(ty);
  mpz_mul(ty, a->y, b->y);
  mpz_mul(t, a->x, b->x);
  mpz_sub(ty, ty, t);
  mpz_mod(e->y, ty, P);
  mpz_set(e->x, tx);

  mpz_clear(tx);
  mpz_clear(t);
  mpz_clear(ty);
}

void gfp2_mul_scalar(gfp2* e, gfp2* a, mpz_t b) {
  mpz_mul(e->x, a->x, b);
  mpz_mul(e->y, a->y, b);
}

// MulXi sets e=ξa where ξ=i+9 and then returns e.
void gfp2_mul_xi(gfp2* e, gfp2* a) {
  // (xi+y)(i+3) = (9x+y)i+(9y-x)
  mpz_t tx;
  mpz_init(tx);
  mpz_mul_2exp(tx, a->x, 3);
  mpz_add(tx, tx, a->x);
  mpz_add(tx, tx, a->y);

  mpz_t ty;
  mpz_init(ty);
  mpz_mul_2exp(ty, a->y, 3);
  mpz_add(ty, ty, a->y);
  mpz_sub(ty, ty, a->x);

  mpz_set(e->x, tx);
  mpz_set(e->y, ty);

  mpz_clear(tx);
  mpz_clear(ty);
}

void gfp2_square(gfp2* e, gfp2* a) {
  // Complex squaring algorithm:
  // (xi+b)² = (x+y)(y-x) + 2*i*x*y
  mpz_t t1;
  mpz_init(t1);
  mpz_sub(t1, a->y, a->x);
  mpz_t t2;
  mpz_init(t2);
  mpz_add(t2, a->x, a->y);
  mpz_t ty;
  mpz_init(ty);
  mpz_mul(ty, t1, t2);
  mpz_mod(ty, ty, P);

  mpz_mul(t1, a->x, a->y);
  mpz_mul_2exp(t1, t1, 1);

  mpz_mod(e->x, t1, P);
  mpz_set(e->y, ty);

  mpz_clear(t1);
  mpz_clear(t2);
  mpz_clear(ty);
}

void gfp2_invert(gfp2* e, gfp2* a) {
  // See "Implementing cryptographic pairings", M. Scott, section 3.2.
  // ftp://136.206.11.249/pub/crypto/pairings.pdf
  mpz_t t;
  mpz_init(t);
  mpz_mul(t, a->y, a->y);
  mpz_t t2;
  mpz_init(t2);
  mpz_mul(t2, a->x, a->x);
  mpz_mul(t, t, t2);

  mpz_t inv;
  mpz_init(inv);
  mpz_invert(inv, t, P);

  mpz_neg(e->x, a->x);
  mpz_mul(e->x, e->x, inv);
  mpz_mod(e->x, e->x, P);

  mpz_mul(e->y, a->y, inv);
  mpz_mod(e->y, e->y, P);

  mpz_clear(t);
  mpz_clear(t2);
  mpz_clear(inv);
}

void gfp2_real(mpz_t r, gfp2* e) {
  mpz_set(r, e->x);
}

void gfp2_imag(mpz_t i, gfp2* e) {
  mpz_set(i, e->y);
}
