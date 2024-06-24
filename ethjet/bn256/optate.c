// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#include "gfp2.h"
#include "gfp6.h"
#include "gfp12.h"
#include "curve.h"
#include "twist.h"
#include "constants.h"

// a, b, c, rOut - returned values
void optate_line_function_add(twist_point* r, twist_point* p, curve_point* q, gfp2* r2, gfp2* a, gfp2* b, gfp2* c, twist_point* rOut) {
// func lineFunctionAdd(r, p *twistPoint, q *curvePoint, r2 *gfP2, pool *bnPool) (a, b, c *gfP2, rOut *twistPoint) {
  // See the mixed addition algorithm from "Faster Computation of the
  // Tate Pairing", http://arxiv.org/pdf/0904.0854v3.pdf

  gfp2 B;
  gfp2_new(&B);
  gfp2_mul(&B, &p->x, &r->t);

  gfp2 D;
  gfp2_new(&D);
  gfp2_add(&D, &p->y, &r->z);
  gfp2_square(&D, &D);
  gfp2_sub(&D, &D, r2);
  gfp2_sub(&D, &D, &r->t);
  gfp2_mul(&D, &D, &r->t);

  gfp2 H;
  gfp2_new(&H);
  gfp2_sub(&H, &B, &r->x);
  gfp2 I;
  gfp2_new(&I);
  gfp2_square(&I, &H);

  gfp2 E;
  gfp2_new(&E);
  gfp2_add(&E, &I, &I);
  gfp2_add(&E, &E, &E);

  gfp2 J;
  gfp2_new(&J);
  gfp2_mul(&J, &H, &E);

  gfp2 L1;
  gfp2_new(&L1);
  gfp2_sub(&L1, &D, &r->y);
  gfp2_sub(&L1, &L1, &r->y);

  gfp2 V;
  gfp2_new(&V);
  gfp2_mul(&V, &r->x, &E);

  gfp2_square(&rOut->x, &L1);
  gfp2_sub(&rOut->x, &rOut->x, &J);
  gfp2_sub(&rOut->x, &rOut->x, &V);
  gfp2_sub(&rOut->x, &rOut->x, &V);

  gfp2_add(&rOut->z, &r->z, &H);
  gfp2_square(&rOut->z, &rOut->z);
  gfp2_sub(&rOut->z, &rOut->z, &r->t);
  gfp2_sub(&rOut->z, &rOut->z, &I);

  gfp2 t;
  gfp2_new(&t);
  gfp2_sub(&t, &V, &rOut->x);
  gfp2_mul(&t, &t, &L1);
  gfp2 t2;
  gfp2_new(&t2);
  gfp2_mul(&t2, &r->y, &J);
  gfp2_add(&t2, &t2, &t2);
  gfp2_sub(&rOut->y, &t, &t2);

  gfp2_square(&rOut->t, &rOut->z);

  gfp2_add(&t, &p->y, &rOut->z);
  gfp2_square(&t, &t);
  gfp2_sub(&t, &t, r2);
  gfp2_sub(&t, &t, &rOut->t);

  gfp2_mul(&t2, &L1, &p->x);
  gfp2_add(&t2, &t2, &t2);
  gfp2_sub(a, &t2, &t);

  gfp2_mul_scalar(c, &rOut->z, q->y);
  gfp2_add(c, c, c);

  gfp2_set_zero(b);
  gfp2_sub(b, b, &L1);
  gfp2_mul_scalar(b, b, q->x);
  gfp2_add(b, b, b);

  gfp2_clear(&B);
  gfp2_clear(&D);
  gfp2_clear(&H);
  gfp2_clear(&I);
  gfp2_clear(&E);
  gfp2_clear(&J);
  gfp2_clear(&L1);
  gfp2_clear(&V);
  gfp2_clear(&t);
  gfp2_clear(&t2);
}

// a, b, c, rOut - returned values
void optate_line_function_double(twist_point* r, curve_point* q, gfp2* a, gfp2* b, gfp2* c, twist_point* rOut) {
  // See the doubling algorithm for a=0 from "Faster Computation of the
  // Tate Pairing", http://arxiv.org/pdf/0904.0854v3.pdf

  gfp2 A;
  gfp2_new(&A);
  gfp2_square(&A, &r->x);
  gfp2 B;
  gfp2_new(&B);
  gfp2_square(&B, &r->y);
  gfp2 C_;
  gfp2_new(&C_);
  gfp2_square(&C_, &B);

  gfp2 D;
  gfp2_new(&D);
  gfp2_add(&D, &r->x, &B);
  gfp2_square(&D, &D);
  gfp2_sub(&D, &D, &A);
  gfp2_sub(&D, &D, &C_);
  gfp2_sub(&D, &D, &D);

  gfp2 E;
  gfp2_new(&E);
  gfp2_add(&E, &A, &A);
  gfp2_add(&E, &E, &A);

  gfp2 G;
  gfp2_new(&G);
  gfp2_square(&G, &E);

  gfp2_sub(&rOut->x, &G, &D);
  gfp2_sub(&rOut->x, &rOut->x, &D);

  gfp2_add(&rOut->z, &r->y, &r->z);
  gfp2_square(&rOut->z, &rOut->z);
  gfp2_sub(&rOut->z, &rOut->z, &B);
  gfp2_sub(&rOut->z, &rOut->z, &r->t);

  gfp2_sub(&rOut->y, &D, &rOut->x);
  gfp2_mul(&rOut->y, &rOut->y, &E);
  gfp2 t;
  gfp2_new(&t);
  gfp2_add(&t, &C_, &C_);
  gfp2_add(&t, &t, &t);
  gfp2_add(&t, &t, &t);
  gfp2_sub(&rOut->y, &rOut->y, &t);

  gfp2_square(&rOut->t, &rOut->z);

  gfp2_mul(&t, &E, &r->t);
  gfp2_add(&t, &t, &t);
  gfp2_set_zero(b);
  gfp2_sub(b, b, &t);
  gfp2_mul_scalar(b, b, q->x);

  gfp2_add(a, &r->x, &E);
  gfp2_square(a, a);
  gfp2_sub(a, a, &A);
  gfp2_sub(a, a, &G);
  gfp2_add(&t, &B, &B);
  gfp2_add(&t, &t, &t);
  gfp2_sub(a, a, &t);

  gfp2_mul(c, &rOut->z, &r->t);
  gfp2_add(c, c, c);
  gfp2_mul_scalar(c, c, q->y);

  gfp2_clear(&A);
  gfp2_clear(&B);
  gfp2_clear(&C_);
  gfp2_clear(&D);
  gfp2_clear(&E);
  gfp2_clear(&G);
  gfp2_clear(&t);
}

void optate_mul_line(gfp12* ret, gfp2* a, gfp2* b, gfp2* c) {
  gfp6 a2;
  gfp6_new(&a2);
  gfp2_set_zero(&a2.x);
  gfp2_set(&a2.y, a);
  gfp2_set(&a2.z, b);
  gfp6_mul(&a2, &a2, &ret->x);
  gfp6 t3;
  gfp6_new(&t3);
  gfp6_mul_scalar(&t3, &ret->y, c);

  gfp2 t;
  gfp2_new(&t);
  gfp2_add(&t, b, c);
  gfp6 t2;
  gfp6_new(&t2);
  gfp2_set_zero(&t2.x);
  gfp2_set(&t2.y, a);
  gfp2_set(&t2.z, &t);
  gfp6_add(&ret->x, &ret->x, &ret->y);

  gfp6_set(&ret->y, &t3);

  gfp6_mul(&ret->x, &ret->x, &t2);
  gfp6_sub(&ret->x, &ret->x, &a2);
  gfp6_sub(&ret->x, &ret->x, &ret->y);
  gfp6_mul_tau(&a2, &a2);
  gfp6_add(&ret->y, &ret->y, &a2);

  gfp6_clear(&a2);
  gfp6_clear(&t3);
  gfp6_clear(&t2);
  gfp2_clear(&t);
}

// sixuPlus2NAF is 6u+2 in non-adjacent form.
char sixuPlus2NAF[] = {
  0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0,
  0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 1,
  1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1,
  1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, 1, 1
};

// miller implements the Miller loop for calculating the Optimal Ate pairing.
// See algorithm 1 from http://cryptojedi.org/papers/dclxvi-20100714.pdf
void optate_miller(twist_point* q, curve_point* p, gfp12* ret) {
  gfp12_set_one(ret);

  twist_point aAffine;
  twist_point_new(&aAffine);
  twist_point_set(&aAffine, q);
  twist_point_make_affine(&aAffine);

  curve_point bAffine;
  curve_point_new(&bAffine);
  curve_point_set(&bAffine, p);
  curve_point_make_affine(&bAffine);

  twist_point minusA;
  twist_point_new(&minusA);
  twist_point_negative(&minusA, &aAffine);

  twist_point r;
  twist_point_new(&r);
  twist_point_set(&r, &aAffine);

  gfp2 r2;
  gfp2_new(&r2);
  gfp2_square(&r2, &aAffine.y);

  gfp2 a, b, c;
  twist_point newR;
  gfp2_new(&a);
  gfp2_new(&b);
  gfp2_new(&c);
  twist_point_new(&newR);

  for (int i = sizeof(sixuPlus2NAF) - 1; i > 0; i--) {
    optate_line_function_double(&r, &bAffine, &a, &b, &c, &newR);
    if (i != sizeof(sixuPlus2NAF)-1) {
      gfp12_square(ret, ret);
    }

    optate_mul_line(ret, &a, &b, &c);
    twist_point_set(&r, &newR); // TODO???

    switch (sixuPlus2NAF[i-1]) {
    case 1:
      optate_line_function_add(&r, &aAffine, &bAffine, &r2, &a, &b, &c, &newR);
      break;
    case -1:
      optate_line_function_add(&r, &minusA, &bAffine, &r2, &a, &b, &c, &newR);
      break;
    default:
      continue;
    }

    optate_mul_line(ret, &a, &b, &c);
    twist_point_set(&r, &newR); // TODO: is this necessary?
  }

  // In order to calculate Q1 we have to convert q from the sextic twist
  // to the full GF(p^12) group, apply the Frobenius there, and convert
  // back.
  //
  // The twist isomorphism is (x', y') -> (xω², yω³). If we consider just
  // x for a moment, then after applying the Frobenius, we have x̄ω^(2p)
  // where x̄ is the conjugate of x. If we are going to apply the inverse
  // isomorphism we need a value with a single coefficient of ω² so we
  // rewrite this as x̄ω^(2p-2)ω². ξ⁶ = ω and, due to the construction of
  // p, 2p-2 is a multiple of six. Therefore we can rewrite as
  // x̄ξ^((p-1)/3)ω² and applying the inverse isomorphism eliminates the
  // ω².
  //
  // A similar argument can be made for the y value.

  twist_point q1;
  twist_point_new(&q1);
  gfp2_conjugate(&q1.x, &aAffine.x);
  gfp2_mul(&q1.x, &q1.x, &xiToPMinus1Over3);
  gfp2_conjugate(&q1.y, &aAffine.y);
  gfp2_mul(&q1.y, &q1.y, &xiToPMinus1Over2);
  gfp2_set_one(&q1.z);
  gfp2_set_one(&q1.t);

  // For Q2 we are applying the p² Frobenius. The two conjugations cancel
  // out and we are left only with the factors from the isomorphism. In
  // the case of x, we end up with a pure number which is why
  // xiToPSquaredMinus1Over3 is ∈ GF(p). With y we get a factor of -1. We
  // ignore this to end up with -Q2.

  twist_point minusQ2;
  twist_point_new(&minusQ2);
  gfp2_mul_scalar(&minusQ2.x, &aAffine.x, xiToPSquaredMinus1Over3);
  gfp2_set(&minusQ2.y, &aAffine.y);
  gfp2_set_one(&minusQ2.z);
  gfp2_set_one(&minusQ2.t);

  gfp2_square(&r2, &q1.y);
  optate_line_function_add(&r, &q1, &bAffine, &r2, &a, &b, &c, &newR);
  optate_mul_line(ret, &a, &b, &c);
  twist_point_set(&r, &newR); // TODO???

  gfp2_square(&r2, &minusQ2.y);
  optate_line_function_add(&r, &minusQ2, &bAffine, &r2, &a, &b, &c, &newR);
  optate_mul_line(ret, &a, &b, &c);
  twist_point_set(&r, &newR); // TODO: is this necessary?

  twist_point_clear(&aAffine);
  curve_point_clear(&bAffine);
  twist_point_clear(&minusA);
  twist_point_clear(&q1);
  twist_point_clear(&minusQ2);
  twist_point_clear(&r);
  gfp2_clear(&r2);

  gfp2_clear(&a);
  gfp2_clear(&b);
  gfp2_clear(&c);
  twist_point_clear(&newR);
}

// finalExponentiation computes the (p¹²-1)/Order-th power of an element of
// GF(p¹²) to obtain an element of GT (steps 13-15 of algorithm 1 from
// http://cryptojedi.org/papers/dclxvi-20100714.pdf)
void optate_final_exponentiation(gfp12* in, gfp12* t0) {
  gfp12 t1;
  gfp12_new(&t1);

  // This is the p^6-Frobenius
  gfp6_negative(&t1.x, &in->x);
  gfp6_set(&t1.y, &in->y);

  gfp12 inv;
  gfp12_new(&inv);
  gfp12_invert(&inv, in);
  gfp12_mul(&t1, &t1, &inv);

  gfp12 t2;
  gfp12_new(&t2);
  gfp12_frobenius_p2(&t2, &t1);
  gfp12_mul(&t1, &t1, &t2);

  gfp12 fp;
  gfp12_new(&fp);
  gfp12_frobenius(&fp, &t1);
  gfp12 fp2;
  gfp12_new(&fp2);
  gfp12_frobenius_p2(&fp2, &t1);
  gfp12 fp3;
  gfp12_new(&fp3);
  gfp12_frobenius(&fp3, &fp2);

  gfp12 fu, fu2, fu3;
  gfp12_new(&fu);
  gfp12_new(&fu2);
  gfp12_new(&fu3);
  gfp12_exp(&fu, &t1, u);
  gfp12_exp(&fu2, &fu, u);
  gfp12_exp(&fu3, &fu2, u);

  gfp12 y3;
  gfp12_new(&y3);
  gfp12_frobenius(&y3, &fu);
  gfp12 fu2p;
  gfp12_new(&fu2p);
  gfp12_frobenius(&fu2p, &fu2);
  gfp12 fu3p;
  gfp12_new(&fu3p);
  gfp12_frobenius(&fu3p, &fu3);
  gfp12 y2;
  gfp12_new(&y2);
  gfp12_frobenius_p2(&y2, &fu2);

  gfp12 y0;
  gfp12_new(&y0);
  gfp12_mul(&y0, &fp, &fp2);
  gfp12_mul(&y0, &y0, &fp3);

  gfp12 y1, y4, y5;
  gfp12_new(&y1);
  gfp12_new(&y4);
  gfp12_new(&y5);
  gfp12_conjugate(&y1, &t1);
  gfp12_conjugate(&y5, &fu2);
  gfp12_conjugate(&y3, &y3);
  gfp12_mul(&y4, &fu, &fu2p);
  gfp12_conjugate(&y4, &y4);

  gfp12 y6;
  gfp12_new(&y6);
  gfp12_mul(&y6, &fu3, &fu3p);
  gfp12_conjugate(&y6, &y6);

  gfp12_square(t0, &y6);
  gfp12_mul(t0, t0, &y4);
  gfp12_mul(t0, t0, &y5);
  gfp12_mul(&t1, &y3, &y5);
  gfp12_mul(&t1, &t1, t0);
  gfp12_mul(t0, t0, &y2);
  gfp12_square(&t1, &t1);
  gfp12_mul(&t1, &t1, t0);
  gfp12_square(&t1, &t1);
  gfp12_mul(t0, &t1, &y1);
  gfp12_mul(&t1, &t1, &y0);
  gfp12_square(t0, t0);
  gfp12_mul(t0, t0, &t1);

  gfp12_clear(&inv);
  gfp12_clear(&t1);
  gfp12_clear(&t2);
  gfp12_clear(&fp);
  gfp12_clear(&fp2);
  gfp12_clear(&fp3);
  gfp12_clear(&fu);
  gfp12_clear(&fu2);
  gfp12_clear(&fu3);
  gfp12_clear(&fu2p);
  gfp12_clear(&fu3p);
  gfp12_clear(&y0);
  gfp12_clear(&y1);
  gfp12_clear(&y2);
  gfp12_clear(&y3);
  gfp12_clear(&y4);
  gfp12_clear(&y5);
  gfp12_clear(&y6);

  // return t0
}

void optate_optimal_ate(twist_point* a, curve_point* b, gfp12* ret) {
  gfp12 e;
  gfp12_new(&e);
  optate_miller(a, b, &e);
  optate_final_exponentiation(&e, ret);
  gfp12_clear(&e);

  if (twist_point_is_infinity(a) || curve_point_is_infinity(b)) {
    gfp12_set_one(ret);
  }
  // return ret
}
