
#include "stdio.h"
#include "gmp.h"
#include "gfp12.h"
#include "curve.h"
#include "twist.h"
#include "optate.h"

#define G1 curve_point
#define G2 twist_point

// PairingCheck calculates the Optimal Ate pairing for a set of points.
int pairing_check(G1 a[], G2 b[], int n) {
  gfp12 acc;
  gfp12_new(&acc);
  gfp12_set_one(&acc);

  gfp12 m;
  gfp12_new(&m);

  for (int i = 0; i < n; i++) {
    if (curve_point_is_infinity(&a[i]) || twist_point_is_infinity(&b[i])) {
      continue;
    }

    optate_miller(&b[i], &a[i], &m);

    gfp12_mul(&acc, &acc, &m);
  }
  gfp12 ret;
  gfp12_new(&ret);
  optate_final_exponentiation(&ret, &acc);

  int is_one = gfp12_is_one(&ret);

  gfp12_clear(&acc);
  gfp12_clear(&m);
  gfp12_clear(&ret);

  return is_one;
}

int main() {
  init_constants();

  /*
  G1 a[1];
  G2 b[1];

  curve_point_new(&a[0]);
  twist_point_new(&b[0]);

  pairing_check(a, b, 1);

  curve_point_clear(&a[0]);
  twist_point_clear(&b[0]);
  */

  setvbuf(stdout, NULL, _IONBF, 0);
  setbuf(stdout, NULL);

  printf("main\n");

  /* ECADD / ECMUL
  curve_point s;
  curve_point_new(&s);

  curve_point c;
  curve_point_new(&c);
  mpz_set_ui(c.x, 1);
  mpz_set_ui(c.y, 2);
  mpz_set_ui(c.z, 1);
  mpz_set_ui(c.t, 1);

  curve_point d;
  curve_point_new(&d);
  mpz_set_ui(d.x, 1);
  mpz_set_ui(d.y, 2);
  mpz_set_ui(d.z, 1);
  mpz_set_ui(d.t, 1);

  mpz_t m;
  mpz_init(m);
  mpz_set_ui(m, 2);

  curve_point_add(&s, &c, &d);
  curve_point_make_affine(&s);
  mpz_out_str(stdout, 16, s.x);
  printf("\n");
  mpz_out_str(stdout, 16, s.y);
  printf("\n");
  mpz_out_str(stdout, 16, s.z);
  printf("\n");
  mpz_out_str(stdout, 16, s.t);
  printf("\n");

  curve_point_clear(&c);
  mpz_clear(m);
  */

  // ECPAIR
  G1 g1[2];
  curve_point_new(&g1[0]);
  mpz_set_str(g1[0].x, "2cf44499d5d27bb186308b7af7af02ac5bc9eeb6a3d147c186b21fb1b76e18da", 16);
  mpz_set_str(g1[0].y, "2c0f001f52110ccfe69108924926e45f0b0c868df0e7bde1fe16d3242dc715f6", 16);
  mpz_set_ui(g1[0].z, 1);
  mpz_set_ui(g1[0].t, 1);

  G2 g2[2];
  twist_point_new(&g2[0]);
  mpz_set_str(g2[0].x.x, "1fb19bb476f6b9e44e2a32234da8212f61cd63919354bc06aef31e3cfaff3ebc", 16);
  mpz_set_str(g2[0].x.y, "22606845ff186793914e03e21df544c34ffe2f2f3504de8a79d9159eca2d98d9", 16);
  mpz_set_str(g2[0].y.x, "2bd368e28381e8eccb5fa81fc26cf3f048eea9abfdd85d7ed3ab3698d63e4f90", 16);
  mpz_set_str(g2[0].y.y, "2fe02e47887507adf0ff1743cbac6ba291e66f59be6bd763950bb16041a0a85e", 16);
  gfp2_set_one(&g2[0].z);
  gfp2_set_one(&g2[0].t);

  curve_point_new(&g1[1]);
  mpz_set_str(g1[1].x, "0000000000000000000000000000000000000000000000000000000000000001", 16);
  mpz_set_str(g1[1].y, "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd45", 16);
  mpz_set_ui(g1[1].z, 1);
  mpz_set_ui(g1[1].t, 1);

  twist_point_new(&g2[1]);
  mpz_set_str(g2[1].x.x, "1971ff0471b09fa93caaf13cbf443c1aede09cc4328f5a62aad45f40ec133eb4", 16);
  mpz_set_str(g2[1].x.y, "091058a3141822985733cbdddfed0fd8d6c104e9e9eff40bf5abfef9ab163bc7", 16);
  mpz_set_str(g2[1].y.x, "2a23af9a5ce2ba2796c1f4e453a370eb0af8c212d9dc9acd8fc02c2e907baea2", 16);
  mpz_set_str(g2[1].y.y, "23a8eb0b0996252cb548a4487da97b02422ebc0e834613f954de6c7e0afdc1fc", 16);
  gfp2_set_one(&g2[1].z);
  gfp2_set_one(&g2[1].t);

  int ret = pairing_check(g1, g2, 2);
  printf("ret = %i\n", ret);

  return 0;
}
