#include "test.hpp"

struct DivMod4Case {
  int a;
  enum ULBN_ROUND_ENUM round_mode;
  int q, r;
};
static const DivMod4Case _divmod_cases[] = {
  { 1, ULBN_ROUND_DOWN, 0, 1 },         { 1, ULBN_ROUND_UP, 1, -3 },          /* */
  { 1, ULBN_ROUND_FLOOR, 0, 1 },        { 1, ULBN_ROUND_CEILING, 1, -3 },     /* */
  { -1, ULBN_ROUND_DOWN, 0, -1 },       { -1, ULBN_ROUND_UP, -1, 3 },         /* */
  { -1, ULBN_ROUND_FLOOR, -1, 3 },      { -1, ULBN_ROUND_CEILING, 0, -1 },    /* */
  { 1, ULBN_ROUND_HALF_ODD, 0, 1 },     { 1, ULBN_ROUND_HALF_EVEN, 0, 1 },    /* */
  { 1, ULBN_ROUND_HALF_DOWN, 0, 1 },    { 1, ULBN_ROUND_HALF_UP, 0, 1 },      /* */
  { 2, ULBN_ROUND_HALF_ODD, 1, -2 },    { 2, ULBN_ROUND_HALF_EVEN, 0, 2 },    /* */
  { 2, ULBN_ROUND_HALF_DOWN, 0, 2 },    { 2, ULBN_ROUND_HALF_UP, 1, -2 },     /* */
  { 3, ULBN_ROUND_HALF_ODD, 1, -1 },    { 3, ULBN_ROUND_HALF_EVEN, 1, -1 },   /* */
  { 3, ULBN_ROUND_HALF_DOWN, 1, -1 },   { 3, ULBN_ROUND_HALF_UP, 1, -1 },     /* */
  { 5, ULBN_ROUND_HALF_ODD, 1, 1 },     { 5, ULBN_ROUND_HALF_EVEN, 1, 1 },    /* */
  { 5, ULBN_ROUND_HALF_DOWN, 1, 1 },    { 5, ULBN_ROUND_HALF_UP, 1, 1 },      /* */
  { 6, ULBN_ROUND_HALF_ODD, 1, 2 },     { 6, ULBN_ROUND_HALF_EVEN, 2, -2 },   /* */
  { 6, ULBN_ROUND_HALF_DOWN, 1, 2 },    { 6, ULBN_ROUND_HALF_UP, 2, -2 },     /* */
  { 7, ULBN_ROUND_HALF_ODD, 2, -1 },    { 7, ULBN_ROUND_HALF_EVEN, 2, -1 },   /* */
  { 7, ULBN_ROUND_HALF_DOWN, 2, -1 },   { 7, ULBN_ROUND_HALF_UP, 2, -1 },     /* */
  { -1, ULBN_ROUND_HALF_ODD, 0, -1 },   { -1, ULBN_ROUND_HALF_EVEN, 0, -1 },  /* */
  { -1, ULBN_ROUND_HALF_DOWN, 0, -1 },  { -1, ULBN_ROUND_HALF_UP, 0, -1 },    /* */
  { -2, ULBN_ROUND_HALF_ODD, -1, 2 },   { -2, ULBN_ROUND_HALF_EVEN, 0, -2 },  /* */
  { -2, ULBN_ROUND_HALF_DOWN, 0, -2 },  { -2, ULBN_ROUND_HALF_UP, -1, 2 },    /* */
  { -3, ULBN_ROUND_HALF_ODD, -1, 1 },   { -3, ULBN_ROUND_HALF_EVEN, -1, 1 },  /* */
  { -3, ULBN_ROUND_HALF_DOWN, -1, 1 },  { -3, ULBN_ROUND_HALF_UP, -1, 1 },    /* */
  { -5, ULBN_ROUND_HALF_ODD, -1, -1 },  { -5, ULBN_ROUND_HALF_EVEN, -1, -1 }, /* */
  { -5, ULBN_ROUND_HALF_DOWN, -1, -1 }, { -5, ULBN_ROUND_HALF_UP, -1, -1 },   /* */
  { -6, ULBN_ROUND_HALF_ODD, -1, -2 },  { -6, ULBN_ROUND_HALF_EVEN, -2, 2 },  /* */
  { -6, ULBN_ROUND_HALF_DOWN, -1, -2 }, { -6, ULBN_ROUND_HALF_UP, -2, 2 },    /* */
  { -7, ULBN_ROUND_HALF_ODD, -2, 1 },   { -7, ULBN_ROUND_HALF_EVEN, -2, 1 },  /* */
  { -7, ULBN_ROUND_HALF_DOWN, -2, 1 },  { -7, ULBN_ROUND_HALF_UP, -2, 1 },    /* */
};
static const enum ULBN_ROUND_ENUM _round_modes[] = {
  ULBN_ROUND_DOWN,      ULBN_ROUND_UP,        ULBN_ROUND_FLOOR,   ULBN_ROUND_CEILING,  ULBN_ROUND_HALF_ODD,
  ULBN_ROUND_HALF_EVEN, ULBN_ROUND_HALF_DOWN, ULBN_ROUND_HALF_UP, ULBN_ROUND_FAITHFUL,
};

void testDivMod2Exp() {
  puts("======Test DivMod 2Exp");

  for(int t = TEST_BIG; t--;) {
    BigInt a = BigInt::fromRandom("32");
    for(short i = 0; i < 32; ++i) {
      auto pair = a.divmod2Exp(i);
      auto ansPair = a.divmod(BigInt::from2Exp(i));
      T_assert_pair_eq(pair, ansPair.first, ansPair.second);
      T_assert_eq(a.is2ExpDivisible(i), ansPair.second == 0);

      BigInt q = a;
      T_assert(
        ulbi_divmod_2exp_sbits(ulbn_default_alloc(), q.get(), ul_nullptr, q.get(), i)
        == (ansPair.second ? ULBN_ERR_INEXACT : 0)
      );
      T_assert(q == ansPair.first);
      BigInt r = a;
      T_assert(ulbi_divmod_2exp_sbits(ulbn_default_alloc(), ul_nullptr, r.get(), r.get(), i) == 0);
      T_assert(r == ansPair.second);
    }
    for(short i = 0; i < 32; ++i) {
      auto pair = a.divmod2Exp(BigInt(i));
      auto ansPair = a.divmod(BigInt::from2Exp(BigInt(i)));
      T_assert_pair_eq(pair, ansPair.first, ansPair.second);
      T_assert_eq(a.is2ExpDivisible(BigInt(i)), ansPair.second == 0);
    }
    for(int i = 0; i >= -4; --i) {
      T_assert_pair_eq(a.divmod2Exp(i), a * BigInt::from2Exp(-i), 0);
      T_assert_eq(a.is2ExpDivisible(i), true);
    }
  }
}
void testDivMod2ExpEx() {
  puts("======Test DivMod 2Exp Ex");

  for(int t = TEST_BIG; t--;) {
    BigInt a = BigInt::fromRandom("32");
    for(auto round_mode: _round_modes) {
      for(int i = 0; i >= -4; --i)
        T_assert_pair_eq(a.divmod2Exp(i, round_mode), a * BigInt::from2Exp(-i), 0);
    }
  }

  for(auto&& item: _divmod_cases) {
    T_assert_pair_eq(BigInt(item.a).divmod2Exp(2, item.round_mode), item.q, item.r);
    T_assert_pair_eq(BigInt(item.a).divmod2Exp(2_bi, item.round_mode), item.q, item.r);
    T_assert_eq(BigInt(item.a).div2Exp(2, item.round_mode), item.q);
    T_assert_eq(BigInt(item.a).mod2Exp(2, item.round_mode), item.r);
    T_assert_eq(BigInt(item.a).div2Exp(2_bi, item.round_mode), item.q);
    T_assert_eq(BigInt(item.a).mod2Exp(2_bi, item.round_mode), item.r);
  }
}

void test() {
  testDivMod2Exp();
  testDivMod2ExpEx();
}
int main() {
  testIt(test);
  return 0;
}