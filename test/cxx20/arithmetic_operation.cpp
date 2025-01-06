#include "test.hpp"

void testAddSub() {
  puts("======Test AddSub");

  for(auto a = -LIMIT; a <= LIMIT; ++a)
    for(auto b = -LIMIT; b <= LIMIT; ++b) {
      T_assert_eq(BigInt(a) + BigInt(b), a + b);
      T_assert_eq(BigInt(a) - BigInt(b), a - b);
      if(fitType<int8_t>(b)) {
        T_assert_eq(BigInt(a) + static_cast<int8_t>(b), a + b);
        T_assert_eq(BigInt(a) - static_cast<int8_t>(b), a - b);
      }
      if(fitType<int8_t>(a)) {
        T_assert_eq(static_cast<int8_t>(a) + BigInt(b), a + b);
        T_assert_eq(static_cast<int8_t>(a) - BigInt(b), a - b);
      }
      if(fitType<uint8_t>(b)) {
        T_assert_eq(BigInt(a) + static_cast<uint8_t>(b), a + b);
        T_assert_eq(BigInt(a) - static_cast<uint8_t>(b), a - b);
      }
      if(fitType<uint8_t>(a)) {
        T_assert_eq(static_cast<uint8_t>(a) + BigInt(b), a + b);
        T_assert_eq(static_cast<uint8_t>(a) - BigInt(b), a - b);
      }
    }
}
void testMul() {
  puts("======Test Mul");

  BigInt a0;
  BigInt a1 = 12_bi;
  BigInt a2 = BigInt("12345678901234567890");


  T_assert_eq(a1 * a2, BigInt("148148146814814814680"));
  T_assert_eq(a1 * -a2, BigInt("-148148146814814814680"));
  T_assert_eq(-a1 * a2, BigInt("-148148146814814814680"));
  T_assert_eq(-a1 * -a2, BigInt("148148146814814814680"));

  T_assert_eq(a2 * a2, BigInt("152415787532388367501905199875019052100"));
  T_assert_eq(a2 * -a2, BigInt("-152415787532388367501905199875019052100"));
  T_assert_eq(-a2 * a2, BigInt("-152415787532388367501905199875019052100"));
  T_assert_eq(-a2 * -a2, BigInt("152415787532388367501905199875019052100"));


  T_assert_eq(a2 * static_cast<uint8_t>(12u), BigInt("148148146814814814680"));
  T_assert_eq(-a2 * static_cast<uint8_t>(12u), BigInt("-148148146814814814680"));

  T_assert_eq(a2 * static_cast<int8_t>(12), BigInt("148148146814814814680"));
  T_assert_eq(a2 * static_cast<int8_t>(-12), BigInt("-148148146814814814680"));
  T_assert_eq(-a2 * static_cast<int8_t>(12), BigInt("-148148146814814814680"));
  T_assert_eq(-a2 * static_cast<int8_t>(-12), BigInt("148148146814814814680"));


  for(auto a = -LIMIT; a <= LIMIT; ++a) {
    for(auto b = -LIMIT; b <= LIMIT; ++b) {
      T_assert_eq(BigInt(a) * BigInt(b), a * b);
      if(fitType<int8_t>(b))
        T_assert_eq(BigInt(a) * static_cast<int8_t>(b), a * b);
      if(fitType<uint8_t>(b))
        T_assert_eq(BigInt(a) * static_cast<uint8_t>(b), a * b);
    }
    {
      BigInt r(a);
      T_assert_eq((r *= r), a * a);
    }
  }

  {
    BigInt r = 1, a = 0x100;
    for(int t = 1; t <= 0xFF; ++t) {
      r *= a;
      T_assert_eq(r, BigInt::from2Exp(8 * t));
      T_assert_eq(r, BigInt::from2Exp(BigInt(8 * t)));
    }
  }

  {
    BigInt r = 1, a = BigInt::from2Exp(1000);
    for(int t = 1; t <= 0xFF; ++t) {
      r *= a;
      T_assert_eq(r, BigInt::from2Exp(1000 * t));
      T_assert_eq(r, BigInt::from2Exp(BigInt(1000 * t)));
    }
  }
}
void testMulRandom() {
  puts("======Test Mul (Random)");
  std::uniform_int_distribution<uint32_t> dist;
  for(auto t = TEST_BIG; t--;) {
    const uint32_t a = dist(mt64);
    const uint32_t b = dist(mt64);
    T_assert_eq(BigInt(a) * BigInt(b), static_cast<uint64_t>(a) * b);
  }
}
void testDivMod() {
  puts("======Test DivMod");

  BigInt a2 = BigInt("12345678901234567890");

  T_assert_eq(a2 / 12_bi, "1028806575102880657"_bi);
  T_assert_eq(a2 % 12_bi, 6);
  T_assert_eq(a2 / 12u, "1028806575102880657"_bi);
  T_assert_eq(a2 % 12u, 6);
  T_assert_eq(a2 / 12, "1028806575102880657"_bi);
  T_assert_eq(a2 % 12, 6);

  for(unsigned i = 64; i < 256; ++i) {
    BigInt d = BigInt::from2Exp(i);
    T_assert_eq((a2 / d) * d + (a2 % d), a2);
    T_assert_eq((a2 * d) / d, a2);
    T_assert_eq((a2 * d) % d, 0);
    d = BigInt::from2Exp(BigInt(i));
    T_assert_eq((a2 / d) * d + (a2 % d), a2);
    T_assert_eq((a2 * d) / d, a2);
    T_assert_eq((a2 * d) % d, 0);
  }


  for(auto a = -LIMIT; a <= LIMIT; ++a)
    for(auto b = -LIMIT; b <= LIMIT; ++b)
      if(b != 0) {
        T_assert_eq(BigInt(a) / BigInt(b), a / b);
        T_assert_eq(BigInt(a) % BigInt(b), a % b);
        T_assert_eq(BigInt(a).isDivisible(BigInt(b)), (a % b) == 0);

        if(fitType<int8_t>(b)) {
          T_assert_eq(BigInt(a) / static_cast<int8_t>(b), a / b);

          ulbn_slimb_t r;
          T_assert(
            ulbi_divmod_slimb(ulbn_default_alloc(), ul_nullptr, &r, BigInt(a).get(), static_cast<ulbn_slimb_t>(b)) >= 0
          );
          T_assert_eq(r, a % b);
          T_assert_eq(BigInt(a).isDivisible(static_cast<int8_t>(b)), r == 0);
        }
        if(fitType<uint8_t>(b)) {
          T_assert_eq(BigInt(a) / static_cast<uint8_t>(b), a / b);

          BigInt tmp(a);
          ulbn_limb_t r;
          T_assert(ulbi_divmod_limb(ulbn_default_alloc(), ul_nullptr, &r, tmp.get(), static_cast<ulbn_limb_t>(b)) >= 0);
          T_assert_eq(static_cast<int>(r), (a % b + b) % b);
          T_assert_eq(BigInt(a).isDivisible(static_cast<uint8_t>(b)), r == 0);
        }
      }
}
void testDivModRandom() {
  puts("======Test DivMod (Random)");

  std::mt19937_64 mt(std::random_device{}());
  std::uniform_int_distribution<uint64_t> ud1;
  std::uniform_int_distribution<uint64_t> ud2(1);
  for(auto t = TEST_BIG; t--;) {
    const uint64_t a = ud1(mt);
    const uint64_t b = ud2(mt);

    T_assert_pair_eq(BigInt(a).divmod(BigInt(b)), (a / b), (a % b));
    T_assert_eq(BigInt(a).isDivisible(BigInt(b)), (a % b) == 0);
  }
}
void testDivModOverlapRandom() {
  puts("======Test DivMod Overlap (Random)");

  std::uniform_int_distribution<uint64_t> ud1;
  std::uniform_int_distribution<uint64_t> ud2(1);
  for(int64_t t = 0; t <= 10000ll; ++t) {
    const uint64_t a = ud1(mt64);
    const uint64_t b = ud2(mt64);

    {  // a == b
      BigInt ra;
      ra = a;
      T_assert_eq((ra /= ra), 1);
      ra = a;
      T_assert_eq((ra %= ra), 0);
    }

    {  // q == a
      BigInt ra(a);
      ra /= BigInt(b);
      T_assert_eq(ra, a / b);
    }

    {  // r == a
      BigInt ra(a);
      ra %= BigInt(b);
      T_assert_eq(ra, a % b);
    }

    {  // q == b
      BigInt ra(a), rb(b);
      T_assert(ulbi_divmod(ulbn_default_alloc(), rb.get(), ul_nullptr, ra.get(), rb.get()) >= 0);
      T_assert_eq(rb, a / b);
    }

    {  // r == b
      BigInt ra(a), rb(b);
      T_assert(ulbi_divmod(ulbn_default_alloc(), ul_nullptr, rb.get(), ra.get(), rb.get()) >= 0);
      T_assert_eq(rb, a % b);
    }

    {  // q == r
      BigInt ra(a), rb(b);
      T_assert(ulbi_divmod(ulbn_default_alloc(), ra.get(), ra.get(), ra.get(), rb.get()) >= 0);
      T_assert((ra == a / b) || (ra == a % b));
    }
  }
}

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
void testDivModEx() {
  puts("======Test DivMod Ex");

  for(auto&& item: _divmod_cases) {
    T_assert_pair_eq(BigInt(item.a).divmod(4, item.round_mode), item.q, item.r);
    T_assert_pair_eq(BigInt(item.a).divmod(4_bi, item.round_mode), item.q, item.r);
    T_assert(BigInt(item.a).div(4, item.round_mode) == item.q);
    T_assert(BigInt(item.a).mod(4, item.round_mode) == item.r);
    T_assert(BigInt(item.a).div(4_bi, item.round_mode) == item.q);
    T_assert(BigInt(item.a).mod(4_bi, item.round_mode) == item.r);
  }
}
void testBigMulDiv() {
  puts("======Test Big MulDiv");

  for(int t = TEST_SMALL; t--;) {
    BigInt x, y, z;
    x = 1 + BigInt::fromRandom("0xFFF");
    y = 1 + BigInt::fromRandom("0xFFF");
    z = x * y;
    T_assert_eq(z / x, y);
    T_assert_eq(z % x, 0);
    T_assert_eq(z / y, x);
    T_assert_eq(z % y, 0);
  }

  for(int t = TEST_SMALL; t--;) {
    BigInt x, y, z;
    x = 1 + BigInt::fromRandom("0xFFF");
    y = 1 + BigInt::fromRandom("0xFF");
    z = x * y;
    T_assert_eq(z / x, y);
    T_assert_eq(z % x, 0);
    T_assert_eq(z / y, x);
    T_assert_eq(z % y, 0);
  }

  for(int t = TEST_VERY_SMALL; t--;) {
    BigInt x, y;
    x = 1 + BigInt::fromRandom("0xFFFFFF");
    y = 1 + BigInt::fromRandom("0xFFFF");
    auto [q, r] = x.divmod(y);
    T_assert(r > 0);
    T_assert(q > 0);
    T_assert_eq(q * y + r, x);
  }
}

void test() {
  testAddSub();
  testMul();
  testMulRandom();
  testDivMod();
  testDivModRandom();
  testDivModOverlapRandom();
  testDivModEx();
  testBigMulDiv();
}
int main() {
  testIt(test);
  return 0;
}
