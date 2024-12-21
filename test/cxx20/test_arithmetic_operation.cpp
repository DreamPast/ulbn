#include "test.hpp"

void testAddSub() {
  puts("======Test AddSub");

  for(int a = -LIMIT; a <= LIMIT; ++a)
    for(int b = -LIMIT; b <= LIMIT; ++b) {
      T_assert(BigInt(a) + BigInt(b) == a + b);
      T_assert(BigInt(a) - BigInt(b) == a - b);
      if(fitType<int8_t>(b)) {
        T_assert(BigInt(a) + static_cast<int8_t>(b) == a + b);
        T_assert(BigInt(a) - static_cast<int8_t>(b) == a - b);
      }
      if(fitType<int8_t>(a)) {
        T_assert(static_cast<int8_t>(a) + BigInt(b) == a + b);
        T_assert(static_cast<int8_t>(a) - BigInt(b) == a - b);
      }
      if(fitType<uint8_t>(b)) {
        T_assert(BigInt(a) + static_cast<uint8_t>(b) == a + b);
        T_assert(BigInt(a) - static_cast<uint8_t>(b) == a - b);
      }
      if(fitType<uint8_t>(a)) {
        T_assert(static_cast<uint8_t>(a) + BigInt(b) == a + b);
        T_assert(static_cast<uint8_t>(a) - BigInt(b) == a - b);
      }
    }
}
void testMul() {
  puts("======Test Mul");

  BigInt a0;
  BigInt a1 = 12_bi;
  BigInt a2 = BigInt("12345678901234567890");


  T_assert(a1 * a2 == BigInt("148148146814814814680"));
  T_assert(a1 * -a2 == BigInt("-148148146814814814680"));
  T_assert(-a1 * a2 == BigInt("-148148146814814814680"));
  T_assert(-a1 * -a2 == BigInt("148148146814814814680"));

  T_assert(a2 * a2 == BigInt("152415787532388367501905199875019052100"));
  T_assert(a2 * -a2 == BigInt("-152415787532388367501905199875019052100"));
  T_assert(-a2 * a2 == BigInt("-152415787532388367501905199875019052100"));
  T_assert(-a2 * -a2 == BigInt("152415787532388367501905199875019052100"));


  T_assert(a2 * static_cast<uint8_t>(12u) == BigInt("148148146814814814680"));
  T_assert(-a2 * static_cast<uint8_t>(12u) == BigInt("-148148146814814814680"));

  T_assert(a2 * static_cast<int8_t>(12) == BigInt("148148146814814814680"));
  T_assert(a2 * static_cast<int8_t>(-12) == BigInt("-148148146814814814680"));
  T_assert(-a2 * static_cast<int8_t>(12) == BigInt("-148148146814814814680"));
  T_assert(-a2 * static_cast<int8_t>(-12) == BigInt("148148146814814814680"));


  for(int64_t a = -LIMIT; a <= LIMIT; ++a) {
    for(int64_t b = -LIMIT; b <= LIMIT; ++b) {
      T_assert(BigInt(a) * BigInt(b) == a * b);
      if(fitType<int8_t>(b))
        T_assert(BigInt(a) * static_cast<int8_t>(b) == a * b);
      if(fitType<uint8_t>(b))
        T_assert(BigInt(a) * static_cast<uint8_t>(b) == a * b);
    }
    {
      BigInt r(a);
      T_assert((r *= r) == a * a);
    }
  }

  {
    BigInt r = 1, a = 0x100;
    for(int t = 1; t <= 0xFF; ++t) {
      r *= a;
      T_assert(r == BigInt::from2Exp(8 * t));
      T_assert(r == BigInt::from2Exp(BigInt(8 * t)));
    }
  }

  {
    BigInt r = 1, a = BigInt::from2Exp(1000);
    for(int t = 1; t <= 0xFF; ++t) {
      r *= a;
      T_assert(r == BigInt::from2Exp(1000 * t));
      T_assert(r == BigInt::from2Exp(BigInt(1000 * t)));
    }
  }
}
void testMulRandom() {
  puts("======Test Mul (Random)");
  std::uniform_int_distribution<uint32_t> dist;
  for(auto t = TEST_BIG; t--;) {
    const uint32_t a = dist(mt64);
    const uint32_t b = dist(mt64);
    T_assert(BigInt(a) * BigInt(b) == static_cast<uint64_t>(a) * b);
  }
}
void testDivMod() {
  puts("======Test DivMod");

  BigInt a2 = BigInt("12345678901234567890");

  T_assert(a2 / 12_bi == "1028806575102880657"_bi && a2 % 12_bi == 6);
  T_assert(a2 / 12u == "1028806575102880657"_bi && a2 % 12u == 6);
  T_assert(a2 / 12 == "1028806575102880657"_bi && a2 % 12 == 6);

  for(unsigned i = 64; i < 256; ++i) {
    BigInt d = BigInt::from2Exp(i);
    T_assert((a2 / d) * d + (a2 % d) == a2);
    T_assert((a2 * d) / d == a2 && (a2 * d) % d == 0);
    d = BigInt::from2Exp(BigInt(i));
    T_assert((a2 / d) * d + (a2 % d) == a2);
    T_assert((a2 * d) / d == a2 && (a2 * d) % d == 0);
  }


  for(int a = -LIMIT; a <= LIMIT; ++a)
    for(int b = -LIMIT; b <= LIMIT; ++b)
      if(b != 0) {
        T_assert(BigInt(a) / BigInt(b) == a / b);
        T_assert(BigInt(a) % BigInt(b) == a % b);
        if(fitType<int8_t>(b)) {
          T_assert(BigInt(a) / static_cast<int8_t>(b) == a / b);

          ulbn_slimb_t r;
          T_assert(
            ulbi_divmod_slimb(ulbn_default_alloc(), ul_nullptr, &r, BigInt(a).get(), static_cast<ulbn_slimb_t>(b)) >= 0
          );
          T_assert(r == a % b);
        }
        if(fitType<uint8_t>(b)) {
          T_assert(BigInt(a) / static_cast<uint8_t>(b) == a / b);

          BigInt tmp(a);
          ulbn_limb_t r;
          T_assert(ulbi_divmod_limb(ulbn_default_alloc(), ul_nullptr, &r, tmp.get(), static_cast<ulbn_limb_t>(b)) >= 0);
          T_assert(static_cast<int>(r) == (a % b + b) % b);
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

    T_assert(BigInt(a).divmod(BigInt(b)) == (std::make_pair<BigInt, BigInt>(a / b, a % b)));
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
      T_assert((ra /= ra) == 1);
      ra = a;
      T_assert((ra %= ra) == 0);
    }

    {  // q == a
      BigInt ra(a);
      ra /= BigInt(b);
      T_assert(ra == a / b);
    }

    {  // r == a
      BigInt ra(a);
      ra %= BigInt(b);
      T_assert(ra == a % b);
    }

    {  // q == b
      BigInt ra(a), rb(b);
      T_assert(ulbi_divmod(ulbn_default_alloc(), rb.get(), ul_nullptr, ra.get(), rb.get()) >= 0);
      T_assert(rb == a / b);
    }

    {  // r == b
      BigInt ra(a), rb(b);
      T_assert(ulbi_divmod(ulbn_default_alloc(), ul_nullptr, rb.get(), ra.get(), rb.get()) >= 0);
      T_assert(rb == a % b);
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
    T_assert(pairEqual(BigInt(item.a).divmod(4, item.round_mode), item.q, item.r));
    T_assert(pairEqual(BigInt(item.a).divmod(4_bi, item.round_mode), item.q, item.r));
    T_assert(BigInt(item.a).div(4, item.round_mode) == item.q);
    T_assert(BigInt(item.a).mod(4, item.round_mode) == item.r);
    T_assert(BigInt(item.a).div(4_bi, item.round_mode) == item.q);
    T_assert(BigInt(item.a).mod(4_bi, item.round_mode) == item.r);
  }
}
void testDivMod2Exp() {
  puts("======Test DivMod 2Exp");

  for(int t = TEST_BIG; t--;) {
    BigInt a = BigInt::fromRandom("32");
    for(short i = 0; i < 32; ++i) {
      auto pair = a.divmod2Exp(i);
      auto ansPair = a.divmod(BigInt::from2Exp(i));
      T_assert(pairEqual(pair, ansPair));

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
      T_assert(pairEqual(pair, ansPair));
    }
    for(int i = 0; i >= -4; --i) {
      T_assert(pairEqual(a.divmod2Exp(i), a * BigInt::from2Exp(-i), 0));
    }
  }
}
void testDivMod2ExpEx() {
  puts("======Test DivMod 2Exp Ex");

  for(auto&& item: _divmod_cases) {
    T_assert(pairEqual(BigInt(item.a).divmod2Exp(2, item.round_mode), item.q, item.r));
    T_assert(pairEqual(BigInt(item.a).divmod2Exp(2_bi, item.round_mode), item.q, item.r));
    T_assert(BigInt(item.a).div2Exp(2, item.round_mode) == item.q);
    T_assert(BigInt(item.a).mod2Exp(2, item.round_mode) == item.r);
    T_assert(BigInt(item.a).div2Exp(2_bi, item.round_mode) == item.q);
    T_assert(BigInt(item.a).mod2Exp(2_bi, item.round_mode) == item.r);
  }
}
void testBigMulDiv() {
  puts("======Test Big MulDiv");

  for(int t = TEST_SMALL; t--;) {
    BigInt x, y, z;
    x = 1 + BigInt::fromRandom("0xFFF");
    y = 1 + BigInt::fromRandom("0xFFF");
    z = x * y;
    T_assert(z / x == y && z % x == 0);
    T_assert(z / y == x && z % y == 0);
  }

  for(int t = TEST_SMALL; t--;) {
    BigInt x, y, z;
    x = 1 + BigInt::fromRandom("0xFFF");
    y = 1 + BigInt::fromRandom("0xFF");
    z = x * y;
    T_assert(z / x == y && z % x == 0);
    T_assert(z / y == x && z % y == 0);
  }

  for(int t = TEST_VERY_SMALL; t--;) {
    BigInt x, y;
    x = 1 + BigInt::fromRandom("0xFFFFFF");
    y = 1 + BigInt::fromRandom("0xFFFF");
    auto [q, r] = x.divmod(y);
    T_assert(r > 0 && q > 0 && q * y + r == x);
  }
}
void testPower() {
  puts("======Test Power");
  auto&& fastpow = [](int64_t a, unsigned e) {
    int64_t r = 1;
    while(e) {
      if(e & 1)
        r *= a;
      a *= a;
      e >>= 1;
    }
    return r;
  };
  for(int64_t a = 2; a <= 32; ++a) {
    for(unsigned e = 1; pow(static_cast<double>(a), e) < static_cast<double>(1ull << 63); ++e) {
      T_assert(BigInt(a).pow(e) == fastpow(a, e));
      T_assert(BigInt(a).pow(BigInt(e)) == fastpow(a, e));
    }
  }

  T_assert(BigInt("0x100").pow(0xFFFF) == BigInt::from2Exp(0xFFFF * 8));
}
void testSqrt() {
  puts("======Test Sqrt");

  T_assert_exception([] { BigInt(-1).sqrt(); }, ULBN_ERR_INVALID);

  for(int64_t i = 0x0; i <= 0xFFFF; ++i) {
    BigInt x = i;
    auto ret = x.sqrtrem();
    T_assert(ret.first * ret.first <= x && x < (ret.first + 1) * (ret.first + 1));
    T_assert(x - ret.first * ret.first == ret.second);
  }

  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt::fromRandom("0xFFF");

    auto ret = x.sqrtrem();
    T_assert(ret.first * ret.first <= x && x < (ret.first + 1) * (ret.first + 1));
    T_assert(x - ret.first * ret.first == ret.second);

    auto xs = x.sqrt();
    T_assert(xs * xs <= x && x < (xs + 1) * (xs + 1));

    auto xr = x;
    ulbi_sqrtrem(ulbn_default_alloc(), ul_nullptr, xr.get(), xr.get());
    T_assert(x - xs * xs == xr);
  }
}
void testRoot() {
  puts("======Test Root");
  T_assert_exception([] { (0_bi).root(0); }, ULBN_ERR_INVALID);
  T_assert_exception([] { (0_bi).root(1); }, 0);
  T_assert_exception([] { (0_bi).root(2); }, 0);
  T_assert_exception([] { (0_bi).root(3); }, 0);
  T_assert_exception([] { (0_bi).root(-1); }, ULBN_ERR_DIV_BY_ZERO);
  T_assert_exception([] { (0_bi).root(-2); }, ULBN_ERR_DIV_BY_ZERO);
  T_assert_exception([] { (0_bi).root(-3); }, ULBN_ERR_DIV_BY_ZERO);

  T_assert_exception([] { (1_bi).root(0); }, ULBN_ERR_INVALID);
  T_assert_exception([] { (1_bi).root(1); }, 0);
  T_assert_exception([] { (1_bi).root(2); }, 0);
  T_assert_exception([] { (1_bi).root(3); }, 0);
  T_assert_exception([] { (1_bi).root(-1); }, 0);
  T_assert_exception([] { (1_bi).root(-2); }, 0);
  T_assert_exception([] { (1_bi).root(-3); }, 0);

  T_assert_exception([] { (2_bi).root(0); }, ULBN_ERR_INVALID);
  T_assert_exception([] { (2_bi).root(1); }, 0);
  T_assert_exception([] { (2_bi).root(2); }, 0);
  T_assert_exception([] { (2_bi).root(3); }, 0);
  {
    BigInt a, r;
    a = 2;
    T_assert(ulbi_rootrem(ulbn_default_alloc(), a.get(), r.get(), a.get(), (-1_bi).get()) == 0);
    a = 2;
    T_assert(ulbi_rootrem(ulbn_default_alloc(), a.get(), r.get(), a.get(), (-2_bi).get()) == 0);
    a = 2;
    T_assert(ulbi_rootrem(ulbn_default_alloc(), a.get(), r.get(), a.get(), (-3_bi).get()) == 0);
  }

  T_assert_exception([] { (-1_bi).root(0); }, ULBN_ERR_INVALID);
  T_assert_exception([] { (-1_bi).root(1); }, 0);
  T_assert_exception([] { (-1_bi).root(2); }, ULBN_ERR_INVALID);
  T_assert_exception([] { (-1_bi).root(3); }, 0);
  T_assert_exception([] { (-1_bi).root(-1); }, 0);
  T_assert_exception([] { (-1_bi).root(-2); }, ULBN_ERR_INVALID);
  T_assert_exception([] { (-1_bi).root(-3); }, 0);

  T_assert_exception([] { (-2_bi).root(0); }, ULBN_ERR_INVALID);
  T_assert_exception([] { (-2_bi).root(1); }, 0);
  T_assert_exception([] { (-2_bi).root(2); }, ULBN_ERR_INVALID);
  T_assert_exception([] { (-2_bi).root(3); }, 0);
  {
    BigInt a, r;
    a = -2;
    T_assert(ulbi_rootrem(ulbn_default_alloc(), a.get(), r.get(), a.get(), (-1_bi).get()) == 0);
    a = -2;
    T_assert(ulbi_rootrem(ulbn_default_alloc(), a.get(), r.get(), a.get(), (-2_bi).get()) == ULBN_ERR_INVALID);
    a = -2;
    T_assert(ulbi_rootrem(ulbn_default_alloc(), a.get(), r.get(), a.get(), (-3_bi).get()) == 0);
  }

  for(int64_t i = 1; i <= 0xFFF; i += 3) {
    for(int e: { 1, 2, 3, 4, 5, 7, 9 }) {
      BigInt x = BigInt(i);
      auto obj = x.rootrem(e);
      BigInt pow = obj.first.pow(e);
      T_assert(pow <= x && x < (obj.first + 1).pow(e));
      T_assert(x - pow == obj.second);
    }
  }

  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt::fromRandom("0xFFF");
    BigInt e = BigInt::fromRandom("0x10");
    auto obj = x.rootrem(e);
    BigInt pow = obj.first.pow(e);
    T_assert(pow <= x && x < (obj.first + 1).pow(e));
    T_assert(x - pow == obj.second);
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
  testDivMod2Exp();
  testDivMod2ExpEx();
  testPower();
  testSqrt();
  testRoot();
}
int main() {
  testIt(test);
  return 0;
}
