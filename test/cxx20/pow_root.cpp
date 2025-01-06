#include "test.hpp"

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
      T_assert_eq(BigInt(a).pow(e), fastpow(a, e));
      T_assert_eq(BigInt(a).pow(BigInt(e)), fastpow(a, e));
    }
  }

  T_assert_eq(BigInt("0x100").pow(0xFFFF), BigInt::from2Exp(0xFFFF * 8));
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

  for(auto t = TEST_SMALL; t--;) {
    BigInt x = BigInt::fromRandom("0xFFF");
    BigInt e = BigInt::fromRandom("0x10");
    if(x == 0 || e == 0)
      continue;
    auto obj = x.rootrem(e);
    BigInt pow = obj.first.pow(e);
    T_assert(pow <= x && x < (obj.first + 1).pow(e));
    T_assert(x - pow == obj.second);
  }
}

void test() {
  testPower();
  testSqrt();
  testRoot();
}
int main() {
  testIt(test);
  return 0;
}
