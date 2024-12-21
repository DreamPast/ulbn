#include "test.hpp"

void testGcdLcm() {
  puts("======Test GCD LCM");

  for(int x = -LIMIT; x <= LIMIT; ++x)
    for(int y = x + 1; y <= LIMIT; ++y) {
      T_assert_eq(BigInt(x).gcd(BigInt(y)), std::gcd(x, y));
      if(fitType<ulbn_limb_t>(y))
        T_assert_eq(BigInt(x).gcd(static_cast<ulbn_limb_t>(y)), std::gcd(x, y));
      if(fitType<ulbn_slimb_t>(y))
        T_assert_eq(BigInt(x).gcd(static_cast<ulbn_slimb_t>(y)), std::gcd(x, y));
      if(y)
        T_assert_eq(BigInt(x).lcm(y) % y, 0);
      if(x)
        T_assert_eq(BigInt(x).lcm(y) % x, 0);
      if(x && y)
        T_assert(BigInt(x).lcm(y).abs() <= (BigInt(x) * y).abs());
    }
}
void testGcdext() {
  puts("======Test Extended GCD");

  for(int t = TEST_BIG; t--;) {
    int64_t a = static_cast<int64_t>(mt64());
    int64_t b = static_cast<int64_t>(mt64());
    auto [g, x, y] = BigInt(a).gcdext(b);
    T_assert_eq(std::gcd(a, b), g);
    T_assert_eq(BigInt(a) * x + BigInt(b) * y, g);
  }

  for(int t = TEST_SMALL; t--;) {
    BigInt a = BigInt::fromRandom("1024");
    BigInt b = BigInt::fromRandom("1024");
    auto [g, x, y] = a.gcdext(b);
    T_assert_eq(g, a.gcd(b));
    T_assert_eq(BigInt(a) * x + BigInt(b) * y, g);
    try {
      T_assert_eq(x, a.invert(b));
      T_assert_eq(g, 1);
    } catch(const ul::bn::Exception& e) {
      if(e.getError() == ULBN_ERR_INVALID) {
        T_assert(g != 1);
      } else {
        throw;
      }
    }
  }
}
void test() {
  puts("===Test Number Theory");
  testGcdLcm();
  testGcdext();
}

int main() {
  testIt(test);
  return 0;
}
