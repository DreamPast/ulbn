#include "test.hpp"

void test() {
  for(auto t = TEST_BIG; t--;) {
    for(int i = 0; i < 16; ++i)
      T_assert(BigInt::fromRandom(i) <= BigInt::from2Exp(i));
  }

  for(auto t = TEST_BIG; t--;) {
    for(int i = 0; i < 16; ++i)
      T_assert(BigInt::fromRandom(BigInt(i)) <= BigInt::from2Exp(BigInt(i)));
  }

  for(int tt = 1; tt <= 100; ++tt) {
    BigInt lbound = BigInt::fromRandom(100), rbound = BigInt::fromRandom(100);
    for(auto t = (TEST_BIG + 99) / 100; t--;) {
      if(lbound == rbound)
        continue;
      BigInt g = BigInt::fromRandomRange(lbound, rbound);
      T_assert(g >= std::min(lbound, rbound) && g < std::max(lbound, rbound));
    }
  }
}

int main() {
  testIt(test);
  return 0;
}
