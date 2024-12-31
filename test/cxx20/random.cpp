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

  {
    using ul::bn::Rand;
    Rand rand0;
    Rand rand1 = rand0;
    std::vector<Rand::result_type> vec0, vec1;
    for(int i = 0; i < 128; ++i) {
      vec0.push_back(rand0());
      rand0();
      rand0();
      rand0();
    }
    for(int i = 0; i < 128; ++i) {
      vec1.push_back(rand1());
      rand1.discard(3);
    }
    T_assert(vec0 == vec1);
  }
}

int main() {
  testIt(test);
  return 0;
}
