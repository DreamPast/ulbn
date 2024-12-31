#include "test.hpp"

void testBitwiseOperation() {
  puts("======Test Bitwise Operation");

  for(int a = -LIMIT; a <= LIMIT; ++a) {
    T_assert_eq((BigInt(a) & BigInt(a)), a);
    T_assert_eq((BigInt(a) | BigInt(a)), a);
    T_assert_eq((BigInt(a) ^ BigInt(a)), 0);
    for(int b = -LIMIT; b <= LIMIT; ++b) {
      T_assert_eq((BigInt(a) | BigInt(b)), (a | b));
      T_assert_eq((BigInt(a) & BigInt(b)), (a & b));
      T_assert_eq((BigInt(a) ^ BigInt(b)), (a ^ b));
    }

    T_assert_eq(~BigInt(a), ~a);
    T_assert_eq(~~BigInt(a), a);

    static_assert((-1 >> 1) == -1);
    for(int b = 0; b <= 16; ++b) {
      T_assert_eq((BigInt(a) << b), (a << b));
      T_assert_eq((BigInt(a) >> b), (a >> b));

      T_assert_eq((BigInt(a) << -b), (a >> b));
      T_assert_eq((BigInt(a) >> -b), (a << b));

      T_assert_eq((BigInt(a) << static_cast<unsigned>(b)), (a << b));
      T_assert_eq((BigInt(a) >> static_cast<unsigned>(b)), (a >> b));

      T_assert_eq((BigInt(a) << BigInt(b)), (a << b));
      T_assert_eq((BigInt(a) >> BigInt(b)), (a >> b));

      T_assert_eq((BigInt(a) << BigInt(-b)), (a >> b));
      T_assert_eq((BigInt(a) >> BigInt(-b)), (a << b));
    }
  }

  for(auto t = TEST_BIG; t--;) {
    int64_t a = static_cast<int64_t>(mt64());
    int64_t b = static_cast<int64_t>(mt64());
    T_assert_eq((BigInt(a) & BigInt(b)), (a & b));
    T_assert_eq((BigInt(a) | BigInt(b)), (a | b));
    T_assert_eq((BigInt(a) ^ BigInt(b)), (a ^ b));
    T_assert_eq(~BigInt(a), ~a);
  }
}
void testSingleBitOperation() {
  puts("======Test Single Bit Operation");

  for(int32_t a = -LIMIT; a <= LIMIT; ++a) {
    for(unsigned b = 0; b < 31; ++b) {
      T_assert_eq(BigInt(a).testBit(b), ((a >> b) & 1));
      T_assert_eq(BigInt(a).setBit(b), (a | (1 << b)));
      T_assert_eq(BigInt(a).resetBit(b), (a & ~(1 << b)));
      T_assert_eq(BigInt(a).comBit(b), (a ^ (1 << b)));
      T_assert_eq(BigInt(a).testBit(BigInt(b)), ((a >> b) & 1));
      T_assert_eq(BigInt(a).setBit(BigInt(b)), (a | (1 << b)));
      T_assert_eq(BigInt(a).resetBit(BigInt(b)), (a & ~(1 << b)));
      T_assert_eq(BigInt(a).comBit(BigInt(b)), (a ^ (1 << b)));
    }
  }
}
void testAsInt() {
  puts("======Test AsInt");

  static constexpr auto INT_BITS = sizeof(int) * CHAR_BIT;
  for(int i = -LIMIT; i <= LIMIT; ++i) {
    T_assert_eq(BigInt(i).asUint(0), 0);
    T_assert_eq(BigInt(i).asUint(0_bi), 0);
    for(unsigned b = 1; b < INT_BITS - 1; ++b) {
      T_assert_eq(BigInt(i).asUint(b), (static_cast<unsigned>(i) << (INT_BITS - b) >> (INT_BITS - b)));
      T_assert_eq(BigInt(i).asInt(b), ((i) << (INT_BITS - b) >> (INT_BITS - b)));
      T_assert_eq(
        BigInt(i).asUint(static_cast<ulbn_bits_t>(b)), (static_cast<unsigned>(i) << (INT_BITS - b) >> (INT_BITS - b))
      );
      T_assert_eq(BigInt(i).asInt(static_cast<ulbn_bits_t>(b)), ((i) << (INT_BITS - b) >> (INT_BITS - b)));
      T_assert_eq(BigInt(i).asUint(BigInt(b)), (static_cast<unsigned>(i) << (INT_BITS - b) >> (INT_BITS - b)));
      T_assert_eq(BigInt(i).asInt(BigInt(b)), ((i) << (INT_BITS - b) >> (INT_BITS - b)));
    }
    T_assert_eq(BigInt(i).asUint(0), 0);
    T_assert_eq(BigInt(i).asInt(0), 0);
    T_assert_eq(BigInt(i).asUint(0_bi), 0);
    T_assert_eq(BigInt(i).asInt(0_bi), 0);
  }
}
void testBitCountInfo() {
  puts("======Test Bit Count Info");

  T_assert_eq(BigInt(0).ctz(), 0);
  T_assert_eq(BigInt(0).absBitWidth(), 0);

  for(unsigned i = 1; i <= 1024u; ++i) {
    T_assert_eq(BigInt(i).ctz(), static_cast<unsigned>(std::countr_zero(i)));
    T_assert_eq(BigInt(i).absBitWidth(), sizeof(unsigned) * CHAR_BIT - static_cast<unsigned>(std::countl_zero(i)));
  }
  for(unsigned i = 0; i <= 1024u; ++i) {
    T_assert_eq(BigInt(i).is2Pow(), ((i & (i - 1u)) == 0));
    T_assert_eq(BigInt(i).cto(), static_cast<unsigned>(std::countr_one(i)));
    T_assert_eq(BigInt(i).absPopcount(), static_cast<unsigned>(std::popcount(i)));
  }
}
void test() {
  testBitwiseOperation();
  testSingleBitOperation();
  testAsInt();
  testBitCountInfo();
}

int main() {
  testIt(test);
}
