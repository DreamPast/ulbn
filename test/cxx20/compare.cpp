#include "test.hpp"

void test() {
  T_assert((12_bi <=> BigInt("12345678901234567890")) < 0);
  T_assert(12_bi != BigInt("12345678901234567890"));
  T_assert((12_bi <=> -BigInt("12345678901234567890")) > 0);
  T_assert(12_bi != -BigInt("12345678901234567890"));
  T_assert((-12_bi <=> BigInt("12345678901234567890")) < 0);
  T_assert(-12_bi != BigInt("12345678901234567890"));
  T_assert((-12_bi <=> -BigInt("12345678901234567890")) > 0);
  T_assert(-12_bi != -BigInt("12345678901234567890"));

  T_assert((BigInt("12345678901234567890") <=> static_cast<uint8_t>(12u)) > 0);
  T_assert((-BigInt("12345678901234567890") <=> static_cast<uint8_t>(12u)) < 0);
  T_assert(BigInt("12345678901234567890") != static_cast<uint8_t>(12u));
  T_assert(-BigInt("12345678901234567890") != static_cast<uint8_t>(12u));

  T_assert((BigInt("12345678901234567890") <=> static_cast<int8_t>(12)) > 0);
  T_assert((-BigInt("12345678901234567890") <=> static_cast<int8_t>(12)) < 0);
  T_assert((BigInt("12345678901234567890") <=> static_cast<int8_t>(-12)) > 0);
  T_assert((-BigInt("12345678901234567890") <=> static_cast<int8_t>(-12)) < 0);
  T_assert(BigInt("12345678901234567890") != static_cast<int8_t>(12));
  T_assert(-BigInt("12345678901234567890") != static_cast<int8_t>(12));
  T_assert(BigInt("12345678901234567890") != static_cast<int8_t>(-12));
  T_assert(-BigInt("12345678901234567890") != static_cast<int8_t>(-12));


  for(auto a = -LIMIT; a <= LIMIT; ++a) {
    T_assert(BigInt(a).isZero() == (a == 0));
    T_assert(BigInt(a).sign() == (a == 0 ? 0 : (a > 0 ? 1 : -1)));
    T_assert(BigInt(a).isEven() == (a % 2 == 0));
    T_assert(BigInt(a).isOdd() == (a % 2 != 0));
    T_assert(-BigInt(a) == -a);
    T_assert(BigInt(a).abs() == std::abs(a));

    for(auto b = -LIMIT; b <= LIMIT; ++b) {
      T_assert((BigInt(a) < BigInt(b)) == (a < b));
      T_assert((BigInt(a) <= BigInt(b)) == (a <= b));
      T_assert((BigInt(a) > BigInt(b)) == (a > b));
      T_assert((BigInt(a) >= BigInt(b)) == (a >= b));
      T_assert((BigInt(a) == BigInt(b)) == (a == b));
      T_assert((BigInt(a) != BigInt(b)) == (a != b));

      if(fitType<int8_t>(b)) {
        T_assert((BigInt(a) < static_cast<int8_t>(b)) == (a < b));
        T_assert((BigInt(a) <= static_cast<int8_t>(b)) == (a <= b));
        T_assert((BigInt(a) > static_cast<int8_t>(b)) == (a > b));
        T_assert((BigInt(a) >= static_cast<int8_t>(b)) == (a >= b));
        T_assert((BigInt(a) == static_cast<int8_t>(b)) == (a == b));
        T_assert((BigInt(a) != static_cast<int8_t>(b)) == (a != b));
      }

      if(fitType<int8_t>(a)) {
        T_assert((static_cast<int8_t>(a) < BigInt(b)) == (a < b));
        T_assert((static_cast<int8_t>(a) <= BigInt(b)) == (a <= b));
        T_assert((static_cast<int8_t>(a) > BigInt(b)) == (a > b));
        T_assert((static_cast<int8_t>(a) >= BigInt(b)) == (a >= b));
        T_assert((static_cast<int8_t>(a) == BigInt(b)) == (a == b));
        T_assert((static_cast<int8_t>(a) != BigInt(b)) == (a != b));
      }

      if(fitType<uint8_t>(b)) {
        T_assert((BigInt(a) < static_cast<uint8_t>(b)) == (a < b));
        T_assert((BigInt(a) <= static_cast<uint8_t>(b)) == (a <= b));
        T_assert((BigInt(a) > static_cast<uint8_t>(b)) == (a > b));
        T_assert((BigInt(a) >= static_cast<uint8_t>(b)) == (a >= b));
        T_assert((BigInt(a) == static_cast<uint8_t>(b)) == (a == b));
        T_assert((BigInt(a) != static_cast<uint8_t>(b)) == (a != b));
      }

      if(fitType<uint8_t>(a)) {
        T_assert((static_cast<uint8_t>(a) < BigInt(b)) == (a < b));
        T_assert((static_cast<uint8_t>(a) <= BigInt(b)) == (a <= b));
        T_assert((static_cast<uint8_t>(a) > BigInt(b)) == (a > b));
        T_assert((static_cast<uint8_t>(a) >= BigInt(b)) == (a >= b));
        T_assert((static_cast<uint8_t>(a) == BigInt(b)) == (a == b));
        T_assert((static_cast<uint8_t>(a) != BigInt(b)) == (a != b));
      }

      if(fitType<ulbn_slong_t>(b)) {
        T_assert((BigInt(a) < static_cast<ulbn_slong_t>(b)) == (a < b));
        T_assert((BigInt(a) <= static_cast<ulbn_slong_t>(b)) == (a <= b));
        T_assert((BigInt(a) > static_cast<ulbn_slong_t>(b)) == (a > b));
        T_assert((BigInt(a) >= static_cast<ulbn_slong_t>(b)) == (a >= b));
        T_assert((BigInt(a) == static_cast<ulbn_slong_t>(b)) == (a == b));
        T_assert((BigInt(a) != static_cast<ulbn_slong_t>(b)) == (a != b));
      }

      if(fitType<ulbn_slong_t>(a)) {
        T_assert((static_cast<ulbn_slong_t>(a) < BigInt(b)) == (a < b));
        T_assert((static_cast<ulbn_slong_t>(a) <= BigInt(b)) == (a <= b));
        T_assert((static_cast<ulbn_slong_t>(a) > BigInt(b)) == (a > b));
        T_assert((static_cast<ulbn_slong_t>(a) >= BigInt(b)) == (a >= b));
        T_assert((static_cast<ulbn_slong_t>(a) == BigInt(b)) == (a == b));
        T_assert((static_cast<ulbn_slong_t>(a) != BigInt(b)) == (a != b));
      }

      if(fitType<ulbn_ulong_t>(b)) {
        T_assert((BigInt(a) < static_cast<ulbn_ulong_t>(b)) == (a < b));
        T_assert((BigInt(a) <= static_cast<ulbn_ulong_t>(b)) == (a <= b));
        T_assert((BigInt(a) > static_cast<ulbn_ulong_t>(b)) == (a > b));
        T_assert((BigInt(a) >= static_cast<ulbn_ulong_t>(b)) == (a >= b));
        T_assert((BigInt(a) == static_cast<ulbn_ulong_t>(b)) == (a == b));
        T_assert((BigInt(a) != static_cast<ulbn_ulong_t>(b)) == (a != b));
      }

      if(fitType<ulbn_ulong_t>(a)) {
        T_assert((static_cast<ulbn_ulong_t>(a) < BigInt(b)) == (a < b));
        T_assert((static_cast<ulbn_ulong_t>(a) <= BigInt(b)) == (a <= b));
        T_assert((static_cast<ulbn_ulong_t>(a) > BigInt(b)) == (a > b));
        T_assert((static_cast<ulbn_ulong_t>(a) >= BigInt(b)) == (a >= b));
        T_assert((static_cast<ulbn_ulong_t>(a) == BigInt(b)) == (a == b));
        T_assert((static_cast<ulbn_ulong_t>(a) != BigInt(b)) == (a != b));
      }
    }
  }
}

int main() {
  testIt(test);
  return 0;
}
