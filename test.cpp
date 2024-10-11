#define ULBN_CONF_CHECK_BITS_OVERFLOW 0
#include <iostream>
#include <cmath>
#include <cfloat>
#include <cstdint>
#include <limits>
#include <bit>

#include "ulbn.hpp"
using ul::bn::BigInt;
using ul::bn::operator""_bi;

void _T_assert(const char* msg, const char* file, int line) {
  std::cerr << "Assertion failed: " << msg << " at " << file << ":" << line << std::endl;
  throw "Assertion failed";
}
#define T_assert(cond) ((void)(!!(cond) || (_T_assert(#cond, __FILE__, __LINE__), 0)))

template<class To, class From>
bool fitType(From from) {
  return static_cast<To>(from) == from;
}

void testException() {
  puts("===Test Exception");

  T_assert(ul::bn::Exception(ULBN_ERR_NOMEM) == ULBN_ERR_NOMEM);
  T_assert(ul::bn::Exception(ULBN_ERR_EXCEED_RANGE) == ULBN_ERR_EXCEED_RANGE);
  T_assert(ul::bn::Exception(ULBN_ERR_SUCCESS) == ULBN_ERR_SUCCESS);
  T_assert(ul::bn::Exception(ULBN_ERR_DIV_BY_ZERO) == ULBN_ERR_DIV_BY_ZERO);
  T_assert(ul::bn::Exception(ULBN_ERR_INEXACT) == ULBN_ERR_INEXACT);
  T_assert(ul::bn::Exception(ULBN_ERR_INVALID) == ULBN_ERR_INVALID);
  T_assert(ul::bn::Exception(ULBN_ERR_OVERFLOW) == ULBN_ERR_OVERFLOW);
  T_assert(ul::bn::Exception(ULBN_ERR_UNDERFLOW) == ULBN_ERR_UNDERFLOW);
}

void testCastFrom() {
  puts("===Test Cast From");

  T_assert(BigInt("0x12") == 0x12);
  T_assert(BigInt("+0x12") == +0x12);
  T_assert(BigInt("-0x12") == -0x12);

  T_assert(BigInt("0x1Ab") == 0x1Ab);
  T_assert(BigInt("+0x1Ab") == +0x1Ab);
  T_assert(BigInt("-0x1Ab") == -0x1Ab);

  T_assert(BigInt("012") == 012);
  T_assert(BigInt("+012") == +012);
  T_assert(BigInt("-012") == -012);

  T_assert(BigInt("0o12") == 012);
  T_assert(BigInt("+0o12") == +012);
  T_assert(BigInt("-0o12") == -012);

  T_assert(BigInt("0b1101") == 13);
  T_assert(BigInt("+0b1101") == +13);
  T_assert(BigInt("-0b1101") == -13);


  T_assert(BigInt(static_cast<ulbn_limb_t>(0)) == 0u);
  T_assert(BigInt(static_cast<ulbn_limb_t>(12)) == 12u);


  T_assert(BigInt(INFINITY) == 0);
  T_assert(BigInt(-INFINITY) == 0);
  T_assert(BigInt(nan("")) == 0);

  T_assert(BigInt(+0.0) == 0);
  T_assert(BigInt(-0.0) == 0);

  T_assert(BigInt(1.0) == 1);
  T_assert(BigInt(0.5) == 0);
  T_assert(BigInt(-1.0) == -1);
  T_assert(BigInt(-0.5) == 0);
  T_assert(BigInt(ldexp(1.0, 51) + 0.5) == BigInt::from_2exp(51));
  T_assert(BigInt(ldexp(1.0, 52) + 0.5) == BigInt::from_2exp(52));
}

void testCastTo() {
  puts("===Test Cast To");

  T_assert(BigInt("0").toString() == "0");
  T_assert(BigInt("12").toString() == "12");
  T_assert(BigInt("-12").toString() == "-12");
  T_assert(BigInt("12345678901234567890").toString() == "12345678901234567890");
  T_assert(BigInt("012").toString(8) == "12");
  T_assert(BigInt("0x12").toString(16) == "12");
  try {
    (12_bi).toString(0);
    throw ul::bn::Exception(0);
  } catch(ul::bn::Exception& e) {
    T_assert(e == ULBN_ERR_EXCEED_RANGE);
  }


  BigInt("12345678901234567890").print();
  fprintf(stdout, "\n");
  BigInt("-12345678901234567890").print();
  fprintf(stdout, "\n");
  try {
    BigInt("-12345678901234567890").print(stdout, 0);
    throw ul::bn::Exception(0);
  } catch(ul::bn::Exception& e) {
    T_assert(ULBN_ERR_EXCEED_RANGE == e);
  }


  T_assert(BigInt(0.0).toDouble() == 0.0);
  T_assert(BigInt(-0.0).toDouble() == 0.0);
  T_assert(BigInt(1.0).toDouble() == 1.0);
  T_assert(BigInt(-1.0).toDouble() == -1.0);
  T_assert(BigInt(ldexp(1.0, 52) + 0.5).toDouble() == ldexp(1.0, 52));

  for(ulbn_slong_t i = -256 * 3; i <= 256 * 3; ++i) {
    T_assert(BigInt(i).toSlong() == i);
    T_assert(BigInt(i).toUlong() == static_cast<ulbn_ulong_t>(i));
    T_assert(BigInt(i).toLimb() == static_cast<ulbn_limb_t>(static_cast<ulbn_ulong_t>(i)));
    T_assert(BigInt(i).toDouble() == static_cast<double>(i));
  }
}

void testCompare() {
  puts("===Test Compare");

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


  for(int a = -256; a <= 256; ++a) {
    T_assert(BigInt(a).is_zero() == (a == 0));
    T_assert(BigInt(a).sign() == (a == 0 ? 0 : (a > 0 ? 1 : -1)));
    T_assert(BigInt(a).is_even() == (a % 2 == 0));
    T_assert(BigInt(a).is_odd() == (a % 2 != 0));

    for(int b = -256; b <= 256; ++b) {
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
    }
  }
}


void subtestAddSub() {
  puts("======Subtest AddSub");

  for(int a = -256; a <= 256; ++a)
    for(int b = -256; b <= 256; ++b) {
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
void subtestMul() {
  puts("======Subtest Mul");

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


  for(int64_t a = -256; a <= 256; ++a)
    for(int64_t b = -256; b <= 256; ++b) {
      T_assert(BigInt(a) * BigInt(b) == a * b);
      if(fitType<int8_t>(b))
        T_assert(BigInt(a) * static_cast<int8_t>(b) == a * b);
      if(fitType<uint8_t>(b))
        T_assert(BigInt(a) * static_cast<uint8_t>(b) == a * b);
    }
}
void subtestDivMod() {
  puts("======Subtest DivMod");

  BigInt a2 = BigInt("12345678901234567890");

  T_assert(a2 / 12_bi == "1028806575102880657"_bi && a2 % 12_bi == 6);
  T_assert(a2 / 12u == "1028806575102880657"_bi && a2 % 12u == 6);
  T_assert(a2 / 12 == "1028806575102880657"_bi && a2 % 12 == 6);

  for(unsigned i = 64; i < 256; ++i) {
    BigInt d = BigInt::from_2exp(i);
    T_assert((a2 / d) * d + (a2 % d) == a2);
    T_assert((a2 * d) / d == a2 && (a2 * d) % d == 0);
  }


  for(int a = -256; a <= 256; ++a)
    for(int b = -256; b <= 256; ++b)
      if(b != 0) {
        T_assert(BigInt(a) / BigInt(b) == a / b);
        T_assert(BigInt(a) % BigInt(b) == a % b);
        if(fitType<int8_t>(b)) {
          T_assert(BigInt(a) / static_cast<int8_t>(b) == a / b);

          ulbn_slimb_t r;
          T_assert(ulbi_mod_slimb(ul::bn::getCurrentContext(), &r, BigInt(a).get(), static_cast<ulbn_slimb_t>(b)) >= 0);
          T_assert(r == a % b);
        }
        if(fitType<uint8_t>(b)) {
          T_assert(BigInt(a) / static_cast<uint8_t>(b) == a / b);
          {
            BigInt tmp(a);
            ulbn_limb_t r;
            T_assert(ulbi_mod_limb(ul::bn::getCurrentContext(), &r, tmp.get(), static_cast<ulbn_limb_t>(b)) >= 0);
            T_assert(static_cast<int>(r) == (a % b + b) % b);
          }
        }
      }
}
void testArithmeticOperation() {
  puts("===Test Arithmetic Operation");

  subtestAddSub();
  subtestMul();
  subtestDivMod();
}


void subtestBitwiseOperation() {
  puts("======Subtest Bitwise Operation");

  for(int a = -256; a <= 256; ++a) {
    T_assert((BigInt(a) & BigInt(a)) == a);
    T_assert((BigInt(a) | BigInt(a)) == a);
    T_assert((BigInt(a) ^ BigInt(a)) == 0);
    for(int b = -256; b <= 256; ++b) {
      T_assert((BigInt(a) | BigInt(b)) == (a | b));
      T_assert((BigInt(a) & BigInt(b)) == (a & b));
      T_assert((BigInt(a) ^ BigInt(b)) == (a ^ b));
    }

    T_assert(~BigInt(a) == ~a);
    T_assert(~~BigInt(a) == a);

    static_assert((-1 >> 1) == -1);
    for(int b = 0; b <= 16; ++b) {
      T_assert((BigInt(a) << b) == (a << b));
      T_assert((BigInt(a) >> b) == (a >> b));

      T_assert((BigInt(a) << -b) == (a >> b));
      T_assert((BigInt(a) >> -b) == (a << b));
    }
  }
}
void subtestSingleBitOperation() {
  puts("======Subtest Single Bit Operation");

  for(int a = -256; a <= 256; ++a) {
    for(int b = 0; b < 31; ++b) {
      T_assert(BigInt(a).testBit(b) == ((a >> b) & 1));
      T_assert(BigInt(a).setBit(b) == (a | (1 << b)));
      T_assert(BigInt(a).resetBit(b) == (a & ~(1 << b)));
      T_assert(BigInt(a).comBit(b) == (a ^ (1 << b)));
    }
  }
}
void subtestAsInt() {
  puts("======Subtest AsInt");

  static constexpr auto INT_BITS = sizeof(int) * CHAR_BIT;
  for(int i = -256 * 3; i <= 256 * 3; ++i) {
    T_assert(BigInt(i).asUint(0) == 0);
    for(int b = 1; b < INT_BITS - 1; ++b) {
      T_assert(BigInt(i).asUint(b) == (static_cast<unsigned>(i) << (INT_BITS - b) >> (INT_BITS - b)));
      T_assert(BigInt(i).asInt(b) == ((i) << (INT_BITS - b) >> (INT_BITS - b)));
    }
    T_assert(BigInt(i).asUint(0) == 0);
    T_assert(BigInt(i).asInt(0) == 0);
  }
}
void subtestBitCountInfo() {
  puts("======Subtest Bit Count Info");

  T_assert(BigInt(0).absFloorLog2() == 0);

  for(unsigned i = 1; i <= 1024u; ++i) {
    T_assert(BigInt(i).ctz() == static_cast<unsigned>(std::countr_zero(i)));
    T_assert(BigInt(i).absFloorLog2() == sizeof(unsigned) * CHAR_BIT - std::countl_zero(i));
    T_assert(BigInt(i).is2Pow() == ((i & (i - 1u)) == 0));
  }
  for(unsigned i = 0; i <= 1024u; ++i) {
    T_assert(BigInt(i).cto() == static_cast<unsigned>(std::countr_one(i)));
    T_assert(BigInt(i).absPopcount() == static_cast<unsigned>(std::popcount(i)));
  }
}
void testBitOperation() {
  puts("===Test Bit Operation");

  subtestBitwiseOperation();
  subtestSingleBitOperation();
  subtestAsInt();
  subtestBitCountInfo();
}


void testOther() {
  puts("===Test Other");

  ulbn_ctx_t* ctx = ul::bn::getCurrentContext();

  {  // ulbi_divmod_limb: b = 0
    ulbn_limb_t r;
    BigInt q;
    T_assert(ulbi_divmod_limb(ctx, q.get(), &r, (0_bi).get(), 0) == ULBN_ERR_DIV_BY_ZERO);
    T_assert(q == 0 && r == 0);
  }

  {  // ulbi_divmod_slimb: b = 0
    ulbn_slimb_t r;
    BigInt q;
    T_assert(ulbi_divmod_slimb(ctx, q.get(), &r, (0_bi).get(), 0) == ULBN_ERR_DIV_BY_ZERO);
    T_assert(q == 0 && r == 0);
  }

  {  // ulbi_divmod: bn == 0
    BigInt q, r;
    T_assert(ulbi_divmod(ctx, q.get(), r.get(), (0_bi).get(), (0_bi).get()) == ULBN_ERR_DIV_BY_ZERO);
    T_assert(q == 0 && r == 0);
  }

  {  // ulbi_divmod: qo == ro
    BigInt r;
    T_assert(ulbi_divmod(ctx, r.get(), r.get(), (12_bi).get(), (12_bi).get()) == 0);
    T_assert(r == 0);
  }

  {  // ulbi_ctz, ulbi_cto, ulbi_abs_popcount, ulbi_abs_floor_log2: rh != nullptr
    BigInt x = 12_bi;
    ulbn_usize_t rh;

    ulbi_ctz(x.get(), &rh);
    T_assert(rh == 0);

    ulbi_cto(x.get(), &rh);
    T_assert(rh == 0);

    ulbi_abs_popcount(x.get(), &rh);
    T_assert(rh == 0);

    ulbi_abs_floor_log2(x.get(), &rh);
    T_assert(rh == 0);
  }
}


int main() {
  BigInt a("8070445940888263371");
  BigInt b("32135758879894");
  // std::cout << (a / b) << '\n';
  std::cout << (a % b) << '\n';
  return 0;

  testException();
  testCastFrom();
  testCastTo();
  testCompare();
  testArithmeticOperation();
  testBitOperation();
  testOther();
  return 0;
}

#undef ul_static_assert
#define ul_static_assert(cond, msg)
#include "ulbn.c"
