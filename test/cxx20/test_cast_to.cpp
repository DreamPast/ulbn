#include "test.hpp"

void testBigString() {
  puts("===Test Big String");

  const BigInt bits = "0xFFFF";
  for(auto t = TEST_SMALL; t--;) {
    BigInt x = BigInt::fromRandom(bits).asInt(bits);
    auto str = x.toString();
    T_assert(BigInt(str) == x);

    auto ins_num = mt64() % 10;
    while(ins_num-- != 0) {
      auto pos = mt64() % (str.size() + 1);
      str.insert(pos, 1, '_');
    }
    T_assert(BigInt::fromString(str, 0, ~0) == x);
  }
}
void test() {
  puts("---Some integers");
  T_assert(BigInt("0").toString() == "0");
  T_assert(BigInt("12").toString() == "12");
  T_assert(BigInt("-12").toString() == "-12");
  T_assert(BigInt("12345678901234567890").toString() == "12345678901234567890");
  T_assert(BigInt("012").toString(8) == "12");
  T_assert(BigInt("0x12").toString(16) == "12");

  T_assert_exception([] { (12_bi).toString(0); }, ULBN_ERR_EXCEED_RANGE);

  for(int i = -LIMIT; i <= LIMIT; ++i)
    T_assert(BigInt(i).toString() == std::to_string(i));


  puts("---Print");
  BigInt("12345678901234567890").print(std::cout);
  fprintf(stdout, "\n");
  BigInt("-12345678901234567890").print(std::cout);
  fprintf(stdout, "\n");
  T_assert_exception([] { BigInt("12345678901234567890").print(stdout, 0); }, ULBN_ERR_EXCEED_RANGE);

  puts("---Float, Double, Long double");
  T_assert(BigInt(0.0).toDouble() == 0.0);
  T_assert(BigInt(-0.0).toDouble() == 0.0);
  T_assert(BigInt(1.0).toDouble() == 1.0);
  T_assert(BigInt(-1.0).toDouble() == -1.0);
  T_assert(BigInt(ldexp(1.0, 52) + 0.5).toDouble() == ldexp(1.0, 52));

  T_assert(BigInt(0.0F).toFloat() == 0.0F);
  T_assert(BigInt(-0.0F).toFloat() == 0.0F);
  T_assert(BigInt(1.0F).toFloat() == 1.0F);
  T_assert(BigInt(-1.0F).toFloat() == -1.0F);
  T_assert(BigInt(ldexpf(1.0F, 23) + 0.5F).toFloat() == ldexpf(1.0F, 23));

  T_assert(BigInt(0.0).toLongDouble() == 0.0L);
  T_assert(BigInt(-0.0).toLongDouble() == 0.0L);
  T_assert(BigInt(1.0).toLongDouble() == 1.0L);
  T_assert(BigInt(-1.0).toLongDouble() == -1.0L);

  puts("---Fit/To slong/ulong/limb/slimb");
  for(ulbn_slong_t i = -LIMIT; i <= LIMIT; ++i) {
    T_assert(BigInt(i).toSlong() == i);
    T_assert(BigInt(i).toUlong() == static_cast<ulbn_ulong_t>(i));
    T_assert(BigInt(i).toLimb() == static_cast<ulbn_limb_t>(static_cast<ulbn_ulong_t>(i)));
    T_assert(BigInt(i).toSlimb() == static_cast<ulbn_slimb_t>(i));

    T_assert(BigInt(i).fitUlong() == fitType<ulbn_ulong_t>(i));
    T_assert(BigInt(i).fitSlong() == fitType<ulbn_slong_t>(i));
    T_assert(BigInt(i).fitLimb() == fitType<ulbn_limb_t>(i));
    T_assert(BigInt(i).fitSlimb() == fitType<ulbn_slimb_t>(i));
  }

  puts("---Fit/To float/double/longdouble");
  for(ulbn_slong_t i = -LIMIT; i <= LIMIT; ++i) {
    float fd = BigInt(i).toFloat();
    T_assert(fd == static_cast<float>(i));
    T_assert(BigInt(i).fitFloat() == (std::truncf(fd) == fd));
    if(i >= 0)
      T_assert(BigInt(static_cast<float>(i) + 0.5F).toFloat() == static_cast<float>(i));
    else
      T_assert(BigInt(static_cast<float>(i) - 0.5F).toFloat() == static_cast<float>(i));

    double d = BigInt(i).toDouble();
    T_assert(d == static_cast<double>(i));
    T_assert(BigInt(i).fitDouble() == (std::trunc(d) == d));
    if(i >= 0)
      T_assert(BigInt(static_cast<double>(i) + 0.5).toDouble() == static_cast<double>(i));
    else
      T_assert(BigInt(static_cast<double>(i) - 0.5).toDouble() == static_cast<double>(i));

    long double ld = BigInt(i).toLongDouble();
    T_assert(ld == static_cast<long double>(i));
    T_assert(BigInt(i).fitLongDouble() == (std::truncl(ld) == ld));
    if(i >= 0)
      T_assert(BigInt(static_cast<long double>(i) + 0.5L).toLongDouble() == static_cast<long double>(i));
    else
      T_assert(BigInt(static_cast<long double>(i) - 0.5L).toLongDouble() == static_cast<long double>(i));
  }

  puts("---Random");
  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt::fromRandom(1024).asInt(1024);
    auto str = x.toString();
    T_assert(str == BigInt(str));
  }

  puts("---Random (10pow)");
  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt(10).pow(BigInt::fromRandom(12));
    auto str = x.toString();
    T_assert(str == BigInt(str));
  }

  testBigString();
}

int main() {
  testIt(test);
  return 0;
}
