#include "test.hpp"
#include <iomanip>
#include <sstream>

void testBigString() {
  puts("======Test Big String");

  const BigInt bits = "0xFFFF";
  for(auto t = TEST_SMALL; t--;) {
    BigInt x = BigInt::fromRandom(bits).asInt(bits);
    auto str = x.toString();
    T_assert_eq(BigInt(str), x);

    auto ins_num = mt64() % 10;
    if(x.sign() < 0)
      while(ins_num-- != 0) {
        auto pos = mt64() % str.size() + 1;
        str.insert(pos, 1, '_');
      }
    else
      while(ins_num-- != 0) {
        auto pos = mt64() % (str.size() + 1);
        str.insert(pos, 1, '_');
      }
    T_assert_eq(BigInt::fromString(str, 0, ~0), x);
  }
}

void testValue() {
  puts("======Test Value");

  T_assert_eq(BigInt(0.0).toDouble(), 0.0);
  T_assert_eq(BigInt(-0.0).toDouble(), 0.0);
  T_assert_eq(BigInt(1.0).toDouble(), 1.0);
  T_assert_eq(BigInt(-1.0).toDouble(), -1.0);
  T_assert_eq(BigInt(ldexp(1.0, 52) + 0.5).toDouble(), ldexp(1.0, 52));

  T_assert_eq(BigInt(0.0F).toFloat(), 0.0F);
  T_assert_eq(BigInt(-0.0F).toFloat(), 0.0F);
  T_assert_eq(BigInt(1.0F).toFloat(), 1.0F);
  T_assert_eq(BigInt(-1.0F).toFloat(), -1.0F);
  T_assert_eq(BigInt(ldexpf(1.0F, 23) + 0.5F).toFloat(), ldexpf(1.0F, 23));

  T_assert_eq(BigInt(0.0).toLongDouble(), 0.0L);
  T_assert_eq(BigInt(-0.0).toLongDouble(), 0.0L);
  T_assert_eq(BigInt(1.0).toLongDouble(), 1.0L);
  T_assert_eq(BigInt(-1.0).toLongDouble(), -1.0L);


  for(ulbn_slong_t i = -LIMIT; i <= LIMIT; ++i) {
    T_assert_eq(BigInt(i).toSlong(), i);
    T_assert_eq(BigInt(i).toUlong(), static_cast<ulbn_ulong_t>(i));
    T_assert_eq(BigInt(i).toLimb(), static_cast<ulbn_limb_t>(static_cast<ulbn_ulong_t>(i)));
    T_assert_eq(BigInt(i).toSlimb(), static_cast<ulbn_slimb_t>(i));

    T_assert_eq(BigInt(i).fitUlong(), fitType<ulbn_ulong_t>(i));
    T_assert_eq(BigInt(i).fitSlong(), fitType<ulbn_slong_t>(i));
    T_assert_eq(BigInt(i).fitLimb(), fitType<ulbn_limb_t>(i));
    T_assert_eq(BigInt(i).fitSlimb(), fitType<ulbn_slimb_t>(i));
  }


  for(ulbn_slong_t i = -LIMIT; i <= LIMIT; ++i) {
    float fd = BigInt(i).toFloat();
    T_assert_eq(fd, static_cast<float>(i));
    T_assert_eq(BigInt(i).fitFloat(), (std::truncf(fd) == fd));
    if(i >= 0)
      T_assert_eq(BigInt(static_cast<float>(i) + 0.5F).toFloat(), static_cast<float>(i));
    else
      T_assert_eq(BigInt(static_cast<float>(i) - 0.5F).toFloat(), static_cast<float>(i));

    double d = BigInt(i).toDouble();
    T_assert_eq(d, static_cast<double>(i));
    T_assert_eq(BigInt(i).fitDouble(), (std::trunc(d) == d));
    if(i >= 0)
      T_assert_eq(BigInt(static_cast<double>(i) + 0.5).toDouble(), static_cast<double>(i));
    else
      T_assert_eq(BigInt(static_cast<double>(i) - 0.5).toDouble(), static_cast<double>(i));

    long double ld = BigInt(i).toLongDouble();
    T_assert_eq(ld, static_cast<long double>(i));
    T_assert_eq(BigInt(i).fitLongDouble(), (std::truncl(ld) == ld));
    if(i >= 0)
      T_assert_eq(BigInt(static_cast<long double>(i) + 0.5L).toLongDouble(), static_cast<long double>(i));
    else
      T_assert_eq(BigInt(static_cast<long double>(i) - 0.5L).toLongDouble(), static_cast<long double>(i));
  }
}

void testChar() {
  puts("======Test Char");

  T_assert_eq(BigInt("0").toString(), "0");
  T_assert_eq(BigInt("12").toString(), "12");
  T_assert_eq(BigInt("-12").toString(), "-12");
  T_assert_eq(BigInt("12345678901234567890").toString(), "12345678901234567890");
  T_assert_eq(BigInt("012").toString(8), "12");
  T_assert_eq(BigInt("0x12").toString(16), "12");

  T_assert_exception([] { (12_bi).toString(0); }, ULBN_ERR_BAD_ARGUMENT);

  for(auto i = -LIMIT; i <= LIMIT; ++i) {
    T_assert_eq(BigInt(i).toString(), std::to_string(i));
  }

#if defined(__cpp_lib_format) && __cpp_lib_format >= 201907L
  T_assert_eq(std::format("{}", BigInt("0")), "0");
  T_assert_eq(std::format("{}", BigInt("12")), "12");
  T_assert_eq(std::format("{}", BigInt("-12")), "-12");
  T_assert_eq(std::format("{}", BigInt("12345678901234567890")), "12345678901234567890");

  for(auto i = -LIMIT; i <= LIMIT; ++i) {
    T_assert_eq(std::format("{}", BigInt(i)), std::to_string(i));
  }
#endif


  BigInt("12345678901234567890").print(std::cout);
  std::cout << '\n';
  BigInt("-12345678901234567890").print(std::cout);
  std::cout << '\n';
  T_assert_exception([] { BigInt("12345678901234567890").print(stdout, 0); }, ULBN_ERR_BAD_ARGUMENT);


  for(auto base: { 8, 10, 16 })
    for(auto uppercase: { false, true })
      for(auto showbase: { false, true })
        for(auto sign: { -1, 0, 1 }) {
          BigInt obj("12345678901234567890");
          if(sign == -1)
            obj.negLoc();
          else if(sign == 0)
            obj = 0;
          std::ostringstream osst;

          if(base == 8)
            osst << std::oct;
          else if(base == 10)
            osst << std::dec;
          else if(base == 16)
            osst << std::hex;
          osst << (uppercase ? std::uppercase : std::nouppercase);
          osst << (showbase ? std::showbase : std::noshowbase);
          osst << obj;

          T_assert_eq(obj, BigInt::fromString(osst.str(), showbase ? 0 : base));
        }


#if defined(__cpp_lib_format) && __cpp_lib_format >= 201907L
  for(auto sign: { -1, 0, 1 }) {
    BigInt obj = "12345678901234567890";
    if(sign == -1)
      obj.negLoc();
    else if(sign == 0)
      obj = 0;

    T_assert_eq(BigInt::fromString(std::format("{:d}", obj), 10), obj);
    T_assert_eq(BigInt::fromString(std::format("{:x}", obj), 16), obj);
    T_assert_eq(BigInt::fromString(std::format("{:X}", obj), 16), obj);
    T_assert_eq(BigInt::fromString(std::format("{:b}", obj), 2), obj);
    T_assert_eq(BigInt::fromString(std::format("{:B}", obj), 2), obj);
    T_assert_eq(BigInt::fromString(std::format("{:o}", obj), 8), obj);
    T_assert_eq(BigInt::fromString(std::format("{:}", obj), 10), obj);

    T_assert_eq(BigInt::fromString(std::format("{:#d}", obj)), obj);
    T_assert_eq(BigInt::fromString(std::format("{:#x}", obj)), obj);
    T_assert_eq(BigInt::fromString(std::format("{:#X}", obj)), obj);
    T_assert_eq(BigInt::fromString(std::format("{:#b}", obj)), obj);
    T_assert_eq(BigInt::fromString(std::format("{:#B}", obj)), obj);
    T_assert_eq(BigInt::fromString(std::format("{:#o}", obj)), obj);
    T_assert_eq(BigInt::fromString(std::format("{:#}", obj)), obj);
  }
#endif


  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt::fromRandom(1024).asInt(1024);
    auto str = x.toString();
    T_assert_eq(str, BigInt(str));
  }


  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt(10).pow(BigInt::fromRandom(12));
    auto str = x.toString();
    T_assert_eq(str, BigInt(str));
  }
}
void testWchar() {
  puts("======Test Wchar");

  T_assert(BigInt(L"0").toString<wchar_t>() == L"0");
  T_assert(BigInt(L"12").toString<wchar_t>() == L"12");
  T_assert(BigInt(L"-12").toString<wchar_t>() == L"-12");
  T_assert(BigInt(L"12345678901234567890").toString<wchar_t>() == L"12345678901234567890");
  T_assert(BigInt(L"012").toString<wchar_t>(8) == L"12");
  T_assert(BigInt(L"0x12").toString<wchar_t>(16) == L"12");

  T_assert_exception([] { (12_bi).toString<wchar_t>(0); }, ULBN_ERR_BAD_ARGUMENT);

  for(auto i = -LIMIT; i <= LIMIT; ++i) {
    T_assert(BigInt(i).toString<wchar_t>() == std::to_wstring(i));
  }

#if defined(__cpp_lib_format) && __cpp_lib_format >= 201907L
  T_assert(std::format(L"{}", BigInt(L"0")) == L"0");
  T_assert(std::format(L"{}", BigInt(L"12")) == L"12");
  T_assert(std::format(L"{}", BigInt(L"-12")) == L"-12");
  T_assert(std::format(L"{}", BigInt(L"12345678901234567890")) == L"12345678901234567890");

  for(auto i = -LIMIT; i <= LIMIT; ++i) {
    T_assert(std::format(L"{}", BigInt(i)) == std::to_wstring(i));
  }
#endif


  BigInt(L"12345678901234567890").print(std::wcout);
  std::wcout << '\n';
  BigInt(L"-12345678901234567890").print(std::wcout);
  std::wcout << '\n';


  for(auto base: { 8, 10, 16 })
    for(auto uppercase: { false, true })
      for(auto showbase: { false, true })
        for(auto sign: { -1, 0, 1 }) {
          BigInt obj(L"12345678901234567890");
          if(sign == -1)
            obj.negLoc();
          else if(sign == 0)
            obj = 0;
          std::wostringstream osst;

          if(base == 8)
            osst << std::oct;
          else if(base == 10)
            osst << std::dec;
          else if(base == 16)
            osst << std::hex;
          osst << (uppercase ? std::uppercase : std::nouppercase);
          osst << (showbase ? std::showbase : std::noshowbase);
          osst << obj;

          T_assert(obj == BigInt::fromString(osst.str(), showbase ? 0 : base));
        }


#if defined(__cpp_lib_format) && __cpp_lib_format >= 201907L
  for(auto sign: { -1, 0, 1 }) {
    BigInt obj = L"12345678901234567890";
    if(sign == -1)
      obj.negLoc();
    else if(sign == 0)
      obj = 0;

    T_assert(BigInt::fromString(std::format(L"{:d}", obj), 10) == obj);
    T_assert(BigInt::fromString(std::format(L"{:x}", obj), 16) == obj);
    T_assert(BigInt::fromString(std::format(L"{:X}", obj), 16) == obj);
    T_assert(BigInt::fromString(std::format(L"{:b}", obj), 2) == obj);
    T_assert(BigInt::fromString(std::format(L"{:B}", obj), 2) == obj);
    T_assert(BigInt::fromString(std::format(L"{:o}", obj), 8) == obj);
    T_assert(BigInt::fromString(std::format(L"{:}", obj), 10) == obj);

    T_assert(BigInt::fromString(std::format(L"{:#d}", obj)) == obj);
    T_assert(BigInt::fromString(std::format(L"{:#x}", obj)) == obj);
    T_assert(BigInt::fromString(std::format(L"{:#X}", obj)) == obj);
    T_assert(BigInt::fromString(std::format(L"{:#b}", obj)) == obj);
    T_assert(BigInt::fromString(std::format(L"{:#B}", obj)) == obj);
    T_assert(BigInt::fromString(std::format(L"{:#o}", obj)) == obj);
    T_assert(BigInt::fromString(std::format(L"{:#}", obj)) == obj);
  }
#endif


  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt::fromRandom(1024).asInt(1024);
    auto str = x.toString<wchar_t>();
    T_assert(str == BigInt(str));
  }


  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt(10).pow(BigInt::fromRandom(12));
    auto str = x.toString<wchar_t>();
    T_assert(str == BigInt(str));
  }
}
void testChar16() {
  puts("======Test char16_t");

  T_assert(BigInt(u"0").toString<char16_t>() == u"0");
  T_assert(BigInt(u"12").toString<char16_t>() == u"12");
  T_assert(BigInt(u"-12").toString<char16_t>() == u"-12");
  T_assert(BigInt(u"12345678901234567890").toString<char16_t>() == u"12345678901234567890");
  T_assert(BigInt(u"012").toString<char16_t>(8) == u"12");
  T_assert(BigInt(u"0x12").toString<char16_t>(16) == u"12");

  T_assert_exception([] { (12_bi).toString<char16_t>(0); }, ULBN_ERR_BAD_ARGUMENT);


  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt::fromRandom(1024).asInt(1024);
    auto str = x.toString<char16_t>();
    T_assert(str == BigInt(str));
  }


  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt(10).pow(BigInt::fromRandom(12));
    auto str = x.toString<char16_t>();
    T_assert(str == BigInt(str));
  }
}
void testChar32() {
  puts("======Test char32_t");

  T_assert(BigInt(U"0").toString<char32_t>() == U"0");
  T_assert(BigInt(U"12").toString<char32_t>() == U"12");
  T_assert(BigInt(U"-12").toString<char32_t>() == U"-12");
  T_assert(BigInt(U"12345678901234567890").toString<char32_t>() == U"12345678901234567890");
  T_assert(BigInt(U"012").toString<char32_t>(8) == U"12");
  T_assert(BigInt(U"0x12").toString<char32_t>(16) == U"12");

  T_assert_exception([] { (12_bi).toString<char32_t>(0); }, ULBN_ERR_BAD_ARGUMENT);


  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt::fromRandom(1024).asInt(1024);
    auto str = x.toString<char32_t>();
    T_assert(str == BigInt(str));
  }


  for(int t = TEST_SMALL; t--;) {
    BigInt x = BigInt(10).pow(BigInt::fromRandom(12));
    auto str = x.toString<char32_t>();
    T_assert(str == BigInt(str));
  }
}

void test() {
  testValue();
  testChar();
  testWchar();
  testChar16();
  testChar32();
  testBigString();
}

int main() {
  testIt(test);
  return 0;
}
