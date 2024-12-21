#include "test.hpp"

template<class ExpectValue>
void _checkSetString(
  const char* str, ExpectValue expect_value, ptrdiff_t expect_len = -1, int expect_error = 0, int flags = ~0
) {
  if(expect_len < 0)
    expect_len = static_cast<ptrdiff_t>(strlen(str)) - (expect_len + 1);
  const char* nstr = str;

  BigInt bi;
  T_assert(ulbi_set_string_ex(ulbn_default_alloc(), bi.get(), &nstr, SIZE_MAX, 0, flags) == expect_error);
  T_assert(bi == expect_value);
  T_assert(nstr - str == expect_len);

  std::string str2 = str;
  nstr = str2.c_str();
  str2.push_back('0');
  T_assert(ulbi_set_string_ex(ulbn_default_alloc(), bi.get(), &nstr, strlen(str), 0, flags) == expect_error);
  T_assert(bi == expect_value);
  T_assert(nstr - str2.c_str() == expect_len);

  nstr = str2.c_str();
  str2.push_back('1');
  T_assert(ulbi_set_string_ex(ulbn_default_alloc(), bi.get(), &nstr, strlen(str), 0, flags) == expect_error);
  T_assert(bi == expect_value);
  T_assert(nstr - str2.c_str() == expect_len);
}

void testSetString() {
  puts("===Test Set String");

  for(auto zero: { "0", "0.", "0.0", "0.00", "0.000" })
    for(auto sign: { "", "+", "-" })
      for(auto prefix: { "", "0x", "0o", "0b" }) {
        std::string str = std::string(sign) + prefix + zero;
        _checkSetString(str.c_str(), 0, -1, strcmp(sign, "-") == 0 ? ULBN_ERR_INEXACT : 0);
        _checkSetString(
          str.c_str(), 0, static_cast<ptrdiff_t>(strlen(prefix) + strlen(sign) + 1),
          strcmp(sign, "-") == 0 ? ULBN_ERR_INEXACT : 0, ~0 ^ ULBN_SET_STRING_ACCEPT_DECIMAL_PART
        );
      }

  _checkSetString("00", 0, 1);
  _checkSetString("000", 0, 1);
  _checkSetString("+00", 0, 2);
  _checkSetString("+000", 0, 2);
  _checkSetString("-00", 0, 2, ULBN_ERR_INEXACT);
  _checkSetString("-000", 0, 2, ULBN_ERR_INEXACT);

  {
    _checkSetString(".1e-10", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString(".1e-2", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString(".1e-1", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString(".1e0", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString(".1e1", 1);
    _checkSetString(".1e2", 10);
    _checkSetString(".1e3", 100);
    _checkSetString(".1e10", 1000000000);

    _checkSetString("0.1e-10", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1e-2", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1e-1", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1e0", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1e1", 1);
    _checkSetString("0.1e2", 10);
    _checkSetString("0.1e3", 100);
    _checkSetString("0.1e10", 1000000000);

    _checkSetString("0.12e-10", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.12e-1", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.12e0", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.12e1", 1, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.12e2", 12);
    _checkSetString("0.12e3", 120);
    _checkSetString("0.12e10", 1200000000);

    _checkSetString("0.123e-10", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.123e-1", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.123e0", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.123e1", 1, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.123e2", 12, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.123e3", 123);
    _checkSetString("0.123e10", 1230000000);

    _checkSetString("1.2", 1, 1, 0, ~0 ^ ULBN_SET_STRING_ACCEPT_DECIMAL_PART);
    _checkSetString(".1", 0, 0, 0, ~0 ^ ULBN_SET_STRING_ACCEPT_DECIMAL_PART);
  }

  {
    _checkSetString("0x.1p-10", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x.1p-2", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x.1p-1", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x.1p0", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x.1p2", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x.1p3", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x.1p4", 1);
    _checkSetString("0x.1p5", 2);
    _checkSetString("0x.1p6", 4);

    _checkSetString("0x0.1p-10", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.1p-2", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.1p-1", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.1p0", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.1p2", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.1p3", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.1p4", 1);
    _checkSetString("0x0.1p5", 2);
    _checkSetString("0x0.1p6", 4);

    _checkSetString("0x0.13p-10", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.13p-1", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.13p0", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.13p1", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.13p2", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.13p3", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.13p4", 1, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.13p7", 9, -1, ULBN_ERR_INEXACT);
    _checkSetString("0x0.13p8", 19, -1, 0);
    _checkSetString("0x0.13p9", 38, -1, 0);
  }

  {
    _checkSetString("0.1p-1", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1p-2", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1p0", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1p1", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1p2", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1p3", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1p4", 1, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1p5", 3, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1p6", 6, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1p-1", 0, -1, ULBN_ERR_INEXACT);
    _checkSetString("0.1p-2", 0, -1, ULBN_ERR_INEXACT);

    _checkSetString("0.1p0", 0, 3, ULBN_ERR_INEXACT, ~0 ^ ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH);
    _checkSetString("0.1p1", 0, 3, ULBN_ERR_INEXACT, ~0 ^ ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH);
    _checkSetString("0.1p2", 0, 3, ULBN_ERR_INEXACT, ~0 ^ ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH);
    _checkSetString("0.1p3", 0, 3, ULBN_ERR_INEXACT, ~0 ^ ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH);
    _checkSetString("0.1p4", 0, 3, ULBN_ERR_INEXACT, ~0 ^ ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH);
    _checkSetString("0.1p5", 0, 3, ULBN_ERR_INEXACT, ~0 ^ ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH);
    _checkSetString("0.1p6", 0, 3, ULBN_ERR_INEXACT, ~0 ^ ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH);
  }
}
void testBytes() {
  puts("===Test Bytes");

  for(auto t = TEST_BIG; t--;) {
    int64_t x = static_cast<int64_t>(mt64()), y;
    T_assert(BigInt::fromBytesUnsigned(&x, sizeof(x)).asInt(64) == x);
    T_assert(BigInt::fromBytesUnsigned(&x, sizeof(x)).asUint(64) == static_cast<uint64_t>(x));
    std::reverse_copy(
      reinterpret_cast<char*>(&x), reinterpret_cast<char*>(&x) + sizeof(x), reinterpret_cast<char*>(&y)
    );
    T_assert(BigInt::fromBytesUnsigned(&x, sizeof(x), std::endian::native != std::endian::big).asInt(64) == y);
    T_assert(
      BigInt::fromBytesUnsigned(&x, sizeof(x), std::endian::native != std::endian::big).asUint(64)
      == static_cast<uint64_t>(y)
    );
  }

  for(auto t = TEST_BIG; t--;) {
    int64_t x = static_cast<int64_t>(mt64()), y;
    T_assert(BigInt::fromBytesSigned(&x, sizeof(x)) == x);
    T_assert(BigInt::fromBytesSigned(&x, sizeof(x)).asUint(64) == static_cast<uint64_t>(x));
    std::reverse_copy(
      reinterpret_cast<char*>(&x), reinterpret_cast<char*>(&x) + sizeof(x), reinterpret_cast<char*>(&y)
    );
    T_assert(BigInt::fromBytesSigned(&x, sizeof(x), std::endian::native != std::endian::big) == y);
    T_assert(
      BigInt::fromBytesSigned(&x, sizeof(x), std::endian::native != std::endian::big).asUint(64)
      == static_cast<uint64_t>(y)
    );
  }

  for(auto t = TEST_BIG; t--;) {
    int64_t x = static_cast<int64_t>(mt64()), y;
    BigInt bx = BigInt::fromBytesSigned(&x, sizeof(x));
    T_assert(bx == x);
    bx.toBytesSigned(&y, sizeof(y));
    T_assert(x == y);

    std::reverse(reinterpret_cast<char*>(&x), reinterpret_cast<char*>(&x) + sizeof(x));
    bx.toBytesSigned(&y, sizeof(y), std::endian::native != std::endian::big);
    T_assert(x == y);
  }
}

void test() {
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


  T_assert(BigInt(static_cast<ulbn_limb_t>(0u)) == 0u);
  T_assert(BigInt(static_cast<ulbn_limb_t>(12u)) == 12u);

  T_assert(BigInt(static_cast<ulbn_slimb_t>(0)) == 0);
  T_assert(BigInt(static_cast<ulbn_slimb_t>(-12)) == -12);
  T_assert(BigInt(static_cast<ulbn_slimb_t>(12)) == 12);

  static const double _INF = HUGE_VAL;
  T_assert_exception([] { BigInt x{ _INF }; }, ULBN_ERR_INVALID);
  T_assert_exception([] { BigInt x{ -_INF }; }, ULBN_ERR_INVALID);
  T_assert_exception([] { BigInt x{ nan("") }; }, ULBN_ERR_INVALID);

  T_assert(BigInt(+0.0) == 0);
  T_assert(BigInt(-0.0) == 0);

  T_assert(BigInt(1.0) == 1);
  T_assert(BigInt(0.5) == 0);
  T_assert(BigInt(-1.0) == -1);
  T_assert(BigInt(-0.5) == 0);
  T_assert(BigInt(ldexp(1.0, 51) + 0.5) == BigInt::from2Exp(51));
  T_assert(BigInt(ldexp(1.0, 52) + 0.5) == BigInt::from2Exp(52));

  {
    BigInt tmp;
    T_assert(ulbi_set_double(ulbn_default_alloc(), tmp.get(), +0.0) == 0);
    T_assert(ulbi_set_double(ulbn_default_alloc(), tmp.get(), +0.5) == ULBN_ERR_INEXACT);
    T_assert(ulbi_set_double(ulbn_default_alloc(), tmp.get(), +1.0) == 0);
  }

  testBytes();
  testSetString();
}

int main() {
  testIt(test);
  return 0;
}
