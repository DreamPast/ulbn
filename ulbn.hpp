/*
ulbn - Big Number Library (C++ Wrapper)

# Dependence
  - C++20
    - Concepts and constranints
    - Three-way comparison
    - `<bit>` header file (The platform is big-endian or little-endian)
  - "ulbn.h"

# License
  The MIT License (MIT)

  Copyright (C) 2024 Jin Cai

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
*/
#pragma once
#include <algorithm>
#include <bit>
#include <compare>
#include <cstdio>
#include <cstring>
#include <exception>
#include <ios>
#include <iterator>
#include <limits>
#include <memory>
#include <ostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>

#include "ulbn.h"

namespace ul::bn {

class Exception : public std::runtime_error {
public:
  explicit Exception(int err) : std::runtime_error(_makeMessage(err)), _error(err) { }
  explicit Exception(int err, const char* message) : std::runtime_error(message), _error(err) { }
  explicit Exception(int err, const std::string& message) : std::runtime_error(message), _error(err) { }

  int getError() const {
    return _error;
  }

  friend bool operator==(const Exception& lhs, const Exception& rhs) {
    return lhs.getError() == rhs.getError();
  }
  friend bool operator==(const Exception& lhs, int rhs) {
    return lhs.getError() == rhs;
  }
  friend bool operator==(int lhs, const Exception& rhs) {
    return rhs.getError() == lhs;
  }

private:
  static const char* _makeMessage(int err) {
    switch(err) {
    case ULBN_ERR_EXCEED_RANGE:
      return "unexpected out-of-bounds error";
    case ULBN_ERR_NOMEM:
      return "memory error";
    case ULBN_ERR_SUCCESS:
      return "success";
    case ULBN_ERR_DIV_BY_ZERO:
      return "pole error";
    case ULBN_ERR_INEXACT:
      return "inexact result";
    case ULBN_ERR_INVALID:
      return "domain error";
    case ULBN_ERR_OVERFLOW:
      return "overflow error";
    case ULBN_ERR_UNDERFLOW:
      return "underflow error";
    default:
      return "<unknown error>";
    }
  }
  int _error;
};

#if ULBN_CONF_USE_RAND
inline ulbn_rand_t* getCurrentRand() {
  class _RandManager {
  public:
    _RandManager() {
      ulbn_rand_init(&hold);
    }
    ulbn_rand_t* get() {
      return &hold;
    }

  private:
    ulbn_rand_t hold{};
  };

  static thread_local _RandManager rng;
  return rng.get();
}
#endif

inline ulbn_alloc_t* getCurrentAllocator() {
  static ulbn_alloc_t alloc = *ulbn_default_alloc();
  return &alloc;
}

template<class T>
concept FitSlong = requires {
  requires std::is_integral_v<T>;
  requires std::is_signed_v<T>;
  requires sizeof(T) <= sizeof(ulbn_slong_t);
  requires std::is_convertible_v<T, ulbn_slong_t>;
};
template<class T>
concept FitUlong = requires {
  requires std::is_integral_v<T>;
  requires std::is_unsigned_v<T>;
  requires sizeof(T) <= sizeof(ulbn_ulong_t);
  requires std::is_convertible_v<T, ulbn_ulong_t>;
};
template<class T>
concept FitLimb = requires {
  requires std::is_integral_v<T>;
  requires std::is_unsigned_v<T>;
  requires sizeof(T) <= sizeof(ulbn_limb_t);
  requires std::is_convertible_v<T, ulbn_limb_t>;
};
template<class T>
concept FitSlimb = requires {
  requires std::is_integral_v<T>;
  requires std::is_signed_v<T>;
  requires sizeof(T) <= sizeof(ulbn_slimb_t);
  requires std::is_convertible_v<T, ulbn_slimb_t>;
};
template<class T>
concept FitUsize = requires {
  requires std::is_integral_v<T>;
  requires std::is_unsigned_v<T>;
  requires sizeof(T) <= sizeof(ulbn_usize_t);
  requires std::is_convertible_v<T, ulbn_usize_t>;
};
template<class T>
concept FitSsize = requires {
  requires std::is_integral_v<T>;
  requires std::is_signed_v<T>;
  requires sizeof(T) <= sizeof(ulbn_ssize_t);
  requires std::is_convertible_v<T, ulbn_ssize_t>;
};
template<class T>
concept FitBits = requires {
  requires std::is_integral_v<T>;
  requires std::is_unsigned_v<T>;
  requires sizeof(T) <= sizeof(ulbn_bits_t);
  requires std::is_convertible_v<T, ulbn_bits_t>;
};
template<class T>
concept FitSbits = requires {
  requires std::is_integral_v<T>;
  requires std::is_signed_v<T>;
  requires sizeof(T) <= sizeof(ulbn_sbits_t);
  requires std::is_convertible_v<T, ulbn_sbits_t>;
};
#if ULBN_CONF_HAS_FLOAT
template<class T>
concept FitFloat = requires {
  requires std::is_floating_point_v<T>;
  requires sizeof(T) <= sizeof(float);
  requires std::is_convertible_v<T, float>;

  requires std::numeric_limits<T>::digits <= std::numeric_limits<float>::digits;
  requires std::numeric_limits<T>::min_exponent >= std::numeric_limits<float>::min_exponent;
  requires std::numeric_limits<T>::max_exponent <= std::numeric_limits<float>::max_exponent;
};
#endif /* ULBN_CONF_HAS_FLOAT */
#if ULBN_CONF_HAS_DOUBLE
template<class T>
concept FitDouble = requires {
  requires std::is_floating_point_v<T>;
  requires sizeof(T) <= sizeof(double);
  requires std::is_convertible_v<T, double>;

  requires std::numeric_limits<T>::digits <= std::numeric_limits<double>::digits;
  requires std::numeric_limits<T>::min_exponent >= std::numeric_limits<double>::min_exponent;
  requires std::numeric_limits<T>::max_exponent <= std::numeric_limits<double>::max_exponent;
};
template<class T>
concept FitDoubleCase = requires {
  requires FitDouble<T>;
  #if ULBN_CONF_HAS_FLOAT
  requires !FitFloat<T>;
  #endif
};
#endif /* ULBN_CONF_HAS_DOUBLE */
#if ULBN_CONF_HAS_LONG_DOUBLE
template<class T>
concept FitLongDouble = requires {
  requires std::is_floating_point_v<T>;
  requires sizeof(T) <= sizeof(long double);
  requires std::is_convertible_v<T, long double>;

  requires std::numeric_limits<T>::digits <= std::numeric_limits<long double>::digits;
  requires std::numeric_limits<T>::min_exponent >= std::numeric_limits<long double>::min_exponent;
  requires std::numeric_limits<T>::max_exponent <= std::numeric_limits<long double>::max_exponent;
};
template<class T>
concept FitLongDoubleCase = requires {
  requires FitLongDouble<T>;
  #if ULBN_CONF_HAS_FLOAT
  requires !FitFloat<T>;
  #endif
  #if ULBN_CONF_HAS_DOUBLE
  requires !FitDouble<T>;
  #endif
};
#endif /* ULBN_CONF_HAS_LONG_DOUBLE */

class BigInt {
public:
  BigInt() noexcept {
    ulbi_init(_value);
  }
  ~BigInt() noexcept {
    ulbi_deinit(_ctx(), _value);
  }

  BigInt(const BigInt& other) {
    _check(ulbi_init_copy(_ctx(), _value, other._value));
  }
  BigInt(BigInt&& other) noexcept {
    ulbi_init_move(_ctx(), _value, other._value);
  }
  BigInt& operator=(const BigInt& other) {
    if(this != &other)
      _check(ulbi_set_copy(_ctx(), _value, other._value));
    return *this;
  }
  BigInt& operator=(BigInt&& other) noexcept {
    ulbi_set_move(_ctx(), _value, other._value);
    return *this;
  }

  BigInt(const char* str, int base = 0) {
    const int err = ulbi_init_string(_ctx(), _value, str, base);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the string cannot be fully parsed as an integer");
    _check(err);
  }
  BigInt(const std::string& str, int base = 0) {
    const int err = ulbi_init_string(_ctx(), _value, str.c_str(), base);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the string cannot be fully parsed as an integer");
    _check(err);
  }
  BigInt& operator=(const char* str) {
    const int err = ulbi_set_string(_ctx(), _value, str, 0);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the string cannot be fully parsed as an integer");
    _check(err);
    return *this;
  }
  BigInt& operator=(const std::string& str) {
    const int err = ulbi_set_string(_ctx(), _value, str.c_str(), 0);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the string cannot be fully parsed as an integer");
    _check(err);
    return *this;
  }

  BigInt(const ulbi_t* src) {
    if(src)
      _check(ulbi_init_copy(_ctx(), _value, src));
    else
      ulbi_init(_value);
  }
  BigInt(const ulbi_t& src) {
    _check(ulbi_init_copy(_ctx(), _value, &src));
  }
  BigInt& operator=(const ulbi_t* src) {
    if(src)
      _check(ulbi_set_copy(_ctx(), _value, src));
    else
      ulbi_set_zero(_value);
    return *this;
  }
  BigInt& operator=(const ulbi_t& src) {
    _check(ulbi_set_copy(_ctx(), _value, &src));
    return *this;
  }

  template<FitSlimb T>
  BigInt(T value) noexcept {
    ulbi_init_slimb(_value, static_cast<ulbn_slimb_t>(value));
  }
  template<FitLimb T>
  BigInt(T value) noexcept {
    ulbi_init_limb(_value, static_cast<ulbn_limb_t>(value));
  }
  template<FitSlimb T>
  BigInt& operator=(T value) noexcept {
    ulbi_set_slimb(_value, static_cast<ulbn_slimb_t>(value));
    return *this;
  }
  template<FitLimb T>
  BigInt& operator=(T value) noexcept {
    ulbi_set_limb(_value, static_cast<ulbn_limb_t>(value));
    return *this;
  }

  template<FitSlong T>
    requires(!FitSlimb<T>)
  BigInt(T value) noexcept {
    ulbi_init_slong(_value, static_cast<ulbn_slong_t>(value));
  }
  template<FitUlong T>
    requires(!FitLimb<T>)
  BigInt(T value) noexcept {
    ulbi_init_ulong(_value, static_cast<ulbn_ulong_t>(value));
  }
  template<FitSlong T>
    requires(!FitSlimb<T>)
  BigInt& operator=(T value) noexcept {
    ulbi_set_slong(_value, static_cast<ulbn_slong_t>(value));
    return *this;
  }
  template<FitUlong T>
    requires(!FitLimb<T>)
  BigInt& operator=(T value) noexcept {
    ulbi_set_ulong(_value, static_cast<ulbn_ulong_t>(value));
    return *this;
  }


  BigInt& moveFrom(ulbi_t* src) noexcept {
    if(src)
      ulbi_set_move(_ctx(), _value, src);
    else
      ulbi_init(_value);
    return *this;
  }
  BigInt& moveFrom(ulbi_t& src) noexcept {
    ulbi_set_move(_ctx(), _value, &src);
    return *this;
  }
  BigInt& moveFrom(BigInt& src) noexcept {
    ulbi_set_move(_ctx(), _value, src._value);
    return *this;
  }


  static BigInt fromReserve(ulbn_usize_t n) {
    BigInt ret;
    _check(ulbi_reserve(_ctx(), ret._value, n) ? 0 : ULBN_ERR_NOMEM);
    return ret;
  }


  template<FitBits T>
  static BigInt from2Exp(T n) {
    BigInt ret;
    _check(ulbi_set_2exp_bits(_ctx(), ret._value, static_cast<ulbn_bits_t>(n)));
    return ret;
  }
  template<FitSbits T>
  static BigInt from2Exp(T n) {
    BigInt ret;
    _check(ulbi_set_2exp_sbits(_ctx(), ret._value, static_cast<ulbn_sbits_t>(n)));
    return ret;
  }
  static BigInt from2Exp(const BigInt& n) {
    BigInt ret;
    _check(ulbi_set_2exp(_ctx(), ret._value, n._value));
    return ret;
  }


#if ULBN_CONF_USE_RAND
  template<FitBits T>
  static BigInt fromRandom(T n) {
    BigInt ret;
    _check(ulbi_set_rand_bits(_ctx(), getCurrentRand(), ret._value, static_cast<ulbn_bits_t>(n)));
    return ret;
  }
  template<FitSbits T>
  static BigInt fromRandom(T n) {
    BigInt ret;
    _check(ulbi_set_rand_sbits(_ctx(), getCurrentRand(), ret._value, static_cast<ulbn_sbits_t>(n)));
    return ret;
  }
  static BigInt fromRandom(const BigInt& n) {
    BigInt ret;
    _check(ulbi_set_rand(_ctx(), getCurrentRand(), ret._value, n._value));
    return ret;
  }


  static BigInt fromRandomRange(const BigInt& limit) {
    BigInt ret;
    _check(ulbi_set_rand_range(_ctx(), getCurrentRand(), ret._value, limit._value));
    return ret;
  }
  static BigInt fromRandomRange(const BigInt& lo, const BigInt& hi) {
    BigInt ret;
    _check(ulbi_set_rand_range2(_ctx(), getCurrentRand(), ret._value, lo._value, hi._value));
    return ret;
  }
#endif


  static_assert(
    std::endian::native == std::endian::little || std::endian::native == std::endian::big,
    "only little-endian and big-endian supported"
  );
  static BigInt fromDataUnsigned(const void* ptr, size_t n, bool is_big_endian) {
    BigInt ret;
    _check(ulbi_set_data_unsigned(_ctx(), ret._value, ptr, n, is_big_endian));
    return ret;
  }
  static BigInt fromDataUnsigned(const void* ptr, size_t n, std::endian endian = std::endian::native) {
    return fromDataUnsigned(ptr, n, endian == std::endian::big);
  }

  static BigInt fromDataSigned(const void* ptr, size_t n, bool is_big_endian) {
    BigInt ret;
    _check(ulbi_set_data_signed(_ctx(), ret._value, ptr, n, is_big_endian));
    return ret;
  }
  static BigInt fromDataSigned(const void* ptr, size_t n, std::endian endian = std::endian::native) {
    return fromDataSigned(ptr, n, endian == std::endian::big);
  }


  void toDataSigned(void* ptr, size_t n, bool is_big_endian) const noexcept {
    ulbi_to_data_signed(_value, ptr, n, is_big_endian);
  }
  void toDataSigned(void* ptr, size_t n, std::endian endian = std::endian::native) const noexcept {
    ulbi_to_data_signed(_value, ptr, n, endian == std::endian::big);
  }


  static BigInt fromStringEx(const char* str, int base = 0, int flags = ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX) {
    BigInt ret;
    _check(ulbi_set_string_ex(_ctx(), ret._value, &str, base, flags));
    return ret;
  }
  static BigInt fromStringEx(
    const std::string& str, int base = 0, int flags = ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX
  ) {
    return fromStringEx(str.c_str(), base, flags);
  }


  BigInt& operator+=(const BigInt& other) {
    _check(ulbi_add(_ctx(), _value, _value, other._value));
    return *this;
  }
  template<FitLimb T>
  BigInt& operator+=(T value) {
    _check(ulbi_add_limb(_ctx(), _value, _value, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator+=(T value) {
    _check(ulbi_add_slimb(_ctx(), _value, _value, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }

  friend BigInt operator+(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_add(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator+(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_add_limb(_ctx(), ret._value, lhs._value, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator+(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_add_slimb(_ctx(), ret._value, lhs._value, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator+(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_add_limb(_ctx(), ret._value, rhs._value, static_cast<ulbn_limb_t>(lhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator+(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_add_slimb(_ctx(), ret._value, rhs._value, static_cast<ulbn_slimb_t>(lhs)));
    return ret;
  }


  BigInt& operator-=(const BigInt& other) {
    _check(ulbi_sub(_ctx(), _value, _value, other._value));
    return *this;
  }
  template<FitLimb T>
  BigInt& operator-=(T value) {
    _check(ulbi_sub_limb(_ctx(), _value, _value, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator-=(T value) {
    _check(ulbi_sub_slimb(_ctx(), _value, _value, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }

  friend BigInt operator-(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_sub(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator-(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_sub_limb(_ctx(), ret._value, lhs._value, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator-(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_sub_slimb(_ctx(), ret._value, lhs._value, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator-(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_limb_sub(_ctx(), ret._value, static_cast<ulbn_limb_t>(lhs), rhs._value));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator-(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_slimb_sub(_ctx(), ret._value, static_cast<ulbn_slimb_t>(lhs), rhs._value));
    return ret;
  }


  BigInt& operator++() {
    _check(ulbi_add_limb(_ctx(), _value, _value, 1));
    return *this;
  }
  BigInt operator++(int) {
    BigInt ret(*this);
    _check(ulbi_add_limb(_ctx(), _value, _value, 1));
    return ret;
  }
  BigInt& operator--() {
    _check(ulbi_sub_limb(_ctx(), _value, _value, 1));
    return *this;
  }
  BigInt operator--(int) {
    BigInt ret(*this);
    _check(ulbi_sub_limb(_ctx(), _value, _value, 1));
    return ret;
  }


  BigInt operator+() const {
    return *this;
  }
  BigInt operator-() const {
    BigInt ret;
    _check(ulbi_neg(_ctx(), ret._value, _value));
    return ret;
  }
  BigInt abs() const {
    BigInt ret;
    _check(ulbi_abs(_ctx(), ret._value, _value));
    return ret;
  }


  BigInt& operator*=(const BigInt& other) {
    _check(ulbi_mul(_ctx(), _value, _value, other._value));
    return *this;
  }
  friend BigInt operator*(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_mul(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }

  template<FitLimb T>
  BigInt& operator*=(T value) {
    _check(ulbi_mul_limb(_ctx(), _value, _value, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator*=(T value) {
    _check(ulbi_mul_slimb(_ctx(), _value, _value, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }
  template<FitLimb T>
  friend BigInt operator*(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_mul_limb(_ctx(), ret._value, lhs._value, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator*(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_mul_slimb(_ctx(), ret._value, lhs._value, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator*(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_mul_limb(_ctx(), ret._value, rhs._value, static_cast<ulbn_limb_t>(lhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator*(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_mul_slimb(_ctx(), ret._value, rhs._value, static_cast<ulbn_slimb_t>(lhs)));
    return ret;
  }


  BigInt& operator/=(const BigInt& other) {
    _check(ulbi_divmod(_ctx(), _value, nullptr, _value, other._value));
    return *this;
  }
  template<FitLimb T>
  BigInt& operator/=(T value) {
    _check(ulbi_divmod_limb(_ctx(), _value, nullptr, _value, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator/=(T value) {
    _check(ulbi_divmod_slimb(_ctx(), _value, nullptr, _value, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }
  friend BigInt operator/(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_divmod(_ctx(), ret._value, nullptr, lhs._value, rhs._value));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator/(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_divmod_limb(_ctx(), ret._value, nullptr, lhs._value, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator/(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_divmod_slimb(_ctx(), ret._value, nullptr, lhs._value, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }

  template<FitSlimb T>
  BigInt& operator%=(T value) {
    ulbn_slimb_t r;
    _check(ulbi_divmod_slimb(_ctx(), nullptr, &r, _value, static_cast<ulbn_slimb_t>(value)));
    ulbi_set_slimb(_value, r);
    return *this;
  }
  BigInt& operator%=(const BigInt& other) {
    _check(ulbi_divmod(_ctx(), nullptr, _value, _value, other._value));
    return *this;
  }
  friend BigInt operator%(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_divmod(_ctx(), nullptr, ret._value, lhs._value, rhs._value));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator%(const BigInt& lhs, T rhs) {
    ulbn_slimb_t r;
    _check(ulbi_divmod_slimb(_ctx(), nullptr, &r, lhs._value, static_cast<ulbn_slimb_t>(rhs)));
    return r;
  }

  std::pair<BigInt, BigInt> divmod(const BigInt& other) const {
    BigInt q, r;
    _check(ulbi_divmod(_ctx(), q._value, r._value, _value, other._value));
    return { q, r };
  }
  std::pair<BigInt, BigInt> divmod(const BigInt& other, enum ULBN_ROUND_ENUM round_mode) const {
    BigInt q, r;
    const int err = ulbi_divmod_ex(_ctx(), q._value, r._value, _value, other._value, round_mode);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the round mode is illegal");
    _check(err);
    return { q, r };
  }
  BigInt div(const BigInt& other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_DOWN) const {
    BigInt q;
    const int err = ulbi_divmod_ex(_ctx(), q._value, nullptr, _value, other._value, round_mode);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the round mode is illegal");
    _check(err);
    return q;
  }
  BigInt mod(const BigInt& other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_DOWN) const {
    BigInt r;
    const int err = ulbi_divmod_ex(_ctx(), nullptr, r._value, _value, other._value, round_mode);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the round mode is illegal");
    _check(err);
    return r;
  }

  template<FitSbits T>
  std::pair<BigInt, BigInt> divmod(T other) const {
    BigInt q;
    ulbn_slimb_t rl;
    _check(ulbi_divmod_slimb(_ctx(), q._value, &rl, _value, static_cast<ulbn_slimb_t>(other)));
    return { q, BigInt(rl) };
  }
  template<FitSbits T>
  std::pair<BigInt, BigInt> divmod(T other, enum ULBN_ROUND_ENUM round_mode) const {
    BigInt q;
    ulbn_slimb_t rl;
    _check(ulbi_divmod_slimb_ex(_ctx(), q._value, &rl, _value, static_cast<ulbn_slimb_t>(other), round_mode));
    return { q, BigInt(rl) };
  }
  template<FitSbits T>
  BigInt div(T other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_DOWN) const {
    BigInt q;
    _check(ulbi_divmod_slimb_ex(_ctx(), q._value, nullptr, _value, static_cast<ulbn_slimb_t>(other), round_mode));
    return q;
  }
  template<FitSbits T>
  BigInt mod(T other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_DOWN) const {
    ulbn_slimb_t rl;
    _check(ulbi_divmod_slimb_ex(_ctx(), nullptr, &rl, _value, static_cast<ulbn_slimb_t>(other), round_mode));
    return rl;
  }


  template<FitBits T>
  std::pair<BigInt, BigInt> divmod2Exp(T n) const {
    BigInt q, r;
    _check(ulbi_divmod_2exp_bits(_ctx(), q._value, r._value, _value, static_cast<ulbn_bits_t>(n)));
    return { q, r };
  }
  template<FitSbits T>
  std::pair<BigInt, BigInt> divmod2Exp(T n) const {
    BigInt q, r;
    _check(ulbi_divmod_2exp_sbits(_ctx(), q._value, r._value, _value, static_cast<ulbn_sbits_t>(n)));
    return { q, r };
  }
  std::pair<BigInt, BigInt> divmod2Exp(const BigInt& other) const {
    BigInt q, r;
    _check(ulbi_divmod_2exp(_ctx(), q._value, r._value, _value, other._value));
    return { q, r };
  }

  template<FitBits T>
  BigInt div2Exp(T n) const {
    BigInt q;
    _check(ulbi_divmod_2exp_bits(_ctx(), q._value, ul_nullptr, _value, static_cast<ulbn_bits_t>(n)));
    return q;
  }
  template<FitSbits T>
  BigInt div2Exp(T n) const {
    BigInt q;
    _check(ulbi_divmod_2exp_sbits(_ctx(), q._value, ul_nullptr, _value, static_cast<ulbn_sbits_t>(n)));
    return q;
  }
  BigInt div2Exp(const BigInt& other) const {
    BigInt q;
    _check(ulbi_divmod_2exp(_ctx(), q._value, ul_nullptr, _value, other._value));
    return q;
  }

  template<FitBits T>
  BigInt mod2Exp(T n) const {
    BigInt r;
    _check(ulbi_divmod_2exp_bits(_ctx(), ul_nullptr, r._value, _value, static_cast<ulbn_bits_t>(n)));
    return r;
  }
  template<FitSbits T>
  BigInt mod2Exp(T n) const {
    BigInt r;
    _check(ulbi_divmod_2exp_sbits(_ctx(), ul_nullptr, r._value, _value, static_cast<ulbn_sbits_t>(n)));
    return r;
  }
  BigInt mod2Exp(const BigInt& other) const {
    BigInt r;
    _check(ulbi_divmod_2exp(_ctx(), ul_nullptr, r._value, _value, other._value));
    return r;
  }


  friend std::strong_ordering operator<=>(const BigInt& lhs, const BigInt& rhs) {
    return ulbi_comp(lhs._value, rhs._value) <=> 0;
  }

  template<FitLimb T>
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) {
    return ulbi_comp_limb(lhs._value, static_cast<ulbn_limb_t>(rhs)) <=> 0;
  }
  template<FitSlimb T>
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) {
    return ulbi_comp_slimb(lhs._value, static_cast<ulbn_slimb_t>(rhs)) <=> 0;
  }
  template<FitUlong T>
    requires(!FitLimb<T>)
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) {
    return ulbi_comp_ulong(lhs._value, static_cast<ulbn_ulong_t>(rhs)) <=> 0;
  }
  template<FitSlong T>
    requires(!FitSlimb<T>)
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) {
    return ulbi_comp_slong(lhs._value, static_cast<ulbn_slong_t>(rhs)) <=> 0;
  }

  template<FitLimb T>
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) {
    return (-ulbi_comp_limb(rhs._value, static_cast<ulbn_limb_t>(lhs))) <=> 0;
  }
  template<FitSlimb T>
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) {
    return (-ulbi_comp_slimb(rhs._value, static_cast<ulbn_slimb_t>(lhs))) <=> 0;
  }
  template<FitUlong T>
    requires(!FitLimb<T>)
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) {
    return (-ulbi_comp_ulong(rhs._value, static_cast<ulbn_ulong_t>(lhs))) <=> 0;
  }
  template<FitSlong T>
    requires(!FitSlimb<T>)
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) {
    return (-ulbi_comp_slong(rhs._value, static_cast<ulbn_slong_t>(lhs))) <=> 0;
  }

  friend bool operator==(const BigInt& lhs, const BigInt& rhs) {
    return ulbi_eq(lhs._value, rhs._value) != 0;
  }
  template<FitLimb T>
  friend bool operator==(const BigInt& lhs, T rhs) {
    return ulbi_eq_limb(lhs._value, static_cast<ulbn_limb_t>(rhs)) != 0;
  }
  template<FitSlimb T>
  friend bool operator==(const BigInt& lhs, T rhs) {
    return ulbi_eq_slimb(lhs._value, static_cast<ulbn_slimb_t>(rhs)) != 0;
  }
  template<FitUlong T>
    requires(!FitLimb<T>)
  friend bool operator==(const BigInt& lhs, T rhs) {
    return ulbi_eq_ulong(lhs._value, static_cast<ulbn_ulong_t>(rhs)) != 0;
  }
  template<FitSlong T>
    requires(!FitSlimb<T>)
  friend bool operator==(const BigInt& lhs, T rhs) {
    return ulbi_eq_slong(lhs._value, static_cast<ulbn_slong_t>(rhs)) != 0;
  }

  template<FitLimb T>
  friend bool operator==(T lhs, const BigInt& rhs) {
    return ulbi_eq_limb(rhs._value, static_cast<ulbn_limb_t>(lhs)) != 0;
  }
  template<FitSlimb T>
  friend bool operator==(T lhs, const BigInt& rhs) {
    return ulbi_eq_slimb(rhs._value, static_cast<ulbn_slimb_t>(lhs)) != 0;
  }
  template<FitUlong T>
    requires(!FitLimb<T>)
  friend bool operator==(T lhs, const BigInt& rhs) {
    return ulbi_eq_ulong(rhs._value, static_cast<ulbn_ulong_t>(lhs)) != 0;
  }
  template<FitSlong T>
    requires(!FitSlimb<T>)
  friend bool operator==(T lhs, const BigInt& rhs) {
    return ulbi_eq_slong(rhs._value, static_cast<ulbn_slong_t>(lhs)) != 0;
  }


  explicit operator bool() const {
    return !ulbi_is_zero(_value);
  }
  bool operator!() const {
    return ulbi_is_zero(_value) != 0;
  }


  BigInt& operator&=(const BigInt& other) {
    _check(ulbi_and(_ctx(), _value, _value, other._value));
    return *this;
  }
  BigInt& operator|=(const BigInt& other) {
    _check(ulbi_or(_ctx(), _value, _value, other._value));
    return *this;
  }
  BigInt& operator^=(const BigInt& other) {
    _check(ulbi_xor(_ctx(), _value, _value, other._value));
    return *this;
  }
  friend BigInt operator&(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_and(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }
  friend BigInt operator|(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_or(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }
  friend BigInt operator^(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_xor(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }

  BigInt operator~() const {
    BigInt ret;
    _check(ulbi_com(_ctx(), ret._value, _value));
    return ret;
  }

  template<FitBits T>
  BigInt& operator<<=(T shift) {
    _check(ulbi_sal_bits(_ctx(), _value, _value, static_cast<ulbn_bits_t>(shift)));
    return *this;
  }
  template<FitSbits T>
  BigInt& operator<<=(T shift) {
    _check(ulbi_sal_sbits(_ctx(), _value, _value, static_cast<ulbn_sbits_t>(shift)));
    return *this;
  }
  BigInt& operator<<=(const BigInt& shift) {
    _check(ulbi_sal(_ctx(), _value, _value, shift._value));
    return *this;
  }
  template<FitBits T>
  friend BigInt operator<<(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sal_bits(_ctx(), ret._value, lhs._value, static_cast<ulbn_bits_t>(shift)));
    return ret;
  }
  template<FitSbits T>
  friend BigInt operator<<(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sal_sbits(_ctx(), ret._value, lhs._value, static_cast<ulbn_sbits_t>(shift)));
    return ret;
  }
  friend BigInt operator<<(const BigInt& lhs, const BigInt& shift) {
    BigInt ret;
    _check(ulbi_sal(_ctx(), ret._value, lhs._value, shift._value));
    return ret;
  }

  template<FitBits T>
  BigInt& operator>>=(T shift) {
    _check(ulbi_sar_bits(_ctx(), _value, _value, static_cast<ulbn_bits_t>(shift)));
    return *this;
  }
  template<FitSbits T>
  BigInt& operator>>=(T shift) {
    _check(ulbi_sar_sbits(_ctx(), _value, _value, static_cast<ulbn_sbits_t>(shift)));
    return *this;
  }
  BigInt& operator>>=(const BigInt& shift) {
    _check(ulbi_sar(_ctx(), _value, _value, shift._value));
    return *this;
  }
  template<FitBits T>
  friend BigInt operator>>(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sar_bits(_ctx(), ret._value, lhs._value, static_cast<ulbn_bits_t>(shift)));
    return ret;
  }
  template<FitSbits T>
  friend BigInt operator>>(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sar_sbits(_ctx(), ret._value, lhs._value, static_cast<ulbn_sbits_t>(shift)));
    return ret;
  }
  friend BigInt operator>>(const BigInt& lhs, const BigInt& shift) {
    BigInt ret;
    _check(ulbi_sar(_ctx(), ret._value, lhs._value, shift._value));
    return ret;
  }


  template<FitUlong T>
  BigInt pow(T e) const {
    BigInt ret;
    _check(ulbi_pow_ulong(_ctx(), ret._value, _value, static_cast<ulbn_ulong_t>(e)));
    return ret;
  }
  template<FitSlong T>
  BigInt pow(T e) const {
    BigInt ret;
    _check(ulbi_pow_slong(_ctx(), ret._value, _value, static_cast<ulbn_slong_t>(e)));
    return ret;
  }
  BigInt pow(const BigInt& e) const {
    BigInt ret;
    _check(ulbi_pow(_ctx(), ret._value, _value, e._value));
    return ret;
  }
  BigInt sqrt() const {
    BigInt ret;
    const int err = ulbi_sqrt(_ctx(), ret._value, _value);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the value is negative");
    _check(err);
    return ret;
  }
  std::pair<BigInt, BigInt> sqrtrem() const {
    BigInt q, r;
    const int err = ulbi_sqrtrem(_ctx(), q._value, r._value, _value);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the value is negative");
    _check(err);
    return { q, r };
  }
  BigInt root(const BigInt& e) const {
    BigInt ret;
    const int err = ulbi_root(_ctx(), ret._value, _value, e._value);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the result is illegal");
    _check(err);
    return ret;
  }
  std::pair<BigInt, BigInt> rootrem(const BigInt& e) const {
    BigInt q, r;
    const int err = ulbi_rootrem(_ctx(), q._value, r._value, _value, e._value);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the result is illegal");
    _check(err);
    return { q, r };
  }


  BigInt& shrink() {
    _check(ulbi_shrink(_ctx(), _value));
    return *this;
  }
  BigInt& reserve(ulbn_usize_t n) {
    _check(ulbi_reserve(_ctx(), _value, n) == nullptr ? ULBN_ERR_NOMEM : 0);
    return *this;
  }


  BigInt& swap(BigInt& other) noexcept {
    ulbi_swap(_value, other._value);
    return *this;
  }


  bool isZero() const noexcept {
    return ulbi_is_zero(_value) != 0;
  }
  bool isOdd() const noexcept {
    return ulbi_is_odd(_value) != 0;
  }
  bool isEven() const noexcept {
    return ulbi_is_even(_value) != 0;
  }
  int sign() const noexcept {
    return ulbi_sign(_value);
  }


  bool fitUlong() const noexcept {
    return ulbi_fit_ulong(_value) != 0;
  }
  bool fitSlong() const noexcept {
    return ulbi_fit_slong(_value) != 0;
  }
  bool fitLimb() const noexcept {
    return ulbi_fit_limb(_value) != 0;
  }
  bool fitSlimb() const noexcept {
    return ulbi_fit_slimb(_value) != 0;
  }


  ulbn_ulong_t toUlong() const noexcept {
    return ulbi_to_ulong(_value);
  }
  ulbn_slong_t toSlong() const noexcept {
    return ulbi_to_slong(_value);
  }
  ulbn_limb_t toLimb() const noexcept {
    return ulbi_to_limb(_value);
  }
  ulbn_slimb_t toSlimb() const noexcept {
    return ulbi_to_slimb(_value);
  }


  explicit operator ulbn_ulong_t() const noexcept {
    return toUlong();
  }
  explicit operator ulbn_slong_t() const noexcept {
    return toSlong();
  }


  template<class StringAllocator = std::allocator<char>>
  auto toString(int base = 10) const {
    using String = std::basic_string<char, std::char_traits<char>, StringAllocator>;
    Wrapper<String> wrapper(String{});
    int err = ulbi_print_ex(
      _ctx(),
      [](void* opaque, const char* str, size_t len) -> int {
        return reinterpret_cast<Wrapper<String>*>(opaque)->call([&](String& s) { s.append(str, len); });
      },
      &wrapper, _value, base
    );
    return wrapper.check(err);
  }
  template<class StringAllocator>
  auto& toString(std::basic_string<char, std::char_traits<char>, StringAllocator>& dst, int base = 10) const {
    using String = std::basic_string<char, std::char_traits<char>, StringAllocator>;
    Wrapper<String&> wrapper(dst);
    dst.clear();
    int err = ulbi_print_ex(
      _ctx(),
      [](void* opaque, const char* str, size_t len) -> int {
        return reinterpret_cast<Wrapper<String>*>(opaque)->call([&](String& s) { s.append(str, len); });
      },
      &wrapper, _value, base
    );
    return wrapper.check(err);
  }

  friend std::ostream& operator<<(std::ostream& ost, const BigInt& value) {
    value.print(ost);
    return ost;
  }
  void print(FILE* fp, int base = 10) const {
    _check(ulbi_print(_ctx(), fp, _value, base));
  }
  std::ostream& print(std::ostream& ost, int base = 10) const {
    Wrapper<std::ostream&> wrapper(ost);
    const int err = ulbi_print_ex(
      _ctx(),
      [](void* opaque, const char* ptr, size_t len) -> int {
        return reinterpret_cast<Wrapper<std::ostream&>*>(opaque)->call([&](std::ostream& os) {
          os.write(ptr, static_cast<std::streamsize>(len));
        });
      },
      &wrapper, _value, base
    );
    return wrapper.check(err);
  }
  template<class Iter>
    requires std::output_iterator<Iter, char>
  Iter print(Iter iter, int base = 10) const {
    Wrapper<Iter&> wrapper(iter);
    int err = ulbi_print_ex(
      _ctx(), _value, base,
      [](void* opaque, const char* ptr, size_t len) -> int {
        return reinterpret_cast<Wrapper<Iter&>*>(opaque)->call([&](Iter& itr) { std::copy_n(ptr, len, itr); });
      },
      &wrapper
    );
    return wrapper->check(err);
  }


  ulbi_t* get() noexcept {
    return _value;
  }
  const ulbi_t* get() const noexcept {
    return _value;
  }


  template<FitBits T>
  bool testBit(T n) const noexcept {
    return ulbi_testbit_bits(_value, static_cast<ulbn_bits_t>(n)) != 0;
  }
  template<FitSbits T>
  bool testBit(T n) const noexcept {
    return ulbi_testbit_sbits(_value, static_cast<ulbn_sbits_t>(n)) != 0;
  }
  bool testBit(const BigInt& n) const noexcept {
    return ulbi_testbit(_value, n._value) != 0;
  }

  template<FitBits T>
  BigInt& setBit(T n) {
    _check(ulbi_setbit_bits(_ctx(), _value, static_cast<ulbn_bits_t>(n)));
    return *this;
  }
  template<FitSbits T>
  BigInt& setBit(T n) {
    _check(ulbi_setbit_sbits(_ctx(), _value, static_cast<ulbn_sbits_t>(n)));
    return *this;
  }
  BigInt& setBit(const BigInt& n) {
    _check(ulbi_setbit(_ctx(), _value, n._value));
    return *this;
  }

  template<FitBits T>
  BigInt& resetBit(T n) {
    _check(ulbi_resetbit_bits(_ctx(), _value, static_cast<ulbn_bits_t>(n)));
    return *this;
  }
  template<FitSbits T>
  BigInt& resetBit(T n) {
    _check(ulbi_resetbit_sbits(_ctx(), _value, static_cast<ulbn_sbits_t>(n)));
    return *this;
  }
  BigInt& resetBit(const BigInt& n) {
    _check(ulbi_resetbit(_ctx(), _value, n._value));
    return *this;
  }

  template<FitBits T>
  BigInt& comBit(T n) {
    _check(ulbi_combit_bits(_ctx(), _value, static_cast<ulbn_bits_t>(n)));
    return *this;
  }
  template<FitSbits T>
  BigInt& comBit(T n) {
    _check(ulbi_combit_sbits(_ctx(), _value, static_cast<ulbn_sbits_t>(n)));
    return *this;
  }
  BigInt& comBit(const BigInt& n) {
    _check(ulbi_combit(_ctx(), _value, n._value));
    return *this;
  }


  template<FitUsize T>
  BigInt asUint(T n) {
    BigInt ret;
    _check(ulbi_as_uint_usize(_ctx(), ret._value, _value, static_cast<ulbn_usize_t>(n)));
    return ret;
  }
  template<FitSsize T>
  BigInt asUint(T n) {
    BigInt ret;
    _check(ulbi_as_uint_ssize(_ctx(), ret._value, _value, static_cast<ulbn_ssize_t>(n)));
    return ret;
  }
  template<FitBits T>
    requires(!FitUsize<T>)
  BigInt asUint(T n) {
    BigInt ret;
    _check(ulbi_as_uint_bits(_ctx(), ret._value, _value, static_cast<ulbn_bits_t>(n)));
    return ret;
  }
  template<FitSbits T>
    requires(!FitSsize<T>)
  BigInt asUint(T n) {
    BigInt ret;
    _check(ulbi_as_uint_sbits(_ctx(), ret._value, _value, static_cast<ulbn_sbits_t>(n)));
    return ret;
  }
  BigInt asUint(const BigInt& n) {
    BigInt ret;
    _check(ulbi_as_uint(_ctx(), ret._value, _value, n._value));
    return ret;
  }

  template<FitUsize T>
  BigInt asInt(T n) {
    BigInt ret;
    _check(ulbi_as_int_usize(_ctx(), ret._value, _value, static_cast<ulbn_usize_t>(n)));
    return ret;
  }
  template<FitSsize T>
  BigInt asInt(T n) {
    BigInt ret;
    _check(ulbi_as_int_ssize(_ctx(), ret._value, _value, static_cast<ulbn_ssize_t>(n)));
    return ret;
  }
  template<FitBits T>
    requires(!FitUsize<T>)
  BigInt asInt(T n) {
    BigInt ret;
    _check(ulbi_as_int_bits(_ctx(), ret._value, _value, static_cast<ulbn_bits_t>(n)));
    return ret;
  }
  template<FitSbits T>
    requires(!FitSsize<T>)
  BigInt asInt(T n) {
    BigInt ret;
    _check(ulbi_as_int_sbits(_ctx(), ret._value, _value, static_cast<ulbn_sbits_t>(n)));
    return ret;
  }
  BigInt asInt(const BigInt& n) {
    BigInt ret;
    _check(ulbi_as_int(_ctx(), ret._value, _value, n._value));
    return ret;
  }


  bool is2Pow() const noexcept {
    return ulbi_is_2pow(_value) != 0;
  }
  ulbn_bits_t ctz() const noexcept {
    return ulbi_ctz(_value);
  }
  ulbn_bits_t cto() const noexcept {
    return ulbi_cto(_value);
  }
  ulbn_bits_t absPopcount() const noexcept {
    return ulbi_abs_popcount(_value);
  }
  ulbn_bits_t absBitWidth() const noexcept {
    return ulbi_abs_bit_width(_value);
  }


#if ULBN_CONF_HAS_FLOAT
  template<FitFloat T>
  explicit BigInt(T value) {
    _check(ulbi_init_float(_ctx(), _value, static_cast<float>(value)));
  }
  template<FitFloat T>
  BigInt& operator=(T value) {
    _check(ulbi_set_float(_ctx(), _value, static_cast<float>(value)));
    return *this;
  }
  float toFloat() const noexcept {
    return ulbi_to_float(_value);
  }
  bool fitFloat() const noexcept {
    return ulbi_fit_float(_value) != 0;
  }
  explicit operator float() const noexcept {
    return toFloat();
  }
#endif


#if ULBN_CONF_HAS_DOUBLE
  template<FitDoubleCase T>
  explicit BigInt(T value) {
    _check(ulbi_init_double(_ctx(), _value, static_cast<double>(value)));
  }
  template<FitDoubleCase T>
  BigInt& operator=(T value) {
    _check(ulbi_set_double(_ctx(), _value, static_cast<double>(value)));
    return *this;
  }
  double toDouble() const noexcept {
    return ulbi_to_double(_value);
  }
  bool fitDouble() const noexcept {
    return ulbi_fit_double(_value) != 0;
  }
  explicit operator double() const noexcept {
    return toDouble();
  }
#endif /* ULBN_CONF_HAS_DOUBLE */


#if ULBN_CONF_HAS_LONG_DOUBLE
  template<FitLongDoubleCase T>
  explicit BigInt(T value) {
    _check(ulbi_init_long_double(_ctx(), _value, static_cast<long double>(value)));
  }
  template<FitLongDoubleCase T>
  BigInt& operator=(T value) {
    _check(ulbi_set_long_double(_ctx(), _value, static_cast<long double>(value)));
    return *this;
  }
  long double toLongDouble() const noexcept {
    return ulbi_to_long_double(_value);
  }
  bool fitLongDouble() const noexcept {
    return ulbi_fit_long_double(_value) != 0;
  }
  explicit operator long double() const noexcept {
    return toLongDouble();
  }
#endif /* ULBN_CONF_HAS_LONG_DOUBLE */


  BigInt gcd(const BigInt& other) {
    BigInt ret;
    _check(ulbi_gcd(_ctx(), ret._value, _value, other._value));
    return ret;
  }
  template<FitLimb T>
  BigInt gcd(T other) {
    BigInt ret;
    _check(ulbi_gcd_limb(_ctx(), ret._value, _value, static_cast<ulbn_limb_t>(other)));
    return ret;
  }
  template<FitSlimb T>
  BigInt gcd(T other) {
    BigInt ret;
    _check(ulbi_gcd_slimb(_ctx(), ret._value, _value, static_cast<ulbn_slimb_t>(other)));
    return ret;
  }
  BigInt lcm(const BigInt& other) {
    BigInt ret;
    _check(ulbi_lcm(_ctx(), ret._value, _value, other._value));
    return ret;
  }


  std::tuple<BigInt, BigInt, BigInt> gcdext(const BigInt& other) {
    BigInt g, x, y;
    _check(ulbi_gcdext(_ctx(), g._value, x._value, y._value, _value, other._value));
    return { g, x, y };
  }
  BigInt invert(const BigInt& m) {
    BigInt ret;
    _check(ulbi_invert(_ctx(), ret._value, _value, m._value));
    return ret;
  }


private:
  static const ulbn_alloc_t* _ctx() noexcept {
    return getCurrentAllocator();
  }
  static int _check(int err) {
    if(err != ULBN_ERR_INEXACT && err != 0 && err != 1)
      throw Exception(err);
    return err;
  }

  template<class T>
  class Wrapper {
  public:
    Wrapper() = delete;
    ~Wrapper() = default;
    Wrapper(const Wrapper&) = default;
    Wrapper(Wrapper&&) = delete;
    Wrapper& operator=(const Wrapper&) = delete;
    Wrapper& operator=(Wrapper&&) = delete;

    template<class TValue>
      requires std::is_constructible_v<T, TValue>
    Wrapper(TValue&& construct_value) : value(std::forward<TValue>(construct_value)) { }
    template<class Func>
    int call(Func func) noexcept {
      try {
        func(value);
        return 0;
      } catch(...) {
        exception = std::current_exception();
        return -1;
      }
    }
    T check(int err) {
      if(err == ULBN_ERR_EXTERNAL)
        std::rethrow_exception(exception);
      _check(err);
      return value;
    }

  private:
    T value;
    std::exception_ptr exception;
  };

  ulbi_t _value[1];
};

inline BigInt operator""_bi(const char* str) {
  return { str };
}
inline BigInt operator""_bi(const char* str, size_t len) {
  (void)len;
  return { str };
}

}  // namespace ul::bn
