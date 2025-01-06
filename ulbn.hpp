/*
ulbn - Big Number Library (C++ Wrapper)

# Requirements
  - C++20
    - Concepts and constranints
    - Three-way comparison
    - std::endian
    - std::span
    - std::format (optional)
  - "ulbn.h"

  According to [cppreference](https://en.cppreference.com/), the common minimum compiler requirements is:
  - GCC 10 (May, 7, 2020)
  - Clang 10 (March, 24, 2020)
  - MSVC 19.26 (May, 19, 2020)

# License
  The MIT License (MIT)

  Copyright (C) 2024-2025 Jin Cai

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
#include <array>
#include <bit>
#include <climits>
#include <compare>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <exception>
#include <ios>
#include <istream>
#include <iterator>
#include <limits>
#include <memory>
#include <ostream>
#include <random>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <utility>

#if defined(__cpp_lib_format) && __cpp_lib_format >= 201907L
  #include <format>
#endif

#include "ulbn.h"

#if CHAR_BIT != 8
  #error "CHAR_BIT must be 8"
#endif

namespace ul {

template<class CharT = char>
struct FormatHelper {
  enum class Align : int8_t {
    DEFUALT,
    LEFT,
    RIGHT,
    INTERNAL,
  };
  enum class Sign : int8_t {
    ONLY_NEGATIVE,
    ALWAYS,
    SPACE_ON_NONNEGATIVE,
  };
#if defined(__cpp_lib_format) && __cpp_lib_format >= 201907L
  using FormatError = std::format_error;
#else
  using FormatError = std::runtime_error;
#endif

  CharT fill = SPACE;
  Align align = Align::DEFUALT;
  Sign sign = Sign::ONLY_NEGATIVE;
  bool use_alter = false;
  size_t width = 0;
  bool has_precision = false;
  size_t precision = 0;
  bool use_locale = false;
  std::basic_string<CharT> target_type;

  template<class Iter, class IterEnd>
  constexpr Iter parse(Iter first, IterEnd last) {
    if(first == last)
      return first;
    {
      CharT c0 = *first;
      if(auto next = std::next(first); next != last) {
        if(CharT c1 = *next; c1 == LESS_THAN || c1 == GREATER_THAN || c1 == CARET) {
          fill = c0;
          ++first;
        }
      }
    }

    if(*first == LESS_THAN) {
      align = Align::LEFT;
      ++first;
    } else if(*first == GREATER_THAN) {
      align = Align::RIGHT;
      ++first;
    } else if(*first == CARET) {
      align = Align::INTERNAL;
      ++first;
    }
    if(first == last || _isIllegal(*first))
      return first;

    if(*first == PLUS) {
      sign = Sign::ALWAYS;
      ++first;
    } else if(*first == MINUS) {
      sign = Sign::ONLY_NEGATIVE;
      ++first;
    } else if(*first == SPACE) {
      sign = Sign::SPACE_ON_NONNEGATIVE;
      ++first;
    }
    if(first == last || _isIllegal(*first))
      return first;

    if(*first == HASH) {
      use_alter = true;
      ++first;
      if(first == last || _isIllegal(*first))
        return first;
    }

    size_t w = 0;
    for(; first != last && (*first >= ZERO && *first <= NINE); ++first) {
      if(w >= _SIZE_LIMIT)
        throw FormatError("width is too large");
      w = w * 10 + static_cast<size_t>(*first - ZERO);
    }
    width = w;
    if(first == last || _isIllegal(*first))
      return first;

    if(*first == DOT) {
      has_precision = true;
      ++first;
      if(first == last || _isIllegal(*first))
        return first;

      w = 0;
      for(; first != last && (*first >= ZERO && *first <= NINE); ++first) {
        if(w >= _SIZE_LIMIT)
          throw FormatError("precision is too large");
        w = w * 10 + static_cast<size_t>(*first - ZERO);
      }
      precision = w;
      if(first == last || _isIllegal(*first))
        return first;
    }

    if(*first == UPPER_L) {
      use_locale = true;
      ++first;
      if(first == last || _isIllegal(*first))
        return first;
    }

    target_type.clear();
    for(; first != last && !_isIllegal(*first); ++first)
      target_type.push_back(*first);
    return first;
  }

  static constexpr const CharT SPACE = static_cast<CharT>(' ');
  static constexpr const CharT LESS_THAN = static_cast<CharT>('<');
  static constexpr const CharT GREATER_THAN = static_cast<CharT>('>');
  static constexpr const CharT CARET = static_cast<CharT>('^');
  static constexpr const CharT PLUS = static_cast<CharT>('+');
  static constexpr const CharT MINUS = static_cast<CharT>('-');
  static constexpr const CharT HASH = static_cast<CharT>('#');
  static constexpr const CharT DOT = static_cast<CharT>('.');
  static constexpr const CharT ZERO = static_cast<CharT>('0');
  static constexpr const CharT NINE = static_cast<CharT>('9');
  static constexpr const CharT UPPER_L = static_cast<CharT>('L');
  static constexpr const CharT LEFT_BRACKET = static_cast<CharT>('{');
  static constexpr const CharT RIGHT_BRACKET = static_cast<CharT>('}');

private:
  static constexpr const size_t _SIZE_LIMIT = (std::numeric_limits<size_t>::max() - 9) / 10;
  static constexpr bool _isIllegal(CharT c) {
    return c == LEFT_BRACKET || c == RIGHT_BRACKET;
  }
};

}  // namespace ul

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
    case ULBN_ERR_NOT_FINITE:
      return "not finite";
    case ULBN_ERR_BAD_ARGUMENT:
      return "bad argument";
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
class Rand {
public:
  using result_type = ulbn_limb_t;

  /* NOTE: This class does not fully meet the requirements of "RandomNumberEngine" (C++11),
    as its initial state created by the default constructor is not the same */
  Rand() noexcept {
    ulbn_rand_init(&_rand);
  }
  explicit Rand(result_type seed) noexcept {
    ulbn_rand_init2(&_rand, static_cast<ulbn_rand_uint_t>(seed));
  }
  template<class SeedSeq>
  explicit Rand(SeedSeq& seq) {
    std::array<uint_least32_t, 1> seed;
    seq.generate(seed.begin(), seed.end());
    ulbn_rand_init2(&_rand, static_cast<ulbn_rand_uint_t>(seed[0]));
  }

  ~Rand() noexcept = default;
  Rand(const Rand& other) noexcept = default;
  Rand(Rand&& other) noexcept = default;
  Rand& operator=(const Rand& other) noexcept = default;
  Rand& operator=(Rand&& other) noexcept = default;

  void seed(result_type seed) noexcept {
    ulbn_rand_init2(&_rand, static_cast<ulbn_rand_uint_t>(seed));
  }
  template<class SeedSeq>
  void seed(SeedSeq& seq) {
    std::array<uint_least32_t, 1> seed;
    seq.generate(seed.begin(), seed.end());
    ulbn_rand_init2(&_rand, static_cast<ulbn_rand_uint_t>(seed[0]));
  }

  #if ULBN_LIMB_MAX < UINT32_MAX
  explicit Rand(ulbn_rand_uint_t seed) noexcept {
    ulbn_rand_init2(&_rand, seed);
  }
  void seed(ulbn_rand_uint_t seed) noexcept {
    ulbn_rand_init2(&_rand, seed);
  }
  #endif

  ulbn_limb_t operator()() noexcept {
    return ulbn_rand_step(&_rand);
  }

  void discard(unsigned long long steps) noexcept {
    ulbn_rand_advance(&_rand, static_cast<ulbn_rand_uint_t>(steps));
  }

  static constexpr ulbn_limb_t min() noexcept {
    return 0;
  }
  static constexpr ulbn_limb_t max() noexcept {
    return std::numeric_limits<ulbn_limb_t>::max();
  }

  friend bool operator==(const Rand& lhs, const Rand& rhs) noexcept {
    return memcmp(&lhs._rand, &rhs._rand, sizeof(ulbn_rand_t)) == 0;
  }
  friend bool operator!=(const Rand& lhs, const Rand& rhs) noexcept {
    return memcmp(&lhs._rand, &rhs._rand, sizeof(ulbn_rand_t)) != 0;
  }

  template<class CharT>
  friend std::basic_ostream<CharT>& operator<<(std::basic_ostream<CharT>& ost, Rand& rng) {
    return ost << rng._rand.state << static_cast<CharT>(' ') << rng._rand.inc;
  }
  template<class CharT>
  friend std::basic_istream<CharT>& operator>>(std::basic_istream<CharT>& ist, Rand& rng) {
    ulbn_rand_uint_t state;
    ulbn_rand_uint_t inc;
    if(ist >> state >> inc) {
      rng._rand.state = state;
      rng._rand.inc = inc;
    }
    return ist;
  }


  ulbn_rand_t* get() noexcept {
    return &_rand;
  }
  const ulbn_rand_t* get() const noexcept {
    return &_rand;
  }

  static Rand& current() noexcept {
    static thread_local Rand rng;
    return rng;
  }

private:
  ulbn_rand_t _rand;
};

static_assert(std::is_standard_layout_v<Rand>);
static_assert(std::is_trivially_copyable_v<Rand>);
static_assert(std::is_trivially_destructible_v<Rand>);
static_assert(std::uniform_random_bit_generator<Rand>);
#endif

inline ulbn_alloc_t* getCurrentAllocator() {
  struct Startup {
    Startup() {
      ulbn_startup();
    }
    Startup(const Startup&) = delete;
    Startup(Startup&&) = delete;
    Startup& operator=(const Startup&) = delete;
    Startup& operator=(Startup&&) = delete;
    ~Startup() = default;
  };
  static const Startup startup;

  static ulbn_alloc_t alloc = *ulbn_default_alloc();
  return &alloc;
}

template<class T>
concept FitSlimb = requires {
  requires std::is_integral_v<T>;
  requires std::is_signed_v<T>;
  requires sizeof(T) <= sizeof(ulbn_slimb_t);
  requires std::is_convertible_v<T, ulbn_slimb_t>;
};
template<class T>
concept FitLimb = requires {
  requires std::is_integral_v<T>;
  requires std::is_unsigned_v<T>;
  requires sizeof(T) <= sizeof(ulbn_limb_t);
  requires std::is_convertible_v<T, ulbn_limb_t>;
};
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
concept FitSlongCase = requires {
  requires FitSlong<T>;
  requires !FitSlimb<T>;
};
template<class T>
concept FitUlongCase = requires {
  requires FitUlong<T>;
  requires !FitLimb<T>;
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
template<class T>
concept FitOutBit = requires {
  requires std::is_integral_v<T>;
  requires std::is_convertible_v<bool, T>;
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

template<class T>
concept IsCharType = requires {
  requires(std::is_same_v<T, char> || std::is_same_v<T, signed char> || std::is_same_v<T, unsigned char>)
            || (std::is_same_v<T, wchar_t> || std::is_same_v<T, char16_t> || std::is_same_v<T, char32_t>)
#if defined(__cpp_char8_t) && __cpp_char8_t >= 201811L
            || (std::is_same_v<T, char8_t>)
#endif
              ;
};


class BigInt {
public:
  BigInt() noexcept = default;
  ~BigInt() noexcept {
    ulbi_deinit(_ctx(), &_val);
  }

  BigInt(const BigInt& other) {
    _check(ulbi_init_copy(_ctx(), &_val, &other._val));
  }
  BigInt(BigInt&& other) noexcept {
    ulbi_init_move(_ctx(), &_val, &other._val);
  }
  BigInt& operator=(const BigInt& other) {
    if(this != &other)  // avoid warnings
      _check(ulbi_set_copy(_ctx(), &_val, &other._val));
    return *this;
  }
  BigInt& operator=(BigInt&& other) noexcept {
    ulbi_set_move(_ctx(), &_val, &other._val);
    return *this;
  }


  template<IsCharType CharT>
    requires(sizeof(CharT) == 1)                                   // char8_t, signed char, char, unsigned char
  BigInt(const CharT* str, size_t len = SIZE_MAX, int base = 0) {  // for C-style string, we needn't know length
    _checkSetString(ulbi_init_string_len(_ctx(), &_val, reinterpret_cast<const char*>(str), len, base));
  }
  template<IsCharType CharT, class StringAllocator>
    requires(sizeof(CharT) == 1)  // char8_t, signed char, char, unsigned char
  BigInt(const std::basic_string<CharT, std::char_traits<CharT>, StringAllocator>& str, int base = 0) {
    _checkSetString(ulbi_init_string_len(_ctx(), &_val, reinterpret_cast<const char*>(str.data()), str.size(), base));
  }
  template<IsCharType CharT>
    requires(sizeof(CharT) == 1)  // char8_t, signed char, char, unsigned char
  BigInt(std::basic_string_view<CharT> str, int base = 0) {
    _checkSetString(ulbi_init_string_len(_ctx(), &_val, reinterpret_cast<const char*>(str.data()), str.size(), base));
  }
  template<IsCharType CharT>
    requires(sizeof(CharT) == 1)         // char8_t, signed char, char, unsigned char
  BigInt& operator=(const CharT* str) {  // for C-style string, we needn't know length
    _checkSetString(ulbi_set_string(_ctx(), &_val, reinterpret_cast<const char*>(str), 0));
    return *this;
  }
  template<IsCharType CharT, class StringAllocator>
    requires(sizeof(CharT) == 1)  // char8_t, signed char, char, unsigned char
  BigInt& operator=(const std::basic_string<CharT, std::char_traits<CharT>, StringAllocator>& str) {
    _checkSetString(ulbi_set_string_len(_ctx(), &_val, reinterpret_cast<const char*>(str.data()), str.size(), 0));
    return *this;
  }
  template<IsCharType CharT>
    requires(sizeof(CharT) == 1)  // char8_t, signed char, char, unsigned char
  BigInt& operator=(std::basic_string_view<CharT> str) {
    _checkSetString(ulbi_set_string_len(_ctx(), &_val, reinterpret_cast<const char*>(str.data()), str.size(), 0));
    return *this;
  }

  template<IsCharType CharT>
    requires(sizeof(CharT) != 1)                                   // wchar_t, char16_t, char32_t
  BigInt(const CharT* str, size_t len = SIZE_MAX, int base = 0) {  // for C-style string, we needn't know length
    std::string str2;
    for(; *str != 0 && len-- != 0; ++str)
      str2.push_back(*str >= 0x7F ? static_cast<char>(0xFF) : static_cast<char>(*str));
    _checkSetString(ulbi_init_string_len(_ctx(), &_val, str2.c_str(), str2.size(), base));
  }
  template<IsCharType CharT, class StringAllocator>
    requires(sizeof(CharT) != 1)  // wchar_t, char16_t, char32_t
  BigInt(const std::basic_string<CharT, std::char_traits<CharT>, StringAllocator>& str, int base = 0) {
    std::string str2;
    for(auto ch: str)
      str2.push_back(ch >= 0x7F ? static_cast<char>(0xFF) : static_cast<char>(ch));
    _checkSetString(ulbi_init_string_len(_ctx(), &_val, str2.data(), str2.size(), base));
  }
  template<IsCharType CharT>
    requires(sizeof(CharT) != 1)  // wchar_t, char16_t, char32_t
  BigInt(std::basic_string_view<CharT> str, int base = 0) {
    std::string str2;
    for(auto ch: str)
      str2.push_back(ch >= 0x7F ? static_cast<char>(0xFF) : static_cast<char>(ch));
    _checkSetString(ulbi_init_string_len(_ctx(), &_val, str2.data(), str2.size(), base));
  }
  template<IsCharType CharT>
    requires(sizeof(CharT) != 1)         // wchar_t, char16_t, char32_t
  BigInt& operator=(const CharT* str) {  // for C-style string, we needn't know length
    std::string str2;
    for(; *str != 0; ++str)
      str2.push_back(*str >= 0x7F ? static_cast<char>(0xFF) : static_cast<char>(*str));
    _checkSetString(ulbi_set_string_len(_ctx(), &_val, str2.c_str(), str2.size(), 0));
    return *this;
  }
  template<IsCharType CharT, class StringAllocator>
    requires(sizeof(CharT) != 1)  // wchar_t, char16_t, char32_t
  BigInt& operator=(const std::basic_string<CharT, std::char_traits<CharT>, StringAllocator>& str) {
    std::string str2;
    for(auto ch: str)
      str2.push_back(ch >= 0x7F ? static_cast<char>(0xFF) : static_cast<char>(ch));
    _checkSetString(ulbi_set_string_len(_ctx(), &_val, str2.data(), str2.size(), 0));
    return *this;
  }
  template<IsCharType CharT>
    requires(sizeof(CharT) != 1)  // wchar_t, char16_t, char32_t
  BigInt& operator=(std::basic_string_view<CharT> str) {
    std::string str2;
    for(auto ch: str)
      str2.push_back(ch >= 0x7F ? static_cast<char>(0xFF) : static_cast<char>(ch));
    _checkSetString(ulbi_set_string_len(_ctx(), &_val, str2.data(), str2.size(), 0));
    return *this;
  }


  BigInt(const ulbi_t* src) {
    if(src)
      _check(ulbi_init_copy(_ctx(), &_val, src));
    else
      ulbi_init(&_val);
  }
  BigInt(const ulbi_t& src) {
    _check(ulbi_init_copy(_ctx(), &_val, &src));
  }
  BigInt& operator=(const ulbi_t* src) {
    if(src)
      _check(ulbi_set_copy(_ctx(), &_val, src));
    else
      ulbi_set_zero(&_val);
    return *this;
  }
  BigInt& operator=(const ulbi_t& src) {
    _check(ulbi_set_copy(_ctx(), &_val, &src));
    return *this;
  }

  template<FitSlimb T>
  BigInt(T value) noexcept {
    ulbi_init_slimb(&_val, static_cast<ulbn_slimb_t>(value));
  }
  template<FitLimb T>
  BigInt(T value) noexcept {
    ulbi_init_limb(&_val, static_cast<ulbn_limb_t>(value));
  }
  template<FitSlimb T>
  BigInt& operator=(T value) noexcept {
    ulbi_set_slimb(&_val, static_cast<ulbn_slimb_t>(value));
    return *this;
  }
  template<FitLimb T>
  BigInt& operator=(T value) noexcept {
    ulbi_set_limb(&_val, static_cast<ulbn_limb_t>(value));
    return *this;
  }

  template<FitSlongCase T>
  BigInt(T value) noexcept {
    ulbi_init_slong(&_val, static_cast<ulbn_slong_t>(value));
  }
  template<FitUlongCase T>
  BigInt(T value) noexcept {
    ulbi_init_ulong(&_val, static_cast<ulbn_ulong_t>(value));
  }
  template<FitSlongCase T>
  BigInt& operator=(T value) noexcept {
    ulbi_set_slong(&_val, static_cast<ulbn_slong_t>(value));
    return *this;
  }
  template<FitUlongCase T>
  BigInt& operator=(T value) noexcept {
    ulbi_set_ulong(&_val, static_cast<ulbn_ulong_t>(value));
    return *this;
  }


  BigInt& moveFrom(ulbi_t* src) noexcept {
    if(src)
      ulbi_set_move(_ctx(), &_val, src);
    else
      ulbi_init(&_val);
    return *this;
  }
  BigInt& moveFrom(ulbi_t& src) noexcept {
    ulbi_set_move(_ctx(), &_val, &src);
    return *this;
  }
  BigInt& moveFrom(BigInt& src) noexcept {
    ulbi_set_move(_ctx(), &_val, &src._val);
    return *this;
  }


  static BigInt fromReserve(ulbn_usize_t n) {
    BigInt ret;
    _check(ulbi_reserve(_ctx(), &ret._val, n));
    return ret;
  }


  template<FitBits T>
  static BigInt from2Exp(T n) {
    BigInt ret;
    _check(ulbi_set_2exp_bits(_ctx(), &ret._val, static_cast<ulbn_bits_t>(n)));
    return ret;
  }
  template<FitSbits T>
  static BigInt from2Exp(T n) {
    BigInt ret;
    _check(ulbi_set_2exp_sbits(_ctx(), &ret._val, static_cast<ulbn_sbits_t>(n)));
    return ret;
  }
  static BigInt from2Exp(const BigInt& n) {
    BigInt ret;
    _check(ulbi_set_2exp(_ctx(), &ret._val, &n._val));
    return ret;
  }


#if ULBN_CONF_USE_RAND
  template<FitBits T>
  static BigInt fromRandom(T n) {
    BigInt ret;
    _check(ulbi_set_rand_bits(_ctx(), Rand::current().get(), &ret._val, static_cast<ulbn_bits_t>(n)));
    return ret;
  }
  template<FitSbits T>
  static BigInt fromRandom(T n) {
    BigInt ret;
    _check(ulbi_set_rand_sbits(_ctx(), Rand::current().get(), &ret._val, static_cast<ulbn_sbits_t>(n)));
    return ret;
  }
  static BigInt fromRandom(const BigInt& n) {
    BigInt ret;
    _check(ulbi_set_rand(_ctx(), Rand::current().get(), &ret._val, &n._val));
    return ret;
  }


  static BigInt fromRandomRange(const BigInt& limit) {
    BigInt ret;
    _check(ulbi_set_rand_range(_ctx(), Rand::current().get(), &ret._val, &limit._val));
    return ret;
  }
  static BigInt fromRandomRange(const BigInt& lo, const BigInt& hi) {
    BigInt ret;
    _check(ulbi_set_rand_range2(_ctx(), Rand::current().get(), &ret._val, &lo._val, &hi._val));
    return ret;
  }
#endif


  static_assert(
    std::endian::native == std::endian::little || std::endian::native == std::endian::big,
    "only little-endian and big-endian supported"
  );
  static BigInt fromBytesUnsigned(const void* bytes, size_t n, bool is_big_endian) {
    BigInt ret;
    _check(ulbi_set_bytes_unsigned(_ctx(), &ret._val, bytes, n, is_big_endian));
    return ret;
  }
  static BigInt fromBytesUnsigned(const void* bytes, size_t n, std::endian endian = std::endian::native) {
    return endian == std::endian::little ? fromBytesUnsignedLE(bytes, n) : fromBytesUnsignedBE(bytes, n);
  }

  static BigInt fromBytesUnsignedLE(const void* bytes, size_t n) {
    BigInt ret;
    _check(ulbi_set_bytes_unsigned_le(_ctx(), &ret._val, bytes, n));
    return ret;
  }
  static BigInt fromBytesUnsignedBE(const void* bytes, size_t n) {
    BigInt ret;
    _check(ulbi_set_bytes_unsigned_be(_ctx(), &ret._val, bytes, n));
    return ret;
  }

  static BigInt fromBytesSigned(const void* bytes, size_t n, bool is_big_endian) {
    BigInt ret;
    _check(ulbi_set_bytes_signed(_ctx(), &ret._val, bytes, n, is_big_endian));
    return ret;
  }
  static BigInt fromBytesSigned(const void* bytes, size_t n, std::endian endian = std::endian::native) {
    return endian == std::endian::little ? fromBytesSignedLE(bytes, n) : fromBytesSignedBE(bytes, n);
  }

  static BigInt fromBytesSignedLE(const void* bytes, size_t n) {
    BigInt ret;
    _check(ulbi_set_bytes_signed_le(_ctx(), &ret._val, bytes, n));
    return ret;
  }
  static BigInt fromBytesSignedBE(const void* bytes, size_t n) {
    BigInt ret;
    _check(ulbi_set_bytes_signed_be(_ctx(), &ret._val, bytes, n));
    return ret;
  }


  void toBytesSigned(void* bytes, size_t n, bool is_big_endian) const noexcept {
    ulbi_to_bytes_signed(&_val, bytes, n, is_big_endian);
  }
  void toBytesSigned(void* bytes, size_t n, std::endian endian = std::endian::native) const noexcept {
    if(endian == std::endian::little)
      ulbi_to_bytes_signed_le(&_val, bytes, n);
    else
      ulbi_to_bytes_signed_be(&_val, bytes, n);
  }

  void toBytesSignedLE(void* bytes, size_t n) const noexcept {
    ulbi_to_bytes_signed_le(&_val, bytes, n);
  }
  void toBytesSignedBE(void* bytes, size_t n) const noexcept {
    ulbi_to_bytes_signed_be(&_val, bytes, n);
  }


  std::span<const ulbn_limb_t> limbs() const noexcept {
    return { ulbi_get_limbs(&_val), ulbi_get_limbs_len(&_val) };
  }

  template<size_t Extent>
  static BigInt fromLimbs(std::span<const ulbn_limb_t, Extent> limbs) {
    BigInt ret;
    _check(ulbi_set_limbs(_ctx(), &ret._val, limbs.data(), limbs.size()));
    return ret;
  }
  BigInt fromLimbs(const ulbn_limb_t* limbs, size_t len) {
    BigInt ret;
    _check(ulbi_set_limbs(_ctx(), &ret._val, limbs, len));
    return ret;
  }


  template<IsCharType CharT>
    requires(sizeof(CharT) == 1)  // char8_t, signed char, char, unsigned char
  static BigInt fromString(
    const CharT* str, size_t len = SIZE_MAX, int base = 0, int flags = ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX
  ) {
    BigInt ret;
    const char* ptr = reinterpret_cast<const char*>(str);
    _check(ulbi_set_string_ex(_ctx(), &ret._val, &ptr, len, base, flags));
    return ret;
  }
  template<IsCharType CharT, class StringAllocator>
    requires(sizeof(CharT) == 1)  // char8_t, signed char, char, unsigned char
  static BigInt fromString(
    const std::basic_string<CharT, std::char_traits<CharT>, StringAllocator>& str, int base = 0,
    int flags = ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX
  ) {
    return fromString(str.data(), str.size(), base, flags);
  }
  template<IsCharType CharT>
    requires(sizeof(CharT) == 1)  // char8_t, signed char, char, unsigned char
  static BigInt fromString(
    std::basic_string_view<CharT> str, int base = 0, int flags = ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX
  ) {
    return fromString(str.data(), str.size(), base, flags);
  }
  template<IsCharType CharT, size_t Extent>
    requires(sizeof(CharT) == 1)  // char8_t, signed char, char, unsigned char
  static BigInt fromString(
    std::span<const CharT, Extent> str, int base = 0, int flag = ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX
  ) {
    return fromString(str.data(), str.size(), base, flag);
  }

  template<IsCharType CharT>
    requires(sizeof(CharT) != 1)  // wchar_t, char16_t, char32_t
  static BigInt fromString(
    const CharT* str, size_t len = SIZE_MAX, int base = 0, int flags = ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX
  ) {
    BigInt ret;
    std::string str2;
    for(; *str != 0 && len-- != 0; ++str)
      str2.push_back(*str >= 0x7F ? static_cast<char>(0xFF) : static_cast<char>(*str));
    const char* ptr = str2.c_str();
    _check(ulbi_set_string_ex(_ctx(), &ret._val, &ptr, str2.size(), base, flags));
    return ret;
  }
  template<IsCharType CharT, class StringAllocator>
    requires(sizeof(CharT) != 1)  // wchar_t, char16_t, char32_t
  static BigInt fromString(
    const std::basic_string<CharT, std::char_traits<CharT>, StringAllocator>& str, int base = 0,
    int flags = ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX
  ) {
    return fromString(str.data(), str.size(), base, flags);
  }
  template<IsCharType CharT>
    requires(sizeof(CharT) != 1)  // wchar_t, char16_t, char32_t
  static BigInt fromString(
    std::basic_string_view<CharT> str, int base = 0, int flags = ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX
  ) {
    return fromString(str.data(), str.size(), base, flags);
  }
  template<IsCharType CharT, size_t Extent>
    requires(sizeof(CharT) != 1)  // wchar_t, char16_t, char32_t
  static BigInt fromString(
    std::span<const CharT, Extent> str, int base = 0, int flag = ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX
  ) {
    return fromString(str.data(), str.size(), base, flag);
  }


  BigInt& operator+=(const BigInt& other) {
    _check(ulbi_add(_ctx(), &_val, &_val, &other._val));
    return *this;
  }
  template<FitLimb T>
  BigInt& operator+=(T value) {
    _check(ulbi_add_limb(_ctx(), &_val, &_val, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator+=(T value) {
    _check(ulbi_add_slimb(_ctx(), &_val, &_val, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }

  friend BigInt operator+(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_add(_ctx(), &ret._val, &lhs._val, &rhs._val));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator+(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_add_limb(_ctx(), &ret._val, &lhs._val, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator+(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_add_slimb(_ctx(), &ret._val, &lhs._val, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator+(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_add_limb(_ctx(), &ret._val, &rhs._val, static_cast<ulbn_limb_t>(lhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator+(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_add_slimb(_ctx(), &ret._val, &rhs._val, static_cast<ulbn_slimb_t>(lhs)));
    return ret;
  }


  BigInt& operator-=(const BigInt& other) {
    _check(ulbi_sub(_ctx(), &_val, &_val, &other._val));
    return *this;
  }
  template<FitLimb T>
  BigInt& operator-=(T value) {
    _check(ulbi_sub_limb(_ctx(), &_val, &_val, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator-=(T value) {
    _check(ulbi_sub_slimb(_ctx(), &_val, &_val, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }

  friend BigInt operator-(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_sub(_ctx(), &ret._val, &lhs._val, &rhs._val));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator-(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_sub_limb(_ctx(), &ret._val, &lhs._val, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator-(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_sub_slimb(_ctx(), &ret._val, &lhs._val, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator-(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_limb_sub(_ctx(), &ret._val, static_cast<ulbn_limb_t>(lhs), &rhs._val));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator-(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_slimb_sub(_ctx(), &ret._val, static_cast<ulbn_slimb_t>(lhs), &rhs._val));
    return ret;
  }


  BigInt& operator++() {
    _check(ulbi_add_limb(_ctx(), &_val, &_val, 1));
    return *this;
  }
  BigInt operator++(int) {
    BigInt ret(*this);
    _check(ulbi_add_limb(_ctx(), &_val, &_val, 1));
    return ret;
  }
  BigInt& operator--() {
    _check(ulbi_sub_limb(_ctx(), &_val, &_val, 1));
    return *this;
  }
  BigInt operator--(int) {
    BigInt ret(*this);
    _check(ulbi_sub_limb(_ctx(), &_val, &_val, 1));
    return ret;
  }


  BigInt operator+() const {
    return *this;
  }
  BigInt operator-() const {
    BigInt ret;
    _check(ulbi_neg(_ctx(), &ret._val, &_val));
    return ret;
  }
  BigInt abs() const {
    BigInt ret;
    _check(ulbi_abs(_ctx(), &ret._val, &_val));
    return ret;
  }

  BigInt& negLoc() {
    _check(ulbi_neg(_ctx(), &_val, &_val));
    return *this;
  }
  BigInt& absLoc() {
    _check(ulbi_abs(_ctx(), &_val, &_val));
    return *this;
  }


  BigInt& operator*=(const BigInt& other) {
    _check(ulbi_mul(_ctx(), &_val, &_val, &other._val));
    return *this;
  }
  friend BigInt operator*(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_mul(_ctx(), &ret._val, &lhs._val, &rhs._val));
    return ret;
  }

  template<FitLimb T>
  BigInt& operator*=(T value) {
    _check(ulbi_mul_limb(_ctx(), &_val, &_val, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator*=(T value) {
    _check(ulbi_mul_slimb(_ctx(), &_val, &_val, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }
  template<FitLimb T>
  friend BigInt operator*(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_mul_limb(_ctx(), &ret._val, &lhs._val, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator*(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_mul_slimb(_ctx(), &ret._val, &lhs._val, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator*(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_mul_limb(_ctx(), &ret._val, &rhs._val, static_cast<ulbn_limb_t>(lhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator*(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_mul_slimb(_ctx(), &ret._val, &rhs._val, static_cast<ulbn_slimb_t>(lhs)));
    return ret;
  }


  BigInt& operator/=(const BigInt& other) {
    _check(ulbi_divmod(_ctx(), &_val, nullptr, &_val, &other._val));
    return *this;
  }
  template<FitLimb T>
  BigInt& operator/=(T value) {
    _check(ulbi_divmod_limb(_ctx(), &_val, nullptr, &_val, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator/=(T value) {
    _check(ulbi_divmod_slimb(_ctx(), &_val, nullptr, &_val, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }
  friend BigInt operator/(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_divmod(_ctx(), &ret._val, nullptr, &lhs._val, &rhs._val));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator/(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_divmod_limb(_ctx(), &ret._val, nullptr, &lhs._val, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator/(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_divmod_slimb(_ctx(), &ret._val, nullptr, &lhs._val, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }

  BigInt& operator%=(const BigInt& other) {
    _check(ulbi_divmod(_ctx(), nullptr, &_val, &_val, &other._val));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator%=(T value) noexcept {
    ulbn_slimb_t r;
    ulbi_divmod_slimb(_ctx(), nullptr, &r, &_val, static_cast<ulbn_slimb_t>(value));
    ulbi_set_slimb(&_val, r);
    return *this;
  }
  friend BigInt operator%(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_divmod(_ctx(), nullptr, &ret._val, &lhs._val, &rhs._val));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator%(const BigInt& lhs, T rhs) {
    ulbn_slimb_t r;
    _check(ulbi_divmod_slimb(_ctx(), nullptr, &r, &lhs._val, static_cast<ulbn_slimb_t>(rhs)));
    return r;
  }

  std::pair<BigInt, BigInt> divmod(const BigInt& other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT)
    const {
    BigInt q, r;
    const int err = ulbi_divmod_ex(_ctx(), &q._val, &r._val, &_val, &other._val, round_mode);
    _checkDivmodEx(err);
    return { q, r };
  }
  BigInt div(const BigInt& other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt q;
    const int err = ulbi_divmod_ex(_ctx(), &q._val, nullptr, &_val, &other._val, round_mode);
    _checkDivmodEx(err);
    return q;
  }
  BigInt mod(const BigInt& other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt r;
    const int err = ulbi_divmod_ex(_ctx(), nullptr, &r._val, &_val, &other._val, round_mode);
    _checkDivmodEx(err);
    return r;
  }

  template<FitSlimb T>
  std::pair<BigInt, BigInt> divmod(T other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt q;
    ulbn_slimb_t rl;
    _checkDivmodEx(ulbi_divmod_slimb_ex(_ctx(), &q._val, &rl, &_val, static_cast<ulbn_slimb_t>(other), round_mode));
    return { q, BigInt(rl) };
  }
  template<FitSlimb T>
  BigInt div(T other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt q;
    _checkDivmodEx(ulbi_divmod_slimb_ex(_ctx(), &q._val, nullptr, &_val, static_cast<ulbn_slimb_t>(other), round_mode));
    return q;
  }
  template<FitSlimb T>
  BigInt mod(T other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    ulbn_slimb_t rl;
    _checkDivmodEx(ulbi_divmod_slimb_ex(_ctx(), nullptr, &rl, &_val, static_cast<ulbn_slimb_t>(other), round_mode));
    return rl;
  }

  bool isDivisible(const BigInt& other) const noexcept {
    return ulbi_divmod(_ctx(), nullptr, nullptr, &_val, &other._val) != ULBN_ERR_INEXACT;
  }
  template<FitLimb T>
  bool isDivisible(T value) const noexcept {
    return ulbi_divmod_limb(_ctx(), nullptr, nullptr, &_val, static_cast<ulbn_limb_t>(value)) != ULBN_ERR_INEXACT;
  }
  template<FitSlimb T>
  bool isDivisible(T value) const noexcept {
    return ulbi_divmod_slimb(_ctx(), nullptr, nullptr, &_val, static_cast<ulbn_slimb_t>(value)) != ULBN_ERR_INEXACT;
  }


  template<FitBits T>
  std::pair<BigInt, BigInt> divmod2Exp(T n, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt q, r;
    _checkDivmodEx(ulbi_divmod_2exp_bits_ex(_ctx(), &q._val, &r._val, &_val, static_cast<ulbn_bits_t>(n), round_mode));
    return { q, r };
  }
  template<FitSbits T>
  std::pair<BigInt, BigInt> divmod2Exp(T n, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt q, r;
    _checkDivmodEx(ulbi_divmod_2exp_sbits_ex(_ctx(), &q._val, &r._val, &_val, static_cast<ulbn_sbits_t>(n), round_mode)
    );
    return { q, r };
  }
  std::pair<BigInt, BigInt> divmod2Exp(
    const BigInt& other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT
  ) const {
    BigInt q, r;
    _checkDivmodEx(ulbi_divmod_2exp_ex(_ctx(), &q._val, &r._val, &_val, &other._val, round_mode));
    return { q, r };
  }

  template<FitBits T>
  BigInt div2Exp(T n, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt q;
    _checkDivmodEx(ulbi_divmod_2exp_bits_ex(_ctx(), &q._val, ul_nullptr, &_val, static_cast<ulbn_bits_t>(n), round_mode)
    );
    return q;
  }
  template<FitSbits T>
  BigInt div2Exp(T n, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt q;
    _checkDivmodEx(
      ulbi_divmod_2exp_sbits_ex(_ctx(), &q._val, ul_nullptr, &_val, static_cast<ulbn_sbits_t>(n), round_mode)
    );
    return q;
  }
  BigInt div2Exp(const BigInt& other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt q;
    _checkDivmodEx(ulbi_divmod_2exp_ex(_ctx(), &q._val, ul_nullptr, &_val, &other._val, round_mode));
    return q;
  }

  template<FitBits T>
  BigInt mod2Exp(T n, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt r;
    _checkDivmodEx(ulbi_divmod_2exp_bits_ex(_ctx(), ul_nullptr, &r._val, &_val, static_cast<ulbn_bits_t>(n), round_mode)
    );
    return r;
  }
  template<FitSbits T>
  BigInt mod2Exp(T n, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt r;
    _checkDivmodEx(
      ulbi_divmod_2exp_sbits_ex(_ctx(), ul_nullptr, &r._val, &_val, static_cast<ulbn_sbits_t>(n), round_mode)
    );
    return r;
  }
  BigInt mod2Exp(const BigInt& other, enum ULBN_ROUND_ENUM round_mode = ULBN_ROUND_BIG_INT_DEFAULT) const {
    BigInt r;
    _checkDivmodEx(ulbi_divmod_2exp_ex(_ctx(), ul_nullptr, &r._val, &_val, &other._val, round_mode));
    return r;
  }


  template<FitBits T>
  bool is2ExpDivisible(T n) const {
    return ulbi_divmod_2exp_bits(_ctx(), nullptr, nullptr, &_val, static_cast<ulbn_bits_t>(n)) != ULBN_ERR_INEXACT;
  }
  template<FitSbits T>
  bool is2ExpDivisible(T n) const {
    return ulbi_divmod_2exp_sbits(_ctx(), nullptr, nullptr, &_val, static_cast<ulbn_sbits_t>(n)) != ULBN_ERR_INEXACT;
  }
  bool is2ExpDivisible(const BigInt& other) const {
    return ulbi_divmod_2exp(_ctx(), nullptr, nullptr, &_val, &other._val) != ULBN_ERR_INEXACT;
  }


  friend std::strong_ordering operator<=>(const BigInt& lhs, const BigInt& rhs) noexcept {
    return ulbi_comp(&lhs._val, &rhs._val) <=> 0;
  }

  template<FitLimb T>
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) noexcept {
    return ulbi_comp_limb(&lhs._val, static_cast<ulbn_limb_t>(rhs)) <=> 0;
  }
  template<FitSlimb T>
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) noexcept {
    return ulbi_comp_slimb(&lhs._val, static_cast<ulbn_slimb_t>(rhs)) <=> 0;
  }
  template<FitUlongCase T>
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) noexcept {
    return ulbi_comp_ulong(&lhs._val, static_cast<ulbn_ulong_t>(rhs)) <=> 0;
  }
  template<FitSlongCase T>
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) noexcept {
    return ulbi_comp_slong(&lhs._val, static_cast<ulbn_slong_t>(rhs)) <=> 0;
  }

  template<FitLimb T>
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) noexcept {
    return (-ulbi_comp_limb(&rhs._val, static_cast<ulbn_limb_t>(lhs))) <=> 0;
  }
  template<FitSlimb T>
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) noexcept {
    return (-ulbi_comp_slimb(&rhs._val, static_cast<ulbn_slimb_t>(lhs))) <=> 0;
  }
  template<FitUlongCase T>
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) noexcept {
    return (-ulbi_comp_ulong(&rhs._val, static_cast<ulbn_ulong_t>(lhs))) <=> 0;
  }
  template<FitSlongCase T>
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) noexcept {
    return (-ulbi_comp_slong(&rhs._val, static_cast<ulbn_slong_t>(lhs))) <=> 0;
  }


  friend bool operator==(const BigInt& lhs, const BigInt& rhs) noexcept {
    return ulbi_eq(&lhs._val, &rhs._val) != 0;
  }

  template<FitLimb T>
  friend bool operator==(const BigInt& lhs, T rhs) noexcept {
    return ulbi_eq_limb(&lhs._val, static_cast<ulbn_limb_t>(rhs)) != 0;
  }
  template<FitSlimb T>
  friend bool operator==(const BigInt& lhs, T rhs) noexcept {
    return ulbi_eq_slimb(&lhs._val, static_cast<ulbn_slimb_t>(rhs)) != 0;
  }
  template<FitUlongCase T>
  friend bool operator==(const BigInt& lhs, T rhs) noexcept {
    return ulbi_eq_ulong(&lhs._val, static_cast<ulbn_ulong_t>(rhs)) != 0;
  }
  template<FitSlongCase T>
  friend bool operator==(const BigInt& lhs, T rhs) noexcept {
    return ulbi_eq_slong(&lhs._val, static_cast<ulbn_slong_t>(rhs)) != 0;
  }

  template<FitLimb T>
  friend bool operator==(T lhs, const BigInt& rhs) noexcept {
    return ulbi_eq_limb(&rhs._val, static_cast<ulbn_limb_t>(lhs)) != 0;
  }
  template<FitSlimb T>
  friend bool operator==(T lhs, const BigInt& rhs) noexcept {
    return ulbi_eq_slimb(&rhs._val, static_cast<ulbn_slimb_t>(lhs)) != 0;
  }
  template<FitUlongCase T>
  friend bool operator==(T lhs, const BigInt& rhs) noexcept {
    return ulbi_eq_ulong(&rhs._val, static_cast<ulbn_ulong_t>(lhs)) != 0;
  }
  template<FitSlongCase T>
  friend bool operator==(T lhs, const BigInt& rhs) noexcept {
    return ulbi_eq_slong(&rhs._val, static_cast<ulbn_slong_t>(lhs)) != 0;
  }


  explicit operator bool() const noexcept {
    return !ulbi_is_zero(&_val);
  }
  bool operator!() const noexcept {
    return ulbi_is_zero(&_val) != 0;
  }


  BigInt& operator&=(const BigInt& other) {
    _check(ulbi_and(_ctx(), &_val, &_val, &other._val));
    return *this;
  }
  BigInt& operator|=(const BigInt& other) {
    _check(ulbi_or(_ctx(), &_val, &_val, &other._val));
    return *this;
  }
  BigInt& operator^=(const BigInt& other) {
    _check(ulbi_xor(_ctx(), &_val, &_val, &other._val));
    return *this;
  }
  friend BigInt operator&(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_and(_ctx(), &ret._val, &lhs._val, &rhs._val));
    return ret;
  }
  friend BigInt operator|(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_or(_ctx(), &ret._val, &lhs._val, &rhs._val));
    return ret;
  }
  friend BigInt operator^(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_xor(_ctx(), &ret._val, &lhs._val, &rhs._val));
    return ret;
  }

  BigInt operator~() const {
    BigInt ret;
    _check(ulbi_com(_ctx(), &ret._val, &_val));
    return ret;
  }

  template<FitBits T>
  BigInt& operator<<=(T shift) {
    _check(ulbi_sal_bits(_ctx(), &_val, &_val, static_cast<ulbn_bits_t>(shift)));
    return *this;
  }
  template<FitSbits T>
  BigInt& operator<<=(T shift) {
    _check(ulbi_sal_sbits(_ctx(), &_val, &_val, static_cast<ulbn_sbits_t>(shift)));
    return *this;
  }
  BigInt& operator<<=(const BigInt& shift) {
    _check(ulbi_sal(_ctx(), &_val, &_val, &shift._val));
    return *this;
  }
  template<FitBits T>
  friend BigInt operator<<(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sal_bits(_ctx(), &ret._val, &lhs._val, static_cast<ulbn_bits_t>(shift)));
    return ret;
  }
  template<FitSbits T>
  friend BigInt operator<<(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sal_sbits(_ctx(), &ret._val, &lhs._val, static_cast<ulbn_sbits_t>(shift)));
    return ret;
  }
  friend BigInt operator<<(const BigInt& lhs, const BigInt& shift) {
    BigInt ret;
    _check(ulbi_sal(_ctx(), &ret._val, &lhs._val, &shift._val));
    return ret;
  }

  template<FitBits T>
  BigInt& operator>>=(T shift) {
    _check(ulbi_sar_bits(_ctx(), &_val, &_val, static_cast<ulbn_bits_t>(shift)));
    return *this;
  }
  template<FitSbits T>
  BigInt& operator>>=(T shift) {
    _check(ulbi_sar_sbits(_ctx(), &_val, &_val, static_cast<ulbn_sbits_t>(shift)));
    return *this;
  }
  BigInt& operator>>=(const BigInt& shift) {
    _check(ulbi_sar(_ctx(), &_val, &_val, &shift._val));
    return *this;
  }
  template<FitBits T>
  friend BigInt operator>>(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sar_bits(_ctx(), &ret._val, &lhs._val, static_cast<ulbn_bits_t>(shift)));
    return ret;
  }
  template<FitSbits T>
  friend BigInt operator>>(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sar_sbits(_ctx(), &ret._val, &lhs._val, static_cast<ulbn_sbits_t>(shift)));
    return ret;
  }
  friend BigInt operator>>(const BigInt& lhs, const BigInt& shift) {
    BigInt ret;
    _check(ulbi_sar(_ctx(), &ret._val, &lhs._val, &shift._val));
    return ret;
  }


  template<FitUlong T>
  BigInt pow(T e) const {
    BigInt ret;
    _check(ulbi_pow_ulong(_ctx(), &ret._val, &_val, static_cast<ulbn_ulong_t>(e)));
    return ret;
  }
  template<FitSlong T>
  BigInt pow(T e) const {
    BigInt ret;
    _check(ulbi_pow_slong(_ctx(), &ret._val, &_val, static_cast<ulbn_slong_t>(e)));
    return ret;
  }
  BigInt pow(const BigInt& e) const {
    BigInt ret;
    _check(ulbi_pow(_ctx(), &ret._val, &_val, &e._val));
    return ret;
  }
  BigInt sqrt() const {
    BigInt ret;
    const int err = ulbi_sqrt(_ctx(), &ret._val, &_val);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the value is negative");
    _check(err);
    return ret;
  }
  std::pair<BigInt, BigInt> sqrtrem() const {
    BigInt q, r;
    const int err = ulbi_sqrtrem(_ctx(), &q._val, &r._val, &_val);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the value is negative");
    _check(err);
    return { q, r };
  }
  BigInt root(const BigInt& e) const {
    BigInt ret;
    const int err = ulbi_root(_ctx(), &ret._val, &_val, &e._val);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the result is illegal");
    _check(err);
    return ret;
  }
  std::pair<BigInt, BigInt> rootrem(const BigInt& e) const {
    BigInt q, r;
    const int err = ulbi_rootrem(_ctx(), &q._val, &r._val, &_val, &e._val);
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the result is illegal");
    _check(err);
    return { q, r };
  }


  BigInt& shrink() {
    _check(ulbi_shrink(_ctx(), &_val));
    return *this;
  }
  BigInt& reserve(ulbn_usize_t n) {
    _check(ulbi_reserve(_ctx(), &_val, n));
    return *this;
  }


  BigInt& swap(BigInt& other) noexcept {
    ulbi_swap(&_val, &other._val);
    return *this;
  }


  bool isZero() const noexcept {
    return ulbi_is_zero(&_val) != 0;
  }
  bool isOdd() const noexcept {
    return ulbi_is_odd(&_val) != 0;
  }
  bool isEven() const noexcept {
    return ulbi_is_even(&_val) != 0;
  }
  int sign() const noexcept {
    return ulbi_sign(&_val);
  }


  bool fitSlimb() const noexcept {
    return ulbi_fit_slimb(&_val) != 0;
  }
  bool fitLimb() const noexcept {
    return ulbi_fit_limb(&_val) != 0;
  }
  bool fitSlong() const noexcept {
    return ulbi_fit_slong(&_val) != 0;
  }
  bool fitUlong() const noexcept {
    return ulbi_fit_ulong(&_val) != 0;
  }


  ulbn_slimb_t toSlimb() const noexcept {
    return ulbi_to_slimb(&_val);
  }
  ulbn_limb_t toLimb() const noexcept {
    return ulbi_to_limb(&_val);
  }
  ulbn_slong_t toSlong() const noexcept {
    return ulbi_to_slong(&_val);
  }
  ulbn_ulong_t toUlong() const noexcept {
    return ulbi_to_ulong(&_val);
  }


  template<FitSlimb T>
  explicit operator T() const noexcept {
    return static_cast<T>(toSlimb());
  }
  template<FitLimb T>
  explicit operator T() const noexcept {
    return static_cast<T>(toLimb());
  }
  template<FitSlongCase T>
  explicit operator T() const noexcept {
    return static_cast<T>(toSlong());
  }
  template<FitUlongCase T>
  explicit operator T() const noexcept {
    return static_cast<T>(toUlong());
  }


  template<IsCharType CharT = char, class StringAllocator = std::allocator<CharT>>
  auto toString(int base = 10) const {
    std::basic_string<CharT, std::char_traits<CharT>, StringAllocator> ret;
    toString(ret, base);
    return ret;
  }
  template<IsCharType CharT = char, class StringAllocator>
    requires(sizeof(CharT) == 1)
  auto& toString(std::basic_string<CharT, std::char_traits<CharT>, StringAllocator>& dst, int base = 10) const {
    using String = std::basic_string<CharT, std::char_traits<CharT>, StringAllocator>;
    Wrapper<String&> wrapper(dst);
    dst.clear();
    const int err = ulbi_print_ex(
      _ctx(),
      [](void* opaque, const char* str, size_t len) -> int {
        return reinterpret_cast<Wrapper<String&>*>(opaque)->call([&](String& s) {
          s.append(reinterpret_cast<std::add_const_t<CharT>*>(str), len);
        });
      },
      &wrapper, &_val, base
    );
    return wrapper.check(err);
  }
  template<IsCharType CharT = char, class StringAllocator>
    requires(sizeof(CharT) != 1)
  auto& toString(std::basic_string<CharT, std::char_traits<CharT>, StringAllocator>& dst, int base = 10) const {
    using String = std::basic_string<CharT, std::char_traits<CharT>, StringAllocator>;
    Wrapper<String&> wrapper(dst);
    dst.clear();
    const int err = ulbi_print_ex(
      _ctx(),
      [](void* opaque, const char* str, size_t len) -> int {
        return reinterpret_cast<Wrapper<String&>*>(opaque)->call([&](String& s) {
          while(len-- != 0)
            s.push_back(static_cast<CharT>(*str++));
        });
      },
      &wrapper, &_val, base
    );
    return wrapper.check(err);
  }

  template<IsCharType CharT = char>
  friend std::basic_ostream<CharT>& operator<<(std::basic_ostream<CharT>& ost, const BigInt& value) {
    value.print(ost);
    return ost;
  }

  void print(FILE* fp, int base = 10) const {
    _check(ulbi_print(_ctx(), fp, &_val, base));
  }
  template<IsCharType CharT = char>
  std::basic_ostream<CharT>& print(std::basic_ostream<CharT>& ost, int base = 0) const {
    Formatter<CharT> formatter;
    formatter.parse(ost, base);
    formatter.format(std::ostream_iterator<CharT, CharT>(ost), *this);
    return ost;
  }
  template<class Iter>
    requires(std::input_or_output_iterator<Iter> && IsCharType<std::iter_value_t<Iter>>)
  Iter print(Iter iter, int base = 10) const {
    Wrapper<Iter&> wrapper(iter);
    int err = ulbi_print_ex(
      _ctx(),
      [](void* opaque, const char* ptr, size_t len) -> int {
        return reinterpret_cast<Wrapper<Iter&>*>(opaque)->call([&](Iter& itr) { std::copy_n(ptr, len, itr); });
      },
      &wrapper, &_val, base
    );
    return wrapper.check(err);
  }


  ulbi_t* get() noexcept {
    return &_val;
  }
  const ulbi_t* get() const noexcept {
    return &_val;
  }


  template<FitBits T>
  bool testBit(T n) const noexcept {
    return ulbi_testbit_bits(&_val, static_cast<ulbn_bits_t>(n)) != 0;
  }
  template<FitSbits T>
  bool testBit(T n) const noexcept {
    return ulbi_testbit_sbits(&_val, static_cast<ulbn_sbits_t>(n)) != 0;
  }
  bool testBit(const BigInt& n) const noexcept {
    return ulbi_testbit(&_val, &n._val) != 0;
  }


  template<FitBits T>
  BigInt& setBit(T n) {
    _check(ulbi_setbit_bits(_ctx(), &_val, static_cast<ulbn_bits_t>(n)));
    return *this;
  }
  template<FitSbits T>
  BigInt& setBit(T n) {
    _check(ulbi_setbit_sbits(_ctx(), &_val, static_cast<ulbn_sbits_t>(n)));
    return *this;
  }
  BigInt& setBit(const BigInt& n) {
    _check(ulbi_setbit(_ctx(), &_val, &n._val));
    return *this;
  }

  template<FitBits T, FitOutBit OutBit>
  BigInt& setBit(T n, OutBit& oldValue) {
    oldValue = static_cast<bool>(_check(ulbi_setbit_bits(_ctx(), &_val, static_cast<ulbn_bits_t>(n))));
    return *this;
  }
  template<FitSbits T, FitOutBit OutBit>
  BigInt& setBit(T n, OutBit& oldValue) {
    oldValue = static_cast<bool>(_check(ulbi_setbit_sbits(_ctx(), &_val, static_cast<ulbn_sbits_t>(n))));
    return *this;
  }
  template<FitOutBit OutBit>
  BigInt& setBit(const BigInt& n, OutBit& oldValue) {
    oldValue = static_cast<bool>(_check(ulbi_setbit(_ctx(), &_val, &n._val)));
    return *this;
  }


  template<FitBits T>
  BigInt& resetBit(T n) {
    _check(ulbi_resetbit_bits(_ctx(), &_val, static_cast<ulbn_bits_t>(n)));
    return *this;
  }
  template<FitSbits T>
  BigInt& resetBit(T n) {
    _check(ulbi_resetbit_sbits(_ctx(), &_val, static_cast<ulbn_sbits_t>(n)));
    return *this;
  }
  BigInt& resetBit(const BigInt& n) {
    _check(ulbi_resetbit(_ctx(), &_val, &n._val));
    return *this;
  }

  template<FitBits T, FitOutBit OutBit>
  BigInt& resetBit(T n, OutBit& oldValue) {
    oldValue = static_cast<bool>(_check(ulbi_resetbit_bits(_ctx(), &_val, static_cast<ulbn_bits_t>(n))));
    return *this;
  }
  template<FitSbits T, FitOutBit OutBit>
  BigInt& resetBit(T n, OutBit& oldValue) {
    oldValue = static_cast<bool>(_check(ulbi_resetbit_sbits(_ctx(), &_val, static_cast<ulbn_sbits_t>(n))));
    return *this;
  }
  template<FitOutBit OutBit>
  BigInt& resetBit(const BigInt& n, OutBit& oldValue) {
    oldValue = static_cast<bool>(_check(ulbi_resetbit(_ctx(), &_val, &n._val)));
    return *this;
  }


  template<FitBits T>
  BigInt& comBit(T n) {
    _check(ulbi_combit_bits(_ctx(), &_val, static_cast<ulbn_bits_t>(n)));
    return *this;
  }
  template<FitSbits T>
  BigInt& comBit(T n) {
    _check(ulbi_combit_sbits(_ctx(), &_val, static_cast<ulbn_sbits_t>(n)));
    return *this;
  }
  BigInt& comBit(const BigInt& n) {
    _check(ulbi_combit(_ctx(), &_val, &n._val));
    return *this;
  }

  template<FitBits T, FitOutBit OutBit>
  BigInt& comBit(T n, OutBit& oldValue) {
    oldValue = static_cast<bool>(_check(ulbi_combit_bits(_ctx(), &_val, static_cast<ulbn_bits_t>(n))));
    return *this;
  }
  template<FitSbits T, FitOutBit OutBit>
  BigInt& comBit(T n, OutBit& oldValue) {
    oldValue = static_cast<bool>(_check(ulbi_combit_sbits(_ctx(), &_val, static_cast<ulbn_sbits_t>(n))));
    return *this;
  }
  template<FitOutBit OutBit>
  BigInt& comBit(const BigInt& n, OutBit& oldValue) {
    oldValue = static_cast<bool>(_check(ulbi_combit(_ctx(), &_val, &n._val)));
    return *this;
  }


  template<FitUsize T>
  BigInt asUint(T n) const {
    BigInt ret;
    _check(ulbi_as_uint_usize(_ctx(), &ret._val, &_val, static_cast<ulbn_usize_t>(n)));
    return ret;
  }
  template<FitSsize T>
  BigInt asUint(T n) const {
    BigInt ret;
    _check(ulbi_as_uint_ssize(_ctx(), &ret._val, &_val, static_cast<ulbn_ssize_t>(n)));
    return ret;
  }
  template<FitBits T>
    requires(!FitUsize<T>)
  BigInt asUint(T n) const {
    BigInt ret;
    _check(ulbi_as_uint_bits(_ctx(), &ret._val, &_val, static_cast<ulbn_bits_t>(n)));
    return ret;
  }
  template<FitSbits T>
    requires(!FitSsize<T>)
  BigInt asUint(T n) const {
    BigInt ret;
    _check(ulbi_as_uint_sbits(_ctx(), &ret._val, &_val, static_cast<ulbn_sbits_t>(n)));
    return ret;
  }
  BigInt asUint(const BigInt& n) const {
    BigInt ret;
    _check(ulbi_as_uint(_ctx(), &ret._val, &_val, &n._val));
    return ret;
  }

  template<FitUsize T>
  BigInt& asUintLoc(T n) {
    _check(ulbi_as_uint_usize(_ctx(), &_val, &_val, static_cast<ulbn_usize_t>(n)));
    return *this;
  }
  template<FitSsize T>
  BigInt& asUintLoc(T n) {
    _check(ulbi_as_uint_ssize(_ctx(), &_val, &_val, static_cast<ulbn_ssize_t>(n)));
    return *this;
  }
  template<FitBits T>
    requires(!FitUsize<T>)
  BigInt& asUintLoc(T n) {
    _check(ulbi_as_uint_bits(_ctx(), &_val, &_val, static_cast<ulbn_bits_t>(n)));
    return *this;
  }
  template<FitSbits T>
    requires(!FitSsize<T>)
  BigInt& asUintLoc(T n) {
    _check(ulbi_as_uint_sbits(_ctx(), &_val, &_val, static_cast<ulbn_sbits_t>(n)));
    return *this;
  }
  BigInt& asUintLoc(const BigInt& n) {
    _check(ulbi_as_uint(_ctx(), &_val, &_val, &n._val));
    return *this;
  }


  template<FitUsize T>
  BigInt asInt(T n) const {
    BigInt ret;
    _check(ulbi_as_int_usize(_ctx(), &ret._val, &_val, static_cast<ulbn_usize_t>(n)));
    return ret;
  }
  template<FitSsize T>
  BigInt asInt(T n) const {
    BigInt ret;
    _check(ulbi_as_int_ssize(_ctx(), &ret._val, &_val, static_cast<ulbn_ssize_t>(n)));
    return ret;
  }
  template<FitBits T>
    requires(!FitUsize<T>)
  BigInt asInt(T n) const {
    BigInt ret;
    _check(ulbi_as_int_bits(_ctx(), &ret._val, &_val, static_cast<ulbn_bits_t>(n)));
    return ret;
  }
  template<FitSbits T>
    requires(!FitSsize<T>)
  BigInt asInt(T n) const {
    BigInt ret;
    _check(ulbi_as_int_sbits(_ctx(), &ret._val, &_val, static_cast<ulbn_sbits_t>(n)));
    return ret;
  }
  BigInt asInt(const BigInt& n) const {
    BigInt ret;
    _check(ulbi_as_int(_ctx(), &ret._val, &_val, &n._val));
    return ret;
  }

  template<FitUsize T>
  BigInt& asIntLoc(T n) {
    _check(ulbi_as_int_usize(_ctx(), &_val, &_val, static_cast<ulbn_usize_t>(n)));
    return *this;
  }
  template<FitSsize T>
  BigInt& asIntLoc(T n) {
    _check(ulbi_as_int_ssize(_ctx(), &_val, &_val, static_cast<ulbn_ssize_t>(n)));
    return *this;
  }
  template<FitBits T>
    requires(!FitUsize<T>)
  BigInt& asIntLoc(T n) {
    _check(ulbi_as_int_bits(_ctx(), &_val, &_val, static_cast<ulbn_bits_t>(n)));
    return *this;
  }
  template<FitSbits T>
    requires(!FitSsize<T>)
  BigInt& asIntLoc(T n) {
    _check(ulbi_as_int_sbits(_ctx(), &_val, &_val, static_cast<ulbn_sbits_t>(n)));
    return *this;
  }
  BigInt& asIntLoc(const BigInt& n) {
    _check(ulbi_as_int(_ctx(), &_val, &_val, &n._val));
    return *this;
  }


  bool is2Pow() const noexcept {
    return ulbi_is_2pow(&_val) != 0;
  }
  ulbn_bits_t ctz() const noexcept {
    return ulbi_ctz(&_val);
  }
  ulbn_bits_t cto() const noexcept {
    return ulbi_cto(&_val);
  }
  ulbn_bits_t absPopcount() const noexcept {
    return ulbi_abs_popcount(&_val);
  }
  ulbn_bits_t absBitWidth() const noexcept {
    return ulbi_abs_bit_width(&_val);
  }


#if ULBN_CONF_HAS_FLOAT
  template<FitFloat T>
  explicit BigInt(T value) {
    _check(ulbi_init_float(_ctx(), &_val, static_cast<float>(value)));
  }
  template<FitFloat T>
  BigInt& operator=(T value) {
    _check(ulbi_set_float(_ctx(), &_val, static_cast<float>(value)));
    return *this;
  }
  float toFloat() const noexcept {
    return ulbi_to_float(&_val);
  }
  bool fitFloat() const noexcept {
    return ulbi_fit_float(&_val) != 0;
  }
  explicit operator float() const noexcept {
    return toFloat();
  }
#endif


#if ULBN_CONF_HAS_DOUBLE
  template<FitDoubleCase T>
  explicit BigInt(T value) {
    _check(ulbi_init_double(_ctx(), &_val, static_cast<double>(value)));
  }
  template<FitDoubleCase T>
  BigInt& operator=(T value) {
    _check(ulbi_set_double(_ctx(), &_val, static_cast<double>(value)));
    return *this;
  }
  double toDouble() const noexcept {
    return ulbi_to_double(&_val);
  }
  bool fitDouble() const noexcept {
    return ulbi_fit_double(&_val) != 0;
  }
  explicit operator double() const noexcept {
    return toDouble();
  }
#endif /* ULBN_CONF_HAS_DOUBLE */


#if ULBN_CONF_HAS_LONG_DOUBLE
  template<FitLongDoubleCase T>
  explicit BigInt(T value) {
    _check(ulbi_init_long_double(_ctx(), &_val, static_cast<long double>(value)));
  }
  template<FitLongDoubleCase T>
  BigInt& operator=(T value) {
    _check(ulbi_set_long_double(_ctx(), &_val, static_cast<long double>(value)));
    return *this;
  }
  long double toLongDouble() const noexcept {
    return ulbi_to_long_double(&_val);
  }
  bool fitLongDouble() const noexcept {
    return ulbi_fit_long_double(&_val) != 0;
  }
  explicit operator long double() const noexcept {
    return toLongDouble();
  }
#endif /* ULBN_CONF_HAS_LONG_DOUBLE */


  BigInt gcd(const BigInt& other) {
    BigInt ret;
    _check(ulbi_gcd(_ctx(), &ret._val, &_val, &other._val));
    return ret;
  }
  template<FitLimb T>
  BigInt gcd(T other) {
    BigInt ret;
    _check(ulbi_gcd_limb(_ctx(), &ret._val, &_val, static_cast<ulbn_limb_t>(other)));
    return ret;
  }
  template<FitSlimb T>
  BigInt gcd(T other) {
    BigInt ret;
    _check(ulbi_gcd_slimb(_ctx(), &ret._val, &_val, static_cast<ulbn_slimb_t>(other)));
    return ret;
  }
  BigInt lcm(const BigInt& other) {
    BigInt ret;
    _check(ulbi_lcm(_ctx(), &ret._val, &_val, &other._val));
    return ret;
  }


  std::tuple<BigInt, BigInt, BigInt> gcdext(const BigInt& other) {
    BigInt g, x, y;
    _check(ulbi_gcdext(_ctx(), &g._val, &x._val, &y._val, &_val, &other._val));
    return { g, x, y };
  }
  BigInt invert(const BigInt& m) {
    BigInt ret;
    _check(ulbi_invert(_ctx(), &ret._val, &_val, &m._val));
    return ret;
  }


private:
  ulbi_t _val = ULBI_INIT;

  static const ulbn_alloc_t* _ctx() noexcept {
    return getCurrentAllocator();
  }
  static int _check(int err) {
    if(err != ULBN_ERR_INEXACT && err != 0 && err != 1)
      throw Exception(err);
    return err;
  }
  static int _checkSetString(int err) {
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the string cannot be fully parsed as an integer");
    return _check(err);
  }
  static int _checkDivmodEx(int err) {
    if(err == ULBN_ERR_INVALID)
      throw Exception(ULBN_ERR_INVALID, "the round mode is illegal");
    return _check(err);
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

  template<class CharT>
  using SameSignCharType = std::conditional_t<std::is_signed_v<CharT>, signed char, unsigned char>;
  // avoid MSVC C4365 warnings for `std::copy_n`

#if defined(__cpp_lib_format) && __cpp_lib_format >= 201907L
  friend struct std::formatter<BigInt, char>;
  friend struct std::formatter<BigInt, wchar_t>;
  // `std::format` only supports `char` and `wchar_t`
#endif
  template<IsCharType CharT>
  class Formatter {
  private:
    using FormatHelper = ul::FormatHelper<CharT>;

    CharT fill = FormatHelper::SPACE;
    typename FormatHelper::Align align = FormatHelper::Align::INTERNAL;
    typename FormatHelper::Sign sign = FormatHelper::Sign::ONLY_NEGATIVE;
    bool show_base = false;
    size_t width = 0;
    int base = 10;

  public:
#if defined(__cpp_lib_format) && __cpp_lib_format >= 201907L
    constexpr void parse(const FormatHelper& helper) {
      fill = helper.fill;
      align = helper.align;
      sign = helper.sign;
      show_base = helper.use_alter;
      width = helper.width;
      if(helper.target_type.empty()) {
        base = 10;
        return;
      }
      if(helper.has_precision)
        throw std::format_error("precision is not supported");
      if(helper.use_locale)
        throw std::format_error("locale is not supported");
      if(helper.target_type.size() != 1)
        throw std::format_error("invalid type");
      switch(helper.target_type[0]) {
      case static_cast<CharT>('b'):
        base = -2;
        break;
      case static_cast<CharT>('B'):
        base = 2;
        break;
      case static_cast<CharT>('o'):
        base = 8;
        break;
      case static_cast<CharT>('d'):
        base = 10;
        break;
      case static_cast<CharT>('x'):
        base = -16;
        break;
      case static_cast<CharT>('X'):
        base = 16;
        break;
      default:
        throw std::format_error("invalid type");
      }
    }
#endif
    void parse(const std::basic_ostream<CharT>& ost, int _base) {
      auto flags = ost.flags();

      fill = ost.fill();
      if((flags & std::ios_base::adjustfield) == std::ios_base::internal)
        align = FormatHelper::Align::INTERNAL;
      else if((flags & std::ios_base::adjustfield) == std::ios_base::right)
        align = FormatHelper::Align::RIGHT;
      else
        align = FormatHelper::Align::LEFT;

      if((flags & std::ios_base::showpos) != 0)
        sign = FormatHelper::Sign::ALWAYS;
      else
        sign = FormatHelper::Sign::ONLY_NEGATIVE;

      show_base = (flags & std::ios_base::showbase) != 0;
      width = ost.width() < 0 ? 0 : static_cast<size_t>(ost.width());

      if(_base == 0) {
        if((flags & std::ios_base::basefield) == std::ios_base::oct)
          base = 8;
        else if((flags & std::ios_base::basefield) == std::ios_base::hex)
          base = 16;
        else
          base = 10;
        if((flags & std::ios_base::uppercase) != 0)
          base = -base;
      } else
        base = _base;
    }

    template<class Iter>
    Iter format(Iter iter, const BigInt& obj) const {
      if(align == FormatHelper::Align::LEFT && sign == FormatHelper::Sign::ONLY_NEGATIVE && !show_base && width <= 1) {
        Wrapper<Iter&> wrapper(iter);
        const int err = ulbi_print_ex(
          obj._ctx(),
          [](void* opaque, const char* ptr, size_t len) -> int {
            return reinterpret_cast<Wrapper<Iter&>*>(opaque)->call([&](Iter& itr) {
              std::copy_n(reinterpret_cast<const SameSignCharType<CharT>*>(ptr), len, itr);
            });
          },
          &wrapper, &obj._val, base
        );
        return wrapper.check(err);
      }

      std::string str = obj.toString(base);
      if(str[0] == '-')
        str.erase(0, 1);

      {
        std::string preffix;
        if(sign == FormatHelper::Sign::ALWAYS)
          preffix += (obj.sign() >= 0 ? "+" : "-");
        else if(sign == FormatHelper::Sign::ONLY_NEGATIVE) {
          if(obj.sign() < 0)
            preffix += "-";
        } else /* if(sign == FormatHelper::Sign::SPACE_ON_NONNEGATIVE) */
          preffix += (obj.sign() >= 0 ? " " : "-");
        if(show_base) {
          if(base == 2)
            preffix += "0B";
          else if(base == -2)
            preffix += "0b";
          else if(base == 8 || base == -8) {
            if(!obj.isZero())
              preffix += "0";
          } else if(base == 16)
            preffix += "0x";
          else if(base == -16)
            preffix += "0X";
        }
        str.insert(0, preffix);
      }

      size_t lpad = 0, rpad = 0;
      if(width > str.size()) {
        if(align == FormatHelper::Align::INTERNAL) {
          lpad = (width - str.size()) >> 1;
          rpad = width - str.size() - lpad;
        } else if(align == FormatHelper::Align::RIGHT)
          lpad = width - str.size();
        else
          rpad = width - str.size();
      }
      std::basic_string<CharT> pad;
      pad.resize(lpad, fill);
      iter = std::copy(pad.begin(), pad.end(), iter);
      iter = std::copy_n(reinterpret_cast<const SameSignCharType<CharT>*>(str.c_str()), str.size(), iter);
      pad.resize(rpad, fill);
      iter = std::copy(pad.begin(), pad.end(), iter);
      return iter;
    }
  };
};

inline BigInt operator""_bi(unsigned long long value) {
  return { static_cast<ulbn_ulong_t>(value) };
}
inline BigInt operator""_bi(const char* str) {
  return { str };
}
inline BigInt operator""_bi(const char* str, size_t len) {
  (void)len;
  return { str };
}

}  // namespace ul::bn


#if defined(__cpp_lib_format) && __cpp_lib_format >= 201907L
template<ul::bn::IsCharType CharT>
struct std::formatter<ul::bn::BigInt, CharT> {
  using BigInt = ul::bn::BigInt;

  template<class ParseContext>
  constexpr auto parse(ParseContext& ctx) {
    ul::FormatHelper<CharT> helper;
    auto iter = helper.parse(ctx.begin(), ctx.end());
    formatterHelper.parse(helper);
    return iter;
  }

  template<class FmtContext>
  auto format(const ul::bn::BigInt& obj, FmtContext& ctx) const {
    return formatterHelper.format(ctx.out(), obj);
  }

private:
  BigInt::Formatter<CharT> formatterHelper;
};
#endif
