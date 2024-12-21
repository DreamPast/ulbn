#include "ulbn.hpp"
using ul::bn::BigInt;
using ul::bn::operator""_bi;

#include <iostream>
#include <cmath>
#include <cfloat>
#include <cstdint>
#include <limits>
#include <bit>
#include <random>
#include <numeric>
#include <algorithm>

[[noreturn]] void _T_assert(const char* msg, const char* file, int line) {
  std::cerr << "Assertion failed: " << msg << " at " << file << ":" << line << std::endl;
  throw "Assertion failed";
}
#define T_assert(cond) ((void)(!!(cond) || (_T_assert(#cond, __FILE__, __LINE__), 0)))

template<class Func>
int _getExceptionCode(Func&& func) {
  try {
    func();
    return 0;
  } catch(const ul::bn::Exception& e) {
    return e.getError();
  }
}
#define T_assert_exception(func, expect) T_assert(_getExceptionCode(func) == (expect))

template<class To, class From>
bool fitType(From from) {
  static_assert(std::is_arithmetic_v<To> && std::is_integral_v<From>);
  if constexpr(std::is_floating_point_v<To>)
    return static_cast<To>(from) == from;
  if constexpr(std::is_signed_v<To>) {
    if constexpr(std::is_signed_v<From>) {
      return from >= std::numeric_limits<To>::min() && from <= std::numeric_limits<To>::max();
    } else {
      return from <= static_cast<std::make_unsigned_t<To>>(std::numeric_limits<To>::max());
    }
  } else {
    if constexpr(std::is_signed_v<From>) {
      return 0 <= from && static_cast<std::make_unsigned_t<From>>(from) <= std::numeric_limits<To>::max();
    } else {
      return from <= std::numeric_limits<To>::max();
    }
  }
}

template<class LT1, class LT2, class RT1, class RT2>
bool pairEqual(const std::pair<LT1, LT2>& l, const std::pair<RT1, RT2>& r) {
  return l.first == r.first && l.second == r.second;
}
template<class LT1, class LT2, class RT1, class RT2>
bool pairEqual(const std::pair<LT1, LT2>& l, RT1&& rt1, RT2&& rt2) {
  return l.first == rt1 && l.second == rt2;
}

inline constexpr const int LIMIT = 1024;
inline constexpr const int64_t TEST_BIG = 1000000ll;
inline constexpr const int64_t TEST_SMALL = 3000;
inline constexpr const int64_t TEST_VERY_SMALL = 30;
static std::mt19937_64 mt64(std::random_device{}());

template<class Func>
void testIt(Func func) {
  static thread_local size_t tot_mem = 0;
  static thread_local size_t max_mem = 0;
  static thread_local ulbn_alloc_func_t* original_alloc_func;
  static thread_local void* original_alloc_opaque;

  ulbn_alloc_t* alloc = ul::bn::getCurrentAllocator();
  original_alloc_func = alloc->alloc_func;
  original_alloc_opaque = alloc->alloc_opaque;
  alloc->alloc_func = [](void* opaque, void* ptr, size_t on, size_t nn) -> void* {
    (void)opaque;
    tot_mem -= on;
    tot_mem += nn;
    max_mem = std::max(max_mem, tot_mem);
    return original_alloc_func(original_alloc_opaque, ptr, on, nn);
  };

  func();

  std::cout << "Maximum Memory:" << max_mem << '\n';
  std::cout << "Total Memory:" << tot_mem << '\n';
  T_assert(tot_mem == 0);
}
