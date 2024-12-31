/*
ulbn - Big Number Library

# Requirements
  - C89/C++98
  - `CHAR_BIT` should be even

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
#ifndef ULBN_HEADER
#define ULBN_HEADER

#if (ULBN_HEADER + 0)
#endif


/***************************
 * Internal Utility Macros *
 ***************************/


/**
 * @def UL_PEDANTIC
 * @brief Enables pedantic mode (disable all non-standard features).
 */
/* #define UL_PEDANTIC */

/**
 * @def ul_unused
 * @brief Marks a variable or function may be unused.
 */
#if !defined(ul_unused) && defined(__has_attribute)
  #if __has_attribute(unused) && !defined(UL_PEDANTIC)
    #define ul_unused __attribute__((unused))
  #endif
#endif /* ul_unused */
#if !defined(ul_unused) && defined(__cplusplus) && __cplusplus >= 201103L && defined(__has_cpp_attribute)
  #if __has_cpp_attribute(maybe_unused)
    #define ul_unused [[maybe_unused]]
  #endif
#endif /* ul_unused */
#ifndef ul_unused
  #define ul_unused
#endif /* ul_unused */

/**
 * @def ul_inline
 * @brief Marks a function as inline. This macro is not intended to instruct the compiler to inline the function,
 * but rather to use another meaning: if the implementation is consistent within the same translation unit,
 * only one copy can be retained.
 */
#ifndef ul_inline
  #if defined(__cplusplus) || (defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L)
    #define ul_inline inline
  #else
    #define ul_inline
  #endif
#endif /* ul_inline */

/**
 * @def ul_likely
 * @brief Hints to the compiler that the condition is more likely to be true.
 */
/**
 * @def ul_unlikely
 * @brief Hints to the compiler that the condition is more likely to be false.
 */
#ifdef __has_builtin
  #if __has_builtin(__builtin_expect) && !defined(UL_PEDANTIC)
    #ifndef ul_likely
      #define ul_likely(x) __builtin_expect(!!(x), 1)
    #endif
    #ifndef ul_unlikely
      #define ul_unlikely(x) __builtin_expect(!!(x), 0)
    #endif
  #endif
#endif /* ul_likely + ul_unlikely */
#ifndef ul_likely
  #define ul_likely(x) (x)
#endif /* ul_likely */
#ifndef ul_unlikely
  #define ul_unlikely(x) (x)
#endif /* ul_unlikely */

/**
 * @def ul_static_cast
 * @brief Converts between types using a combination of implicit and user-defined conversions
 * (same as C++ `static_cast`).
 */
#ifndef ul_static_cast
  #ifdef __cplusplus
    #define ul_static_cast(T, val) (static_cast<T>(val))
  #else
    #define ul_static_cast(T, val) ((T)(val))
  #endif
#endif /* ul_static_cast */

/**
 * @def ul_reinterpret_cast
 * @brief Converts between types by reinterpreting the underlying bit pattern
 * (same as C++ `reinterpret_cast`).
 */
#ifndef ul_reinterpret_cast
  #ifdef __cplusplus
    #define ul_reinterpret_cast(T, val) (reinterpret_cast<T>(val))
  #else
    #define ul_reinterpret_cast(T, val) ((T)(val))
  #endif
#endif /* ul_reinterpret_cast */

/**
 * @def ul_has_builtin
 * @brief Tests whether given symbol name is recognized as a builtin-in function by GCC/Clang
 * in the current language and conformance mode.
 */
#ifndef ul_has_builtin
  #if defined(__has_builtin) && !defined(UL_PEDANTIC)
    #define ul_has_builtin(x) __has_builtin(x)
  #else
    #define ul_has_builtin(x) 0
  #endif
#endif /* ul_has_builtin */

/**
 * @def UL_JOIN
 * @brief Concatenates two identifiers.
 */
#ifndef UL_JOIN
  #define __UL_JOIN2(X, Y) X##Y
  #define __UL_JOIN(X, Y) __UL_JOIN2(X, Y)
  #define UL_JOIN(X, Y) __UL_JOIN(X, Y)
#endif /* UL_JOIN */

/**
 * @def ul_static_assert
 * @brief Static assertion checking.
 */
/* clang-format off */
#if defined(__cplusplus) && __cplusplus >= 201103L
  #define ul_static_assert(cond, msg) static_assert(cond, msg)
#elif defined(__STDC_VERSION__) && __STDC_VERSION__ >= 202311L
  #define ul_static_assert(cond, msg) static_assert(cond, msg)
#elif defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
  #define ul_static_assert(cond, msg) _Static_assert(cond, msg)
#elif defined(__cplusplus)
  namespace __ul_static_assert {
    template<bool x> struct __UL_STATIC_CAST_FAILURE;
    template<> struct __UL_STATIC_CAST_FAILURE<true> { enum { value = 1 }; };
  }
  #define ul_static_assert(cond, msg)                                                        \
    enum { UL_JOIN(___UL_STATIC_ASSERT_, __LINE__) =                                         \
      sizeof(::__ul_static_assert::__UL_STATIC_CAST_FAILURE<static_cast<bool>(cond)>::value) \
    }
#else
  #define ul_static_assert(cond, msg) \
    typedef struct { int __error_if_negative: (cond) ? 1 : -1; } UL_JOIN(___UL_STATIC_ASSERT_, __LINE__)
#endif /* ul_static_assert */
/* clang-format on */

/**
 * @def ul_nullptr
 * @brief Null pointer constant.
 */
#ifndef ul_nullptr
  #if defined(__cplusplus) && __cplusplus >= 201103L
    #define ul_nullptr nullptr
  #elif defined(__STDC_VERSION__) && __STDC_VERSION__ >= 202311L
    #define ul_nullptr nullptr
  #else
    #define ul_nullptr NULL
  #endif
#endif /* ul_nullptr */

/**
 * @def ul_restrict
 * @brief Restrict qualifier (C99/C++ extensions). Marks pointers with same types doesn't overlap.
 */
#ifndef ul_restrict
  #if defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 199901L)
    #define ul_restrict restrict
  #elif !defined(UL_PEDANTIC)
    #if defined(_MSC_VER) && _MSC_VER >= 1900
      #define ul_restrict __restrict
    #elif defined(__GNUC__) && __GNUC__ > 3
      #define ul_restrict __restrict__
    #endif
  #endif
  #ifndef ul_restrict
    #define ul_restrict
  #endif
#endif /* ul_restrict */

/**
 * @def ul_constexpr
 * @brief Marks a function able to be evaluated at compile time (C++11).
 */
#ifndef ul_constexpr
  /* clang-format off */
  #ifdef __cplusplus
    #if __cplusplus >= 201103L
      #define ul_constexpr constexpr
      #define UL_CONSTEXPR_INIT { }
    #elif defined(_MSC_VER) && _MSC_VER >= 1900 && !defined(__clang__) /* Visual Studio 2015 and above */
      #define ul_constexpr constexpr
      #define UL_CONSTEXPR_INIT { }
    #endif
  #endif
  #ifndef ul_constexpr
    #define ul_constexpr
    #define UL_CONSTEXPR_INIT
  #endif
  /* clang-format on */
#endif /* ul_constexpr */

/**
 * @def UL_HAS_STDINT_H
 * @brief Check if exisiting `<stdint.h>`.
 */
#ifndef UL_HAS_STDINT_H
  #if defined(__GLIBC__) && (__GLIBC__ > 2 || (__GLIBC__ == 2 && __GLIBC_MINOR__ >= 1))
    #if defined(__GNUC__) || ((__GLIBC__ > 2) || ((__GLIBC__ == 2) && (__GLIBC_MINOR__ >= 5)))
      #define UL_HAS_STDINT_H
    #endif
  #endif
  #if defined(__MINGW32__)
    #include <_mingw.h>
    #if (__MINGW32_MAJOR_VERSION > 2 || (__MINGW32_MAJOR_VERSION == 2 && __MINGW32_MINOR_VERSION >= 0))
      #define UL_HAS_STDINT_H
    #endif
  #endif
  #if defined(unix) || defined(__unix) || defined(_XOPEN_SOURCE) || defined(_POSIX_SOURCE)
    #include <unistd.h>
    #if defined(_POSIX_VERSION) && (_POSIX_VERSION >= 200100L)
      #define UL_HAS_STDINT_H
    #endif
  #endif
  #if (defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L) || (defined(__cplusplus) && __cplusplus >= 201103L)
    #define UL_HAS_STDINT_H
  #endif
  #if (defined(_MSC_VER) && _MSC_VER >= 1600) || (defined(__CYGWIN__) && defined(_STDINT_H))
    #define UL_HAS_STDINT_H
  #endif
  #if defined(__has_include)
    #if __has_include(<stdint.h>)
      #define UL_HAS_STDINT_H
    #endif
  #endif
#endif /* UL_HAS_STDINT_H */
#ifdef UL_HAS_STDINT_H
  #include <stdint.h>
#endif

/**
 * @def ul_export
 * @brief Exports a symbol.
 */
#ifndef ul_export
  #if defined(__clang__)
    #if defined(_WIN32) || defined(__WIN32__) || defined(WIN32) || defined(__CYGWIN__)
      #define ul_export __attribute__((__dllexport__))
    #else
      #define ul_export __attribute__((__visibility__("default")))
    #endif
  #elif defined(__GNUC__) && __GNUC__ >= 4
    #if defined(_WIN32) || defined(__WIN32__) || defined(WIN32) || defined(__CYGWIN__)
      #define ul_export __attribute__((__dllexport__))
    #else
      #define ul_export __attribute__((__visibility__("default")))
    #endif
  #endif
  #if !defined(ul_export)
    #if defined(_WIN32) || defined(__WIN32__) || defined(WIN32)
      #define ul_export __declspec(dllexport)
    #else
      #define ul_export
    #endif
  #endif

  #ifdef UL_PEDANTIC
    #undef ul_export
    #define ul_export
  #endif
#endif /* ul_export */


/****************
 * Header Files *
 ****************/


#include <float.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>


/*****************
 * Configuration *
 *****************/


/**
 * @def ULBN_CONF_CHECK_ALLOCATION_FAILURE
 * @brief Configuration: Whether to check for memory allocation failure.
 */
#ifndef ULBN_CONF_CHECK_ALLOCATION_FAILURE
  #define ULBN_CONF_CHECK_ALLOCATION_FAILURE 1
#endif /* ULBN_CONF_CHECK_ALLOCATION_FAILURE */

/**
 * @def ULBN_CONF_HAS_FLOAT
 * @brief Configuration: Whether `float` is available.
 */
#ifndef ULBN_CONF_HAS_FLOAT
  #if defined(FLT_MAX) && defined(FLT_MAX_EXP) && defined(FLT_MANT_DIG)
    #define ULBN_CONF_HAS_FLOAT 1
  #else
    #define ULBN_CONF_HAS_FLOAT 0
  #endif
#endif /* ULBN_CONF_HAS_FLOAT */

/**
 * @def ULBN_CONF_HAS_DOUBLE
 * @brief Configuration: Whether `double` is available.
 */
#ifndef ULBN_CONF_HAS_DOUBLE
  #if defined(DBL_MAX) && defined(DBL_MAX_EXP) && defined(DBL_MANT_DIG)
    #define ULBN_CONF_HAS_DOUBLE 1
  #else
    #define ULBN_CONF_HAS_DOUBLE 0
  #endif
#endif /* ULBN_CONF_HAS_DOUBLE */

/**
 * @def ULBN_CONF_HAS_DOUBLE
 * @brief Configuration: Whether `long double` is available.
 */
#ifndef ULBN_CONF_HAS_LONG_DOUBLE
  #if defined(LDBL_MAX) && defined(LDBL_MAX_EXP) && defined(LDBL_MANT_DIG) \
    && defined(HUGE_VALL) /* `HUGE_VALL` is defined in C99, so we guess `floorl` exists when `HUGE_VALL` exists */
    #define ULBN_CONF_HAS_LONG_DOUBLE 1
  #else
    #define ULBN_CONF_HAS_LONG_DOUBLE 0
  #endif
#endif /* ULBN_CONF_HAS_LONG_DOUBLE */

/**
 * @def ULBN_CONF_ONLY_ALLOCATE_NEEDED
 * @brief Configuration: Whether to only allocate memory needed.
 */
#ifndef ULBN_CONF_ONLY_ALLOCATE_NEEDED
  #define ULBN_CONF_ONLY_ALLOCATE_NEEDED 0
#endif /* ULBN_CONF_ONLY_ALLOCATE_NEEDED */

/**
 * @def ULBN_CONF_EXPORT_PUBLIC
 * @brief Configuration: Whether to export public functions.
 */
#ifndef ULBN_CONF_EXPORT_PUBLIC
  #define ULBN_CONF_EXPORT_PUBLIC 0
#endif /* ULBN_CONF_EXPORT_PUBLIC */

/**
 * @def ULBN_CONF_IMPLE
 * @brief Configuration: Whether to include the implementation in this file.
 * @note It will mark all public functions to be `static` (`ULBN_CONF_EXPORT_PUBLIC` takes precedence).
 */
#ifndef ULBN_CONF_IMPLE
  #define ULBN_CONF_IMPLE 0
#endif /* ULBN_CONF_IMPLE */

/**
 * @def ULBN_CONF_USE_RAND
 * @brief Configuration: Whether to use random number generator.
 */
#ifndef ULBN_CONF_USE_RAND
  #define ULBN_CONF_USE_RAND 1
#endif

#ifndef ULBN_CONF_BIG_INT
  #define ULBN_CONF_BIG_INT 1
#endif


/*********************
 * Basic Definitions *
 *********************/


#ifdef __cplusplus
extern "C" {
#endif

#define _ulbn_max_(a, b) ((a) > (b) ? (a) : (b))
#define _ulbn_min_(a, b) ((a) < (b) ? (a) : (b))


#if 0
typedef unsigned char ulbn_limb_t;
typedef signed char ulbn_slimb_t;
  #define ULBN_LIMB_MAX UCHAR_MAX
  #define ULBN_SLIMB_MAX SCHAR_MAX
  #define ULBN_SLIMB_MIN SCHAR_MIN
#endif
#if (!defined(ULBN_LIMB_MAX) || !defined(ULBN_SLIMB_MAX) || !defined(ULBN_SLIMB_MIN)) \
  && (defined(_WIN64) && defined(LLONG_MAX))
typedef unsigned long long ulbn_limb_t;
typedef signed long long ulbn_slimb_t;
  #define ULBN_LIMB_MAX ULLONG_MAX
  #define ULBN_SLIMB_MAX LLONG_MAX
  #define ULBN_SLIMB_MIN LLONG_MIN
#endif
#if (!defined(ULBN_LIMB_MAX) || !defined(ULBN_SLIMB_MAX) || !defined(ULBN_SLIMB_MIN))
typedef unsigned long ulbn_limb_t;
typedef signed long ulbn_slimb_t;
  #define ULBN_LIMB_MAX ULONG_MAX
  #define ULBN_SLIMB_MAX LONG_MAX
  #define ULBN_SLIMB_MIN LONG_MIN
#endif

#if !defined(ulbn_limb2_t) && USHRT_MAX / ULBN_LIMB_MAX >= ULBN_LIMB_MAX \
  && USHRT_MAX / ULBN_LIMB_MAX - ULBN_LIMB_MAX >= 2
  #define ulbn_limb2_t unsigned short
#endif
#if !defined(ulbn_limb2_t) && UINT_MAX / ULBN_LIMB_MAX >= ULBN_LIMB_MAX && UINT_MAX / ULBN_LIMB_MAX - ULBN_LIMB_MAX >= 2
  #define ulbn_limb2_t unsigned int
#endif
#if !defined(ulbn_limb2_t) && ULONG_MAX / ULBN_LIMB_MAX >= ULBN_LIMB_MAX \
  && ULONG_MAX / ULBN_LIMB_MAX - ULBN_LIMB_MAX >= 2
  #define ulbn_limb2_t unsigned long
#endif
#if !defined(ulbn_limb2_t) && defined(ULLONG_MAX) && ULLONG_MAX / ULBN_LIMB_MAX >= ULBN_LIMB_MAX \
  && ULLONG_MAX / ULBN_LIMB_MAX - ULBN_LIMB_MAX >= 2
  #define ulbn_limb2_t unsigned long long
#endif
#if !defined(ulbn_limb2_t) && !defined(UL_PEDANTIC) && defined(__SIZEOF_INT128__) && defined(__GNUC__)
  #if ULBN_LIMB_MAX <= 0xFFFFFFFFFFFFFFFFu
    #define ulbn_limb2_t unsigned __int128
  #endif
#endif


#if !defined(ULBN_USIZE_MAX) || !defined(ULBN_SSIZE_MAX) || !defined(ULBN_SSIZE_MIN)
typedef signed ulbn_ssize_t;
typedef unsigned ulbn_usize_t;
  #define ULBN_USIZE_MAX UINT_MAX
  #define ULBN_SSIZE_MAX INT_MAX
  #define ULBN_SSIZE_MIN INT_MIN
#endif

#define ulbn_cast_usize(n) ul_static_cast(ulbn_usize_t, (n))
#define ulbn_cast_ssize(n) ul_static_cast(ulbn_ssize_t, (n))


#if !defined(ULBN_BITS_MAX)
  #if USHRT_MAX >= ULBN_USIZE_MAX * CHAR_BIT
typedef unsigned short ulbn_bits_t;
typedef signed short ulbn_sbits_t;
    #define ULBN_BITS_MAX USHRT_MAX
    #define ULBN_SBITS_MAX SHRT_MAX
    #define ULBN_SBITS_MIN SHRT_MIN
  #elif UINT_MAX >= ULBN_USIZE_MAX * CHAR_BIT
typedef unsigned int ulbn_bits_t;
typedef signed int ulbn_sbits_t;
    #define ULBN_BITS_MAX UINT_MAX
    #define ULBN_SBITS_MAX INT_MAX
    #define ULBN_SBITS_MIN INT_MIN
  #elif ULONG_MAX >= ULBN_USIZE_MAX * CHAR_BIT
typedef unsigned long ulbn_bits_t;
typedef signed long ulbn_sbits_t;
    #define ULBN_BITS_MAX ULONG_MAX
    #define ULBN_SBITS_MAX LONG_MAX
    #define ULBN_SBITS_MIN LONG_MIN
  #elif defined(ULLONG_MAX) && ULLONG_MAX >= ULBN_USIZE_MAX * CHAR_BIT
typedef unsigned long long ulbn_bits_t;
typedef signed long long ulbn_sbits_t;
    #define ULBN_BITS_MAX ULLONG_MAX
    #define ULBN_SBITS_MAX LLONG_MAX
    #define ULBN_SBITS_MIN LLONG_MIN
  #else
typedef ulbn_usize_t ulbn_bits_t; /* we will limit `ulbn_usize_t` to make `ulbn_bits_t` won't overflow */
typedef ulbn_ssize_t ulbn_sbits_t;
    #define ULBN_BITS_MAX ULBN_USIZE_MAX
    #define ULBN_SBITS_MAX ULBN_SSIZE_MAX
    #define ULBN_SBITS_MIN ULBN_SSIZE_MIN
  #endif
#endif


#if !defined(ULBN_ULONG_MAX) || !defined(ULBN_SLONG_MAX) || !defined(ULBN_SLONG_MIN)
  #if defined(UINTMAX_MAX)
typedef uintmax_t ulbn_ulong_t;
typedef intmax_t ulbn_slong_t;
    #define ULBN_ULONG_MAX UINTMAX_MAX
    #define ULBN_SLONG_MAX INTMAX_MAX
    #define ULBN_SLONG_MIN INTMAX_MIN
  #elif defined(ULLONG_MAX)
typedef unsigned long long ulbn_ulong_t;
typedef signed long long ulbn_slong_t;
    #define ULBN_ULONG_MAX ULLONG_MAX
    #define ULBN_SLONG_MAX LLONG_MAX
    #define ULBN_SLONG_MIN LLONG_MIN
  #else
typedef unsigned long ulbn_ulong_t;
typedef signed long ulbn_slong_t;
    #define ULBN_ULONG_MAX ULONG_MAX
    #define ULBN_SLONG_MAX LONG_MAX
    #define ULBN_SLONG_MIN LONG_MIN
  #endif
#endif

#define ULBN_ULONG_BITS (sizeof(ulbn_ulong_t) * CHAR_BIT)
#define _ULBN_ULONG_LIMB_LEN ((sizeof(ulbn_ulong_t) + sizeof(ulbn_limb_t) - 1) / sizeof(ulbn_limb_t))


#if ULBN_LIMB_MAX > ULBN_ULONG_MAX
  #error "ulbn: `ulbn_limb_t` cannot be larger than `ulbn_ulong_t`"
#endif
#if ULBN_USIZE_MAX > ULBN_ULONG_MAX
  #error "ulbn: `ulbn_usize_t` cannot be larger than `ulbn_ulong_t`"
#endif
#if ULBN_BITS_MAX > ULBN_ULONG_MAX
  #error "ulbn: `ulbn_bits_t` cannot be larger than `ulbn_ulong_t`"
#endif


#if ULBN_CONF_EXPORT_PUBLIC
  #define ULBN_PUBLIC ul_export
#endif

#if ULBN_CONF_IMPLE
  #ifndef ULBN_PUBLIC
    #define ULBN_PUBLIC static ul_inline
  #endif /* ULBN_PUBLIC */
  #ifndef ULBN_INTERNAL
    #define ULBN_INTERNAL static ul_inline
  #endif /* ULBN_INTERNAL */
  #ifndef ULBN_PRIVATE
    #define ULBN_PRIVATE static ul_inline
  #endif /* ULBN_PRIVATE */
#endif

#ifndef ULBN_PUBLIC
  #define ULBN_PUBLIC
#endif /* ULBN_PUBLIC */
#ifndef ULBN_INTERNAL
  #define ULBN_INTERNAL static
#endif /* ULBN_INTERNAL */
#ifndef ULBN_PRIVATE
  #define ULBN_PRIVATE static
#endif /* ULBN_PRIVATE */

#ifndef ULBN_CONF_FFT
  #if ULBN_LIMB_MAX >= 0xFFFu
    #define ULBN_CONF_FFT 1
  #else
    #define ULBN_CONF_FFT 0
  #endif
#endif

#define _ULBN_SHORT_LIMB_SIZE                                                                              \
  _ulbn_max_(                                                                                              \
    sizeof(void*) / sizeof(ulbn_limb_t), /* same size as `void*` */                                        \
    _ulbn_max_(                                                                                            \
      _ULBN_ULONG_LIMB_LEN, /* able to hold `ulbn_ulong_t` */                                              \
      2u                    /* make operations on a single `ulbn_limb_t` not to cause memory allocation */ \
    )                                                                                                      \
  )

/*********
 * Enums *
 *********/


/* <0 indicates a system error, >0 indicates a mathematical error.
This error directly corresponds to the IEEE754 error code. */
enum ULBN_ERROR_ENUM {
  /**
   * @brief External error
   */
  ULBN_ERR_EXTERNAL = -3,
  /**
   * @brief Unexpected out-of-bounds error (usually means the result exceeds ulbn_usize_t)
   */
  ULBN_ERR_EXCEED_RANGE = -2,
  /**
   * @brief Memory error
   */
  ULBN_ERR_NOMEM = -1,

  ULBN_ERR_SUCCESS = 0,
  /**
   * @brief Pole error
   * @details The calculation results in infinity or undefined.
   * @details For example, 1/0, atan(pi/2).
   */
  ULBN_ERR_DIV_BY_ZERO = 2,
  /**
   * @brief Inexact result.
   * @note This error occurs very frequently and can usually be ignored.
   */
  ULBN_ERR_INEXACT = 4,
  /**
   * @brief Domain error
   * @details For example, log(-1).
   */
  ULBN_ERR_INVALID = 8,
  /**
   * @brief Overflow error
   * @details The result is finite but rounded to infinity, or rounded down to the maximum finite value.
   */
  ULBN_ERR_OVERFLOW = 16,
  /**
   * @brief Underflow error
   * @details The result is non-zero but rounded to zero.
   */
  ULBN_ERR_UNDERFLOW = 32
};

enum ULBN_ROUND_ENUM {
  ULBN_ROUND_DOWN = 0,
  ULBN_ROUND_UP = 1,
  ULBN_ROUND_FLOOR = 2,
  ULBN_ROUND_CEILING = 3,
  ULBN_ROUND_HALF_ODD = 4,
  ULBN_ROUND_HALF_EVEN = 5,
  ULBN_ROUND_HALF_DOWN = 6,
  ULBN_ROUND_HALF_UP = 7,
  ULBN_ROUND_FAIL = 8,

  ULBN_ROUND_TRUNC = ULBN_ROUND_DOWN,
  ULBN_ROUND_TO_ZERO = ULBN_ROUND_DOWN,
  ULBN_ROUND_AWAY_FROM_ZERO = ULBN_ROUND_UP,
  ULBN_ROUND_TO_POSITIVE_INFINITY = ULBN_ROUND_CEILING,
  ULBN_ROUND_TO_NEGATIVE_INFINITY = ULBN_ROUND_FLOOR,
  ULBN_ROUND_TO_NEAREST = ULBN_ROUND_HALF_EVEN,

  ULBN_RNDN = ULBN_ROUND_HALF_EVEN,
  ULBN_RNDZ = ULBN_ROUND_TO_ZERO,
  ULBN_RNDU = ULBN_ROUND_CEILING,
  ULBN_RNDD = ULBN_ROUND_FLOOR,
  ULBN_RNDA = ULBN_ROUND_AWAY_FROM_ZERO,
  ULBN_RNDNA = ULBN_ROUND_HALF_UP,
  ULBN_RNDF = ULBN_ROUND_FAIL
};

enum ULBN_SET_STRING_FLAG_ENUM {
  /**
   * @brief Accept separator ('_').
   * @note Separator is ignored when parsing the string.
   * @note Separator cannot appear at the exponent part (e.g., "10e1_2" is illegal).
   */
  ULBN_SET_STRING_ACCEPT_SEPARATOR = (1 << 0),
  /**
   * @brief Accept decimal part (e.g., "1.5", ".5").
   */
  ULBN_SET_STRING_ACCEPT_DECIMAL_PART = (1 << 1),
  /**
   * @brief Accept decimal exponent part (e.g., "1e2", "1e+2", "1e-2").
   * @note "{a}e{b}" is equivalent to "{a} * 10^{b}".
   */
  ULBN_SET_STRING_ACCEPT_DEC_EXPONENT = (1 << 2),
  /**
   * @brief Accept hexadecimal exponent part (e.g., "1p2", "1p+2", "1p-2").
   * @note "{a}p{b}" is equivalent to "{a} * 2^{b}".
   */
  ULBN_SET_STRING_ACCEPT_HEX_EXPONENT = (1 << 3),
  /**
   * @brief Accept octal number with implicit prefix (e.g., "0123").
   * @note This flag is only effective when `base` is 0.
   */
  ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX = (1 << 4),
  /**
   * @brief Allow exponent mismatch (e.g., "0x1e2.5").
   * @note If this flag is not set, 'e' or 'E' can only be used in decimal, 'p' or 'P' can only be used in hexadecimal.
   */
  ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH = (1 << 5)
};


/************************
 * `ulbn_*` Common APIs *
 ************************/


typedef void* ulbn_alloc_func_t(void* opaque, void* ptr, size_t on, size_t nn);
/* Note: `ulbn_alloc_t` is thread-safe if `alloc_func` is thread-safe. */
typedef struct ulbn_alloc_t {
  ulbn_alloc_func_t* alloc_func;
  void* alloc_opaque;
} ulbn_alloc_t;
ULBN_PUBLIC const ulbn_alloc_t* ulbn_default_alloc(void);

ULBN_PUBLIC void* ulbn_alloc(const ulbn_alloc_t* alloc, size_t sz);
ULBN_PUBLIC void* ulbn_realloc(const ulbn_alloc_t* alloc, void* ptr, size_t on, size_t nn);
ULBN_PUBLIC void ulbn_dealloc(const ulbn_alloc_t* alloc, void* ptr, size_t sz);


typedef int ulbn_printer_t(void* opaque, const char* str, size_t len);


#if ULBN_CONF_USE_RAND
  #if defined(UINT_FAST32_MAX)
typedef uint_fast32_t ulbn_rand_uint_t;
  #elif UINT_MAX >= 0xFFFFFFFFu
typedef unsigned ulbn_rand_uint_t; /* uint_fast32_t */
  #else
typedef unsigned long ulbn_rand_uint_t; /* uint_fast32_t */
  #endif
/* [PCG Random Number Generators](https://www.pcg-random.org/) */
/* Note: `ulbn_rand_t` is not thread-safe. */
typedef struct ulbn_rand_t {
  ulbn_rand_uint_t state;
  ulbn_rand_uint_t inc;
} ulbn_rand_t;

/**
 * @brief sizeof(ulbn_rand_t)
 * @note When you want to use FFI to call this library, you can call this function to get the size of `ulbn_rand_t`.
 */
ULBN_PUBLIC size_t ulbn_rand_sizeof(void);
/**
 * @brief Initializes a random number generator.
 * @return Random seed.
 */
ULBN_PUBLIC ulbn_rand_uint_t ulbn_rand_init(ulbn_rand_t* rng);
/**
 * @brief Initializes a random number generator with a seed.
 */
ULBN_PUBLIC void ulbn_rand_init2(ulbn_rand_t* rng, ulbn_rand_uint_t seed);
/**
 * @brief Generates a random `ulbn_limb_t`.
 */
ULBN_PUBLIC ulbn_limb_t ulbn_rand_step(ulbn_rand_t* rng);
/**
 * @brief Advances the random number generator.
 */
ULBN_PUBLIC void ulbn_rand_advance(ulbn_rand_t* rng, ulbn_rand_uint_t steps);
/**
 * @brief Generates random bytes.
 */
ULBN_PUBLIC void ulbn_rand_fill(ulbn_rand_t* rng, void* dst, size_t n);
#endif /* ULBN_CONF_USE_RAND */


/**
 * @brief Get the limit of `ulbn_usize_t`.
 */
ULBN_PUBLIC ulbn_usize_t ulbn_usize_limit(void);
/**
 * @brief Get the limit of `ulbn_ssize_t`.
 */
ULBN_PUBLIC ulbn_ssize_t ulbn_ssize_limit(void);


/********************
 * Big Integer APIs *
 ********************/


#if ULBN_CONF_BIG_INT
typedef struct ulbi_t {
  ulbn_ssize_t len;
  ulbn_usize_t cap;
  union {
    ulbn_limb_t shrt[_ULBN_SHORT_LIMB_SIZE];
    ulbn_limb_t* ul_restrict lng;
  } u;
} ulbi_t;
  /* clang-format off */
#define ULBI_INIT { 0, _ULBN_SHORT_LIMB_SIZE, { { 0 } } }
/* clang-format on */

/**
 * @brief sizeof(ulbi_t)
 * @note When you want to use FFI to call this library, you can call this function to get the size of `ulbi_t`.
 */
ULBN_PUBLIC size_t ulbi_sizeof(void);
/**
 * @brief Get the zero big integer constant.
 */
ULBN_PUBLIC const ulbi_t* ulbi_zero(void);


/**
 * @brief Initializes a big integer.
 * @note This function never fails.
 * @return `o` itself.
 */
ULBN_PUBLIC ulbi_t* ulbi_init(ulbi_t* o);
/**
 * @brief Initializes a big integer and reserve space.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_init_reserve(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n);
/**
 * @brief Deinitializes a big integer.
 * @note After this, `o` will become 0.
 * @note `o` is still usable but memory is free.
 */
ULBN_PUBLIC void ulbi_deinit(const ulbn_alloc_t* alloc, ulbi_t* o);

/**
 * @brief Shrinks the memory of `o`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory (in this case `o` remains unchanged, so this error can be ignored)
 */
ULBN_PUBLIC int ulbi_shrink(const ulbn_alloc_t* alloc, ulbi_t* o);
/**
 * @brief Reserve space for at least `n` limbs in `o`.
 * @return Non-null pointer if allocation is successful;
 * @return `NULL` if `n` == 0 and `o` is not allocated (handled as `ULBN_ERR_SUCCESS`);
 * @return `NULL` if out of memory (handled as `ULBN_ERR_NOMEM`).
 */
ULBN_PUBLIC ulbn_limb_t* ulbi_reserve(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n);

/**
 * @brief Get the internal limbs of `obj`.
 * @note In order to keep the big integer safe, you should not modify the returned pointer.
 */
ULBN_PUBLIC const ulbn_limb_t* ulbi_get_limbs(const ulbi_t* obj);
/**
 * @brief Get the length of the internal limbs of `obj`.
 */
ULBN_PUBLIC size_t ulbi_get_limbs_len(const ulbi_t* obj);
/**
 * @brief Sets `dst` to `limbs` with length of `len`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `src` is too large.
 */
ULBN_PUBLIC int ulbi_set_limbs(const ulbn_alloc_t* alloc, ulbi_t* obj, const ulbn_limb_t* limbs, size_t len);
/**
 * @brief Initializes `dst` to `limbs` with length of `len`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `src` is too large.
 */
ULBN_PUBLIC int ulbi_init_limbs(const ulbn_alloc_t* alloc, ulbi_t* obj, const ulbn_limb_t* limbs, size_t len);


/**
 * @brief Sets `dst` to zero.
 * @note This function never fails.
 */
ULBN_PUBLIC ulbi_t* ulbi_set_zero(ulbi_t* dst);

/**
 * @brief Initializes `dst` with `limb`.
 * @note This function never fails.
 */
ULBN_PUBLIC ulbi_t* ulbi_init_limb(ulbi_t* dst, ulbn_limb_t limb);
/**
 * @brief Initializes `dst` with `slimb`.
 * @note This function never fails.
 */
ULBN_PUBLIC ulbi_t* ulbi_init_slimb(ulbi_t* dst, ulbn_slimb_t slimb);
/**
 * @brief Sets `dst` to `limb`.
 * @note This function never fails.
 */
ULBN_PUBLIC void ulbi_set_limb(ulbi_t* dst, ulbn_limb_t limb);
/**
 * @brief Sets `dst` to `slimb`.
 * @note This function never fails.
 */
ULBN_PUBLIC void ulbi_set_slimb(ulbi_t* dst, ulbn_slimb_t slimb);

/**
 * @brief Sets `dst` to `l`
 * @note This function never fails.
 */
ULBN_PUBLIC void ulbi_set_ulong(ulbi_t* dst, ulbn_ulong_t l);
/**
 * @brief Sets `dst` to `l`.
 * @note This function never fails.
 */
ULBN_PUBLIC void ulbi_set_slong(ulbi_t* dst, ulbn_slong_t l);
/**
 * @brief Initializes `dst` with `l`.
 * @note This function never fails.
 */
ULBN_PUBLIC ulbi_t* ulbi_init_ulong(ulbi_t* dst, ulbn_ulong_t l);
/**
 * @brief Initializes `dst` with `l`.
 * @note This function never fails.
 */
ULBN_PUBLIC ulbi_t* ulbi_init_slong(ulbi_t* dst, ulbn_slong_t l);


/**
 * @brief Swappes `o1` and `o2`.
 * @note This function never fails.
 */
ULBN_PUBLIC void ulbi_swap(ulbi_t* o1, ulbi_t* o2);
/**
 * @brief `ro` = -`ao`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory and `ro` != `ao`.
 */
ULBN_PUBLIC int ulbi_neg(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao);
/**
 * @brief `ro` = abs(`ao`).
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory and `ro` != `ao`.
 */
ULBN_PUBLIC int ulbi_abs(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao);


/**
 * @brief Copies `src` to `dst`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory and `dst` != `src`.
 */
ULBN_PUBLIC int ulbi_set_copy(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* src);
/**
 * @brief Moves `src` to `dst`
 * @note This function never fails; after that `src` will be as if `ulbi_deinit` was called.
 */
ULBN_PUBLIC void ulbi_set_move(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbi_t* src);
/**
 * @brief Sets `dst` to 2^`n`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_set_2exp_bits(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_bits_t n);
/**
 * @brief Sets `dst` to 2^`n`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_INEXACT` if `n` is negative (and `dst` will be set to 0);
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_set_2exp_sbits(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_sbits_t n);
/**
 * @brief Sets `dst` to 2^`n`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_INEXACT` if `n` is negative (and `dst` will be set to 0);
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_set_2exp(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* n);

/**
 * @brief Sets `dst` to the integer represented by `*pstr` in base `base`, and write the pointer back to `*pstr`.
 * @note This function stops parsing when it encounters the first illegal character,
 *       so it's safe to pass `SIZE_MAX` to `len` and this functions will stop at `(char)0`.
 * @param base 0 means automatic detection (according to the prefix); 2-36 means the base; otherwise, it is invalid.
 * @param flag Combination of `ULBN_SET_STRING_FLAG_ENUM`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `base` is invalid;
 * @return `ULBN_ERR_EXCEED_RANGE` if some value is too large when calculating the result;
 * @return `ULBN_ERR_INEXACT` if the number represented by the string cannot be exactly represented as an integer;
 * @return `ULBN_ERR_INEXACT` if the string represents some form of -0.
 */
ULBN_PUBLIC int ulbi_set_string_ex(
  const ulbn_alloc_t* alloc, ulbi_t* dst,           /* */
  const char** pstr, size_t len, int base, int flag /* */
);
/**
 * @brief Sets `dst` to the integer represented by 0-ended `str` in base `base`.
 * @param base 0 means automatic detection (according to the prefix); 2-36 means the base; otherwise, it is invalid.
 * @note it's equivalent to
 *       `ulbi_set_string_ex(alloc, dst, &str, SIZE_MAX, base, ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX)`
 *       and check if `str` is fully parsed and ignore `ULBN_ERR_INEXACT` (this function won't accpet decimal part)
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `base` is invalid;
 * @return `ULBN_ERR_EXCEED_RANGE` if some value is too large when calculating the result;
 * @return `ULBN_ERR_INVALID` if the string cannot be fully parsed as an integer
 *         (but the result is still stored, so you can ignore it).
 */
ULBN_PUBLIC int ulbi_set_string(const ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, int base);
/**
 * @brief Sets `dst` to the integer represented by `str` in base `base`.
 * @param base 0 means automatic detection (according to the prefix); 2-36 means the base; otherwise, it is invalid.
 * @note it's equivalent to
 *       `ulbi_set_string_ex(alloc, dst, &str, len, base, ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX)`
 *       and check if `str` is fully parsed and ignore `ULBN_ERR_INEXACT` (this function won't accpet decimal part)
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `base` is invalid;
 * @return `ULBN_ERR_EXCEED_RANGE` if some value is too large when calculating the result;
 * @return `ULBN_ERR_INVALID` if the string cannot be fully parsed as an integer
 *         (but the result is still stored, so you can ignore it).
 */
ULBN_PUBLIC int ulbi_set_string_len(const ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, size_t len, int base);

/**
 * @brief Sets `dst` to the unsigned integer represented by `bytes` in little-endian.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_set_bytes_unsigned_le(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
);
/**
 * @brief Sets `dst` to the unsigned integer represented by `bytes` in big-endian.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_set_bytes_unsigned_be(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
);
/**
 * @brief Sets `dst` to the signed integer represented by `bytes` in little-endian.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_set_bytes_signed_le(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
);
/**
 * @brief Sets `dst` to the signed integer represented by `bytes` in big-endian.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_set_bytes_signed_be(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
);
/**
 * @brief Sets `dst` to the unsigned integer represented by `bytes`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_set_bytes_unsigned(
  const ulbn_alloc_t* alloc, ulbi_t* dst,          /* */
  const void* bytes, size_t len, int is_big_endian /* */
);
/**
 * @brief Sets `dst` to the signed integer represented by `bytes`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_set_bytes_signed(
  const ulbn_alloc_t* alloc, ulbi_t* dst,          /* */
  const void* bytes, size_t len, int is_big_endian /* */
);


/**
 * @brief Initializes `dst` as a copy of `src`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_init_copy(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* src);
/**
 * @brief Initializes `dst` as a move from `src`.
 * @note This function never fails; after this `src` will be as if `ulbi_deinit` was called.
 */
ULBN_PUBLIC void ulbi_init_move(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbi_t* src);
/**
 * @brief Initializes `dst` with 2^`n`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_init_2exp_bits(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_bits_t n);
/**
 * @brief Initializes `dst` with 2^`n`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_INEXACT` if `n` is negative (and `dst` will be set to 0);
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_init_2exp_sbits(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_sbits_t n);
/**
 * @brief Initializes `dst` with 2^`n`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_INEXACT` if `n` is negative (and `dst` will be set to 0);
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_2exp(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* n);
/**
 * @brief Initializes `dst` with the integer represented by 0-ended `str` in base `base`.
 * @note This function stops parsing when it encounters the first illegal character.
 * @param base 0 means automatic detection (according to the prefix); 2-36 means the base; otherwise, it is invalid.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `base` is invalid;
 * @return `ULBN_ERR_EXCEED_RANGE` if some value is too large when calculating the result;
 * @return `ULBN_ERR_INVALID` if the string cannot be fully parsed as an integer
 *         (but the result is still stored, so you can ignore it).
 */
ULBN_PUBLIC int ulbi_init_string(const ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, int base);
/**
 * @brief Initializes `dst` with the integer represented by 0-ended `str` in base `base`.
 * @note This function stops parsing when it encounters the first illegal character.
 * @param base 0 means automatic detection (according to the prefix); 2-36 means the base; otherwise, it is invalid.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `base` is invalid;
 * @return `ULBN_ERR_EXCEED_RANGE` if some value is too large when calculating the result;
 * @return `ULBN_ERR_INVALID` if the string cannot be fully parsed as an integer
 *         (but the result is still stored, so you can ignore it).
 */
ULBN_PUBLIC int ulbi_init_string_len(const ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, size_t len, int base);

/**
 * @brief Initializes `dst` with the unsigned integer represented by `bytes` in little-endian.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_init_bytes_unsigned_le(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
);
/**
 * @brief Initializes `dst` with the unsigned integer represented by `bytes` in big-endian.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_init_bytes_unsigned_be(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
);
/**
 * @brief Initializes `dst` with the signed integer represented by `bytes` in little-endian.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_init_bytes_signed_le(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
);
/**
 * @brief Initializes `dst` with the signed integer represented by `bytes` in big-endian.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_init_bytes_signed_be(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
);
/**
 * @brief Initializes `dst` with the unsigned integer represented by `bytes`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_init_bytes_unsigned(
  const ulbn_alloc_t* alloc, ulbi_t* dst,          /* */
  const void* bytes, size_t len, int is_big_endian /* */
);
/**
 * @brief Initializes `dst` with the signed integer represented by `bytes`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `len` is too large.
 */
ULBN_PUBLIC int ulbi_init_bytes_signed(
  const ulbn_alloc_t* alloc, ulbi_t* dst,          /* */
  const void* bytes, size_t len, int is_big_endian /* */
);


/**
 * @brief `ao` <=> `bo`
 * @return <0 if `ao` < `bo`;
 * @return 0 if `ao` == `bo`;
 * @return >0 if `ao` > `bo`.
 */
ULBN_PUBLIC int ulbi_comp(const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ao` <=> `b`
 * @return <0 if `ao` < `b`;
 * @return 0 if `ao` == `b`;
 * @return >0 if `ao` > `b`.
 */
ULBN_PUBLIC int ulbi_comp_limb(const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief `ao` <=> `b`
 * @return <0 if `ao` < `b`;
 * @return 0 if `ao` == `b`;
 * @return >0 if `ao` > `b`.
 */
ULBN_PUBLIC int ulbi_comp_slimb(const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief `ao` <=> `b`
 * @return <0 if `ao` < `b`;
 * @return 0 if `ao` == `b`;
 * @return >0 if `ao` > `b`.
 */
ULBN_PUBLIC int ulbi_comp_ulong(const ulbi_t* ao, ulbn_ulong_t b);
/**
 * @brief `ao` <=> `b`
 * @return <0 if `ao` < `b`;
 * @return 0 if `ao` == `b`;
 * @return >0 if `ao` > `b`.
 */
ULBN_PUBLIC int ulbi_comp_slong(const ulbi_t* ao, ulbn_slong_t b);

/**
 * @brief Returns `ao` == `bo`.
 */
ULBN_PUBLIC int ulbi_eq(const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief Returns `ao` == `b`.
 */
ULBN_PUBLIC int ulbi_eq_limb(const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief Returns `ao` == `b`.
 */
ULBN_PUBLIC int ulbi_eq_slimb(const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief Returns `ao` == `b`.
 */
ULBN_PUBLIC int ulbi_eq_ulong(const ulbi_t* ao, ulbn_ulong_t b);
/**
 * @brief Returns `ao` == `b`.
 */
ULBN_PUBLIC int ulbi_eq_slong(const ulbi_t* ao, ulbn_slong_t b);


/**
 * @brief Gets the sign of `o`.
 * @return `1` if `o` is positive;
 * @return `-1` if `o` is negative;
 * @return `0` if `o` is zero.
 */
ULBN_PUBLIC int ulbi_sign(const ulbi_t* o);
/**
 * @brief Checks if `o` is zero.
 * @return `1` if `o` is zero;
 * @return `0` if `o` is not zero.
 */
ULBN_PUBLIC int ulbi_is_zero(const ulbi_t* o);
/**
 * @brief Checks if `o` is even.
 * @return `1` if `o` is even;
 * @return `0` if `o` is not even
 */
ULBN_PUBLIC int ulbi_is_even(const ulbi_t* o);
/**
 * @brief Checks if `o` is odd.
 * @return `1` if `o` is odd;
 * @return `0` if `o` is not odd.
 */
ULBN_PUBLIC int ulbi_is_odd(const ulbi_t* o);


/**
 * @brief `ro` = `ao` + `bo`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_add(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ro` = `ao` - `bo`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_sub(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);

/**
 * @brief `ro` = `ao` + `b`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_add_limb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief `ro` = `ao` - `b`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_sub_limb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief `ro` = `a` - `bo`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_limb_sub(const ulbn_alloc_t* alloc, ulbi_t* ro, ulbn_limb_t a, const ulbi_t* bo);

/**
 * @brief `ro` = `ao` + `b`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_add_slimb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief `ro` = `ao` - `b`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_sub_slimb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief `ro` = `a` - `bo`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_slimb_sub(const ulbn_alloc_t* alloc, ulbi_t* ro, ulbn_slimb_t a, const ulbi_t* bo);


/**
 * @brief `ro` = `ao` * `b`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_mul_limb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief `ro` = `ao` * `b`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_mul_slimb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief `ro` = `ao` * `bo`.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_mul(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);


/**
 * @brief `qo` = `ao` // `bo`, `ro` = `ao` % `bo`.
 * @note `qo` and `ro` is allowed to be `NULL`.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if `ro` is NULL and the remainder is not zero;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod(const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `qo` = `ao` // `bo`, `ro` = `ao` % `bo`.
 * @note `qo` and `ro` are allowed to be `NULL`.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INVALID` if `round_mode` is illegal;
 * @return `ULBN_ERR_INEXACT` if the remainder is not zero and (`ro` is NULL or `round_mode` is `ULBN_ROUND_FAIL`);
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, const ulbi_t* bo,                /* */
  enum ULBN_ROUND_ENUM round_mode                    /* */
);

/**
 * @brief `qo` = `ao` // `b`, `ro` = The smallest non-negative number congruent to (`ao` % `b`) under modulo `b`.
 * @note `qo` and `ro` are allowed to be `NULL`;
 * @note The representation of `ro` is different from `ulbi_divmod` because `ro` cannot store negative values
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if the remainder is not zero and `ro` is NULL;
 * @return `ULBN_ERR_INEXACT` if `ro` is not NULL but the remainder is negative;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod_limb(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_limb_t* ro, /* */
  const ulbi_t* ao, ulbn_limb_t b                         /* */
);
/**
 * @brief `qo` = `ao` // `b`, `ro` = The smallest non-negative number congruent to (`ao` % `b`) under modulo `b`.
 * @note `qo` and `ro` are allowed to be `NULL`;
 * @note The representation of `ro` is different from `ulbi_divmod` because `ro` cannot store negative values
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INVALID` if `round_mode` is illegal;
 * @return `ULBN_ERR_INEXACT` if the remainder is not zero and (`ro` is NULL or `round_mode` is `ULBN_ROUND_FAIL`);
 * @return `ULBN_ERR_INEXACT` if `ro` is not NULL but the remainder is negative;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod_limb_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_limb_t* ro, /* */
  const ulbi_t* ao, ulbn_limb_t b,                        /* */
  enum ULBN_ROUND_ENUM round_mode                         /* */
);

/**
 * @brief `qo` = `ao` // `b`, `ro` = `ao` % `b`.
 * @note `qo` and `ro` is allowed to be `NULL`;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if the remainder is not zero and `ro` is NULL;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod_slimb(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_slimb_t* ro, /* */
  const ulbi_t* ao, ulbn_slimb_t b                         /* */
);
/**
 * @brief `qo` = `ao` // `b`, `ro` = `ao` % `b`.
 * @note `qo` and `ro` is allowed to be `NULL`;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INVALID` if `round_mode` is illegal;
 * @return `ULBN_ERR_INEXACT` if the ramainder is not zero and (`ro` is NULL or `round_mode` is `ULBN_ROUND_FAIL`);
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod_slimb_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_slimb_t* ro, /* */
  const ulbi_t* ao, ulbn_slimb_t b,                        /* */
  enum ULBN_ROUND_ENUM round_mode                          /* */
);


/**
 * @brief `qo` = `ao` // (2**`e`), `ro` = `ao` % (2**`e`).
 * @note `qo` and `ro` are allowed to be `NULL`.
 * @note If `qo` and `ro` are NULL, this function won't allocate any memory.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if `ro` is NULL and the remainder is not zero;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod_2exp_bits(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_bits_t e                    /* */
);
/**
 * @brief `qo` = `ao` / (2**`e`), `ro` = `ao` % (2**`e`).
 * @note `qo` and `ro` are allowed to be `NULL`.
 * @note If `qo` and `ro` are NULL, this function won't allocate any memory.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if `ro` is NULL and the remainder is not zero;
 * @return `ULBN_ERR_EXCEED_RANGE` if `e` is negative and very large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod_2exp_sbits(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_sbits_t e                   /* */
);
/**
 * @brief `qo` = `ao` / (2**`e`), `ro` = `ao` % (2**`e`).
 * @note `qo` and `ro` are allowed to be `NULL`.
 * @note If `qo` and `ro` are NULL, this function won't allocate any memory.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if `ro` is NULL and the remainder is not zero;
 * @return `ULBN_ERR_EXCEED_RANGE` if `e` is negative and very large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod_2exp(const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* eo);

/**
 * @brief `qo` = `ao` // (2**`e`), `ro` = `ao` % (2**`e`).
 * @note `qo` and `ro` are allowed to be `NULL`.
 * @note If `qo` and `ro` are NULL, this function won't allocate any memory.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INVALID` if `round_mode` is illegal;
 * @return `ULBN_ERR_INEXACT` if the ramainder is not zero and (`ro` is NULL or `round_mode` is `ULBN_ROUND_FAIL`);
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod_2exp_bits_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_bits_t e,                   /* */
  enum ULBN_ROUND_ENUM round_mode                    /* */
);
/**
 * @brief `qo` = `ao` / (2**`e`), `ro` = `ao` % (2**`e`).
 * @note `qo` and `ro` are allowed to be `NULL`.
 * @note If `qo` and `ro` are NULL, this function won't allocate any memory.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INVALID` if `round_mode` is illegal;
 * @return `ULBN_ERR_INEXACT` if the ramainder is not zero and (`ro` is NULL or `round_mode` is `ULBN_ROUND_FAIL`);
 * @return `ULBN_ERR_EXCEED_RANGE` if `e` is negative and very large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod_2exp_sbits_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_sbits_t e,                  /* */
  enum ULBN_ROUND_ENUM round_mode                    /* */
);
/**
 * @brief `qo` = `ao` / (2**`e`), `ro` = `ao` % (2**`e`).
 * @note `qo` and `ro` are allowed to be `NULL`.
 * @note If `qo` and `ro` are NULL, this function won't allocate any memory.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INVALID` if `round_mode` is illegal;
 * @return `ULBN_ERR_INEXACT` if the ramainder is not zero and (`ro` is NULL or `round_mode` is `ULBN_ROUND_FAIL`);
 * @return `ULBN_ERR_EXCEED_RANGE` if `e` is negative and very large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_divmod_2exp_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, const ulbi_t* eo,                /* */
  enum ULBN_ROUND_ENUM round_mode                    /* */
);


/**
 * @brief `ro` = `ao` ** b.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_pow_ulong(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ulong_t b);
/**
 * @brief `ro` = `ao` ** b.
 * @return `0` if successful;
 * @return `ULBN_ERR_DIV_BY_ZERO` if `ao` = 0 and `b` < 0 (in this case, `ro` is set to 0);
 * @return `ULBN_ERR_INEXACT` if `b` < 0 (in this case, `ro` is set to 0);
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_pow_slong(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slong_t b);
/**
 * @brief `ro` = `ao` ** b.
 * @return `0` if successful;
 * @return `ULBN_ERR_DIV_BY_ZERO` if `ao` = 0 and `b` < 0 (in this case, `ro` is set to 0);
 * @return `ULBN_ERR_INEXACT` if `b` < 0 (in this case, `ro` is set to 0);
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_pow(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b);


/**
 * @brief Calculates the square root of `ao`, and store the result in `so` and the remainder in `ro`.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INVALID` if `ao` < 0 (and `so` and `ro` will be set to 0);
 * @return `ULBN_ERR_INEXACT` if `ro` == NULL and the remainder is not zero;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_sqrtrem(const ulbn_alloc_t* alloc, ulbi_t* so, ulbi_t* ro, const ulbi_t* ao);
/**
 * @brief Calculates the square root of `ao`, and store the result in `so`.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INVALID` if `ao` < 0 (and `so` and `ro` will be set to 0);
 * @return `ULBN_ERR_INEXACT` if the remainder is not zero;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_sqrt(const ulbn_alloc_t* alloc, ulbi_t* so, const ulbi_t* ao);
/**
 * @brief Calculates the k-th root of `ao` (round to zero), and store the result in `so` and the remainder in `ro`.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INVALID` if `eo` = 0 (and `so` and `ro` will be set to 0);
 * @return `ULBN_ERR_DIV_BY_ZERO` if `ao` = 0 and `eo` < 0 (and `so` and `ro` will be set to 0);
 * @return `ULBN_ERR_INVALID` if `ao` < 0 and `eo` is even (and `so` and `ro` will be set to 0);
 * @return `ULBN_ERR_INEXACT` if `ao` - trunc(rootn(`ao`, `eo`)) ** `eo` != 0 and `ro` is NULL;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_rootrem(const ulbn_alloc_t* alloc, ulbi_t* so, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* eo);
/**
 * @brief Calculates the k-th root of `ao` (round to zero), and store the result in `so`.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INVALID` if `eo` = 0 (and `so` will be set to 0);
 * @return `ULBN_ERR_DIV_BY_ZERO` if `ao` = 0 and `eo` < 0 (and `so` will be set to 0);
 * @return `ULBN_ERR_INVALID` if `ao` < 0 and `eo` is even (and `so` will be set to 0);
 * @return `ULBN_ERR_INEXACT` if `ao` - trunc(rootn(`ao`, `eo`)) ** `eo` != `ao`;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_root(const ulbn_alloc_t* alloc, ulbi_t* so, const ulbi_t* ao, const ulbi_t* eo);

/**
 * @brief `ro` = `ao` & `bo`.
 * @note The calculation is performed in the sense of two's complement.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_and(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ro` = `ao` | `bo`.
 * @note The calculation is performed in the sense of two's complement.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_or(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ro` = `ao` ^ `bo`.
 * @note The calculation is performed in the sense of two's complement.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_xor(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ro` = ~`ao`.
 * @note The calculation is performed in the sense of two's complement.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_com(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao);


/**
 * @brief `ro` = `ao` << `b`.
 * @note The calculation is performed in the sense of two's complement.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_sal_bits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_bits_t b);
/**
 * @brief `ro` = `ao` >> `b`.
 * @note The calculation is performed in the sense of two's complement.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_sar_bits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_bits_t b);

/**
 * @brief `ro` = `ao` << `b`.
 * @note The calculation is performed in the sense of two's complement.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_sal_sbits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_sbits_t b);
/**
 * @brief `ro` = `ao` >> `b`
 * @note The calculation is performed in the sense of two's complement
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_sar_sbits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_sbits_t b);

/**
 * @brief `ro` = `ao` << `b`.
 * @note The calculation is performed in the sense of two's complement.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_sal(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b);
/**
 * @brief `ro` = `ao` >> `b`.
 * @note The calculation is performed in the sense of two's complement.
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_sar(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b);


/**
 * @brief Tests whether the k-th bit is 1 in the sense of two's complement.
 * @return 0 if the k-th bit is 0;
 * @return 1 if the k-th bit is 1.
 */
ULBN_PUBLIC int ulbi_testbit_bits(const ulbi_t* o, ulbn_bits_t k);
/**
 * @brief Sets the k-th bit to 1 in two's complement representation.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return The original value of the k-th bit otherwise.
 */
ULBN_PUBLIC int ulbi_setbit_bits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_bits_t k);
/**
 * @brief Sets the k-th bit to 0 in two's complement representation.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return The original value of the k-th bit otherwise.
 */
ULBN_PUBLIC int ulbi_resetbit_bits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_bits_t k);
/**
 * @brief Flippes the k-th bit in two's complement representation.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return The original value of the k-th bit otherwise.
 */
ULBN_PUBLIC int ulbi_combit_bits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_bits_t k);

/**
 * @brief Tests whether the k-th bit is 1 in the sense of two's complement.
 * @note Fractional bits are always 0 in integer representation.
 * @return 0 if the k-th bit is 0;
 * @return 1 if the k-th bit is 1.
 */
ULBN_PUBLIC int ulbi_testbit_sbits(const ulbi_t* o, ulbn_sbits_t k);
/**
 * @brief Sets the k-th bit to 1 in two's complement representation.
 * @note Fractional bits are always 0 in integer representation.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_INEXACT` if `k` is negative;
 * @return The original value of the k-th bit otherwise.
 */
ULBN_PUBLIC int ulbi_setbit_sbits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_sbits_t k);
/**
 * @brief Sets the k-th bit to 0 in two's complement representation.
 * @note Fractional bits are always 0 in integer representation.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return The original value of the k-th bit otherwise.
 */
ULBN_PUBLIC int ulbi_resetbit_sbits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_sbits_t k);
/**
 * @brief Flippes the k-th bit in two's complement representation.
 * @note Fractional bits are always 0 in integer representation.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is too large;
 * @return `ULBN_ERR_INEXACT` if `k` is negative;
 * @return The original value of the k-th bit otherwise.
 */
ULBN_PUBLIC int ulbi_combit_sbits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_sbits_t k);

/**
 * @brief Tests whether the k-th bit is 1 in the sense of two's complement.
 * @note Fractional bits are always 0 in integer representation.
 * @return 0 if the k-th bit is 0;
 * @return 1 if the k-th bit is 1.
 */
ULBN_PUBLIC int ulbi_testbit(const ulbi_t* o, const ulbi_t* k);
/**
 * @brief Sets the k-th bit to 1 in two's complement representation.
 * @note Fractional bits are always 0 in integer representation.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if too large;
 * @return `ULBN_ERR_INEXACT` if `k` is negative;
 * @return The original value of the k-th bit otherwise.
 */
ULBN_PUBLIC int ulbi_setbit(const ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k);
/**
 * @brief Sets the k-th bit to 0 in two's complement representation.
 * @note Fractional bits are always 0 in integer representation.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if too large;
 * @return The original value of the k-th bit otherwise.
 */
ULBN_PUBLIC int ulbi_resetbit(const ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k);
/**
 * @brief Flippes the k-th bit in two's complement representation.
 * @note Fractional bits are always 0 in integer representation.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if too large;
 * @return `ULBN_ERR_INEXACT` if `k` is negative;
 * @return The original value of the k-th bit otherwise.
 */
ULBN_PUBLIC int ulbi_combit(const ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k);


/**
 * @brief Converts `ao` to a number within the range of an n-bit unsigned binary number.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_as_uint_usize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b);
/**
 * @brief Converts `ao` to a number within the range of an n-bit signed binary number.
 * @note If `b` == 2, the valid range of the number is -1 and 0.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_as_int_usize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b);

/**
 * @brief Converts `ao` to a number within the range of an n-bit unsigned binary number.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `b` is negative;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_as_uint_ssize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t b);
/**
 * @brief Converts `ao` to a number within the range of an n-bit signed binary number.
 * @note If `b` == 2, the valid range of the number is -1 and 0.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `b` is negative;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_as_int_ssize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t b);

/**
 * @brief Converts `ao` to a number within the range of an n-bit unsigned binary number.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if too large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_as_uint_bits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_bits_t b);
/**
 * @brief Converts `ao` to a number within the range of an n-bit signed binary number.
 * @note If `b` == 2, the valid range of the number is -1 and 0.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if too large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_as_int_bits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_bits_t b);

/**
 * @brief Converts `ao` to a number within the range of an n-bit unsigned binary number.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if too large;
 * @return `ULBN_ERR_EXCEED_RANGE` if `b` is negative;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_as_uint_sbits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_sbits_t b);
/**
 * @brief Converts `ao` to a number within the range of an n-bit signed binary number.
 * @note If `b` == 2, the valid range of the number is -1 and 0.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if too large;
 * @return `ULBN_ERR_EXCEED_RANGE` if `b` is negative;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_as_int_sbits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_sbits_t b);

/**
 * @brief Converts `ao` to a number within the range of an n-bit unsigned binary number.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if too large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_as_uint(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b);
/**
 * @brief Converts `ao` to a number within the range of an n-bit unsigned binary number.
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if too large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_as_int(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b);


/**
 * @brief Checks if `o` is a power of 2.
 */
ULBN_PUBLIC int ulbi_is_2pow(const ulbi_t* o);
/**
 * @brief Returns the number of trailing zeros in the two's complement representation of `o`.
 * @note If `ro` == 0, return 0.
 */
ULBN_PUBLIC ulbn_bits_t ulbi_ctz(const ulbi_t* ro);
/**
 * @brief Returns the number of trailing ones in the two's complement representation of `o`.
 * @note If `ro` == 0, return 0.
 */
ULBN_PUBLIC ulbn_bits_t ulbi_cto(const ulbi_t* ro);
/**
 * @brief Returns the number of 1s in the binary representation of the absolute value of `ro`.
 */
ULBN_PUBLIC ulbn_bits_t ulbi_abs_popcount(const ulbi_t* ro);
/**
 * @brief Gets the minimum number of bits required to represent the absolute value of `ro`.
 * @note If `ro` == 0, return 0.
 */
ULBN_PUBLIC ulbn_bits_t ulbi_abs_bit_width(const ulbi_t* ro);


/**
 * @brief Converts `src` to `ulbn_limb_t` type.
 */
ULBN_PUBLIC ulbn_limb_t ulbi_to_limb(const ulbi_t* src);
/**
 * @brief Converts `src` to `ulbn_slimb_t` type.
 */
ULBN_PUBLIC ulbn_slimb_t ulbi_to_slimb(const ulbi_t* src);
/**
 * @brief Converts `src` to `ulbn_ulong_t` type.
 */
ULBN_PUBLIC ulbn_ulong_t ulbi_to_ulong(const ulbi_t* src);
/**
 * @brief Converts `src` to `ulbn_slong_t` type.
 */
ULBN_PUBLIC ulbn_slong_t ulbi_to_slong(const ulbi_t* src);

/**
 * @brief Checks if `src` can be represented as `ulbn_limb_t`.
 */
ULBN_PUBLIC int ulbi_fit_limb(const ulbi_t* src);
/**
 * @brief Checks if `src` can be represented as `ulbn_slimb_t`.
 */
ULBN_PUBLIC int ulbi_fit_slimb(const ulbi_t* src);
/**
 * @brief Checks if `src` can be represented as `ulbn_ulong_t`.
 */
ULBN_PUBLIC int ulbi_fit_ulong(const ulbi_t* src);
/**
 * @brief Checks if `src` can be represented as `ulbn_slong_t`.
 */
ULBN_PUBLIC int ulbi_fit_slong(const ulbi_t* src);


/**
 * @brief Converts `ao` to signed integer.
 */
ULBN_PUBLIC void ulbi_to_bytes_signed(const ulbi_t* ao, void* dst, size_t size, int is_big_endian);
/**
 * @brief Converts `ao` to signed integer in little-endian.
 */
ULBN_PUBLIC void ulbi_to_bytes_signed_le(const ulbi_t* ao, void* dst, size_t size);
/**
 * @brief Converts `ao` to signed integer in big-endian.
 */
ULBN_PUBLIC void ulbi_to_bytes_signed_be(const ulbi_t* ao, void* dst, size_t size);


/**
 * @brief Converts `ao` to a string.
 *
 * @param p_len If not `NULL`, the length of the string will be written into it.
 * @param p_alloced The number of bytes allocated.
 * @param alloc_func Allocation function, ensuring the passed `ptr` is used for the returned string.
 *                   If `NULL` is passed, `alloc` will be used;
 *                   and then you need to call `ulbn_dealloc` to free the memory.
 * @param alloc_opaque Parameter for the allocation function.
 * @param base String base (2 <= base <= 36 with uppercase letters, -36 <= base <= -2 with lowercase letters).
 *
 * @return String if successful (allocated by alloc_func);
 * @return `NULL` if out of memory (considered as `ULBN_ERR_NOMEM`);
 * @return `NULL` if the base is invalid (considered as `ULBN_ERR_EXCEED_RANGE`).
 */
ULBN_PUBLIC char* ulbi_to_string_alloc(
  const ulbn_alloc_t* alloc, size_t* p_len, size_t* p_alloced, /* */
  ulbn_alloc_func_t* alloc_func, void* alloc_opaque,           /* */
  const ulbi_t* ao, int base                                   /* */
);
/**
 * @brief Prints `o` with `printer`.
 * @note The `printer` function should return 0 if successful; otherwise, it should return a non-zero value.
 * @warning It's unsafe to throw an exception or do a no-return operation in the `printer` function.
 *
 * @param base String base (2 <= base <= 36 with uppercase letters, -36 <= base <= -2 with lowercase letters).
 *
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `base` is invalid;
 * @return `ULBN_ERR_EXTERNAL` if `printer` returns non-zero;
 * @return `0` if successful.
 */
ULBN_PUBLIC int ulbi_print_ex(
  const ulbn_alloc_t* alloc, ulbn_printer_t* printer, void* opaque, /* */
  const ulbi_t* ao, int base                                        /* */
);
/**
 * @brief Prints `o` to `fp`.
 *
 * @param base String base (2 <= base <= 36 with uppercase letters, -36 <= base <= -2 with lowercase letters).
 *
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `base` is invalid;
 * @return `ULBN_ERR_EXTERNAL` if write to `fp` failed;
 * @return `0` if successful.
 */
ULBN_PUBLIC int ulbi_print(const ulbn_alloc_t* alloc, FILE* fp, const ulbi_t* ao, int base);


  #if ULBN_CONF_HAS_FLOAT
/**
 * @brief Sets `dst` to `x`.
 * @return `0` if `x` can be exactly represented as an integer;
 * @return `ULBN_ERR_INEXACT` if `x` cannot be exactly represented as an integer (in this case `x` will be truncated);
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_set_float(const ulbn_alloc_t* alloc, ulbi_t* dst, float x);
/**
 * @brief Initializes `dst` with `x`.
 * @return `0` if `x` can be exactly represented as an integer;
 * @return `ULBN_ERR_INEXACT` if `x` cannot be exactly represented as an integer (in this case `x` will be truncated);
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_init_float(const ulbn_alloc_t* alloc, ulbi_t* dst, float x);
/**
 * @brief Converts `src` to `float` type.
 */
ULBN_PUBLIC float ulbi_to_float(const ulbi_t* src);
/**
 * @brief Checks if `src` can be represented as `float`.
 */
ULBN_PUBLIC int ulbi_fit_float(const ulbi_t* src);
  #endif /* ULBN_CONF_HAS_FLOAT */


  #if ULBN_CONF_HAS_DOUBLE
/**
 * @brief Sets `dst` to `x`.
 * @return `0` if `x` can be exactly represented as an integer;
 * @return `ULBN_ERR_INEXACT` if `x` cannot be exactly represented as an integer (in this case `x` will be truncated);
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_set_double(const ulbn_alloc_t* alloc, ulbi_t* dst, double x);
/**
 * @brief Initializes `dst` with `x`.
 * @return `0` if `x` can be exactly represented as an integer;
 * @return `ULBN_ERR_INEXACT` if `x` cannot be exactly represented as an integer (in this case `x` will be truncated);
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_init_double(const ulbn_alloc_t* alloc, ulbi_t* dst, double x);
/**
 * @brief Converts `src` to `double` type.
 */
ULBN_PUBLIC double ulbi_to_double(const ulbi_t* src);
/**
 * @brief Checks if `src` can be represented as `double`.
 */
ULBN_PUBLIC int ulbi_fit_double(const ulbi_t* src);
  #endif /* ULBN_CONF_HAS_DOUBLE */


  #if ULBN_CONF_HAS_LONG_DOUBLE
/**
 * @brief Sets `dst` to `x`.
 * @return `0` if `x` can be exactly represented as an integer;
 * @return `ULBN_ERR_INEXACT` if `x` cannot be exactly represented as an integer (in this case `x` will be truncated);
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_set_long_double(const ulbn_alloc_t* alloc, ulbi_t* dst, long double x);
/**
 * @brief Initializes `dst` with `x`.
 * @return `0` if `x` can be exactly represented as an integer;
 * @return `ULBN_ERR_INEXACT` if `x` cannot be exactly represented as an integer (in this case `x` will be truncated);
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_init_long_double(const ulbn_alloc_t* alloc, ulbi_t* dst, long double x);
/**
 * @brief Converts `src` to `long double` type.
 */
ULBN_PUBLIC long double ulbi_to_long_double(const ulbi_t* src);
/**
 * @brief Checks if `src` can be represented as `long double`.
 */
ULBN_PUBLIC int ulbi_fit_long_double(const ulbi_t* src);
  #endif /* ULBN_CONF_HAS_LONG_DOUBLE */


  #if ULBN_CONF_USE_RAND
/**
 * @brief Sets `dst` to a random number in the range [0, 2**n).
 *
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_set_rand_bits(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_bits_t n);
/**
 * @brief Sets `dst` to a random number in the range [0, 2**n).
 *
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is negative;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_set_rand_sbits(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_sbits_t n);
/**
 * @brief Sets `dst` to a random number in the range [0, 2**n).
 *
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_set_rand(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* n);
/**
 * @brief Initializes `dst` with a random number in the range [0, 2**n).
 *
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_init_rand_bits(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_bits_t n);
/**
 * @brief Initializes `dst` with a random number in the range [0, 2**n).
 *
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is negative;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_init_rand_sbits(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_sbits_t n);
/**
 * @brief Initializes `dst` with a random number in the range [0, 2**n).
 *
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `0` otherwise.
 */
ULBN_PUBLIC int ulbi_init_rand(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* n);

/**
 * @brief Sets `dst` to a random number in the range [0, limit).
 */
ULBN_PUBLIC int ulbi_set_rand_range(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* limit);
/**
 * @brief Sets `dst` to a random number in the range [lo, hi).
 * @note If `lo` > `hi`, swap them.
 */
ULBN_PUBLIC int ulbi_set_rand_range2(
  const ulbn_alloc_t* alloc, ulbn_rand_t* rng,    /* */
  ulbi_t* dst, const ulbi_t* lo, const ulbi_t* hi /* */
);
/**
 * @brief Initializes `dst` with a random number in the range [0, limit).
 */
ULBN_PUBLIC int ulbi_init_rand_range(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* limit);
/**
 * @brief Initializes `dst` with a random number in the range [lo, hi).
 * @note If `lo` > `hi`, swap them.
 */
ULBN_PUBLIC int ulbi_init_rand_range2(
  const ulbn_alloc_t* alloc, ulbn_rand_t* rng,    /* */
  ulbi_t* dst, const ulbi_t* lo, const ulbi_t* hi /* */
);
  #endif /* ULBN_CONF_USE_RAND */


/**
 * @brief `ro` = gcd(abs(`ao`), abs(`bo`)).
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_gcd(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ro` = gcd(abs(`ao`), `b`).
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_gcd_limb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief `ro` = gcd(abs(`ao`), abs(`b`)).
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_gcd_slimb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief `ro` = lcm(abs(`ao`), abs(`bo`)).
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory.
 */
ULBN_PUBLIC int ulbi_lcm(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);

/**
 * @brief Calculates `g,u,v` makes `g = u*a + v*b = gcd(a,b)`.
 * @note `go`, `uo`, `vo` are allowed to be `NULL`.
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if overflow when calculating;
 * @return `ULBN_ERR_INVALID` if `go` is `NULL` and `gcd(a,b) != 1`.
 */
ULBN_PUBLIC int ulbi_gcdext(
  const ulbn_alloc_t* alloc, ulbi_t* go, ulbi_t* uo, ulbi_t* vo, /* */
  const ulbi_t* ao, const ulbi_t* bo                             /* */
);
/**
 * @brief Calculates the modular inverse of `a` modulo `m` (`a*b = 1 (mod m)`).
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if overflow when calculating;
 * @return `ULBN_ERR_INVALID` if there is no modular inverse.
 */
ULBN_PUBLIC int ulbi_invert(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* mo);
#endif /* ULBN_CONF_BIG_INT */


/*******
 * End *
 *******/


#ifdef __cplusplus
}
#endif

#if ULBN_CONF_IMPLE
  #ifndef ULBN_SOURCE
    #include "ulbn.c"
  #endif
#endif

#endif /* ULBN_HEADER */
