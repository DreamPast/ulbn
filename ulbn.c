/*
ulbn - Big Number Library

# Requirements
  - C89/C++98
  - `CHAR_BIT` or `sizeof(ulbn_limb_t)` should be even

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
#ifndef ULBN_SOURCE
#define ULBN_SOURCE

#ifndef ULBN_HEADER
  #include "ulbn.h"
#endif
#include <assert.h> /* assert */
#include <limits.h> /* CHAR_BIT, UCHAR_MAX, UINT_MAX, INT_MAX */
#include <stdio.h>  /* FILE*, fwrite, (printf, fprintf, fputc, fputs) */
#include <stdlib.h> /* free, realloc */
#include <string.h> /* memset, memcpy, memmove, memcmp */

#if defined(ULBN_CONF_USE_RAND)
  #include <time.h> /* clock, time */
#endif
#if defined(ULBN_CONF_HAS_FLOAT) || defined(ULBN_CONF_HAS_DOUBLE) || defined(ULBN_CONF_HAS_LONG_DOUBLE)
  #include <float.h> /* FLT_MAX_EXP, FLT_MANT_DIG, DBL_MAX_EXP, DBL_MANT_DIG, LDBL_MAX_EXP, LDBL_MANT_DIG */
  #include <math.h>  /* (HUGE_VALF & floorf), floor, floorl */
#endif

/***********
 * Utility *
 ***********/

#ifndef ulbn_assert
  #define ulbn_assert(expr) assert(expr)
#endif /* ulbn_assert */

#ifndef ulbn_condexpr
  #define ulbn_condexpr(cond, expr) (ulbn_assert(cond), (expr))
#endif /* ulbn_condexpr */

#ifndef ul_assume
  #ifndef UL_PEDANTIC
    #if defined(_MSC_VER)
      #define ul_assume(cond) __assume(cond)
    #endif
    #if !defined(ul_assume) && ul_has_builtin(__builtin_assume)
      #define ul_assume(cond) __builtin_assume(cond)
    #endif
    #if !defined(ul_assume) && defined(__cplusplus) && defined(__has_cpp_attribute)
      #if __has_cpp_attribute(cond)
        #define ul_assume(cond) [[assume(cond)]]
      #endif
    #endif
    #if !defined(ul_assume) && defined(__has_attribute) && !defined(UL_PEDANTIC)
      #if __has_attribute(assume)
        #define ul_assume(cond) __attribute__((assume(cond)))
      #endif
    #endif
    #if !defined(ul_assume) && ul_has_builtin(__builtin_unreachable)
      #if ul_has_builtin(__builtin_expect)
        #define ul_assume(cond) (__builtin_expect(!(cond), 0) ? __builtin_unreachable() : (void)0)
      #else
        #define ul_assume(cond) (!(cond) ? __builtin_unreachable() : (void)0)
      #endif
    #endif
  #endif
  #ifndef ul_assume
    #define ul_assume(cond) ((void)0)
  #endif
#endif /* ul_assume */

#if !defined(UL_ENDIAN_BIG) && !defined(UL_ENDIAN_LITTLE)
  #if defined(BIG_ENDIAN) && defined(LITTLE_ENDIAN)
    #if defined(BYTE_ORDER) && BYTE_ORDER == BIG_ENDIAN
      #define UL_ENDIAN_BIG
    #elif defined(BYTE_ORDER) && BYTE_ORDER == LITTLE_ENDIAN
      #define UL_ENDIAN_LITTLE
    #endif
  #elif defined(BIG_ENDIAN)
    #define UL_ENDIAN_BIG
  #elif defined(LITTLE_ENDIAN)
    #define UL_ENDIAN_LITTLE
  #endif

  #if defined(_BIG_ENDIAN) && defined(_LITTLE_ENDIAN)
    #if defined(_BYTE_ORDER) && _BYTE_ORDER == _BIG_ENDIAN
      #define UL_ENDIAN_BIG
    #elif defined(_BYTE_ORDER) && _BYTE_ORDER == _LITTLE_ENDIAN
      #define UL_ENDIAN_LITTLE
    #endif
  #elif defined(_BIG_ENDIAN)
    #define UL_ENDIAN_BIG
  #elif defined(_LITTLE_ENDIAN)
    #define UL_ENDIAN_LITTLE
  #endif

  #if defined(__BIG_ENDIAN) && defined(__LITTLE_ENDIAN)
    #if defined(__BYTE_ORDER) && __BYTE_ORDER == __BIG_ENDIAN
      #define UL_ENDIAN_BIG
    #elif defined(__BYTE_ORDER) && __BYTE_ORDER == __LITTLE_ENDIAN
      #define UL_ENDIAN_LITTLE
    #endif
  #elif defined(__BIG_ENDIAN)
    #define UL_ENDIAN_BIG
  #elif defined(__LITTLE_ENDIAN)
    #define UL_ENDIAN_LITTLE
  #endif

  #if defined(__BIG_ENDIAN__) && defined(__LITTLE_ENDIAN__)
    #if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __BIG_ENDIAN__
      #define UL_ENDIAN_BIG
    #elif defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __LITTLE_ENDIAN__
      #define UL_ENDIAN_LITTLE
    #endif
  #elif defined(__BIG_ENDIAN__)
    #define UL_ENDIAN_BIG
  #elif defined(__LITTLE_ENDIAN__)
    #define UL_ENDIAN_LITTLE
  #endif

  #if !defined(UL_ENDIAN_BIG) && !defined(UL_ENDIAN_LITTLE)
    #if defined(__alpha__) || defined(__alpha) || defined(i386) || defined(__i386__) || defined(_M_I86) \
      || defined(_M_IX86) || defined(__OS2__) || defined(sun386) || defined(__TURBOC__) || defined(vax) \
      || defined(vms) || defined(VMS) || defined(__VMS) || defined(_M_X64)
      #define UL_ENDIAN_LITTLE
    #elif defined(AMIGA) || defined(applec) || defined(__AS400__) || defined(_CRAY) || defined(__hppa)         \
      || defined(__hp9000) || defined(ibm370) || defined(mc68000) || defined(m68k) || defined(__MRC__)         \
      || defined(__MVS__) || defined(__MWERKS__) || defined(sparc) || defined(__sparc) || defined(SYMANTEC_C)  \
      || defined(__VOS__) || defined(__TIGCC__) || defined(__TANDEM) || defined(THINK_C) || defined(__VMCMS__) \
      || defined(_AIX) || defined(__s390__) || defined(__s390x__) || defined(__zarch__)
      #define UL_ENDIAN_BIG
    #elif defined(__arm__)
      #ifdef __BIG_ENDIAN
        #define UL_ENDIAN_BIG
      #else
        #define UL_ENDIAN_LITTLE
      #endif
    #endif
  #endif
#endif /* !UL_ENDIAN_BIG && !UL_ENDIAN_LITTLE */

/* check if `x` is 64-bit integer */
#if defined(ULONG_MAX) && (ULONG_MAX >> 63) == 1
  #define _ULBN_IS_64BIT(x) ((x) == 0xFFFFFFFFFFFFFFFFul)
#elif defined(ULLONG_MAX) && (ULLONG_MAX >> 63) == 1
  #define _ULBN_IS_64BIT(x) ((x) == 0xFFFFFFFFFFFFFFFFull)
#else
  #define _ULBN_IS_64BIT(x) (0)
#endif /* _ULBN_IS_64BIT */

#ifdef __cplusplus
  #define ulbn_may_static static
#else
  #define ulbn_may_static
#endif

/************************
 * Macros about overlap *
 ************************/

#define ulbn_safe_forward_overlap(d, dn, s, sn) ((d) <= (s) || (d) >= (s) + (sn))
#define ulbn_safe_backward_overlap(d, dn, s, sn) ((d) + (dn) <= (s) || ((d) >= (s) && (d) + (dn) >= (s) + (sn)))
#define ulbn_safe_overlap(d, dn, s, sn) ((d) + (dn) <= (s) || (s) + (sn) <= (d))

#define ulbn_assert_forward_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_forward_overlap(d, dn, s, sn))
#define ulbn_assert_backward_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_backward_overlap(d, dn, s, sn))
#define ulbn_assert_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_overlap(d, dn, s, sn))
#define ulbn_assert_same_or_not_overlap(d, dn, s, sn) \
  ulbn_assert((d) == ul_nullptr || (s) == ul_nullptr || (s) == (d) || ulbn_safe_overlap(d, dn, s, sn))

/***********************************
 * Definations about `ulbn_limb_t` *
 ***********************************/

#if (CHAR_BIT & 1) != 0
ul_static_assert((sizeof(ulbn_limb_t) & 1) == 0, "`CHAR_BIT` or `sizeof(ulbn_limb_t)` should be even");
#endif

#define _ULBN_LIMB_HALF_BITS (ULBN_LIMB_BITS >> 1)
#define ULBN_LIMB_SHL(val, shift) ulbn_cast_limb(ulbn_cast_limb(val) << (shift))
#define _ULBN_LIMB_SIGNBIT (ULBN_LIMB_SHL(1, ULBN_LIMB_BITS - 1))
#define _ULBN_LOWMASK ulbn_cast_limb(ULBN_LIMB_SHL(1, _ULBN_LIMB_HALF_BITS) - 1u)
#define ULBN_LOWPART(x) ulbn_cast_limb((x) & ULBN_LOWMASK)
#define ULBN_HIGHPART(x) ulbn_cast_limb((x) >> ULBN_LIMB_HALF_BITS)

static ul_constexpr const size_t ULBN_LIMB_HALF_BITS = _ULBN_LIMB_HALF_BITS;
static ul_constexpr const ulbn_limb_t ULBN_LIMB_SIGNBIT = _ULBN_LIMB_SIGNBIT;
static ul_constexpr const ulbn_limb_t ULBN_LOWMASK = _ULBN_LOWMASK;

#if ULBN_LIMB_MAX < UCHAR_MAX
  #define _ULBN_LIMB_1X_CHAR
#endif
#if ULBN_LIMB_MAX / UCHAR_MAX / UCHAR_MAX <= 1 || ULBN_LIMB_MAX / UCHAR_MAX <= UCHAR_MAX + 2
  #define _ULBN_LIMB_2X_CHAR
#endif
#define _ULBN_DIV_4LIMB(x) ((x) / UCHAR_MAX / UCHAR_MAX / UCHAR_MAX / UCHAR_MAX)
#if _ULBN_DIV_4LIMB(ULBN_LIMB_MAX) <= 1 \
  || ULBN_LIMB_MAX / UCHAR_MAX <= UCHAR_MAX * UCHAR_MAX * UCHAR_MAX + 4 * UCHAR_MAX * UCHAR_MAX + 6 * UCHAR_MAX + 4
  #define ULBN_LIMB_4X_CHAR
#endif
#define _ULBN_MUL_4LIMB(x) ((x) * UCHAR_MAX * UCHAR_MAX * UCHAR_MAX * UCHAR_MAX)
#if _ULBN_DIV_4LIMB(_ULBN_DIV_4LIMB(ULBN_LIMB_MAX)) <= 1                                                           \
  || ULBN_LIMB_MAX / UCHAR_MAX <= _ULBN_MUL_4LIMB(UCHAR_MAX * UCHAR_MAX * UCHAR_MAX)                               \
                                    + 8 * _ULBN_MUL_4LIMB(UCHAR_MAX * UCHAR_MAX) + 28 * _ULBN_MUL_4LIMB(UCHAR_MAX) \
                                    + 56 * _ULBN_MUL_4LIMB(1) + 70 * UCHAR_MAX * UCHAR_MAX * UCHAR_MAX             \
                                    + 56 * UCHAR_MAX * UCHAR_MAX + 28 * UCHAR_MAX + 8
  #define ULBN_LIMB_8X_CHAR
#endif
#undef _ULBN_DIV_4LIMB
#undef _ULBN_MUL_4LIMB

/******************************************************
 * Definations about `ulbn_usize_t` and `ulbn_bits_t` *
 ******************************************************/

#define _ULBN_SIZET_MAX ul_static_cast(size_t, ~ul_static_cast(size_t, 0))
#define _ULBN_ALLOC_LIMIT ul_static_cast(size_t, _ULBN_SIZET_MAX / sizeof(ulbn_limb_t))
/* The limitation of `ulbn_usize_t`, mainly to avoid overflow caused by the multiplication of `ulbn_usize_t` */
#define _ULBN_USIZE_LIMIT ulbn_cast_usize(_ulbn_min_(_ULBN_SIZET_MAX / ULBN_LIMB_BITS, ULBN_USIZE_MAX))

static ul_constexpr const size_t ULBN_ALLOC_LIMIT = _ULBN_ALLOC_LIMIT;
static ul_constexpr const ulbn_usize_t ULBN_USIZE_LIMIT = _ULBN_USIZE_LIMIT;

/*
#define _ULBN_BITS_LIMIT ulbn_cast_bits(ULBN_LIMB_BITS* ulbn_cast_bits(_ULBN_USIZE_LIMIT))
static ul_constexpr const ulbn_bits_t ULBN_BITS_LIMIT = _ULBN_BITS_LIMIT;
*/


#ifndef ULBN_CHECK_USIZE_OVERFLOW
  /* If `ulbn_usize_t` is able to hold bits of `ulbi_t`, we don't need to check if `ulbn_usize_t` exceeds the limit */
  #if defined(SIZE_MAX)
    #if defined(_ULBN_LIMB_1X_CHAR) && ULBN_USIZE_MAX <= SIZE_MAX / CHAR_BIT
      #define ULBN_CHECK_USIZE_OVERFLOW 0
    #elif defined(_ULBN_LIMB_2X_CHAR) && ULBN_USIZE_MAX <= SIZE_MAX / 2 / CHAR_BIT
      #define ULBN_CHECK_USIZE_OVERFLOW 0
    #elif defined(ULBN_LIMB_4X_CHAR) && ULBN_USIZE_MAX <= SIZE_MAX / 4 / CHAR_BIT
      #define ULBN_CHECK_USIZE_OVERFLOW 0
    #elif defined(ULBN_LIMB_8X_CHAR) && ULBN_USIZE_MAX <= SIZE_MAX / 8 / CHAR_BIT
      #define ULBN_CHECK_USIZE_OVERFLOW 0
    #endif
  #endif

  #ifndef ULBN_CHECK_USIZE_OVERFLOW
    #define ULBN_CHECK_USIZE_OVERFLOW 1
  #endif
#endif /* ULBN_CHECK_USIZE_OVERFLOW */

#if ULBN_CHECK_USIZE_OVERFLOW
  #define ULBN_DO_IF_USIZE_COND(cond, expr) \
    if(ul_unlikely(cond))                   \
    expr((void)0)
  #define ULBN_RETURN_IF_USIZE_COND(cond, ret) \
    if(ul_unlikely(cond))                      \
    return (ret)
#else /* !ULBN_CHECK_USIZE_OVERFLOW */
  #define ULBN_DO_IF_USIZE_COND(cond, expr) ((void)0)
  #define ULBN_RETURN_IF_USIZE_COND(cond, ret) ((void)0)
#endif
#define ULBN_DO_IF_USIZE_OVERFLOW(n, expr) ULBN_DO_IF_USIZE_COND((n) > ULBN_USIZE_LIMIT, expr)
#define ULBN_RETURN_IF_USIZE_OVERFLOW(n, ret) ULBN_RETURN_IF_USIZE_COND((n) > ULBN_USIZE_LIMIT, ret)

#if ULBN_CONF_CHECK_ALLOCATION_FAILURE
  #define ULBN_RETURN_IF_ALLOC_COND(cond, ret) \
    if(ul_unlikely((cond)))                    \
    return (ret)
  #define ULBN_DO_IF_ALLOC_COND(cond, expr) \
    if(ul_unlikely((cond)))                 \
    expr((void)0)
#else /* !ULBN_CONF_CHECK_ALLOCATION_FAILURE */
  #define ULBN_RETURN_IF_ALLOC_COND(cond, ret) ((void)0)
  #define ULBN_DO_IF_ALLOC_COND(cond, expr) ((void)0)
#endif
#define ULBN_RETURN_IF_ALLOC_FAILED(ptr, ret) ULBN_RETURN_IF_ALLOC_COND((ptr) == ul_nullptr, ret)
#define ULBN_DO_IF_ALLOC_FAILED(ptr, expr) ULBN_DO_IF_ALLOC_COND((ptr) == ul_nullptr, expr)


#define ULBN_DO_IF_PUBLIC_COND(cond, expr) \
  if(ul_unlikely(cond))                    \
  expr((void)0)


#ifdef __cplusplus
extern "C" {
#endif

/******************
 * <ulbn> Startup *
 ******************/

ULBN_PRIVATE void _ulbn_startup_fft(void);
ULBN_PRIVATE void _ulbn_startup_setstr(void);
ULBN_PRIVATE void _ulbn_startup_baseconv(void);
ULBN_PRIVATE void _ulbn_startup_shortdiv(void);

static int _ulbn_startup_state = 0;
ULBN_PUBLIC void ulbn_startup(void) {
  if(_ulbn_startup_state != 0)
    return;

  _ulbn_startup_fft();
  _ulbn_startup_setstr();
  _ulbn_startup_baseconv();
  _ulbn_startup_shortdiv();

  _ulbn_startup_state = 1;
}

#if !defined(ulbn_check_startup) && defined(__has_attribute) && !defined(UL_PEDANTIC)
  #if __has_attribute(constructor)
ULBN_PRIVATE __attribute__((constructor)) void ulbn_auto_startup(void) {
  ulbn_startup();
}
    #define ulbn_check_startup() ((void)0)
  #endif
#endif

/*
#if !defined(ulbn_check_startup) && defined(__cplusplus)
ULBN_PRIVATE void _ulbn_auto_startup(void) {
  struct AutoStartup {
    AutoStartup() {
      ulbn_startup();
    }
  };
  static AutoStartup auto_startup;
}
  #define ulbn_check_startup() _ulbn_auto_startup()
#endif
*/

#ifndef ulbn_check_startup
  #define ulbn_check_startup() ulbn_assert(_ulbn_startup_state != 0)
#endif

/*********************
 * <ulbn> Allocation *
 *********************/

#define ulbn_doalloc(alloc, p, on, nn) (alloc)->alloc_func((alloc)->alloc_opaque, (p), (on), (nn))

#define ulbn_doallocT(T, alloc, p, onum, nnum)                                                                         \
  ul_reinterpret_cast(                                                                                                 \
    T*, ulbn_doalloc((alloc), (p), ul_static_cast(size_t, onum) * sizeof(T), ul_static_cast(size_t, nnum) * sizeof(T)) \
  )
#define ulbn_allocT(T, alloc, num) ulbn_doallocT(T, alloc, ul_nullptr, 0, num)
#define ulbn_reallocT(T, alloc, p, onum, nnum) ulbn_doallocT(T, alloc, p, onum, nnum)
#define ulbn_deallocT(T, alloc, p, num) ((void)ulbn_doallocT(T, alloc, p, num, 0))

ULBN_PRIVATE void* _ulbn_default_alloc(void* opaque, void* ptr, size_t on, size_t nn) {
  (void)opaque;
  (void)on;
  if(nn == 0) {
    free(ptr);
    return ul_nullptr;
  }
  return realloc(ptr, nn);
}
ULBN_PUBLIC const ulbn_alloc_t* ulbn_default_alloc(void) {
  static const ulbn_alloc_t alloc = { &_ulbn_default_alloc, ul_nullptr };
  return &alloc;
}

ULBN_PUBLIC void* ulbn_alloc(const ulbn_alloc_t* alloc, size_t sz) {
  ulbn_assert(sz != 0);
  return ulbn_doalloc(alloc, ul_nullptr, 0, sz);
}
ULBN_PUBLIC void* ulbn_realloc(const ulbn_alloc_t* alloc, void* ptr, size_t on, size_t nn) {
  ulbn_assert(ptr == ul_nullptr ? on == 0 : on != 0);
  ulbn_assert(nn != 0);
  return ulbn_doalloc(alloc, ptr, on, nn);
}
ULBN_PUBLIC void ulbn_dealloc(const ulbn_alloc_t* alloc, void* ptr, size_t sz) {
  ulbn_assert(sz != 0);
  ulbn_doalloc(alloc, ptr, sz, 0);
}

ULBN_PUBLIC ulbn_usize_t ulbn_usize_limit(void) {
  return ULBN_USIZE_LIMIT;
}

/*********************************************
 * <ulbn> Operations for short `ulbn_limb_t` *
 *********************************************/

ULBN_PRIVATE int _ulbn_clz_(ulbn_limb_t x) {
#if ul_has_builtin(__builtin_clz) && ULBN_LIMB_MAX <= UINT_MAX
  return ulbn_condexpr(x != 0, __builtin_clz(x) - ulbn_cast_int(sizeof(int) * CHAR_BIT - ULBN_LIMB_BITS));
#elif ul_has_builtin(__builtin_clz) && ULBN_LIMB_MAX == UINT_MAX
  return ulbn_condexpr(x != 0, __builtin_clz(x));
#elif ul_has_builtin(__builtin_clzl) && ULBN_LIMB_MAX == ULONG_MAX
  return ulbn_condexpr(x != 0, __builtin_clzl(x));
#elif ul_has_builtin(__builtin_clzll) && ULBN_LIMB_MAX == ULLONG_MAX
  return ulbn_condexpr(x != 0, __builtin_clzll(x));
#else
  int r = 0;

  #if ULBN_LIMB_MAX > 0xFFu
  static ul_constexpr const ulbn_limb_t MASK8 = ULBN_LIMB_SHL(0xFF, ULBN_LIMB_BITS - 8);
  ulbn_assert(x != 0);
  while(!(x & MASK8)) {
    r += 8;
    x <<= 8;
  }
  #else
  ulbn_assert(x != 0);
  #endif

  while(!(x & ULBN_LIMB_SIGNBIT)) {
    ++r;
    x <<= 1;
  }
  return r;
#endif
}
ULBN_PRIVATE int _ulbn_ctz_(ulbn_limb_t x) {
#if ul_has_builtin(__builtin_ctz) && ULBN_LIMB_MAX <= UINT_MAX
  return ulbn_condexpr(x != 0, __builtin_ctz(x));
#elif ul_has_builtin(__builtin_ctzl) && ULBN_LIMB_MAX <= ULONG_MAX
  return ulbn_condexpr(x != 0, __builtin_ctzl(x));
#elif ul_has_builtin(__builtin_ctzll) && ULBN_LIMB_MAX <= ULLONG_MAX
  return ulbn_condexpr(x != 0, __builtin_ctzll(x));
#else
  int r = 0;
  ulbn_assert(x != 0);
  #if ULBN_LIMB_MAX > 0xFFu
  while(!(x & 0xFF)) {
    r += 8;
    x >>= 8;
  }
  #endif
  while(!(x & 1)) {
    ++r;
    x >>= 1;
  }
  return r;
#endif
}
ULBN_PRIVATE int _ulbn_popcount_(ulbn_limb_t x) {
#if ul_has_builtin(__builtin_popcount) && ULBN_LIMB_MAX <= UINT_MAX
  return __builtin_popcount(x);
#elif ul_has_builtin(__builtin_popcountl) && ULBN_LIMB_MAX <= ULONG_MAX
  return __builtin_popcountl(x);
#elif ul_has_builtin(__builtin_popcountll) && ULBN_LIMB_MAX <= ULLONG_MAX
  return __builtin_popcountll(x);
#else
  int r = 0;
  while(x) {
    r += ulbn_cast_int(x & 1);
    x >>= 1;
  }
  return r;
#endif
}

#if ULBN_ULONG_MAX > ULBN_LIMB_MAX
ULBN_PRIVATE int _ulbn_clz_ulong(ulbn_ulong_t x) {
  #if ul_has_builtin(__builtin_clz) && ULBN_ULONG_MAX <= UINT_MAX
  return ulbn_condexpr(x != 0, __builtin_clz(x) - ulbn_cast_int((sizeof(int) - sizeof(ulbn_ulong_t)) * CHAR_BIT));
  #elif ul_has_builtin(__builtin_clz) && ULBN_ULONG_MAX == UINT_MAX
  return ulbn_condexpr(x != 0, __builtin_clz(x));
  #elif ul_has_builtin(__builtin_clzl) && ULBN_ULONG_MAX == ULONG_MAX
  return ulbn_condexpr(x != 0, __builtin_clzl(x));
  #elif ul_has_builtin(__builtin_clzll) && ULBN_ULONG_MAX == ULLONG_MAX
  return ulbn_condexpr(x != 0, __builtin_clzll(x));
  #else
  static ul_constexpr const ulbn_ulong_t MASK = ulbn_cast_ulong(ulbn_cast_ulong(1) << (ULBN_ULONG_BITS - 1));
  int r = 0;

    #if ULBN_ULONG_MAX > 0xFFu
  static ul_constexpr const ulbn_ulong_t MASK8 = ulbn_cast_ulong(ulbn_cast_ulong(0xFF) << (ULBN_ULONG_BITS - 8));
  ulbn_assert(x != 0);
  while(!(x & MASK8)) {
    r += 8;
    x <<= 8;
  }
    #else
  ulbn_assert(x != 0);
    #endif

  while(!(x & MASK)) {
    ++r;
    x <<= 1;
  }
  return r;
  #endif
}
#endif

#define _ulbn_swap_(T, a, b)  \
  do {                        \
    T const __swap_tmp = (a); \
    (a) = (b);                \
    (b) = __swap_tmp;         \
  } while(0)

#define _ulbn_neg_(v) ulbn_cast_limb(ulbn_cast_limb(0u) - (v))

#ifdef ulbn_dlimb_t
  #define _ulbn_dlimb_(h, l) ulbn_cast_dlimb(ulbn_cast_dlimb((h)) << ULBN_LIMB_BITS | (l))

  #define _ulbn_add_(s1, s0, a1, a0, b1, b0)                                                         \
    do {                                                                                             \
      const ulbn_dlimb_t __s = ulbn_cast_dlimb(_ulbn_dlimb_((a1), (a0)) + _ulbn_dlimb_((b1), (b0))); \
      (s1) = ulbn_cast_limb((__s) >> ULBN_LIMB_BITS);                                                \
      (s0) = ulbn_cast_limb((__s));                                                                  \
    } while(0)
  #define _ulbn_sub_(d1, d0, a1, a0, b1, b0)                                                         \
    do {                                                                                             \
      const ulbn_dlimb_t __d = ulbn_cast_dlimb(_ulbn_dlimb_((a1), (a0)) - _ulbn_dlimb_((b1), (b0))); \
      (d1) = ulbn_cast_limb((__d) >> ULBN_LIMB_BITS);                                                \
      (d0) = ulbn_cast_limb((__d));                                                                  \
    } while(0)
  #define _ulbn_umul_(p1, p0, u, v)                                         \
    do {                                                                    \
      const ulbn_dlimb_t __p = ulbn_cast_dlimb(ulbn_cast_dlimb((u)) * (v)); \
      (p1) = ulbn_cast_limb((__p) >> ULBN_LIMB_BITS);                       \
      (p0) = ulbn_cast_limb((__p));                                         \
    } while(0)
  #define _ulbn_udiv_(q, r, n1, n0, d)                   \
    do {                                                 \
      const ulbn_dlimb_t __n = _ulbn_dlimb_((n1), (n0)); \
      (r) = ulbn_cast_limb(__n % (d));                   \
      (q) = ulbn_cast_limb(__n / (d));                   \
    } while(0)
#endif

#ifndef _ulbn_add_
  #define _ulbn_add_(s1, s0, a1, a0, b1, b0)               \
    do {                                                   \
      const ulbn_limb_t __s = ulbn_cast_limb((a0) + (b0)); \
      (s1) = ulbn_cast_limb((a1) + (b1) + (__s < (a0)));   \
      (s0) = __s;                                          \
    } while(0)
#endif
#ifndef _ulbn_sub_
  #define _ulbn_sub_(d1, d0, a1, a0, b1, b0)               \
    do {                                                   \
      const ulbn_limb_t __d = ulbn_cast_limb((a0) - (b0)); \
      (d1) = ulbn_cast_limb((a1) - (b1) - ((a0) < (b0)));  \
      (d0) = __d;                                          \
    } while(0)
#endif

#if !defined(_ulbn_umul_) && !defined(UL_PEDANTIC) && defined(_MSC_VER) && _ULBN_IS_64BIT(ULBN_LIMB_MAX)
  #include <intrin.h>
  #if defined(__x86_64__) || defined(_M_X64) /* x86_64 */
    #if _MSC_VER >= 1900
      #pragma intrinsic(_mul128)
      #define _ulbn_umul_(p1, p0, u, v) (p0) = _umul128((u), (v), &(p1))
    #endif
  #elif defined(__arm64) || defined(__arm64__) || defined(__aarch64__) || defined(_M_ARM64) /* arm64 */
    #if _MSC_VER >= 1900
      #pragma intrinsic(__umulh)
      #define _ulbn_umul_(p1, p0, u, v) ((void)((p0) = (u) * (v)), (p1) = __umulh((u), (v)))
    #endif
  #endif
#endif

#if !defined(_ulbn_udiv_) && !defined(UL_PEDANTIC) && defined(_MSC_VER) && _ULBN_IS_64BIT(ULBN_LIMB_MAX)
  #include <intrin.h>
  #if _MSC_VER >= 1929 && !defined(__clang__) && (defined(__x86_64__) || defined(_M_X64)) /* x86_64 */
    #pragma intrinsic(_udiv128)
    #define _ulbn_udiv_(q, r, n1, n0, d) ((q) = _udiv128((n1), (n0), (d), &(r)))
  #endif
#endif

#ifndef _ulbn_umul_
  #define _ulbn_umul_(p1, p0, u, v)                                              \
    do {                                                                         \
      const ulbn_limb_t __ul = ULBN_LOWPART(u);                                  \
      const ulbn_limb_t __uh = ULBN_HIGHPART(u);                                 \
      const ulbn_limb_t __vl = ULBN_LOWPART(v);                                  \
      const ulbn_limb_t __vh = ULBN_HIGHPART(v);                                 \
      const ulbn_limb_t __x0 = ulbn_cast_limb(__ul * __vl);                      \
      ulbn_limb_t __x1 = ulbn_cast_limb(__ul * __vh);                            \
      const ulbn_limb_t __x2 = ulbn_cast_limb(__uh * __vl);                      \
      ulbn_limb_t __x3 = ulbn_cast_limb(__uh * __vh);                            \
      __x1 += ULBN_HIGHPART(__x0);                                               \
      __x1 += __x2;                                                              \
      if(__x1 < __x2)                                                            \
        __x3 += ULBN_LIMB_SHL(1, ULBN_LIMB_HALF_BITS);                           \
      (p0) = ulbn_cast_limb((__x1 << ULBN_LIMB_HALF_BITS) | ULBN_LOWPART(__x0)); \
      (p1) = __x3 + ULBN_HIGHPART(__x1);                                         \
    } while(0)
#endif /* _ulbn_umul_ */

#ifndef _ulbn_udiv_norm_
  #ifdef _ulbn_udiv_
    #define _ulbn_udiv_norm_(q, r, n1, n0, d) _ulbn_udiv_((q), (r), (n1), (n0), (d))
  #else
    #define _ulbn_udiv_norm_(q, r, n1, n0, d)                              \
      do {                                                                 \
        const ulbn_limb_t __dh = ULBN_HIGHPART(d);                         \
        const ulbn_limb_t __dl = ULBN_LOWPART(d);                          \
        ulbn_limb_t __qh, __ql, __r, __m;                                  \
        ulbn_assert((n1) < (d));                                           \
        ulbn_assert((d) != 0);                                             \
                                                                           \
        __qh = (n1) / __dh;                                                \
        __r = (n1) - __qh * __dh;                                          \
        __m = __qh * __dl;                                                 \
        __r = ULBN_LIMB_SHL(__r, ULBN_LIMB_HALF_BITS) | ULBN_HIGHPART(n0); \
        if(__r < __m) {                                                    \
          --__qh, __r += (d);                                              \
          if(__r >= (d) && __r < __m)                                      \
            --__qh, __r += (d);                                            \
        }                                                                  \
        __r -= __m;                                                        \
                                                                           \
        __ql = __r / __dh;                                                 \
        __r = __r - __ql * __dh;                                           \
        __m = __ql * __dl;                                                 \
        __r = ULBN_LIMB_SHL(__r, ULBN_LIMB_HALF_BITS) | ULBN_LOWPART(n0);  \
        if(__r < __m) {                                                    \
          --__ql, __r += (d);                                              \
          if(__r >= (d) && __r < __m)                                      \
            --__ql, __r += (d);                                            \
        }                                                                  \
        __r -= __m;                                                        \
                                                                           \
        (r) = __r;                                                         \
        (q) = ULBN_LIMB_SHL(__qh, ULBN_LIMB_HALF_BITS) | __ql;             \
      } while(0)
  #endif
#endif /* _ulbn_udiv_norm_ */

#ifndef _ulbn_udiv_
  #define _ulbn_udiv_(q, r, n1, n0, d)                                                                            \
    do {                                                                                                          \
      if((n1) == 0) {                                                                                             \
        (r) = (ulbn_cast_limb(n0) % (d));                                                                         \
        (q) = (ulbn_cast_limb(n0) / (d));                                                                         \
      } else {                                                                                                    \
        const int _U_shift = _ulbn_clz_(ulbn_cast_limb(d));                                                       \
        const ulbn_limb_t __U_n1 = (ulbn_cast_limb(n1) << _U_shift)                                               \
                                   | (ulbn_cast_limb(n0) >> (ulbn_cast_int(ULBN_LIMB_BITS) - _U_shift - 1) >> 1); \
        const ulbn_limb_t __U_n0 = ulbn_cast_limb(n0) << _U_shift;                                                \
        const ulbn_limb_t __U_d = ulbn_cast_limb(d) << _U_shift;                                                  \
        ulbn_limb_t __U_r;                                                                                        \
        _ulbn_udiv_norm_((q), __U_r, __U_n1, __U_n0, __U_d);                                                      \
        (r) = __U_r >> _U_shift;                                                                                  \
      }                                                                                                           \
    } while(0)
#endif /* _ulbn_udiv_ */

/* Let B to be 2^{ULBN_LIMB_BITS}, di = (B^2-1)//d1 - B */
ULBN_INTERNAL ulbn_limb_t _ulbn_divinv1(ulbn_limb_t d1) {
  /*
   * di = (B^2-1)//d1 - B
   * di = <B-1-d1, B-1>//d1
   */
  ulbn_limb_t n1, n0, di;

  n1 = _ulbn_neg_(d1 + 1u);
  n0 = _ulbn_neg_(1);
  _ulbn_udiv_norm_(di, di, n1, n0, d1);
  return di;
}
#define ulbn_divinv1(d1) ulbn_condexpr(((d1) & ULBN_LIMB_SIGNBIT) != 0 /* B/2 <= d1 < B */, _ulbn_divinv1(d1))
/* Let B to be 2^{ULBN_LIMB_BITS}, di = (B^3-1)//(d1*B+d0) - B */
ULBN_INTERNAL ulbn_limb_t _ulbn_divinv2(ulbn_limb_t d1, ulbn_limb_t d0) {
  /*
   * di = (B^3-1 - <d1,d0,0>)//<d1, d0>
   * di = <B-1-d1, B-1-d0, B-1>//<d1, d0>
   */
  ulbn_limb_t n1, n0, di;
  ulbn_limb_t p, t1, t0;

  /*
   * di = (B^2-1)//d1 - B
   * di = <B-1-d1, B-1>//d1
   */
  n1 = _ulbn_neg_(d1 + 1u);
  n0 = _ulbn_neg_(1);
  _ulbn_udiv_norm_(di, di, n1, n0, d1);

  /**
   * calc <B-1-d1, B-1-d0>//d1
   *
   * As 0 < -d0/d1 <= 2 - 2/B,
   * -2 <= <B-1-d1, B-1-d0>//d1 - <B-1-d1, B-1>//d1 <= 0
   */
  p = ulbn_cast_limb(ulbn_cast_limb(d1 * di) + d0);
  if(p < d0) {
    --di;
    if(p >= d1) {
      --di;
      p -= d1;
    }
    p -= d1;
  }

  _ulbn_umul_(t1, t0, d0, di); /* <t1, t0> = <0, d0> * <0, di> */
  p += t1;
  if(p < t1) {
    --di;
    if(p >= d1)
      if(p > d1 || t0 >= d0)
        --di;
  }

  return di;
}
#define ulbn_divinv2(d1, d0) ulbn_condexpr(((d1) & ULBN_LIMB_SIGNBIT) != 0 /* B/2 <= d1 < B */, _ulbn_divinv2(d1, d0))

#define _ulbn_udiv_2by1_(q, r, a1, a0, d, di)                \
  do {                                                       \
    ulbn_limb_t __q1, __q0, __r;                             \
    _ulbn_umul_(__q1, __q0, (a1), (di));                     \
    _ulbn_add_(__q1, __q0, __q1, __q0, (a1) + 1, (a0));      \
    __r = ulbn_cast_limb((a0) - ulbn_cast_limb(__q1 * (d))); \
    if(__r > __q0) {                                         \
      --__q1;                                                \
      __r += (d);                                            \
    }                                                        \
    if(ul_unlikely(__r >= (d))) {                            \
      ++__q1;                                                \
      __r -= (d);                                            \
    }                                                        \
    (r) = __r;                                               \
    (q) = __q1;                                              \
  } while(0)

#if 0
  /* it seems that `ulbn_dlimb_t` cannot accelerate this */
  #define _ulbn_udiv_3by2_(q, r1, r0, a2, a1, a0, d1, d0, di)                                       \
    do {                                                                                            \
      ulbn_dlimb_t __q = ulbn_cast_dlimb(ulbn_cast_dlimb((a2)) * (di));                             \
      ulbn_dlimb_t __r;                                                                             \
      ulbn_dlimb_t __t;                                                                             \
      const ulbn_dlimb_t __d = _ulbn_dlimb_((d1), (d0));                                            \
      __q += _ulbn_dlimb_((a2), (a1));                                                              \
      __t = ulbn_cast_dlimb(ulbn_cast_dlimb((d0)) * (__q >> ULBN_LIMB_BITS));                       \
      __r = _ulbn_dlimb_((a1) - ulbn_cast_limb(__q >> ULBN_LIMB_BITS) * (d1), ulbn_cast_limb(__r)); \
      __r -= __t + __d;                                                                             \
      if(__r >= (ulbn_cast_dlimb(ulbn_cast_limb(__q)) << ULBN_LIMB_BITS)) {                         \
        __q -= ulbn_cast_dlimb(ulbn_cast_dlimb(1) << ULBN_LIMB_BITS);                               \
        __r += __d;                                                                                 \
      }                                                                                             \
      if(ul_unlikely(__r >= __d)) {                                                                 \
        __q += ulbn_cast_dlimb(ulbn_cast_dlimb(1) << ULBN_LIMB_BITS);                               \
        __r -= __d;                                                                                 \
      }                                                                                             \
      (r1) = ulbn_cast_limb(__r);                                                                   \
      (r0) = ulbn_cast_limb(__r >> ULBN_LIMB_BITS);                                                 \
      (q) = ulbn_cast_limb(__q >> ULBN_LIMB_BITS);                                                  \
    } while(0)
#else
  #define _ulbn_udiv_3by2_(q, r1, r0, a2, a1, a0, d1, d0, di) \
    do {                                                      \
      ulbn_limb_t __q1, __q0;                                 \
      ulbn_limb_t __r1, __r0;                                 \
      ulbn_limb_t __t1, __t0;                                 \
      _ulbn_umul_(__q1, __q0, (a2), (di));                    \
      _ulbn_add_(__q1, __q0, __q1, __q0, (a2), (a1));         \
      __r1 = ulbn_cast_limb((a1) - __q1 * (d1));              \
      _ulbn_umul_(__t1, __t0, (d0), __q1);                    \
      _ulbn_sub_(__r1, __r0, __r1, (a0), __t1, __t0);         \
      _ulbn_sub_(__r1, __r0, __r1, __r0, (d1), (d0));         \
      ++__q1;                                                 \
      if(__r1 >= __q0) {                                      \
        --__q1;                                               \
        _ulbn_add_(__r1, __r0, __r1, __r0, (d1), (d0));       \
      }                                                       \
      if(ul_unlikely(__r1 >= (d1)))                           \
        if(ul_unlikely(__r1 > (d1) || __r0 >= (d0))) {        \
          ++__q1;                                             \
          _ulbn_sub_(__r1, __r0, __r1, __r0, (d1), (d0));     \
        }                                                     \
      (r1) = __r1;                                            \
      (r0) = __r0;                                            \
      (q) = __q1;                                             \
    } while(0)
#endif

/*********************************
 * <ulbn> Copy, Check, Normalize *
 *********************************/

/* Normalize p[0:n] from high to low, return the length */
ULBN_INTERNAL ulbn_usize_t ulbn_rnorm(const ulbn_limb_t* p, ulbn_usize_t n) {
  while(n > 0 && p[n - 1] == 0)
    --n;
  return n;
}
/* Normalize p[0:n] from low to high, return the index of the first non-zero element */
ULBN_INTERNAL ulbn_usize_t ulbn_fnorm(const ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_usize_t i = 0;
  while(i < n && p[i] == 0)
    ++i;
  return i;
}

/* Fill p[0:n] with 0 */
ULBN_INTERNAL void ulbn_fill0(ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_assert(ul_static_cast(size_t, n) < _ULBN_SIZET_MAX / sizeof(ulbn_limb_t));
  memset(p, 0, ul_static_cast(size_t, n) * sizeof(ulbn_limb_t));
}
/* Fill p[0:n] with ~0 */
ULBN_INTERNAL void ulbn_fill1(ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_assert(ul_static_cast(size_t, n) < _ULBN_SIZET_MAX / sizeof(ulbn_limb_t));
  memset(p, 0xFF, ul_static_cast(size_t, n) * sizeof(ulbn_limb_t));
}

/* Check if p[0:n] is 0 */
ULBN_INTERNAL int ulbn_is0(const ulbn_limb_t* p, ulbn_usize_t n) {
  return ulbn_fnorm(p, n) >= n;
}

/* Copy src[0:n] to dst[0:n], ensuring src[] and dest[] do not overlap */
ULBN_INTERNAL void ulbn_copy(ulbn_limb_t* ul_restrict dst, const ulbn_limb_t* ul_restrict src, ulbn_usize_t n) {
  ulbn_assert_overlap(dst, n, src, n);
  ulbn_assert(ul_static_cast(size_t, n) < _ULBN_SIZET_MAX / sizeof(ulbn_limb_t));
  memcpy(dst, src, ul_static_cast(size_t, n) * sizeof(*dst));
}
/* Copy src[0:n] to dst[0:n], ensuring dest is after src */
ULBN_INTERNAL void ulbn_fcopy(ulbn_limb_t* dst, const ulbn_limb_t* src, ulbn_usize_t n) {
  ulbn_assert_forward_overlap(dst, n, src, n);
  ulbn_assert(ul_static_cast(size_t, n) < _ULBN_SIZET_MAX / sizeof(ulbn_limb_t));
  memcpy(dst, src, ul_static_cast(size_t, n) * sizeof(*dst));
}
/* Copy src[0:n] to dst[0:n], ensuring dest is before src */
ULBN_INTERNAL void ulbn_rcopy(ulbn_limb_t* dst, const ulbn_limb_t* src, ulbn_usize_t n) {
  ulbn_assert_backward_overlap(dst, n, src, n);
  ulbn_assert(ul_static_cast(size_t, n) < _ULBN_SIZET_MAX / sizeof(ulbn_limb_t));
  memmove(dst, src, ul_static_cast(size_t, n) * sizeof(*dst));
}
#if 0
/* Copy src[0:n] to dst[0:n], not ensuring anything */
ULBN_INTERNAL void ulbn_mcopy(ulbn_limb_t* dst, const ulbn_limb_t* src, ulbn_usize_t n) {
  ulbn_assert(ul_static_cast(size_t, n) < _ULBN_SIZET_MAX / sizeof(ulbn_limb_t));
  memmove(dst, src, ul_static_cast(size_t, n) * sizeof(*dst));
}
#endif
#define ulbn_maycopy(dst, src, n) ((dst) != (src) ? ulbn_copy((dst), (src), (n)) : (void)0)

/*************************
 * <ulbn> Bit operations *
 *************************/

/* rp[0:n] = ap[0:n] << b, return overflow part (do not write to rp[n]), ensure 0 < b < {ULBN_LIMB_BITS} */
ULBN_INTERNAL ulbn_limb_t ulbn_shl(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t n, int b) {
  ulbn_usize_t i;
  ulbn_limb_t rh, rl, ret;
  const int br = ulbn_cast_int(ULBN_LIMB_BITS) - b;

  ulbn_assert(n > 0);
  ulbn_assert(0 < b && ulbn_cast_uint(b) < ULBN_LIMB_BITS);
  ulbn_assert_backward_overlap(rp, n, ap, n);

  rl = ap[n - 1];
  ret = ulbn_cast_limb(rl >> br);
  rh = ulbn_cast_limb(rl << b);
  for(i = n - 1; i > 0; --i) {
    rl = ap[i - 1];
    rp[i] = ulbn_cast_limb(rh | (rl >> br));
    rh = ulbn_cast_limb(rl << b);
  }
  rp[0] = rh;
  return ret;
}
/* rp[0:n] = ap[0:n] >> b, return overflow part (do not write to rp[-1]), ensure 0 < b < {ULBN_LIMB_BITS} */
ULBN_INTERNAL ulbn_limb_t ulbn_shr(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t n, int b) {
  ulbn_usize_t i;
  ulbn_limb_t rh, rl, ret;
  const int br = ulbn_cast_int(ULBN_LIMB_BITS) - b;

  ulbn_assert(n > 0);
  ulbn_assert(0 < b && ulbn_cast_uint(b) < ULBN_LIMB_BITS);
  ulbn_assert_forward_overlap(rp, n, ap, n);

  rh = ap[0];
  ret = ulbn_cast_limb(rh << br);
  rl = ulbn_cast_limb(rh >> b);
  for(i = 1; i < n; ++i) {
    rh = ap[i];
    rp[i - 1] = ulbn_cast_limb(rl | (rh << br));
    rl = ulbn_cast_limb(rh >> b);
  }
  rp[n - 1] = rl;
  return ret;
}

ul_static_assert(ULBN_LIMB_BITS <= ULBN_BITS_MAX, "ulbn_usize_t must be able to hold at least ULBN_LIMB_BITS");
ULBN_INTERNAL ulbn_bits_t ulbn_ctz(const ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_bits_t r = 0;
  ulbn_usize_t i;

  ulbn_assert(ulbn_cast_bits(n) <= ULBN_BITS_MAX / CHAR_BIT);
  ulbn_assert(n == 0 || p[n - 1] != 0);
  if(ul_unlikely(n == 0))
    return 0;
  for(i = 0; p[i] == 0; ++i)
    r += ULBN_LIMB_BITS;
  return ulbn_cast_bits(r + ulbn_cast_uint(_ulbn_ctz_(p[i])));
}
ULBN_INTERNAL ulbn_bits_t ulbn_cto(const ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_bits_t r = 0;
  ulbn_usize_t i;

  ulbn_assert(ulbn_cast_bits(n) <= ULBN_BITS_MAX / CHAR_BIT);
  ulbn_assert(n == 0 || p[n - 1] != 0);
  if(ul_unlikely(n == 0))
    return 0;
  for(i = 0; p[i] == ULBN_LIMB_MAX; ++i)
    r += ULBN_LIMB_BITS;
  return ulbn_cast_bits(r + ulbn_cast_uint(_ulbn_ctz_(ulbn_cast_limb(~p[i]))));
}
ULBN_INTERNAL ulbn_bits_t ulbn_popcount(const ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_bits_t r = 0;
  ulbn_usize_t i;

  ulbn_assert(ulbn_cast_bits(n) <= ULBN_BITS_MAX / CHAR_BIT);
  ulbn_assert(n == 0 || p[n - 1] != 0);
  for(i = 0; i < n; ++i)
    r += ulbn_cast_bits(ulbn_cast_uint(_ulbn_popcount_(p[i])));
  return r;
}
ULBN_INTERNAL ulbn_bits_t ulbn_bit_width(const ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_assert(n > 0 && ulbn_cast_bits(n) <= ULBN_BITS_MAX / CHAR_BIT);
  return ulbn_cast_bits(ulbn_cast_bits(n) * ULBN_LIMB_BITS - ulbn_cast_uint(_ulbn_clz_(p[n - 1])));
}

ULBN_INTERNAL ulbn_usize_t ulbn_set_ulong(ulbn_limb_t* p, ulbn_ulong_t v) {
  ulbn_usize_t n = 0;

  if(v == 0)
    return 0;
#if ULBN_ULONG_MAX <= ULBN_LIMB_MAX
  p[n++] = ulbn_cast_limb(v);
#else
  do {
    p[n++] = ulbn_cast_limb(v);
    v >>= ULBN_LIMB_BITS;
  } while(v);
#endif
  return n;
}


/*********************
 * <ulbn> Comparison *
 *********************/

/* Compare ap[0:n] and bp[0:n], return direction (<0 means less than, =0 means equal, >0 means greater) */
ULBN_INTERNAL int ulbn_cmpn(const ulbn_limb_t* ap, const ulbn_limb_t* bp, ulbn_usize_t n) {
  ulbn_usize_t i = n;
  while(i-- > 0)
    if(ap[i] != bp[i])
      return ap[i] < bp[i] ? -1 : 1;
  return 0;
}
/* Compare ap[0:an] and bp[0:bn], return direction (<0 means less than, =0 means equal, >0 means greater) */
ULBN_INTERNAL int ulbn_cmp(const ulbn_limb_t* ap, ulbn_usize_t an, const ulbn_limb_t* bp, ulbn_usize_t bn) {
  ulbn_assert(an == 0 || ap[an - 1] != 0);
  ulbn_assert(bn == 0 || bp[bn - 1] != 0);
  if(an != bn)
    return an < bn ? -1 : 1;
  else
    return ulbn_cmpn(ap, bp, an);
}
/* Compare ap[0:n] and (bp[0:bn] << b), return direction (<0 means less than, =0 means equal, >0 means greater) */
ULBN_INTERNAL int ulbn_cmpshl(const ulbn_limb_t* ap, ulbn_usize_t an, const ulbn_limb_t* bp, ulbn_usize_t bn, int b) {
  const int br = ulbn_cast_int(ULBN_LIMB_BITS) - b;
  ulbn_limb_t bh, bl;
  ulbn_limb_t a0;
  ulbn_usize_t i;

  ulbn_assert(0 < b && ul_static_cast(size_t, b) < ULBN_LIMB_BITS);

  if(an < bn)
    return -1;
  if(an - bn > 1)
    return 1;

  a0 = ulbn_cast_limb(an == bn ? 0 : ap[bn]);
  bl = bp[bn - 1];
  bh = ulbn_cast_limb(bl >> br);
  if(bh != a0)
    return a0 < bh ? -1 : 1;
  bh = ulbn_cast_limb(bl << b);
  for(i = bn - 1; i > 0; --i) {
    bl = bp[i - 1];
    bh |= bl >> br;
    if(bh != ap[i])
      return ap[i] < bh ? -1 : 1;
    bh = ulbn_cast_limb(bl << b);
  }
  if(bh == ap[0])
    return 0;
  return ap[0] < bh ? -1 : 1;
}

/*********************************
 * <ulbn> Addition, Substraction *
 *********************************/

/* rp[0:an] = ap[0:an] + b, return carry (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_add1(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t b) {
  ulbn_usize_t i;

  ulbn_assert_forward_overlap(rp, an, ap, an);

  for(i = 0; i < an; ++i)
    b = ((rp[i] = ulbn_cast_limb(ap[i] + b)) < b);
  return b;
}
/* rp[0:an] = ap[0:n] + bp[0:n], return carry (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_addn(ulbn_limb_t* rp, const ulbn_limb_t* ap, const ulbn_limb_t* bp, ulbn_usize_t n) {
  ulbn_usize_t i;
  ulbn_limb_t a, b, r;
  ulbn_limb_t cy = 0;

  ulbn_assert_forward_overlap(rp, n, ap, n);
  ulbn_assert_forward_overlap(rp, n, bp, n);

  for(i = 0; i < n; ++i) {
    a = ap[i];
    b = bp[i];
    cy = ((r = ulbn_cast_limb(a + cy)) < cy);
    cy = ulbn_cast_limb(cy + ((r += b) < b));
    rp[i] = r;
  }
  return cy;
}
/* rp[0:an] = ap[0:an] + bp[0:bn], return carray (do not write to rp[an]), ensuring an>=bn */
ULBN_INTERNAL ulbn_limb_t ulbn_add(
  ulbn_limb_t* rp,                        /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn  /* */
) {
  ulbn_limb_t cy;

  ulbn_assert(an >= bn);
  ulbn_assert_forward_overlap(rp, _ulbn_max_(an, bn), ap, an);
  ulbn_assert_forward_overlap(rp, _ulbn_max_(an, bn), bp, bn);

  cy = ulbn_addn(rp, ap, bp, bn);
  return ulbn_add1(rp + bn, ap + bn, an - bn, cy);
}

/* rp[0:an] = ap[0:an] - b, return borrow (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_sub1(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t b) {
  ulbn_usize_t i;
  ulbn_limb_t a;

  ulbn_assert_forward_overlap(rp, an, ap, an);

  for(i = 0; i < an; ++i) {
    a = ap[i];
    rp[i] = ulbn_cast_limb(a - b);
    b = (a < b);
    ulbn_assert(b <= 1);
  }
  return b;
}
/* rp[0:an] = ap[0:n] - bp[0:n], return borrow (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_subn(ulbn_limb_t* rp, const ulbn_limb_t* ap, const ulbn_limb_t* bp, ulbn_usize_t n) {
  ulbn_usize_t i;
  ulbn_limb_t a, b;
  ulbn_limb_t cy = 0;

  ulbn_assert_forward_overlap(rp, n, ap, n);
  ulbn_assert_forward_overlap(rp, n, bp, n);

  for(i = 0; i < n; ++i) {
    a = ap[i];
    cy = ((b = ulbn_cast_limb(bp[i] + cy)) < cy);
    rp[i] = ulbn_cast_limb(a - b);
    cy = ulbn_cast_limb(cy + (a < b));
    ulbn_assert(cy <= 1);
  }
  return cy;
}
/* rp[0:an] = ap[0:an] - bp[0:bn], return borrow (do not write to rp[an]),
 * ensuring an>=bn */
ULBN_INTERNAL ulbn_limb_t ulbn_sub(
  ulbn_limb_t* rp,                        /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn  /* */
) {
  ulbn_limb_t cy;

  /* ulbn_assert(ulbn_cmp(ap, ulbn_rnorm(ap, an), bp, ulbn_rnorm(bp, bn)) >= 0); */
  ulbn_assert_forward_overlap(rp, an, ap, an);
  ulbn_assert_forward_overlap(rp, an, bp, bn);

  cy = ulbn_subn(rp, ap, bp, bn);
  return ulbn_sub1(rp + bn, ap + bn, an - bn, cy);
}

/*********************************************
 * <ulbn> Shift addition, Shift substraction *
 *********************************************/

#define _ULBN_TOOM_1_THRESHOLD 48
#define _ULBN_TOOM_2_THRESHOLD 128
#define _ULBN_TOOM_3_THRESHOLD 1024

#if _ULBN_TOOM_1_THRESHOLD < 2
  #error "ulbn: toom-2 and toom-1.5 thresholds must be at least 2"
#endif
#if _ULBN_TOOM_2_THRESHOLD < 4
  #error "ulbn: toom-3 and toom-2.5 thresholds must be at least 4"
#endif
#if _ULBN_TOOM_3_THRESHOLD < 9
  #error "ulbn: toom-4 and toom-3.5 thresholds must be at least 9"
#endif

#if !(_ULBN_TOOM_1_THRESHOLD <= _ULBN_TOOM_2_THRESHOLD && _ULBN_TOOM_2_THRESHOLD <= _ULBN_TOOM_3_THRESHOLD)
  #error "ulbn: toom thresholds must be in increasing order"
#endif

#if _ULBN_TOOM_2_THRESHOLD < ULBN_USIZE_MAX
  #define _ULBN_USE_TOOM_3 1
#endif
#if _ULBN_TOOM_3_THRESHOLD < ULBN_USIZE_MAX
  #define _ULBN_USE_TOOM_4 1
#else
  #define _ULBN_USE_TOOM_4 0
#endif

#if _ULBN_USE_TOOM_4
/* rp[0:n] = ap[0:n] + (bp[0:n] << b), return overflow part (do not write to rp[n]), ensure 0 < b < {ULBN_LIMB_BITS} */
ULBN_INTERNAL ulbn_limb_t ulbn_addshln(
  ulbn_limb_t* rp, const ulbn_limb_t* ap,      /* */
  const ulbn_limb_t* bp, ulbn_usize_t n, int b /* */
) {
  ulbn_usize_t i;
  ulbn_limb_t bl, r, limb = 0, cy = 0;
  const int br = ulbn_cast_int(ULBN_LIMB_BITS) - b;

  ulbn_assert(n > 0);
  ulbn_assert(0 < b && ulbn_cast_uint(b) < ULBN_LIMB_BITS);
  ulbn_assert_forward_overlap(rp, n, bp, n);

  for(i = 0; i < n; ++i) {
    bl = bp[i];
    limb |= bl << b;
    cy = ((r = ulbn_cast_limb(ap[i] + cy)) < cy);
    cy = ulbn_cast_limb(cy + ((r += limb) < limb));
    ulbn_assert(cy <= 1u);
    rp[i] = r;
    limb = ulbn_cast_limb(bl >> br);
  }
  return ulbn_cast_limb(limb + cy);
}
/* rp[0:an] = ap[0:an] + (bp[0:bn] << b), return overflow part (do not write to rp[n]),
  ensure 0 < b < {ULBN_LIMB_BITS} */
ULBN_INTERNAL ulbn_limb_t ulbn_addshl(
  ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn, int b            /* */
) {
  ulbn_limb_t cy;

  ulbn_assert(an >= bn);
  ulbn_assert_forward_overlap(rp, an, ap, an);
  ulbn_assert_forward_overlap(rp, an, bp, bn);

  cy = ulbn_addshln(rp, ap, bp, bn, b);
  return ulbn_add1(rp + bn, ap + bn, an - bn, cy);
}
/* rp[0:n] = ap[0:n] - (bp[0:n] << b), return overflow part (do not write to rp[n]), ensure 0 < b < {ULBN_LIMB_BITS} */
ULBN_INTERNAL ulbn_limb_t ulbn_subshln(
  ulbn_limb_t* rp, const ulbn_limb_t* ap,      /* */
  const ulbn_limb_t* bp, ulbn_usize_t n, int b /* */
) {
  ulbn_usize_t i;
  ulbn_limb_t bl, limb = 0, cy = 0;
  const int br = ulbn_cast_int(ULBN_LIMB_BITS) - b;

  ulbn_assert(n > 0);
  ulbn_assert(0 < b && ulbn_cast_uint(b) < ULBN_LIMB_BITS);
  ulbn_assert_forward_overlap(rp, n, bp, n);

  for(i = 0; i < n; ++i) {
    bl = bp[i];
    limb |= bl << b;
    cy = ((limb += cy) < cy);
    cy = ulbn_cast_limb(cy + (ap[i] < limb));
    ulbn_assert(cy <= 1u);
    rp[i] = ulbn_cast_limb(ap[i] - limb);
    limb = ulbn_cast_limb(bl >> br);
  }
  return ulbn_cast_limb(limb + cy);
}
/* rp[0:an] = ap[0:an] - (bp[0:bn] << b), return overflow part (do not write to rp[n]),
  ensure 0 < b < {ULBN_LIMB_BITS} */
ULBN_INTERNAL ulbn_limb_t ulbn_subshl(
  ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn, int b            /* */
) {
  ulbn_limb_t cy;

  ulbn_assert(an >= bn);
  ulbn_assert_forward_overlap(rp, an, ap, an);
  ulbn_assert_forward_overlap(rp, an, bp, bn);

  cy = ulbn_subshln(rp, ap, bp, bn, b);
  return ulbn_sub1(rp + bn, ap + bn, an - bn, cy);
}
#endif /* _ULBN_USE_TOOM_4 */

/*************************
 * <ulbn> Multiplication *
 *************************/

/* rp[0:an] = ap[0:an] * b, return carry (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_mul1(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t b) {
  ulbn_usize_t i;
  ulbn_limb_t ph, pl;
  ulbn_limb_t cy = 0;

  ulbn_assert_forward_overlap(rp, an, ap, an);

  for(i = 0; i < an; ++i) {
    _ulbn_umul_(ph, pl, ap[i], b);
    cy = ulbn_cast_limb(ph + ((pl += cy) < cy));
    rp[i] = pl;
  }
  return cy;
}
/* rp[0:an] += ap[0:an] * b, return carry (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_addmul1(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t b) {
  ulbn_usize_t i;
  ulbn_limb_t ph, pl;
  ulbn_limb_t r, cy = 0;

  ulbn_assert_forward_overlap(rp, an, ap, an);

  for(i = 0; i < an; ++i) {
    _ulbn_umul_(ph, pl, ap[i], b);
    cy = ulbn_cast_limb(ph + ((pl += cy) < cy));
    r = rp[i];
    cy = ulbn_cast_limb(cy + ((pl += r) < r));
    rp[i] = pl;
  }
  return cy;
}
/* rp[0:an] -= ap[0:an] * b, return borrow (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_submul1(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t b) {
  ulbn_usize_t i;
  ulbn_limb_t ph, pl;
  ulbn_limb_t r, cy = 0;

  ulbn_assert_forward_overlap(rp, an, ap, an);

  for(i = 0; i < an; ++i) {
    _ulbn_umul_(ph, pl, ap[i], b);
    cy = ulbn_cast_limb(ph + ((pl += cy) < cy));
    r = rp[i];
    rp[i] = ulbn_cast_limb(r - pl);
    cy = ulbn_cast_limb(cy + (r < pl));
  }
  return cy;
}

/* rp[0:an+bn] = ap[0:an] * bp[0:bn].
  This version is for short `an` and `bn`, with time complexity O(an*bn). */
ULBN_INTERNAL void ulbn_mul_school(
  ulbn_limb_t* ul_restrict rp,            /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn  /* */
) {
  ulbn_usize_t i;

  ulbn_assert(an >= bn);
  ulbn_assert(an > 0 && bn > 0);
  ulbn_assert_overlap(rp, an + bn, ap, an);
  ulbn_assert_overlap(rp, an + bn, bp, bn);

  rp[an] = ulbn_mul1(rp, ap, an, bp[0]);
  for(i = 1; i < bn; ++i) {
    ++rp;
    rp[an] = ulbn_addmul1(rp, ap, an, bp[i]);
  }
}

ULBN_INTERNAL void ulbn_divmod_inv1(
  ulbn_limb_t* qp, ulbn_limb_t* rp,        /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,  /* */
  ulbn_limb_t d, ulbn_limb_t di, int shift /* */
);
ULBN_INTERNAL void ulbn_mul(
  const ulbn_alloc_t* alloc, ulbn_limb_t* ul_restrict rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,                 /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn                  /* */
);
ULBN_INTERNAL void ulbn_shortdiv(ulbn_limb_t* qp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t d);

ULBN_PRIVATE int _ulbn_mul_toom_21(
  const ulbn_alloc_t* alloc,                         /* */
  ulbn_limb_t* ul_restrict rp, const ulbn_usize_t m, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,            /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn             /* */
) {
  /**
   * Toom-1.5
   * Note: This function is designed to handle cases where `ap` is extremely large but `bp` is not small enough.
   * It will split `ap` in half and expect to trigger a more efficient algorithm.
   *
   * a = a1 * x + a0
   * b = b0
   *
   * z0 = a0 * b0
   * z1 = a1 * b0
   *
   * r = z1 * x + z0
   */
  ulbn_limb_t* ul_restrict zp;

  ulbn_assert(an > 0 && bn > 0);
  ulbn_assert(an >= bn);
  ulbn_assert(an >= m && an - m <= m);
  ulbn_assert(bn <= m);
  ulbn_assert(an + bn >= an);

  ulbn_mul(alloc, rp, ap, m, bp, bn);
  zp = ulbn_allocT(ulbn_limb_t, alloc, an - m + bn);
  ULBN_RETURN_IF_ALLOC_FAILED(zp, ULBN_ERR_NOMEM);
  ulbn_mul(alloc, zp, ap + m, an - m, bp, bn);
  ulbn_add(rp + m, zp, an - m + bn, rp + m, bn);
  ulbn_deallocT(ulbn_limb_t, alloc, zp, an - m + bn);
  return 0;
}
ULBN_PRIVATE int _ulbn_mul_toom_22(
  const ulbn_alloc_t* alloc,                         /* */
  ulbn_limb_t* ul_restrict rp, const ulbn_usize_t m, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,            /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn             /* */
) {
  /**
   * Toom-2 (also called Karatsuba algorithm):
   *
   * a = a1 * x + a0
   * b = b1 * x + b0
   *
   * z0 = a0 * b0
   * z1 = (a0 + a1) * (b0 + b1)
   * z2 = a1 * b1
   *
   * r = z2 * x^2 + (z1 - z2 - z0) * x + z0
   */
  ulbn_limb_t *ul_restrict zp, *ul_restrict p1, *ul_restrict p2;
  ulbn_usize_t nz, n1, n2;
  int err = ULBN_ERR_NOMEM;

  ulbn_assert(an > 0 && bn > 0);
  ulbn_assert(an >= bn);
  ulbn_assert(an >= m && an - m <= m);
  ulbn_assert(bn > m);
  ulbn_assert(an + bn >= an);

  /* z0 = a0 * b0, store it in rp[0:2*m] */
  ulbn_mul(alloc, rp, ap, m, bp, m);
  /* z2 = a1 * b1, store it in rp[2m:an+bn] */
  ulbn_mul(alloc, rp + (m << 1), ap + m, an - m, bp + m, bn - m);

  p1 = ulbn_allocT(ulbn_limb_t, alloc, m + 1);
  ULBN_DO_IF_ALLOC_FAILED(p1, goto cleanup_p1;);
  p2 = ulbn_allocT(ulbn_limb_t, alloc, m + 1);
  ULBN_DO_IF_ALLOC_FAILED(p2, goto cleanup_p2;);
  /* store (a0 + a1) in `p1` */
  p1[m] = ulbn_add(p1, ap, m, ap + m, an - m);
  n1 = m + (p1[m] != 0);
  /* store (b0 + b1) in `p2` */
  p2[m] = ulbn_add(p2, bp, m, bp + m, bn - m);
  n2 = m + (p2[m] != 0);

  zp = ulbn_allocT(ulbn_limb_t, alloc, n1 + n2);
  ULBN_DO_IF_ALLOC_FAILED(zp, goto cleanup_zp;);
  /* z1 = (a0 + a1) * (b0 + b1), store it in `zp[0:n1+n2]` */
  ulbn_mul(alloc, zp, p1, n1, p2, n2);
  nz = n1 + n2 - (zp[n1 + n2 - 1] == 0);
  /* `zp[0:nz]` -= z0 */
  ulbn_sub(zp, zp, nz, rp, ulbn_cast_usize((m << 1) - (rp[(m << 1) - 1] == 0)));
  /* `zp[0:nz]` -= z2 */
  ulbn_sub(zp, zp, nz, rp + (m << 1), ulbn_cast_usize(an + bn - (rp[an + bn - 1] == 0) - (m << 1)));
  nz = ulbn_rnorm(zp, nz);
  /* now `zp[0:nz]` is z1 */

  /* `rp[m:]` += z1 */
  ulbn_add(rp + m, rp + m, an + bn - m, zp, nz);
  err = 0;

  ulbn_deallocT(ulbn_limb_t, alloc, zp, n1 + n2);
cleanup_zp:
  ulbn_deallocT(ulbn_limb_t, alloc, p2, m + 1);
cleanup_p2:
  ulbn_deallocT(ulbn_limb_t, alloc, p1, m + 1);
cleanup_p1:
  return err;
}

#if _ULBN_USE_TOOM_3
ULBN_PRIVATE int _ulbn_mul_toom_32(
  const ulbn_alloc_t* alloc,                         /* */
  ulbn_limb_t* ul_restrict rp, const ulbn_usize_t m, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,            /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn             /* */
) {
  /*
    Toom-2.5

    v(  0) = (   0   0   0   1)
    v(  1) = (   1   1   1   1)
    v( -1) = (  -1   1  -1   1)
    v(inf) = (   1   0   0   0)
  */

  /*************
   * splitting *
   *************/

  const ulbn_usize_t m2 = ulbn_cast_usize(m << 1), am = an - m2, bm = bn - m, abm = am + bm;
  const ulbn_limb_t *const a0 = ap, *const a1 = ap + m, *const a2 = ap + m2;
  const ulbn_limb_t *const b0 = bp, *const b1 = bp + m;
  ulbn_limb_t* const rinf = rp + m2 + m;

  ulbn_limb_t *ul_restrict v1, *ul_restrict vm1;
  ulbn_limb_t* ul_restrict t1;

  ulbn_usize_t n1, n2, nt;
  int vm1_sign;
  int err = ULBN_ERR_NOMEM;

  ulbn_assert(an >= bn);
  ulbn_assert(an >= 3 && an <= 3 * m && an >= 3 * m - 2);
  ulbn_assert(bn > m && bn <= m * 2);
  ulbn_assert(an + bn >= an);

  v1 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(v1, goto cleanup_v1;);
  vm1 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(vm1, goto cleanup_vm1;);
  t1 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(t1, goto cleanup_t1;);

  /*******************************************
   * evaluation and pointwise multiplication *
   *******************************************/

  /* t1 = a0 + a2 */
  t1[m] = ulbn_add(t1, a0, m, a2, am);
  /* rp = t1 + a1 = a0 + a1 + a2 */
  rp[m] = ulbn_cast_limb(t1[m] + ulbn_add(rp, t1, m, a1, m));
  /* vm1 = b0 + b1 */
  vm1[m] = ulbn_add(vm1, b0, m, b1, bm);
  /* v1 = rp * vm1 = (a0 + a1 + a2) * (b0 + b1) */
  ulbn_mul(alloc, v1, rp, m + 1, vm1, m + 1);

  /* t1 = t1 - a1 = a0 - a1 + a2 */
  n1 = ulbn_rnorm(t1, m + 1);
  nt = ulbn_rnorm(a1, m);
  if(ulbn_cmp(t1, n1, a1, nt) >= 0) {
    ulbn_sub(t1, t1, n1, a1, nt);
    n1 = ulbn_rnorm(t1, n1);
    vm1_sign = 0;
  } else {
    ulbn_sub(t1, a1, nt, t1, n1);
    n1 = ulbn_rnorm(t1, nt);
    vm1_sign = 1;
  }

  /* rp = b0 - b1 */
  n2 = ulbn_rnorm(b0, m);
  nt = ulbn_rnorm(b1, bm);
  if(ulbn_cmp(b0, n2, b1, nt) >= 0) {
    ulbn_sub(rp, b0, n2, b1, nt);
    n2 = ulbn_rnorm(rp, n2);
  } else {
    ulbn_sub(rp, b1, nt, b0, n2);
    n2 = ulbn_rnorm(rp, nt);
    vm1_sign ^= 1;
  }

  /* vm1 = t1 * rp = (a0 - a1 + a2) * (b0 - b1) */
  if(n1 && n2) {
    ulbn_mul(alloc, vm1, t1, n1, rp, n2);
    ulbn_fill0(vm1 + n1 + n2, (m2 + 2) - (n1 + n2));
  } else
    ulbn_fill0(vm1, m2 + 2);

  ulbn_mul(alloc, rp, a0, m, b0, m);
  ulbn_mul(alloc, rinf, a2, am, b1, bm);

    /*****************
     * interpolation *
     *****************/

  #if 0
  ulbn_dprint(stdout, "v0 = ", rp, m2);
  ulbn_dprint(stdout, "v1 = ", v1, m2 + 1);
  printf("vm1 = %c", vm1_sign ? '-' : '+');
  ulbn_dprint(stdout, ul_nullptr, vm1, m2 + 1);
  ulbn_dprint(stdout, "vinf = ", rinf, abm);
  #endif

  /* t1 = v1 + vm1 = (0, 2, 0, 2) */
  /* v1 = v1 - vm1 = (2, 0, 2, 0) */
  if(vm1_sign == 0) {
    ulbn_add(t1, v1, m2 + 1, vm1, m2 + 1);
    ulbn_sub(v1, v1, m2 + 1, vm1, m2 + 1);
  } else {
    ulbn_sub(t1, v1, m2 + 1, vm1, m2 + 1);
    ulbn_add(v1, v1, m2 + 1, vm1, m2 + 1);
  }

  /* t1 = t1 / 2 = (0, 1, 0, 1) */
  /* t1 = t1 - v0 = (0, 1, 0, 0) */
  ulbn_shr(t1, t1, m2 + 1, 1);
  ulbn_sub(t1, t1, m2 + 1, rp, m2);

  /* v1 = v1 / 2 = (1, 0, 1, 0) */
  /* v1 = v1 - vinf = (0, 0, 1, 0) */
  ulbn_shr(v1, v1, m2 + 1, 1);
  ulbn_sub(v1, v1, m2 + 1, rinf, abm);

    /*****************
     * recomposition *
     *****************/

  #if 0
  ulbn_dprint(stdout, "v0 = ", rp, m2);
  ulbn_dprint(stdout, "v1 = ", v1, m2 + 1);
  ulbn_dprint(stdout, "t1 = ", vm1, m2 + 1);
  ulbn_dprint(stdout, "vinf = ", rinf, abm);
  #endif

  ulbn_copy(rp + m2, t1, m);
  ulbn_assert(ulbn_rnorm(t1, m2 + 1) <= m + abm);
  ulbn_add(rinf, rinf, abm, t1 + m, _ulbn_min_(m + 1, abm));
  ulbn_add(rp + m, rp + m, abm + m2, v1, m2 + 1);
  err = 0;

  ulbn_deallocT(ulbn_limb_t, alloc, t1, m2 + 2);
cleanup_t1:
  ulbn_deallocT(ulbn_limb_t, alloc, vm1, m2 + 2);
cleanup_vm1:
  ulbn_deallocT(ulbn_limb_t, alloc, v1, m2 + 2);
cleanup_v1:
  return err;
}
ULBN_PRIVATE int _ulbn_mul_toom_33(
  const ulbn_alloc_t* alloc,                         /* */
  ulbn_limb_t* ul_restrict rp, const ulbn_usize_t m, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,            /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn             /* */
) {
  /*
    Toom-3

    v(  0) = (  0   0   0   0   1)
    v(  1) = (  1   1   1   1   1)
    v( -1) = (  1  -1   1  -1   1)
    v(  2) = ( 16   8   4   2   1)
    v(inf) = (  1   0   0   0   0)
  */

  /*************
   * splitting *
   *************/

  const ulbn_usize_t m2 = ulbn_cast_usize(m << 1), am = an - m2, bm = bn - m2, abm = am + bm;
  const ulbn_limb_t *const a0 = ap, *const a1 = ap + m, *const a2 = ap + m2;
  const ulbn_limb_t *const b0 = bp, *const b1 = bp + m, *const b2 = bp + m2;
  ulbn_limb_t* const rinf = rp + m2 + m2;

  ulbn_limb_t *ul_restrict v1, *ul_restrict vm1, *ul_restrict v2;
  ulbn_limb_t *ul_restrict t1, *ul_restrict t2;

  ulbn_usize_t n1, n2, nt;
  int vm1_sign;
  int err = ULBN_ERR_NOMEM;

  ulbn_assert(an >= bn);
  ulbn_assert(an >= 3 && an <= 3 * m && an >= 3 * m - 2);
  ulbn_assert(bn > m * 2);
  ulbn_assert(an + bn >= an);

  ulbn_mul(alloc, rp, a0, m, b0, m);
  ulbn_mul(alloc, rinf, a2, am, b2, bm);

  v1 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(v1, goto cleanup_v1;);
  vm1 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(vm1, goto cleanup_vm1;);
  v2 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(v2, goto cleanup_v2;);
  t1 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(t1, goto cleanup_t1;);
  t2 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 1);
  ULBN_DO_IF_ALLOC_FAILED(t2, goto cleanup_t2;);

  /*******************************************
   * evaluation and pointwise multiplication *
   *******************************************/

  /* t1 = a1 + a2 */
  t1[m] = ulbn_add(t1, a1, m, a2, am);
  /* vm1 = t1 + a0 = a0 + a1 + a2 */
  vm1[m] = ulbn_cast_limb(t1[m] + ulbn_add(vm1, t1, m, a0, m));
  /* t2 = b1 + b2 */
  t2[m] = ulbn_add(t2, b1, m, b2, bm);
  /* v2 = t2 + b0 = b0 + b1 + b2 */
  v2[m] = ulbn_cast_limb(t2[m] + ulbn_add(v2, t2, m, b0, m));
  /* v1 = vm1 * v2 = (a0 + a1 + a2) * (b0 + b1 + b2) */
  ulbn_mul(alloc, v1, vm1, m + 1, v2, m + 1);

  /* t1 = t1 + a2 = a1 + 2*a2 */
  t1[m] += ulbn_add(t1, t1, m, a2, am);
  /* t1 = t1 << 1 = 2*a1 + 4*a2 */
  t1[m] = ulbn_cast_limb((t1[m] << 1) | ulbn_shl(t1, t1, m, 1));
  /* t1 = t1 + a0 = a0 + 2*a1 + 4*a2 */
  t1[m] += ulbn_add(t1, t1, m, a0, m);
  /* t2 = t2 + b2 = b1 + 2*b2 */
  t2[m] += ulbn_add(t2, t2, m, b2, bm);
  /* t2 = t2 << 1 = 2*b1 + 4*b2 */
  t2[m] = ulbn_cast_limb((t2[m] << 1) | ulbn_shl(t2, t2, m, 1));
  /* t2 = t2 + b0 = b0 + 2*b1 + 4*b2 */
  t2[m] += ulbn_add(t2, t2, m, b0, m);
  /* v2 = t1 * t2 = (a0 + 2*a1 + 4*a2) * (b0 + 2*b1 + 4*b2) */
  ulbn_mul(alloc, v2, t1, m + 1, t2, m + 1);

  /* t1 = a0 + a2 */
  t1[m] = ulbn_add(t1, a0, m, a2, am);
  /* t1 = t1 - a1 = (a0 - a1 + a2) */
  n1 = ulbn_rnorm(t1, m + 1);
  nt = ulbn_rnorm(a1, m);
  if(ulbn_cmp(t1, n1, a1, nt) >= 0) {
    ulbn_sub(t1, t1, n1, a1, nt);
    n1 = ulbn_rnorm(t1, n1);
    vm1_sign = 0;
  } else {
    ulbn_sub(t1, a1, nt, t1, n1);
    n1 = ulbn_rnorm(t1, nt);
    vm1_sign = 1;
  }

  /* t2 = b0 + b2 */
  t2[m] = ulbn_add(t2, b0, m, b2, bm);
  /* t2 = t2 - b1 = (b0 - b1 + b2) */
  n2 = ulbn_rnorm(t2, m + 1);
  nt = ulbn_rnorm(b1, m);
  if(ulbn_cmp(t2, n2, b1, nt) >= 0) {
    ulbn_sub(t2, t2, n2, b1, nt);
    n2 = ulbn_rnorm(t2, n2);
  } else {
    ulbn_sub(t2, b1, nt, t2, n2);
    n2 = ulbn_rnorm(t2, nt);
    vm1_sign ^= 1;
  }

  /* vm1 = t1 * t2 = (a0 - a1 + a2) * (b0 - b1 + b2) */
  if(n1 && n2) {
    ulbn_mul(alloc, vm1, t1, n1, t2, n2);
    ulbn_fill0(vm1 + n1 + n2, (m2 + 2) - (n1 + n2));
  } else
    ulbn_fill0(vm1, m2 + 2);

    /*****************
     * interpolation *
     *****************/

  #if 0
  ulbn_dprint(stdout, "v0 = ", rp, m2);
  ulbn_dprint(stdout, "v1 = ", v1, m2 + 1);
  printf("vm1 = %c", vm1_sign ? '-' : '+');
  ulbn_dprint(stdout, ul_nullptr, vm1, m2 + 1);
  ulbn_dprint(stdout, "v2 = ", v2, m2 + 1);
  ulbn_dprint(stdout, "vinf = ", rinf, abm);
  #endif

  /* v2 = v2 - vm1 = (15, 9, 3, 3, 0) */
  /* vm1 = v1 - vm1 = (0, 2, 0, 2, 0) */
  if(vm1_sign == 0) {
    ulbn_sub(v2, v2, m2 + 1, vm1, m2 + 1);
    ulbn_sub(vm1, v1, m2 + 1, vm1, m2 + 1);
  } else {
    ulbn_add(v2, v2, m2 + 1, vm1, m2 + 1);
    ulbn_add(vm1, v1, m2 + 1, vm1, m2 + 1);
  }
  /* v2 = v2 / 3 = (5, 3, 1, 1, 0) */
  ulbn_shortdiv(v2, v2, m2 + 1, 3);
  /* vm1 = vm1 / 2 = (0, 1, 0, 1, 0) */
  ulbn_shr(vm1, vm1, m2 + 1, 1);

  /* v1 = v1 - v0 = (1, 1, 1, 1, 0) */
  /* t1 = v1 - vm1 = (1, 0, 1, 0, 0) */
  /* t1 = t1 - vinf = (0, 0, 1, 0, 0) */
  ulbn_sub(v1, v1, m2 + 1, rp, m2);
  ulbn_sub(t1, v1, m2 + 1, vm1, m2 + 1);
  ulbn_sub(t1, t1, m2 + 1, rinf, abm);

  /* v1 = v2 - v1 = (4, 2, 0, 0, 0) */
  /* v1 = v1 / 2 = (2, 1, 0, 0, 0) */
  ulbn_sub(v1, v2, m2 + 1, v1, m2 + 1);
  ulbn_shr(v1, v1, m2 + 1, 1);

  /* t2 = vinf * 2 = (2, 0, 0, 0, 0) */
  /* v1 = v1 - t2 = (0, 1, 0, 0, 0) */
  /* vm1 = vm1 - v1 = (0, 0, 0, 1, 0) */
  t2[abm] = ulbn_add(t2, rinf, abm, rinf, abm);
  ulbn_sub(v1, v1, m2 + 1, t2, abm + 1);
  ulbn_sub(vm1, vm1, m2 + 1, v1, m2 + 1);

    /*****************
     * recomposition *
     *****************/

  #if 0
  ulbn_dprint(stdout, "v0 = ", rp, m2);
  ulbn_dprint(stdout, "vm1 = ", vm1, m2 + 1);
  ulbn_dprint(stdout, "t1 = ", t1, m2 + 1);
  ulbn_dprint(stdout, "v1 = ", v1, m2 + 1);
  ulbn_dprint(stdout, "vinf = ", rinf, abm);
  #endif

  ulbn_copy(rp + m2, t1, m2);
  ulbn_add1(rinf, rinf, abm, t1[m2]);
  ulbn_add(rp + m, rp + m, an + bn - m, vm1, m2 + 1);
  ulbn_add(rinf - m, rinf - m, abm + m, v1, _ulbn_min_(m2 + 1, abm + m));
  err = 0;

  ulbn_deallocT(ulbn_limb_t, alloc, t2, m2 + 1);
cleanup_t2:
  ulbn_deallocT(ulbn_limb_t, alloc, t1, m2 + 2);
cleanup_t1:
  ulbn_deallocT(ulbn_limb_t, alloc, v2, m2 + 2);
cleanup_v2:
  ulbn_deallocT(ulbn_limb_t, alloc, vm1, m2 + 2);
cleanup_vm1:
  ulbn_deallocT(ulbn_limb_t, alloc, v1, m2 + 2);
cleanup_v1:
  return err;
}
#endif /* _ULBN_USE_TOOM_3 */

#if _ULBN_USE_TOOM_4
ULBN_INTERNAL ulbn_limb_t ulbn_neg(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t cy);
ULBN_PRIVATE int _ulbn_mul_toom_43(
  const ulbn_alloc_t* alloc,                         /* */
  ulbn_limb_t* ul_restrict rp, const ulbn_usize_t m, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,            /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn             /* */
) {
  /*
    Toom-3.5
                                         |     a(x)      |   |    b(x)   |
    v(  0) = (  0   0   0   0   0   1)   (  0   0   0   1) * (  0   0   1)
    v(  1) = (  1   1   1   1   1   1)   (  1   1   1   1) * (  1   1   1)
    v( -1) = ( -1   1  -1   1  -1   1)   ( -1   1  -1   1) * (  1  -1   1)
    v(  2) = ( 32  16   8   4   2   1)   (  8   4   2   1) * (  4   2   1)
    v( -2) = (-32  16  -8   4  -2   1)   ( -8   4  -2   1) * (  4  -2   1)
    v(inf) = (  1   0   0   0   0   0)   (  1   0   0   0) * (  1   0   0)

    32 * C(5,0) + 16 * C(5,1) + 8 * C(5,2) + 4 * C(5,3) + 2 * C(5,4) + 1 * C(5,5) = 243 < 2**8
    64 * C(5,0) + 0 * C(5,1) + 16 * C(5,2) + 0 * C(5,3) + 4 * C(5,4) + 0 * C(5,5) = 244 < 2**8
    0 * C(5,0) + 32 * C(5,1) + 0 * C(5,2) + 8 * C(5,3) + 0 * C(5,4) + 2 * C(5,5) = 242 < 2**8
  */

  /*************
   * splitting *
   *************/

  const ulbn_usize_t m2 = m << 1, m3 = m2 + m, am = an - m3, bm = bn - m2, abm = am + bm;
  const ulbn_limb_t *const a0 = ap, *const a1 = ap + m, *const a2 = ap + m2, *const a3 = ap + m3;
  const ulbn_limb_t *const b0 = bp, *const b1 = bp + m, *const b2 = bp + m2;
  ulbn_limb_t *const rinf = rp + m3 + m2, *const v1 = rp + m2;

  ulbn_limb_t *ul_restrict vm1, *ul_restrict v2, *ul_restrict vm2;
  ulbn_limb_t *ul_restrict t1, *ul_restrict t2, *ul_restrict t3;

  ulbn_usize_t n1, n2, nt;
  int vm1_sign, vm2_sign;
  int err = ULBN_ERR_NOMEM;

  ulbn_assert(an >= bn);
  ulbn_assert(an >= 4 && an <= 4 * m && an >= 4 * m - 3);
  ulbn_assert(bn > m * 2);
  ulbn_assert(an + bn >= an);
  ulbn_assert(m > 0);

  /*******************************************
   * evaluation and pointwise multiplication *
   *******************************************/

  vm1 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(vm1, goto cleanup_vm1;);
  v2 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(v2, goto cleanup_v2;);
  vm2 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(vm2, goto cleanup_vm2;);
  t1 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(t1, goto cleanup_t1;);
  t2 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(t2, goto cleanup_t2;);
  t3 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(t3, goto cleanup_t3;);

  /* t1 = a0 + a2 */
  t1[m] = ulbn_add(t1, a0, m, a2, m);
  /* t2 = a1 + a3 */
  t2[m] = ulbn_add(t2, a1, m, a3, am);
  /* t3 = b0 + b2 */
  t3[m] = ulbn_add(t3, b0, m, b2, bm);

  /* vm1 = t1 + t2 = a0 + a1 + a2 + a3 */
  vm1[m] = ulbn_cast_limb(t1[m] + t2[m] + ulbn_add(vm1, t1, m, t2, m));
  /* vm2 = t3 + b1 = b0 + b1 + b2 */
  vm2[m] = ulbn_cast_limb(t3[m] + ulbn_add(vm2, t3, m, b1, m));
  /* v1 = vm1 * vm2 = (a0 + a1 + a2 + a3) * (b0 + b1 + b2) */
  ulbn_mul(alloc, v1, vm1, m + 1, vm2, m + 1);

  /* t1 = t1 - t2 = a0 - a1 + a2 - a3 */
  n1 = ulbn_rnorm(t1, m + 1);
  nt = ulbn_rnorm(t2, m + 1);
  if(ulbn_cmp(t1, n1, t2, nt) >= 0) {
    ulbn_sub(t1, t1, n1, t2, nt);
    n1 = ulbn_rnorm(t1, n1);
    vm1_sign = 0;
  } else {
    ulbn_sub(t1, t2, nt, t1, n1);
    n1 = ulbn_rnorm(t1, nt);
    vm1_sign = 1;
  }

  /* t3 = t3 - b1 = b0 - b1 + b2 */
  n2 = ulbn_rnorm(t3, m + 1);
  nt = ulbn_rnorm(b1, m);
  if(ulbn_cmp(t3, n2, b1, nt) >= 0) {
    ulbn_sub(t3, t3, n2, b1, nt);
    n2 = ulbn_rnorm(t3, n2);
  } else {
    ulbn_sub(t3, b1, nt, t3, n2);
    n2 = ulbn_rnorm(t3, nt);
    vm1_sign ^= 1;
  }

  /* vm1 = t1 * t3 = (a0 - a1 + a2 - a3) * (b0 - b1 + b2) */
  if(n1 && n2) {
    ulbn_mul(alloc, vm1, t1, n1, t3, n2);
    ulbn_fill0(vm1 + n1 + n2, (m2 + 2) - (n1 + n2));
  } else
    ulbn_fill0(vm1, m2 + 2);

  /* t1 = a0 + (a2 << 2) = a0 + 4*a2 */
  t1[m] = ulbn_addshl(t1, a0, m, a2, m, 2);
  /* t2 = a1 << 1 = 2*a1 */
  t2[m] = ulbn_shl(t2, a1, m, 1);
  /* t2 = t2 + (a3 << 3) = 2*a1 + 8*a3 */
  t2[m] += ulbn_addshl(t2, t2, m, a3, am, 3);
  /* t3 = b0 + (b2 << 2) = b0 + 4*b2 */
  t3[m] = ulbn_addshl(t3, b0, m, b2, bm, 2);
  /* t3 = t3 + (b1 << 1) = b0 + 2*b1 + 4*b2 */
  t3[m] += ulbn_addshl(t3, t3, m, b1, m, 1);

  /* vm2 = t1 + t2 = a0 + 2*a1 + 4*a2 + 8*a3 */
  vm2[m] = ulbn_cast_limb(t1[m] + t2[m] + ulbn_add(vm2, t1, m, t2, m));
  /* v2 = vm2 * t3 = (a0 + 2*a1 + 4*a2 + 8*a3) * (b0 + 2*b1 + 4*b2) */
  ulbn_mul(alloc, v2, vm2, m + 1, t3, m + 1);

  /* t1 = t1 - t2 = a0 - 2*a1 + 4*a2 - 8*a3 */
  n1 = ulbn_rnorm(t1, m + 1);
  nt = ulbn_rnorm(t2, m + 1);
  if(ulbn_cmp(t1, n1, t2, nt) >= 0) {
    ulbn_sub(t1, t1, n1, t2, nt);
    n1 = ulbn_rnorm(t1, n1);
    vm2_sign = 0;
  } else {
    ulbn_sub(t1, t2, nt, t1, n1);
    n1 = ulbn_rnorm(t1, nt);
    vm2_sign = 1;
  }
  /* t2 = b1 << 2 = 4*b1 */
  t2[m] = ulbn_shl(t2, b1, m, 2);
  /* t3 = t3 - t2 = b0 - 2*b1 + 4*b2 */
  n2 = ulbn_rnorm(t3, m + 1);
  nt = ulbn_rnorm(t2, m + 1);
  if(ulbn_cmp(t3, n2, t2, nt) >= 0) {
    ulbn_sub(t3, t3, n2, t2, nt);
    n2 = ulbn_rnorm(t3, n2);
  } else {
    ulbn_sub(t3, t2, nt, t3, n2);
    n2 = ulbn_rnorm(t3, nt);
    vm2_sign ^= 1;
  }

  /* vm2 = t1 * t3 = (a0 - 2*a1 + 4*a2 - 8*a3) * (b0 - 2*b1 + 4*b2) */
  if(n1 && n2) {
    ulbn_mul(alloc, vm2, t1, n1, t3, n2);
    ulbn_fill0(vm2 + n1 + n2, (m2 + 2) - (n1 + n2));
  } else
    ulbn_fill0(vm2, m2 + 2);

  /* v0 = a0 * b0 */
  ulbn_mul(alloc, rp, a0, m, b0, m);
  /* vinf = a4 * b3 */
  ulbn_mul(alloc, rinf, a3, am, b2, bm);

    /*****************
     * interpolation *
     *****************/

  #if 0
  ulbn_dprint(stdout, "v0 = ", rp, m2);
  ulbn_dprint(stdout, "v1 = ", v1, m2 + 1);
  printf("vm1 = %c", vm1_sign ? '-' : '+');
  ulbn_dprint(stdout, ul_nullptr, vm1, m2 + 1);
  ulbn_dprint(stdout, "v2 = ", v2, m2 + 1);
  printf("vm2 = %c", vm2_sign ? '-' : '+');
  ulbn_dprint(stdout, ul_nullptr, vm2, m2 + 1);
  ulbn_dprint(stdout, "vinf = ", rinf, abm);
  #endif

  /* t1 = v1 - vm1 = (2, 0, 2, 0, 2, 0) */
  /* v1 = v1 + vm1 = (0, 2, 0, 2, 0, 2) */
  if(!vm1_sign) {
    ulbn_sub(t1, v1, m2 + 1, vm1, m2 + 1);
    ulbn_add(v1, v1, m2 + 1, vm1, m2 + 1);
  } else {
    ulbn_add(t1, v1, m2 + 1, vm1, m2 + 1);
    ulbn_sub(v1, v1, m2 + 1, vm1, m2 + 1);
  }
  /* t2 = v2 - vm2 = (64, 0, 16, 0, 4, 0) */
  /* v2 = v2 + vm2 = (0, 32, 0, 8, 0, 2) */
  if(!vm2_sign) {
    ulbn_sub(t2, v2, m2 + 1, vm2, m2 + 1);
    ulbn_add(v2, v2, m2 + 1, vm2, m2 + 1);
  } else {
    ulbn_add(t2, v2, m2 + 1, vm2, m2 + 1);
    ulbn_sub(v2, v2, m2 + 1, vm2, m2 + 1);
  }

  /* v2 = v2 - v1 = (0, 30, 0, 6, 0, 0) */
  ulbn_sub(v2, v2, m2 + 1, v1, m2 + 1);
  /* v2 = v2 / 6 = (0, 5, 0, 1, 0, 0) */
  ulbn_shortdiv(v2, v2, m2 + 1, 6);
  /* v1 = v1 / 2 = (0, 1, 0, 1, 0, 1) */
  ulbn_shr(v1, v1, m2 + 1, 1);
  /* v1 = v1 - v0 = (0, 1, 0, 1, 0, 0) */
  ulbn_sub(v1, v1, m2 + 1, rp, m2);
  /* v2 = v2 - v1 = (0, 4, 0, 0, 0, 0) */
  ulbn_sub(v2, v2, m2 + 1, v1, m2 + 1);
  /* v2 = v2 / 4 = (0, 1, 0, 0, 0, 0) */
  ulbn_shr(v2, v2, m2 + 1, 2);
  /* v1 = v1 - v2 = (0, 0, 0, 1, 0, 0) */
  ulbn_sub(v1, v1, m2 + 1, v2, m2 + 1);

  /* t1 = t1 / 2 = (1, 0, 1, 0, 1, 0) */
  ulbn_shr(t1, t1, m2 + 1, 1);
  /* t1 = t1 - vinf = (0, 0, 1, 0, 1, 0) */
  ulbn_sub(t1, t1, m2 + 1, rinf, abm);
  /* t2 = t2 - (vinf << 6) = (0, 0, 16, 0, 4, 0) */
  ulbn_subshl(t2, t2, m2 + 1, rinf, abm, 6);
  /* t2 = t2 / 4 = (0, 0, 4, 0, 1, 0) */
  ulbn_shr(t2, t2, m2 + 1, 2);
  /* t2 = t2 - t1 = (0, 0, 3, 0, 0, 0) */
  ulbn_sub(t2, t2, m2 + 1, t1, m2 + 1);
  /* t2 = t2 / 3 = (0, 0, 1, 0, 0, 0) */
  ulbn_shortdiv(t2, t2, m2 + 1, 3);
  /* t1 = t1 - t2 = (0, 0, 0, 0, 1, 0) */
  ulbn_sub(t1, t1, m2 + 1, t2, m2 + 1);

    /*****************
     * recomposition *
     *****************/

  #if 0
  ulbn_dprint(stdout, "v0 = ", rp, m2);
  ulbn_dprint(stdout, "t1 = ", t1, m2 + 1);
  ulbn_dprint(stdout, "v1 = ", v1, m2 + 1);
  ulbn_dprint(stdout, "t2 = ", t2, m2 + 1);
  ulbn_dprint(stdout, "v2 = ", v2, m2 + 1);
  ulbn_dprint(stdout, "vinf = ", rinf, abm);
  #endif

  ulbn_fill0(rinf - m + 1, m - 1);
  ulbn_add(rp + m, rp + m, an + bn - m, t1, m2 + 1);
  ulbn_add(rp + m3, rp + m3, an + bn - m3, t2, m2 + 1);
  ulbn_add(rinf - m, rinf - m, abm + m, v2, _ulbn_min_(m2 + 1, abm + m));
  err = 0;

  ulbn_deallocT(ulbn_limb_t, alloc, t3, m2 + 2);
cleanup_t3:
  ulbn_deallocT(ulbn_limb_t, alloc, t2, m2 + 2);
cleanup_t2:
  ulbn_deallocT(ulbn_limb_t, alloc, t1, m2 + 2);
cleanup_t1:
  ulbn_deallocT(ulbn_limb_t, alloc, vm2, m2 + 2);
cleanup_vm2:
  ulbn_deallocT(ulbn_limb_t, alloc, v2, m2 + 2);
cleanup_v2:
  ulbn_deallocT(ulbn_limb_t, alloc, vm1, m2 + 2);
cleanup_vm1:
  return err;
}
ULBN_PRIVATE int _ulbn_mul_toom_44(
  const ulbn_alloc_t* alloc,                         /* */
  ulbn_limb_t* ul_restrict rp, const ulbn_usize_t m, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,            /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn             /* */
) {
    /*
      Toom-4

                                                    |     a(x)      |   |     b(x)      |
      v(  0) = (  0   0   0   0   0   0   1)        (  0   0   0   1) * (  0   0   0   1)   ranging [0, 1)
      v(  1) = (  1   1   1   1   1   1   1)        (  1   1   1   1) * (  1   1   1   1)   ranging [0, 64)
      v( -1) = (  1  -1   1  -1   1  -1   1)        ( -1   1  -1   1) * ( -1   1  -1   1)   ranging (-32, 32)
      v(  2) = ( 64  32  16   8   4   2   1)        (  8   4   2   1) * (  8   4   2   1)   ranging [0, 729)
      v( -2) = ( 64 -32  16  -8   4  -2   1)        ( -8   4  -2   1) * ( -8   4  -2   1)   ranging (-364, 365)
      v(1/2) = (  1   2   4   8  16  32  64) / 64   (  1   2   4   8) * (  1   2   4   8)   ranging [0, 729)
      v(inf) = (  1   0   0   0   0   0   0)        (  1   0   0   0) * (  1   0   0   0)   ranging [0, 1)
    */

    /*************
     * splitting *
     *************/

  #if ULBN_LIMB_MAX < 1458
    #define _ULBN_FLEN 2
  #else
    #define _ULBN_FLEN 1
  #endif
  const ulbn_usize_t m2 = m << 1, m3 = m2 + m, m4 = m2 + m2, am = an - m3, bm = bn - m3, abm = am + bm;
  const ulbn_limb_t *const a0 = ap, *const a1 = ap + m, *const a2 = ap + m2, *const a3 = ap + m3;
  const ulbn_limb_t *const b0 = bp, *const b1 = bp + m, *const b2 = bp + m2, *const b3 = bp + m3;
  ulbn_limb_t *const rinf = rp + m3 + m3, *const v1 = rp + m2;

  ulbn_limb_t *ul_restrict v2, *ul_restrict vm1, *ul_restrict vm2, *ul_restrict vh;
  ulbn_limb_t *ul_restrict t1, *ul_restrict t2, *ul_restrict t3, *ul_restrict t4;

  ulbn_usize_t n1, n2, nt;
  unsigned vm1_sign, vm2_sign;
  int err = ULBN_ERR_NOMEM;

  ulbn_assert(an >= bn);
  ulbn_assert(an >= 4 && an <= 4 * m && an >= 4 * m - 3);
  ulbn_assert(bn > m * 3);
  ulbn_assert(an + bn >= an);
  ulbn_assert(m > 1);

  /*******************************************
   * evaluation and pointwise multiplication *
   *******************************************/

  v2 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(v2, goto cleanup_v2;);
  vm1 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(vm1, goto cleanup_vm1;);
  vm2 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(vm2, goto cleanup_vm2;);
  vh = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(vh, goto cleanup_vh;);
  t1 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(t1, goto cleanup_t1;);
  t2 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(t2, goto cleanup_t2;);
  t3 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(t3, goto cleanup_t3;);
  t4 = ulbn_allocT(ulbn_limb_t, alloc, m2 + 2);
  ULBN_DO_IF_ALLOC_FAILED(t4, goto cleanup_t4;);

  /* t1 = a0 + a2 */
  t1[m] = ulbn_add(t1, a0, m, a2, m);
  /* t2 = a1 + a3 */
  t2[m] = ulbn_add(t2, a1, m, a3, am);
  /* t3 = b0 + b2 */
  t3[m] = ulbn_add(t3, b0, m, b2, m);
  /* t4 = b1 + b3 */
  t4[m] = ulbn_add(t4, b1, m, b3, bm);

  /* vm1 = t1 + t2 = a0 + a1 + a2 + a3 */
  ulbn_add(vm1, t1, m + 1, t2, m + 1);
  /* vm2 = t3 + t4 = b0 + b1 + b2 + b3 */
  ulbn_add(vm2, t3, m + 1, t4, m + 1);
  /* v1 = vm1 * vm2 = (a0 + a1 + a2 + a3) * (b0 + b1 + b2 + b3) */
  ulbn_mul(alloc, v1, vm1, m + 1, vm2, m + 1);

  /* t1 = a0 - a1 + a2 - a3 */
  n1 = ulbn_rnorm(t1, m + 1);
  nt = ulbn_rnorm(t2, m + 1);
  if(ulbn_cmp(t1, n1, t2, nt) >= 0) {
    ulbn_sub(t1, t1, n1, t2, nt);
    n1 = ulbn_rnorm(t1, n1);
    vm1_sign = 0;
  } else {
    ulbn_sub(t1, t2, nt, t1, n1);
    n1 = ulbn_rnorm(t1, nt);
    vm1_sign = 1;
  }

  /* t3 = b0 - b1 + b2 - b3 */
  n2 = ulbn_rnorm(t3, m + 1);
  nt = ulbn_rnorm(t4, m + 1);
  if(ulbn_cmp(t3, n2, t4, nt) >= 0) {
    ulbn_sub(t3, t3, n2, t4, nt);
    n2 = ulbn_rnorm(t3, n2);
  } else {
    ulbn_sub(t3, t4, nt, t3, n2);
    n2 = ulbn_rnorm(t3, nt);
    vm1_sign ^= 1;
  }

  /* vm1 = t1 * t3 = (a0 - a1 + a2 - a3) * (b0 - b1 + b2 - b3) */
  if(n1 && n2) {
    ulbn_mul(alloc, vm1, t1, n1, t3, n2);
    ulbn_fill0(vm1 + n1 + n2, (m2 + 2) - (n1 + n2));
    ulbn_neg(vm1, vm1, m2 + 2, ulbn_cast_limb(vm1_sign));
  } else {
    if(!vm1_sign)
      ulbn_fill0(vm1, m2 + 2);
    else
      ulbn_fill1(vm1, m2 + 2);
  }

  /* t1 = a0 + 4*a2 */
  t1[m] = ulbn_addshl(t1, a0, m, a2, m, 2);
  /* t2 = 2*a1 */
  t2[m] = ulbn_shl(t2, a1, m, 1);
  /* t2 = t2 + 8*a3 */
  t2[m] += ulbn_addshl(t2, t2, m, a3, am, 3);
  /* t3 = b0 + 4*b2 */
  t3[m] = ulbn_addshl(t3, b0, m, b2, m, 2);
  /* t4 = 2*b1 */
  t4[m] = ulbn_shl(t4, b1, m, 1);
  /* t4 = t4 + 8*b3 */
  t4[m] += ulbn_addshl(t4, t4, m, b3, bm, 3);

  /* vm2 = t1 + t2 = a0 + 2*a1 + 4*a2 + 8*a3 */
  ulbn_add(vm2, t1, m + 1, t2, m + 1);
  /* vh = t3 + t4 = b0 + 2*b1 + 4*b2 + 8*b3 */
  ulbn_add(vh, t3, m + 1, t4, m + 1);
  /* v2 = vm2 * vh = (a0 + 2*a1 + 4*a2 + 8*a3) * (b0 + 2*b1 + 4*b2 + 8*b3) */
  ulbn_mul(alloc, v2, vm2, m + 1, vh, m + 1);

  /* t1 = a0 - 2*a1 + 4*a2 - 8*a3 */
  n1 = ulbn_rnorm(t1, m + 1);
  nt = ulbn_rnorm(t2, m + 1);
  if(ulbn_cmp(t1, n1, t2, nt) >= 0) {
    ulbn_sub(t1, t1, n1, t2, nt);
    n1 = ulbn_rnorm(t1, n1);
    vm2_sign = 0u;
  } else {
    ulbn_sub(t1, t2, nt, t1, n1);
    n1 = ulbn_rnorm(t1, nt);
    vm2_sign = 1u;
  }

  /* t3 = b0 - 2*b1 + 4*b2 - 8*b3 */
  n2 = ulbn_rnorm(t3, m + 1);
  nt = ulbn_rnorm(t4, m + 1);
  if(ulbn_cmp(t3, n2, t4, nt) >= 0) {
    ulbn_sub(t3, t3, n2, t4, nt);
    n2 = ulbn_rnorm(t3, n2);
  } else {
    ulbn_sub(t3, t4, nt, t3, n2);
    n2 = ulbn_rnorm(t3, nt);
    vm2_sign ^= 1u;
  }

  /* vm2 = t1 * t3 = (a0 - 2*a1 + 4*a2 - 8*a3) * (b0 - 2*b1 + 4*b2 - 8*b3) */
  if(n1 && n2) {
    ulbn_mul(alloc, vm2, t1, n1, t3, n2);
    ulbn_fill0(vm2 + n1 + n2, (m2 + 2) - (n1 + n2));
    ulbn_neg(vm2, vm2, m2 + 2, ulbn_cast_limb(vm2_sign));
  } else {
    if(!vm2_sign)
      ulbn_fill0(vm2, m2 + 2);
    else
      ulbn_fill1(vm2, m2 + 2);
  }

  /* t1 = a3 + a2 */
  t1[m] = ulbn_add(t1, a2, m, a3, am);
  /* t1 += t1 + a2 */
  t1[m] += ulbn_add(t1, t1, m, a2, m);
  /* t1 += 4*a1 */
  t1[m] += ulbn_addshl(t1, t1, m, a1, m, 2);
  /* t1 += 8*a0 */
  t1[m] += ulbn_addshl(t1, t1, m, a0, m, 3);
  /* t2 = b3 + b2 */
  t2[m] = ulbn_add(t2, b2, m, b3, bm);
  /* t2 += t2 + b2 */
  t2[m] += ulbn_add(t2, t2, m, b2, m);
  /* t2 += 4*b1 */
  t2[m] += ulbn_addshl(t2, t2, m, b1, m, 2);
  /* t2 += 8*b0 */
  t2[m] += ulbn_addshl(t2, t2, m, b0, m, 3);

  /* vh = t1 * t2 = (8*a0 + 4*a1 + 2*a2 + a3) * (8*b0 + 4*b1 + 2*b2 + b3) */
  ulbn_mul(alloc, vh, t1, m + 1, t2, m + 1);

  /* v0 = a0 * b0 */
  ulbn_mul(alloc, rp, a0, m, b0, m);
  /* vinf = a4 * b4 */
  ulbn_mul(alloc, rinf, a3, am, b3, bm);

    /*****************
     * interpolation *
     *****************/

  #if 0
  ulbn_dprint(stdout, "v0 = ", rp, m2);
  ulbn_dprint(stdout, "v1 = ", v1, m2 + _ULBN_FLEN);
  ulbn_dprint(stdout, "vm1 = ", vm1, m2 + _ULBN_FLEN);
  ulbn_dprint(stdout, "v2 = ", v2, m2 + _ULBN_FLEN);
  ulbn_dprint(stdout, "vm2 = ", vm2, m2 + _ULBN_FLEN);
  ulbn_dprint(stdout, "vh = ", vh, m2 + _ULBN_FLEN);
  ulbn_dprint(stdout, "vinf = ", rinf, abm);
  #endif

  /* vh = vh + v2 = (65, 34, 20, 16, 20, 34, 65)        ranging [0, 1458) */
  ulbn_add(vh, vh, m2 + _ULBN_FLEN, v2, m2 + _ULBN_FLEN);
  /* vm2 = (v2 - vm2) / 2 = (0, 32, 0, 8, 0, 2, 0)      ranging [0, 364) */
  ulbn_sub(vm2, v2, m2 + _ULBN_FLEN, vm2, m2 + _ULBN_FLEN);
  ulbn_shr(vm2, vm2, m2 + _ULBN_FLEN, 1);
  /* v2 = v2 - v0 = (64, 32, 16, 8, 4, 2, 0)            ranging [0, 728) */
  ulbn_sub(v2, v2, m2 + _ULBN_FLEN, rp, m2);
  /* v2 = (v2 - vm2 - vinf * 64) / 4 = (0, 0, 4, 0, 1, 0, 0)       ranging [0, 75) */
  ulbn_sub(v2, v2, m2 + _ULBN_FLEN, vm2, m2 + _ULBN_FLEN);
  ulbn_subshl(v2, v2, m2 + _ULBN_FLEN, rinf, abm, 6);
  ulbn_shr(v2, v2, m2 + _ULBN_FLEN, 2);
  /* vm1 = (v1 - vm1) / 2 = (0, 1, 0, 1, 0, 1, 0)       ranging [0, 32) */
  ulbn_sub(vm1, v1, m2 + _ULBN_FLEN, vm1, m2 + _ULBN_FLEN);
  ulbn_shr(vm1, vm1, m2 + _ULBN_FLEN, 1);
  /* v1 = v1 - vm1 = (1, 0, 1, 0, 1, 0, 1)              ranging [0, 32) */
  ulbn_sub(v1, v1, m2 + _ULBN_FLEN, vm1, m2 + _ULBN_FLEN);

  /* vh = vh - v1 * 65 = (0, 34, -45, 16, -45, 34, 0)   ranging (-1350, 728) */
  ulbn_submul1(vh, v1, m2 + _ULBN_FLEN, 65);
  /* v1 = v1 - vinf - v0 = (0, 0, 1, 0, 1, 0, 0)        ranging [0, 30) */
  ulbn_sub(v1, v1, m2 + _ULBN_FLEN, rinf, am + bm);
  ulbn_sub(v1, v1, m2 + _ULBN_FLEN, rp, m2);
  /* vh = (vh + v1 * 45) / 2 = (0, 17, 0, 8, 0, 17, 0)  ranging [0, 364) */
  ulbn_addmul1(vh, v1, m2 + _ULBN_FLEN, 45);
  ulbn_shr(vh, vh, m2 + _ULBN_FLEN, 1);
  /* v2 = (v2 - v1) / 3 = (0, 0, 1, 0, 0, 0, 0)         ranging [0, 15) */
  ulbn_sub(v2, v2, m2 + _ULBN_FLEN, v1, m2 + _ULBN_FLEN);
  ulbn_shortdiv(v2, v2, m2 + _ULBN_FLEN, 3);
  /* v1 = v1 - v2 = (0, 0, 0, 0, 1, 0, 0)               ranging [0, 15) */
  ulbn_sub(v1, v1, m2 + _ULBN_FLEN, v2, m2 + _ULBN_FLEN);

  /* vm2 = vh - vm2 = (0, -15, 0, 0, 0, 15, 0)          ranging (-90, 90) */
  ulbn_sub(vm2, vh, m2 + _ULBN_FLEN, vm2, m2 + _ULBN_FLEN);
  /* vh = (vh - vm1 * 8) / 9 = (0, 1, 0, 0, 0, 1, 0)    ranging [0, 12) */
  ulbn_subshln(vh, vh, vm1, m2 + _ULBN_FLEN, 3);
  ulbn_shortdiv(vh, vh, m2 + _ULBN_FLEN, 9);
  /* vm1 = vm1 - vh = (0, 0, 0, 1, 0, 0, 0)             ranging [0, 20) */
  ulbn_sub(vm1, vm1, m2 + _ULBN_FLEN, vh, m2 + _ULBN_FLEN);
  /* vm2 = (vm2 / 15 + vh) / 2 = (0, 0, 0, 0, 0, 1, 0)  ranging [0, 6) */
  if(vm2[m2 + _ULBN_FLEN - 1] & ULBN_LIMB_SIGNBIT) {
    ulbn_neg(vm2, vm2, m2 + _ULBN_FLEN, 1);
    ulbn_shortdiv(vm2, vm2, m2 + _ULBN_FLEN, 15);
    ulbn_neg(vm2, vm2, m2 + _ULBN_FLEN, 1);
  } else {
    ulbn_shortdiv(vm2, vm2, m2 + _ULBN_FLEN, 15);
  }
  ulbn_add(vm2, vm2, m2 + _ULBN_FLEN, vh, m2 + _ULBN_FLEN);
  ulbn_shr(vm2, vm2, m2 + _ULBN_FLEN, 1);
  /* vh = vh - vm2 = (0, 1, 0, 0, 0, 0, 0)              ranging [0, 6) */
  ulbn_sub(vh, vh, m2 + _ULBN_FLEN, vm2, m2 + _ULBN_FLEN);

    /*****************
     * recomposition *
     *****************/

  #if 0
  ulbn_dprint(stdout, "v0 = ", rp, m2);
  ulbn_dprint(stdout, "vm2 = ", vm2, m2 + _ULBN_FLEN);
  ulbn_dprint(stdout, "v1 = ", v1, m2 + _ULBN_FLEN);
  ulbn_dprint(stdout, "vm1 = ", vm1, m2 + _ULBN_FLEN);
  ulbn_dprint(stdout, "v2 = ", v2, m2 + _ULBN_FLEN);
  ulbn_dprint(stdout, "vh = ", vh, m2 + _ULBN_FLEN);
  ulbn_dprint(stdout, "vinf = ", rinf, abm);
  #endif

  ulbn_fill0(rinf - m2 + _ULBN_FLEN, m2 - _ULBN_FLEN);
  ulbn_add(rp + m, rp + m, an + bn - m, vm2, m2 + _ULBN_FLEN);
  ulbn_add(rp + m3, rp + m3, an + bn - m3, vm1, m2 + _ULBN_FLEN);
  ulbn_add(rp + m4, rp + m4, an + bn - m4, v2, m2 + _ULBN_FLEN);
  ulbn_add(rinf - m, rinf - m, abm + m, vh, _ulbn_min_(m2 + _ULBN_FLEN, abm + m));
  err = 0;

  ulbn_deallocT(ulbn_limb_t, alloc, t4, m2 + 2);
cleanup_t4:
  ulbn_deallocT(ulbn_limb_t, alloc, t3, m2 + 2);
cleanup_t3:
  ulbn_deallocT(ulbn_limb_t, alloc, t2, m2 + 2);
cleanup_t2:
  ulbn_deallocT(ulbn_limb_t, alloc, t1, m2 + 2);
cleanup_t1:
  ulbn_deallocT(ulbn_limb_t, alloc, vh, m2 + 2);
cleanup_vh:
  ulbn_deallocT(ulbn_limb_t, alloc, vm2, m2 + 2);
cleanup_vm2:
  ulbn_deallocT(ulbn_limb_t, alloc, vm1, m2 + 2);
cleanup_vm1:
  ulbn_deallocT(ulbn_limb_t, alloc, v2, m2 + 2);
cleanup_v2:
  return err;
  #undef _ULBN_FLEN
}
#endif /* _ULBN_USE_TOOM_4 */

#define _ULBN_FFT_THRESHOLD 2048
#if _ULBN_FFT_THRESHOLD >= ULBN_USIZE_MAX
  #undef ULBN_CONF_FFT
  #define ULBN_CONF_FFT 0
#endif
#if ULBN_CONF_FFT
ULBN_PRIVATE int _ulbn_mul_fft(
  const ulbn_alloc_t* alloc, ulbn_limb_t* rp,                                    /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, const ulbn_limb_t* bp, ulbn_usize_t bn /* */
);
#endif

/* Note: If allocation fails, it falls back to using a version demanding less cache,
  eventually falling back to the school method (time complexity O(n^2)) */
ULBN_INTERNAL void ulbn_mul(
  const ulbn_alloc_t* alloc, ulbn_limb_t* ul_restrict rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,                 /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn                  /* */
) {
  ulbn_usize_t m, m2;
#if ULBN_CONF_CHECK_ALLOCATION_FAILURE
  #define _ULBN_DO_IF_MUL_FAILED(x, expr) ULBN_DO_IF_ALLOC_COND((x) < 0, expr)
#else
  #define _ULBN_DO_IF_MUL_FAILED(x, expr) (x)
#endif

  ulbn_check_startup();
  ulbn_assert(an + bn >= an);

#if ULBN_CONF_FFT
  /* if `ulbn_limb_t` is small, it's hard to use a large FFT, so we can split it first */
  if(ul_unlikely(an + bn > _ULBN_FFT_THRESHOLD)) {
    if(_ulbn_mul_fft(alloc, rp, ap, an, bp, bn) >= 0)
      return;
  }
#endif

  if(an < bn) {
    _ulbn_swap_(const ulbn_limb_t*, ap, bp);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }
  if(an <= _ULBN_TOOM_1_THRESHOLD) {
  fallback_school:
    ulbn_mul_school(rp, ap, an, bp, bn);
    return;
  }

  m2 = m = (an + 1) >> 1;
  if(bn <= m) {
    _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_21(alloc, rp, m2, ap, an, bp, bn), goto fallback_school;);
    return;
  }

  if(an <= _ULBN_TOOM_2_THRESHOLD) {
  fallback_toom2:
    /* if(bn > m) */
    _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_22(alloc, rp, m2, ap, an, bp, bn), goto fallback_school;);
    return;
  }

#if _ULBN_USE_TOOM_3 && _ULBN_USE_TOOM_4
  if(an <= _ULBN_TOOM_3_THRESHOLD) {
  fallback_toom3:
    m = (an + 2) / 3;
    if(bn > m + m) {
      _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_33(alloc, rp, m, ap, an, bp, bn), goto fallback_toom2;);
      return;
    }
    /* if(bn > m) */
    _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_32(alloc, rp, m, ap, an, bp, bn), goto fallback_toom2;);
    return;
  }

  m = (an + 3) >> 2;
  if(bn > m * 3) {
    _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_44(alloc, rp, m, ap, an, bp, bn), goto fallback_toom3;);
    return;
  }
  if(ul_likely(bn > m * 2)) {
    _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_43(alloc, rp, m, ap, an, bp, bn), goto fallback_toom3;);
    return;
  }
#elif _ULBN_USE_TOOM_3 && !_ULBN_USE_TOOM_4
  m = (an + 2) / 3;
  if(bn > m + m) {
    _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_33(alloc, rp, m, ap, an, bp, bn), goto fallback_toom2;);
    return;
  }
  /* if(bn > m) */
  _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_32(alloc, rp, m, ap, an, bp, bn), goto fallback_toom2;);
  return;
#else
  goto fallback_toom2;
#endif

  ulbn_assert(bn > m2);
  goto fallback_toom2;
#undef _ULBN_DO_IF_MUL_FAILED
}

/* rp[0:an+bn] = ap[0:an] * bp[0:bn]
  This version will automatically select the appropriate algorithm for computation. */
ULBN_INTERNAL int ulbn_mul_guard(
  const ulbn_alloc_t* alloc, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,     /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn      /* */
) {
  ulbn_limb_t *ul_restrict tap = ul_nullptr, *ul_restrict tbp = ul_nullptr;
  int err;

  ulbn_assert_same_or_not_overlap(rp, an + bn, ap, an);
  ulbn_assert_same_or_not_overlap(rp, an + bn, bp, bn);

  ulbn_assert(an + bn >= an);

#if ULBN_CONF_FFT
  if(an + bn >= _ULBN_FFT_THRESHOLD) {
    err = _ulbn_mul_fft(alloc, rp, ap, an, bp, bn);
    if(err >= 0)
      return err;
  }
#endif

  if(ul_unlikely(rp == ap)) {
    tap = ulbn_allocT(ulbn_limb_t, alloc, an);
    ULBN_RETURN_IF_ALLOC_FAILED(tap, ULBN_ERR_NOMEM);
    ulbn_copy(tap, ap, an);
    if(ul_unlikely(ap == bp))
      bp = tap;
    ap = tap;
  }
  if(ul_unlikely(rp == bp)) {
    tbp = ulbn_allocT(ulbn_limb_t, alloc, bn);
    ULBN_DO_IF_ALLOC_FAILED(tbp, {
      err = ULBN_ERR_NOMEM;
      goto cleanup;
    });
    ulbn_copy(tbp, bp, bn);
    bp = tbp;
  }

  ulbn_mul(alloc, rp, ap, an, bp, bn);
  err = 0;

cleanup:
  if(ul_unlikely(tap != ul_nullptr))
    ulbn_deallocT(ulbn_limb_t, alloc, tap, an);
  if(ul_unlikely(tbp != ul_nullptr))
    ulbn_deallocT(ulbn_limb_t, alloc, tbp, bn);
  return err;
}

/**************
 * <ulbn> FFT *
 **************/

#if ULBN_CONF_FFT
ULBN_PRIVATE ulbn_limb_t ulbnfft_addmod(ulbn_limb_t a, ulbn_limb_t b, ulbn_limb_t m) {
  const ulbn_limb_t c = a + b;
  ulbn_assert(a < m && b < m && m < ULBN_LIMB_SIGNBIT);
  return c < m ? c : c - m;
}

  /*
  The implementation idea of FFT comes from [libbf](https://bellard.org/libbf/)
  The related ideas come from <<Prime Numbers: A Computational Perspective>> (Richard Crandall, Carl Pomerance)

  Below is the FFT (ping-pong variant, in-order, no bit-scramble), where `X` is a signal sequence of length `N`
  Algorithm FFT {
    // # Initialize
    F = 1;
    Y = [];

    // # Outer loop
    for(log2(N) >= f > 0) { // F == N / (2 ** f)
      for(0 <= i < N / F) {
        a := exp(-2 * pi * i * F / N);
        for(0 <= j < F) {
          (a0, a1) = (X[i * F + j], X[i * F + j + N / 2]);
          Y[i * F * 2 + j] = a0 + a1;
          Y[i * F * 2 + j + F] = a * (a0 - a1);
        }
      }
      F *= 2;
      (X, Y) = (Y, X); // swap X and Y
    }

    // # Make ping-pong parity decision
    if(log2(N) is odd) return X;
    else return Y;
  }
  */
  /*
    During the NTT process, we frequently need to compute $w^{(P-1)/l}$,
      where $P$ is the modulus, $w$ is the primitive root of the modulus, and $l$ is the length of the NTT.
    $P$ must to be the form $1 + s * 2^x$,
      where $s$ is an odd number (not necessarily a prime), and $x$ is a preset size (`ULBNFFT_PROOT_2EXP` in the code).
    In this way, we can precompute $w^s$ and store it as our primitive root, which is the unit root when $n=2^x$.
    When we need the unit root for length $n$, we can compute $proot^{x/2^l}$, which is the unit root we need.
    This process can be precomputed and stored in `ulbnfft_proot_pow`.
  */



  #define ULBNFFT_NMODS 5
  #define ULBNFFT_MOD_LOG2_MAX (ULBN_LIMB_BITS - 2)
  #define ULBNFFT_MOD_LOG2_MIN (ULBN_LIMB_BITS - 3)
  #if ULBN_LIMB_MAX == 0xFFFFFFFFu
    #define ULBNFFT_PROOT_2EXP 23
static const ulbn_limb_t ulbnfft_mods[ULBNFFT_NMODS] = {
  0x23800001, 0x26800001, 0x34800001, 0x35800001, 0x3B800001,
};
static const unsigned ulbnfft_int_bits[ULBNFFT_NMODS] = {
  147, 118, 89, 59, 29,
};
static ulbn_limb_t ulbnfft_proot[2][ULBNFFT_NMODS] = {
  { 0x158A82F1, 0x0D5E196D, 0x104D68E3, 0x340422F0, 0x00E9A248 },
  { 0x136A882F, 0x1B0FE28F, 0x068AA1FC, 0x15279CC7, 0x1C01A690 },
};
static const ulbn_limb_t ulbnfft_mods_cr[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2] = {
  0x20155563, 0xDE5A5A9, 0x2B18E392, 0x32D2AAAE, 0xD200004, 0x33B7777C, 0x31955559, 0x1AC00036, 0x1DC00009, 0x18CAAAB5,
};
    #define _ULBNFFT_PREDEFINED
  #elif _ULBN_IS_64BIT(ULBN_LIMB_MAX)
    #define ULBNFFT_PROOT_2EXP 53
static const ulbn_limb_t ulbnfft_mods[ULBNFFT_NMODS] = { 0x3460000000000001, 0x3820000000000001, 0x3960000000000001,
                                                         0x3AE0000000000001, 0x3EA0000000000001 };
static const unsigned ulbnfft_int_bits[ULBNFFT_NMODS] = { 309, 247, 185, 123, 61 };
static const ulbn_limb_t ulbnfft_proot[2][ULBNFFT_NMODS] = {
  { 0x1C708B2263FABBAD, 0x0433067489E59ABC, 0x093E91AE10FEF2BB, 0x364C95F88A24DA05, 0x0CBA83E69F37F265 },
  { 0x1FAA406AC14078D1, 0x1BD993B1FDB306B0, 0x22502FE8592A9BD5, 0x1F7FD269B1EE9A9F, 0x2AF4AFB022785FF6 },
};
static const ulbn_limb_t ulbnfft_mods_cr[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2] = {
  0x3641111111111121, 0x2998CCCCCCCCCCD9, 0x32F313B13B13B145, 0x1625DA895DA895E1, 0x33A3333333333362,
  0x0D61745D1745D18A, 0x389A76276276276D, 0x2C28000000000028, 0x165DB6DB6DB6DB7A, 0x0643333333333344,
};
    #define _ULBNFFT_PREDEFINED
  #else
    #define ULBNFFT_PROOT_2EXP (ULBNFFT_MOD_LOG2_MIN - 8)
static ulbn_limb_t ulbnfft_mods[ULBNFFT_NMODS];
static unsigned ulbnfft_int_bits[ULBNFFT_NMODS];
static ulbn_limb_t ulbnfft_proot[2][ULBNFFT_NMODS];
static ulbn_limb_t ulbnfft_mods_cr[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2];
  #endif

ul_static_assert(
  ULBNFFT_PROOT_2EXP < ULBNFFT_MOD_LOG2_MIN && ULBNFFT_PROOT_2EXP > 0, "`ulbn_limb_t` is too small to support NTT"
);
static ulbn_limb_t ulbnfft_mods_div[ULBNFFT_NMODS];
static ulbn_limb_t ulbnfft_mods_cr_finv[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2];

static ulbn_limb_t ulbnfft_proot_pow[2][ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1];
static ulbn_limb_t ulbnfft_proot_pow_finv[2][ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1];

static ulbn_limb_t ulbnfft_len_inv[ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1];
static ulbn_limb_t ulbnfft_len_inv_finv[ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1];


/* rh < 2^{ULBNFFT_MOD_LOG2_MIN} */
ULBN_PRIVATE ulbn_limb_t ulbnfft_mod(ulbn_limb_t rh, ulbn_limb_t rl, ulbn_limb_t m, ulbn_limb_t m_div) {
  ulbn_limb_t q, t1, t0;

  ulbn_assert(ULBN_LIMB_SHL(1u, ULBNFFT_MOD_LOG2_MIN) <= m && m < ULBN_LIMB_SHL(1u, ULBNFFT_MOD_LOG2_MAX));
  ulbn_assert(rh < ULBN_LIMB_SHL(1u, ULBNFFT_MOD_LOG2_MIN));

  t1 = ulbn_cast_limb((rh << (ULBN_LIMB_BITS - ULBNFFT_MOD_LOG2_MIN)) | (rl >> ULBNFFT_MOD_LOG2_MIN));
  _ulbn_umul_(q, t0, t1, m_div);
  ulbn_assert(q <= ULBN_LIMB_MAX - 2);
  q += 2;
  _ulbn_umul_(t1, t0, q, m);
  _ulbn_sub_(rh, rl, rh, rl, t1, t0);
  if(rh & ULBN_LIMB_SIGNBIT)
    _ulbn_add_(rh, rl, rh, rl, 0, m);
  return rl + (m & rh);
}
/* 0 <= a * b < 2^{64+ULBNFFT_MOD_LOG2} */
ULBN_PRIVATE ulbn_limb_t ulbnfft_mulmod(ulbn_limb_t a, ulbn_limb_t b, ulbn_limb_t m, ulbn_limb_t m_div) {
  ulbn_limb_t ph, pl;
  _ulbn_umul_(ph, pl, a, b);
  return ulbnfft_mod(ph, pl, m, m_div);
}

/* `r` or `r + m` */
ULBN_PRIVATE ulbn_limb_t ulbnfft_mulmod2(ulbn_limb_t a, ulbn_limb_t b, ulbn_limb_t m, ulbn_limb_t b_finv) {
  ulbn_limb_t q, r;
  ulbn_assert(b < m);
  _ulbn_umul_(q, r, a, b_finv);
  (void)r;
  return ulbn_cast_limb(a * b - q * m);
}
ULBN_PRIVATE ulbn_limb_t ulbnfft_mod_init(ulbn_limb_t m) {
  ulbn_limb_t q, r;
  const ulbn_limb_t ah = ulbn_cast_limb(ULBN_LIMB_SHL(1u, ULBNFFT_MOD_LOG2_MIN));
  _ulbn_udiv_(q, r, ah, 0, m);
  (void)r;
  return q;
}
ULBN_PRIVATE ulbn_limb_t ulbnfft_mulmod2_init(ulbn_limb_t b, ulbn_limb_t m) {
  ulbn_limb_t q, r;
  _ulbn_udiv_(q, r, b, 0, m);
  (void)r;
  return q;
}


  #ifndef _ULBNFFT_PREDEFINED
ULBN_PRIVATE ulbn_limb_t ulbnfft_mulmod_slow(ulbn_limb_t a, ulbn_limb_t b, ulbn_limb_t m) {
    #ifdef ulbn_dlimb_t
  ulbn_dlimb_t v = ulbn_cast_dlimb(a) * b;
  return ulbn_cast_limb(v % m);
    #else
  ulbn_limb_t h, l;
  _ulbn_umul_(h, l, a, b);
  _ulbn_udiv_(a, b, h, l, m);
  return b;
    #endif
}
ULBN_PRIVATE ulbn_limb_t ulbnfft_powmod_slow(ulbn_limb_t a, ulbn_limb_t exp, ulbn_limb_t m) {
  ulbn_limb_t r = 1;
  while(exp != 0) {
    if(exp & 1)
      r = ulbnfft_mulmod_slow(r, a, m);
    a = ulbnfft_mulmod_slow(a, a, m);
    exp >>= 1;
  }
  return r;
}
ULBN_PRIVATE ulbn_limb_t ulbnfft_invmod_slow(ulbn_limb_t a, ulbn_limb_t m) {
  return ulbnfft_powmod_slow(a, m - 2, m);
}

/* Miller-Rabin primality test */
ULBN_PRIVATE int ulbnfft_miller_rabin(ulbn_rand_t* rng, ulbn_limb_t n) {
  ulbn_limb_t u = n - 1;
  ulbn_limb_t t = 0;
  ulbn_limb_t test = ULBN_LIMB_BITS; /* the number of tests is not guaranteed to be smallest */

  if(n < 5)
    return n == 2 || n == 3;
  if((n % 6) != 1 && (n % 6) != 5)
    return 0;
  while((u & 1) == 0) {
    u >>= 1;
    t++;
  }
  while(test-- != 0) {
    ulbn_limb_t a = ulbn_rand_step(rng) % (n - 3) + 2;
    ulbn_limb_t v = ulbnfft_powmod_slow(a, u, n);
    ulbn_limb_t s;
    if(v == 1)
      continue;
    for(s = 0; s < t; ++s) {
      if(v == n - 1)
        break;
      v = ulbnfft_mulmod_slow(v, v, n);
    }
    if(s == t)
      return 0;
  }
  return 1;
}

ULBN_PRIVATE ulbn_limb_t _ulbn_gcd_(ulbn_limb_t a, ulbn_limb_t b);
/* Pollard Rho algorithm */
ULBN_PRIVATE ulbn_limb_t ulbnfft_pollard_rho(ulbn_rand_t* rng, ulbn_limb_t x) {
  ulbn_limb_t s = 0, t = 0;
  ulbn_limb_t c, d, val = 1;
  ulbn_limb_t step = 0, goal = 1;
  c = ulbn_rand_step(rng) % (x - 1) + 1;
  for(;;) {
    ulbn_assert(goal != 0);
    for(step = 1; step <= goal; ++step) {
      t = ulbnfft_addmod(ulbnfft_mulmod_slow(t, t, x), c, x);
      val = ulbnfft_mulmod_slow(val, (t >= s ? t - s : s - t), x);
      if(val == 0)
        return x;
      if((step & 0x7F) == 0) {
        d = _ulbn_gcd_(val, x);
        if(d > 1)
          return d;
      }
    }
    d = _ulbn_gcd_(val, x);
    if(d > 1)
      return d;

    goal <<= 1;
    s = t;
    val = 1;
  }
}

typedef struct ulbnfft_factors_t {
  ulbn_limb_t* factors;
  size_t len, cap;
} ulbnfft_factors_t;
ULBN_PRIVATE void ulbnfft_factorize(ulbn_rand_t* rng, ulbnfft_factors_t* ptr, ulbn_limb_t x) {
  ulbn_limb_t l;
  while(x > 1) {
    if(ulbnfft_miller_rabin(rng, x)) /* is prime number? */
      break;
    l = ulbnfft_pollard_rho(rng, x);
    ulbnfft_factorize(rng, ptr, l);
    x /= l;
  }

  if(x <= 1)
    return;
  if(ptr->len == ptr->cap) {
    ptr->cap += (ptr->cap >> 1) + 1u;
    if(ul_unlikely(ptr->cap < ptr->len)) {
      fprintf(stderr, "ulbn: factorize overflow\n");
      abort();
    }
    ptr->factors = ul_reinterpret_cast(ulbn_limb_t*, realloc(ptr->factors, ptr->cap * sizeof(ulbn_limb_t)));
    if(ul_unlikely(ptr->factors == ul_nullptr)) {
      fprintf(stderr, "ulbn: factorize out of memory\n");
      abort();
    }
  }
  ptr->factors[ptr->len++] = x;
}
/* check if `test` is a primitive root of `x`, requires `ptr` to hold prime factors of `x - 1` */
ULBN_PRIVATE int ulbnfft_check_proot(const ulbnfft_factors_t* ptr, ulbn_limb_t x, ulbn_limb_t test) {
  size_t n;
  for(n = ptr->len; n-- != 0;)
    if(ulbnfft_powmod_slow(test, (x - 1) / ptr->factors[n], x) == 1)
      return 0;
  return 1;
}
/* `ptr` holds prime factors of `x - 1` */
ULBN_PRIVATE ulbn_limb_t ulbnfft_get_proot(const ulbnfft_factors_t* ptr, ulbn_limb_t x) {
  ulbn_limb_t r = 2;
  for(;; ++r) {
    ulbn_assert(r < x);
    if(ulbnfft_check_proot(ptr, x, r))
      return r;
  }
}

ULBN_PRIVATE void ulbnfft_init_mods(ulbn_rand_t* rng) {
  static ul_constexpr const ulbn_limb_t LOWER_GUARD = ULBN_LIMB_SHL(1, ULBNFFT_MOD_LOG2_MIN);
  static ul_constexpr const ulbn_limb_t STEP_NUM = ULBN_LIMB_SHL(1, ULBNFFT_PROOT_2EXP) << 1;

  ulbn_limb_t m = ULBN_LIMB_SHL(1, ULBNFFT_MOD_LOG2_MAX) - 1;
  int mods = ULBNFFT_NMODS;
  m >>= ULBNFFT_PROOT_2EXP;
  m <<= ULBNFFT_PROOT_2EXP;
  m |= 1;
  for(; m >= LOWER_GUARD; m -= STEP_NUM) {
    if(ulbnfft_miller_rabin(rng, m))
      ulbnfft_mods[--mods] = m;
    if(mods == 0)
      break;
  }
  if(mods != 0) {
    fprintf(stderr, "ulbn: cannot find enough prime numbers for NTT, try to decrease ULBNFFT_PROOT_2EXP\n");
    abort();
  }
}
ULBN_PRIVATE void ulbnfft_init_int_bits(void) {
  ulbn_limb_t mul[ULBNFFT_NMODS + 1];
  ulbn_limb_t mul_copy[ULBNFFT_NMODS + 1];
  ulbn_usize_t muln = 1;
  int mods = ULBNFFT_NMODS - 1;

  mul[0] = 1;
  for(; mods >= 0; --mods) {
    ulbn_copy(mul_copy, mul, muln);
    mul[muln] = ulbn_mul1(mul, mul_copy, muln, ulbnfft_mods[mods]);
    muln += (mul[muln] != 0);
    ulbn_assert(muln > 0 && muln <= ULBNFFT_NMODS + 1);
    ulbnfft_int_bits[mods] = ulbn_cast_uint(ulbn_bit_width(mul, muln) - 1);
  }
}
ULBN_PRIVATE void ulbnfft_init_proot(ulbn_rand_t* rng) {
  int mods;
  ulbnfft_factors_t ptr;
  ulbn_limb_t m, min_proot;

  ptr.len = ptr.cap = 0;
  ptr.factors = ul_nullptr;
  for(mods = 0; mods < ULBNFFT_NMODS; ++mods) {
    m = ulbnfft_mods[mods];

    ptr.len = 0;
    ulbnfft_factorize(rng, &ptr, m - 1);
    min_proot = ulbnfft_get_proot(&ptr, m);

    ulbnfft_proot[0][mods] = ulbnfft_powmod_slow(min_proot, m >> ULBNFFT_PROOT_2EXP, m);
    ulbnfft_proot[1][mods] = ulbnfft_invmod_slow(ulbnfft_proot[0][mods], m);
  }
  free(ptr.factors);
}
  #endif

ULBN_PRIVATE void ulbnfft_init_mods_div(void) {
  int mods;
  for(mods = 0; mods < ULBNFFT_NMODS; ++mods)
    ulbnfft_mods_div[mods] = ulbnfft_mod_init(ulbnfft_mods[mods]);
}
ULBN_PRIVATE void ulbnfft_init_mods_cr(void) {
  int inv, mods, cnt = 0;
  for(inv = 0; inv < ULBNFFT_NMODS; ++inv)
    for(mods = inv + 1; mods < ULBNFFT_NMODS; ++mods) {
      /* 1/{MODS[inv]} (mod {MODS[mods]}) */
  #ifndef _ULBNFFT_PREDEFINED
      ulbnfft_mods_cr[cnt] = ulbnfft_invmod_slow(ulbnfft_mods[inv], ulbnfft_mods[mods]);
  #endif
      ulbnfft_mods_cr_finv[cnt] = ulbnfft_mulmod2_init(ulbnfft_mods_cr[cnt], ulbnfft_mods[mods]);
      ++cnt;
    }
}
ULBN_PRIVATE void ulbnfft_init_proot_pow(void) {
  int mods, inverse;
  unsigned exp;
  ulbn_limb_t m, mdiv;

  for(mods = 0; mods < ULBNFFT_NMODS; ++mods) {
    m = ulbnfft_mods[mods];
    mdiv = ulbnfft_mods_div[mods];
    for(inverse = 0; inverse < 2; ++inverse) {
      ulbn_limb_t c = ulbnfft_proot[inverse][mods];
      for(exp = 0; exp < ULBNFFT_PROOT_2EXP; ++exp) {
        ulbnfft_proot_pow[inverse][mods][ULBNFFT_PROOT_2EXP - exp] = c;
        ulbnfft_proot_pow_finv[inverse][mods][ULBNFFT_PROOT_2EXP - exp] = ulbnfft_mulmod2_init(c, m);
        c = ulbnfft_mulmod(c, c, m, mdiv);
      }
    }
  }
}
ULBN_PRIVATE void ulbnfft_init_len_inv(void) {
  int mods;
  unsigned exp;
  ulbn_limb_t m, mdiv;
  ulbn_limb_t c, c_step;
  for(mods = 0; mods < ULBNFFT_NMODS; ++mods) {
    m = ulbnfft_mods[mods];
    mdiv = ulbnfft_mods_div[mods];
    c = 1;
    c_step = (m + 1) >> 1; /* 1/2 (mod m) */
    for(exp = 0; exp <= ULBNFFT_PROOT_2EXP; ++exp) {
      ulbnfft_len_inv[mods][exp] = c; /* 1/2^{exp} (mod m) */
      ulbnfft_len_inv_finv[mods][exp] = ulbnfft_mulmod2_init(c, m);
      c = ulbnfft_mulmod(c, c_step, m, mdiv);
    }
  }
}

ULBN_PRIVATE void _ulbn_startup_fft(void) {
  #ifndef _ULBNFFT_PREDEFINED
  ulbn_rand_t rng;
  ulbn_rand_init(&rng);

  ulbnfft_init_mods(&rng);
  ulbnfft_init_int_bits();
  ulbnfft_init_proot(&rng);
  #endif

  ulbnfft_init_mods_div();
  ulbnfft_init_mods_cr();
  ulbnfft_init_proot_pow();
  ulbnfft_init_len_inv();
}

ul_static_assert(ULBNFFT_PROOT_2EXP < ULBNFFT_MOD_LOG2_MIN, "ULBNFFT_PROOT_2EXP < ULBNFFT_MOD_LOG2_MIN");
ul_static_assert(ULBNFFT_MOD_LOG2_MIN < ULBNFFT_MOD_LOG2_MAX, "ULBNFFT_MOD_LOG2_MIN < ULBNFFT_MOD_LOG2_MAX");


ULBN_PRIVATE int ulbnfft_clz_bits_(ulbn_bits_t x) {
  #if ul_has_builtin(__builtin_clz) && ULBN_BITS_MAX <= UINT_MAX
  return ulbn_condexpr(
    x != 0, __builtin_clz(x) - ulbn_cast_int(sizeof(int) * CHAR_BIT - sizeof(ulbn_bits_t) * CHAR_BIT)
  );
  #elif ul_has_builtin(__builtin_clz) && ULBN_BITS_MAX == UINT_MAX
  return ulbn_condexpr(x != 0, __builtin_clz(x));
  #elif ul_has_builtin(__builtin_clzl) && ULBN_BITS_MAX == ULONG_MAX
  return ulbn_condexpr(x != 0, __builtin_clzl(x));
  #elif ul_has_builtin(__builtin_clzll) && ULBN_BITS_MAX == ULLONG_MAX
  return ulbn_condexpr(x != 0, __builtin_clzll(x));
  #else
  static const ulbn_bits_t MASK = ulbn_cast_bits(ulbn_cast_bits(1) << (sizeof(ulbn_bits_t) * CHAR_BIT - 1));
  int r = 0;

    #if ULBN_BITS_MAX > 0xFFu
  static const ulbn_bits_t MASK8 = ulbn_cast_bits(ulbn_cast_bits(0xFF) << (sizeof(ulbn_bits_t) * CHAR_BIT - 8));
  ulbn_assert(x != 0);
  while(!(x & MASK8)) {
    r += 8;
    x <<= 8;
  }
    #else
  ulbn_assert(x != 0);
    #endif

  while(!(x & MASK)) {
    ++r;
    x <<= 1;
  }
  return r;
  #endif
}
ULBN_PRIVATE unsigned ulbnfft_get_size(unsigned* pdpl, unsigned* pnmods, ulbn_usize_t len) {
  unsigned nmods;
  unsigned dpl_best = 0, nmods_best = 0;
  ulbn_bits_t cost, cost_best = ULBN_BITS_MAX;
  unsigned fft_len_log2, fft_len_log2_best = 0;
  ulbn_bits_t fft_len;

  /* use ulbnfft_mods[ULBNFFT_NMODS - nmods:] as modulos */
  for(nmods = 3; nmods <= ULBNFFT_NMODS; ++nmods) {
    const unsigned int_bits = ulbnfft_int_bits[ULBNFFT_NMODS - nmods];
    unsigned dpl = ulbn_cast_uint(
      _ulbn_min_((int_bits - 4) >> 1, 2 * ULBN_LIMB_BITS + 2 * ULBNFFT_MOD_LOG2_MIN - ULBNFFT_MOD_LOG2_MAX)
    );

    for(;;) {
      ulbn_assert(ulbn_cast_bits(len) < (ULBN_BITS_MAX - ULBN_LIMB_BITS + 1) / ULBN_LIMB_BITS);
      fft_len = (ulbn_cast_bits(len) * ULBN_LIMB_BITS + dpl - 1) / dpl;
      ulbn_assert(fft_len > 0);
      fft_len_log2 = sizeof(ulbn_bits_t) * CHAR_BIT - ulbn_cast_uint(ulbnfft_clz_bits_(fft_len));
      if(ul_unlikely(fft_len_log2 > ULBNFFT_PROOT_2EXP))
        goto next;
      ulbn_assert(fft_len_log2 < INT_MAX / nmods);
      if(ul_unlikely((ULBN_BITS_MAX >> fft_len_log2) <= ulbn_cast_bits(fft_len_log2 + 1) * nmods))
        goto next;

      if(fft_len_log2 + 2 * dpl <= int_bits) {
        cost = (ulbn_cast_bits(fft_len_log2 + 1) << fft_len_log2) * nmods;
        if(cost < cost_best) {
          cost_best = cost;
          dpl_best = dpl;
          nmods_best = nmods;
          fft_len_log2_best = fft_len_log2;
        }
        break;
      }

      --dpl;
      if(ul_unlikely(dpl == 0))
        break;
    }
  next:
    (void)0;
  }
  if(ul_unlikely(dpl_best == 0))
    return 0;
  if(dpl_best > (ULBN_LIMB_BITS + ULBNFFT_MOD_LOG2_MIN)
     && (ulbn_cast_bits(ULBN_LIMB_BITS + ULBNFFT_MOD_LOG2_MIN) << fft_len_log2_best)
          >= ulbn_cast_bits(len) * ULBN_LIMB_BITS)
    dpl_best = ULBN_LIMB_BITS + ULBNFFT_MOD_LOG2_MIN;
  *pdpl = dpl_best;
  *pnmods = nmods_best;
  return fft_len_log2_best;
}

ULBN_PRIVATE ulbn_limb_t ulbnfft_get(const ulbn_limb_t* ptr, ulbn_usize_t len, ulbn_bits_t bit_idx) {
  const ulbn_bits_t idx = bit_idx / ULBN_LIMB_BITS;
  const unsigned shift = ulbn_cast_uint(bit_idx % ULBN_LIMB_BITS);
  ulbn_limb_t a0, a1 = 0;

  if(idx >= len)
    return 0;
  a0 = ptr[idx];
  if(shift == 0)
    return a0;

  if(idx < len - 1u)
    a1 = ptr[idx + 1];
  return ulbn_cast_limb((a0 >> shift) | (a1 << (ULBN_LIMB_BITS - shift)));
}
ULBN_PRIVATE void ulbnfft_limb_to_ntt(
  ulbn_limb_t* ul_restrict dst, ulbn_usize_t fft_len,       /* */
  const ulbn_limb_t* ul_restrict src, ulbn_usize_t src_len, /* */
  const unsigned dpl, unsigned mod_idx                      /* */
) {
  static ul_constexpr const size_t LOG2_DIFF = ULBNFFT_MOD_LOG2_MAX - ULBNFFT_MOD_LOG2_MIN;
  static ul_constexpr const size_t LOG2_LIMB_DIFF = ULBN_LIMB_BITS - ULBNFFT_MOD_LOG2_MAX + ULBNFFT_MOD_LOG2_MIN;
  static ul_constexpr const ulbn_limb_t ADJ_MASK =
    ulbn_cast_limb(ULBN_LIMB_SHL(1, ULBN_LIMB_BITS - ULBNFFT_MOD_LOG2_MAX + ULBNFFT_MOD_LOG2_MIN) - 1);

  const unsigned shift = ulbn_cast_uint(dpl % ULBN_LIMB_BITS);
  const ulbn_limb_t mask = shift ? ulbn_cast_limb(ULBN_LIMB_SHL(1, shift) - 1u) : ULBN_LIMB_MAX;
  const ulbn_limb_t m = ulbnfft_mods[mod_idx], mdiv = ulbnfft_mods_div[mod_idx];
  const ulbn_usize_t n =
    ulbn_cast_usize(_ulbn_min_(fft_len, (ulbn_cast_bits(src_len) * ULBN_LIMB_BITS + dpl - 1) / dpl));
  ulbn_usize_t i;
  ulbn_bits_t bits = 0, bits2;
  ulbn_limb_t a0, a1 = 0, a2 = 0;

  for(i = 0; i < n; ++i) {
    a0 = ulbnfft_get(src, src_len, bits);
    if(dpl <= ULBN_LIMB_BITS + ULBNFFT_MOD_LOG2_MIN) {
      if(dpl > ULBN_LIMB_BITS)
        a1 = ulbn_cast_limb(ulbnfft_get(src, src_len, bits + ULBN_LIMB_BITS) & mask);
      else
        a0 &= mask;
      a0 = ulbnfft_mod(a1, a0, m, mdiv);
    } else {
      bits2 = bits + ULBN_LIMB_BITS;
      a1 = ulbnfft_get(src, src_len, bits2);
      if(dpl > ULBN_LIMB_BITS + ULBN_LIMB_BITS)
        a2 = ulbn_cast_limb(ulbnfft_get(src, src_len, bits2 + ULBN_LIMB_BITS) & mask);
      else
        a1 &= mask;

      a2 = ulbn_cast_limb((a2 << LOG2_DIFF) | (a1 >> LOG2_LIMB_DIFF));
      a1 = ulbn_cast_limb((a1 << LOG2_DIFF) | (a0 >> LOG2_LIMB_DIFF));
      a1 = ulbnfft_mod(a2, a1, m, mdiv);

      a0 = ulbn_cast_limb((a1 << LOG2_LIMB_DIFF) | (a0 & ADJ_MASK));
      a1 >>= LOG2_DIFF;
      a0 = ulbnfft_mod(a1, a0, m, mdiv);
    }
    bits += ulbn_cast_uint(dpl);
    ulbn_assert(a0 < m);
    dst[i] = a0;
  }

  if(n < fft_len)
    memset(dst + n, 0, (fft_len - n) * sizeof(ulbn_limb_t));
}

ULBN_PRIVATE void ulbnfft_vec_mul(
  ulbn_limb_t* ul_restrict ap, const ulbn_limb_t* ul_restrict bp, unsigned k, unsigned mod_idx
) {
  const ulbn_limb_t m = ulbnfft_mods[mod_idx];
  const ulbn_limb_t mdiv = ulbnfft_mods_div[mod_idx];
  const ulbn_limb_t norm = ulbnfft_len_inv[mod_idx][k];
  const ulbn_limb_t norm_finv = ulbnfft_len_inv_finv[mod_idx][k];
  const ulbn_usize_t n = ulbn_cast_usize(1) << k;
  ulbn_limb_t x;
  ulbn_usize_t i;

  for(i = 0; i < n; ++i) {
    x = ap[i];
    if(x >= m)
      x -= m;
    x = ulbnfft_mulmod(x, bp[i], m, mdiv);
    x = ulbnfft_mulmod2(x, norm, m, norm_finv);
    ap[i] = x;
  }
}
ULBN_PRIVATE void ulbnfft_fft(
  ulbn_limb_t* dest, ulbn_limb_t* src, ulbn_limb_t* tmp, /* */
  unsigned fft_len_log2, int inverse, unsigned mod_idx   /* */
) {
  ulbn_usize_t nblocks = ulbn_cast_usize(1) << fft_len_log2;
  unsigned fft_log2 = fft_len_log2;
  const ulbn_usize_t stride_in = nblocks >> 1;
  const ulbn_limb_t m = ulbnfft_mods[mod_idx], m2 = m + m;

  ulbn_limb_t *ul_restrict p1, *ul_restrict p2;

  ulbn_usize_t i, j, k, p;
  ulbn_usize_t fft_per_block = 1;

  ulbn_limb_t c, c_mul, c_mul_finv, c_inv;
  ulbn_limb_t a0, a1, b0, b1;

  p1 = src;
  p2 = tmp;
  ulbn_assert(nblocks > 1);
  while(nblocks > 2) {
    nblocks >>= 1;
    k = 0;
    p = 0;
    c = 1;
    c_mul = ulbnfft_proot_pow[inverse][mod_idx][fft_log2];
    c_mul_finv = ulbnfft_proot_pow_finv[inverse][mod_idx][fft_log2];

    for(i = 0; i < nblocks; ++i) {
      c_inv = ulbnfft_mulmod2_init(c, m);
      for(j = 0; j < fft_per_block; ++j) {
        a0 = p1[k + j];
        a1 = p1[k + j + stride_in];
        b0 = ulbnfft_addmod(a0, a1, m2);
        b1 = a0 - a1 + m2;
        b1 = ulbnfft_mulmod2(b1, c, m, c_inv);
        ulbn_assert(b0 < m2 && b1 < m2);
        p2[p + j] = b0;
        p2[p + j + fft_per_block] = b1;
      }

      k += fft_per_block;
      p += fft_per_block + fft_per_block;
      c = ulbnfft_mulmod2(c, c_mul, m, c_mul_finv);
      if(c >= m)
        c -= m;
    }

    fft_per_block <<= 1;
    --fft_log2;
    _ulbn_swap_(ulbn_limb_t*, p1, p2);
  }

  p2 = dest;
  for(k = 0; k < stride_in; ++k) {
    a0 = p1[k];
    a1 = p1[k + stride_in];
    b0 = ulbnfft_addmod(a0, a1, m2);
    b1 = a0 - a1;
    if(b1 > a0)
      b1 += m2;
    p2[k] = b0;
    p2[k + stride_in] = b1;
  }
}

ULBN_PRIVATE void ulbnfft_put(ulbn_limb_t* ptr, ulbn_usize_t len, ulbn_bits_t bit_idx, ulbn_limb_t val) {
  const ulbn_usize_t idx = ulbn_cast_usize(bit_idx / ULBN_LIMB_BITS);
  const unsigned shift = ulbn_cast_uint(bit_idx % ULBN_LIMB_BITS);
  if(idx >= len)
    return;
  ptr[idx] |= val << shift;
  if(shift != 0 && idx < len - 1u)
    ptr[idx + 1] |= val >> (ULBN_LIMB_BITS - shift);
}
ULBN_PRIVATE void ulbnfft_ntt_to_limb(
  ulbn_limb_t* ul_restrict dest, ulbn_usize_t dest_len,                                   /* */
  const ulbn_limb_t* ul_restrict src, unsigned fft_len_log2, unsigned dpl, unsigned nmods /* */
) {
  /*
    Garner's Algorithm:
      p[i] is modulos, x[i] is the modulo result, r[i][j] is (1/p[i]) mod p[j]

      for(0 <= i < k) {
        for(0 <= j < i) {
          x[i] = r[j][i] * (x[i] - x[j])
          x[i] = x[i] % p[i]
          if(x[i] < 0) {
            x[i] += p[i]
          }
        }
      }
      a = x[1] + (x[2] * p[1]) + (x[3] * p[1] * p[2]) + ... + (x[k] * p[1] * p[2] * ... * p[k-1])
    */

  const unsigned cr_idx = ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2 - nmods * (nmods - 1) / 2;
  const ulbn_limb_t* const mods_table = ulbnfft_mods + ULBNFFT_NMODS - nmods;
  const ulbn_limb_t* const mods_cr_table = ulbnfft_mods_cr + cr_idx;
  const ulbn_limb_t* const mods_cr_finv_table = ulbnfft_mods_cr_finv + cr_idx;
  const ulbn_usize_t fft_len = ulbn_cast_usize(1) << fft_len_log2;

  ulbn_usize_t i;
  unsigned j, k, l;
  const ulbn_usize_t n =
    ulbn_cast_usize(_ulbn_min_(fft_len, ulbn_cast_usize((ulbn_cast_bits(dest_len) * ULBN_LIMB_BITS + dpl - 1) / dpl)));

  ulbn_limb_t y[ULBNFFT_NMODS], u[ULBNFFT_NMODS], carry[ULBNFFT_NMODS] = { 0 };
  ulbn_limb_t th, tl;
  ulbn_limb_t r;

  const unsigned nlimb_to_put = ulbn_cast_uint((dpl - 1) / ULBN_LIMB_BITS);
  const unsigned shift = ulbn_cast_uint(dpl % ULBN_LIMB_BITS);
  const ulbn_limb_t mask = shift ? ulbn_cast_limb(ULBN_LIMB_SHL(1, shift) - 1u) : ULBN_LIMB_MAX;
  ulbn_bits_t bit_idx = 0;

  memset(dest, 0, dest_len * sizeof(ulbn_limb_t));

  for(i = 0; i < n; ++i) {
    for(j = 0; j < nmods; ++j) {
      const ulbn_limb_t m = mods_table[j];
      y[j] = src[i + (ul_static_cast(size_t, j) << fft_len_log2)];
      if(y[j] >= m)
        y[j] -= m;
    }

    /* Chinese remainder to get mixed radix representation */
    l = 0;
    for(j = 0; j < nmods - 1; ++j) {
      for(k = j + 1; k < nmods; ++k) {
        const ulbn_limb_t m = mods_table[k];
        /* Note: there is no overflow because the modulos are sorted by increasing order */
        y[k] = ulbnfft_mulmod2(y[k] - y[j] + m, mods_cr_table[l], m, mods_cr_finv_table[l]);
        if(y[k] >= m)
          y[k] -= m;
        ulbn_assert(y[k] < m);
        ++l;
      }
    }

    /* back to normal representation */
    u[0] = y[nmods - 1];
    l = 1;
    for(j = nmods - 2; j >= 1; --j) {
      r = y[j];
      for(k = 0; k < l; ++k) {
        _ulbn_umul_(th, tl, u[k], mods_table[j]);
        _ulbn_add_(th, tl, th, tl, 0, r);
        u[k] = tl;
        r = th;
      }
      u[l] = r;
      ++l;
    }

    /* last step, add the carry */
    r = y[0];
    for(k = 0; k < l; ++k) {
      _ulbn_umul_(th, tl, u[k], mods_table[j]);
      _ulbn_add_(th, tl, th, tl, 0, r);
      _ulbn_add_(r, u[k], th, tl, 0, carry[k]);
    }
    u[l] = r + carry[l];

    /* write the digits */
    for(j = 0; j < nlimb_to_put; ++j) {
      ulbnfft_put(dest, dest_len, bit_idx, u[j]);
      bit_idx += ulbn_cast_uint(ULBN_LIMB_BITS);
    }
    ulbnfft_put(dest, dest_len, bit_idx, u[nlimb_to_put] & mask);
    bit_idx += ulbn_cast_uint(shift);

    /* set carry */
    if(shift == 0) {
      for(j = nlimb_to_put + 1; j < nmods; ++j)
        carry[j - (nlimb_to_put + 1)] = u[j];
    } else {
      for(j = nlimb_to_put; j < nmods - 1; ++j)
        carry[j - nlimb_to_put] = ulbn_cast_limb((u[j] >> shift) | (u[j + 1] << (ULBN_LIMB_BITS - shift)));
      carry[nmods - nlimb_to_put - 1] = u[nmods - 1] >> shift;
    }
  }
}

/* return `ULBN_ERR_NOMEM` if out of memory; return `ULBN_ERR_EXCEED_RANGE` if `ulbn_limb_t` is too small to do FFT */
ULBN_PRIVATE int _ulbn_mul_fft(
  const ulbn_alloc_t* alloc, ulbn_limb_t* rp,                                    /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, const ulbn_limb_t* bp, ulbn_usize_t bn /* */
) {
  ulbn_usize_t rn;
  unsigned dpl, fft_len_log2, nmods, mod_idx, i;
  int err = ULBN_ERR_NOMEM;
  ulbn_usize_t fft_len;

  ulbn_limb_t *fft, *fft_ptr;
  ulbn_limb_t *buf1, *buf2;
  ulbn_limb_t* buf_temp;

  ulbn_check_startup();
  ulbn_assert(ulbn_cast_usize(an + bn) >= an);
  rn = an + bn;
  fft_len_log2 = ulbnfft_get_size(&dpl, &nmods, rn);
  if(ul_unlikely(fft_len_log2 == 0))
    return ULBN_ERR_EXCEED_RANGE;
  ulbn_assert(nmods >= 3);
  fft_len = ulbn_cast_usize(ulbn_cast_usize(1) << fft_len_log2);
  if(ul_unlikely(fft_len > _ULBN_SIZET_MAX / nmods))
    return ULBN_ERR_EXCEED_RANGE;

  fft = ulbn_allocT(ulbn_limb_t, alloc, fft_len * ul_static_cast(size_t, nmods) * sizeof(ulbn_limb_t));
  ULBN_DO_IF_ALLOC_FAILED(fft, goto cleanup_fft;);
  buf1 = ulbn_allocT(ulbn_limb_t, alloc, fft_len * sizeof(ulbn_limb_t));
  ULBN_DO_IF_ALLOC_FAILED(buf1, goto cleanup_buf1;);
  buf2 = ulbn_allocT(ulbn_limb_t, alloc, fft_len * sizeof(ulbn_limb_t));
  ULBN_DO_IF_ALLOC_FAILED(buf2, goto cleanup_buf2;);
  buf_temp = ulbn_allocT(ulbn_limb_t, alloc, fft_len * sizeof(ulbn_limb_t));
  ULBN_DO_IF_ALLOC_FAILED(buf_temp, goto cleanup_buf_temp;);

  fft_ptr = fft;
  for(i = 0; i < nmods; ++i) {
    mod_idx = ULBNFFT_NMODS - nmods + i;
    /* printf("m = %llX\n", (unsigned long long)ulbnfft_mods[mod_idx]); */
    ulbnfft_limb_to_ntt(buf2, fft_len, ap, an, dpl, mod_idx);
    /* ulbn_dprint(stdout, "src1 = ", buf2, fft_len); */
    ulbnfft_fft(buf1, buf2, buf_temp, fft_len_log2, 0, mod_idx);
    /* ulbn_dprint(stdout, "fft1 = ", buf1, fft_len); */

    ulbnfft_limb_to_ntt(fft_ptr, fft_len, bp, bn, dpl, mod_idx);
    /* ulbn_dprint(stdout, "src2 = ", fft_ptr, fft_len); */
    ulbnfft_fft(buf2, fft_ptr, buf_temp, fft_len_log2, 0, mod_idx);
    /* ulbn_dprint(stdout, "fft2 = ", buf2, fft_len); */

    ulbnfft_vec_mul(buf1, buf2, fft_len_log2, mod_idx);
    /* ulbn_dprint(stdout, "fftA = ", buf1, fft_len); */
    ulbnfft_fft(fft_ptr, buf1, buf_temp, fft_len_log2, 1, mod_idx);
    /* ulbn_dprint(stdout, "ifft = ", fft_ptr, fft_len); */

    fft_ptr += fft_len;
  }
  ulbnfft_ntt_to_limb(rp, rn, fft, fft_len_log2, dpl, nmods);
  err = 0;

  ulbn_deallocT(ulbn_limb_t, alloc, buf_temp, fft_len * sizeof(ulbn_limb_t));
cleanup_buf_temp:
  ulbn_deallocT(ulbn_limb_t, alloc, buf2, fft_len * sizeof(ulbn_limb_t));
cleanup_buf2:
  ulbn_deallocT(ulbn_limb_t, alloc, buf1, fft_len * sizeof(ulbn_limb_t));
cleanup_buf1:
  ulbn_deallocT(ulbn_limb_t, alloc, fft, fft_len * ul_static_cast(size_t, nmods) * sizeof(ulbn_limb_t));
cleanup_fft:
  return err;
}
#else /* !ULBN_CONF_FFT */
ULBN_PRIVATE void _ulbn_startup_fft(void) {
  (void)0;
}
#endif

/*******************
 * <ulbn> Division *
 *******************/

/* qp[0:an] = ap[0:an] // (d>>shift), rp[0] = ap[0:an] % (d>>shift),
  ensuring `d` is normalized and `di` is `ulbn_divinv1(d)` */
ULBN_INTERNAL void ulbn_divmod_inv1(
  ulbn_limb_t* qp, ulbn_limb_t* rp,        /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,  /* */
  ulbn_limb_t d, ulbn_limb_t di, int shift /* */
) {
  int rshift;
  ulbn_usize_t i;
  ulbn_limb_t a1, a0, ai;

  ulbn_assert(an >= 1);
  ulbn_assert_backward_overlap(qp, an, ap, an);
  ulbn_assert_forward_overlap(rp, an, ap, an);

  ulbn_assert(d != 0);
  ulbn_assert(shift >= 0 && ul_static_cast(size_t, shift) < ULBN_LIMB_BITS);
  /* `rshift` may be equal to the number of bits in `ulbn_limb_t`, so subtract
   * by 1 to avoid UB */
  rshift = ulbn_cast_int(ULBN_LIMB_BITS) - shift - 1;

  ai = ap[an - 1];
  a1 = ulbn_cast_limb((ai >> rshift) >> 1);

  /* ap'[i] = (ap[i] << shift) | (ap[i - 1] >> rshift) */
  for(i = an - 1; i > 0; --i) {
    a0 = ulbn_cast_limb(ai << shift);
    ai = ap[i - 1];
    a0 |= ulbn_cast_limb((ai >> rshift) >> 1);
    _ulbn_udiv_2by1_(qp[i], a1, a1, a0, d, di);
  }

  a0 = ulbn_cast_limb(ai << shift);
  _ulbn_udiv_2by1_(qp[0], a1, a1, a0, d, di);
  rp[0] = ulbn_cast_limb(a1 >> shift);
}
/* qp[0:an-1] = ap[0:an] // ((d1*B+d0)>>shift), rp[0:2] = ap[0:an] % ((d1*B+d0) >> shift),
  ensuring `d1` is normalized and `di` is `ulbn_divinv2(d1,d0)` */
ULBN_INTERNAL void ulbn_divmod_inv2(
  ulbn_limb_t* qp, ulbn_limb_t* rp,                         /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,                   /* */
  ulbn_limb_t d1, ulbn_limb_t d0, ulbn_limb_t di, int shift /* */
) {
  int rshift;
  ulbn_usize_t i;
  ulbn_limb_t a2, a1, a0, ai;

  ulbn_assert(an >= 2);
  ulbn_assert_backward_overlap(qp, an, ap, an);
  ulbn_assert_forward_overlap(rp, an, ap, an);

  ulbn_assert(d1 != 0);
  ulbn_assert(shift >= 0 && ulbn_cast_uint(shift) < ULBN_LIMB_BITS);
  rshift = ulbn_cast_int(ULBN_LIMB_BITS) - shift - 1;

  a2 = ulbn_cast_limb((ap[an - 1] >> rshift) >> 1);
  ai = ap[an - 2];
  a1 = ulbn_cast_limb((ap[an - 1] << shift) | ((ai >> rshift) >> 1));
  for(i = an - 2; i > 0; --i) {
    a0 = ulbn_cast_limb(ai << shift);
    ai = ap[i - 1];
    a0 |= ulbn_cast_limb((ai >> rshift) >> 1);
    _ulbn_udiv_3by2_(qp[i], a2, a1, a2, a1, a0, d1, d0, di);
  }

  a0 = ulbn_cast_limb(ai << shift);
  _ulbn_udiv_3by2_(qp[0], a2, a1, a2, a1, a0, d1, d0, di);
  rp[1] = ulbn_cast_limb(a2 >> shift);
  rp[0] = ulbn_cast_limb(((a2 << rshift) << 1) | (a1 >> shift));
}
/* qp[0:an-dn+1] = ap[0:an] // dp[0:dn], rp[0:dn] = ap[0:an] % dp[0:dn],
  ensuring `dp` is normalized and `di` is `ulbn_divinv2(dp[dn-1],dp[dn-2])` */
ULBN_INTERNAL void ulbn_divmod_inv(
  ulbn_limb_t* ul_restrict qp,                                       /* */
  ulbn_limb_t* ul_restrict rp, ulbn_usize_t rn, ulbn_limb_t a2,      /* */
  const ulbn_limb_t* ul_restrict dp, ulbn_usize_t dn, ulbn_limb_t di /* */
) {
  ulbn_limb_t a1, a0;
  ulbn_limb_t d1, d0;
  ulbn_limb_t q, cy, cy2;
  ulbn_usize_t i;

  d1 = dp[dn - 1];
  d0 = dp[dn - 2];
  ulbn_assert(dn >= 2);
  ulbn_assert(rn >= dn);
  ulbn_assert(d1 & ULBN_LIMB_SIGNBIT);

  ulbn_assert_overlap(qp, rn - dn + 1, rp, dn);
  ulbn_assert_overlap(qp, rn - dn + 1, dp, dn);
  ulbn_assert_overlap(rp, rn, dp, dn);

  i = rn - dn;
  do {
    a1 = rp[dn - 1 + i];
    if(ul_unlikely(a2 == d1 && a1 == d0)) {
      q = ULBN_LIMB_MAX;
      ulbn_submul1(rp + i, dp, dn, q);
      a2 = rp[dn - 1 + i];
    } else {
      a0 = rp[dn - 2 + i];
      _ulbn_udiv_3by2_(q, a2, a1, a2, a1, a0, d1, d0, di);

      cy = ulbn_submul1(rp + i, dp, dn - 2, q);
      cy2 = (a1 < cy);
      a1 -= cy;
      cy = (a2 < cy2);
      a2 -= cy2;
      rp[dn - 2 + i] = a1;

      if(ul_unlikely(cy != 0)) {
        a2 += ulbn_cast_limb(d1 + ulbn_addn(rp + i, rp + i, dp, dn - 1));
        --q;
      }
    }

    qp[i] = q;
  } while(i-- > 0);

  rp[dn - 1] = a2;
}

#define ULBN_DIVMOD_REC_THRESHOLD 256
#if ULBN_DIVMOD_REC_THRESHOLD < 2
  #error "ulbn: ulbn_divmod_rec_guard threshold must be at least 2"
#endif
#if ULBN_DIVMOD_REC_THRESHOLD <= ULBN_USIZE_MAX
ULBN_INTERNAL void ulbn_divmod_rec(
  const ulbn_alloc_t* alloc, ulbn_limb_t* ul_restrict tp, ulbn_limb_t* ul_restrict qp, /**/
  ulbn_limb_t* ul_restrict rp, ulbn_usize_t rn, ulbn_limb_t a2,                        /* */
  const ulbn_limb_t* ul_restrict dp, ulbn_usize_t dn, ulbn_limb_t di                   /* */
);
ULBN_PRIVATE void _ulbn_divmod_rec_step(
  const ulbn_alloc_t* alloc, ulbn_limb_t* ul_restrict tp, ulbn_limb_t* ul_restrict qp, /**/
  ulbn_limb_t* ul_restrict rp, ulbn_usize_t rn, ulbn_limb_t a2,                        /* */
  const ulbn_limb_t* ul_restrict dp, ulbn_usize_t dn, ulbn_limb_t di                   /* */
) {
  const ulbn_usize_t m = rn - dn, k = m >> 1, k2 = ulbn_cast_usize(k << 1);
  ulbn_limb_t q_tmp;

  ulbn_assert(rn >= dn);
  ulbn_assert(dp[dn - 1] & ULBN_LIMB_SIGNBIT);

  ulbn_assert_overlap(qp, rn - dn + 1, rp, dn);
  ulbn_assert_overlap(qp, rn - dn + 1, dp, dn);
  ulbn_assert_overlap(rp, rn, dp, dn);
  ulbn_assert(m < dn);
  ulbn_assert(k > 0);

  ulbn_divmod_rec(alloc, tp, qp + k, rp + k2, rn - k2, a2, dp + k, dn - k, di);
  ulbn_mul(alloc, tp, qp + k, m - k + 1, dp, k);
  a2 = ulbn_sub(rp + k, rp + k, dn, tp, m + 1);
  while(a2) {
    ulbn_sub1(qp + k, qp + k, m - k + 1, 1);
    a2 -= ulbn_add(rp + k, rp + k, dn, dp, dn);
  }

  if(memcmp(rp + k2, dp + k, (dn - k) * sizeof(ulbn_limb_t)) == 0) {
    ulbn_fill1(qp, k);
    ulbn_add(rp, rp, dn + k, dp, dn);
    ulbn_sub(rp + k, rp + k, dn, dp, dn);
    return;
  }

  q_tmp = qp[k];
  ulbn_divmod_rec(alloc, tp, qp, rp + k, dn, 0, dp + k, dn - k, di);
  ulbn_assert(qp[k] == 0);
  qp[k] = q_tmp;
  ulbn_mul(alloc, tp, qp, k, dp, k);
  a2 = ulbn_sub(rp, rp, dn, tp, k2);
  while(a2 != 0) {
    ulbn_sub1(qp, qp, k, 1);
    a2 -= ulbn_add(rp, rp, dn, dp, dn);
  }
}
/* `tp` must be able to hold `rn - dn + 1` limbs */
ULBN_INTERNAL void ulbn_divmod_rec(
  const ulbn_alloc_t* alloc, ulbn_limb_t* ul_restrict tp, ulbn_limb_t* ul_restrict qp, /**/
  ulbn_limb_t* ul_restrict rp, ulbn_usize_t rn, ulbn_limb_t a2,                        /* */
  const ulbn_limb_t* ul_restrict dp, ulbn_usize_t dn, ulbn_limb_t di                   /* */
) {
  const ulbn_usize_t dn_m1 = dn - 1;
  ulbn_usize_t m = rn - dn;
  ulbn_limb_t q_tmp;

  if(m <= ULBN_DIVMOD_REC_THRESHOLD || dn <= ULBN_DIVMOD_REC_THRESHOLD) {
    ulbn_divmod_inv(qp, rp, rn, a2, dp, dn, di);
    return;
  }

  m -= m % dn_m1;
  rp += m;
  qp += m;
  if(rn - m - dn <= ULBN_DIVMOD_REC_THRESHOLD)
    ulbn_divmod_inv(qp, rp, rn - m, a2, dp, dn, di);
  else
    _ulbn_divmod_rec_step(alloc, tp, qp, rp, rn - m, a2, dp, dn, di);

  while(m) {
    rp -= dn_m1;
    qp -= dn_m1;
    m -= dn_m1;

    q_tmp = qp[dn_m1];
    _ulbn_divmod_rec_step(alloc, tp, qp, rp, dn + dn_m1, 0, dp, dn, di);
    ulbn_assert(qp[dn_m1] == 0);
    qp[dn_m1] = q_tmp;
  }
}

ULBN_INTERNAL void ulbn_divmod_rec_guard(
  const ulbn_alloc_t* alloc, ulbn_limb_t* ul_restrict qp,            /**/
  ulbn_limb_t* ul_restrict rp, ulbn_usize_t rn, ulbn_limb_t a2,      /* */
  const ulbn_limb_t* ul_restrict dp, ulbn_usize_t dn, ulbn_limb_t di /* */
) {
  const ulbn_usize_t m = rn - dn;
  ulbn_limb_t* tp;

  if(m <= ULBN_DIVMOD_REC_THRESHOLD || dn <= ULBN_DIVMOD_REC_THRESHOLD) {
  fallback:
    ulbn_divmod_inv(qp, rp, rn, a2, dp, dn, di);
    return;
  }

  tp = ulbn_allocT(ulbn_limb_t, alloc, m + 1);
  ULBN_DO_IF_ALLOC_FAILED(tp, goto fallback;);
  ulbn_divmod_rec(alloc, tp, qp, rp, rn, a2, dp, dn, di);
  ulbn_deallocT(ulbn_limb_t, alloc, tp, m + 1);
}
#else /* ULBN_DIVMOD_REC_THRESHOLD > ULBN_USIZE_MAX */
ULBN_INTERNAL void ulbn_divmod_rec_guard(
  const ulbn_alloc_t* alloc, ulbn_limb_t* ul_restrict qp,            /**/
  ulbn_limb_t* ul_restrict rp, ulbn_usize_t rn, ulbn_limb_t a2,      /* */
  const ulbn_limb_t* ul_restrict dp, ulbn_usize_t dn, ulbn_limb_t di /* */
) {
  (void)alloc;
  ulbn_divmod_inv(qp, rp, rn, a2, dp, dn, di);
}
#endif

/* `rp` is not NULL, won't return `ULBN_ERR_INEXACT` */
ULBN_INTERNAL int ulbn_divmod1(
  const ulbn_alloc_t* alloc, ulbn_limb_t* qp, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t d        /* */
) {
  ulbn_limb_t* nqp = qp;
  int shift;

  ulbn_assert(rp != ul_nullptr);
  ulbn_assert(d != 0);
  shift = _ulbn_clz_(d);
  d <<= shift;

  if(qp == ul_nullptr) {
    nqp = ulbn_allocT(ulbn_limb_t, alloc, an);
    ULBN_RETURN_IF_ALLOC_FAILED(nqp, ULBN_ERR_NOMEM);
  }
  ulbn_divmod_inv1(nqp, rp, ap, an, d, ulbn_divinv1(d), shift);
  if(ul_unlikely(nqp != qp))
    ulbn_deallocT(ulbn_limb_t, alloc, nqp, an);
  return 0;
}

ULBN_PRIVATE int _ulbn_divmod_large(
  const ulbn_alloc_t* alloc, ulbn_limb_t* qp, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,                      /* */
  const ulbn_limb_t* dp, ulbn_usize_t dn, int shift            /* */
) {
  ulbn_limb_t a2 = 0;
  ulbn_limb_t *nrp = rp, *nqp = qp;
  ulbn_limb_t* tdp = ul_nullptr;
  int err;

  ulbn_assert(dn > 2);

  /* Ensure `dp` is independent and normalized */
  if(shift != 0) {
    tdp = ulbn_allocT(ulbn_limb_t, alloc, dn);
    ULBN_DO_IF_ALLOC_FAILED(tdp, {
      err = ULBN_ERR_NOMEM;
      goto cleanup;
    });
    ulbn_shl(tdp, dp, dn, shift);
    dp = tdp;
  } else if(ul_unlikely(dp == qp) || ul_unlikely(dp == ap) || ul_unlikely(dp == rp)) {
    tdp = ulbn_allocT(ulbn_limb_t, alloc, dn);
    ULBN_DO_IF_ALLOC_FAILED(tdp, {
      err = ULBN_ERR_NOMEM;
      goto cleanup;
    });
    ulbn_copy(tdp, dp, dn);
    dp = tdp;
  }

  /* check if the remainder can be calculated in place */
  if(ap != rp) {
    nrp = ulbn_allocT(ulbn_limb_t, alloc, an);
    ULBN_DO_IF_ALLOC_FAILED(nrp, {
      err = ULBN_ERR_NOMEM;
      goto cleanup;
    });
  }
  ulbn_assert(nrp != ul_nullptr);
  if(shift)
    a2 = ulbn_shl(nrp, ap, an, shift);
  else if(ap != rp)
    ulbn_copy(nrp, ap, an);

  if(qp == ul_nullptr) {
    nqp = ulbn_allocT(ulbn_limb_t, alloc, an - dn + 1);
    ULBN_DO_IF_ALLOC_FAILED(nqp, {
      err = ULBN_ERR_NOMEM;
      goto cleanup;
    });
  }

  ulbn_divmod_rec_guard(alloc, nqp, nrp, an, a2, dp, dn, ulbn_divinv2(dp[dn - 1], dp[dn - 2]));

  if(rp != ul_nullptr) {
    if(shift != 0)
      ulbn_shr(rp, nrp, dn, shift);
    else
      ulbn_maycopy(rp, nrp, dn);
    err = 0;
  } else
    err = ulbn_rnorm(nrp, dn) == 0 ? 0 : ULBN_ERR_INEXACT;

cleanup:
  if(nrp != rp)
    ulbn_deallocT(ulbn_limb_t, alloc, nrp, an);
  if(tdp)
    ulbn_deallocT(ulbn_limb_t, alloc, tdp, dn);
  if(nqp != qp)
    ulbn_deallocT(ulbn_limb_t, alloc, nqp, an - dn + 1);
  return err;
}
/**
 * qp[0:an-dn+1] = ap[0:an] // dp[0:dn], rp[0:dn] = ap[0:an] % dp[0:dn].
 *
 * @note `qp` and `rp` can be NULL.
 * @note This function will use buffer in `alloc` to normalize `dp` and compute `qp` and `rp`.
 *
 * @return `ULBN_ERR_NOMEM` if memory is insufficient;
 * @return `ULBN_ERR_INEXACT` if `rp` is NULL and remainder is not 0;
 * @return `0` otherwise.
 */
ULBN_INTERNAL int ulbn_divmod_guard(
  const ulbn_alloc_t* alloc, ulbn_limb_t* qp, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,                      /* */
  const ulbn_limb_t* dp, ulbn_usize_t dn                       /* */
) {
  ulbn_limb_t rp_buf[2] = { 0, 0 };
  const int shift = _ulbn_clz_(dp[dn - 1]);
  ulbn_limb_t rem = 0;

  ulbn_assert(an >= dn && dn >= 1);
  ulbn_assert(dp[dn - 1] != 0);
  ulbn_assert(ap != ul_nullptr && dp != ul_nullptr);

  /* Ensure qp, rp, ap, and dp are either equal to each other, do not overlap, or are NULL */
  ulbn_assert_same_or_not_overlap(ap, an, dp, dn);
  ulbn_assert_same_or_not_overlap(rp, dn, ap, an);
  ulbn_assert_same_or_not_overlap(rp, dn, dp, dn);
  ulbn_assert_same_or_not_overlap(qp, an - dn + 1, ap, an);
  ulbn_assert_same_or_not_overlap(qp, an - dn + 1, dp, dn);
  ulbn_assert_same_or_not_overlap(qp, an - dn + 1, rp, dn);

  if(ul_likely(dn <= 2)) {
    const ulbn_limb_t d0 = ulbn_cast_limb(dp[0] << shift);
    ulbn_limb_t* nqp = qp;

    /* `qp` can be equal to `ap`, but `qp` cannot be NULL */
    if(qp == ul_nullptr) {
      nqp = ulbn_allocT(ulbn_limb_t, alloc, an);
      ULBN_RETURN_IF_ALLOC_FAILED(nqp, ULBN_ERR_NOMEM);
    }
    if(dn == 1)
      ulbn_divmod_inv1(nqp, rp_buf, ap, an, d0, ulbn_divinv1(d0), shift);
    else {
      const ulbn_limb_t d1 =
        ulbn_cast_limb((dp[1] << shift) | (dp[0] >> (ulbn_cast_int(ULBN_LIMB_BITS) - shift - 1) >> 1));
      ulbn_divmod_inv2(nqp, rp_buf, ap, an, d1, d0, ulbn_divinv2(d1, d0), shift);
    }

    if(rp) {
      rp[0] = rp_buf[0];
      if(dn == 2)
        rp[1] = rp_buf[1];
    } else
      rem = ulbn_cast_limb(rp_buf[0] | rp_buf[1]);
    if(qp != nqp)
      ulbn_deallocT(ulbn_limb_t, alloc, nqp, an);
    return rem ? ULBN_ERR_INEXACT : 0;
  }

  return _ulbn_divmod_large(alloc, qp, rp, ap, an, dp, dn, shift);
}

/*************************
 * <ulbn> Short Division *
 *************************/

#define _ULBN_SHORTDIV_N 15
static ulbn_limb_t _ulbn_shortdiv_d[_ULBN_SHORTDIV_N + 1];
static int _ulbn_shortdiv_shift[_ULBN_SHORTDIV_N + 1];
static ulbn_limb_t _ulbn_shortdiv_di[_ULBN_SHORTDIV_N + 1];
ULBN_PRIVATE void _ulbn_startup_shortdiv(void) {
  ulbn_limb_t i, d;
  int shift;
  for(i = 2; i <= _ULBN_SHORTDIV_N; ++i) {
    shift = _ulbn_clz_(i);
    ulbn_assert(0 < shift && ulbn_cast_uint(shift) < ULBN_LIMB_BITS);
    d = ulbn_cast_limb(i << shift);
    _ulbn_shortdiv_d[i] = d;
    _ulbn_shortdiv_shift[i] = shift;
    _ulbn_shortdiv_di[i] = ulbn_divinv1(d);
  }
}

ULBN_INTERNAL void ulbn_shortdiv(ulbn_limb_t* qp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t d) {
  static ulbn_limb_t DIV_R;
  ulbn_assert(d >= 2 && d <= _ULBN_SHORTDIV_N);
  ulbn_divmod_inv1(qp, &DIV_R, ap, an, _ulbn_shortdiv_d[d], _ulbn_shortdiv_di[d], _ulbn_shortdiv_shift[d]);
}
#define ulbn_shortdiv1(q, r, a, d)   \
  do {                               \
    (r) = ulbn_cast_limb((a) % (d)); \
    (q) = ulbn_cast_limb((a) / (d)); \
  } while(0)

/****************
 * <ulbn> Round *
 ****************/

/* return ap[0:an]*2 <=> mp[0:mn] */
ULBN_INTERNAL int ulbn_check_round(const ulbn_limb_t* ap, ulbn_usize_t an, const ulbn_limb_t* mp, ulbn_usize_t mn) {
  return -ulbn_cmpshl(mp, mn, ap, an, 1);
}

/* adjust half `round_mode` to normal */
ULBN_INTERNAL enum ULBN_ROUND_ENUM ulbn_adjust_half_round(enum ULBN_ROUND_ENUM round_mode, int is_even) {
  if(round_mode == ULBN_ROUND_HALF_DOWN)
    return ULBN_ROUND_DOWN;
  else if(round_mode == ULBN_ROUND_HALF_UP)
    return ULBN_ROUND_UP;
  else if(round_mode == ULBN_ROUND_HALF_ODD)
    return !is_even ? ULBN_ROUND_DOWN : ULBN_ROUND_UP;
  else /* if(round_mode == ULBN_ROUND_HALF_EVEN) */ {
    ulbn_assert(round_mode == ULBN_ROUND_HALF_EVEN);
    return is_even ? ULBN_ROUND_DOWN : ULBN_ROUND_UP;
  }
}
ULBN_INTERNAL int ulbn_round_direction(enum ULBN_ROUND_ENUM round_mode, int positive) {
  ulbn_assert(positive == 0 || positive == 1);
  if(round_mode == ULBN_ROUND_DOWN)
    return 0;
  else if(round_mode == ULBN_ROUND_UP)
    return positive ? 1 : -1;
  else if(round_mode == ULBN_ROUND_FLOOR)
    return positive - 1;
  else /* if(round_mode == ULBN_ROUND_CEILING) */{
    ulbn_assert(round_mode == ULBN_ROUND_CEILING);
    return positive;
  }
}

/*********************
 * <ulbn> Set string *
 *********************/

static const char _ulbn_lower_table[] = "0123456789abcdefghijklmnopqrstuvwxyz";
static const char _ulbn_upper_table[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
static unsigned char _ulbn_setstr_table[256];
#if CHAR_BIT <= 8
  #define _ulbn_setstr_val(ch) (_ulbn_setstr_table[ul_static_cast(unsigned char, (ch))])
#else
  #define _ulbn_setstr_val(ch) \
    (ul_static_cast(unsigned char, (ch)) > 0xFF ? 0xFF : _ulbn_setstr_table[ul_static_cast(unsigned char, (ch))])
#endif
ULBN_PRIVATE void _ulbn_startup_setstr(void) {
  unsigned i;
  memset(_ulbn_setstr_table, 0xFF, sizeof(_ulbn_setstr_table));
  for(i = 0; i < 10; ++i) {
    ulbn_assert(ulbn_cast_uint(_ulbn_lower_table[i]) <= 0xFF);
    _ulbn_setstr_table[ul_static_cast(unsigned char, _ulbn_lower_table[i])] = ul_static_cast(unsigned char, i);
  }
  for(; i <= 36; ++i) {
    ulbn_assert(ulbn_cast_uint(_ulbn_lower_table[i]) <= 0xFF && ulbn_cast_uint(_ulbn_upper_table[i]) <= 0xFF);
    _ulbn_setstr_table[ul_static_cast(unsigned char, _ulbn_lower_table[i])] = ul_static_cast(unsigned char, i);
    _ulbn_setstr_table[ul_static_cast(unsigned char, _ulbn_upper_table[i])] = ul_static_cast(unsigned char, i);
  }
}

/* 0: invalid, 1: inf, 2: nan, 3: nan (with char_sequence) */
ULBN_INTERNAL int ulbn_setstr_infinite(const char** p_str, size_t len) {
  static const char nfinity_lower[] = "nfinity";
  static const char nfinity_upper[] = "NFINITY";
  static const char an_lower[] = "an";
  static const char an_upper[] = "AN";

  const char* str = *p_str;
  unsigned i;
  int ret = 0;

  ulbn_assert(len != 0);
  --len;
  if(*str == 'I' || *str == 'i') { /* inf */
    ++str;
    if(len < 2)
      goto done;
    for(i = 0; i < 2; ++i)
      if(str[i] != nfinity_lower[i] && str[i] != nfinity_upper[i])
        goto done;
    ret = 1;
    str += 2;
    if(len < 7)
      goto done;

    for(i = 0; i < 5; ++i)
      if(str[i] != nfinity_lower[i + 2] && str[i] != nfinity_upper[i + 2])
        goto done;
    str += 5;
  } else if(*str == 'n' || *str == 'N') { /* nan */
    ++str;
    if(len < 2)
      goto done;
    for(i = 0; i < 2; ++i)
      if(str[i] != an_lower[i] && str[i] != an_upper[i])
        goto done;
    ret = 2;
    str += 2;
    len -= 2;
    if(ul_likely(len == 0))
      goto done;
    
    if(str[0] != '(') goto done;
    {
      const char* str2 = str + 1;
      /* parse `char_sequence` */
      for(--len; len != 0; --len) {
        if(*str2 == ')') {
          ret = 3;
          str = str2 + 1;
          goto done;
        }
        if(!(_ulbn_setstr_val(*str2) < 36 || *str2 == '_'))
          break;
        ++str2;
      }
    }
  }

done:
  *p_str = str;
  return ret;
}

/**************************
 * <ulbn> Base conversion *
 **************************/

#if 0
ul_unused ULBN_INTERNAL void ulbn_dumplimb(FILE* fp, ulbn_limb_t l) {
  size_t j = sizeof(l) * CHAR_BIT / 4;
  while(j--)
    fputc(_ulbn_upper_table[(l >> (j << 2)) & 0xF], fp);
}
ul_unused ULBN_INTERNAL void ulbn_dump(FILE* fp, const ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_usize_t i;
  for(i = n; i > 0; --i) {
    ulbn_dumplimb(fp, p[i - 1]);
    if(i != 1)
      fputc('_', stdout);
  }
}
ul_unused ULBN_INTERNAL void ulbn_dprint(FILE* fp, const char* prefix, const ulbn_limb_t* p, ulbn_usize_t n) {
  if(prefix)
    fputs(prefix, fp);
  ulbn_dump(fp, p, n);
  fputc('\n', fp);
}
#endif

ULBN_PRIVATE int _ulbn_write0(ulbn_printer_t* printer, void* opaque, size_t len) {
  static const char ONLY_ZERO[16 + 1] = "0000000000000000";
  while(len > 16) {
    if(ul_unlikely(printer(opaque, ONLY_ZERO, 16)))
      return ULBN_ERR_EXTERNAL;
    len -= 16;
  }
  if(ul_unlikely(printer(opaque, ONLY_ZERO, len)))
    return ULBN_ERR_EXTERNAL;
  return 0;
}

static unsigned _ulbn_baseconv_pow[37];   /* the maximum power to make `b` <= ULBN_LIMB_MAX */
static int _ulbn_baseconv_shift[37];      /* = _ulbn_ctz_(b) */
static ulbn_limb_t _ulbn_baseconv_b[37];  /* = base**base_pow */
static ulbn_limb_t _ulbn_baseconv_bi[37]; /* _ulbn_divinv1(b<<shift) */
ULBN_PRIVATE void _ulbn_startup_baseconv(void) {
  ulbn_limb_t b_guard;
  ulbn_limb_t base;
  unsigned base_pow;
  ulbn_limb_t b;

  for(base = 2; base <= 36; ++base) {
    b_guard = ulbn_cast_limb(ULBN_LIMB_MAX / base);
    base_pow = 1;
    for(b = base; b <= b_guard; b *= base)
      ++base_pow;

    _ulbn_baseconv_pow[base] = base_pow;
    _ulbn_baseconv_shift[base] = _ulbn_clz_(b);
    _ulbn_baseconv_b[base] = b;
    b <<= _ulbn_baseconv_shift[base];
    _ulbn_baseconv_bi[base] = ulbn_divinv1(b);
  }
}

ULBN_INTERNAL int ulbn_conv2print_generic(
  const ulbn_alloc_t* alloc, size_t desire_len,        /* */
  ulbn_printer_t* printer, void* opaque,               /* */
  const ulbn_limb_t* ap, const ulbn_usize_t an,        /* */
  const char* ul_restrict char_table, ulbn_limb_t base /* */
) {
  ulbn_limb_t* cp;
  size_t ccap = 0, ci = 0;

  ulbn_limb_t* tp;
  ulbn_usize_t tn = an;

  int err = ULBN_ERR_NOMEM;
  char buf[ULBN_LIMB_BITS];
  char *pbuf, *const buf_end = buf + ULBN_LIMB_BITS;
  ulbn_limb_t c;

  ulbn_limb_t short_r;
  const ulbn_limb_t b = ((void)ulbn_check_startup(), _ulbn_baseconv_b[base]);
  const ulbn_limb_t bi = _ulbn_baseconv_bi[base];
  const int b_shift = _ulbn_baseconv_shift[base];
  const unsigned base_pow = _ulbn_baseconv_pow[base];

  ulbn_assert(an > 0);

  tp = ulbn_allocT(ulbn_limb_t, alloc, an);
  ULBN_DO_IF_ALLOC_FAILED(tp, return err;);
  cp = ulbn_allocT(ulbn_limb_t, alloc, an);
  ULBN_DO_IF_ALLOC_FAILED(cp, goto cleanup;);
  ccap = an;

  ulbn_copy(tp, ap, tn);
  do {
    if(ul_unlikely(ci >= ccap)) {
      ulbn_limb_t* new_cp;
      size_t new_ccap;
      new_ccap = ccap + (ccap >> 1) + 1u;
      if(ul_unlikely(new_ccap < ccap || new_ccap > ULBN_ALLOC_LIMIT))
        goto cleanup;
      new_cp = ulbn_reallocT(ulbn_limb_t, alloc, cp, ccap, new_ccap);
      ULBN_DO_IF_ALLOC_COND(new_cp == ul_nullptr, goto cleanup;);
      cp = new_cp;
      ccap = new_ccap;
    }

    ulbn_divmod_inv1(tp, cp + (ci++), tp, tn, ulbn_cast_limb(b << b_shift), bi, b_shift);
    if(ul_likely(tp[tn - 1] == 0))
      --tn;
  } while(tn > 0);

  err = ULBN_ERR_EXTERNAL;
  c = cp[--ci];
  for(pbuf = buf_end; c;) {
    ulbn_shortdiv1(c, short_r, c, base);
    *--pbuf = char_table[short_r];
  }
  if(desire_len / base_pow >= ci) {
    desire_len -= base_pow * ci;
    if(desire_len > ul_static_cast(size_t, buf_end - pbuf)) {
      desire_len -= ul_static_cast(size_t, buf_end - pbuf);
      err = _ulbn_write0(printer, opaque, desire_len);
      if(ul_unlikely(err))
        goto cleanup;
    }
  }
  if(ul_unlikely(printer(opaque, pbuf, ul_static_cast(size_t, buf_end - pbuf))))
    goto cleanup;

  while(ci > 0) {
    c = cp[--ci];
    for(pbuf = buf + base_pow; c;) {
      ulbn_shortdiv1(c, short_r, c, base);
      *--pbuf = char_table[short_r];
    }
    memset(buf, char_table[0], ul_static_cast(size_t, pbuf - buf));
    if(ul_unlikely(printer(opaque, buf, base_pow)))
      goto cleanup;
  }
  err = 0;

cleanup:
  ulbn_deallocT(ulbn_limb_t, alloc, cp, ccap);
  ulbn_deallocT(ulbn_limb_t, alloc, tp, an);
  return err;
}

#define ULBN_CONV2PRINT_GENERIC_THRESHOLD 2048
#if ULBN_CONV2PRINT_GENERIC_THRESHOLD < ULBN_USIZE_MAX
/* Estimate `ceil(bits * log2(base))` (when `inv=0`) or `ceil(bits / log2(base))` (when `inv=1`) */
ULBN_INTERNAL ulbn_ulong_t ulbn_estimate_conv2_size(ulbn_ulong_t bits, int base, int inv) {
    /* Store log2(base) as a fraction, 1/log2(base0) is smaller than exact value */
  #if ULBN_LIMB_MAX >= 0xFFFFFFFF
  static const ulbn_limb_t table_log2[][2] = {
    /* clang-format off */
    { 0x1, 0x1 },              { 0x5C2C498, 0x92173AF },  { 0x1, 0x2 },              { 0x630FC6B, 0xE60393A },
    { 0x5C2C498, 0xEE43847 },  { 0x1A90993, 0x4A93B18 },  { 0x1, 0x3 },              { 0x2E1624C, 0x92173AF },
    { 0x2A30F19, 0x8C27F54 },  { 0x587A443, 0x132150C3 }, { 0x28F211F, 0x92C9D40 },  { 0x1F11ECF, 0x72F905A },
    { 0x1A90993, 0x65244AB },  { 0x4CB667E, 0x12BB51A5 }, { 0x1, 0x4 },              { 0x440389A, 0x11601035 },
    { 0x333A379, 0xD59D4D3 },  { 0x4F22C47, 0x15029C67 }, { 0x478CB8B, 0x1353B8D9 }, { 0x4A8E34B, 0x14778ACA },
    { 0x42C29E7, 0x129B6724 }, { 0x2541D3B, 0xA888F37 },  { 0x333A379, 0xEAE0318 },  { 0x46A05C2, 0x147FA975 },
    { 0x365C0D6, 0xFF83909 },  { 0x2FCCD5B, 0xE348C5C },  { 0x2D99FD3, 0xDB39023 },  { 0xE2E5200, 0x44E406EF },
    { 0x4CB667E, 0x1786B823 }, { 0x376B249, 0x1128DE40 }, { 0x1, 0x5 },              { 0x2D11821, 0xE357BCE },
    { 0x440389A, 0x15A048CF }, { 0x303F25F, 0xF77888E },  { 0x2E1624C, 0xEE43847 }, /* clang-format on */
  };
  #elif ULBN_LIMB_MAX >= 0xFFFF
  static const ulbn_limb_t table_log2[][2] = {
    { 1, 1 },        { 15601, 24727 }, { 1, 2 },         { 21306, 49471 }, { 15601, 40328 }, { 2964, 8321 },
    { 1, 3 },        { 15601, 49454 }, { 8651, 28738 },  { 4856, 16799 },  { 15601, 55929 }, { 5458, 20197 },
    { 2964, 11285 }, { 15659, 61178 }, { 1, 4 },         { 12451, 50893 }, { 15601, 65055 }, { 11701, 49705 },
    { 8651, 37389 }, { 13433, 59002 }, { 4856, 21655 },  { 5963, 26974 },  { 14271, 65432 }, { 10653, 49471 },
    { 5458, 25655 }, { 10179, 48400 }, { 2964, 14249 },  { 10738, 52165 }, { 11610, 56969 }, { 10676, 52891 },
    { 1, 5 },        { 10159, 51246 }, { 12451, 63344 }, { 3473, 17814 },  { 7468, 38609 },
  };
  #else
  static const ulbn_limb_t table_log2[][2] = {
    { 1, 1 },    { 147, 233 }, { 1, 2 },    { 59, 137 }, { 94, 243 }, { 26, 73 },  { 1, 3 },
    { 47, 149 }, { 59, 196 },  { 37, 128 }, { 41, 147 }, { 67, 248 }, { 26, 99 },  { 43, 168 },
    { 1, 4 },    { 57, 233 },  { 47, 196 }, { 4, 17 },   { 31, 134 }, { 28, 123 }, { 37, 165 },
    { 21, 95 },  { 41, 188 },  { 45, 209 }, { 47, 221 }, { 49, 233 }, { 26, 125 }, { 50, 243 },
    { 43, 211 }, { 22, 109 },  { 1, 5 },    { 45, 227 }, { 34, 173 }, { 23, 118 }, { 47, 243 }, /* clang-format off */
    /* clang-format on */
  };
  #endif
  static ulbn_limb_t _ULBN_SHORT_DIV_R; /* write-only variable */

  ulbn_limb_t buf[_ULBN_ULONG_LIMB_LEN + 1];
  ulbn_usize_t len;
  ulbn_limb_t d;
  int shift;

  ulbn_assert(2 <= base && base <= 36);
  ulbn_assert(inv == 0 || inv == 1);

  len = ulbn_set_ulong(buf, bits);
  buf[len] = ulbn_mul1(buf, buf, len, table_log2[base - 2][inv]);
  len += (buf[len] != 0);
  if(len) {
    d = table_log2[base - 2][!inv];
    shift = _ulbn_clz_(d);
    d <<= shift;
    ulbn_divmod_inv1(buf, &_ULBN_SHORT_DIV_R, buf, len, d, ulbn_divinv1(d), shift);
    len -= (buf[len - 1] == 0);
  }

  if(len == 0)
    return 0;

  #if ULBN_ULONG_MAX <= ULBN_LIMB_MAX
    #if ULBN_ULONG_MAX < ULBN_LIMB_MAX
  if(ul_unlikely(buf[0] > ULBN_ULONG_MAX))
    return ULBN_ULONG_MAX;
    #endif
  return ulbn_cast_ulong(buf[0]);
  #else
  do {
    ulbn_ulong_t ret = 0;
    if(ul_unlikely(ulbn_bit_width(buf, len) > ULBN_ULONG_BITS))
      return ULBN_ULONG_MAX;
    do {
      ret <<= ULBN_LIMB_BITS - 1;
      ret <<= 1;
      ret |= buf[--len];
    } while(len > 0);
    return ret;
  } while(0);
  #endif
}
#endif /* ULBN_CONV2PRINT_GENERIC_THRESHOLD < ULBN_USIZE_MAX */


ULBN_PRIVATE int _ulbn_fileprinter(void* file, const char* buf, size_t len) {
  return fwrite(buf, 1, len, ul_reinterpret_cast(FILE*, file)) != len;
}

typedef struct _ulbn_strprinter_t {
  char* data;
  size_t len;
  size_t cap;
  ulbn_alloc_func_t* alloc;
  void* alloc_opaque;
} _ulbn_strprinter_t;
ULBN_PRIVATE int _ulbn_strprinter(void* opaque, const char* str, size_t len) {
  _ulbn_strprinter_t* printer = ul_reinterpret_cast(_ulbn_strprinter_t*, opaque);
  if(ul_unlikely(printer->len > _ULBN_SIZET_MAX - len))
    return -1;
  if(ul_unlikely(printer->len + len > printer->cap)) {
    size_t new_cap = printer->cap + (printer->cap >> 1);
    char* new_data;
    if(ul_unlikely(new_cap < printer->len + len))
      new_cap = printer->len + len;
    new_data = ul_reinterpret_cast(char*, printer->alloc(printer->alloc_opaque, printer->data, printer->cap, new_cap));
    ULBN_RETURN_IF_ALLOC_FAILED(new_data, -1);
    printer->data = new_data;
    printer->cap = new_cap;
  }
  memcpy(printer->data + printer->len, str, len);
  printer->len += len;
  return 0;
}

/****************************
 * <ulbn> Bitwise operation *
 ****************************/

ULBN_INTERNAL void ulbn_and_nocy(
  ulbn_limb_t* rp, const ulbn_limb_t* ap, const ulbn_limb_t* bp, ulbn_limb_t b_rev_mask, ulbn_usize_t n
) {
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
    rp[i] = ulbn_cast_limb(ap[i] & (bp[i] ^ b_rev_mask));
}
ULBN_INTERNAL void ulbn_or_nocy(
  ulbn_limb_t* rp, const ulbn_limb_t* ap, const ulbn_limb_t* bp, ulbn_limb_t b_rev_mask, ulbn_usize_t n
) {
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
    rp[i] = ulbn_cast_limb(ap[i] | (bp[i] ^ b_rev_mask));
}
ULBN_INTERNAL void ulbn_xor_nocy(
  ulbn_limb_t* rp, const ulbn_limb_t* ap, const ulbn_limb_t* bp, ulbn_limb_t b_rev_mask, ulbn_usize_t n
) {
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
    rp[i] = ulbn_cast_limb(ap[i] ^ bp[i] ^ b_rev_mask);
}

/* In 2's complement, rp[0:an] = ap[0:an] & bp[0:bn], return carry (do not write to rp[an]).
 The sign of `rp`, `ap`, and `bp` is given by the corresponding cy */
ULBN_INTERNAL ulbn_limb_t ulbn_and(
  ulbn_limb_t* rp, ulbn_limb_t r_cy,                        /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t a_cy, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn, ulbn_limb_t b_cy  /* */
) {
  ulbn_usize_t i;
  ulbn_limb_t al, bl, rl;
  const ulbn_limb_t a_mask = _ulbn_neg_(a_cy);
  const ulbn_limb_t b_mask = _ulbn_neg_(b_cy);
  const ulbn_limb_t r_mask = _ulbn_neg_(r_cy);
  ulbn_assert(an >= bn);
  ulbn_assert_forward_overlap(rp, an, ap, an);
  ulbn_assert_forward_overlap(rp, an, bp, bn);
  ulbn_assert(a_cy == 0 || a_cy == 1);
  ulbn_assert(b_cy == 0 || b_cy == 1);
  ulbn_assert(r_cy == (a_cy & b_cy));
  for(i = 0; i < bn; ++i) {
    al = ulbn_cast_limb((ap[i] ^ a_mask) + a_cy);
    a_cy = (al < a_cy);
    bl = ulbn_cast_limb((bp[i] ^ b_mask) + b_cy);
    b_cy = (bl < b_cy);
    rl = ulbn_cast_limb(((al & bl) ^ r_mask) + r_cy);
    rp[i] = rl;
    r_cy = (rl < r_cy);
  }
  ulbn_assert(b_cy == 0);
  for(; i < an; ++i) {
    al = ulbn_cast_limb((ap[i] ^ a_mask) + a_cy);
    a_cy = (al < a_cy);
    rl = ulbn_cast_limb(((al & b_mask) ^ r_mask) + r_cy);
    rp[i] = rl;
    r_cy = (rl < r_cy);
  }
  ulbn_assert(a_cy == 0);
  return r_cy;
}
/* In 2's complement, rp[0:an] = ap[0:an] | bp[0:bn], return carry (do not write to rp[an]).
  The sign of `rp`, `ap`, and `bp` is given by the corresponding cy */
ULBN_INTERNAL ulbn_limb_t ulbn_or(
  ulbn_limb_t* rp, ulbn_limb_t r_cy,                        /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t a_cy, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn, ulbn_limb_t b_cy  /* */
) {
  ulbn_usize_t i;
  ulbn_limb_t al, bl, rl;
  const ulbn_limb_t a_mask = _ulbn_neg_(a_cy);
  const ulbn_limb_t b_mask = _ulbn_neg_(b_cy);
  const ulbn_limb_t r_mask = _ulbn_neg_(r_cy);

  ulbn_assert(an >= bn);
  ulbn_assert_forward_overlap(rp, an, ap, an);
  ulbn_assert_forward_overlap(rp, an, bp, bn);
  ulbn_assert(a_cy == 0 || a_cy == 1);
  ulbn_assert(b_cy == 0 || b_cy == 1);
  ulbn_assert(r_cy == (a_cy | b_cy));

  for(i = 0; i < bn; ++i) {
    al = ulbn_cast_limb((ap[i] ^ a_mask) + a_cy);
    a_cy = (al < a_cy);
    bl = ulbn_cast_limb((bp[i] ^ b_mask) + b_cy);
    b_cy = (bl < b_cy);
    rl = ulbn_cast_limb(((al | bl) ^ r_mask) + r_cy);
    rp[i] = rl;
    r_cy = (rl < r_cy);
  }
  ulbn_assert(b_cy == 0);
  for(; i < an; ++i) {
    al = ulbn_cast_limb((ap[i] ^ a_mask) + a_cy);
    a_cy = (al < a_cy);
    rl = ulbn_cast_limb(((al | b_mask) ^ r_mask) + r_cy);
    rp[i] = rl;
    r_cy = (rl < r_cy);
  }
  ulbn_assert(a_cy == 0);
  return r_cy;
}
/* In 2's complement, rp[0:an] = ap[0:an] ^ bp[0:bn], return carry (do not write to rp[an]).
  The sign of `rp`, `ap`, and `bp` is given by the corresponding cy */
ULBN_INTERNAL ulbn_limb_t ulbn_xor(
  ulbn_limb_t* rp, ulbn_limb_t r_cy,                        /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t a_cy, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn, ulbn_limb_t b_cy  /* */
) {
  ulbn_usize_t i;
  ulbn_limb_t al, bl, rl;
  const ulbn_limb_t a_mask = _ulbn_neg_(a_cy);
  const ulbn_limb_t b_mask = _ulbn_neg_(b_cy);
  const ulbn_limb_t r_mask = _ulbn_neg_(r_cy);

  ulbn_assert(an >= bn);
  ulbn_assert_forward_overlap(rp, an, ap, an);
  ulbn_assert_forward_overlap(rp, an, bp, bn);
  ulbn_assert(a_cy == 0 || a_cy == 1);
  ulbn_assert(b_cy == 0 || b_cy == 1);
  ulbn_assert(r_cy == (a_cy ^ b_cy));

  for(i = 0; i < bn; ++i) {
    al = ulbn_cast_limb((ap[i] ^ a_mask) + a_cy);
    a_cy = (al < a_cy);
    bl = ulbn_cast_limb((bp[i] ^ b_mask) + b_cy);
    b_cy = (bl < b_cy);
    rl = ulbn_cast_limb(((al ^ bl) ^ r_mask) + r_cy);
    rp[i] = rl;
    r_cy = (rl < r_cy);
  }
  ulbn_assert(b_cy == 0);
  for(; i < an; ++i) {
    al = ulbn_cast_limb((ap[i] ^ a_mask) + a_cy);
    a_cy = (al < a_cy);
    rl = ulbn_cast_limb(((al ^ b_mask) ^ r_mask) + r_cy);
    rp[i] = rl;
    r_cy = (rl < r_cy);
  }
  ulbn_assert(a_cy == 0);
  return r_cy;
}
/* In 2's complement, rp[0:an] = cy ? -ap[0:an] : ap[0:an], return carry (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_neg(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t cy) {
  ulbn_usize_t i;
  const ulbn_limb_t mask = _ulbn_neg_(cy);

  ulbn_assert(cy == 0 || cy == 1);
  ulbn_assert_forward_overlap(rp, an, ap, an);

  for(i = 0; i < an; ++i)
    cy = ((rp[i] = ulbn_cast_limb((ap[i] ^ mask) + cy)) < cy);
  return cy;
}

/* Get (cy ? -p[0:n] : p[0:n])[k] in two's complement sense */
ULBN_INTERNAL ulbn_limb_t ulbn_limb(const ulbn_limb_t* p, ulbn_usize_t n, ulbn_limb_t cy, ulbn_usize_t k) {
  /* The method here is the same as `ulbn_neg_limb`, except positive numbers
   * need special handling */

  const ulbn_limb_t mask = _ulbn_neg_(cy);
  const ulbn_limb_t l = ulbn_cast_limb((k < n ? p[k] : 0) ^ mask);
  /* If it is a positive number, cy == 0, mask == 0, at this time i will be
    equal to k, and the loop will terminate directly */
  ulbn_usize_t i = ulbn_cast_usize(~mask) & k;

  ulbn_assert(cy == 0 || cy == 1);

  while(i < k && p[i] == 0)
    ++i;
  /* If `cy`==0, there is no carry 1, it is masked out */
  return ulbn_cast_limb(l + ((i == k) & cy));
}
/* return p[0:n] is power of 2 */
ULBN_INTERNAL int ulbn_is_2pow(const ulbn_limb_t* p, ulbn_usize_t n) {
  if(n == 0)
    return 1;
  return (p[n - 1] & (p[n - 1] - 1u)) == 0 && ulbn_is0(p, n - 1) != 0;
}


ul_static_assert(ULBN_LIMB_BITS < ULBN_LIMB_MAX, "ULBN_LIMB_BITS is too large");
ul_static_assert(ULBN_LIMB_BITS < INT_MAX, "ULBN_LIMB_BITS is too large");
#if ULBN_LIMB_MAX > ULBN_USIZE_MAX
ul_static_assert(
  ULBN_LIMB_MAX / ULBN_LIMB_BITS >= ULBN_USIZE_MAX,
  "if ULBN_LIMB_MAX > ULBN_USIZE_MAX, we must make sure that `ulbn_limb_t` is able to hold bits"
);
#endif
/* may return `ULBN_ERR_EXCEED_RANGE` */
ULBN_INTERNAL int ulbn_to_bit_info(const ulbn_limb_t* limb, ulbn_usize_t n, ulbn_usize_t* p_idx) {
#if ULBN_LIMB_MAX > ULBN_USIZE_MAX
  ulbn_limb_t q, r;
  if(ul_unlikely(n > 1))
    return ULBN_ERR_EXCEED_RANGE;
  if(n == 0) {
    *p_idx = 0;
    return 0;
  }
  q = limb[0] / ULBN_LIMB_BITS;
  r = limb[0] % ULBN_LIMB_BITS;
  if(ul_unlikely(q > ULBN_USIZE_MAX))
    return ULBN_ERR_EXCEED_RANGE;
  *p_idx = ulbn_cast_usize(q);
  return ulbn_cast_int(r);
#elif ULBN_LIMB_MAX == ULBN_USIZE_MAX
  ulbn_limb_t q, r;

  if(ul_unlikely(n > 2))
    return ULBN_ERR_EXCEED_RANGE;
  if(n == 0) {
    *p_idx = 0;
    return 0;
  }
  if(ul_unlikely(n == 2)) {
    if(ul_unlikely(limb[1] >= ULBN_LIMB_BITS))
      return ULBN_ERR_EXCEED_RANGE;
    _ulbn_udiv_(q, r, limb[1], limb[0], ULBN_LIMB_BITS);
  } else {
    q = limb[0] / ULBN_LIMB_BITS;
    r = limb[0] % ULBN_LIMB_BITS;
  }
  *p_idx = ulbn_cast_usize(q);
  return ulbn_cast_int(r);
#else
  ulbn_limb_t q[(sizeof(ulbn_usize_t) * CHAR_BIT + ULBN_LIMB_BITS - 1u) / ULBN_LIMB_BITS];
  ulbn_limb_t r[1];
  ulbn_usize_t qn;
  ulbn_usize_t idx = 0;

  static const ulbn_usize_t N_LIMIT = (sizeof(ulbn_usize_t) * CHAR_BIT + ULBN_LIMB_BITS - 1u) / ULBN_LIMB_BITS;
  const int shift = _ulbn_clz_(ulbn_cast_limb(ULBN_LIMB_BITS));
  const ulbn_limb_t d_norm = ulbn_cast_limb(ulbn_cast_limb(ULBN_LIMB_BITS) << shift);
  const ulbn_limb_t d_inv = ulbn_divinv1(d_norm);

  if(n > N_LIMIT)
    return ULBN_ERR_EXCEED_RANGE;
  if(n == 0) {
    *p_idx = 0;
    return 0;
  } else if(n == 1) { /* fast path */
    *p_idx = limb[0] / ULBN_LIMB_BITS;
    return ulbn_cast_int(limb[0] % ULBN_LIMB_BITS);
  }

  ulbn_divmod_inv1(q, r, limb, n, d_norm, d_inv, shift);
  qn = ulbn_rnorm(q, n);
  ulbn_assert(qn > 0);

  if(ul_unlikely(ulbn_bit_width(q, qn) > sizeof(ulbn_usize_t) * CHAR_BIT))
    return ULBN_ERR_EXCEED_RANGE;

  do {
    idx <<= sizeof(ulbn_limb_t) * CHAR_BIT;
    idx |= q[--qn];
  } while(qn);
  *p_idx = idx;
  return ulbn_cast_int(r[0]);
#endif
}

/**********************************
 * <ulbn> Random number generator *
 **********************************/

#if ULBN_CONF_USE_RAND
  #define ULBN_RAND_MULTIPLIER 0x321Du
  #define ULBN_RAND_INCREMENT 0xBB75u

/* generate 16 bits */
ULBN_INTERNAL unsigned ulbn_rand_gen(ulbn_rand_t* rng) {
  ulbn_rand_uint_t state;
  unsigned ret, shift;
  state = rng->state;
  rng->state = state * ULBN_RAND_MULTIPLIER + rng->inc;
  shift = ulbn_cast_uint(state >> 28);
  ret = ulbn_cast_uint((((state >> 10u) ^ state) >> 12u) & 0xFFFFu);
  ret = (ret >> shift) | (ret << ((0u - shift) & 15));
  return ret & 0xFFFFu;
}
ULBN_INTERNAL void ulbn_rand_adv(ulbn_rand_t* rng, ulbn_rand_uint_t steps) {
  const ulbn_rand_uint_t state = rng->state;
  ulbn_rand_uint_t cur_mult = ULBN_RAND_MULTIPLIER;
  ulbn_rand_uint_t cur_plus = rng->inc;
  ulbn_rand_uint_t acc_mult = 1u;
  ulbn_rand_uint_t acc_plus = 0u;
  while(steps) {
    if(steps & 1) {
      acc_mult *= cur_mult;
      acc_plus = acc_plus * cur_mult + cur_plus;
    }
    cur_plus = (cur_mult + 1u) * cur_plus;
    cur_mult *= cur_mult;
    steps >>= 1;
  }
  rng->state = state * acc_mult + acc_plus;
}

ULBN_PUBLIC size_t ulbn_rand_sizeof(void) {
  return sizeof(ulbn_rand_t);
}
ULBN_PUBLIC void ulbn_rand_init2(ulbn_rand_t* rng, ulbn_rand_uint_t seed) {
  rng->state = 0u;
  rng->inc = (ULBN_RAND_INCREMENT << 1u) | 1u;
  rng->state = rng->state * ULBN_RAND_MULTIPLIER + rng->inc;
  rng->state += seed;
  rng->state = rng->state * ULBN_RAND_MULTIPLIER + rng->inc;
}
ULBN_PUBLIC ulbn_rand_uint_t ulbn_rand_init(ulbn_rand_t* rng) {
  ulbn_rand_uint_t seed;
  seed = ul_static_cast(ulbn_rand_uint_t, ul_reinterpret_cast(size_t, &seed));
  seed ^= ul_static_cast(ulbn_rand_uint_t, time(ul_nullptr) << 16);
  seed ^= ul_static_cast(ulbn_rand_uint_t, clock());
  ulbn_rand_init2(rng, seed);
  return seed;
}

ULBN_INTERNAL ulbn_limb_t ulbn_rand0(ulbn_rand_t* rng) {
  #if ULBN_LIMB_MAX <= 0xFFFFu
  return ulbn_cast_limb(ulbn_rand_gen(rng));
  #elif ULBN_LIMB_MAX <= 0xFFFFFFFFu
  return ulbn_cast_limb((ulbn_cast_limb(ulbn_rand_gen(rng)) << 16u) | ulbn_rand_gen(rng));
  #elif _ULBN_IS_64BIT(ULBN_LIMB_MAX)
  const ulbn_limb_t vh = ulbn_cast_limb((ulbn_cast_limb(ulbn_rand_gen(rng)) << 16u) | ulbn_rand_gen(rng));
  const ulbn_limb_t vl = ulbn_cast_limb((ulbn_cast_limb(ulbn_rand_gen(rng)) << 16u) | ulbn_rand_gen(rng));
  return ulbn_cast_limb((vh << 32u) | vl);
  #else
  ulbn_limb_t v = 0;
  int bits = ulbn_cast_int(ULBN_LIMB_BITS);
  do {
    v = ulbn_cast_limb(((v) << 16u) | ulbn_rand_gen(rng));
    bits -= 16;
  } while(bits > 0);
  return v;
  #endif
}
ULBN_INTERNAL ulbn_limb_t ulbn_randx(ulbn_rand_t* rng, unsigned n) {
  ulbn_assert(n != 0 && n < ULBN_LIMB_BITS);
  return ulbn_cast_limb(ulbn_rand0(rng) & ulbn_cast_limb(ULBN_LIMB_SHL(1u, n) - 1u));
}

ULBN_PUBLIC ulbn_limb_t ulbn_rand_step(ulbn_rand_t* rng) {
  return ulbn_rand0(rng);
}
ULBN_PUBLIC void ulbn_rand_advance(ulbn_rand_t* rng, ulbn_rand_uint_t steps) {
  #if ULBN_LIMB_MAX <= 0xFFFFu
  #elif ULBN_LIMB_MAX <= 0xFFFFFFFFu
  steps <<= 1;
  steps &= 0xFFFFFFFFu;
  #elif _ULBN_IS_64BIT(ULBN_LIMB_MAX)
  steps <<= 2;
  steps &= 0xFFFFFFFFu;
  #else
  int bits = ulbn_cast_int(ULBN_LIMB_BITS) - 16;
  const ulbn_rand_uint_t delta = steps;
  for(; bits > 0; bits -= 16)
    steps += delta;
  steps &= 0xFFFFFFFFu;
  #endif
  ulbn_rand_adv(rng, steps);
}

ULBN_INTERNAL void ulbn_rand_multi(ulbn_rand_t* rng, ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
    p[i] = ulbn_rand0(rng);
}

ULBN_PUBLIC void ulbn_rand_fill(ulbn_rand_t* rng, void* dst, size_t n) {
  unsigned char* p = ul_reinterpret_cast(unsigned char*, dst);
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
  #if ULBN_LIMB_MAX == UCHAR_MAX
    p[i] = ul_static_cast(unsigned char, ulbn_rand0(rng));
  #else
    p[i] = ul_static_cast(unsigned char, ulbn_randx(rng, CHAR_BIT));
  #endif
}
#endif /* ULBN_CONF_USE_RAND */

/**********************
 * <ulbn> Square root *
 **********************/

#if ULBN_LIMB_MAX == 0xFFu || ULBN_LIMB_MAX == 0xFFFFu || ULBN_LIMB_MAX == 0xFFFFFFFFu || _ULBN_IS_64BIT(ULBN_LIMB_MAX)
/* 8/16/32/64 bit platform, use faster version */

/* Ensure v >= 2^{ULBN_LIMB_BITS-2} */
ULBN_PRIVATE ulbn_limb_t _ulbn_sqrt_(ulbn_limb_t* pr, ulbn_limb_t v) {
  static ul_constexpr const unsigned char _SQRT_TABLE[] = {
    128, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, /* sqrt(0x4000) ~ sqrt(0x4F00) */
    143, 144, 144, 145, 146, 147, 148, 149, 150, 150, 151, 152, 153, 154, 155, 155, /* sqrt(0x5000) ~ sqrt(0x5F00) */
    156, 157, 158, 159, 160, 160, 161, 162, 163, 163, 164, 165, 166, 167, 167, 168, /* sqrt(0x6000) ~ sqrt(0x6F00) */
    169, 170, 170, 171, 172, 173, 173, 174, 175, 176, 176, 177, 178, 178, 179, 180, /* sqrt(0x7000) ~ sqrt(0x7F00) */
    181, 181, 182, 183, 183, 184, 185, 185, 186, 187, 187, 188, 189, 189, 190, 191, /* sqrt(0x8000) ~ sqrt(0x8F00) */
    192, 192, 193, 193, 194, 195, 195, 196, 197, 197, 198, 199, 199, 200, 201, 201, /* sqrt(0x9000) ~ sqrt(0x9F00) */
    202, 203, 203, 204, 204, 205, 206, 206, 207, 208, 208, 209, 209, 210, 211, 211, /* sqrt(0xA000) ~ sqrt(0xAF00) */
    212, 212, 213, 214, 214, 215, 215, 216, 217, 217, 218, 218, 219, 219, 220, 221, /* sqrt(0xB000) ~ sqrt(0xBF00) */
    221, 222, 222, 223, 224, 224, 225, 225, 226, 226, 227, 227, 228, 229, 229, 230, /* sqrt(0xC000) ~ sqrt(0xCF00) */
    230, 231, 231, 232, 232, 233, 234, 234, 235, 235, 236, 236, 237, 237, 238, 238, /* sqrt(0xD000) ~ sqrt(0xDF00) */
    239, 240, 240, 241, 241, 242, 242, 243, 243, 244, 244, 245, 245, 246, 246, 247, /* sqrt(0xE000) ~ sqrt(0xEF00) */
    247, 248, 248, 249, 249, 250, 250, 251, 251, 252, 252, 253, 253, 254, 254, 255, /* sqrt(0xF000) ~ sqrt(0xFF00) */
  };

  #if ULBN_LIMB_MAX == 0xFF || ULBN_LIMB_MAX == 0xFFFF
  ulbn_limb_t s;
  ulbn_assert(v >> (ULBN_LIMB_BITS - 2) != 0);
  s = _SQRT_TABLE[(v >> (ULBN_LIMB_BITS - 8)) - 0x40u];
    #if ULBN_LIMB_MAX == 0xFF
  s >>= 4;
  v -= ulbn_cast_limb(s * s);
    #else
  v -= s * s;
  if(v > 2 * s) {
    v -= 2 * s + 1;
    ++s;
  }
    #endif
  *pr = v;
  return s;
  #else
  ulbn_limb_t s, s1, r, r1, num;
  ulbn_limb_t q, u;

  ulbn_assert(v >> (ULBN_LIMB_BITS - 2) != 0);

  s1 = _SQRT_TABLE[(v >> (ULBN_LIMB_BITS - 8)) - 0x40u];
  r1 = (v >> (ULBN_LIMB_BITS - 16)) - s1 * s1;
  if(r1 > 2 * s1) {
    r1 -= 2 * s1 + 1;
    ++s1;
  }

  num = (r1 << 8) | ((v >> (ULBN_LIMB_BITS - 32 + 8)) & 0xFFu);
  q = num / (s1 << 1);
  u = num % (s1 << 1);
  s = (s1 << 8) + q;
  r = (u << 8) | ((v >> (ULBN_LIMB_BITS - 32)) & 0xFFu);
  r -= q * q;
  if(r >= ULBN_LIMB_SIGNBIT) { /* (ulbn_slimb_t)r < 0 */
    --s;
    r += 2 * s + 1;
  }

    #if _ULBN_IS_64BIT(ULBN_LIMB_MAX)
  s1 = s;
  r1 = r;
  num = (r1 << 16) | ((v >> (ULBN_LIMB_BITS - 64 + 16)) & 0xFFFFu);
  q = num / (s1 << 1);
  u = num % (s1 << 1);
  s = (s1 << 16) + q;
  r = (u << 16) | ((v >> (ULBN_LIMB_BITS - 64)) & 0xFFFFu);
  r -= q * q;
  if(r >= ULBN_LIMB_SIGNBIT) { /* (ulbn_slimb_t)r < 0 */
    --s;
    r += 2 * s + 1;
  }
    #endif

  *pr = r;
  return s;
  #endif
}
#else
/* Ensure v != 0. Time complexity is at most O(log({ULBN_LIMB_BITS}))*/
ULBN_PRIVATE ulbn_limb_t _ulbn_sqrt_generic_(ulbn_limb_t v) {
  ulbn_limb_t x, y = 1;
  ulbn_assert(v != 0);
  x = ULBN_LIMB_SHL(1, (ULBN_LIMB_BITS - ulbn_cast_uint(_ulbn_clz_(v)) + 3) >> 1);
  /*
    Newton's method:
    f(x) = x^2 - v
    f'(x) = 2x
    x' = x - f(x)/f'(x) = x - (x^2 - v)/(2x) = (x + v/x)/2
  */
  while(x > y) {
    x = (x + y) >> 1;
    y = v / x;
  }
  return x;
}
ULBN_PRIVATE ulbn_limb_t _ulbn_sqrt_(ulbn_limb_t* pr, ulbn_limb_t v) {
  ulbn_limb_t r = _ulbn_sqrt_generic_(v);
  *pr = v - r * r;
  return r;
}
#endif
/* Ensuring v >= 2^{ULBN_LIMB_BITS-2} */
ULBN_PRIVATE ulbn_limb_t _ulbn_sqrtrem2(ulbn_limb_t a1, ulbn_limb_t a0, ulbn_limb_t* ps, ulbn_limb_t* prl) {
  ulbn_limb_t s, q, u;
  ulbn_limb_t numh, numl;
  ulbn_limb_t rh, rl;

  s = _ulbn_sqrt_(&numl, a1);
  numh = ULBN_HIGHPART(numl);
  numl = ulbn_cast_limb((numl << ULBN_LIMB_HALF_BITS) | ULBN_HIGHPART(a0));
  s <<= 1;
  _ulbn_udiv_(q, u, numh, numl, s);
  s = ulbn_cast_limb((s << (ULBN_LIMB_HALF_BITS - 1u)) + q);
  rh = ULBN_HIGHPART(u);
  rl = ulbn_cast_limb((u << ULBN_LIMB_HALF_BITS) | ULBN_LOWPART(a0));
  if(ul_unlikely(q >> ULBN_LIMB_HALF_BITS) != 0)
    --rh;
  else {
    q *= q;
    rh = ulbn_cast_limb(rh - (rl < q));
    rl -= q;
  }
  if(rh >= ULBN_LIMB_SIGNBIT) {
    --s;
    numh = ulbn_cast_limb(s >> (ULBN_LIMB_BITS - 1));
    numl = ulbn_cast_limb(ulbn_cast_limb(s << 1u) | 1u);
    _ulbn_add_(rh, rl, rh, rl, numh, numl);
  }
  *prl = rl;
  *ps = s;
  return rh;
}

/* Calculate sqrt(rp[0:2*n]), store the result in sp[0:n], and store the remainder in rp[0:n]
  (the high part is returned via the return value) */
/* `tp` is a buffer, its size should be at least (n//2+1) */
ULBN_INTERNAL ulbn_limb_t ulbn_sqrtrem(
  const ulbn_alloc_t* alloc, ulbn_limb_t* ul_restrict sp, /* */
  ulbn_limb_t* ul_restrict rp, ulbn_usize_t n,            /* */
  ulbn_limb_t* ul_restrict tp                             /* */
) {
  /*
    "Karatsuba Square Root" (P Zimmermann, 1999):

    function sqrtrem(a3 * B^3 + a2 * B^2 + a1 * B + a0) {
      [s', r'] = sqrtrem(a3 * B + a2)
      [q, u] = divmod(r' * B + a1, 2 * s')
      s = (s' * B + q)
      r = u * B + a0 - q * q
      if(r < 0) {
        r = r + 2 * s + 1
        s = s - 1
      }
      return [s, r];
    }
  */

  ulbn_limb_t rh, qh, ql;
  ulbn_limb_t cy;
  ulbn_usize_t nl, nh;

  ulbn_assert(n > 0);
  ulbn_assert_overlap(sp, n, rp, n << 1);
  ulbn_assert_overlap(tp, n - (n >> 1), rp, n << 1);
  ulbn_assert_overlap(tp, n - (n >> 1), sp, n);

  if(n == 1)
    return _ulbn_sqrtrem2(rp[1], rp[0], sp, rp);
  nl = n >> 1;
  nh = n - nl;
  qh = ulbn_sqrtrem(alloc, sp + nl, rp + (nl << 1), nh, tp);
  /* s' at `sp[nl:n]`, r' at `rp[nl+nl,nl+n]` */
  ulbn_assert(qh == 0 || qh == 1);

  /* s' is normalized, so instead of do (r' * B + a1) / (2 * s'), we now do (r' * B + a1) / s' */
  /* if `qh` is 1, we make r' = r' - s' */
  if(qh)
    ulbn_subn(rp + (nl << 1), rp + (nl << 1), sp + nl, nh);
  switch(nh) {
  case 1:
    ulbn_divmod_inv1(tp, rp + nl, rp + nl, n, sp[nl], ulbn_divinv1(sp[n - 1]), 0);
    break;
  case 2:
    ulbn_divmod_inv2(tp, rp + nl, rp + nl, n, sp[nl + 1], sp[nl], ulbn_divinv2(sp[nl + 1], sp[nl]), 0);
    break;
  default:
    ulbn_divmod_inv(tp, rp + nl, n, 0, sp + nl, nh, ulbn_divinv2(sp[n - 1], sp[n - 2]));
    break;
  }
  qh += tp[nl]; /* if `qh` is 1, we add B to q' */
  /* q /= 2, as we divide by s' before */
  /* if q is odd, we will fix r with u = u + s' */
  ql = ulbn_shr(sp, tp, nl, 1);
  sp[nl - 1] |= qh << (ULBN_LIMB_BITS - 1);
  qh >>= 1;
  ulbn_assert(qh == 0 || qh == 1);
  if(ql)
    rh = ulbn_addn(rp + nl, rp + nl, sp + nl, nh);
  else
    rh = 0;
  /* s = s' * B + q, `q` is calculated at sp[0:nl], so will need to add qh to s  */
  ulbn_add1(sp + nl, sp + nl, nh, qh);

  /* r = u * B + a0 - q * q */
  /* if qh == 1, q = B^nl, so we can take shortcuts */
  if(qh)
    cy = qh;
  else {
    ulbn_mul(alloc, rp + n, sp, nl, sp, nl);
    cy = ulbn_subn(rp, rp, rp + n, ulbn_cast_usize(nl << 1));
  }
  rh -= ulbn_sub1(rp + (nl << 1), rp + (nl << 1), ulbn_cast_usize(n - (nl << 1)), cy);
  /* `r` < 0 */
  if(rh >= ULBN_LIMB_SIGNBIT) {
    ulbn_sub1(sp, sp, n, 1);
    rh += ulbn_addmul1(rp, sp, n, 2);
    rh += ulbn_add1(rp, rp, n, 1);
  }
  return rh;
}
/* `sp` is NULL or able to hold (n//2+1), `rp` is NULL or able to hold (n+(n&1)) */
ULBN_INTERNAL int ulbn_sqrtrem_guard(
  const ulbn_alloc_t* alloc, ulbn_limb_t* sp, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an                       /* */
) {
  ulbn_limb_t *nrp = rp, *nsp = sp, *tp;
  ulbn_limb_t rh;
  int shift, shift2, err = ULBN_ERR_NOMEM;
  const unsigned odd = ulbn_cast_uint(an & 1u);
  const ulbn_usize_t nh = an - (an >> 1), nr = (an >> 1) + 1u;

  ulbn_assert(an > 0 && an < ULBN_USIZE_MAX);
  ulbn_assert(ap != ul_nullptr);
  ulbn_assert(ap[an - 1] != 0);
  ulbn_assert_same_or_not_overlap(sp, an - (an >> 1), ap, an);
  ulbn_assert_same_or_not_overlap(sp, an - (an >> 1), rp, an - (an >> 1));
  ulbn_assert_same_or_not_overlap(rp, an - (an >> 1), ap, an);

  shift = (_ulbn_clz_(ap[an - 1]) >> 1) << 1;
  shift2 = shift + ulbn_cast_int(odd ? ULBN_LIMB_BITS : 0u);
  if(ap == rp && odd == 0) {
    if(shift)
      ulbn_shl(rp, ap, an, shift);
  } else {
    nrp = ulbn_allocT(ulbn_limb_t, alloc, nh << 1);
    ULBN_DO_IF_ALLOC_FAILED(nrp, goto cleanup;);
    nrp[0] = 0;
    if(shift)
      ulbn_shl(nrp + odd, ap, an, shift);
    else
      ulbn_copy(nrp + odd, ap, an);
  }

  if(nsp == rp || sp == ul_nullptr) {
    nsp = ulbn_allocT(ulbn_limb_t, alloc, nh);
    ULBN_DO_IF_ALLOC_FAILED(nsp, goto cleanup;);
  }

  tp = ulbn_allocT(ulbn_limb_t, alloc, nr);
  ULBN_DO_IF_ALLOC_FAILED(tp, goto cleanup;);

  rh = ulbn_sqrtrem(alloc, nsp, nrp, nh, tp);
  err = 0;
  if(rp) {
    if(shift2) {
      ulbn_limb_t cr;
      cr = ulbn_cast_limb(nsp[0] & ulbn_cast_limb(ULBN_LIMB_SHL(1u, shift2 >> 1) - 1u));
      rh += ulbn_addmul1(nrp, nsp, nh, cr);
      rh += ulbn_addmul1(nrp, nsp, nh, cr);
      rh -= ulbn_sub1(nrp, nrp, nh, ulbn_cast_limb(cr * cr));
      rp[nr - 1] = ulbn_cast_limb(rh >> shift);
      if(nh > odd) {
        if(shift) {
          ulbn_shr(rp, nrp + odd, ulbn_cast_usize(nh - odd), shift);
          rp[nh - 1 - odd] |= rh << (ulbn_cast_int(ULBN_LIMB_BITS) - shift);
        } else
          ulbn_copy(rp, nrp + odd, ulbn_cast_usize(nh - odd));
      }
    } else {
      rp[nr - 1] = rh;
      ulbn_maycopy(rp, nrp, nh);
    }
  } else
    err = ulbn_rnorm(nrp, nh) == 0 ? 0 : ULBN_ERR_INEXACT;
  if(sp) {
    if(shift2)
      ulbn_shr(sp, nsp, nh, shift2 >> 1);
    else
      ulbn_maycopy(sp, nsp, nh);
  }

  ulbn_deallocT(ulbn_limb_t, alloc, tp, nr);
cleanup:
  if(nrp != rp)
    ulbn_deallocT(ulbn_limb_t, alloc, nrp, nh << 1);
  if(nsp != sp)
    ulbn_deallocT(ulbn_limb_t, alloc, nsp, nh);
  return err;
}

/**************
 * <ulbn> GCD *
 **************/

ULBN_PRIVATE ulbn_limb_t _ulbn_gcd_(ulbn_limb_t a, ulbn_limb_t b) {
  /**
   * Binary GCD algorithm:
   *
   * function gcd(a, b) {
   *   if(a == b) return a;
   *   if(a % 2 == 0)
   *     if(b % 2 == 0)
   *       return 2 * gcd(a/2, b/2);
   *     else
   *       return gcd(a/2, b);
   *   else
   *     if(b % 2 == 0)
   *       return gcd(a, b/2);
   *     else
   *       return gcd(|a - b|/2, min(a, b));
   * }
   */
  int shift = 0, a_shift, b_shift;
  ulbn_assert(a > 0 && b > 0);
  for(;;) {
    a_shift = _ulbn_ctz_(a);
    b_shift = _ulbn_ctz_(b);
    a >>= a_shift;
    b >>= b_shift;
    shift += _ulbn_min_(a_shift, b_shift);
    if(a == b)
      break;
    if(a > b)
      a -= b;
    else
      b -= a;
  }
  return ulbn_cast_limb(a << shift);
}
ULBN_INTERNAL ulbn_usize_t ulbn_gcd(
  ulbn_limb_t* ul_restrict ap, ulbn_usize_t an, /* */
  ulbn_limb_t* ul_restrict bp, ulbn_usize_t bn  /* */
) {
  ulbn_usize_t shl_idx = 0;
  int shl_shift = 0;
  int cmp;
  ulbn_usize_t a_idx, b_idx;
  int a_shift, b_shift;

  ulbn_assert_overlap(ap, an, bp, bn);
  ulbn_assert(an > 0 && bn > 0);

  for(;;) {
    if((an | bn) == 1) {
      ap[0] = _ulbn_gcd_(ap[0], bp[0]);
      break;
    }

    for(a_idx = 0; ap[a_idx] == 0; ++a_idx) { }
    a_shift = _ulbn_ctz_(ap[a_idx]);
    for(b_idx = 0; bp[b_idx] == 0; ++b_idx) { }
    b_shift = _ulbn_ctz_(bp[b_idx]);

    if(a_idx == b_idx) {
      shl_idx += a_idx;
      shl_shift += _ulbn_min_(a_shift, b_shift);
    } else {
      if(a_idx < b_idx) {
        shl_idx += a_idx;
        shl_shift += a_shift;
      } else {
        shl_idx += b_idx;
        shl_shift += b_shift;
      }
    }
    if(shl_shift > ulbn_cast_int(ULBN_LIMB_BITS)) {
      shl_shift -= ulbn_cast_int(ULBN_LIMB_BITS);
      ++shl_idx;
    }

    if(a_shift)
      ulbn_shr(ap, ap + a_idx, an - a_idx, a_shift);
    else
      ulbn_fcopy(ap, ap + a_idx, an - a_idx);
    if(b_shift)
      ulbn_shr(bp, bp + b_idx, bn - b_idx, b_shift);
    else
      ulbn_fcopy(bp, bp + b_idx, bn - b_idx);
    an -= a_idx;
    an -= (ap[an - 1] == 0);
    bn -= b_idx;
    bn -= (bp[bn - 1] == 0);

    cmp = ulbn_cmp(ap, an, bp, bn);
    if(cmp == 0)
      break;
    if(cmp > 0) {
      ulbn_sub(ap, ap, an, bp, bn);
      an = ulbn_rnorm(ap, an);
    } else {
      ulbn_sub(bp, bp, bn, ap, an);
      bn = ulbn_rnorm(bp, bn);
    }
  }

  if(shl_shift) {
    const ulbn_limb_t cy = ulbn_shl(ap + shl_idx, ap, an, shl_shift);
    if(cy) {
      ap[an + shl_idx] = cy;
      ++an;
    }
  } else
    ulbn_rcopy(ap + shl_idx, ap, an);
  ulbn_fill0(ap, shl_idx);
  return ulbn_rnorm(ap, shl_idx + an);
}



#if ULBN_CONF_BIG_INT

  /***************************************
   * <ulbi> Utility about `ulbn_ssize_t` *
   ***************************************/

  #define _ULBI_SSIZE_LIMIT ulbn_cast_usize(_ulbn_min_(_ULBN_USIZE_LIMIT / 2, ulbn_cast_usize(ULBN_SSIZE_MAX)))
static ul_constexpr const ulbn_usize_t ULBI_SSIZE_LIMIT = _ULBI_SSIZE_LIMIT;
static ul_constexpr const ulbn_usize_t ULBI_SHORT_LIMB_SIZE = _ULBI_SHORT_LIMB_SIZE;

  #define _ulbi_abs_size(n) ulbn_cast_usize((n) < 0 ? -(n) : (n))
  #define _ulbi_make_ssize(pos, n) ((pos) ? ulbn_cast_ssize(n) : -ulbn_cast_ssize(n))
  /* However, we must check if `ulbn_ssize_t` exceeds the limit */
  /*
  #define ULBI_DO_IF_SSIZE_COND(cond, expr) \
    if(ul_unlikely(cond))                   \
    expr((void)0)
  #define ULBI_DO_IF_SSIZE_OVERFLOW(n, expr) ULBI_DO_IF_SSIZE_COND((n) > ULBI_SSIZE_LIMIT, expr)
  */
  #define ULBI_RETURN_IF_SSIZE_COND(cond, ret) \
    if(ul_unlikely(cond))                      \
    return (ret)
  #define ULBI_RETURN_IF_SSIZE_OVERFLOW(n, ret) ULBI_RETURN_IF_SSIZE_COND((n) > ULBI_SSIZE_LIMIT, ret)

ULBN_PUBLIC ulbn_usize_t ulbi_len_limit(void) {
  return ULBI_SSIZE_LIMIT;
}

ul_static_assert(
  _ULBI_SHORT_LIMB_SIZE >= (sizeof(ulbn_ulong_t) + sizeof(ulbn_limb_t) - 1) / sizeof(ulbn_limb_t),
  "ULBI_SHORT_LIMB_SIZE is too small, it cannot hold `ulbn_ulong_t`"
);

  #if ULBN_SSIZE_MAX == -ULBN_SSIZE_MIN
    #define _ulbi_same_sign(a, b) (((a) >= 0) == ((b) >= 0))
  #else
    #define _ulbi_same_sign(a, b) (((a) ^ (b)) >= 0)
  #endif

/************************
 * <ulbi> Memory manage *
 ************************/

ULBN_PUBLIC size_t ulbi_sizeof(void) {
  return sizeof(ulbi_t);
}
ULBN_PUBLIC const ulbi_t* ulbi_zero(void) {
  static const ulbi_t zero = ULBI_INIT;
  return &zero;
}


ULBN_PUBLIC ulbi_t* ulbi_init(ulbi_t* o) {
  o->len = 0;
  o->cap = ULBI_SHORT_LIMB_SIZE;
  return o;
}
ULBN_PUBLIC int ulbi_init_reserve(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n) {
  ULBN_RETURN_IF_USIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
  o->cap = ULBI_SHORT_LIMB_SIZE;
  o->len = 0;
  if(n > ULBI_SHORT_LIMB_SIZE) {
    o->u.lng = ulbn_allocT(ulbn_limb_t, alloc, n);
    ULBN_RETURN_IF_ALLOC_FAILED(o->u.lng, ULBN_ERR_NOMEM);
    o->cap = n;
  }
  return 0;
}
ULBN_PRIVATE ulbn_limb_t* _ulbi_reserve(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n) {
  ulbn_usize_t new_cap;
  ulbn_limb_t* new_limb;

  ulbn_assert(n > o->cap);
  ulbn_assert(n > ULBI_SHORT_LIMB_SIZE);
  #if ULBN_CONF_ONLY_ALLOCATE_NEEDED
  new_cap = n;
  #else
  new_cap = o->cap + (o->cap >> 1);
  new_cap = _ulbn_max_(new_cap, n);
  ULBN_DO_IF_USIZE_OVERFLOW(new_cap, new_cap = n;);
  #endif
  ULBN_DO_IF_USIZE_OVERFLOW(new_cap, return ul_nullptr;);

  if(o->cap > ULBI_SHORT_LIMB_SIZE) {
    new_limb = ulbn_reallocT(ulbn_limb_t, alloc, o->u.lng, o->cap, new_cap);
    ULBN_RETURN_IF_ALLOC_FAILED(new_limb, ul_nullptr);
  } else {
    new_limb = ulbn_allocT(ulbn_limb_t, alloc, new_cap);
    ULBN_RETURN_IF_ALLOC_FAILED(new_limb, ul_nullptr);
    memcpy(new_limb, o->u.shrt, sizeof(o->u.shrt));
  }
  o->u.lng = new_limb;
  o->cap = new_cap;
  return new_limb;
}
  #define _ulbi_limbs(o) ((o)->cap <= ULBI_SHORT_LIMB_SIZE ? (o)->u.shrt : (o)->u.lng)
  #define _ulbi_res(alloc, o, n) \
    ((ulbn_cast_usize(n) <= (o)->cap) ? _ulbi_limbs(o) : _ulbi_reserve((alloc), (o), ulbn_cast_usize(n)))
ULBN_PUBLIC int ulbi_reserve(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n) {
  ulbn_limb_t* ptr;
  if(ulbn_cast_usize(n) <= (o)->cap)
    return 0;
  ULBN_RETURN_IF_USIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
  ptr = _ulbi_res(alloc, o, n);
  (void)ptr;
  ULBN_RETURN_IF_ALLOC_FAILED(ptr, ULBN_ERR_NOMEM);
  return 0;
}


ULBN_PUBLIC const ulbn_limb_t* ulbi_get_limbs(const ulbi_t* obj) {
  return _ulbi_limbs(obj);
}
ULBN_PUBLIC size_t ulbi_get_limbs_len(const ulbi_t* obj) {
  return _ulbi_abs_size(obj->len);
}
ULBN_PUBLIC int ulbi_set_limbs(const ulbn_alloc_t* alloc, ulbi_t* obj, const ulbn_limb_t* limbs, size_t len) {
  ulbn_limb_t* rp;
  ulbn_usize_t rn;

  if(ul_unlikely(len > _ULBI_SSIZE_LIMIT))
    return ULBN_ERR_EXCEED_RANGE;
  rp = _ulbi_res(alloc, obj, len);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  memmove(rp, limbs, len * sizeof(ulbn_limb_t));
  rn = ulbn_rnorm(rp, ulbn_cast_usize(len));
  obj->len = ulbn_cast_ssize(rn);
  return 0;
}
ULBN_PUBLIC int ulbi_init_limbs(const ulbn_alloc_t* alloc, ulbi_t* obj, const ulbn_limb_t* limbs, size_t len) {
  return ulbi_set_limbs(alloc, ulbi_init(obj), limbs, len);
}


  #define _ulbi_set_zero(dst) ((dst)->len = 0)
  #define _ulbi_may_set_zero(dst) ((dst) && _ulbi_set_zero(dst))
ULBN_PUBLIC ulbi_t* ulbi_set_zero(ulbi_t* dst) {
  _ulbi_set_zero(dst);
  return dst;
}

ULBN_PUBLIC ulbi_t* ulbi_init_limb(ulbi_t* dst, ulbn_limb_t limb) {
  dst->cap = ULBI_SHORT_LIMB_SIZE;
  if(limb == 0)
    _ulbi_set_zero(dst);
  else {
    dst->u.shrt[0] = limb;
    dst->len = 1;
  }
  return dst;
}
ULBN_PUBLIC ulbi_t* ulbi_init_slimb(ulbi_t* dst, ulbn_slimb_t slimb) {
  dst->cap = ULBI_SHORT_LIMB_SIZE;
  if(slimb == 0)
    _ulbi_set_zero(dst);
  else {
    if(slimb < 0) {
      dst->u.shrt[0] = ulbn_from_neg_slimb(slimb);
      dst->len = -1;
    } else {
      dst->u.shrt[0] = ulbn_from_pos_slimb(slimb);
      dst->len = 1;
    }
  }
  return dst;
}
ULBN_PUBLIC void ulbi_set_limb(ulbi_t* dst, ulbn_limb_t limb) {
  if(limb == 0)
    _ulbi_set_zero(dst);
  else {
    _ulbi_limbs(dst)[0] = limb;
    dst->len = 1;
  }
}
ULBN_PUBLIC void ulbi_set_slimb(ulbi_t* dst, ulbn_slimb_t slimb) {
  if(slimb == 0)
    _ulbi_set_zero(dst);
  else {
    if(slimb < 0) {
      _ulbi_limbs(dst)[0] = ulbn_from_neg_slimb(slimb);
      dst->len = -1;
    } else {
      _ulbi_limbs(dst)[0] = ulbn_from_pos_slimb(slimb);
      dst->len = 1;
    }
  }
}


ULBN_PUBLIC void ulbi_deinit(const ulbn_alloc_t* alloc, ulbi_t* o) {
  if(o->cap > ULBI_SHORT_LIMB_SIZE)
    ulbn_deallocT(ulbn_limb_t, alloc, o->u.lng, o->cap);
  _ulbi_set_zero(o);
  o->cap = ULBI_SHORT_LIMB_SIZE;
}
ULBN_PUBLIC int ulbi_shrink(const ulbn_alloc_t* alloc, ulbi_t* o) {
  const ulbn_usize_t n = _ulbi_abs_size(o->len);
  if(o->cap <= ULBI_SHORT_LIMB_SIZE)
    return 0;
  if(n <= ULBI_SHORT_LIMB_SIZE) {
    ulbn_limb_t temp[_ULBI_SHORT_LIMB_SIZE];
    memcpy(temp, o->u.lng, sizeof(temp));
    ulbn_deallocT(ulbn_limb_t, alloc, o->u.lng, o->cap);
    memcpy(o->u.shrt, temp, sizeof(temp));
    o->cap = ULBI_SHORT_LIMB_SIZE;
    return 0;
  } else {
    ulbn_limb_t* limb = ul_nullptr;
    limb = ulbn_reallocT(ulbn_limb_t, alloc, o->u.lng, o->cap, n);
    ULBN_RETURN_IF_ALLOC_FAILED(limb, ULBN_ERR_NOMEM);
    o->u.lng = limb;
    o->cap = n;
  }
  return 0;
}


  #if 0
ULBN_PRIVATE void ulbi_dprint(FILE* fp, const char* prefix, const ulbi_t* bi) {
  if(prefix)
    fputs(prefix, fp);
  if(bi->len == 0)
    fputc('0', fp);
  else {
    if(bi->len < 0)
      fputc('-', fp);
    ulbn_conv2print_generic(
      ulbn_default_alloc(), 0, _ulbn_fileprinter, fp, _ulbi_limbs(bi), _ulbi_abs_size(bi->len), _ulbn_upper_table, 10
    );
  }
  fputc('\n', fp);
}
  #endif

/********************************************
 * <ulbi> `ulbn_ulong_t` and `ulbn_slong_t` *
 ********************************************/

ULBN_PUBLIC void ulbi_set_ulong(ulbi_t* dst, ulbn_ulong_t l) {
  dst->len = ulbn_cast_ssize(ulbn_set_ulong(_ulbi_limbs(dst), l));
}
ULBN_PUBLIC void ulbi_set_slong(ulbi_t* dst, ulbn_slong_t l) {
  if(l >= 0)
    dst->len = ulbn_cast_ssize(ulbn_set_ulong(_ulbi_limbs(dst), ulbn_from_pos_slong(l)));
  else
    dst->len = -ulbn_cast_ssize(ulbn_set_ulong(_ulbi_limbs(dst), ulbn_from_neg_slong(l)));
}
ULBN_PUBLIC ulbi_t* ulbi_init_ulong(ulbi_t* dst, ulbn_ulong_t l) {
  dst->len = ulbn_cast_ssize(ulbn_set_ulong(dst->u.shrt, l));
  dst->cap = ULBI_SHORT_LIMB_SIZE;
  return dst;
}
ULBN_PUBLIC ulbi_t* ulbi_init_slong(ulbi_t* dst, ulbn_slong_t l) {
  if(l >= 0)
    dst->len = ulbn_cast_ssize(ulbn_set_ulong(dst->u.shrt, ulbn_from_pos_slong(l)));
  else
    dst->len = -ulbn_cast_ssize(ulbn_set_ulong(dst->u.shrt, ulbn_from_neg_slong(l)));
  dst->cap = ULBI_SHORT_LIMB_SIZE;
  return dst;
}

/************************************
 * <ulbi> Copy, Modify integer sign *
 ************************************/

ULBN_PUBLIC int ulbi_set_copy(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* src) {
  if(dst != src) {
    ulbn_limb_t* limb;
    const ulbn_usize_t n = _ulbi_abs_size(src->len);
    if(n <= ULBI_SHORT_LIMB_SIZE)
      limb = _ulbi_limbs(dst);
    else {
      limb = _ulbi_res(alloc, dst, n);
      ULBN_RETURN_IF_ALLOC_FAILED(limb, ULBN_ERR_NOMEM);
    }
    ulbn_copy(limb, _ulbi_limbs(src), n);
    dst->len = src->len;
  }
  return 0;
}
ULBN_PUBLIC void ulbi_set_move(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbi_t* src) {
  if(dst != src) {
    ulbi_deinit(alloc, dst);
    *dst = *src;
    ulbi_init(src);
  }
}

ULBN_PUBLIC void ulbi_swap(ulbi_t* o1, ulbi_t* o2) {
  _ulbn_swap_(ulbi_t, *o1, *o2);
}
ULBN_PUBLIC int ulbi_neg(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao) {
  const int err = ulbi_set_copy(alloc, ro, ao);
  ro->len = -ro->len;
  return err;
}
ULBN_PUBLIC int ulbi_abs(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao) {
  const int err = ulbi_set_copy(alloc, ro, ao);
  ro->len = ulbn_cast_ssize(_ulbi_abs_size(ro->len));
  return err;
}

/*********************
 * <ulbi> Set 2^bits *
 *********************/

ULBN_PRIVATE int _ulbi_set_2exp(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t idx, int shift) {
  ulbn_limb_t* p;
  p = _ulbi_res(alloc, dst, idx + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(p, ULBN_ERR_NOMEM);
  ulbn_fill0(p, ulbn_cast_usize(idx));
  p[idx] = ULBN_LIMB_SHL(1, shift);
  dst->len = ulbn_cast_ssize(ulbn_cast_usize(idx + 1));
  return 0;
}
ULBN_PUBLIC int ulbi_set_2exp_bits(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_bits_t n) {
  const ulbn_bits_t idx = n / ULBN_LIMB_BITS;
  ULBI_RETURN_IF_SSIZE_COND(idx > ULBI_SSIZE_LIMIT - 1, ULBN_ERR_EXCEED_RANGE);
  return _ulbi_set_2exp(alloc, dst, ulbn_cast_usize(idx), ulbn_cast_int(n % ULBN_LIMB_BITS));
}
ULBN_PUBLIC int ulbi_set_2exp_sbits(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_sbits_t n) {
  ulbn_bits_t idx;
  if(ul_unlikely(n < 0)) {
    _ulbi_set_zero(dst);
    return ULBN_ERR_INEXACT;
  }
  idx = ulbn_cast_bits(n) / ULBN_LIMB_BITS;
  ULBI_RETURN_IF_SSIZE_COND(idx > ULBI_SSIZE_LIMIT - 1, ULBN_ERR_EXCEED_RANGE);
  return _ulbi_set_2exp(alloc, dst, ulbn_cast_usize(idx), ulbn_cast_int(ulbn_cast_bits(n) % ULBN_LIMB_BITS));
}
ULBN_PUBLIC int ulbi_set_2exp(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* n) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(n->len < 0)) {
    _ulbi_set_zero(dst);
    return ULBN_ERR_INEXACT;
  }
  shift = ulbn_to_bit_info(_ulbi_limbs(n), ulbn_cast_usize(n->len), &idx);
  if(ul_unlikely(shift < 0))
    return ULBN_ERR_EXCEED_RANGE;
  ULBI_RETURN_IF_SSIZE_COND(idx > ULBI_SSIZE_LIMIT - 1, ULBN_ERR_EXCEED_RANGE);
  return _ulbi_set_2exp(alloc, dst, idx, shift);
}

  /********************
   * <ulbi> Set bytes *
   ********************/

  #if ULBN_LIMB_MAX == UCHAR_MAX
    #define _ulbi_set_bytes_fix_len(len) (len)
  #else
    #define _ulbi_set_bytes_fix_len(len) ((len) / sizeof(ulbn_limb_t) + ((len) % sizeof(ulbn_limb_t) != 0))
  #endif

ULBN_PRIVATE void _ulbi_set_bytes_unsafe_le(
  ulbn_limb_t* dp, ulbn_usize_t wlen, /* */
  const unsigned char* p, size_t len  /* */
) {
  #if ULBN_LIMB_MAX == UCHAR_MAX || (defined(UL_ENDIAN_LITTLE) && !defined(UL_ENDIAN_BIG))
  if(ul_likely(wlen))
    dp[wlen - 1] = 0;
  memcpy(dp, p, len);
  #else
  const unsigned char* q;
  unsigned sz;
  ulbn_limb_t limb = 0;

  (void)wlen;
  limb = 0;
  for(; len >= sizeof(ulbn_limb_t); len -= sizeof(ulbn_limb_t)) {
    p += sizeof(ulbn_limb_t);
    q = p;
    for(sz = sizeof(ulbn_limb_t); sz--;)
      limb = (limb << CHAR_BIT) | *--q;
    *dp++ = limb;
  }
  limb = 0;
  q = p + len;
  while(len--)
    limb = (limb << CHAR_BIT) | *--q;
  if(limb)
    *dp++ = limb;
  #endif
}
ULBN_PRIVATE void _ulbi_set_bytes_unsafe_be(
  ulbn_limb_t* dp, ulbn_usize_t wlen, /* */
  const unsigned char* p, size_t len  /* */
) {
  #if ULBN_LIMB_MAX == UCHAR_MAX
  (void)wlen;
  for(p += len; len--;)
    *dp++ = *--p;
  #else
  const unsigned char* q;
  unsigned sz;
  ulbn_limb_t limb = 0;

  (void)wlen;
  p += len;
  for(; len >= sizeof(ulbn_limb_t); len -= sizeof(ulbn_limb_t)) {
    p -= sizeof(ulbn_limb_t);
    q = p;
    for(sz = sizeof(ulbn_limb_t); sz--;)
      limb = ulbn_cast_limb((limb << CHAR_BIT) | *q++);
    *dp++ = limb;
  }
  limb = 0;
  q = p - len;
  while(len--)
    limb = ulbn_cast_limb((limb << CHAR_BIT) | *q++);
  if(limb)
    *dp++ = limb;
  #endif
}

ULBN_PRIVATE int _ulbi_set_bytes_pos_le(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const unsigned char* p, size_t len      /* */
) {
  ulbn_limb_t* dp;
  size_t wlen;

  while(len > 0 && p[len - 1] == 0)
    --len;
  wlen = _ulbi_set_bytes_fix_len(len);
  ULBI_RETURN_IF_SSIZE_OVERFLOW(wlen, ULBN_ERR_EXCEED_RANGE);
  dp = _ulbi_res(alloc, dst, wlen);
  ULBN_RETURN_IF_ALLOC_FAILED(dp, ULBN_ERR_NOMEM);

  _ulbi_set_bytes_unsafe_le(dp, ulbn_cast_usize(wlen), p, len);
  dst->len = ulbn_cast_ssize(ulbn_rnorm(_ulbi_limbs(dst), ulbn_cast_usize(wlen)));
  return 0;
}
ULBN_PRIVATE int _ulbi_set_bytes_pos_be(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const unsigned char* p, size_t len      /* */
) {
  ulbn_limb_t* dp;
  size_t wlen;

  while(len > 0 && p[0] == 0) {
    ++p;
    --len;
  }
  wlen = _ulbi_set_bytes_fix_len(len);
  ULBI_RETURN_IF_SSIZE_OVERFLOW(wlen, ULBN_ERR_EXCEED_RANGE);
  dp = _ulbi_res(alloc, dst, wlen);
  ULBN_RETURN_IF_ALLOC_FAILED(dp, ULBN_ERR_NOMEM);

  _ulbi_set_bytes_unsafe_be(dp, ulbn_cast_usize(wlen), p, len);
  dst->len = ulbn_cast_ssize(ulbn_rnorm(_ulbi_limbs(dst), ulbn_cast_usize(wlen)));
  return 0;
}

ULBN_PRIVATE int _ulbi_set_bytes_neg_le(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const unsigned char* p, size_t len      /* */
) {
  ulbn_limb_t* dp;
  size_t wlen;

  while(len > 1 && p[len - 1] == UCHAR_MAX)
    --len;
  wlen = _ulbi_set_bytes_fix_len(len);
  ULBI_RETURN_IF_SSIZE_OVERFLOW(wlen, ULBN_ERR_EXCEED_RANGE);
  dp = _ulbi_res(alloc, dst, wlen);
  ULBN_RETURN_IF_ALLOC_FAILED(dp, ULBN_ERR_NOMEM);

  _ulbi_set_bytes_unsafe_le(dp, ulbn_cast_usize(wlen), p, len);
  #if ULBN_LIMB_MAX != UCHAR_MAX
  len = sizeof(ulbn_limb_t) - (wlen * sizeof(ulbn_limb_t) - len);
  if(len != sizeof(ulbn_limb_t)) {
    ulbn_assert(wlen > 0);
    dp[wlen - 1] |= ULBN_LIMB_SHL(ULBN_LIMB_MAX, len * CHAR_BIT);
  }
  #endif
  ulbn_neg(dp, dp, ulbn_cast_usize(wlen), 1);
  dst->len = -ulbn_cast_ssize(ulbn_rnorm(_ulbi_limbs(dst), ulbn_cast_usize(wlen)));
  return 0;
}
ULBN_PRIVATE int _ulbi_set_bytes_neg_be(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const unsigned char* p, size_t len      /* */
) {
  ulbn_limb_t* dp;
  size_t wlen;

  while(len > 1 && p[0] == UCHAR_MAX) {
    ++p;
    --len;
  }
  wlen = _ulbi_set_bytes_fix_len(len);
  ULBI_RETURN_IF_SSIZE_OVERFLOW(wlen, ULBN_ERR_EXCEED_RANGE);
  dp = _ulbi_res(alloc, dst, wlen);
  ULBN_RETURN_IF_ALLOC_FAILED(dp, ULBN_ERR_NOMEM);

  _ulbi_set_bytes_unsafe_be(dp, ulbn_cast_usize(wlen), p, len);
  #if ULBN_LIMB_MAX != UCHAR_MAX
  len = sizeof(ulbn_limb_t) - (wlen * sizeof(ulbn_limb_t) - len);
  if(len != sizeof(ulbn_limb_t)) {
    ulbn_assert(wlen > 0);
    dp[wlen - 1] |= ULBN_LIMB_SHL(ULBN_LIMB_MAX, len * CHAR_BIT);
  }
  #endif
  ulbn_neg(dp, dp, ulbn_cast_usize(wlen), 1);
  dst->len = -ulbn_cast_ssize(ulbn_rnorm(_ulbi_limbs(dst), ulbn_cast_usize(wlen)));
  return 0;
}

ULBN_PUBLIC int ulbi_set_bytes_unsigned_le(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
) {
  return _ulbi_set_bytes_pos_le(alloc, dst, ul_reinterpret_cast(const unsigned char*, bytes), len);
}
ULBN_PUBLIC int ulbi_set_bytes_unsigned_be(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
) {
  return _ulbi_set_bytes_pos_be(alloc, dst, ul_reinterpret_cast(const unsigned char*, bytes), len);
}
ULBN_PUBLIC int ulbi_set_bytes_signed_le(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
) {
  static ul_constexpr const unsigned char NEG_MASK = ul_static_cast(unsigned char, 1u << (CHAR_BIT - 1));
  const unsigned char* p = ul_reinterpret_cast(const unsigned char*, bytes);

  if(ul_unlikely(len == 0)) {
    _ulbi_set_zero(dst);
    return 0;
  }

  if(p[len - 1] & NEG_MASK)
    return _ulbi_set_bytes_neg_le(alloc, dst, p, len);
  else
    return _ulbi_set_bytes_pos_le(alloc, dst, p, len);
}
ULBN_PUBLIC int ulbi_set_bytes_signed_be(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
) {
  static ul_constexpr const unsigned char NEG_MASK = ul_static_cast(unsigned char, 1u << (CHAR_BIT - 1));
  const unsigned char* p = ul_reinterpret_cast(const unsigned char*, bytes);

  if(ul_unlikely(len == 0)) {
    _ulbi_set_zero(dst);
    return 0;
  }

  if(p[0] & NEG_MASK)
    return _ulbi_set_bytes_neg_be(alloc, dst, p, len);
  else
    return _ulbi_set_bytes_pos_be(alloc, dst, p, len);
}
ULBN_PUBLIC int ulbi_set_bytes_unsigned(
  const ulbn_alloc_t* alloc, ulbi_t* dst,          /* */
  const void* bytes, size_t len, int is_big_endian /* */
) {
  return is_big_endian ? _ulbi_set_bytes_pos_be(alloc, dst, ul_reinterpret_cast(const unsigned char*, bytes), len)
                       : _ulbi_set_bytes_pos_le(alloc, dst, ul_reinterpret_cast(const unsigned char*, bytes), len);
}
ULBN_PUBLIC int ulbi_set_bytes_signed(
  const ulbn_alloc_t* alloc, ulbi_t* dst,          /* */
  const void* bytes, size_t len, int is_big_endian /* */
) {
  static ul_constexpr const unsigned char NEG_MASK = ul_static_cast(unsigned char, 1u << (CHAR_BIT - 1));
  const unsigned char* p = ul_reinterpret_cast(const unsigned char*, bytes);

  if(len == 0) {
    _ulbi_set_zero(dst);
    return 0;
  }

  if(is_big_endian) {
    if(p[0] & NEG_MASK)
      return _ulbi_set_bytes_neg_be(alloc, dst, p, len);
    else
      return _ulbi_set_bytes_pos_be(alloc, dst, p, len);
  } else {
    if(p[len - 1] & NEG_MASK)
      return _ulbi_set_bytes_neg_le(alloc, dst, p, len);
    else
      return _ulbi_set_bytes_pos_le(alloc, dst, p, len);
  }
}

/*************************
 * <ulbi> Initialization *
 *************************/

ULBN_PUBLIC int ulbi_init_copy(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* src) {
  return ulbi_set_copy(alloc, ulbi_init(dst), src);
}
ULBN_PUBLIC void ulbi_init_move(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbi_t* src) {
  if(dst != src) {
    (void)alloc;
    *dst = *src;
    ulbi_init(src);
  }
}
ULBN_PUBLIC int ulbi_init_2exp_bits(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_bits_t n) {
  return ulbi_set_2exp_bits(alloc, ulbi_init(dst), n);
}
ULBN_PUBLIC int ulbi_init_2exp_sbits(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_sbits_t n) {
  return ulbi_set_2exp_sbits(alloc, ulbi_init(dst), n);
}
ULBN_PUBLIC int ulbi_init_2exp(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* n) {
  return ulbi_set_2exp(alloc, ulbi_init(dst), n);
}
ULBN_PUBLIC int ulbi_init_string(const ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, int base) {
  return ulbi_set_string(alloc, ulbi_init(dst), str, base);
}
ULBN_PUBLIC int ulbi_init_string_len(const ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, size_t len, int base) {
  return ulbi_set_string_len(alloc, ulbi_init(dst), str, len, base);
}

ULBN_PUBLIC int ulbi_init_bytes_unsigned_le(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
) {
  return ulbi_set_bytes_unsigned_le(alloc, ulbi_init(dst), bytes, len);
}
ULBN_PUBLIC int ulbi_init_bytes_unsigned_be(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
) {
  return ulbi_set_bytes_unsigned_be(alloc, ulbi_init(dst), bytes, len);
}
ULBN_PUBLIC int ulbi_init_bytes_signed_le(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
) {
  return ulbi_set_bytes_signed_le(alloc, ulbi_init(dst), bytes, len);
}
ULBN_PUBLIC int ulbi_init_bytes_signed_be(
  const ulbn_alloc_t* alloc, ulbi_t* dst, /* */
  const void* bytes, size_t len           /* */
) {
  return ulbi_set_bytes_signed_be(alloc, ulbi_init(dst), bytes, len);
}
ULBN_PUBLIC int ulbi_init_bytes_unsigned(
  const ulbn_alloc_t* alloc, ulbi_t* dst,          /* */
  const void* bytes, size_t len, int is_big_endian /* */
) {
  return ulbi_set_bytes_unsigned(alloc, ulbi_init(dst), bytes, len, is_big_endian);
}
ULBN_PUBLIC int ulbi_init_bytes_signed(
  const ulbn_alloc_t* alloc, ulbi_t* dst,          /* */
  const void* bytes, size_t len, int is_big_endian /* */
) {
  return ulbi_set_bytes_signed(alloc, ulbi_init(dst), bytes, len, is_big_endian);
}

/*********************
 * <ulbi> Comparison *
 *********************/

ULBN_PUBLIC int ulbi_comp(const ulbi_t* ao, const ulbi_t* bo) {
  const int a_positive = (ao->len >= 0);
  int cmp;
  if(ao->len != bo->len)
    return ao->len < bo->len ? -1 : 1;
  cmp = ulbn_cmpn(_ulbi_limbs(ao), _ulbi_limbs(bo), _ulbi_abs_size(bo->len));
  return a_positive ? cmp : -cmp;
}
ULBN_PUBLIC int ulbi_comp_limb(const ulbi_t* ao, ulbn_limb_t b) {
  const ulbn_ssize_t an = ao->len;
  if(an == 1) {
    const ulbn_limb_t a = _ulbi_limbs(ao)[0];
    if(a == b)
      return 0;
    return a < b ? -1 : 1;
  } else if(an == 0)
    return -(b != 0);
  else
    return an < 0 ? -1 : 1;
}
ULBN_PUBLIC int ulbi_comp_slimb(const ulbi_t* ao, ulbn_slimb_t b) {
  ulbn_ssize_t an = ao->len;
  ulbn_limb_t b_fix;
  int c;

  if(b == 0)
    return an == 0 ? 0 : (an < 0 ? -1 : 1);
  if(b > 0) {
    b_fix = ulbn_from_pos_slimb(b);
    c = 1;
  } else {
    b_fix = ulbn_from_neg_slimb(b);
    c = -1;
    an = -an;
  }
  if(an == 1) {
    const ulbn_limb_t a = _ulbi_limbs(ao)[0];
    if(a == b_fix)
      return 0;
    return a < b_fix ? -c : c;
  } else
    return an <= 0 ? -c : c;
}

ULBN_PRIVATE int _ulbi_comp_ulong(const ulbn_limb_t* ap, ulbn_ssize_t an, ulbn_ulong_t b) {
  #if ULBN_ULONG_MAX <= ULBN_LIMB_MAX
  if(an == 1) {
    const ulbn_limb_t a = ap[0];
    if(a == b)
      return 0;
    return a < b ? -1 : 1;
  } else if(an == 0)
    return -(b != 0);
  else
    return an < 0 ? -1 : 1;
  #else
  unsigned bits, num;
  ulbn_limb_t x;

  if(an < 0)
    return -1;
  if(b == 0)
    return an == 0 ? 0 : 1;
  bits = ulbn_cast_uint(ulbn_cast_int(ULBN_ULONG_BITS) - _ulbn_clz_ulong(b));
  num = (bits - 1u) / ULBN_LIMB_BITS;
  bits = num * ULBN_LIMB_BITS;
  if(ulbn_cast_uint(an) != num + 1)
    return ulbn_cast_uint(an) < num + 1 ? -1 : 1;
  do {
    x = ulbn_cast_limb(b >> bits);
    if(ap[num] != x)
      return ap[num] < x ? -1 : 1;
    bits -= ulbn_cast_uint(ULBN_LIMB_BITS);
  } while(num--);
  return 0;
  #endif
}
ULBN_PUBLIC int ulbi_comp_ulong(const ulbi_t* ao, ulbn_ulong_t b) {
  return _ulbi_comp_ulong(_ulbi_limbs(ao), ao->len, b);
}
ULBN_PUBLIC int ulbi_comp_slong(const ulbi_t* ao, ulbn_slong_t b) {
  return b >= 0 ? _ulbi_comp_ulong(_ulbi_limbs(ao), ao->len, ulbn_from_pos_slong(b))
                : -_ulbi_comp_ulong(_ulbi_limbs(ao), -ao->len, ulbn_from_neg_slong(b));
}


ULBN_PUBLIC int ulbi_eq(const ulbi_t* ao, const ulbi_t* bo) {
  if(ao->len != bo->len)
    return 0;
  return ao->len >= 0 ? ulbn_cmpn(_ulbi_limbs(ao), _ulbi_limbs(bo), ulbn_cast_usize(ao->len)) == 0
                      : ulbn_cmpn(_ulbi_limbs(ao), _ulbi_limbs(bo), ulbn_cast_usize(-ao->len)) == 0;
}
ULBN_PUBLIC int ulbi_eq_limb(const ulbi_t* ao, ulbn_limb_t b) {
  return b ? (ao->len == 1 && _ulbi_limbs(ao)[0] == b) : (ao->len == 0);
}
ULBN_PUBLIC int ulbi_eq_slimb(const ulbi_t* ao, ulbn_slimb_t b) {
  if(b == 0)
    return ao->len == 0;
  else if(b > 0)
    return ao->len == 1 && _ulbi_limbs(ao)[0] == ulbn_from_pos_slimb(b);
  else
    return ao->len == -1 && _ulbi_limbs(ao)[0] == ulbn_from_neg_slimb(b);
}

ULBN_PRIVATE int _ulbi_eq_ulong(const ulbn_limb_t* ap, ulbn_ssize_t an, ulbn_ulong_t b) {
  #if ULBN_ULONG_MAX <= ULBN_LIMB_MAX
  return b ? (an == 1 && ap[0] == b) : (an == 0);
  #else
  unsigned bits, num;

  if(an < 0)
    return 0;
  if(b == 0)
    return an == 0;

  bits = ulbn_cast_uint(ulbn_cast_int(ULBN_ULONG_BITS) - _ulbn_clz_ulong(b));
  num = (bits - 1u) / ULBN_LIMB_BITS;
  bits = num * ULBN_LIMB_BITS;
  if(ulbn_cast_uint(an) != num + 1)
    return 0;
  do {
    if(ap[num] != ulbn_cast_limb(b >> bits))
      return 0;
    bits -= ulbn_cast_uint(ULBN_LIMB_BITS);
  } while(num--);
  return 1;
  #endif
}
ULBN_PUBLIC int ulbi_eq_ulong(const ulbi_t* ao, ulbn_ulong_t b) {
  return _ulbi_eq_ulong(_ulbi_limbs(ao), ao->len, b);
}
ULBN_PUBLIC int ulbi_eq_slong(const ulbi_t* ao, ulbn_slong_t b) {
  return b >= 0 ? _ulbi_eq_ulong(_ulbi_limbs(ao), ao->len, ulbn_from_pos_slong(b))
                : _ulbi_eq_ulong(_ulbi_limbs(ao), -ao->len, ulbn_from_neg_slong(b));
}


ULBN_PUBLIC int ulbi_sign(const ulbi_t* o) {
  if(o->len == 0)
    return 0;
  return o->len > 0 ? 1 : -1;
}
ULBN_PUBLIC int ulbi_is_zero(const ulbi_t* o) {
  return o->len == 0;
}
ULBN_PUBLIC int ulbi_is_even(const ulbi_t* o) {
  return o->len == 0 || (_ulbi_limbs(o)[0] & 1) == 0;
}
ULBN_PUBLIC int ulbi_is_odd(const ulbi_t* o) {
  return o->len != 0 && (_ulbi_limbs(o)[0] & 1) != 0;
}

/********************************
 * <ulbi> Addition, Subtraction *
 ********************************/

/* ignore sign of `ao` and `bo` */
ULBN_PRIVATE int _ulbi_add_ignore_sign(
  const ulbn_alloc_t* alloc, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_usize_t an,     /* */
  const ulbi_t* bo, ulbn_usize_t bn      /* */
) {
  ulbn_limb_t* rp;

  if(an < bn) {
    _ulbn_swap_(const ulbi_t*, ao, bo);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }
  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);

  rp[an] = ulbn_add(rp, _ulbi_limbs(ao), an, _ulbi_limbs(bo), bn);
  an += (rp[an] != 0);
  ULBI_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = ulbn_cast_ssize(an);
  return 0;
}
/* ignore sign of `ao` and `bo` */
ULBN_PRIVATE int _ulbi_sub_ignore_sign(
  const ulbn_alloc_t* alloc, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_usize_t an,     /* */
  const ulbi_t* bo, ulbn_usize_t bn      /* */
) {
  ulbn_usize_t rn;
  ulbn_limb_t* rp;
  const int cmp = ulbn_cmp(_ulbi_limbs(ao), an, _ulbi_limbs(bo), bn);
  if(cmp == 0) {
    _ulbi_set_zero(ro);
    return 0;
  }

  rn = _ulbn_max_(an, bn);
  rp = _ulbi_res(alloc, ro, rn);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  if(cmp > 0) {
    ulbn_sub(rp, _ulbi_limbs(ao), an, _ulbi_limbs(bo), bn);
    ro->len = ulbn_cast_ssize(ulbn_rnorm(rp, rn));
  } else {
    ulbn_sub(rp, _ulbi_limbs(bo), bn, _ulbi_limbs(ao), an);
    ro->len = -ulbn_cast_ssize(ulbn_rnorm(rp, rn));
  }
  return 0;
}
ULBN_PUBLIC int ulbi_add(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  const ulbn_usize_t an = _ulbi_abs_size(ao->len), bn = _ulbi_abs_size(bo->len);
  const int positive = (ao->len >= 0);
  int err;
  if(_ulbi_same_sign(ao->len, bo->len))
    err = _ulbi_add_ignore_sign(alloc, ro, ao, an, bo, bn);
  else
    err = _ulbi_sub_ignore_sign(alloc, ro, ao, an, bo, bn);
  ro->len = _ulbi_make_ssize(positive, ro->len);
  return err;
}
ULBN_PUBLIC int ulbi_sub(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  const ulbn_usize_t an = _ulbi_abs_size(ao->len), bn = _ulbi_abs_size(bo->len);
  const int positive = (ao->len >= 0);
  int err;
  if(_ulbi_same_sign(ao->len, bo->len))
    err = _ulbi_sub_ignore_sign(alloc, ro, ao, an, bo, bn);
  else
    err = _ulbi_add_ignore_sign(alloc, ro, ao, an, bo, bn);
  ro->len = _ulbi_make_ssize(positive, ro->len);
  return err;
}

ULBN_PRIVATE int _ulbi_add_limb_ignore_sign(
  const ulbn_alloc_t* alloc, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_usize_t an,     /* */
  ulbn_limb_t b                          /* */
) {
  ulbn_limb_t* rp;

  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);

  rp[an] = ulbn_add1(rp, _ulbi_limbs(ao), an, b);
  an += (rp[an] != 0);
  ULBI_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = ulbn_cast_ssize(an);
  return 0;
}
ULBN_PRIVATE int _ulbi_sub_limb_ignore_sign(
  const ulbn_alloc_t* alloc, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_usize_t an,     /* */
  ulbn_limb_t b                          /* */
) {
  const ulbn_limb_t* ap;
  ulbn_limb_t* rp;

  rp = _ulbi_res(alloc, ro, _ulbn_max_(an, 1u));
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);

  ap = _ulbi_limbs(ao);
  if(an >= 2) {
    ulbn_sub1(rp, _ulbi_limbs(ao), an, b);
    ro->len = ulbn_cast_ssize(ulbn_rnorm(rp, an));
  } else if(an == 1) {
    if(ap[0] >= b) {
      rp[0] = ulbn_cast_limb(ap[0] - b);
      ro->len = (rp[0] != 0);
    } else {
      rp[0] = ulbn_cast_limb(b - ap[0]);
      ro->len = -1;
    }
  } else {
    rp[0] = b;
    ro->len = -(b != 0);
  }
  return 0;
}
ULBN_PUBLIC int ulbi_add_limb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  const int positive = (ao->len >= 0);
  int err;
  if(ao->len >= 0)
    err = _ulbi_add_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(ao->len), b);
  else
    err = _ulbi_sub_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(-ao->len), b);
  ro->len = _ulbi_make_ssize(positive, ro->len);
  return err;
}
ULBN_PUBLIC int ulbi_sub_limb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  const int positive = (ao->len >= 0);
  int err;
  if(ao->len >= 0)
    err = _ulbi_sub_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(ao->len), b);
  else
    err = _ulbi_add_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(-ao->len), b);
  ro->len = _ulbi_make_ssize(positive, ro->len);
  return err;
}
ULBN_PUBLIC int ulbi_limb_sub(const ulbn_alloc_t* alloc, ulbi_t* ro, ulbn_limb_t a, const ulbi_t* bo) {
  int err;
  if(bo->len >= 0) {
    err = _ulbi_sub_limb_ignore_sign(alloc, ro, bo, ulbn_cast_usize(bo->len), a);
    ro->len = -ro->len;
  } else
    err = _ulbi_add_limb_ignore_sign(alloc, ro, bo, ulbn_cast_usize(-bo->len), a);
  return err;
}
ULBN_PUBLIC int ulbi_add_slimb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  return b >= 0 ? ulbi_add_limb(alloc, ro, ao, ulbn_from_pos_slimb(b))
                : ulbi_sub_limb(alloc, ro, ao, ulbn_from_neg_slimb(b));
}
ULBN_PUBLIC int ulbi_sub_slimb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  return b >= 0 ? ulbi_sub_limb(alloc, ro, ao, ulbn_from_pos_slimb(b))
                : ulbi_add_limb(alloc, ro, ao, ulbn_from_neg_slimb(b));
}
ULBN_PUBLIC int ulbi_slimb_sub(const ulbn_alloc_t* alloc, ulbi_t* ro, ulbn_slimb_t a, const ulbi_t* bo) {
  int err;
  if(a >= 0)
    err = ulbi_limb_sub(alloc, ro, ulbn_from_pos_slimb(a), bo);
  else {
    err = ulbi_add_limb(alloc, ro, bo, ulbn_from_neg_slimb(a));
    ro->len = -ro->len;
  }
  return err;
}

/*************************
 * <ulbi> Multiplication *
 *************************/

ULBN_PUBLIC int ulbi_mul_limb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  const int positive = (ao->len >= 0);
  ulbn_usize_t an = _ulbi_abs_size(ao->len);
  ulbn_limb_t* rp;

  if(ul_unlikely(ao->len == 0 || b == 0)) {
    _ulbi_set_zero(ro);
    return 0;
  }
  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  rp[an] = ulbn_mul1(rp, _ulbi_limbs(ao), an, b);
  an += (rp[an] != 0);
  ULBI_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbi_make_ssize(positive, an);
  return 0;
}
ULBN_PUBLIC int ulbi_mul_slimb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  if(b >= 0) {
    return ulbi_mul_limb(alloc, ro, ao, ulbn_from_pos_slimb(b));
  } else {
    const int err = ulbi_mul_limb(alloc, ro, ao, ulbn_from_neg_slimb(b));
    ro->len = -ro->len;
    return err;
  }
}
ULBN_PUBLIC int ulbi_mul(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  const int positive = _ulbi_same_sign(ao->len, bo->len);
  int err;
  ulbn_usize_t an = _ulbi_abs_size(ao->len), bn = _ulbi_abs_size(bo->len);
  ulbn_limb_t* rp;
  ulbn_usize_t rn;

  if(ul_unlikely(an == 0 || bn == 0)) {
    _ulbi_set_zero(ro);
    return 0;
  }
  if(an < bn) {
    _ulbn_swap_(const ulbi_t*, ao, bo);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }
  rn = an + bn;
  rp = _ulbi_res(alloc, ro, rn);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  err = ulbn_mul_guard(alloc, rp, _ulbi_limbs(ao), an, _ulbi_limbs(bo), bn);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  rn -= (rp[rn - 1] == 0);
  ULBI_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbi_make_ssize(positive, rn);
  return 0;
}

/*******************
 * <ulbi> Division *
 *******************/

ULBN_PRIVATE int _ulbi_divmod(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_usize_t an, int a_positive, /* */
  const ulbi_t* bo, ulbn_usize_t bn, int b_positive  /* */
) {
  const int positive = (a_positive == b_positive);
  int err = 0;
  ulbn_limb_t *qp = ul_nullptr, *rp = ul_nullptr;

  ulbn_assert(bn > 0);

  if(an < bn) {
    _ulbi_may_set_zero(qo);
    if(ro) {
      err = ulbi_set_copy(alloc, ro, ao);
      ULBN_RETURN_IF_ALLOC_COND(err, err);
    } else
      err = an ? ULBN_ERR_INEXACT : 0;
    return err;
  }
  if(ul_unlikely(qo == ro))
    qo = ul_nullptr;

  if(qo) {
    qp = _ulbi_res(alloc, qo, an - bn + 1);
    ULBN_RETURN_IF_ALLOC_FAILED(qp, ULBN_ERR_NOMEM);
  }
  if(ro) {
    rp = _ulbi_res(alloc, ro, bn);
    ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  }

  err = ulbn_divmod_guard(alloc, qp, rp, _ulbi_limbs(ao), an, _ulbi_limbs(bo), bn);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  if(qo) {
    qo->len = ulbn_cast_ssize(ulbn_rnorm(qp, an - bn + 1));
    qo->len = _ulbi_make_ssize(positive, qo->len);
  }
  if(ro) {
    ro->len = ulbn_cast_ssize(ulbn_rnorm(rp, bn));
    ro->len = _ulbi_make_ssize(a_positive, ro->len);
  }
  return err;
}
ULBN_PUBLIC int ulbi_divmod(const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  if(ul_unlikely(bo->len == 0)) {
    _ulbi_may_set_zero(qo);
    _ulbi_may_set_zero(ro);
    return ULBN_ERR_DIV_BY_ZERO;
  }

  return _ulbi_divmod(
    alloc, qo, ro,                             /* */
    ao, _ulbi_abs_size(ao->len), ao->len >= 0, /* */
    bo, _ulbi_abs_size(bo->len), bo->len >= 0  /* */
  );
}
ULBN_PUBLIC int ulbi_divmod_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, const ulbi_t* bo,                /* */
  enum ULBN_ROUND_ENUM round_mode                    /* */
) {
  ulbi_t tqo = ULBI_INIT, tro = ULBI_INIT;
  int err, op = 0;

  if(round_mode == ULBN_ROUND_DOWN)
    return ulbi_divmod(alloc, qo, ro, ao, bo);
  if(ul_unlikely(round_mode < ULBN_ROUND_DOWN || round_mode > ULBN_ROUND_FAITHFUL)) {
    _ulbi_may_set_zero(qo);
    _ulbi_may_set_zero(ro);
    return ULBN_ERR_BAD_ARGUMENT;
  }
  if(ul_unlikely(bo->len == 0)) {
    _ulbi_may_set_zero(qo);
    _ulbi_may_set_zero(ro);
    return ULBN_ERR_DIV_BY_ZERO;
  }

  /* use `tqo` and `tro` to avoid `qo==bo` or `ro==bo` */
  err = _ulbi_divmod(
    alloc, &tqo, &tro,                         /* */
    ao, _ulbi_abs_size(ao->len), ao->len >= 0, /* */
    bo, _ulbi_abs_size(bo->len), bo->len >= 0  /* */
  );
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  if(tro.len == 0)
    goto do_op;
  if(round_mode == ULBN_ROUND_FAITHFUL)
    goto do_op; /* `ULBN_ROUND_DOWN` is fastest */

  if(round_mode > ULBN_ROUND_CEILING)
    switch(ulbn_check_round(_ulbi_limbs(&tro), _ulbi_abs_size(tro.len), _ulbi_limbs(bo), _ulbi_abs_size(bo->len))) {
    case -1:
      round_mode = ULBN_ROUND_DOWN;
      break;
    case 1:
      round_mode = ULBN_ROUND_UP;
      break;
    default:
      round_mode = ulbn_adjust_half_round(round_mode, ulbi_is_even(&tqo));
    }

  op = ulbn_round_direction(round_mode, _ulbi_same_sign(ao->len, bo->len));
do_op:
  if(qo) {
    if(op == 0)
      ulbi_swap(qo, &tqo);
    else {
      if(op == 1)
        err = ulbi_add_limb(alloc, qo, &tqo, 1);
      else
        err = ulbi_sub_limb(alloc, qo, &tqo, 1);
      ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    }
  }
  if(ro) {
    if(op == 0)
      ulbi_swap(ro, &tro);
    else if(op == 1)
      err = ulbi_sub(alloc, ro, &tro, bo);
    else
      err = ulbi_add(alloc, ro, &tro, bo);
  } else
    err = (tro.len == 0 ? 0 : ULBN_ERR_INEXACT);

cleanup:
  ulbi_deinit(alloc, &tqo);
  ulbi_deinit(alloc, &tro);
  return err;
}


/* `r` is not fixed */
ULBN_PRIVATE int _ulbi_divmod_limb(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_limb_t* ro,                    /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, int keep_q_positive, ulbn_limb_t b /* */
) {
  int err = 0;
  ulbn_limb_t* qp = ul_nullptr;

  ulbn_assert(b != 0);
  ulbn_assert(an > 0);
  ulbn_assert(ro != ul_nullptr);

  if(qo) {
    qp = _ulbi_res(alloc, qo, an);
    ULBN_RETURN_IF_ALLOC_FAILED(qp, ULBN_ERR_NOMEM);
  }

  if(an == 1) {
    const ulbn_limb_t a = ap[0];
    const ulbn_limb_t r = ulbn_cast_limb(a % b);
    if(qp)
      qp[0] = ulbn_cast_limb(a / b);
    *ro = r;
  } else
    err = ulbn_divmod1(alloc, qp, ro, ap, an, b);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  if(qo) {
    qo->len = ulbn_cast_ssize(ulbn_rnorm(qp, an));
    qo->len = _ulbi_make_ssize(keep_q_positive, qo->len);
  }
  return err;
}
ULBN_PUBLIC int ulbi_divmod_limb(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_limb_t* ro, /* */
  const ulbi_t* ao, ulbn_limb_t b                         /* */
) {
  const int positive = (ao->len >= 0);
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);
  ulbn_limb_t tr;
  int err;

  if(ul_unlikely(b == 0)) {
    _ulbi_may_set_zero(qo);
    if(ro)
      *ro = 0;
    return ULBN_ERR_DIV_BY_ZERO;
  }
  if(ul_unlikely(an == 0)) {
    _ulbi_may_set_zero(qo);
    if(ro)
      *ro = 0;
    return 0;
  }

  err = _ulbi_divmod_limb(alloc, qo, &tr, _ulbi_limbs(ao), an, positive, b);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  ulbn_assert(err == 0);

  if(ro) {
    if(!positive && tr != 0) {
      *ro = ulbn_cast_limb(b - tr);
      err = ULBN_ERR_INEXACT;
    } else
      *ro = tr;
  } else
    err = tr == 0 ? 0 : ULBN_ERR_INEXACT;
  return err;
}
ULBN_PUBLIC int ulbi_divmod_limb_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_limb_t* ro, /* */
  const ulbi_t* ao, ulbn_limb_t b,                        /* */
  enum ULBN_ROUND_ENUM round_mode                         /* */
) {
  ulbi_t tqo = ULBI_INIT;
  ulbn_limb_t r;
  const int a_positive = (ao->len >= 0);
  int err, op = 0;

  if(ul_unlikely(round_mode < ULBN_ROUND_DOWN || round_mode > ULBN_ROUND_FAITHFUL)) {
    _ulbi_may_set_zero(qo);
    if(ro)
      *ro = 0;
    return ULBN_ERR_BAD_ARGUMENT;
  }
  if(ul_unlikely(b == 0)) {
    _ulbi_may_set_zero(qo);
    if(ro)
      *ro = 0;
    return ULBN_ERR_DIV_BY_ZERO;
  }
  if(ul_unlikely(ao->len == 0)) {
    _ulbi_may_set_zero(qo);
    if(ro)
      *ro = 0;
    return 0;
  }

  if(qo == ul_nullptr)
    qo = &tqo;
  err = _ulbi_divmod_limb(alloc, qo, &r, _ulbi_limbs(ao), _ulbi_abs_size(ao->len), a_positive, b);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  if(r == 0) {
    if(ro)
      *ro = 0;
    goto cleanup;
  }
  if(round_mode == ULBN_ROUND_FAITHFUL)
    goto do_op; /* `ULBN_ROUND_DOWN` is fastest */

  if(round_mode > ULBN_ROUND_CEILING) {
    if(r < b - r)
      round_mode = ULBN_ROUND_DOWN;
    else if(r > b - r)
      round_mode = ULBN_ROUND_UP;
    else
      round_mode = ulbn_adjust_half_round(round_mode, ulbi_is_even(qo));
  }
  op = ulbn_round_direction(round_mode, a_positive);

do_op:
  if(qo != &tqo) {
    if(op == 0) { /* do nothing */
    } else {
      if(op == 1)
        err = ulbi_add_limb(alloc, qo, qo, 1);
      else /* if(op == -1) */
        err = ulbi_sub_limb(alloc, qo, qo, 1);
      ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    }
  }
  if(ro) {
    if(a_positive) { /* +r */
      ulbn_assert(op == 0 || op == 1);
      if(op == 0) { /* r */
        /* do nothing */
      } else /* if(op == 1) */ { /* r - b */
        err = ULBN_ERR_INEXACT;
      }
    } else { /* -r */
      ulbn_assert(op == 0 || op == -1);
      if(op == 0) { /* -r */
        r = ulbn_cast_limb(b - r);
        err = ULBN_ERR_INEXACT;
      } else /* if(op == -1) */ { /* -r + b */
        r = ulbn_cast_limb(b - r);
      }
    }
    *ro = r;
  } else
    err = ULBN_ERR_INEXACT;

cleanup:
  ulbi_deinit(alloc, &tqo);
  return err;
}

ULBN_PUBLIC int ulbi_divmod_slimb(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_slimb_t* ro, /* */
  const ulbi_t* ao, ulbn_slimb_t _b                        /* */
) {
  const int positive = (ao->len >= 0) == (_b >= 0), a_positive = ao->len >= 0;
  int err = 0;
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);
  const ulbn_limb_t b = _b >= 0 ? ulbn_from_pos_slimb(_b) : ulbn_from_neg_slimb(_b);
  ulbn_limb_t r;

  if(ul_unlikely(b == 0)) {
    _ulbi_may_set_zero(qo);
    if(ro)
      *ro = 0;
    return ULBN_ERR_DIV_BY_ZERO;
  }
  if(ul_unlikely(ao->len == 0)) {
    _ulbi_may_set_zero(qo);
    if(ro)
      *ro = 0;
    return 0;
  }

  err = _ulbi_divmod_limb(alloc, qo, &r, _ulbi_limbs(ao), an, positive, b);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);

  if(ro) {
    if(a_positive)
      *ro = ulbn_cast_slimb(r);
    else
  #if ULBN_LIMB_MAX < UINT_MAX
      *ro = ulbn_cast_slimb(ulbn_cast_limb(ulbn_cast_uint(-ulbn_cast_slimb(r))));
  #else
      *ro = -ulbn_cast_slimb(r);
  #endif
  } else
    err = r ? ULBN_ERR_INEXACT : 0;
  return err;
}
ULBN_PUBLIC int ulbi_divmod_slimb_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_slimb_t* ro, /* */
  const ulbi_t* ao, ulbn_slimb_t _b,                       /* */
  enum ULBN_ROUND_ENUM round_mode                          /* */
) {
  const int positive = (ao->len >= 0) == (_b >= 0), a_positive = ao->len >= 0;
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);
  const ulbn_limb_t b = _b >= 0 ? ulbn_from_pos_slimb(_b) : ulbn_from_neg_slimb(_b);
  ulbn_limb_t r;
  ulbi_t tqo = ULBI_INIT;
  int op = 0, err = 0;

  if(ul_unlikely(round_mode < ULBN_ROUND_DOWN || round_mode > ULBN_ROUND_FAITHFUL)) {
    _ulbi_may_set_zero(qo);
    if(ro)
      *ro = 0;
    return ULBN_ERR_BAD_ARGUMENT;
  }
  if(ul_unlikely(b == 0)) {
    _ulbi_may_set_zero(qo);
    if(ro)
      *ro = 0;
    return ULBN_ERR_DIV_BY_ZERO;
  }
  if(ul_unlikely(ao->len == 0)) {
    _ulbi_may_set_zero(qo);
    if(ro)
      *ro = 0;
    return 0;
  }

  if(qo == ul_nullptr)
    qo = &tqo;
  err = _ulbi_divmod_limb(alloc, qo, &r, _ulbi_limbs(ao), an, positive, b);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  if(r == 0) {
    if(ro)
      *ro = 0;
    goto cleanup;
  }
  if(round_mode == ULBN_ROUND_FAITHFUL)
    goto do_op; /* `ULBN_ROUND_DOWN` is fastest */

  if(round_mode > ULBN_ROUND_CEILING) {
    if(r < b - r)
      round_mode = ULBN_ROUND_DOWN;
    else if(r > b - r)
      round_mode = ULBN_ROUND_UP;
    else
      round_mode = ulbn_adjust_half_round(round_mode, ulbi_is_even(qo));
  }
  op = ulbn_round_direction(round_mode, positive);

do_op:
  if(qo != &tqo) {
    if(op == 0) { /* do nothing */
    } else {
      if(op == 1)
        err = ulbi_add_limb(alloc, qo, qo, 1);
      else /* if(op == -1) */
        err = ulbi_sub_limb(alloc, qo, qo, 1);
      ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    }
  }
  ulbn_assert(r > 0 && r < b);
  if(ro) {
    if(a_positive) { /* +r */
      ulbn_assert(op == 0 || op == 1);
      if(op == 0) /* r */
        *ro = ulbn_cast_slimb(r);
      else /* if(op == 1) */ /* r - b */
        *ro = ulbn_cast_slimb(-ulbn_cast_slimb(b - r));
    } else { /* -r */
      ulbn_assert(op == 0 || op == -1);
      if(op == 0) /* -r */
        *ro = ulbn_cast_slimb(-ulbn_cast_slimb(r));
      else /* if(op == -1) */ /* -r + b */
        *ro = ulbn_cast_slimb(b - r);
    }
  } else
    err = ULBN_ERR_INEXACT;

cleanup:
  ulbi_deinit(alloc, &tqo);
  return err;
}

/****************************
 * <ulbi> Bitwise Operation *
 ****************************/

ULBN_PUBLIC int ulbi_and(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  ulbn_usize_t an = _ulbi_abs_size(ao->len), bn = _ulbi_abs_size(bo->len);
  const ulbn_limb_t *ap, *bp;
  ulbn_limb_t* rp;

  if(an < bn) {
    _ulbn_swap_(const ulbi_t*, ao, bo);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }

  if(ul_likely(ao->len >= 0)) {
    if(ul_likely(bo->len >= 0)) {
      rp = _ulbi_res(alloc, ro, bn);
      ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
      ulbn_and_nocy(rp, _ulbi_limbs(ao), _ulbi_limbs(bo), 0, bn);
      ro->len = ulbn_cast_ssize(ulbn_rnorm(rp, bn));
    } else {
      const ulbn_usize_t sep = ulbn_fnorm(_ulbi_limbs(bo), bn);
      ulbn_assert(sep < bn);
      rp = _ulbi_res(alloc, ro, an);
      ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
      ap = _ulbi_limbs(ao);
      bp = _ulbi_limbs(bo);

      ulbn_fill0(rp, sep);
      rp[sep] = ulbn_cast_limb(ap[sep] & _ulbn_neg_(bp[sep]));
      ulbn_and_nocy(rp + sep + 1, ap + sep + 1, bp + sep + 1, ULBN_LIMB_MAX, bn - sep - 1);
      ulbn_maycopy(rp + bn, ap + bn, an - bn);
      ro->len = ulbn_cast_ssize(ulbn_rnorm(rp, an));
    }
    return 0;
  }

  if(bo->len >= 0) {
    const ulbn_usize_t sep = ulbn_fnorm(_ulbi_limbs(ao), an);
    ulbn_assert(sep < an);
    if(sep > bn) {
      ro->len = 0;
    } else {
      rp = _ulbi_res(alloc, ro, bn);
      ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
      ap = _ulbi_limbs(ao);
      bp = _ulbi_limbs(bo);

      ulbn_fill0(rp, sep);
      rp[sep] = ulbn_cast_limb(_ulbn_neg_(ap[sep]) & bp[sep]);
      if(sep < bn)
        ulbn_and_nocy(rp + sep + 1, bp + sep + 1, ap + sep + 1, ULBN_LIMB_MAX, bn - sep - 1);
      ro->len = ulbn_cast_ssize(ulbn_rnorm(rp, bn));
    }
  } else {
    rp = _ulbi_res(alloc, ro, an + 1);
    ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
    rp[an] = ulbn_and(rp, 1, _ulbi_limbs(ao), an, 1, _ulbi_limbs(bo), bn, 1);
    an = ulbn_rnorm(rp, an + 1);
    ULBI_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
    ro->len = -ulbn_cast_ssize(an);
  }
  return 0;
}
ULBN_PUBLIC int ulbi_or(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  ulbn_usize_t an = _ulbi_abs_size(ao->len), bn = _ulbi_abs_size(bo->len);
  ulbn_limb_t* rp;

  if(an < bn) {
    _ulbn_swap_(const ulbi_t*, ao, bo);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }

  if(ul_likely(ao->len >= 0 && bo->len >= 0)) {
    const ulbn_limb_t *ap, *bp;
    rp = _ulbi_res(alloc, ro, an);
    ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
    ap = _ulbi_limbs(ao);
    bp = _ulbi_limbs(bo);
    ulbn_or_nocy(rp, ap, bp, 0, bn);
    ulbn_maycopy(rp + bn, ap + bn, an - bn);
    ro->len = ulbn_cast_ssize(an);
  } else {
    rp = _ulbi_res(alloc, ro, an + 1);
    ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
    rp[an] = ulbn_or(rp, 1, _ulbi_limbs(ao), an, ao->len < 0, _ulbi_limbs(bo), bn, bo->len < 0);
    an = ulbn_rnorm(rp, an + 1);
    ULBI_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
    ro->len = -ulbn_cast_ssize(an);
  }
  return 0;
}
ULBN_PUBLIC int ulbi_xor(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  ulbn_limb_t a_cy, b_cy;
  ulbn_usize_t an = _ulbi_abs_size(ao->len), bn = _ulbi_abs_size(bo->len);
  const ulbn_limb_t *ap, *bp;
  ulbn_limb_t* rp;

  if(an < bn) {
    _ulbn_swap_(const ulbi_t*, ao, bo);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }
  a_cy = ao->len < 0;
  b_cy = bo->len < 0;

  if(ul_likely(!a_cy && !b_cy)) {
    rp = _ulbi_res(alloc, ro, an);
    ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
    ap = _ulbi_limbs(ao);
    bp = _ulbi_limbs(bo);
    ulbn_xor_nocy(rp, ap, bp, 0, bn);
    ulbn_maycopy(rp + bn, ap + bn, an - bn);
    ro->len = ulbn_cast_ssize(ulbn_rnorm(rp, an));
  } else {
    const ulbn_limb_t r_cy = ulbn_cast_limb(a_cy ^ b_cy);
    rp = _ulbi_res(alloc, ro, an + 1);
    ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
    rp[an] = ulbn_xor(rp, r_cy, _ulbi_limbs(ao), an, a_cy, _ulbi_limbs(bo), bn, b_cy);
    an = ulbn_rnorm(rp, an + 1);
    ULBI_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
    ro->len = _ulbi_make_ssize(!r_cy, an);
  }
  return 0;
}
ULBN_PUBLIC int ulbi_com(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao) {
  ulbn_usize_t an = _ulbi_abs_size(ao->len);
  ulbn_limb_t* rp;

  rp = _ulbi_res(alloc, ro, an + (ao->len >= 0));
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  if(ao->len >= 0) {
    rp[an] = ulbn_add1(rp, _ulbi_limbs(ao), an, 1);
    an += (rp[an] != 0);
    ULBI_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
    ro->len = -ulbn_cast_ssize(an);
  } else {
    ulbn_sub1(rp, _ulbi_limbs(ao), an, 1);
    an = ulbn_rnorm(rp, an);
    ro->len = ulbn_cast_ssize(an);
  }
  return 0;
}


ul_static_assert(ULBN_LIMB_BITS < _ULBN_LIMB_SIGNBIT, "ulbn_usize_t is too large");
ULBN_PRIVATE int _ulbi_sal(
  const ulbn_alloc_t* alloc, ulbi_t* ro,                    /* */
  const ulbi_t* ao, const ulbn_usize_t idx, const int shift /* */
) {
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);
  ulbn_usize_t rn;
  ulbn_limb_t* rp;

  if(an == 0) {
    _ulbi_set_zero(ro);
    return 0;
  }
  rn = an + idx;

  if(shift) {
    ULBI_RETURN_IF_SSIZE_COND(rn > ULBN_USIZE_LIMIT - 1, ULBN_ERR_EXCEED_RANGE);
    ++rn;
    rp = _ulbi_res(alloc, ro, rn);
    rp[rn - 1] = ulbn_shl(rp + idx, _ulbi_limbs(ao), an, shift);
  } else {
    rp = _ulbi_res(alloc, ro, rn);
    ulbn_rcopy(rp + idx, _ulbi_limbs(ao), an);
  }

  ulbn_fill0(rp, idx);
  rn = ulbn_rnorm(rp, rn);
  ULBI_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbi_make_ssize(ao->len >= 0, rn);
  return 0;
}
ULBN_PRIVATE int _ulbi_sar(
  const ulbn_alloc_t* alloc, ulbi_t* ro,                    /* */
  const ulbi_t* ao, const ulbn_usize_t idx, const int shift /* */
) {
  const int a_neg = ao->len < 0;
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);
  ulbn_usize_t rn;
  ulbn_limb_t cy = 0;
  ulbn_limb_t* rp;
  const ulbn_limb_t* ap;

  if(an == 0) {
    _ulbi_set_zero(ro);
    return 0;
  }
  if(an <= idx) {
    if(a_neg) {
      rp = _ulbi_res(alloc, ro, 1u);
      ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
      rp[0] = 1;
    }
    ro->len = ulbn_cast_ssize(-a_neg);
    return 0;
  }

  rn = an - idx;
  rp = _ulbi_res(alloc, ro, rn + ulbn_cast_uint(a_neg));
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  ap = _ulbi_limbs(ao);

  /* When right-shifting a negative number, we need to check if the bits being shifted out are non-zero.
    If any non-zero bits exist, we need to add 1. */
  if(a_neg)
    cy = !ulbn_is0(ap, idx);

  if(shift)
    cy |= ulbn_shr(rp, ap + idx, rn, shift);
  else
    ulbn_fcopy(rp, ap + idx, rn);

  if(a_neg && cy)
    ulbn_add1(rp, rp, rn, 1);
  rn = ulbn_rnorm(rp, rn);
  ro->len = _ulbi_make_ssize(!a_neg, rn);
  return 0;
}

ULBN_PUBLIC int ulbi_sal_bits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_bits_t b) {
  const ulbn_bits_t idx = b / ULBN_LIMB_BITS;
  const int shift = ulbn_cast_int(b % ULBN_LIMB_BITS);
  if(ul_unlikely(idx > ULBI_SSIZE_LIMIT))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_sal(alloc, ro, ao, ulbn_cast_usize(idx), shift);
}
ULBN_PUBLIC int ulbi_sar_bits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_bits_t b) {
  const ulbn_bits_t idx = b / ULBN_LIMB_BITS;
  const int shift = ulbn_cast_int(b % ULBN_LIMB_BITS);
  return _ulbi_sar(alloc, ro, ao, ul_unlikely(idx > ULBI_SSIZE_LIMIT) ? ULBN_USIZE_MAX : ulbn_cast_usize(idx), shift);
}
ULBN_PUBLIC int ulbi_sal_sbits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_sbits_t b) {
  return b >= 0 ? ulbi_sal_bits(alloc, ro, ao, ulbn_from_pos_sbits(b))
                : ulbi_sar_bits(alloc, ro, ao, ulbn_from_neg_sbits(b));
}
ULBN_PUBLIC int ulbi_sar_sbits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_sbits_t b) {
  return b >= 0 ? ulbi_sar_bits(alloc, ro, ao, ulbn_from_pos_sbits(b))
                : ulbi_sal_bits(alloc, ro, ao, ulbn_from_neg_sbits(b));
}

ULBN_PUBLIC int ulbi_sal(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbn_usize_t idx;
  int shift;
  if(b->len >= 0) {
    shift = ulbn_to_bit_info(_ulbi_limbs(b), ulbn_cast_usize(b->len), &idx);
    if(ul_unlikely(shift < 0 || idx > ULBI_SSIZE_LIMIT))
      return ULBN_ERR_EXCEED_RANGE;
    return _ulbi_sal(alloc, ro, ao, idx, shift);
  } else {
    shift = ulbn_to_bit_info(_ulbi_limbs(b), ulbn_cast_usize(-b->len), &idx);
    if(ul_unlikely(shift < 0))
      return _ulbi_sar(alloc, ro, ao, ULBN_USIZE_MAX, shift);
    else
      return _ulbi_sar(alloc, ro, ao, idx, shift);
  }
}
ULBN_PUBLIC int ulbi_sar(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbn_usize_t idx;
  int shift;
  if(b->len >= 0) {
    shift = ulbn_to_bit_info(_ulbi_limbs(b), ulbn_cast_usize(b->len), &idx);
    if(ul_unlikely(shift < 0))
      return _ulbi_sar(alloc, ro, ao, ULBN_USIZE_MAX, shift);
    else
      return _ulbi_sar(alloc, ro, ao, idx, shift);
  } else {
    shift = ulbn_to_bit_info(_ulbi_limbs(b), ulbn_cast_usize(-b->len), &idx);
    if(ul_unlikely(shift < 0 || idx > ULBI_SSIZE_LIMIT))
      return ULBN_ERR_EXCEED_RANGE;
    return _ulbi_sal(alloc, ro, ao, idx, shift);
  }
}

/**************************
 * <ulbi> Division (2exp) *
 *************************/

ULBN_PRIVATE int _ulbi_divmod_2exp(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro,        /* */
  const ulbi_t* ao, const ulbn_usize_t idx, const int shift /* */
) {
  const int a_pos = ao->len >= 0;
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);
  ulbn_usize_t qn;

  ulbn_limb_t* rp;
  const ulbn_limb_t* ap;

  ulbn_limb_t cy = 0;
  ulbn_limb_t rrest;
  int err = 0;

  if(idx >= an) {
    _ulbi_may_set_zero(qo);
    if(ro)
      err = ulbi_set_copy(alloc, ro, ao);
    else
      err = an ? ULBN_ERR_INEXACT : 0;
    return err;
  }

  if(ul_unlikely(qo == ro))
    qo = ul_nullptr;
  ap = _ulbi_limbs(ao);
  rrest = !ulbn_is0(ap, idx);
  qn = an - idx;

  /* if `ro` != `ao`, we will copy enough limbs to `ro`, and then it's safe to calculate `qo` */
  if(ro && ro != ao) {
    rp = _ulbi_res(alloc, ro, idx + (shift != 0));
    ulbn_assert(ro == ao ? rp == ap : rp != ap);
    ULBN_RETURN_IF_ALLOC_COND(rp == ul_nullptr && (idx + (shift != 0)) != 0, ULBN_ERR_NOMEM);
    ulbn_copy(rp, ap, idx);
  }
  if(shift)
    cy = ulbn_cast_limb(ap[idx] & (ULBN_LIMB_SHL(2u, shift - 1) - 1u));

  if(qo) {
    ulbn_limb_t* qp = _ulbi_res(alloc, qo, qn);
    ULBN_RETURN_IF_ALLOC_FAILED(qp, ULBN_ERR_NOMEM);
    if(shift)
      ulbn_shr(qp, ap + idx, qn, shift);
    else
      ulbn_fcopy(qp, ap + idx, qn);
    qn = ulbn_rnorm(qp, qn);
    qo->len = _ulbi_make_ssize(a_pos, qn);
  }

  if(ro) {
    rp = _ulbi_limbs(ro);
    if(cy) {
      rp[idx] = cy;
      ro->len = _ulbi_make_ssize(a_pos, idx + 1);
    } else {
      const ulbn_usize_t rn = ulbn_rnorm(rp, idx);
      ro->len = _ulbi_make_ssize(a_pos, rn);
    }
  } else
    err = (rrest | cy) != 0 ? ULBN_ERR_INEXACT : 0;
  return err;
}

ULBN_PUBLIC int ulbi_divmod_2exp_bits(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_bits_t e                    /* */
) {
  const ulbn_bits_t idx = e / ULBN_LIMB_BITS;
  const int shift = ulbn_cast_int(e % ULBN_LIMB_BITS);
  return _ulbi_divmod_2exp(
    alloc, qo, ro, ao, ul_unlikely(idx > ULBI_SSIZE_LIMIT) ? ULBN_USIZE_MAX : ulbn_cast_usize(idx), shift
  );
}
ULBN_PUBLIC int ulbi_divmod_2exp_sbits(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_sbits_t e                   /* */
) {
  int err;
  if(ul_likely(e >= 0))
    return ulbi_divmod_2exp_bits(alloc, qo, ro, ao, ulbn_from_pos_sbits(e));
  err = qo ? ulbi_sal_bits(alloc, qo, ao, ulbn_from_neg_sbits(e)) : 0;
  _ulbi_may_set_zero(ro);
  return err;
}
ULBN_PUBLIC int ulbi_divmod_2exp(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, const ulbi_t* eo                 /* */
) {
  ulbn_usize_t idx;
  int shift, err;

  shift = ulbn_to_bit_info(_ulbi_limbs(eo), _ulbi_abs_size(eo->len), &idx);
  if(shift < 0) {
    if(eo->len < 0)
      return ULBN_ERR_EXCEED_RANGE;
    shift = 0;
    idx = ULBN_USIZE_MAX;
  }

  if(ul_likely(eo->len >= 0))
    return _ulbi_divmod_2exp(alloc, qo, ro, ao, idx, shift);
  else {
    err = qo ? _ulbi_sal(alloc, qo, ao, idx, shift) : 0;
    _ulbi_may_set_zero(ro);
    return err;
  }
}


ULBN_PRIVATE int _ulbi_divmod_2exp_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro,         /* */
  const ulbi_t* ao, const ulbn_usize_t idx, const int shift, /* */
  enum ULBN_ROUND_ENUM round_mode
) {
  const int a_pos = ao->len >= 0;
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);
  ulbn_usize_t qn;

  ulbn_limb_t* rp;
  const ulbn_limb_t* ap;

  ulbn_usize_t idx2;
  int shift2;
  ulbn_limb_t cy = 0;
  ulbn_limb_t rrest, rh = 0;
  int err = 0;

  int op = 0, q_even;

  if(ul_unlikely(round_mode < ULBN_ROUND_DOWN || round_mode > ULBN_ROUND_FAITHFUL)) {
    _ulbi_may_set_zero(qo);
    _ulbi_may_set_zero(ro);
    return ULBN_ERR_BAD_ARGUMENT;
  }
  if(ul_unlikely(ao->len == 0)) {
    _ulbi_may_set_zero(qo);
    _ulbi_may_set_zero(ro);
    return 0;
  }

  ap = _ulbi_limbs(ao);
  if(shift == 0) {
    if(ul_unlikely(idx == 0)) {
      rrest = 0;
      goto handle_ro;
    }
    idx2 = idx - 1;
    shift2 = ulbn_cast_int(ULBN_LIMB_BITS);
  } else {
    idx2 = idx;
    shift2 = shift;
  }
  if(idx2 < an)
    rh = ulbn_cast_limb((ap[idx2] >> (shift2 - 1)) & 1u);
  if(idx2 >= an)
    rrest = ulbn_cast_limb(!ulbn_is0(ap, an));
  else
    rrest =
      ulbn_cast_limb(ulbn_cast_limb(!ulbn_is0(ap, idx2)) | (ap[idx2] << (ulbn_cast_int(ULBN_LIMB_BITS) - shift2 + 1)));

handle_ro:
  if(idx >= an) {
    _ulbi_may_set_zero(qo);
    if(ro)
      err = ulbi_set_copy(alloc, ro, ao);
    else
      err = an ? ULBN_ERR_INEXACT : 0;
    ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
    q_even = 0;
    goto fix_remainder;
  }

  if(ul_unlikely(qo == ro))
    qo = ul_nullptr;
  qn = an - idx;

  /* if `ro` != `ao`, we will copy enough limbs to `ro`, and then it's safe to calculate `qo` */
  if(ro && ro != ao) {
    rp = _ulbi_res(alloc, ro, idx + (shift != 0));
    ulbn_assert(ro == ao ? rp == ap : rp != ap);
    ULBN_RETURN_IF_ALLOC_COND(rp == ul_nullptr && (idx + (shift != 0)) != 0, ULBN_ERR_NOMEM);
    ulbn_copy(rp, ap, idx);
  }
  if(shift)
    cy = ulbn_cast_limb(ap[idx] & (ULBN_LIMB_SHL(2u, shift - 1) - 1u));

  if(qo) {
    ulbn_limb_t* qp = _ulbi_res(alloc, qo, qn);
    ULBN_RETURN_IF_ALLOC_FAILED(qp, ULBN_ERR_NOMEM);
    if(shift)
      ulbn_shr(qp, ap + idx, qn, shift);
    else
      ulbn_fcopy(qp, ap + idx, qn);
    qn = ulbn_rnorm(qp, qn);
    qo->len = _ulbi_make_ssize(a_pos, qn);
    q_even = ulbi_is_even(qo);
  } else
    q_even = ((ap[idx] >> shift) & 1u) == 0;

  if(ro) {
    rp = _ulbi_limbs(ro);
    if(cy) {
      rp[idx] = cy;
      ro->len = _ulbi_make_ssize(a_pos, idx + 1);
    } else {
      const ulbn_usize_t rn = ulbn_rnorm(rp, idx);
      ro->len = _ulbi_make_ssize(a_pos, rn);
    }
  }

fix_remainder:
  if((rrest | rh) == 0) {
    ulbn_assert(err <= 0);
    return err;
  }
  if(round_mode == ULBN_ROUND_FAITHFUL)
    goto do_op; /* `ULBN_ROUND_DOWN` is fastest */

  if(round_mode > ULBN_ROUND_CEILING) {
    if(rh == 0)
      round_mode = ULBN_ROUND_DOWN;
    else if(rh != 0 && rrest != 0)
      round_mode = ULBN_ROUND_UP;
    else
      round_mode = ulbn_adjust_half_round(round_mode, q_even);
  }
  op = ulbn_round_direction(round_mode, a_pos);

do_op:
  if(qo) {
    if(op == 0) { /* do nothing */
    } else {
      if(op == 1)
        err = ulbi_add_limb(alloc, qo, qo, 1);
      else /* if(op == -1) */
        err = ulbi_sub_limb(alloc, qo, qo, 1);
      ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
    }
  }
  if(ro) {
    if(op != 0) {
      ulbi_t tmp = ULBI_INIT;
      ULBI_RETURN_IF_SSIZE_COND(idx > ULBI_SSIZE_LIMIT - 1, ULBN_ERR_EXCEED_RANGE);
      err = _ulbi_set_2exp(alloc, &tmp, idx, shift);
      ULBN_DO_IF_PUBLIC_COND(err < 0, return err;);
      if(a_pos) { /* r - b */
        ulbn_assert(op == 1);
        err = ulbi_sub(alloc, ro, ro, &tmp);
      } else { /* r + b */
        ulbn_assert(op == -1);
        err = ulbi_add(alloc, ro, ro, &tmp);
      }
      ulbi_deinit(alloc, &tmp);
    }
  } else
    err = ULBN_ERR_INEXACT;

  return err;
}

ULBN_PUBLIC int ulbi_divmod_2exp_bits_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_bits_t e,                   /* */
  enum ULBN_ROUND_ENUM round_mode                    /* */
) {
  const ulbn_bits_t idx = e / ULBN_LIMB_BITS;
  const int shift = ulbn_cast_int(e % ULBN_LIMB_BITS);
  return _ulbi_divmod_2exp_ex(
    alloc, qo, ro, ao, ul_unlikely(idx > ULBI_SSIZE_LIMIT) ? ULBN_USIZE_MAX : ulbn_cast_usize(idx), shift, round_mode
  );
}
ULBN_PUBLIC int ulbi_divmod_2exp_sbits_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_sbits_t e,                  /* */
  enum ULBN_ROUND_ENUM round_mode                    /* */
) {
  int err;
  if(ul_likely(e >= 0))
    return ulbi_divmod_2exp_bits_ex(alloc, qo, ro, ao, ulbn_from_pos_sbits(e), round_mode);

  if(ul_unlikely(round_mode < ULBN_ROUND_DOWN || round_mode > ULBN_ROUND_FAITHFUL)) {
    _ulbi_may_set_zero(qo);
    _ulbi_may_set_zero(ro);
    return ULBN_ERR_BAD_ARGUMENT;
  }
  err = ulbi_sal_bits(alloc, qo, ao, ulbn_from_neg_sbits(e));
  _ulbi_may_set_zero(ro);
  return err;
}
ULBN_PUBLIC int ulbi_divmod_2exp_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, const ulbi_t* eo,                /* */
  enum ULBN_ROUND_ENUM round_mode                    /* */
) {
  ulbn_usize_t idx;
  int shift, err;

  shift = ulbn_to_bit_info(_ulbi_limbs(eo), _ulbi_abs_size(eo->len), &idx);
  if(shift < 0) {
    if(eo->len < 0)
      return ULBN_ERR_EXCEED_RANGE;
    shift = 0;
    idx = ULBN_USIZE_MAX;
  }

  if(ul_likely(eo->len) >= 0)
    return _ulbi_divmod_2exp_ex(alloc, qo, ro, ao, idx, shift, round_mode);
  if(ul_unlikely(round_mode < ULBN_ROUND_DOWN || round_mode > ULBN_ROUND_FAITHFUL)) {
    _ulbi_may_set_zero(qo);
    _ulbi_may_set_zero(ro);
    return ULBN_ERR_BAD_ARGUMENT;
  }
  err = _ulbi_sal(alloc, qo, ao, idx, shift);
  _ulbi_may_set_zero(ro);
  return err;
}

/*********************
 * <ulbi> Set string *
 *********************/

ul_static_assert(ULBN_LIMB_MAX >= 36, "ulbn_limb_t is too small to hold base");
ULBN_PRIVATE int _ulbi_setstr_parse_short(
  const ulbn_alloc_t* alloc, ulbi_t* dst, const unsigned char* p, size_t len, ulbn_limb_t base
) {
  ulbn_limb_t intpart_l = 0, intpart_B = 1;
  const ulbn_limb_t B_guard = ulbn_cast_limb(ULBN_LIMB_MAX / base);
  unsigned c;
  int err;
  while(len-- != 0) {
    c = _ulbn_setstr_val(*p);
    ++p;
    if(c >= base)
      continue;
    if(intpart_B >= B_guard) {
      err = ulbi_mul_limb(alloc, dst, dst, intpart_B);
      ULBN_DO_IF_PUBLIC_COND(err < 0, return err;);
      ulbi_add_limb(alloc, dst, dst, intpart_l);
      ULBN_DO_IF_PUBLIC_COND(err < 0, return err;);
      intpart_l = 0;
      intpart_B = 1;
    }
    intpart_l = ulbn_cast_limb(intpart_l * base + c);
    intpart_B *= base;
  }
  err = ulbi_mul_limb(alloc, dst, dst, intpart_B);
  ULBN_DO_IF_PUBLIC_COND(err < 0, return err;);
  ulbi_add_limb(alloc, dst, dst, intpart_l);
  ULBN_DO_IF_PUBLIC_COND(err < 0, return err;);
  return 0;
}

ULBN_PRIVATE int _ulbi_setstr_mul_base_exp(const ulbn_alloc_t* alloc, ulbi_t* obj, ulbn_limb_t base, ulbn_bits_t expo) {
  unsigned shift = 0;
  int err;

  ulbn_assert(2 <= base && base <= 36);

  if(base == 32)
    shift = 5;
  else if(base == 16)
    shift = 4;
  else if(base == 8)
    shift = 3;
  else if(base == 4)
    shift = 2;
  else if(base == 2)
    shift = 1;

  if(shift > 0) {
    ulbn_assert(expo <= ULBN_BITS_MAX / shift);
    err = ulbi_sal_bits(alloc, obj, obj, ulbn_cast_bits(expo * shift));
  } else {
    ulbi_t temp;
    ulbi_init_limb(&temp, base);
    err = ulbi_pow_ulong(alloc, &temp, &temp, expo);
    if(ul_likely(err >= 0))
      err = ulbi_mul(alloc, obj, obj, &temp);
    ulbi_deinit(alloc, &temp);
  }
  return err;
}
ULBN_PRIVATE int _ulbi_setstr_div_base_exp(const ulbn_alloc_t* alloc, ulbi_t* obj, ulbn_limb_t base, ulbn_bits_t expo) {
  unsigned shift = 0;
  int err;

  ulbn_assert(2 <= base && base <= 36);

  if(base == 32)
    shift = 5;
  else if(base == 16)
    shift = 4;
  else if(base == 8)
    shift = 3;
  else if(base == 4)
    shift = 2;
  else if(base == 2)
    shift = 1;

  if(shift > 0) {
    ulbn_assert(expo <= ULBN_BITS_MAX / shift);
    err = ulbi_divmod_2exp_bits(alloc, obj, ul_nullptr, obj, ulbn_cast_bits(expo * shift));
  } else {
    ulbi_t temp;
    ulbi_init_limb(&temp, base);
    err = ulbi_pow_ulong(alloc, &temp, &temp, expo);
    if(ul_likely(err >= 0))
      err = ulbi_divmod(alloc, obj, ul_nullptr, obj, &temp);
    ulbi_deinit(alloc, &temp);
  }
  ulbn_assert(err < 0 || err == 0 || err == ULBN_ERR_INEXACT);
  return err;
}

  #define _ULBI_SETSTR_PARSE_LONG_THRESHOLD 256
  #if _ULBI_SETSTR_PARSE_LONG_THRESHOLD < ULBN_BITS_MAX
ULBN_PRIVATE int _ulbi_setstr_parse(
  const ulbn_alloc_t* alloc, ulbi_t* dst, const unsigned char* p, size_t len, ulbn_limb_t base, int has_sep
) {
  size_t slen;
  ulbn_bits_t pow;
  int l_has_sep, err;
  ulbi_t lobj = ULBI_INIT, robj = ULBI_INIT;

  if(ul_unlikely(has_sep)) {
    size_t last_sep = 0;
    ulbn_bits_t pow_copy;

    /* count digits */
    pow = 0;
    while(len > 0 && _ulbn_setstr_val(p[len - 1]) >= base) /* skip trailling seperate characters */
      --len;
    for(slen = 0; slen < len; ++slen)
      if(_ulbn_setstr_val(p[slen]) < base)
        ++pow;
      else
        last_sep = slen;

    /* split the string into two part */
    pow_copy = pow - (pow >> 1);
    l_has_sep = 0;
    for(slen = 0;; ++slen) {
      ulbn_assert(slen < len);
      if(_ulbn_setstr_val(p[slen]) < base) {
        if(pow_copy == 0)
          break;
        --pow_copy;
      } else
        l_has_sep |= 1;
    }

    has_sep = (last_sep > slen);
  } else {
    slen = len - (len >> 1);
    pow = ulbn_cast_bits(len);
    l_has_sep = 0;
  }
  if(ul_unlikely(pow <= _ULBI_SETSTR_PARSE_LONG_THRESHOLD))
    return _ulbi_setstr_parse_short(alloc, dst, p, len, base);

  err = _ulbi_setstr_parse(alloc, &lobj, p, slen, base, l_has_sep);
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;);
  err = _ulbi_setstr_parse(alloc, &robj, p + slen, len - slen, base, has_sep);
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;);
  err = _ulbi_setstr_mul_base_exp(alloc, &lobj, base, pow >> 1);
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;);
  err = ulbi_add(alloc, dst, &lobj, &robj);

done:
  ulbi_deinit(alloc, &lobj);
  ulbi_deinit(alloc, &robj);
  return err;
}
  #else
ULBN_PRIVATE int _ulbi_setstr_parse(
  const ulbn_alloc_t* alloc, ulbi_t* dst, const unsigned char* p, size_t len, ulbn_limb_t base, int has_sep
) {
  (void)has_sep;
  return _ulbi_setstr_parse_short(alloc, dst, p, len, base);
}
  #endif

ULBN_PUBLIC int ulbi_set_string_ex(
  const ulbn_alloc_t* alloc, ulbi_t* dst,           /* */
  const char** pstr, size_t len, int base, int flag /* */
) {
  const int ch_dot = (flag & ULBN_SET_STRING_ACCEPT_DECIMAL_PART) ? '.' : INT_MIN;
  const int ch_sep = (flag & ULBN_SET_STRING_ACCEPT_SEPARATOR) ? '_' : INT_MIN;
  int neg = 0; /* 1 means negative, 0 means positive */
  int err = 0;
  const char* str = *pstr;

  const char* parse_ptr;
  size_t parse_len = 0;
  size_t parse_sep = 0;
  size_t parse_pow = 0;

  ulbn_bits_t expo = 0;
  int expo_neg = 0;
  ulbn_limb_t expo_base = 0;

  ulbi_t dec = ULBI_INIT; /* decimal part */
  int err_dec = 0;        /* store `ULBN_ERR_INEXACT` in decimal part */

  ulbn_check_startup();
  _ulbi_set_zero(dst);
  if(len == 0)
    return 0;

  /* eat sign */

  if(*str == '+') {
    --len;
    if(ul_unlikely(len == 0))
      goto done;
    ++str;
  } else if(*str == '-') {
    neg = 1;
    --len;
    if(ul_unlikely(len == 0))
      goto done;
    ++str;
  }

  /* eat preffix */

  if(base == 0) {
    if(*str != '0') {
      base = 10;
      goto handle_integer;
    }
    ++str;
    --len;
    if(len == 0) /* "0" */
      goto done;
    if(*str == 'x' || *str == 'X') {
      base = 16;
    eat_prefix:
      if(len == 1) /* "0x" or "0X" */
        goto done;
      if(!(_ulbn_setstr_val(str[1]) < ulbn_cast_uint(base) || str[1] == ch_dot
         )) /* the first character after preffix must be legal */
        goto done;
      ++str; /* eat "0x" or "0X" */
      --len;
    } else if(*str == 'o' || *str == 'O') {
      base = 8;
      goto eat_prefix;
    } else if(*str == 'b' || *str == 'B') {
      base = 2;
      goto eat_prefix;
    } else if(*str == '0') {
      goto done; /* "00" */
    } else if(_ulbn_setstr_val(*str) < 8 && (flag & ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX)) {
      base = 8;
      goto handle_integer;
    } else if(*str == ch_dot) {
      base = 10;
      goto handle_integer;
    } else /* illegal character */
      goto done;
  }
  if(ul_unlikely(base < 2 || base > 36)) {
    err = ULBN_ERR_BAD_ARGUMENT;
    goto done;
  }

handle_integer:
  if(ul_unlikely(flag & ULBN_SET_STRING_ACCEPT_INFINITE) && len != 0) {
    if(base < 18 || (base < 23 && str[0] != 'i' && str[1] != 'I')) {
      if(ulbn_setstr_infinite(&str, len) != 0) {
        err = ULBN_ERR_INVALID;
        goto done;
      }
    }
  }

  parse_ptr = str;
  for(; len != 0; --len) {
    if(*str == ch_sep)
      ++parse_sep;
    else {
      if(_ulbn_setstr_val(*str) >= ulbn_cast_uint(base))
        break;
      ++parse_pow;
    }
    ++str;
  }
  #if !defined(SIZE_MAX) || SIZE_MAX > ULBN_BITS_MAX
  if(ul_unlikely(parse_pow) >= ULBN_BITS_MAX) {
    err = ULBN_ERR_EXCEED_RANGE;
    goto done;
  }
  #endif
  err = _ulbi_setstr_parse(
    alloc, dst, ul_reinterpret_cast(const unsigned char*, parse_ptr), ul_static_cast(size_t, str - parse_ptr),
    ulbn_cast_limb(base), parse_sep != 0
  );
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;);
  if(len == 0)
    goto handle_decimal;

  /* if !(flag & ULBN_SET_STRING_ACCEPT_DECIMAL_PART), and `ch_dot` = INT_MIN, then `*str` never equals to `ch_dot` */
  if(*str == ch_dot) {
    ++str;
    --len;
    parse_ptr = str;
    parse_pow = 0;
    parse_sep = 0;

    for(; len != 0; --len) {
      if(*str == ch_sep)
        ++parse_sep;
      else if(_ulbn_setstr_val(*str) >= ulbn_cast_uint(base))
        break;
      ++str;
      ++parse_pow;
    }
    parse_len = ul_static_cast(size_t, str - parse_ptr);
    for(; parse_len != 0; --parse_len)
      if(parse_ptr[parse_len - 1] == '0') {
        --parse_pow;
      } else if(parse_ptr[parse_len - 1] == ch_sep) {
        --parse_sep;
      } else
        break;
  #if !defined(SIZE_MAX) || SIZE_MAX > ULBN_BITS_MAX
    if(ul_unlikely(parse_pow >= ULBN_BITS_MAX)) {
      err = ULBN_ERR_EXCEED_RANGE;
      goto done;
    }
  #endif
    if(len == 0)
      goto handle_decimal;
  }

  if(*str == 'e' || *str == 'E' || *str == 'p' || *str == 'P') {
    const ulbn_bits_t expo_limit = (ULBN_BITS_MAX - 9) / 10;
    const char* p = str;

    if(*p == 'e' || *p == 'E') {
      if(!(flag & ULBN_SET_STRING_ACCEPT_DEC_EXPONENT))
        goto handle_decimal;
      if(!(flag & ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH) && base != 10)
        goto handle_decimal;
      expo_base = 10;
    } else {
      if(!(flag & ULBN_SET_STRING_ACCEPT_HEX_EXPONENT))
        goto handle_decimal;
      if(!(flag & ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH) && base != 16)
        goto handle_decimal;
      expo_base = 2;
    }
    if(ul_unlikely(len == 1))
      goto handle_decimal;

    ++p;
    --len;
    if(ul_unlikely(len == 0))
      goto handle_decimal;
    if(*p == '+') {
      --len;
      ++p;
    } else if(*p == '-') {
      --len;
      ++p;
      expo_neg = 1;
    }
    if(ul_unlikely(len == 0))
      goto handle_decimal;

    for(; len != 0; --len) {
      if(!(_ulbn_setstr_val(*p) < 10))
        break;
      if(ul_unlikely(expo > expo_limit)) {
        err = ULBN_ERR_EXCEED_RANGE;
        goto done;
      }
      expo *= 10;
      expo += ul_static_cast(unsigned char, _ulbn_setstr_val(*p));
      ++p;
    }
    str = p;
  }

handle_decimal:
  if(ul_likely(expo == 0)) {
    err = (parse_len != 0 ? ULBN_ERR_INEXACT : 0);
    goto done;
  }
  if(ul_unlikely(expo_neg)) {
    err = _ulbi_setstr_div_base_exp(alloc, dst, expo_base, expo);
    if(err == 0)
      err = ULBN_ERR_INEXACT;
    goto done;
  }

  if(ul_likely(parse_len == 0)) {
    err = _ulbi_setstr_mul_base_exp(alloc, dst, expo_base, expo);
    goto done;
  }

  if(ul_unlikely(expo_base != ulbn_cast_uint(base))) {
    err = _ulbi_setstr_parse(
      alloc, &dec, ul_reinterpret_cast(const unsigned char*, parse_ptr), parse_len, ulbn_cast_limb(base), parse_sep != 0
    );
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup_dec;);
    err = _ulbi_setstr_mul_base_exp(alloc, &dec, expo_base, expo);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup_dec;);
    err_dec = err = _ulbi_setstr_div_base_exp(alloc, &dec, ulbn_cast_limb(base), ulbn_cast_bits(parse_pow));
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup_dec;);
    err = _ulbi_setstr_mul_base_exp(alloc, dst, expo_base, expo);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup_dec;);
    err = ulbi_add(alloc, dst, dst, &dec);
    if(ul_likely(err == 0))
      err = err_dec;
    goto cleanup_dec;
  }

  for(; parse_len > 0; --parse_len)
    if(parse_ptr[parse_len - 1] != ch_sep) {
      if(parse_pow <= expo)
        break;
      --parse_pow;
      err_dec = ULBN_ERR_INEXACT;
    }
  err = _ulbi_setstr_parse(
    alloc, &dec, ul_reinterpret_cast(const unsigned char*, parse_ptr), parse_len, ulbn_cast_limb(base), parse_sep != 0
  );
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup_dec;);
  if(parse_pow < expo) {
    err = _ulbi_setstr_mul_base_exp(alloc, &dec, ulbn_cast_limb(base), ulbn_cast_bits(expo - parse_pow));
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup_dec;);
  }
  err = _ulbi_setstr_mul_base_exp(alloc, dst, ulbn_cast_limb(base), expo);
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup_dec;);
  err = ulbi_add(alloc, dst, dst, &dec);
  if(ul_likely(err == 0))
    err = err_dec;

cleanup_dec:
  ulbi_deinit(alloc, &dec);
done:
  *pstr = str;
  if(neg) {
    dst->len = -dst->len;
    if(ul_likely(err == 0) && dst->len == 0)
      err = ULBN_ERR_INEXACT;
  }
  return err;
}
ULBN_PUBLIC int ulbi_set_string(const ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, int base) {
  const int err =
    ulbi_set_string_ex(alloc, dst, &str, _ULBN_SIZET_MAX, base, ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX);
  if(err < 0)
    return err;
  return *str == 0 ? 0 : ULBN_ERR_INVALID;
}
ULBN_PUBLIC int ulbi_set_string_len(const ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, size_t len, int base) {
  const int err = ulbi_set_string_ex(alloc, dst, &str, len, base, ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX);
  if(err < 0)
    return err;
  return *str == 0 ? 0 : ULBN_ERR_INVALID;
}

/*******************************
 * <ulbi> Single bit operation *
 *******************************/

ULBN_PRIVATE int _ulbi_testbit(const ulbi_t* o, ulbn_usize_t idx, int shift) {
  ulbn_assert(0 <= shift && ulbn_cast_uint(shift) < ULBN_LIMB_BITS);
  return (ulbn_limb(_ulbi_limbs(o), _ulbi_abs_size(o->len), o->len < 0, idx) & ULBN_LIMB_SHL(1, shift)) != 0;
}
ULBN_PRIVATE int _ulbi_setbit(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t idx, int shift) {
  ulbn_usize_t n = _ulbi_abs_size(o->len);
  ulbn_limb_t* op;

  if(ul_likely(o->len >= 0)) {
    if(idx >= n) {
      op = _ulbi_res(alloc, o, idx + 1);
      ULBN_RETURN_IF_ALLOC_FAILED(op, ULBN_ERR_NOMEM);
      ulbn_fill0(op + n, idx - n);
      op[idx] = ULBN_LIMB_SHL(1, shift);
      ULBI_RETURN_IF_SSIZE_OVERFLOW(ulbn_cast_usize(idx + 1), ULBN_ERR_EXCEED_RANGE);
      o->len = ulbn_cast_ssize(idx + 1);
    } else {
      op = _ulbi_limbs(o);
      op[idx] |= ULBN_LIMB_SHL(1, shift);
    }
  } else {
    op = _ulbi_limbs(o);
    ulbn_sub1(op + idx, op + idx, n - idx, ULBN_LIMB_SHL(1, shift));
    if(op[n - 1] == 0) {
      n = ulbn_rnorm(op, n);
      o->len = -ulbn_cast_ssize(n);
    }
  }
  return 0;
}
ULBN_PRIVATE int _ulbi_resetbit(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t idx, int shift) {
  ulbn_usize_t n = _ulbi_abs_size(o->len);
  ulbn_limb_t* op;

  if(ul_likely(o->len >= 0)) {
    ulbn_assert(idx < n);
    op = _ulbi_limbs(o);
    op[idx] &= ~ULBN_LIMB_SHL(1, shift);
    if(op[n - 1] == 0)
      n = ulbn_rnorm(op, n - 1);
  } else {
    if(idx >= n) {
      op = _ulbi_res(alloc, o, idx + 1);
      ULBN_RETURN_IF_ALLOC_FAILED(op, ULBN_ERR_NOMEM);
      ulbn_fill0(op + n, idx - n);
      op[idx] = ULBN_LIMB_SHL(1, shift);
      n = idx + 1;
      ULBI_RETURN_IF_SSIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
    } else {
      op = _ulbi_res(alloc, o, n + 1);
      op[n] = ulbn_add1(op + idx, op + idx, n - idx, ULBN_LIMB_SHL(1, shift));
      if(op[n] != 0) {
        ++n;
        ULBI_RETURN_IF_SSIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
      }
    }
  }
  o->len = _ulbi_make_ssize(o->len >= 0, n);
  return 1;
}

ULBN_PUBLIC int ulbi_testbit_bits(const ulbi_t* o, ulbn_bits_t k) {
  const ulbn_bits_t idx = k / ULBN_LIMB_BITS;
  #if ULBN_BITS_MAX > ULBN_USIZE_MAX
  if(ul_unlikely(idx > ULBN_USIZE_MAX))
    return o->len >= 0 ? 0 : 1;
  #endif
  return _ulbi_testbit(o, ulbn_cast_usize(idx), ulbn_cast_int(k % ULBN_LIMB_BITS));
}
ULBN_PUBLIC int ulbi_setbit_bits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_bits_t k) {
  const ulbn_bits_t idx = k / ULBN_LIMB_BITS;
  const int shift = ulbn_cast_int(k % ULBN_LIMB_BITS);
  #if ULBN_BITS_MAX > ULBN_USIZE_MAX
  if(ul_unlikely(idx > ULBN_USIZE_MAX))
    return o->len >= 0 ? ULBN_ERR_EXCEED_RANGE : 1;
  #endif
  if(_ulbi_testbit(o, ulbn_cast_usize(idx), shift))
    return 1;
  if(ul_unlikely(ulbn_cast_usize(idx) > ULBI_SSIZE_LIMIT - (o->len >= 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_setbit(alloc, o, ulbn_cast_usize(idx), shift);
}
ULBN_PUBLIC int ulbi_resetbit_bits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_bits_t k) {
  const ulbn_bits_t idx = k / ULBN_LIMB_BITS;
  const int shift = ulbn_cast_int(k % ULBN_LIMB_BITS);
  #if ULBN_BITS_MAX > ULBN_USIZE_MAX
  if(ul_unlikely(idx > ULBN_USIZE_MAX))
    return o->len >= 0 ? 0 : ULBN_ERR_EXCEED_RANGE;
  #endif
  if(!_ulbi_testbit(o, ulbn_cast_usize(idx), shift))
    return 0;
  if(ul_unlikely(ulbn_cast_usize(idx) > ULBI_SSIZE_LIMIT - (o->len < 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_resetbit(alloc, o, ulbn_cast_usize(idx), shift);
}
ULBN_PUBLIC int ulbi_combit_bits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_bits_t k) {
  const ulbn_bits_t idx = k / ULBN_LIMB_BITS;
  const int shift = ulbn_cast_int(k % ULBN_LIMB_BITS);
  if(ul_unlikely(idx > ULBI_SSIZE_LIMIT - 1))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_testbit(o, ulbn_cast_usize(idx), shift) ? _ulbi_resetbit(alloc, o, ulbn_cast_usize(idx), shift)
                                                       : _ulbi_setbit(alloc, o, ulbn_cast_usize(idx), shift);
}

ULBN_PUBLIC int ulbi_testbit_sbits(const ulbi_t* o, ulbn_sbits_t k) {
  if(ul_unlikely(k < 0))
    return 0;
  return ulbi_testbit_bits(o, ulbn_from_pos_sbits(k));
}
ULBN_PUBLIC int ulbi_setbit_sbits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_sbits_t k) {
  if(ul_unlikely(k < 0))
    return ULBN_ERR_INEXACT;
  return ulbi_setbit_bits(alloc, o, ulbn_from_pos_sbits(k));
}
ULBN_PUBLIC int ulbi_resetbit_sbits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_sbits_t k) {
  if(ul_unlikely(k < 0))
    return 0;
  return ulbi_resetbit_bits(alloc, o, ulbn_from_pos_sbits(k));
}
ULBN_PUBLIC int ulbi_combit_sbits(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_sbits_t k) {
  if(ul_unlikely(k < 0))
    return ULBN_ERR_INEXACT;
  return ulbi_combit_bits(alloc, o, ulbn_from_pos_sbits(k));
}

ULBN_PUBLIC int ulbi_testbit(const ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return 0;
  shift = ulbn_to_bit_info(_ulbi_limbs(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return o->len >= 0 ? 0 : 1;
  return _ulbi_testbit(o, idx, shift);
}
ULBN_PUBLIC int ulbi_setbit(const ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return ULBN_ERR_INEXACT;
  shift = ulbn_to_bit_info(_ulbi_limbs(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return o->len >= 0 ? ULBN_ERR_EXCEED_RANGE : 1;
  if(_ulbi_testbit(o, idx, shift))
    return 1;
  if(ul_unlikely(idx > ULBI_SSIZE_LIMIT - (o->len >= 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_setbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_resetbit(const ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return 0;
  shift = ulbn_to_bit_info(_ulbi_limbs(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return o->len >= 0 ? 0 : ULBN_ERR_EXCEED_RANGE;
  if(!_ulbi_testbit(o, idx, shift))
    return 0;
  if(ul_unlikely(idx > ULBI_SSIZE_LIMIT - (o->len < 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_resetbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_combit(const ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return ULBN_ERR_INEXACT;
  shift = ulbn_to_bit_info(_ulbi_limbs(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return ULBN_ERR_EXCEED_RANGE;
  if(ul_unlikely(idx > ULBI_SSIZE_LIMIT - 1))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_testbit(o, idx, shift) ? _ulbi_resetbit(alloc, o, idx, shift) : _ulbi_setbit(alloc, o, idx, shift);
}


ULBN_PUBLIC int ulbi_is_2pow(const ulbi_t* o) {
  return ulbn_is_2pow(_ulbi_limbs(o), _ulbi_abs_size(o->len));
}
ULBN_PUBLIC ulbn_bits_t ulbi_ctz(const ulbi_t* ro) {
  return ulbn_ctz(_ulbi_limbs(ro), _ulbi_abs_size(ro->len));
}
ULBN_PUBLIC ulbn_bits_t ulbi_cto(const ulbi_t* ro) {
  return ulbn_cto(_ulbi_limbs(ro), _ulbi_abs_size(ro->len));
}
ULBN_PUBLIC ulbn_bits_t ulbi_abs_popcount(const ulbi_t* ro) {
  return ulbn_popcount(_ulbi_limbs(ro), _ulbi_abs_size(ro->len));
}
ULBN_PUBLIC ulbn_bits_t ulbi_abs_bit_width(const ulbi_t* ro) {
  const ulbn_usize_t n = _ulbi_abs_size(ro->len);
  return n ? ulbn_bit_width(_ulbi_limbs(ro), n) : 0;
}

/**********************
 * <ulbi> Power, Root *
 **********************/

ULBN_PUBLIC int ulbi_pow_ulong(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ulong_t b) {
  ulbi_t B = ULBI_INIT, ta = ULBI_INIT;
  int err;

  if(ul_unlikely(ro == ao)) {
    err = ulbi_init_copy(alloc, &ta, ao);
    ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
    ao = &ta;
  }
  ulbi_set_limb(ro, 1);
  err = ulbi_set_copy(alloc, &B, ao);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);

  while(b) {
    if(b & 1) {
      err = ulbi_mul(alloc, ro, ro, &B);
      ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    }
    err = ulbi_mul(alloc, &B, &B, &B);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    b >>= 1;
  }

cleanup:
  ulbi_deinit(alloc, &B);
  ulbi_deinit(alloc, &ta);
  return err;
}
ULBN_PUBLIC int ulbi_pow_slong(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slong_t b) {
  if(ao->len == 0) {
    _ulbi_set_zero(ro);
    return ul_unlikely(b < 0) ? ULBN_ERR_DIV_BY_ZERO : 0;
  }
  if(ul_unlikely(b < 0)) {
    _ulbi_set_zero(ro);
    return ULBN_ERR_INEXACT;
  }
  return ulbi_pow_ulong(alloc, ro, ao, ulbn_from_pos_slong(b));
}
ULBN_PUBLIC int ulbi_pow(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbi_t B = ULBI_INIT, ta = ULBI_INIT;
  int err;
  ulbn_limb_t l;
  const ulbn_limb_t* p;
  ulbn_usize_t i = 0, n;
  unsigned j;

  if(ao->len == 0) {
    _ulbi_set_zero(ro);
    return ul_unlikely(b->len < 0) ? ULBN_ERR_DIV_BY_ZERO : 0;
  }
  if(ul_unlikely(b->len < 0)) {
    _ulbi_set_zero(ro);
    return ULBN_ERR_INEXACT;
  }

  if(ul_unlikely(ro == ao)) {
    err = ulbi_init_copy(alloc, &ta, ao);
    ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
    ao = &ta;
  }
  ulbi_set_limb(ro, 1);
  err = ulbi_set_copy(alloc, &B, ao);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);

  n = ulbn_cast_usize(b->len);
  p = _ulbi_limbs(b);
  if(ul_likely(n)) {
    while(i + 1 < n) {
      l = p[i++];
      j = ulbn_cast_uint(ULBN_LIMB_BITS);
      while(j--) {
        if(l & 1) {
          err = ulbi_mul(alloc, ro, ro, &B);
          ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
        }
        err = ulbi_mul(alloc, &B, &B, &B);
        ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
        l >>= 1;
      }
    }
    l = p[i++];
    while(l) {
      if(l & 1) {
        err = ulbi_mul(alloc, ro, ro, &B);
        ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
      }
      err = ulbi_mul(alloc, &B, &B, &B);
      ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
      l >>= 1;
    }
  }

cleanup:
  ulbi_deinit(alloc, &B);
  ulbi_deinit(alloc, &ta);
  return err;
}


ULBN_PUBLIC int ulbi_sqrtrem(const ulbn_alloc_t* alloc, ulbi_t* so, ulbi_t* ro, const ulbi_t* ao) {
  ulbn_limb_t *sp = ul_nullptr, *rp = ul_nullptr;
  ulbn_usize_t n;
  int err;

  if(ao->len == 0) {
    _ulbi_may_set_zero(so);
    _ulbi_may_set_zero(ro);
    return 0;
  }
  if(ao->len < 0) {
    _ulbi_may_set_zero(so);
    _ulbi_may_set_zero(ro);
    return ULBN_ERR_INVALID;
  }

  n = ulbn_cast_usize(ao->len);
  if(so) {
    sp = _ulbi_res(alloc, so, n - (n >> 1));
    ULBN_RETURN_IF_ALLOC_FAILED(sp, ULBN_ERR_NOMEM);
  }
  if(ro) {
    rp = _ulbi_res(alloc, ro, (n >> 1) + 1u);
    ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  }

  err = ulbn_sqrtrem_guard(alloc, sp, rp, _ulbi_limbs(ao), n);
  if(so)
    so->len = ulbn_cast_ssize(ulbn_rnorm(sp, n - (n >> 1)));
  if(ro)
    ro->len = ulbn_cast_ssize(ulbn_rnorm(rp, (n >> 1) + 1u));
  return err;
}
ULBN_PUBLIC int ulbi_sqrt(const ulbn_alloc_t* alloc, ulbi_t* so, const ulbi_t* ao) {
  return ulbi_sqrtrem(alloc, so, ul_nullptr, ao);
}
ULBN_PUBLIC int ulbi_rootrem(const ulbn_alloc_t* alloc, ulbi_t* so, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* eo) {
  ulbi_t eo_n1 = ULBI_INIT;
  ulbi_t xo = ULBI_INIT, yo = ULBI_INIT, to = ULBI_INIT;
  int err, cy;
  const int sign = ao->len < 0;

  /*
    Newton's method:
    f(x) = x^e - a
    f'(x) = e * x^(e-1)
    x' = x - f(x)/f'(x) = x - (x^e - a)/(e * x^(e - 1)) = ((e-1)*x + a/x^(e-1)) / e
  */

  if(eo->len == 0) {
    _ulbi_may_set_zero(so);
    _ulbi_may_set_zero(ro);
    return ULBN_ERR_INVALID;
  }
  if(ao->len == 0) {
    _ulbi_may_set_zero(so);
    _ulbi_may_set_zero(ro);
    return eo->len > 0 ? 0 : ULBN_ERR_DIV_BY_ZERO;
  }
  if(ao->len < 0 && ulbi_is_even(eo)) {
    _ulbi_may_set_zero(so);
    _ulbi_may_set_zero(ro);
    return ULBN_ERR_INVALID;
  }
  if(ao->len == 1 && _ulbi_limbs(ao)[0] == 1) {
    if(so)
      ulbi_set_slimb(so, ao->len > 0 ? 1 : -1);
    _ulbi_may_set_zero(ro);
    return 0;
  }
  if(eo->len == 1) {
    if(_ulbi_limbs(eo)[0] == 1) {
      err = so ? ulbi_set_copy(alloc, so, ao) : 0;
      _ulbi_may_set_zero(ro);
      return err;
    }
    if(_ulbi_limbs(eo)[0] == 2)
      return ulbi_sqrtrem(alloc, so, ro, ao);
  }
  if(eo->len < 0) {
    _ulbi_may_set_zero(so);
    err = ro ? ulbi_set_copy(alloc, ro, ao) : ULBN_ERR_INEXACT;
    return err;
  }

  /* e_n1 = e - 1, x = 2 ** (ceil(bits_width(a) / e) + 1) */
  err = ulbi_sub_limb(alloc, &eo_n1, eo, 1);
  ulbn_assert(err != ULBN_ERR_EXCEED_RANGE);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  ulbi_set_ulong(&yo, ulbi_abs_bit_width(ao));
  cy = ulbi_divmod(alloc, &yo, ul_nullptr, &yo, eo);
  ULBN_DO_IF_ALLOC_COND(cy < 0, goto cleanup;);
  err = ulbi_add_limb(alloc, &yo, &yo, ulbn_cast_limb(1 + (cy == ULBN_ERR_INEXACT)));
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
  err = ulbi_set_2exp(alloc, &xo, &yo);
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);

  ulbi_set_limb(&yo, 1);
  while(ulbi_comp(&xo, &yo) > 0) {
    /* x = (x * (e - 1) + y) / e */
    /* y = abs(a) / (x ** (e - 1)) */
    err = ulbi_mul(alloc, &xo, &xo, &eo_n1);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    err = ulbi_add(alloc, &xo, &xo, &yo);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    err = ulbi_divmod(alloc, &xo, ul_nullptr, &xo, eo);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    err = ulbi_pow(alloc, &to, &xo, &eo_n1);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    err = _ulbi_divmod(alloc, &yo, ul_nullptr, ao, _ulbi_abs_size(ao->len), 1, &to, ulbn_cast_usize(to.len), 1);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  }

  ulbn_assert(!ulbi_eq_limb(&xo, 0));
  if(sign)
    xo.len = -xo.len;
  err = ulbi_mul(alloc, &to, &to, &xo);
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
  if(ro) {
    err = ulbi_sub(alloc, ro, ao, &to);
    ulbn_assert(err != ULBN_ERR_EXCEED_RANGE);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  } else
    err = ulbi_eq(&to, ao) ? 0 : ULBN_ERR_INEXACT;
  if(so)
    ulbi_swap(so, &xo);

cleanup:
  ulbi_deinit(alloc, &eo_n1);
  ulbi_deinit(alloc, &xo);
  ulbi_deinit(alloc, &yo);
  ulbi_deinit(alloc, &to);
  return err;
}
ULBN_PUBLIC int ulbi_root(const ulbn_alloc_t* alloc, ulbi_t* so, const ulbi_t* ao, const ulbi_t* eo) {
  return ulbi_rootrem(alloc, so, ul_nullptr, ao, eo);
}

/*******************************************
 * <ulbi> Conversion to fixed-bits integer *
 *******************************************/

ULBN_PRIVATE int _ulbi_as_uint(
  const ulbn_alloc_t* alloc, ulbi_t* ro,                      /* */
  const ulbi_t* ao, ulbn_usize_t idx, int shift, int need_com /* */
) {
  const ulbn_usize_t n_desire = idx + (shift != 0);
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);
  ulbn_limb_t* rp;
  ulbn_usize_t rn;

  rn = _ulbn_min_(an, n_desire);
  if(!need_com) {
    const ulbn_limb_t* ap;
    rp = _ulbi_res(alloc, ro, rn);
    ULBN_RETURN_IF_ALLOC_COND(rn != 0 && rp == ul_nullptr, ULBN_ERR_NOMEM);
    ap = _ulbi_limbs(ao);
    if(ap != rp)
      ulbn_copy(rp, ap, rn);
  } else {
    rp = _ulbi_res(alloc, ro, n_desire);
    ULBN_RETURN_IF_ALLOC_COND(n_desire != 0 && rp == ul_nullptr, ULBN_ERR_NOMEM);
    ulbn_neg(rp, _ulbi_limbs(ao), rn, 1);
    if(an < n_desire) {
      ulbn_fill1(rp + an, n_desire - an);
      goto fix_bits;
    }
  }

  if(an >= n_desire) {
  fix_bits:
    if(shift != 0)
      rp[idx] &= ULBN_LIMB_SHL(1, shift) - 1;
    rn = ulbn_rnorm(rp, n_desire);
  }

  ULBI_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = ulbn_cast_ssize(rn);
  return 0;
}
ULBN_PRIVATE int _ulbi_as_int(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t idx, int shift) {
  const ulbn_limb_t* ap;
  int err, positive, need_com;

  positive = (_ulbi_testbit(ao, idx, shift) == 0);
  ap = _ulbi_limbs(ao);
  if(ul_unlikely(!positive && idx < _ulbi_abs_size(ao->len))) {
    const ulbn_limb_t mask = ULBN_LIMB_SHL(1u, shift);
    if(ul_unlikely((ap[idx] & (ulbn_cast_limb(mask << 1u) - 1u)) == mask) && ulbn_is0(ap, idx)) {
      ulbn_limb_t* rp;
      if(ul_unlikely(idx > ULBI_SSIZE_LIMIT - 1))
        return ULBN_ERR_EXCEED_RANGE;
      rp = _ulbi_res(alloc, ro, idx + 1);
      ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
      ulbn_fill0(rp, idx);
      rp[idx] = ULBN_LIMB_SHL(1u, shift);
      ro->len = -ulbn_cast_ssize(idx + 1);
      return 0;
    }
  }

  need_com = (positive != (ao->len >= 0));
  if(ul_unlikely(need_com && idx > ULBI_SSIZE_LIMIT - (shift != 0)))
    return ULBN_ERR_EXCEED_RANGE;
  err = _ulbi_as_uint(alloc, ro, ao, idx, shift, positive ^ (ao->len >= 0));
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  ro->len = _ulbi_make_ssize(positive, ro->len);
  return err;
}

ULBN_PUBLIC int ulbi_as_uint_usize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  return _ulbi_as_uint(alloc, ro, ao, b / ULBN_LIMB_BITS, ulbn_cast_int(b % ULBN_LIMB_BITS), ao->len < 0);
}
ULBN_PUBLIC int ulbi_as_int_usize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  if(ul_unlikely(b == 0)) {
    _ulbi_set_zero(ro);
    return 0;
  }
  return _ulbi_as_int(alloc, ro, ao, (b - 1) / ULBN_LIMB_BITS, ulbn_cast_int((b - 1) % ULBN_LIMB_BITS));
}

ULBN_PUBLIC int ulbi_as_uint_ssize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t b) {
  if(ul_unlikely(b < 0))
    return ULBN_ERR_BAD_ARGUMENT;
  return ulbi_as_uint_usize(alloc, ro, ao, ulbn_cast_usize(b));
}
ULBN_PUBLIC int ulbi_as_int_ssize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t b) {
  if(ul_unlikely(b < 0))
    return ULBN_ERR_BAD_ARGUMENT;
  return ulbi_as_int_usize(alloc, ro, ao, ulbn_cast_usize(b));
}

ULBN_PUBLIC int ulbi_as_uint_bits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_bits_t b) {
  ulbn_bits_t idx = b / ULBN_LIMB_BITS;
  const int shift = ulbn_cast_int(b % ULBN_LIMB_BITS);
  #if ULBN_BITS_MAX > ULBN_USIZE_MAX
  if(ul_unlikely(idx > ULBN_USIZE_MAX))
    idx = ULBN_USIZE_MAX;
  #endif
  if(ul_unlikely(ao->len < 0 && idx > ULBI_SSIZE_LIMIT - (shift != 0)))
    return ULBN_ERR_BAD_ARGUMENT;
  return _ulbi_as_uint(alloc, ro, ao, ulbn_cast_usize(idx), shift, ao->len < 0);
}
ULBN_PUBLIC int ulbi_as_int_bits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_bits_t b) {
  ulbn_bits_t idx;
  int shift;

  if(ul_unlikely(b == 0)) {
    _ulbi_set_zero(ro);
    return 0;
  }
  idx = b / ULBN_LIMB_BITS;
  shift = ulbn_cast_int(b % ULBN_LIMB_BITS);
  #if ULBN_BITS_MAX > ULBN_USIZE_MAX
  if(ul_unlikely(idx > ULBN_USIZE_MAX))
    idx = ULBN_USIZE_MAX;
  #endif
  if(shift == 0) {
    --idx;
    shift = ulbn_cast_int(ULBN_LIMB_BITS) - 1;
  } else
    --shift;
  return _ulbi_as_int(alloc, ro, ao, ulbn_cast_usize(idx), shift);
}

ULBN_PUBLIC int ulbi_as_uint_sbits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_sbits_t b) {
  if(ul_unlikely(b < 0))
    return ULBN_ERR_BAD_ARGUMENT;
  return ulbi_as_uint_bits(alloc, ro, ao, ulbn_from_pos_sbits(b));
}
ULBN_PUBLIC int ulbi_as_int_sbits(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_sbits_t b) {
  if(ul_unlikely(b < 0))
    return ULBN_ERR_BAD_ARGUMENT;
  return ulbi_as_int_bits(alloc, ro, ao, ulbn_from_pos_sbits(b));
}

ULBN_PUBLIC int ulbi_as_uint(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbn_usize_t idx;
  int shift;
  if(b->len < 0)
    return ULBN_ERR_BAD_ARGUMENT;
  shift = ulbn_to_bit_info(_ulbi_limbs(b), ulbn_cast_usize(b->len), &idx);
  if(ul_unlikely(shift < 0)) {
    idx = ULBN_USIZE_MAX;
    shift = 0;
  }
  if(ul_unlikely(ao->len < 0 && idx > ULBI_SSIZE_LIMIT - (shift != 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_as_uint(alloc, ro, ao, idx, shift, ao->len < 0);
}
ULBN_PUBLIC int ulbi_as_int(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbn_usize_t idx;
  int shift;
  if(b->len < 0)
    return ULBN_ERR_BAD_ARGUMENT;
  if(ul_unlikely(b->len == 0)) {
    _ulbi_set_zero(ro);
    return 0;
  }
  shift = ulbn_to_bit_info(_ulbi_limbs(b), ulbn_cast_usize(b->len), &idx);
  if(ul_unlikely(shift < 0)) {
    idx = ULBN_USIZE_MAX;
    shift = 0;
  }
  if(shift == 0) {
    --idx;
    shift = ulbn_cast_int(ULBN_LIMB_BITS) - 1;
  } else
    --shift;
  return _ulbi_as_int(alloc, ro, ao, idx, shift);
}

/************************************
 * <ulbi> Conversion to other types *
 ************************************/

ULBN_PUBLIC ulbn_limb_t ulbi_to_limb(const ulbi_t* src) {
  if(src->len == 0)
    return 0;
  return src->len > 0 ? _ulbi_limbs(src)[0] : ulbn_cast_limb(0u - _ulbi_limbs(src)[0]);
}
ULBN_PUBLIC ulbn_slimb_t ulbi_to_slimb(const ulbi_t* src) {
  const union {
    ulbn_limb_t ul;
    ulbn_slimb_t sl;
  } u = { ulbi_to_limb(src) };
  return u.sl;
}

ULBN_PRIVATE ulbn_ulong_t _ulbi_to_ulong(const ulbi_t* src) {
  #if ULBN_LIMB_MAX >= ULBN_ULONG_MAX
  return src->len != 0 ? ulbn_cast_ulong(_ulbi_limbs(src)[0]) : 0u;
  #else
  static ul_constexpr const ulbn_usize_t N_LIMIT = (ULBN_ULONG_BITS + ULBN_LIMB_BITS - 1) / ULBN_LIMB_BITS;
  ulbn_usize_t n = _ulbi_abs_size(src->len);
  const ulbn_limb_t* p = _ulbi_limbs(src);
  ulbn_usize_t i;
  ulbn_ulong_t r;

  if(n == 0)
    return 0u;
  n = _ulbn_min_(n, N_LIMIT);
  r = p[n - 1];
  for(i = n - 1; i > 0; --i)
    r = (r << ULBN_LIMB_BITS) | p[i - 1];
  return r;
  #endif
}
ULBN_PUBLIC ulbn_ulong_t ulbi_to_ulong(const ulbi_t* src) {
  const ulbn_ulong_t x = _ulbi_to_ulong(src);
  return src->len >= 0 ? x : 0u - x;
}
ULBN_PUBLIC ulbn_slong_t ulbi_to_slong(const ulbi_t* src) {
  const union {
    ulbn_ulong_t ul;
    ulbn_slong_t sl;
  } u = { ulbi_to_ulong(src) };
  return u.sl;
}


ULBN_PUBLIC int ulbi_fit_limb(const ulbi_t* src) {
  return src->len == 0 || src->len == 1;
}
ULBN_PUBLIC int ulbi_fit_slimb(const ulbi_t* src) {
  if(src->len > 1 || src->len < -1)
    return 0;
  if(src->len == 0)
    return 1;
  #if ULBN_SLIMB_MIN == -ULBN_SLIMB_MAX
  return _ulbi_limbs(src)[0] < ULBN_LIMB_SIGNBIT;
  #else
  return _ulbi_limbs(src)[0] < ULBN_LIMB_SIGNBIT + (src->len == -1);
  #endif
}
ULBN_PUBLIC int ulbi_fit_ulong(const ulbi_t* src) {
  return src->len >= 0 && ulbi_abs_bit_width(src) <= ULBN_ULONG_BITS;
}
ULBN_PUBLIC int ulbi_fit_slong(const ulbi_t* src) {
  const ulbn_bits_t r = ulbi_abs_bit_width(src);
  #if ULBN_SLONG_MIN == -ULBN_SLONG_MAX
  return r < sizeof(ulbn_slong_t) * CHAR_BIT;
  #else
  if(ul_likely(r < sizeof(ulbn_slong_t) * CHAR_BIT))
    return 1;
  return r == sizeof(ulbn_slong_t) * CHAR_BIT && src->len < 0 && ulbi_is_2pow(src) != 0;
  #endif
}


  #if ULBN_CONF_HAS_FLOAT
ULBN_PRIVATE int _ulbn_feqf(float a, float b) {
  return a >= b && a <= b;
}
ULBN_PUBLIC int ulbi_set_float(const ulbn_alloc_t* alloc, ulbi_t* dst, float x) {
  static ul_constexpr const float B = ul_static_cast(float, _ULBN_LIMB_SIGNBIT) * 2.0F;
  static ul_constexpr const float Bi = 1.0F / (ul_static_cast(float, _ULBN_LIMB_SIGNBIT) * 2.0F);
  ulbn_usize_t rn;
  ulbn_limb_t* rp;
  float xl;
  int positive;

  /* NaN, +Inf, -Inf or 0 */
  if(x != x || _ulbn_feqf(x, x * 0.5F)) {
    _ulbi_set_zero(dst);
    return _ulbn_feqf(x, 0.0F) ? 0 : ULBN_ERR_INVALID;
  }
  positive = x >= 0.0F;
  if(!positive)
    x = -x;
  if(x < 1.0F) {
    _ulbi_set_zero(dst);
    return ULBN_ERR_INEXACT;
  }
  for(rn = 1; x >= B; ++rn)
    x *= Bi;
  ULBI_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);

  rp = _ulbi_res(alloc, dst, rn);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  dst->len = _ulbi_make_ssize(positive, rn);
  while(rn) {
    #ifdef HUGE_VALF /* we guess that `floorf` exists when `HUGE_VALF` exists */
    xl = floorf(x);
    #else
    xl = ul_static_cast(float, floor(x));
    #endif
    x -= xl;
    rp[--rn] = ulbn_cast_limb(xl);
    x = B * x;
  }
  return x <= 0.0F ? 0 : ULBN_ERR_INEXACT;
}
ULBN_PUBLIC int ulbi_init_float(const ulbn_alloc_t* alloc, ulbi_t* dst, float x) {
  return ulbi_set_float(alloc, ulbi_init(dst), x);
}
ULBN_PUBLIC float ulbi_to_float(const ulbi_t* src) {
  static ul_constexpr const float B = ul_static_cast(float, _ULBN_LIMB_SIGNBIT) * 2.0F;
  const ulbn_usize_t n = _ulbi_abs_size(src->len);
  const ulbn_limb_t* p = _ulbi_limbs(src);
  float r;
  ulbn_usize_t i = n;

  if(n == 0)
    return 0.0F;
  r = ul_static_cast(float, p[--i]);
  while(i > 0)
    r = r * B + ul_static_cast(float, p[--i]);
  return src->len >= 0 ? r : -r;
}
ULBN_PUBLIC int ulbi_fit_float(const ulbi_t* src) {
  const ulbn_bits_t bits = ulbi_abs_bit_width(src);
  const ulbn_bits_t ctz = ulbi_ctz(src);
  return bits <= FLT_MAX_EXP && bits - ctz <= FLT_MANT_DIG;
}
  #endif /* ULBN_CONF_HAS_FLOAT */


  #if ULBN_CONF_HAS_DOUBLE
ULBN_PRIVATE int _ulbn_feq(double a, double b) {
  return a >= b && a <= b;
}
ULBN_PUBLIC int ulbi_set_double(const ulbn_alloc_t* alloc, ulbi_t* dst, double x) {
  static ul_constexpr const double B = ul_static_cast(double, _ULBN_LIMB_SIGNBIT) * 2.0;
  static ul_constexpr const double Bi = 1.0 / (ul_static_cast(double, _ULBN_LIMB_SIGNBIT) * 2.0);
  ulbn_usize_t rn;
  ulbn_limb_t* rp;
  double xl;
  int positive;

  /* NaN, +Inf, -Inf or 0 */
  if(x != x || _ulbn_feq(x, x * 0.5)) {
    _ulbi_set_zero(dst);
    return _ulbn_feq(x, 0.0) ? 0 : ULBN_ERR_INVALID;
  }
  positive = x >= 0.0;
  if(!positive)
    x = -x;
  if(x < 1.0) {
    _ulbi_set_zero(dst);
    return ULBN_ERR_INEXACT;
  }
  for(rn = 1; x >= B; ++rn)
    x *= Bi;
  ULBI_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);

  rp = _ulbi_res(alloc, dst, rn);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  dst->len = _ulbi_make_ssize(positive, rn);
  while(rn) {
    xl = floor(x);
    x -= xl;
    rp[--rn] = ulbn_cast_limb(xl);
    x = B * x;
  }
  return x <= 0 ? 0 : ULBN_ERR_INEXACT;
}
ULBN_PUBLIC int ulbi_init_double(const ulbn_alloc_t* alloc, ulbi_t* dst, double x) {
  return ulbi_set_double(alloc, ulbi_init(dst), x);
}
ULBN_PUBLIC double ulbi_to_double(const ulbi_t* src) {
  static ul_constexpr const double B = ul_static_cast(double, _ULBN_LIMB_SIGNBIT) * 2.0;
  const ulbn_usize_t n = _ulbi_abs_size(src->len);
  const ulbn_limb_t* p = _ulbi_limbs(src);
  double r;
  ulbn_usize_t i = n;

  if(n == 0)
    return 0.0;
  r = ul_static_cast(double, p[--i]);
  while(i > 0)
    r = r * B + ul_static_cast(double, p[--i]);
  return src->len >= 0 ? r : -r;
}
ULBN_PUBLIC int ulbi_fit_double(const ulbi_t* src) {
  const ulbn_bits_t bits = ulbi_abs_bit_width(src);
  const ulbn_bits_t ctz = ulbi_ctz(src);
  return bits <= DBL_MAX_EXP && bits - ctz <= DBL_MANT_DIG;
}
  #endif /* ULBN_CONF_HAS_DOUBLE */


  #if ULBN_CONF_HAS_LONG_DOUBLE
ULBN_PRIVATE int _ulbn_feql(long double a, long double b) {
  return a >= b && a <= b;
}
ULBN_PUBLIC int ulbi_set_long_double(const ulbn_alloc_t* alloc, ulbi_t* dst, long double x) {
  static ul_constexpr const long double B = ul_static_cast(long double, _ULBN_LIMB_SIGNBIT) * 2.0L;
  static ul_constexpr const long double Bi = 1.0L / (ul_static_cast(long double, _ULBN_LIMB_SIGNBIT) * 2.0L);
  ulbn_usize_t rn;
  ulbn_limb_t* rp;
  long double xl;
  int positive;

  /* NaN, +Inf, -Inf or 0 */
  if(x != x || _ulbn_feql(x, x * 0.5L)) {
    _ulbi_set_zero(dst);
    return _ulbn_feql(x, 0.0L) ? 0 : ULBN_ERR_INVALID;
  }
  positive = x >= 0.0L;
  if(!positive)
    x = -x;
  if(x < 1.0L) {
    _ulbi_set_zero(dst);
    return ULBN_ERR_INEXACT;
  }
  for(rn = 1; x >= B; ++rn)
    x *= Bi;
  ULBI_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);

  rp = _ulbi_res(alloc, dst, rn);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  dst->len = _ulbi_make_ssize(positive, rn);
  while(rn) {
    xl = floorl(x);
    x -= xl;
    rp[--rn] = ulbn_cast_limb(xl);
    x = B * x;
  }
  return x <= 0.0L ? 0 : ULBN_ERR_INEXACT;
}
ULBN_PUBLIC int ulbi_init_long_double(const ulbn_alloc_t* alloc, ulbi_t* dst, long double x) {
  return ulbi_set_long_double(alloc, ulbi_init(dst), x);
}
ULBN_PUBLIC long double ulbi_to_long_double(const ulbi_t* src) {
  static ul_constexpr const long double B = ul_static_cast(long double, _ULBN_LIMB_SIGNBIT) * 2.0L;
  const ulbn_usize_t n = _ulbi_abs_size(src->len);
  const ulbn_limb_t* p = _ulbi_limbs(src);
  long double r;
  ulbn_usize_t i = n;

  if(n == 0)
    return 0.0L;
  r = ul_static_cast(long double, p[--i]);
  while(i > 0)
    r = r * B + ul_static_cast(long double, p[--i]);
  return src->len >= 0 ? r : -r;
}
ULBN_PUBLIC int ulbi_fit_long_double(const ulbi_t* src) {
  const ulbn_bits_t bits = ulbi_abs_bit_width(src);
  const ulbn_bits_t ctz = ulbi_ctz(src);
  return bits <= LDBL_MAX_EXP && bits - ctz <= LDBL_MANT_DIG;
}
  #endif /* ULBN_CONF_HAS_LONG_DOUBLE */

/******************************
 * <ulbi> Conversion to bytes *
 ******************************/

ULBN_PRIVATE void _ulbi_to_bytes_pos_le(unsigned char* dst, size_t size, const ulbn_limb_t* limb, ulbn_usize_t len) {
  #if ULBN_LIMB_MAX == UCHAR_MAX || (defined(UL_ENDIAN_LITTLE) && !defined(UL_ENDIAN_BIG))
  ulbn_assert(ul_static_cast(size_t, len) <= _ULBN_SIZET_MAX / sizeof(ulbn_limb_t));
  if(size <= len * sizeof(ulbn_limb_t)) {
    memcpy(dst, limb, size);
  } else {
    memcpy(dst, limb, len * sizeof(ulbn_limb_t));
    memset(dst + len * sizeof(ulbn_limb_t), 0, size - len * sizeof(ulbn_limb_t));
  }
  #else
  ulbn_limb_t l;
  size_t t;

  ulbn_assert(ul_static_cast(size_t, len) <= _ULBN_SIZET_MAX / sizeof(ulbn_limb_t));
  while(len-- != 0) {
    l = *limb++;
    t = _ulbn_min_(sizeof(ulbn_limb_t), size);
    size -= t;
    while(t-- != 0) {
      *dst++ = ul_static_cast(unsigned char, l);
      l >>= CHAR_BIT;
    }
    if(size == 0)
      return;
  }
  memset(dst, 0, size);
  #endif
}
ULBN_PRIVATE void _ulbi_to_bytes_pos_be(unsigned char* dst, size_t size, const ulbn_limb_t* limb, ulbn_usize_t len) {
  size_t t;
  ulbn_limb_t l;

  ulbn_assert(ul_static_cast(size_t, len) <= _ULBN_SIZET_MAX / sizeof(ulbn_limb_t));
  dst += size;
  while(len-- != 0) {
    l = *limb++;
    t = _ulbn_min_(sizeof(ulbn_limb_t), size);
    size -= t;
  #if ULBN_LIMB_MAX == UCHAR_MAX
    *--dst = ul_static_cast(unsigned char, l);
  #else
    while(t-- != 0) {
      *--dst = ul_static_cast(unsigned char, l);
      l >>= CHAR_BIT;
    }
  #endif
    if(size == 0)
      return;
  }
  dst -= size;
  memset(dst, 0, size);
}

ULBN_PRIVATE void _ulbi_to_bytes_neg_le(unsigned char* dst, size_t size, const ulbn_limb_t* limb, ulbn_usize_t len) {
  ulbn_limb_t l;
  size_t t = 0;

  ulbn_assert(ul_static_cast(size_t, len) <= _ULBN_SIZET_MAX / sizeof(ulbn_limb_t));
  while(*limb == 0) {
    t += sizeof(ulbn_limb_t);
    --len;
    ++limb;
  }
  ulbn_assert(len > 0);
  t = _ulbn_min_(t, size);
  size -= t;
  memset(dst, 0, t);
  if(size == 0)
    return;
  dst += t;

  l = _ulbn_neg_(*limb++);
  --len;
  t = _ulbn_min_(size, sizeof(ulbn_limb_t));
  size -= t;
  #if ULBN_LIMB_MAX == UCHAR_MAX
  *dst++ = ul_static_cast(unsigned char, l);
  #else
  while(t-- != 0) {
    *dst++ = ul_static_cast(unsigned char, l);
    l >>= CHAR_BIT;
  }
  #endif
  if(size == 0)
    return;

  while(len-- != 0) {
    l = ulbn_cast_limb(~*limb++);
    t = _ulbn_min_(sizeof(ulbn_limb_t), size);
    size -= t;
  #if ULBN_LIMB_MAX == UCHAR_MAX
    *dst++ = ul_static_cast(unsigned char, l);
  #else
    while(t-- != 0) {
      *dst++ = ul_static_cast(unsigned char, l);
      l >>= CHAR_BIT;
    }
  #endif
    if(size == 0)
      break;
  }

  memset(dst, ulbn_cast_int(UCHAR_MAX), size);
}
ULBN_PRIVATE void _ulbi_to_bytes_neg_be(unsigned char* dst, size_t size, const ulbn_limb_t* limb, ulbn_usize_t len) {
  ulbn_limb_t l;
  size_t t = 0;

  dst += size;

  ulbn_assert(ul_static_cast(size_t, len) <= _ULBN_SIZET_MAX / sizeof(ulbn_limb_t));
  while(*limb == 0) {
    t += sizeof(ulbn_limb_t);
    --len;
    ++limb;
  }
  ulbn_assert(len > 0);
  t = _ulbn_min_(t, size);
  dst -= t;
  size -= t;
  memset(dst, 0, t);
  if(size == 0)
    return;

  l = _ulbn_neg_(*limb++);
  --len;
  t = _ulbn_min_(size, sizeof(ulbn_limb_t));
  size -= t;
  #if ULBN_LIMB_MAX == UCHAR_MAX
  *--dst = ul_static_cast(unsigned char, l);
  #else
  while(t-- != 0) {
    *--dst = ul_static_cast(unsigned char, l);
    l >>= CHAR_BIT;
  }
  #endif
  if(size == 0)
    return;

  while(len-- != 0) {
    l = ulbn_cast_limb(~*limb++);
    t = _ulbn_min_(sizeof(ulbn_limb_t), size);
    size -= t;
  #if ULBN_LIMB_MAX == UCHAR_MAX
    *--dst = ul_static_cast(unsigned char, l);
  #else
    while(t-- != 0) {
      *--dst = ul_static_cast(unsigned char, l);
      l >>= CHAR_BIT;
    }
  #endif
    if(size == 0)
      break;
  }

  dst -= size;
  memset(dst, ulbn_cast_int(UCHAR_MAX), size);
}

ULBN_PUBLIC void ulbi_to_bytes_signed(const ulbi_t* ao, void* dst, size_t size, int is_big_endian) {
  const ulbn_limb_t* ap = _ulbi_limbs(ao);
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);

  if(ao->len >= 0) {
    if(!is_big_endian)
      _ulbi_to_bytes_pos_le(ul_reinterpret_cast(unsigned char*, dst), size, ap, an);
    else
      _ulbi_to_bytes_pos_be(ul_reinterpret_cast(unsigned char*, dst), size, ap, an);
  } else {
    if(!is_big_endian)
      _ulbi_to_bytes_neg_le(ul_reinterpret_cast(unsigned char*, dst), size, ap, an);
    else
      _ulbi_to_bytes_neg_be(ul_reinterpret_cast(unsigned char*, dst), size, ap, an);
  }
}
ULBN_PUBLIC void ulbi_to_bytes_signed_le(const ulbi_t* ao, void* dst, size_t size) {
  const ulbn_limb_t* ap = _ulbi_limbs(ao);
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);

  if(ao->len >= 0)
    _ulbi_to_bytes_pos_le(ul_reinterpret_cast(unsigned char*, dst), size, ap, an);
  else
    _ulbi_to_bytes_neg_le(ul_reinterpret_cast(unsigned char*, dst), size, ap, an);
}
ULBN_PUBLIC void ulbi_to_bytes_signed_be(const ulbi_t* ao, void* dst, size_t size) {
  const ulbn_limb_t* ap = _ulbi_limbs(ao);
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);

  if(ao->len >= 0)
    _ulbi_to_bytes_pos_be(ul_reinterpret_cast(unsigned char*, dst), size, ap, an);
  else
    _ulbi_to_bytes_neg_be(ul_reinterpret_cast(unsigned char*, dst), size, ap, an);
}

  /****************************
   * <ulbi> Base conversation *
   ****************************/

  #if ULBN_CONV2PRINT_GENERIC_THRESHOLD < ULBN_USIZE_MAX
ULBN_PRIVATE int _ulbi_print_ex(
  const ulbn_alloc_t* alloc, ulbn_printer_t* printer, void* opaque, /* */
  ulbi_t* ao, int base, size_t desire_len, const char* char_table   /* */
) {
  /**
   * Fast base conversion algorithm:
   *
   * function baseconv(a, base) {
   *   if(a < base) { return [a]; } // base case (can be optimized with constants)
   *   exp = ceil(log(a, base) / 2); // ceil/floor/round is not important
   *   (q, r) = divmod(a, base**exp);
   *   str1 = baseconv(q, base);
   *   str2 = baseconv(r, base);
   *   return str1 + [0] * (exp - len(str2)) + str2;
   * }
   */

  ulbn_bits_t bits, pow;
  ulbi_t qo = ULBI_INIT, _do = ULBI_INIT;
  int err;

  ulbn_assert(ao->len > 0);
  while(ao->len > ULBN_CONV2PRINT_GENERIC_THRESHOLD) { /* convert the right half recursively into a loop */
    bits = ulbn_bit_width(_ulbi_limbs(ao), ulbn_cast_usize(ao->len));
    pow = ulbn_estimate_conv2_size(bits, base, 0) >> 1;
    if(ul_unlikely(pow >= ULBN_USIZE_MAX))
      return ULBN_ERR_EXCEED_RANGE;
    ulbi_set_limb(&_do, ulbn_cast_limb(base));
    err = ulbi_pow_ulong(alloc, &_do, &_do, pow);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);

    err = ulbi_divmod(alloc, &qo, ao, ao, &_do);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    ulbi_deinit(alloc, &_do);

    err = _ulbi_print_ex(
      alloc, printer, opaque, &qo, base, desire_len > pow ? ul_static_cast(size_t, desire_len - pow) : 0, char_table
    );
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    desire_len = ul_static_cast(size_t, pow);
  }

  if(ao->len != 0) {
    err = ulbn_conv2print_generic(
      alloc, desire_len, printer, opaque, _ulbi_limbs(ao), ulbn_cast_usize(ao->len), char_table, ulbn_cast_limb(base)
    );
  } else
    err = _ulbn_write0(printer, opaque, desire_len);

cleanup:
  ulbi_deinit(alloc, &qo);
  ulbi_deinit(alloc, &_do);
  return err;
}
  #else /* !(ULBN_CONV2PRINT_GENERIC_THRESHOLD < ULBN_USIZE_MAX) */
ULBN_PRIVATE int _ulbi_print_ex(
  const ulbn_alloc_t* alloc, ulbn_printer_t* printer, void* opaque, /* */
  ulbi_t* ao, int base, size_t desire_len, const char* char_table   /* */
) {
  ulbn_assert(desire_len == 0);
  ulbn_assert(ao->len > 0);
  return ulbn_conv2print_generic(
    alloc, desire_len, printer, opaque, _ulbi_limbs(ao), ulbn_cast_usize(ao->len), char_table, ulbn_cast_limb(base)
  );
}
  #endif

ULBN_PUBLIC int ulbi_print_ex(
  const ulbn_alloc_t* alloc, ulbn_printer_t* printer, void* opaque, /* */
  const ulbi_t* ao, int base                                        /* */
) {
  ulbi_t ro = ULBI_INIT;
  int err;

  if(ul_unlikely(!((base >= 2 && base <= 36) || (base >= -36 && base <= -2))))
    return ULBN_ERR_BAD_ARGUMENT;
  if(ao->len == 0)
    return ul_unlikely(printer(opaque, "0", 1)) ? ULBN_ERR_EXTERNAL : 0;
  if(ao->len < 0 && ul_unlikely(printer(opaque, "-", 1)))
    return ULBN_ERR_EXTERNAL;

  err = ulbi_abs(alloc, &ro, ao);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  if(base > 0)
    err = _ulbi_print_ex(alloc, printer, opaque, &ro, base, 0, _ulbn_upper_table);
  else
    err = _ulbi_print_ex(alloc, printer, opaque, &ro, -base, 0, _ulbn_lower_table);
  ulbi_deinit(alloc, &ro);
  return err;
}
ULBN_PUBLIC int ulbi_print(const ulbn_alloc_t* alloc, FILE* fp, const ulbi_t* ao, int base) {
  return ulbi_print_ex(alloc, _ulbn_fileprinter, fp, ao, base);
}
ULBN_PUBLIC char* ulbi_to_string_alloc(
  const ulbn_alloc_t* alloc, size_t* p_len, size_t* p_alloced, /* */
  ulbn_alloc_func_t* alloc_func, void* alloc_opaque,           /* */
  const ulbi_t* ao, int base                                   /* */
) {
  const ulbn_usize_t an = _ulbi_abs_size(ao->len);
  _ulbn_strprinter_t printer;
  int err;

  *p_len = 0;
  *p_alloced = 0;

  if(ul_unlikely(base < 2 || base > 36))
    return ul_nullptr;
  if(alloc_func == ul_nullptr) {
    alloc_func = alloc->alloc_func;
    alloc_opaque = alloc->alloc_opaque;
  }
  printer.alloc = alloc_func;
  printer.alloc_opaque = alloc_opaque;
  printer.data = ul_reinterpret_cast(char*, alloc_func(alloc_opaque, ul_nullptr, 0, an + 1));
  ULBN_RETURN_IF_ALLOC_FAILED(printer.data, ul_nullptr);
  printer.len = 0;
  printer.cap = an + 1;
  err = ulbi_print_ex(alloc, _ulbn_strprinter, &printer, ao, base);
  ULBN_DO_IF_ALLOC_COND(err < 0, {
    alloc_func(alloc_opaque, printer.data, printer.cap, 0);
    return ul_nullptr;
  });
  err = _ulbn_strprinter(&printer, "", 1);
  ULBN_DO_IF_ALLOC_COND(err < 0, {
    alloc_func(alloc_opaque, printer.data, printer.cap, 0);
    return ul_nullptr;
  });
  *p_alloced = printer.cap;
  *p_len = printer.len - 1;
  return printer.data;
}

  /***********************************
   * <ulbi> Random number generation *
   ***********************************/

  #if ULBN_CONF_USE_RAND
ULBN_PRIVATE int _ulbi_set_rand(
  const ulbn_alloc_t* alloc, ulbn_rand_t* rng, /* */
  ulbi_t* dst, ulbn_usize_t idx, int shift     /* */
) {
  ulbn_usize_t n = idx + (shift != 0);
  ulbn_limb_t* p;
  if(ul_unlikely(n == 0)) {
    _ulbi_set_zero(dst);
    return 0;
  }

  p = _ulbi_res(alloc, dst, n);
  ULBN_RETURN_IF_ALLOC_FAILED(p, ULBN_ERR_NOMEM);
  ulbn_rand_multi(rng, p, idx);
  if(shift != 0)
    p[idx] = ulbn_randx(rng, ulbn_cast_uint(shift));
  n = ulbn_rnorm(p, n);
  ULBI_RETURN_IF_SSIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
  dst->len = ulbn_cast_ssize(n);
  return 0;
}
ULBN_PUBLIC int ulbi_set_rand_bits(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_bits_t n) {
  const ulbn_bits_t idx = n / ULBN_LIMB_BITS;
  const int shift = ulbn_cast_int(n % ULBN_LIMB_BITS);
  if(ul_unlikely(idx > ULBI_SSIZE_LIMIT - (shift != 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_set_rand(alloc, rng, dst, ulbn_cast_usize(idx), shift);
}
ULBN_PUBLIC int ulbi_set_rand_sbits(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_sbits_t n) {
  if(n < 0)
    return ULBN_ERR_BAD_ARGUMENT;
  return ulbi_set_rand_bits(alloc, rng, dst, ulbn_from_pos_sbits(n));
}
ULBN_PUBLIC int ulbi_set_rand(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* n) {
  ulbn_usize_t idx;
  int shift;
  if(ul_unlikely(n->len < 0))
    return ULBN_ERR_BAD_ARGUMENT;
  shift = ulbn_to_bit_info(_ulbi_limbs(n), ulbn_cast_usize(n->len), &idx);
  if(ul_unlikely(shift < 0 || idx > ULBI_SSIZE_LIMIT - (shift != 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_set_rand(alloc, rng, dst, idx, shift);
}
ULBN_PUBLIC int ulbi_init_rand_bits(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_bits_t n) {
  return ulbi_set_rand_bits(alloc, rng, ulbi_init(dst), n);
}
ULBN_PUBLIC int ulbi_init_rand_sbits(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_sbits_t n) {
  return ulbi_set_rand_sbits(alloc, rng, ulbi_init(dst), n);
}
ULBN_PUBLIC int ulbi_init_rand(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* n) {
  return ulbi_set_rand(alloc, rng, ulbi_init(dst), n);
}

ULBN_PUBLIC int ulbi_set_rand_range(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* limit) {
  ulbi_t reroll = ULBI_INIT;
  ulbi_t tlimit = ULBI_INIT;
  ulbn_bits_t bits;
  int err;

  if(ul_unlikely(limit->len <= 0)) {
    _ulbi_set_zero(dst);
    return ULBN_ERR_BAD_ARGUMENT;
  }
  bits = ulbi_abs_bit_width(limit);
  if(ulbi_is_2pow(limit)) {
    err = ulbi_set_rand_bits(alloc, rng, dst, ulbn_cast_bits(bits - 1));
    goto cleanup;
  }

  err = ulbi_set_2exp_bits(alloc, &reroll, bits);
  ulbn_assert(err != ULBN_ERR_EXCEED_RANGE);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  err = ulbi_sub(alloc, &reroll, &reroll, limit);
  ulbn_assert(err != ULBN_ERR_EXCEED_RANGE);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  ulbn_assert(reroll.len >= 0);
  err = ulbi_divmod(alloc, ul_nullptr, &reroll, &reroll, limit);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);

  if(ul_unlikely(dst == limit)) {
    err = ulbi_set_copy(alloc, &tlimit, limit);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    limit = &tlimit;
  }

  do {
    err = ulbi_set_rand_bits(alloc, rng, dst, bits);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
  } while(ulbi_comp(dst, &reroll) < 0);
  err = ulbi_divmod(alloc, ul_nullptr, dst, dst, limit);
cleanup:
  ulbi_deinit(alloc, &reroll);
  ulbi_deinit(alloc, &tlimit);
  return err;
}
ULBN_PUBLIC int ulbi_set_rand_range2(
  const ulbn_alloc_t* alloc, ulbn_rand_t* rng,    /* */
  ulbi_t* dst, const ulbi_t* lo, const ulbi_t* hi /* */
) {
  ulbi_t limit = ULBI_INIT, tlo = ULBI_INIT;
  int err, cmp;

  cmp = ulbi_comp(hi, lo);
  if(cmp == 0) {
    err = ulbi_set_copy(alloc, dst, lo);
    return err;
  }
  if(cmp < 0)
    _ulbn_swap_(const ulbi_t*, lo, hi);

  err = ulbi_sub(alloc, &limit, hi, lo);
  ulbn_assert(err != ULBN_ERR_EXCEED_RANGE);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  ulbn_assert(limit.len > 0);
  if(ul_unlikely(lo == dst)) {
    err = ulbi_set_copy(alloc, &tlo, lo);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    lo = &tlo;
  }

  err = ulbi_set_rand_range(alloc, rng, dst, &limit);
  ulbn_assert(limit.len >= 0);
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
  err = ulbi_add(alloc, dst, dst, lo);

cleanup:
  ulbi_deinit(alloc, &limit);
  ulbi_deinit(alloc, &tlo);
  return err;
}
ULBN_PUBLIC int ulbi_init_rand_range(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* limit) {
  return ulbi_set_rand_range(alloc, rng, ulbi_init(dst), limit);
}
ULBN_PUBLIC int ulbi_init_rand_range2(
  const ulbn_alloc_t* alloc, ulbn_rand_t* rng,    /* */
  ulbi_t* dst, const ulbi_t* lo, const ulbi_t* hi /* */
) {
  return ulbi_set_rand_range2(alloc, rng, ulbi_init(dst), lo, hi);
}
  #endif /* ULBN_CONF_USE_RAND */

/*********************************
 * <ulbi> GCD, LCM, Extended GCD *
 *********************************/

ULBN_PUBLIC int ulbi_gcd(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  ulbn_limb_t *ap, *bp;
  ulbn_usize_t an, bn;

  an = _ulbi_abs_size(ao->len);
  bn = _ulbi_abs_size(bo->len);
  if(ul_unlikely(an == 0))
    return ulbi_abs(alloc, ro, bo);
  if(ul_unlikely(bn == 0))
    return ulbi_abs(alloc, ro, ao);

  ap = _ulbi_res(alloc, ro, an);
  ULBN_RETURN_IF_ALLOC_FAILED(ap, ULBN_ERR_NOMEM);
  if(ro != ao)
    ulbn_copy(ap, _ulbi_limbs(ao), an);

  bp = ulbn_allocT(ulbn_limb_t, alloc, bn);
  ULBN_RETURN_IF_ALLOC_FAILED(bp, ULBN_ERR_NOMEM);
  ulbn_copy(bp, _ulbi_limbs(bo), bn);

  ro->len = ulbn_cast_ssize(ulbn_gcd(ap, an, bp, bn));
  ulbn_deallocT(ulbn_limb_t, alloc, bp, bn);
  return 0;
}
ULBN_PUBLIC int ulbi_gcd_limb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  ulbn_limb_t* ap;
  ulbn_usize_t an;

  an = _ulbi_abs_size(ao->len);
  if(ul_unlikely(an == 0)) {
    ulbi_set_limb(ro, b);
    return 0;
  }
  if(ul_unlikely(b == 0))
    return ulbi_abs(alloc, ro, ao);

  ap = _ulbi_res(alloc, ro, an);
  ULBN_RETURN_IF_ALLOC_FAILED(ap, ULBN_ERR_NOMEM);
  if(ro != ao)
    ulbn_copy(ap, _ulbi_limbs(ao), an);

  ro->len = ulbn_cast_ssize(ulbn_gcd(ap, an, &b, 1));
  return 0;
}
ULBN_PUBLIC int ulbi_gcd_slimb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  if(b >= 0)
    return ulbi_gcd_limb(alloc, ro, ao, ulbn_from_pos_slimb(b));
  else
    return ulbi_gcd_limb(alloc, ro, ao, ulbn_from_neg_slimb(b));
}
ULBN_PUBLIC int ulbi_lcm(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  int err;
  err = ulbi_gcd(alloc, ro, ao, bo);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  /* if `a` and `b` are both 0, `ulbi_div` will return `ULBN_ERR_DIV_BY_ZERO`, and set `r` to 0 */
  err = ulbi_divmod(alloc, ro, ul_nullptr, ao, ro);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  err = ulbi_mul(alloc, ro, ro, bo);
  ro->len = ulbn_cast_ssize(_ulbi_abs_size(ro->len));
  return err;
}


  #ifdef __GNUC__
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wstrict-overflow"
  #endif
ULBN_PUBLIC int ulbi_gcdext(
  const ulbn_alloc_t* alloc, ulbi_t* go, ulbi_t* uo, ulbi_t* vo, /* */
  const ulbi_t* ao, const ulbi_t* _bo                            /* */
) {
  /**
   * Extended GCD Algorithm:
   *
   * function exgcd(a, b) {
   *   (u, w) = (1, 0)
   *   (v, x) = (0, 1)
   *   while(b != 0) {
   *     (q, r) = DivMod(a, b)
   *     (a, b) = (b, r)
   *     (u, w) = (w, u - q * w)
   *     (v, x) = (x, v - q * x)
   *   }
   *   return (a, u, v);
   * }
   */

  ulbi_t tuo = ULBI_INIT;
  ulbi_t wo = ULBI_INIT, xo = ULBI_INIT;
  ulbi_t qo = ULBI_INIT, tgo = ULBI_INIT;
  ulbi_t to = ULBI_INIT;
  ulbi_t bo = ULBI_INIT;
  int err;
  const int a_sign = ao->len < 0, b_sign = _bo->len < 0;

  if(go == ul_nullptr)
    go = &tgo;
  if(uo == ul_nullptr || ul_unlikely(uo == go))
    uo = &tuo;
  if(ul_unlikely(vo == uo || vo == go))
    vo = ul_nullptr;

  err = ulbi_abs(alloc, go, ao);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  err = ulbi_abs(alloc, &bo, _bo);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  ulbi_set_limb(uo, 1);
  ulbi_set_limb(&xo, 1);

  while(bo.len != 0) {
    err = ulbi_divmod(alloc, &qo, go, go, &bo);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    ulbi_swap(go, &bo);

    err = ulbi_mul(alloc, &to, &qo, &wo);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    err = ulbi_sub(alloc, uo, uo, &to);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    ulbi_swap(uo, &wo);

    if(vo) {
      err = ulbi_mul(alloc, &to, &qo, &xo);
      ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
      err = ulbi_sub(alloc, vo, vo, &to);
      ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
      ulbi_swap(vo, &xo);
    }
  }

  if(a_sign)
    uo->len = -uo->len;
  if(b_sign) {
    if(vo)
      vo->len = -vo->len;
  }
  if(go == &tgo)
    err = ulbi_eq_limb(go, 1) ? 0 : ULBN_ERR_INVALID;

cleanup:
  ulbi_deinit(alloc, &tuo);
  ulbi_deinit(alloc, &wo);
  ulbi_deinit(alloc, &xo);
  ulbi_deinit(alloc, &qo);
  ulbi_deinit(alloc, &tgo);
  ulbi_deinit(alloc, &to);
  ulbi_deinit(alloc, &bo);
  return err;
}
  #ifdef __GNUC__
    #pragma GCC diagnostic pop
  #endif
ULBN_PUBLIC int ulbi_invert(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* mo) {
  return ulbi_gcdext(alloc, ul_nullptr, ro, ul_nullptr, ao, mo);
}
#endif /* ULBN_CONF_BIG_INT */



#ifdef __cplusplus
}
#endif

#endif /* ULBN_SOURCE */
