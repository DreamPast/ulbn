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

static const char _ULBN_LOWER_TABLE[] = "0123456789abcdefghijklmnopqrstuvwxyz";
static const char _ULBN_UPPER_TABLE[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
#if 0
ul_unused ULBN_INTERNAL void ulbn_dumplimb(FILE* fp, ulbn_limb_t l) {
  size_t j = sizeof(l) * CHAR_BIT / 4;
  while(j--)
    fputc(_ULBN_UPPER_TABLE[(l >> (j << 2)) & 0xF], fp);
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

#if ULBN_LIMB_MAX == 0xFFu
  #define _ULBN_DEF_SHORT_DIV(prefix, a, b, c) 0x##prefix##a##u
#elif ULBN_LIMB_MAX == 0xFFFFu
  #define _ULBN_DEF_SHORT_DIV(prefix, a, b, c) 0x##prefix##a##b##c##u
#elif ULBN_LIMB_MAX == 0xFFFFFFFFu
  #define _ULBN_DEF_SHORT_DIV(prefix, a, b, c) 0x##prefix##a##b##c##a##b##c##a##u
#elif _ULBN_IS_64BIT(ULBN_LIMB_MAX)
  #define _ULBN_DEF_SHORT_DIV(prefix, a, b, c) 0x##prefix##a##b##c##a##b##c##a##b##c##a##b##c##a##b##c##u
#endif

ULBN_PRIVATE void _ulbn_divby3(ulbn_limb_t* qp, const ulbn_limb_t* ap, ulbn_usize_t an, int dshift) {
#ifdef _ULBN_DEF_SHORT_DIV
  static ul_constexpr const int SHIFT = ulbn_cast_int(ULBN_LIMB_BITS) - 2;
  static ul_constexpr const ulbn_limb_t NORM = _ULBN_DEF_SHORT_DIV(C, 0, 0, 0);
  static ul_constexpr const ulbn_limb_t INV = _ULBN_DEF_SHORT_DIV(5, 5, 5, 5);
#else
  ulbn_may_static const int SHIFT = _ulbn_clz_(3);
  ulbn_may_static const ulbn_limb_t NORM = ULBN_LIMB_SHL(3, SHIFT);
  ulbn_may_static const ulbn_limb_t INV = _ulbn_divinv1(NORM);
#endif
  static ulbn_limb_t _ULBN_SHORT_DIV_R; /* write-only variable */
  ulbn_divmod_inv1(qp, &_ULBN_SHORT_DIV_R, ap, an, NORM, INV, SHIFT - dshift);
}
#if 0
ULBN_PRIVATE void _ulbn_divby5(ulbn_limb_t* qp, const ulbn_limb_t* ap, ulbn_usize_t an, int dshift) {
  #ifdef _ULBN_DEF_SHORT_DIV
  static ul_constexpr const int SHIFT = ulbn_cast_int(ULBN_LIMB_BITS) - 3;
  static ul_constexpr const ulbn_limb_t NORM = _ULBN_DEF_SHORT_DIV(A, 0, 0, 0);
  static ul_constexpr const ulbn_limb_t INV = _ULBN_DEF_SHORT_DIV(9, 9, 9, 9);
  #else
  ulbn_may_static const int SHIFT = _ulbn_clz_(5);
  ulbn_may_static const ulbn_limb_t NORM = ULBN_LIMB_SHL(5, SHIFT);
  ulbn_may_static const ulbn_limb_t INV = _ulbn_divinv1(NORM);
  #endif
  static ulbn_limb_t _ULBN_SHORT_DIV_R; /* write-only variable */
  ulbn_divmod_inv1(qp, &_ULBN_SHORT_DIV_R, ap, an, NORM, INV, SHIFT - dshift);
}
#endif
#if _ULBN_USE_TOOM_4
ULBN_PRIVATE void _ulbn_divby9(ulbn_limb_t* qp, const ulbn_limb_t* ap, ulbn_usize_t an, int dshift) {
  #ifdef _ULBN_DEF_SHORT_DIV
  static ul_constexpr const int SHIFT = ulbn_cast_int(ULBN_LIMB_BITS) - 4;
  static ul_constexpr const ulbn_limb_t NORM = _ULBN_DEF_SHORT_DIV(9, 0, 0, 0);
  static ul_constexpr const ulbn_limb_t INV = _ULBN_DEF_SHORT_DIV(C, 7, 1, C);
  #else
  ulbn_may_static const int SHIFT = _ulbn_clz_(15);
  ulbn_may_static const ulbn_limb_t NORM = ULBN_LIMB_SHL(15, SHIFT);
  ulbn_may_static const ulbn_limb_t INV = _ulbn_divinv1(NORM);
  #endif
  static ulbn_limb_t _ULBN_SHORT_DIV_R; /* write-only variable */
  ulbn_divmod_inv1(qp, &_ULBN_SHORT_DIV_R, ap, an, NORM, INV, SHIFT - dshift);
}
#endif /* _ULBN_USE_TOOM_4 */
#if _ULBN_USE_TOOM_4
ULBN_PRIVATE void _ulbn_divby15(ulbn_limb_t* qp, const ulbn_limb_t* ap, ulbn_usize_t an, int dshift) {
  #ifdef _ULBN_DEF_SHORT_DIV
  static ul_constexpr const int SHIFT = ulbn_cast_int(ULBN_LIMB_BITS) - 4;
  static ul_constexpr const ulbn_limb_t NORM = _ULBN_DEF_SHORT_DIV(F, 0, 0, 0);
  static ul_constexpr const ulbn_limb_t INV = _ULBN_DEF_SHORT_DIV(1, 1, 1, 1);
  #else
  ulbn_may_static const int SHIFT = _ulbn_clz_(15);
  ulbn_may_static const ulbn_limb_t NORM = ULBN_LIMB_SHL(15, SHIFT);
  ulbn_may_static const ulbn_limb_t INV = _ulbn_divinv1(NORM);
  #endif
  static ulbn_limb_t _ULBN_SHORT_DIV_R; /* write-only variable */
  ulbn_divmod_inv1(qp, &_ULBN_SHORT_DIV_R, ap, an, NORM, INV, SHIFT - dshift);
}
#endif /* _ULBN_USE_TOOM_4 */
#ifdef _ULBN_DEF_SHORT_DIV
  #undef _ULBN_DEF_SHORT_DIV
#endif

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
  _ulbn_divby3(v2, v2, m2 + 1, 0);
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
  _ulbn_divby3(v2, v2, m2 + 1, 1);
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
  _ulbn_divby3(t2, t2, m2 + 1, 0);
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
  _ulbn_divby3(v2, v2, m2 + _ULBN_FLEN, 0);
  /* v1 = v1 - v2 = (0, 0, 0, 0, 1, 0, 0)               ranging [0, 15) */
  ulbn_sub(v1, v1, m2 + _ULBN_FLEN, v2, m2 + _ULBN_FLEN);

  /* vm2 = vh - vm2 = (0, -15, 0, 0, 0, 15, 0)          ranging (-90, 90) */
  ulbn_sub(vm2, vh, m2 + _ULBN_FLEN, vm2, m2 + _ULBN_FLEN);
  /* vh = (vh - vm1 * 8) / 9 = (0, 1, 0, 0, 0, 1, 0)    ranging [0, 12) */
  ulbn_subshln(vh, vh, vm1, m2 + _ULBN_FLEN, 3);
  _ulbn_divby9(vh, vh, m2 + _ULBN_FLEN, 0);
  /* vm1 = vm1 - vh = (0, 0, 0, 1, 0, 0, 0)             ranging [0, 20) */
  ulbn_sub(vm1, vm1, m2 + _ULBN_FLEN, vh, m2 + _ULBN_FLEN);
  /* vm2 = (vm2 / 15 + vh) / 2 = (0, 0, 0, 0, 0, 1, 0)  ranging [0, 6) */
  if(vm2[m2 + _ULBN_FLEN - 1] & ULBN_LIMB_SIGNBIT) {
    ulbn_neg(vm2, vm2, m2 + _ULBN_FLEN, 1);
    _ulbn_divby15(vm2, vm2, m2 + _ULBN_FLEN, 0);
    ulbn_neg(vm2, vm2, m2 + _ULBN_FLEN, 1);
  } else {
    _ulbn_divby15(vm2, vm2, m2 + _ULBN_FLEN, 0);
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
ULBN_PRIVATE void _ulbn_init_fft(void);
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

  ulbn_assert(an + bn >= an);

#if ULBN_CONF_FFT && _ULBN_FFT_THRESHOLD < ULBN_USIZE_MAX
  /* if `ulbn_limb_t` is small, it's hard to use a large FFT, so we can split it first */
  if(ul_unlikely(an + bn > _ULBN_FFT_THRESHOLD)) {
    _ulbn_init_fft();
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

#if ULBN_CONF_FFT && _ULBN_FFT_THRESHOLD < ULBN_USIZE_MAX
  if(an + bn >= _ULBN_FFT_THRESHOLD) {
    _ulbn_init_fft();
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

  #if ULBN_LIMB_MAX == 0xFFFFFFFFu
    #define ULBNFFT_NMODS 5
    #define ULBNFFT_MOD_LOG2_MIN 29
    #define ULBNFFT_MOD_LOG2_MAX 30
    #define ULBNFFT_PROOT_2EXP 23
static const ulbn_limb_t ulbnfft_mods[ULBNFFT_NMODS] = {
  0x23800001, 0x26800001, 0x34800001, 0x35800001, 0x3B800001,
};
static const ulbn_limb_t ulbnfft_mods_div[ULBNFFT_NMODS] = {
  0xE6C2B441, 0xD4C77AFD, 0x9C09C099, 0x991F1A4E, 0x89AE4087,
};
static const unsigned ulbnfft_int_bits[ULBNFFT_NMODS] = {
  147, 118, 89, 59, 29,
};
static const ulbn_limb_t ulbnfft_mods_cr[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2] = {
  0x20155563, 0xDE5A5A9, 0x2B18E392, 0x32D2AAAE, 0xD200004, 0x33B7777C, 0x31955559, 0x1AC00036, 0x1DC00009, 0x18CAAAB5,
};
static const ulbn_limb_t ulbnfft_mods_cr_finv[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2] = {
  0xD55555AA, 0x43C3C3D2, 0xCE38E39C, 0xDAAAAAB5, 0x40000012,
  0xF7777788, 0xD5555561, 0x800000FF, 0x80000024, 0x6AAAAAD5,
};
/* clang-format off */ static const ulbn_limb_t ulbnfft_proot_pow[2][ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = { { {
0x00000000, 0x23800000, 0x0EAED064, 0x040ED6C0, 0x1A6F6DE9, 0x1E160952, 0x0F802E3F, 0x1DA1029A, 0x14E74EDE, 0x05B9ECB8,
0x10D56243, 0x22138A01, 0x200B701C, 0x2038078F, 0x0D09AF05, 0x0136F2F3, 0x17C6B8FF, 0x057D2C85, 0x107416BF, 0x06D64765,
0x1CEDB471, 0x1733BA25, 0x1F3B7FC2, 0x158A82F1, }, {   0x0, 0x26800000, 0x0B19D84F, 0x08BD273D, 0x10B79081, 0x0EFC4A1D,
0x142CC6A7, 0x11448990, 0x0C9589FA, 0x1829F456, 0x0B4B3D88, 0x1FE35F96, 0x07E3B845, 0x2278BA56, 0x22C3209E, 0x01B2D33B,
0x1BA16FD6, 0x0F78D105, 0x19DC470C, 0x1CFDEBF8, 0x0F9EBF78, 0x0E6BAC10, 0x10EE48BB, 0x0D5E196D, }, {   0x0, 0x34800000,
0x073D1719, 0x20A4F275, 0x31E36DC0, 0x0A2B9C6C, 0x20A5E7FA, 0x1747EF3E, 0x2D0DD716, 0x071F2683, 0x25163A91, 0x25D6F43F,
0x1D932935, 0x34070481, 0x0278C546, 0x20E4D837, 0x0D1211F1, 0x0BCD3E59, 0x228914E8, 0x2BBB4001, 0x21BE8CE9, 0x1652A7B1,
0x17F74A44, 0x104D68E3, }, {   0x0, 0x35800000, 0x0BF3D077, 0x32B89EAD, 0x0D91BF95, 0x28D6FA49, 0x2774BB57, 0x2ACA1E3B,
0x290A61FD, 0x03D724F2, 0x2D790C79, 0x2E972DB7, 0x240DC460, 0x1C15A95A, 0x0E786EC7, 0x12A98375, 0x1136A65F, 0x2BA180D9,
0x1A14BD05, 0x19AEFA6B, 0x10AC4F41, 0x05774B37, 0x1F31D201, 0x340422F0, }, {   0x0, 0x3B800000, 0x3656D65B, 0x163456B8,
0x375FE6C1, 0x1AFD27AC, 0x3700CCCC, 0x2E97FC55, 0x1C667A0F, 0x09E5815E, 0x0F6AAB68, 0x22D216F7, 0x03CF3BC1, 0x14DCAF74,
0x27BD1177, 0x39BF8E8A, 0x258806A4, 0x0176115B, 0x3B606892, 0x15A8F896, 0x21ADDBD1, 0x2BB9C9ED, 0x0FEB9EDC, 0x00E9A248,
}, }, { {          0x0, 0x23800000, 0x14D12F9D, 0x0465C76D, 0x1A8899EB, 0x00DFDDDA, 0x039304E6, 0x1EA50D4F, 0x0F6D30F6,
0x10E6F448, 0x17D9B924, 0x11EE4471, 0x1A2C70B9, 0x171EE1AE, 0x1180918C, 0x1C8F3206, 0x139A7087, 0x1D76B871, 0x1D796F96,
0x21126ECD, 0x0F60DA0E, 0x12AAA4B9, 0x053F6BAC, 0x136A882F, }, {   0x0, 0x26800000, 0x1B6627B2, 0x051579C1, 0x0D10CD75,
0x19E12F24, 0x25FBD7DE, 0x1D1DF772, 0x09853EB6, 0x1B34D6E7, 0x1679161D, 0x0BC1A475, 0x0E3BACEE, 0x05829792, 0x01482729,
0x085B573D, 0x178C0442, 0x1B2F7EE3, 0x193C35C2, 0x20E664D3, 0x019993E9, 0x1AC36124, 0x0D3D1D2B, 0x1B0FE28F, }, {   0x0,
0x34800000, 0x2D42E8E8, 0x143B0E60, 0x10D03B4F, 0x05005754, 0x2529E004, 0x3469157F, 0x018E554E, 0x2A3B3221, 0x2DE3AB87,
0x324AAF8F, 0x2A5C8BD5, 0x2529DCF8, 0x1F7D5761, 0x2050C68F, 0x30BCCD04, 0x220985BF, 0x1867365D, 0x1E19A8F4, 0x14FF675F,
0x0F05D5E8, 0x17DE4705, 0x068AA1FC, }, {   0x0, 0x35800000, 0x298C2F8A, 0x1A5F903B, 0x1DF58D2B, 0x0B749E6C, 0x15D7F002,
0x110017FA, 0x2566DFA1, 0x25B9B941, 0x2A9FEE94, 0x3170E46C, 0x3562D5F8, 0x31D1971B, 0x0C88874C, 0x006E8254, 0x1F9946D7,
0x15CA7F55, 0x2A7ABF9E, 0x306DCB60, 0x0E8B88E5, 0x150C130F, 0x2F47B7BF, 0x15279CC7, }, {   0x0, 0x3B800000, 0x052929A6,
0x1E5EA9E6, 0x14191D56, 0x053803C8, 0x245358AD, 0x080F8A3E, 0x1225AFB9, 0x28DB09F8, 0x16BEBAA0, 0x14003AB8, 0x07B4D9B7,
0x15570604, 0x308D724E, 0x2A395EC1, 0x10DEE6BE, 0x0038933D, 0x073C4B97, 0x2A0445EA, 0x38A5D246, 0x1991700C, 0x16D05613,
0x1C01A690, }, } }; static const ulbn_limb_t ulbnfft_proot_pow_finv[2][ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = { { {
0x00000000, 0xFFFFFFF8, 0x69E1D053, 0x1D435855, 0xBEA1BE6E, 0xD8F5720F, 0x6FC79CCD, 0xD5A989B9, 0x96BDB6E9, 0x294B2CD7,
0x79641EB8, 0xF5BBC64F, 0xE7152FA2, 0xE856BF7E, 0x5E04EE1A, 0x08C2562B, 0xAB74FC58, 0x279515C5, 0x76A67FF5, 0x314DBABA,
0xD09C84F6, 0xA750F634, 0xE139AEE7, 0x9B569E35, }, {   0x0, 0xFFFFFFF9, 0x49D06C6F, 0x3A1B9DD6, 0x6F285321, 0x63A4D585,
0x86266810, 0x72D1B3EF, 0x53AD2468, 0xA0AC9480, 0x4B18DEF4, 0xD40921CB, 0x3475D33D, 0xE536B5BE, 0xE7256B25, 0x0B4B4DFF,
0xB7B9C30B, 0x66E0DB8C, 0xABF48BEE, 0xC0C6F5CC, 0x67DD13BA, 0x5FE338EC, 0x70942CBD, 0x58E2BD01, }, {   0x0, 0xFFFFFFFB,
0x234C0559, 0x9F2E10D8, 0xF343EB42, 0x3197B408, 0x9F32BE0B, 0x7185C6A8, 0xDBB1339A, 0x22BA075E, 0xB4D7AAFA, 0xB8836EE6,
0x90366C46, 0xFDB21111, 0x0C0D828D, 0xA065A463, 0x3FBC1336, 0x398C28B3, 0xA866CC54, 0xD53E2BE3, 0xA48B37A0, 0x6CD9BF18,
0x74DCD7D6, 0x4F7E5736, }, {   0x0, 0xFFFFFFFB, 0x39315ABE, 0xF2B40337, 0x40EE0C59, 0xC36B8E82, 0xBCCC793D, 0xCCBFF784,
0xC461884D, 0x12606439, 0xD996F648, 0xDEF01B54, 0xAC84DDE4, 0x8662DDC8, 0x453DE238, 0x594CA016, 0x525E068E, 0xD0C69860,
0x7CCC8147, 0x7AE593EF, 0x4FC80F90, 0x1A27AFAE, 0x954485FD, 0xF8E655D0, }, {   0x0, 0xFFFFFFFB, 0xE9CBAB76, 0x5F88FCA1,
0xEE401D0B, 0x741EC8CC, 0xECA6F00D, 0xC87868AD, 0x7A31610D, 0x2A9475BE, 0x4254A0EF, 0x95D10EE5, 0x1063F655, 0x59C26934,
0xAAF9D6F6, 0xF8769049, 0xA17ABBC1, 0x06496F3E, 0xFF7813A5, 0x5D315AB7, 0x90E7BA5C, 0xBC2182E5, 0x447F7168, 0x03ED36FD,
}, }, { {          0x0, 0xFFFFFFF8, 0x961E2FAC, 0x1FB64B2D, 0xBF5743E4, 0x064E5CAC, 0x19C672A5, 0xDCFCC4E7, 0x6F3EACC6,
0x79E2D324, 0xABFE00FE, 0x814DA56C, 0xBCBEAB0C, 0xA6BAA387, 0x7E369427, 0xCDF2FC8A, 0x8D5D4F81, 0xD4789362, 0xD48C2842,
0xEE7DB66C, 0x6EE5B10E, 0x869C139E, 0x25D7C3F0, 0x8C03D60A, }, {   0x0, 0xFFFFFFF9, 0xB62F9390, 0x21CDF7B5, 0x56E0C3DC,
0xAC152C23, 0xFC913E42, 0xC19C0997, 0x3F4E18AB, 0xB4E7A8E4, 0x956E49E1, 0x4E2C2AED, 0x5EA41378, 0x24A38573, 0x08860110,
0x37913A19, 0x9C926570, 0xB4C42079, 0xA7CC3391, 0xDAC3732C, 0x0AA36D1D, 0xB1F5396F, 0x5807682C, 0xB3F1EFBF, }, {   0x0,
0xFFFFFFFB, 0xDCB3FAA6, 0x62A61073, 0x51FC40E3, 0x18632FEC, 0xB5377787, 0xFF9041CA, 0x07965941, 0xCDED7334, 0xDFC3E06B,
0xF53B6B8B, 0xCE9012AB, 0xB53768AC, 0x998CA2C0, 0x9D93A130, 0xEDA741E3, 0xA5F8CB8C, 0x76FE98EC, 0x92C64406, 0x66637E25,
0x494106DA, 0x7462E064, 0x1FE5D409, }, {   0x0, 0xFFFFFFFB, 0xC6CEA541, 0x7E328BDC, 0x8F5B2977, 0x36D0B7D8, 0x6885AEAF,
0x5158F8B4, 0xB2F837A1, 0xB484A8AD, 0xCBF61AAD, 0xEC93D226, 0xFF7472AC, 0xEE628677, 0x3BF8F574, 0x0210CA8A, 0x9733912A,
0x68455EE3, 0xCB442E00, 0xE7BC0690, 0x459949A8, 0x64B6301F, 0xE23CDAE1, 0x6539F55B, }, {   0x0, 0xFFFFFFFB, 0x16345489,
0x82AAA75A, 0x5678F6AE, 0x16743B4A, 0x9C4AA217, 0x22AE6C9A, 0x4E1429D3, 0xAFC83C16, 0x61DC69F1, 0x560DE4F8, 0x21283B01,
0x5BD0C5FA, 0xD0E5F463, 0xB5AB8AC2, 0x489629E9, 0x00F36A6F, 0x1F218A10, 0xB4C71748, 0xF3BA641E, 0x6E01E213, 0x62282B56,
0x787F928B, }, }, }; static const ulbn_limb_t ulbnfft_len_inv[ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = { {
0x00000001, 0x11C00001, 0x1AA00001, 0x1F100001, 0x21480001, 0x22640001, 0x22F20001, 0x23390001, 0x235C8001, 0x236E4001,
0x23772001, 0x237B9001, 0x237DC801, 0x237EE401, 0x237F7201, 0x237FB901, 0x237FDC81, 0x237FEE41, 0x237FF721, 0x237FFB91,
0x237FFDC9, 0x237FFEE5, 0x237FFF73, 0x237FFFBA, }, {   0x1, 0x13400001, 0x1CE00001, 0x21B00001, 0x24180001, 0x254C0001,
0x25E60001, 0x26330001, 0x26598001, 0x266CC001, 0x26766001, 0x267B3001, 0x267D9801, 0x267ECC01, 0x267F6601, 0x267FB301,
0x267FD981, 0x267FECC1, 0x267FF661, 0x267FFB31, 0x267FFD99, 0x267FFECD, 0x267FFF67, 0x267FFFB4, }, {   0x1, 0x1A400001,
0x27600001, 0x2DF00001, 0x31380001, 0x32DC0001, 0x33AE0001, 0x34170001, 0x344B8001, 0x3465C001, 0x3472E001, 0x34797001,
0x347CB801, 0x347E5C01, 0x347F2E01, 0x347F9701, 0x347FCB81, 0x347FE5C1, 0x347FF2E1, 0x347FF971, 0x347FFCB9, 0x347FFE5D,
0x347FFF2F, 0x347FFF98, }, {   0x1, 0x1AC00001, 0x28200001, 0x2ED00001, 0x32280001, 0x33D40001, 0x34AA0001, 0x35150001,
0x354A8001, 0x35654001, 0x3572A001, 0x35795001, 0x357CA801, 0x357E5401, 0x357F2A01, 0x357F9501, 0x357FCA81, 0x357FE541,
0x357FF2A1, 0x357FF951, 0x357FFCA9, 0x357FFE55, 0x357FFF2B, 0x357FFF96, }, {   0x1, 0x1DC00001, 0x2CA00001, 0x34100001,
0x37C80001, 0x39A40001, 0x3A920001, 0x3B090001, 0x3B448001, 0x3B624001, 0x3B712001, 0x3B789001, 0x3B7C4801, 0x3B7E2401,
0x3B7F1201, 0x3B7F8901, 0x3B7FC481, 0x3B7FE241, 0x3B7FF121, 0x3B7FF891, 0x3B7FFC49, 0x3B7FFE25, 0x3B7FFF13, 0x3B7FFF8A,
}, }; static const ulbn_limb_t ulbnfft_len_inv_finv[ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = { {
0x00000007, 0x80000003, 0xC0000001, 0xE0000000, 0xF0000000, 0xF8000000, 0xFC000000, 0xFE000000, 0xFF000000, 0xFF800000,
0xFFC00000, 0xFFE00000, 0xFFF00000, 0xFFF80000, 0xFFFC0000, 0xFFFE0000, 0xFFFF0000, 0xFFFF8000, 0xFFFFC000, 0xFFFFE000,
0xFFFFF000, 0xFFFFF800, 0xFFFFFC00, 0xFFFFFE00, }, {   0x6, 0x80000003, 0xC0000001, 0xE0000000, 0xF0000000, 0xF8000000,
0xFC000000, 0xFE000000, 0xFF000000, 0xFF800000, 0xFFC00000, 0xFFE00000, 0xFFF00000, 0xFFF80000, 0xFFFC0000, 0xFFFE0000,
0xFFFF0000, 0xFFFF8000, 0xFFFFC000, 0xFFFFE000, 0xFFFFF000, 0xFFFFF800, 0xFFFFFC00, 0xFFFFFE00, }, {   0x4, 0x80000002,
0xC0000001, 0xE0000000, 0xF0000000, 0xF8000000, 0xFC000000, 0xFE000000, 0xFF000000, 0xFF800000, 0xFFC00000, 0xFFE00000,
0xFFF00000, 0xFFF80000, 0xFFFC0000, 0xFFFE0000, 0xFFFF0000, 0xFFFF8000, 0xFFFFC000, 0xFFFFE000, 0xFFFFF000, 0xFFFFF800,
0xFFFFFC00, 0xFFFFFE00, }, {   0x4, 0x80000002, 0xC0000001, 0xE0000000, 0xF0000000, 0xF8000000, 0xFC000000, 0xFE000000,
0xFF000000, 0xFF800000, 0xFFC00000, 0xFFE00000, 0xFFF00000, 0xFFF80000, 0xFFFC0000, 0xFFFE0000, 0xFFFF0000, 0xFFFF8000,
0xFFFFC000, 0xFFFFE000, 0xFFFFF000, 0xFFFFF800, 0xFFFFFC00, 0xFFFFFE00, }, {   0x4, 0x80000002, 0xC0000001, 0xE0000000,
0xF0000000, 0xF8000000, 0xFC000000, 0xFE000000, 0xFF000000, 0xFF800000, 0xFFC00000, 0xFFE00000, 0xFFF00000, 0xFFF80000,
0xFFFC0000, 0xFFFE0000, 0xFFFF0000, 0xFFFF8000, 0xFFFFC000, 0xFFFFE000, 0xFFFFF000, 0xFFFFF800, 0xFFFFFC00, 0xFFFFFE00,
}, }; /* clang-format on */
ULBN_PRIVATE void _ulbn_init_fft(void) {
  (void)0;
}
  #elif _ULBN_IS_64BIT(ULBN_LIMB_MAX)
    #define ULBNFFT_NMODS 5
    #define ULBNFFT_MOD_LOG2_MIN 61
    #define ULBNFFT_MOD_LOG2_MAX 62
    #define ULBNFFT_PROOT_2EXP 53
static const ulbn_limb_t ulbnfft_mods[ULBNFFT_NMODS] = { 0x3460000000000001, 0x3820000000000001, 0x3960000000000001,
                                                         0x3AE0000000000001, 0x3EA0000000000001 };
static const ulbn_limb_t ulbnfft_mods_div[ULBNFFT_NMODS] = { 0x9C69169B30446DF6, 0x91F5BCB8BB02D9CA, 0x8EC7AB397255E41A,
                                                             0x8B246A87E19008AF, 0x82CF750393AC3316 };
static const unsigned ulbnfft_int_bits[ULBNFFT_NMODS] = { 309, 247, 185, 123, 61 };
static const ulbn_limb_t ulbnfft_mods_cr[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2] = {
  0x3641111111111121, 0x2998CCCCCCCCCCD9, 0x32F313B13B13B145, 0x1625DA895DA895E1, 0x33A3333333333362,
  0x0D61745D1745D18A, 0x389A76276276276D, 0x2C28000000000028, 0x165DB6DB6DB6DB7A, 0x0643333333333344,
};
static const ulbn_limb_t ulbnfft_mods_cr_finv[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2] = {
  0xF7777777777777BB, 0xB9999999999999CC, 0xDD89D89D89D89DB1, 0x5A895DA895DA8976, 0xE666666666666733,
  0x3A2E8BA2E8BA2EE8, 0xE762762762762789, 0xC0000000000000AA, 0x5B6DB6DB6DB6DB9E, 0x19999999999999DD,
};
/* clang-format off */ static const ulbn_limb_t ulbnfft_proot_pow[2][ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = { { {
0x0000000000000000, 0x3460000000000000, 0x1C4AEC81D763A90F, 0x1672DB30133DAD42, 0x0B0193D9FC8926B6, 0x3030D104C61A3C77,
0x19081F778AF1D962, 0x007F34DA6EBAED28, 0x05702421FFD2436A, 0x2ABDC35EBA08B19F, 0x1615B0E2FBE5FC00, 0x285979A7D20F4AE1,
0x18FED274C8A391D6, 0x2FB80E12B41563BE, 0x3330420475B9FF9B, 0x1102254039259930, 0x220EDF6A0EF1E3AB, 0x29AA9C0888728C7B,
0x0CE675EC1C0DE405, 0x30194E3EE2A9E649, 0x0586FDB01ABAF90E, 0x1ED649193B452C68, 0x16C37F5C62E97AEF, 0x279DD9BE8D71CE48,
0x1CB4B35346360715, 0x10D0C51A7E4DCDE1, 0x24868C025DFF0C0D, 0x334293783A9E6527, 0x07BF373DB5710AB5, 0x0043A2A7861B3A2A,
0x133659A47ECF5C85, 0x31817F0F05D9950E, 0x03254A1C51628B1F, 0x0E9071E18DD2AF30, 0x0796F6557AF6062D, 0x119BE54041D64575,
0x2EC2E6F4818AD8DD, 0x03F2BC382F409C0F, 0x00B8AE11E35AA2AC, 0x1C356824049B707F, 0x25C7A23593183C62, 0x245401EC19EFC836,
0x1813152F92B5DBE9, 0x220686A0DA068192, 0x2C4FF221D42D931E, 0x195DBD1808B74E31, 0x07BE43D1D0D95AF9, 0x33D1DFED9BBC25C1,
0x17E86DCEFDB4B9A0, 0x00F1A579ED0B73B8, 0x101012D3B5723DD6, 0x22271EC0B1C3CD6A, 0x33A244F6B1C2918F, 0x1C708B2263FABBAD,
}, {           0x0, 0x3820000000000000, 0x22B6BB930A26E890, 0x377EB875057159C3, 0x2FB45CADAE93DB8F, 0x092CAFC836FF7886,
0x277FB4494E4FEA6B, 0x1355FD4E557CE520, 0x35F1125759034631, 0x0F160AC198C0FD2F, 0x2E52E8A9263D3E8F, 0x019A62E38E545095,
0x2851FA40AF4F19B3, 0x1AE4B3FE9A206A7A, 0x20F190CA56BC5316, 0x24E3CDD156429914, 0x25F275142FF2FFEB, 0x017AA751C1DA947A,
0x1DD1297CE8800BE7, 0x1B4803E628B0DB17, 0x23E20269ED55418F, 0x22122B9AE5D3C0E3, 0x2AFE062D99CD99C9, 0x36F52D378F86155C,
0x1098CEE3837BCCD6, 0x25E348787C6D2EB3, 0x19392DABB730FB24, 0x2F12447D82C035BB, 0x0FE64350C07601FA, 0x1FA18F2CB45932BB,
0x09C2DECB45BC0EB5, 0x19297EF372534AF8, 0x09DFCC2F604FC8F0, 0x034CCC6565AC689A, 0x2A762D5F7F9DBC3C, 0x102CBF57739746A1,
0x0FCF5C35A421B8EE, 0x1FEB996E06C2B3DA, 0x2F20E08863610058, 0x2F4E289AD2981112, 0x1B6A6ADF3A0E1509, 0x3530F2DBFB65E7C9,
0x0D7879685B170B48, 0x2121F5C1B3FF1BC5, 0x26DE22DEA7BEDC86, 0x16FD1F621E62B353, 0x0E3917787B0CD0A1, 0x0BE9459BF88DF801,
0x16CB8B72EEDCADD7, 0x09130EB14D5D9B63, 0x1F09E1CC7B1FC826, 0x303DE903C34836C4, 0x36B428C0D05BFC64, 0x0433067489E59ABC,
}, {           0x0, 0x3960000000000000, 0x379C2A0C62FAD441, 0x26D07833D26BE097, 0x071156287C1A81D2, 0x12883D5314DC1CDA,
0x348E817E480B9D41, 0x30E9CB46811D0A0F, 0x09AA7DE6BA22B1AB, 0x274BFD6F98953A39, 0x1717901149CCB1DA, 0x16BF72FAFF2470C4,
0x117510E8F86A5BA7, 0x25F56932A01F1598, 0x25BB78F89F98BECE, 0x18C9F20600DF192B, 0x36EA0BE9508AD380, 0x148A0FF7D248965E,
0x2073F66231491429, 0x19571CB0459E026A, 0x32828558503734DB, 0x1DF7233F639A03EC, 0x3034FC68633AADAD, 0x2DD5152284A01909,
0x1CE1C3473E27A09E, 0x27BBF1A67A7EF19D, 0x19588A3417100746, 0x2BD092D3C47EADF3, 0x05A9A637650ED909, 0x112EDF7FF3072D77,
0x2C32B9BDE597B3A4, 0x16420919A2C45B3D, 0x18B32034F8744BE7, 0x1F511D81EC09A4BF, 0x3324D7BC9A9274EE, 0x109D276CBDF7B50D,
0x0E4460BB48F20664, 0x194E1B0FC5970D56, 0x29662C2C9234D324, 0x2A3BFEBFE91E829D, 0x1E51BE22F1B35C23, 0x1B0AE27FE78BD13E,
0x0E49F3BBB7763D78, 0x06BE9DCC1F0669CA, 0x2F5F9D86023D16EF, 0x2554A54FB2B22276, 0x023B7E79D27D0954, 0x13D6C50A851D05E6,
0x0D2C789F29CBA9A8, 0x30AA12AF9A193211, 0x0BE65A8511C78C9C, 0x1AB8374605D8EE6E, 0x380159A53F27FC6F, 0x093E91AE10FEF2BB,
}, {           0x0, 0x3AE0000000000000, 0x33D440DDA1B91980, 0x0922BB1D545B27E2, 0x23F2699288C8A374, 0x0E3491D71587A882,
0x1606B729EAB784A9, 0x1EC819E4C1A96EBB, 0x234F2BBE7BA3EC98, 0x216D0566E22F1DD6, 0x102AA847728BA498, 0x0FA944089FEB7178,
0x0A932AFC7C347AB4, 0x165940554FB08F07, 0x2401351A88C64515, 0x2ECEF68D7CE62991, 0x383E2C0D2AEF9C46, 0x245DA0AC8FE06540,
0x1CB9840FE2878936, 0x2BF6CCF1A787B20E, 0x35F7B5976E733A65, 0x08A96D14EB77F4D6, 0x28FE3EA4E9B3F339, 0x1CC7AFFDA1676025,
0x10C7F328DEFF0B2E, 0x2AE7268735E1FDD9, 0x2C6FCA59A9F32E72, 0x2076B17FA1AC5440, 0x27B02823C40D562C, 0x1FA8F9079F74B843,
0x27D1A3471E493ABC, 0x052E780A2938E168, 0x3464913534AB4785, 0x32F3FC34904474E5, 0x37A4CCFC66A10C9F, 0x17AFDC6A7C308DE4,
0x2FAD87693039A106, 0x204D46144A1E4185, 0x39AAC16930E64D48, 0x0B847F084550C42B, 0x3715A2107DA425B4, 0x164AEE9C7CCB42CA,
0x18BD9C5366546792, 0x3A00E7136DD199ED, 0x19214BE1A3E7BFDF, 0x186FA23FCB0609FD, 0x23DC639CD5AF6EB9, 0x05F96B51F49E4CE9,
0x39CBF7B3F316C061, 0x20932DA300AF50B8, 0x113568EA0D522742, 0x0B8DB17BF4B88F72, 0x19BFC4E824CE9B18, 0x364C95F88A24DA05,
}, {           0x0, 0x3EA0000000000000, 0x1D053A77E3FA20BB, 0x31916E26B6D6DE57, 0x2041476AF8A3461C, 0x0AC7FB6685F73B5F,
0x12D5502E9357F01C, 0x3BB24853F08CB06F, 0x116C396FFFBEC2D0, 0x1DEA6B31AAAE7A0E, 0x1E04F23D893B70A6, 0x21330D3F2FDCB12D,
0x2415138CD14CD42C, 0x35802AE705FE0D13, 0x1AA6547841022A0F, 0x10E3875CCDF116A5, 0x0840BF3A51B9B419, 0x0C2EEC41DE782FF0,
0x38A73B3D1EFA88AA, 0x2E66F95C31CEAB5A, 0x2418C6569B5D6B40, 0x18B1DFD208F318D6, 0x25D687175C5787EE, 0x042383A5D70F7402,
0x08EC13EDA6A98913, 0x1C19ECE7975E7E85, 0x394A7F5F87120896, 0x358FFAB21882F7F4, 0x377FA42D0B20CD98, 0x0AC777D55A1E9A61,
0x3CD2AE0365AEFF7C, 0x1C3C01ADA387056E, 0x21B44A7F3FC49774, 0x01F5E96A78B9DA84, 0x0ED6DB50929B8B17, 0x030B1674557D437B,
0x12CB0BE597A2EA1C, 0x26003854C331BD70, 0x0B70BF039B0AED87, 0x0B569D17AFD3CB40, 0x146F6C210708EA95, 0x2376F1FA9D265F3E,
0x1888EDAFB52618E0, 0x055CE0F826B042F0, 0x1853290CB74E8E3B, 0x2A2D596797FDC247, 0x188EFA637A04BE3D, 0x1811CDD24882F350,
0x0127D4216DA00EB5, 0x0895FC2F35232C13, 0x26AA5A624C2ABFF6, 0x0954DA8E8EB0A117, 0x254F2B293844C925, 0x0CBA83E69F37F265,
} }, { {       0x0, 0x3460000000000000, 0x1815137E289C56F2, 0x09B172F8E2327C01, 0x18AAA8D74252592D, 0x33C4526DBA738140,
0x0A8F781315017F1B, 0x20FB6809C3ED9283, 0x33DDA316ECDFCFA4, 0x0555F21871C41EB4, 0x303C008F3F15F36A, 0x0EBAA2EEB084D099,
0x16021598A8ECA3D0, 0x2BBDFA2E0166828C, 0x2E1EFF3D3DF1E1D2, 0x1765D7D7FEADDD5F, 0x281E584CB4528E0C, 0x0183CDE56D5A7798,
0x29CF0101F1578F38, 0x27313E9404674AB8, 0x31F574064FCA3779, 0x1FEC267FD8C2652D, 0x301C683FAE3B17E7, 0x017866293E93F173,
0x12138E4FC2B469B1, 0x03A287640FB6A741, 0x253C7D074693EF1A, 0x130C700B689C2209, 0x3314FC9397CC1131, 0x0B01F5E5CE851F3C,
0x0F7D076669C49809, 0x0B1C0F372E8D2EA4, 0x2CD8FCFD486C61A5, 0x173CBEF508D5D726, 0x30F89F8214E68CEA, 0x055296E7B1658D8C,
0x11B7B6DFD9D26EF0, 0x0112D0E591E6F395, 0x26245F9DF2A6829A, 0x337CFF0FD2DEA6AF, 0x1FAB54DEFD0BDD96, 0x0544FF1D59C13219,
0x1A1E1DD421D45B3C, 0x10275119404C7376, 0x0EBC545CD6C47437, 0x33439766FA75C378, 0x11AB392BB868C143, 0x274846AC94F748FA,
0x16A0BD101DE6609B, 0x2D5FDB3A516DD74D, 0x1DFA80F801F489B2, 0x191F49AA5C2E602E, 0x203DEC296B4FAD6C, 0x1FAA406AC14078D1,
}, {           0x0, 0x3820000000000000, 0x1569446CF5D91771, 0x2B01F3CF2DFF23C0, 0x0DBA49E9641336B1, 0x05B2151A7D75E539,
0x0CEEF74540BE8859, 0x20604DF3C5935BA3, 0x13E5D7E7C9B55D99, 0x191E0526D47B4065, 0x13471B4A9B9AE3A4, 0x1CCCD90A59522150,
0x345E45D9E88F0F10, 0x227DE773B9DDEE47, 0x13E789C49B6DDB89, 0x07B6FBB943A036F8, 0x26FF463161666FB7, 0x222FCBEC09311C36,
0x35D8130DACC9C7D5, 0x23F995499902368F, 0x11FC63593D2E1CE1, 0x1494BEF7F3B0542F, 0x1A34A54F1E3F74B1, 0x268B3D84D0B3B75B,
0x0B7070804B993719, 0x22771984A68F8918, 0x08290DBC63DD9CAD, 0x0DDBDD264F1D8D16, 0x149188040A7CF9BC, 0x12260A1B9BEE12E3,
0x16E820F63325A630, 0x1D13CCE8DCAF8601, 0x29A7BE2691875A25, 0x21E148D546935177, 0x1AAE656B86E9D027, 0x38172A6E30F1F976,
0x269426E9D3A53C09, 0x049A252C8C139AC9, 0x2FA63F198ECA89FC, 0x369513095576DC0B, 0x24B7C3C1B82AA077, 0x1EF74DE09C652E2A,
0x33FA8A18F681B979, 0x06CE711DDCB98ACD, 0x2850A50DA9AF01AA, 0x15DC6D2ED76BFD22, 0x346E30B4D132E73A, 0x0F0BFAC46B70489D,
0x03A52A7CA885B498, 0x10D5A4C36F0E887A, 0x321834ABAFD6B365, 0x004B9CC5D2BF8A49, 0x34F6EF526A4DD3AE, 0x1BD993B1FDB306B0,
}, {           0x0, 0x3960000000000000, 0x01C3D5F39D052BC0, 0x2811475E581DC4D1, 0x373CE0AC1B185B2D, 0x29DF1971ECE15954,
0x242F44C6C4062ECA, 0x036BFAD1A5922B0B, 0x2D41257AED25ADFD, 0x0FA3433D8182E39A, 0x0D18D617E251C5B5, 0x0BF8FF3B7FBB68A6,
0x2243BA374CBDC795, 0x0B40D3F59A98D33E, 0x0C88B357C01F4BEA, 0x2858B6D804AA648D, 0x17631492E822F492, 0x1950D88DEDCA030E,
0x35771C50E64BB5C7, 0x039D93D5EF447CC9, 0x1BB3395BBBDA03D8, 0x2E373185AA53E089, 0x274439DBB1C03EAB, 0x35D8216D33333841,
0x14866ECF0C398899, 0x21F10B1B129D6E95, 0x15E469DE40B27EB2, 0x069049BED42EDD4E, 0x2AE5BAAC91517738, 0x163D71CFCAEE168C,
0x2170D16F63D43DDB, 0x352CE9A9C0306017, 0x23FC9D139C4FAFEE, 0x03A2D41616CA5F52, 0x33400CEDDF391898, 0x33CAC5737FFD43B5,
0x1F7B68E689A701B1, 0x0693D77C37162403, 0x2E3D3935AAF8DD9E, 0x02D07C7E9366177F, 0x1334539923A819ED, 0x0CFC31FFC7E0AB1C,
0x28F1D142D49359BA, 0x0F80C28D709BB7E1, 0x22FC24268BFC7B4B, 0x13C2CE6BF56F9C83, 0x22EF8BB3F47FF490, 0x1B19192524419826,
0x1D72C7721D93967A, 0x320567262CE785AA, 0x1CFE53E0E2B9CEC8, 0x16CAF8199ED8BA65, 0x333BE9072636B454, 0x22502FE8592A9BD5,
}, {           0x0, 0x3AE0000000000000, 0x070BBF225E46E681, 0x0A7633B90AC78B87, 0x126B6B5FE7BE0CD9, 0x1E3F39FBE90A6EB9,
0x20D16330366B2C7F, 0x1A086C9E498D02E7, 0x10F313EC2F9E5EF9, 0x2ED52FE98DFDF571, 0x0D005844F85CF514, 0x1F1126BBCE9F05CB,
0x24193AAB5369D4C5, 0x009B492D0C834507, 0x005B0E1E9238810A, 0x03C2EBD8D9C23E2C, 0x040EA59D7DBE096E, 0x21334111BEF6CDAF,
0x1A3C5EFB33FC8E8B, 0x042DA145D95A02E1, 0x163312F7EDD34289, 0x107911A7BCF5C95D, 0x298343ED075DFFB1, 0x2D0D84F597598390,
0x2DDCB09B9400CF31, 0x37D6A80E91BCC0F2, 0x00FA59D3C3A83D48, 0x17DF585636BBA630, 0x00E01B89D63CEA30, 0x0A11C3DCAA330C43,
0x10C4FD0D1A5189AF, 0x0D15B90ACD91E231, 0x2FA4BE625F4CEF9B, 0x14221BE3A1D46304, 0x1AC2CFC088D99163, 0x19E12230ACDDCCE7,
0x02D437C9AB68B3E5, 0x0B0BDE9AFFB4194B, 0x026ACCC40E367348, 0x2B1AE245BD0916EA, 0x1D64CAA64BD72E51, 0x39B9735ADCF1E5EB,
0x0FEC23606E5FA0ED, 0x09B934EA3A68640C, 0x2D2FFB60A509BA91, 0x0916CAA8A84818E4, 0x19320817CDA5BE01, 0x15495A654077B5FE,
0x34AD21F8BCD54B2B, 0x3668788BA6C8041A, 0x295913D053FD276D, 0x28B5F6DE5A88B94F, 0x0D1B343A4694DE10, 0x1F7FD269B1EE9A9F,
}, {           0x0, 0x3EA0000000000000, 0x219AC5881C05DF46, 0x2A14D58BB29A01EB, 0x314EE470E90D1D3B, 0x18B3DF484C524949,
0x27C496700923CE0B, 0x072D36032CD4327C, 0x37FD4DD1E37310FE, 0x0230BE86EA0099CC, 0x3A7384E7805A9904, 0x04159A4B8EC13318,
0x32677BDAC3BBBC33, 0x14F0E3BACC88C980, 0x1E5179A2E5500335, 0x333652F0D3AFD5B9, 0x34AEC5CC898EDDF3, 0x2D80F7415454498B,
0x12988969AD7F55C5, 0x0EEEFB08C9254BD1, 0x176DA74EE3130F61, 0x3E8F75B0B5B01055, 0x0A7860B6BF1863A6, 0x1B2D4672B73F1D80,
0x18BD200A4A1D82E7, 0x362895D855C58F36, 0x2C94046E237FF9A6, 0x1CFDA4EEB2E08E78, 0x25E7E6C610E650AD, 0x19CED2FA3D5FB360,
0x0C5B90C26AFA9040, 0x202164C4740FC458, 0x1CF347A0BFFF4E22, 0x0CAF84717628F2C1, 0x3E6FDA3E89739D72, 0x15111EEE88DA8060,
0x2FD770CD7B82EB22, 0x206F42B3584946ED, 0x35ABD43E29F1756D, 0x04C6C4E48DE24DE8, 0x18420BF7B3D8ABFC, 0x1E0BD340AA7A4591,
0x2767FF0D337FFA03, 0x26A9DE6B5CAE56C2, 0x35EF46ECF18F2E52, 0x368F87CFF7310216, 0x3D38D3C7373878F5, 0x0DE6DC46ACBB8394,
0x026A4254B56782D4, 0x2FA5A83C31F229CB, 0x0B310B582D4CF822, 0x3225FEA6B396849D, 0x22339C89D93F1FC3, 0x2AF4AFB022785FF6,
} } }; static const ulbn_limb_t ulbnfft_proot_pow_finv[2][ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = { { {
0x0000000000000000, 0xFFFFFFFFFFFFFFFB, 0x8A4A2ACDBC40535E, 0x6DB9A545686ED718, 0x35CBD5BA48452B2F, 0xEB8C3D306241EB09,
0x7A59CDBD00573E59, 0x026DC36825C8A6F3, 0x1A948BF3C6EAAE51, 0xD0E9754897B04C56, 0x6BF24518F8C85315, 0xC538B32A8098F3C8,
0x7A2C57C449FF1E59, 0xE93DFA3F50725309, 0xFA335C57C8E5B866, 0x532250A746FAFB69, 0xA6785A0181DE7756, 0xCBA88DE8F1B0CF9F,
0x3F0DDC2EF8528F0F, 0xEB195275F83F0CFC, 0x1B043B9288C36169, 0x96B9E943BA727D64, 0x6F43CE71162D1D9A, 0xC1A39F7010D61D77,
0x8C4F2F69D1600F0D, 0x5230F9C8FAC3C731, 0xB287DDD4950F8126, 0xFA8CE5945D72F656, 0x25DD9E331EDFD293, 0x014A970E2B49D125,
0x5DE80CEA97D0E35F, 0xF1F9DF4B4315C942, 0x0F601DDE1DFC8BE4, 0x472FFF6B2F66EF31, 0x2518DD9597F17454, 0x5611D1920F16B5DA,
0xE48FB6768F2D137A, 0x134C4CD585D0E120, 0x0386AF14D659DD67, 0x89E0FEDAD17A82B8, 0xB8A94881E45B93E1, 0xB190D6AF3C2D5E7F,
0x75AC16E74E9F6324, 0xA64F8DC366285AC1, 0xD897420545E925D3, 0x7BFC475517A98310, 0x25D8F865BE7F9938, 0xFD4950E8B38DDB57,
0x74DB9ADD216377BE, 0x049D204411537835, 0x4E831BDECE3F801B, 0xA6EEDE68D106FA11, 0xFC60A11EE35542DD, 0x8B020BA77BED9689,
}, {           0x0, 0xFFFFFFFFFFFFFFFB, 0x9E5695B8575B60A1, 0xFD205D4F5940E2F5, 0xD9979A2F952A1CC2, 0x29D8F0C08D63A4E1,
0xB429FB9AC46ACE02, 0x5832202F22B96457, 0xF60A96EFE94089B1, 0x44CFBA782C7D6254, 0xD34B6A3646A675B4, 0x074FDF90813799BE,
0xB7E917637ADA41E4, 0x7AAAD536A15C8D48, 0x964393DAC65948CA, 0xA843864BA83E060B, 0xAD160A9F5B903F78, 0x06BF21F4A141EEC9,
0x8800BD3C9685A0E6, 0x7C6FD1ED56F6CA3C, 0xA3ABA8F169DB89A9, 0x9B67F9A32B1D17FD, 0xC419326A823CE559, 0xFAACFE23A0527BA2,
0x4BB3DD4878CC5830, 0xACD0D3F6D0577EE6, 0x730CC979494852BC, 0xD6B43FD027EA26AA, 0x488579BDDEC0BF75, 0x9046F83E8271CB72,
0x2C85F7140EC0F987, 0x72C541582169AC9B, 0x2D09E8E5C74401FE, 0x0F0D559E9ABBBC0B, 0xC1AD90CF87A820FB, 0x49C6F9017D476338,
0x481D02AA8CDBF445, 0x9198AF49ABAA4297, 0xD6F6E3124E21133A, 0xD7C56D60B0096D34, 0x7D0CBCB534229588, 0xF29E44EAD27E24A2,
0x3D7157F3F0723B6F, 0x972050FE135E9209, 0xB14907F54E17507C, 0x68DB7FC0AF16029C, 0x40DFEB572549D8AC, 0x36547BA6EC4B1E3B,
0x67F95CB3DD294C3B, 0x29640A003CF6CB98, 0x8D9321DC903EDCBF, 0xDC0AFE5B488E5FD7, 0xF9846E9FEF64DA6C, 0x132774AD80F480C8,
}, {           0x0, 0xFFFFFFFFFFFFFFFB, 0xF81FF74AC9CF45B7, 0xAD2F4581285D26DF, 0x1F8907F4C703EF94, 0x52B0328755D2C4C5,
0xEA804E0D869DCA75, 0xDA3EA9AA20DACE9B, 0x2B20DEA737D20417, 0xAF566773E1230958, 0x6708A564015633C1, 0x657F7E84B9CD89D2,
0x4DE46873E063C235, 0xA95DDC126847C42B, 0xA85B588D1987822F, 0x6E9ACE775ECC91C0, 0xF5053A2AAD161768, 0x5BA4CF55A6E985D0,
0x90CD141DDC76974B, 0x7110AC9F9C21818F, 0xE15E59A946ADD19B, 0x85B3A5A2EBD137F9, 0xD717EB8290EB0B5D, 0xCC7F88218B6F6CE6,
0x80DE090CCBB4B773, 0xB149EDB52AED580E, 0x71170B813D12882F, 0xC37EEF0E058DE855, 0x194426E433920145, 0x4CAB3736FD56202F,
0xC534E02C2891E930, 0x634FEA232F7BBBE5, 0x6E34FD04E35A00AC, 0x8BBB5AF1B56E8399, 0xE4329C1B3BFFCE97, 0x4A210925553054FF,
0x3FA872CFA20E9CC9, 0x70E87D351509B6C1, 0xB8B7B4ECCBEF99FD, 0xBC71C1883EFF7CDE, 0x8747EA4CB7D4FCB2, 0x78A9097AD542ABBD,
0x3FC151E98AB4A968, 0x1E17F1B5CDEA6B41, 0xD35FE31A40A57D2D, 0xA6908BB5081FD56D, 0x09F5EF29096E0945, 0x5884D41F527E2695,
0x3AC78A4DB21ED7FA, 0xD92258F3A0824453, 0x351871DDBAF8F81E, 0x77382DD6D45F9FBF, 0xF9E371DE85700AD7, 0x293F550550DA6688,
}, {           0x0, 0xFFFFFFFFFFFFFFFB, 0xE15CF516DB777704, 0x27B94243BE26B95F, 0x9C4DE2F6E8C671ED, 0x3DC483ECCC7EC922,
0x5FC63C7FE907251B, 0x85D83810557E590B, 0x998814A0CF2642B5, 0x915799640BABB788, 0x464BB0C59D46BC76, 0x441912153232D82E,
0x2DFB4B7D7D5BC401, 0x612D1E417D4AB7D2, 0x9C8E37E3E2C194BA, 0xCB8843A0497AFFBB, 0xF48E108785F8DEEE, 0x9E201452E2A809C5,
0x7CE685FA106F090F, 0xBF2A123C7588300E, 0xEAA9671FC5151A28, 0x25A9CD439781B673, 0xB23F069B11BB4C81, 0x7D2424EB5EB2D26B,
0x48F7A108ADE95CA1, 0xBA8CE23A875F1485, 0xC13828A81E383A73, 0x8D28849D1B62B8C9, 0xAC9258A88FB78B55, 0x89AA01376E24D404,
0xAD23EDA41D81D017, 0x1687BEF31CAF950F, 0xE3D0764E1337060C, 0xDD8DCBA09DB2A17F, 0xF1F32D0D283D16CB, 0x66FEDA21A2405F2D,
0xCF500622848301B7, 0x8C746AE01A9A62FF, 0xFABF58350247F882, 0x3214A332A3579405, 0xEF84A7AF84B0BE03, 0x60EEDAFB0DC78553,
0x6B93C6B7467612C7, 0xFC35EDD9A4FCA2B7, 0x6D453ABA7EC5D736, 0x6A40B7B52E4D599F, 0x9BEE2003A12535AD, 0x19FA36A84C9BAAD1,
0xFB4FC1D562C3ACD7, 0x8DA460413C0C3DD1, 0x4AD39518AF52BD2C, 0x323CA0D08594A4FD, 0x6FF64CC677D2CDDA, 0xEC1A765C924A5C77,
}, {           0x0, 0xFFFFFFFFFFFFFFFB, 0x76A16177A1E2E2C9, 0xCAA0297F16565427, 0x83DA4E5AD626EE8D, 0x2C12525F231E12E3,
0x4CFCAE79EBF17058, 0xF407496364DD840E, 0x47389D2030031C5A, 0x7A4A45439EA26563, 0x7AB6B5DE6C4128F7, 0x87B6A174C19B9C8E,
0x937F8BB3A129B617, 0xDAB38702A68C3779, 0x6CF07C8E1168666D, 0x4509D37E6F27B4F6, 0x21BC89DF949814D6, 0x31CD9BE0CE4F74C1,
0xE796A99946F04C47, 0xBDAF28D1463CFCD3, 0x938EAA01757BD617, 0x64F2B63238006584, 0x9AACD2E55EE81C51, 0x10EB1BAFA23A0F5C,
0x2478E8B6868A1BE4, 0x72DF80E33F5654E5, 0xEA3210DACFBEBB5A, 0xDAF429AD9CEAEBDD, 0xE2DE5795E4EE5531, 0x2C10388C6CD0E676,
0xF8A2342C8BBC8AE8, 0x736AD23AD19CF4F9, 0x89C6F025CF04F928, 0x0803BA29C8B75A81, 0x3CA90F153F4A44D5, 0x0C70C612BD04A785,
0x4CD2B6822A752CE5, 0x9B574139CAA16D98, 0x2EC43327C6F1E89A, 0x2E595FEE5E560620, 0x538922C34E526FB9, 0x90F922264720B0C1,
0x644B5512BBA05553, 0x15EC165B92663E15, 0x636F89A7F91427C5, 0xAC69AAC9B55C85FA, 0x64640FE55568B8EB, 0x62645F5578207FFE,
0x04B94BA5C642A978, 0x2318FA1C70FA0FA1, 0x9E0EBA8B2E28E0A9, 0x262536E837F64F0E, 0x98837FE448A2A312, 0x34083CE981261B28,
} }, { {       0x0, 0xFFFFFFFFFFFFFFFB, 0x75B5D53243BFACA1, 0x2F60E597908B3A0E, 0x7890F880598D9DDF, 0xFD0712976AAEC37E,
0x339E1794DE6CBCB1, 0xA135EB69C637576A, 0xFD82CEF2CDE56A5E, 0x1A1481FE819B29ED, 0xEBC2E9AF555859FC, 0x47FE3919F9FB6DD6,
0x6B926FAB3E8FA718, 0xD5CDC9E3EBF645DD, 0xE16E92950A1DF8FE, 0x725D52F0B3480B94, 0xC417AE5F16F5E1AA, 0x0767854C042BD477,
0xCC5A71ADD958E1E4, 0xBF90C656D7D08C5B, 0xF430A64E81B8F6AE, 0x9C08111ABEABC8A3, 0xEB287B695C2A00BA, 0x072FC62230097F72,
0x585AB2B4E6BA8890, 0x11C443E56ABE271E, 0xB6012A4BE30DBAD4, 0x5D1B307C316A595E, 0xF9AE104270A683AA, 0x35CDB4F5E3FE2705,
0x4BB461449DB85D08, 0x364D46181B227E8B, 0xDB3518FF8CC2EEF8, 0x719472A793A9AED8, 0xEF5CDBFDF48437C5, 0x1A041A6B40DEA7A2,
0x5699CAD78EB5BEEC, 0x053F40DEBCECD293, 0xBA6E946DB8A3CAB7, 0xFBAA71F1B26145EB, 0x9ACB3E4CED494572, 0x19C1A9CD2B66FD6B,
0x7FA896AF62C196D3, 0x4EF4B7C692DF60F2, 0x48067FA25810E1E2, 0xFA91DC15E3B31536, 0x565CBD0421C55EC0, 0xC00159716E6BB41C,
0x6E99E9172D558C6B, 0xDDC84F5197C974ED, 0x9287A7DDD2919913, 0x7ACB0787907724EA, 0x9D97C13FC1FAC1E5, 0x9AC5F70A6918E9B4,
}, {           0x0, 0xFFFFFFFFFFFFFFFB, 0x61A96A47A8A49F5E, 0xC42B1D5931969681, 0x3E9D8A2521FB45DB, 0x19FAACA8B88CEBEB,
0x3AFE224D8DF1531D, 0x93AD017E1A9273C8, 0x5AC2476882F245FF, 0x7290E950C1C4B5F5, 0x57EE3DC40E29AFAC, 0x835D61AE5944712A,
0xEEDD53225CA2314D, 0x9D5360233D8A3B68, 0x5ACA025CDA9DDA86, 0x233063164CF9913E, 0xB1E02E7E0786D634, 0x9BEF1B94F976865E,
0xF59892341CAE9B70, 0xA4172F7E7335FF1D, 0x5209C0979C796338, 0x5DE00D8A541A9636, 0x7787CAACB9DC72E5, 0xAFCEEC215DDB5B1F,
0x342D56194B23C2DD, 0x9D3456BF1E7EBC91, 0x2538B0AF1B532EFB, 0x3F36AF2678425F08, 0x5DD163D96A90B53B, 0x52C7BC12BE1CD823,
0x687BBDAFF2FCB074, 0x84A103942E758F1E, 0xBDFFF7908FCF6EAF, 0x9A88FEAB29F7304A, 0x79B320225520C961, 0xFFD7B46C0FB6E749,
0xAFF792228F33D041, 0x14FDCFC2A369F4C1, 0xD95737C2AFCBB936, 0xF8F6A582F2B93AE7, 0xA77AA68422F806AB, 0x8D3E64EDB0D7337B,
0xED166A7E67CC91D1, 0x1F0BB545802B8637, 0xB7E303181E7C52D6, 0x63B6AF4D636BB556, 0xEF25ED8E46774A91, 0x44A1D4BF34BE95E4,
0x10A066918AA64844, 0x4CC959935E55ACA5, 0xE47E5F6C9CA08F2E, 0x0158E3069B12FF97, 0xF195A762401A93E7, 0x7F07C35059DA7D23,
}, {           0x0, 0xFFFFFFFFFFFFFFFB, 0x07E008B53630BA48, 0xB2C6AE8ABD08732D, 0xF676CF2160E99B42, 0xBAD3445B229A6044,
0xA17388C346F0A423, 0x0F4482D13F5732F1, 0xC9EB7597EECF29C3, 0x45C60D5797324242, 0x3A6FEE919BEAE7D2, 0x356BA11B5305BA62,
0x98E256DADA97D5F7, 0x3235E3EE9DB6B6E6, 0x37ECD101ACE2A5D1, 0xB4056AF22351822A, 0x6859989749AC2400, 0x70F4B72DF97B4FFE,
0xEE8E28738F8AB294, 0x1021CF4D3BC17A4C, 0x7B98254B38C8D9ED, 0xCE354A47032296BB, 0xAF33C321C5FFFA0B, 0xF03F0C800E474141,
0x5B949D8B16C12038, 0x977169E234F0A336, 0x61AE2F60800B21C5, 0x1D493BA83AD23803, 0xBF67168746056C9B, 0x633B6E261DCE3266,
0x953549E39F4E9A65, 0xED4318B5D31BE361, 0xA09184865982C993, 0x10393D2D92DD689B, 0xE4AC01EA3C1D6E46, 0xE716F64CF7961855,
0x8C781167595C0E3A, 0x1D5916CD1740C45F, 0xCE503204186A7C53, 0x0C8EB80707EA19A3, 0x55B00721871CE573, 0x39F023B0F06524BC,
0xB6B08B7B9E2D112C, 0x452C1B0167A9F7A5, 0x9C192B9E0C3575DC, 0x582BC12F39293625, 0x9BE0F88A1E1DEB13, 0x78E874A7F3C1F462,
0x83651464E85BDC31, 0xDF3016F98837DF40, 0x815D7CF2A9717A46, 0x65B2E51E18F8A6D7, 0xE49988C4FD0C9FD8, 0x9919EEDB12084B17,
}, {           0x0, 0xFFFFFFFFFFFFFFFB, 0x1EA30AE9248888FB, 0x2D7D5879EEBC4156, 0x501790936D371D39, 0x83850FB157AF43D0,
0x8EB2DFA9F5DCE214, 0x713237F434663B5B, 0x49B3286D83815762, 0xCBA353DD73BC6C6F, 0x38884B173DE8FC88, 0x8715DAF8187126C4,
0x9CF6AB670E4C7236, 0x02A33692F6D0CC7B, 0x018BECF3CEF49A87, 0x105AF844EBED7D36, 0x11A43D602A5C8F2E, 0x905C6AD50B41FFB3,
0x721417D566AAE9E5, 0x122AF5C5BADEE4D6, 0x60871DC1BAC189A8, 0x47A0A3BB76DBBE2D, 0xB4816CED1A0E2058, 0xC3E5FEBC74BF618C,
0xC76AD018413C96D4, 0xF2CBF560814DBD6F, 0x0440931658BC0365, 0x67CD527311DCC6A6, 0x03CE76A7C882134B, 0x2BC8A0487644B13C,
0x48EAC0A1548B4E84, 0x38E53FC69DED038B, 0xCF29D2ED821F3EF3, 0x578B128AA13AC078, 0x745CAAACFDB77688, 0x70875FF18B1ADA10,
0x0C4D0A7DBF77E9CC, 0x30082111EE67B300, 0x0A82A9A6042F9D36, 0xBB6DD49D925CC9CE, 0x7FCF43810432CA78, 0xFAFF3DDFE152B756,
0x453BD8547D8C3EB8, 0x2A478E93BE6045C5, 0xC47BD8556B3D536F, 0x27855832B03D4C28, 0x6D8DFF5137897A4D, 0x5C8EDA0AE0E0D95E,
0xE50BFDB3DA50A199, 0xEC93B647511F0CED, 0xB3C9FBEDDC143C8A, 0xB104BC9333C87262, 0x38FD1519A84DB0E9, 0x88F712A4FE12EE94,
}, {           0x0, 0xFFFFFFFFFFFFFFFB, 0x895E9E885E1D1D36, 0xAC05742DC629EE47, 0xC9902AAE6356D26E, 0x64FAE0F67CF87BCB,
0xA290743F81D963CE, 0x1D563220657F0488, 0xE4E007707862610A, 0x08F4395706A6FDA2, 0xEEF03CED19766F71, 0x10B23D807DB841C9,
0xCE0B2CE1E972E8C9, 0x559A5FFB1722631F, 0x7BEF8C0DE198D567, 0xD158B39F3A811D00, 0xD75B8EC358A2F81D, 0xBA02ED1D734B441F,
0x4C043CF5FEF7A935, 0x3D0BAC5703268313, 0x5FC55AAE4AE83AC5, 0xFFBC62E2B5A759BD, 0x2ACCE9E153ADCA70, 0x6F181E7251BE0B3C,
0x6520B40750B1DDDE, 0xDD63FD529D78529A, 0xB63A527E44787D46, 0x768260CF3F5EC30E, 0x9AF3D83D9654110F, 0x697F895C71F17DB1,
0x3284199667217919, 0x8357F6DF9E24DC18, 0x765802911E22F8DE, 0x33DB47D0D53881CD, 0xFF3B2E79C381BF60, 0x561E217216E7FD70,
0xC39162D58463D185, 0x8496454A7AC869F8, 0xDB660203BC51966B, 0x138677216F6E1513, 0x6329948FE6D855C6, 0x7AD2D493D707C0E7,
0xA115F4F822BF0297, 0x9E0CBFCC569591A6, 0xDC79B92E44B6A5D4, 0xDF08CFB6474C2B42, 0xFA43C3D1DF2D5D51, 0x38D3FF15AA1584A8,
0x09DF55A9FC8B07FB, 0xC2C5E147D2D01FD8, 0x2DBFCC442C26B56D, 0xCCFF77AD05FAF6BD, 0x8BCF66DD254993B6, 0xAF98859F76EFA5E5,
} } }; static const ulbn_limb_t ulbnfft_len_inv[ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = { {
0x0000000000000001, 0x1A30000000000001, 0x2748000000000001, 0x2DD4000000000001, 0x311A000000000001, 0x32BD000000000001,
0x338E800000000001, 0x33F7400000000001, 0x342BA00000000001, 0x3445D00000000001, 0x3452E80000000001, 0x3459740000000001,
0x345CBA0000000001, 0x345E5D0000000001, 0x345F2E8000000001, 0x345F974000000001, 0x345FCBA000000001, 0x345FE5D000000001,
0x345FF2E800000001, 0x345FF97400000001, 0x345FFCBA00000001, 0x345FFE5D00000001, 0x345FFF2E80000001, 0x345FFF9740000001,
0x345FFFCBA0000001, 0x345FFFE5D0000001, 0x345FFFF2E8000001, 0x345FFFF974000001, 0x345FFFFCBA000001, 0x345FFFFE5D000001,
0x345FFFFF2E800001, 0x345FFFFF97400001, 0x345FFFFFCBA00001, 0x345FFFFFE5D00001, 0x345FFFFFF2E80001, 0x345FFFFFF9740001,
0x345FFFFFFCBA0001, 0x345FFFFFFE5D0001, 0x345FFFFFFF2E8001, 0x345FFFFFFF974001, 0x345FFFFFFFCBA001, 0x345FFFFFFFE5D001,
0x345FFFFFFFF2E801, 0x345FFFFFFFF97401, 0x345FFFFFFFFCBA01, 0x345FFFFFFFFE5D01, 0x345FFFFFFFFF2E81, 0x345FFFFFFFFF9741,
0x345FFFFFFFFFCBA1, 0x345FFFFFFFFFE5D1, 0x345FFFFFFFFFF2E9, 0x345FFFFFFFFFF975, 0x345FFFFFFFFFFCBB, 0x345FFFFFFFFFFE5E,
}, {           0x1, 0x1C10000000000001, 0x2A18000000000001, 0x311C000000000001, 0x349E000000000001, 0x365F000000000001,
0x373F800000000001, 0x37AFC00000000001, 0x37E7E00000000001, 0x3803F00000000001, 0x3811F80000000001, 0x3818FC0000000001,
0x381C7E0000000001, 0x381E3F0000000001, 0x381F1F8000000001, 0x381F8FC000000001, 0x381FC7E000000001, 0x381FE3F000000001,
0x381FF1F800000001, 0x381FF8FC00000001, 0x381FFC7E00000001, 0x381FFE3F00000001, 0x381FFF1F80000001, 0x381FFF8FC0000001,
0x381FFFC7E0000001, 0x381FFFE3F0000001, 0x381FFFF1F8000001, 0x381FFFF8FC000001, 0x381FFFFC7E000001, 0x381FFFFE3F000001,
0x381FFFFF1F800001, 0x381FFFFF8FC00001, 0x381FFFFFC7E00001, 0x381FFFFFE3F00001, 0x381FFFFFF1F80001, 0x381FFFFFF8FC0001,
0x381FFFFFFC7E0001, 0x381FFFFFFE3F0001, 0x381FFFFFFF1F8001, 0x381FFFFFFF8FC001, 0x381FFFFFFFC7E001, 0x381FFFFFFFE3F001,
0x381FFFFFFFF1F801, 0x381FFFFFFFF8FC01, 0x381FFFFFFFFC7E01, 0x381FFFFFFFFE3F01, 0x381FFFFFFFFF1F81, 0x381FFFFFFFFF8FC1,
0x381FFFFFFFFFC7E1, 0x381FFFFFFFFFE3F1, 0x381FFFFFFFFFF1F9, 0x381FFFFFFFFFF8FD, 0x381FFFFFFFFFFC7F, 0x381FFFFFFFFFFE40,
}, {           0x1, 0x1CB0000000000001, 0x2B08000000000001, 0x3234000000000001, 0x35CA000000000001, 0x3795000000000001,
0x387A800000000001, 0x38ED400000000001, 0x3926A00000000001, 0x3943500000000001, 0x3951A80000000001, 0x3958D40000000001,
0x395C6A0000000001, 0x395E350000000001, 0x395F1A8000000001, 0x395F8D4000000001, 0x395FC6A000000001, 0x395FE35000000001,
0x395FF1A800000001, 0x395FF8D400000001, 0x395FFC6A00000001, 0x395FFE3500000001, 0x395FFF1A80000001, 0x395FFF8D40000001,
0x395FFFC6A0000001, 0x395FFFE350000001, 0x395FFFF1A8000001, 0x395FFFF8D4000001, 0x395FFFFC6A000001, 0x395FFFFE35000001,
0x395FFFFF1A800001, 0x395FFFFF8D400001, 0x395FFFFFC6A00001, 0x395FFFFFE3500001, 0x395FFFFFF1A80001, 0x395FFFFFF8D40001,
0x395FFFFFFC6A0001, 0x395FFFFFFE350001, 0x395FFFFFFF1A8001, 0x395FFFFFFF8D4001, 0x395FFFFFFFC6A001, 0x395FFFFFFFE35001,
0x395FFFFFFFF1A801, 0x395FFFFFFFF8D401, 0x395FFFFFFFFC6A01, 0x395FFFFFFFFE3501, 0x395FFFFFFFFF1A81, 0x395FFFFFFFFF8D41,
0x395FFFFFFFFFC6A1, 0x395FFFFFFFFFE351, 0x395FFFFFFFFFF1A9, 0x395FFFFFFFFFF8D5, 0x395FFFFFFFFFFC6B, 0x395FFFFFFFFFFE36,
}, {           0x1, 0x1D70000000000001, 0x2C28000000000001, 0x3384000000000001, 0x3732000000000001, 0x3909000000000001,
0x39F4800000000001, 0x3A6A400000000001, 0x3AA5200000000001, 0x3AC2900000000001, 0x3AD1480000000001, 0x3AD8A40000000001,
0x3ADC520000000001, 0x3ADE290000000001, 0x3ADF148000000001, 0x3ADF8A4000000001, 0x3ADFC52000000001, 0x3ADFE29000000001,
0x3ADFF14800000001, 0x3ADFF8A400000001, 0x3ADFFC5200000001, 0x3ADFFE2900000001, 0x3ADFFF1480000001, 0x3ADFFF8A40000001,
0x3ADFFFC520000001, 0x3ADFFFE290000001, 0x3ADFFFF148000001, 0x3ADFFFF8A4000001, 0x3ADFFFFC52000001, 0x3ADFFFFE29000001,
0x3ADFFFFF14800001, 0x3ADFFFFF8A400001, 0x3ADFFFFFC5200001, 0x3ADFFFFFE2900001, 0x3ADFFFFFF1480001, 0x3ADFFFFFF8A40001,
0x3ADFFFFFFC520001, 0x3ADFFFFFFE290001, 0x3ADFFFFFFF148001, 0x3ADFFFFFFF8A4001, 0x3ADFFFFFFFC52001, 0x3ADFFFFFFFE29001,
0x3ADFFFFFFFF14801, 0x3ADFFFFFFFF8A401, 0x3ADFFFFFFFFC5201, 0x3ADFFFFFFFFE2901, 0x3ADFFFFFFFFF1481, 0x3ADFFFFFFFFF8A41,
0x3ADFFFFFFFFFC521, 0x3ADFFFFFFFFFE291, 0x3ADFFFFFFFFFF149, 0x3ADFFFFFFFFFF8A5, 0x3ADFFFFFFFFFFC53, 0x3ADFFFFFFFFFFE2A,
}, {           0x1, 0x1F50000000000001, 0x2EF8000000000001, 0x36CC000000000001, 0x3AB6000000000001, 0x3CAB000000000001,
0x3DA5800000000001, 0x3E22C00000000001, 0x3E61600000000001, 0x3E80B00000000001, 0x3E90580000000001, 0x3E982C0000000001,
0x3E9C160000000001, 0x3E9E0B0000000001, 0x3E9F058000000001, 0x3E9F82C000000001, 0x3E9FC16000000001, 0x3E9FE0B000000001,
0x3E9FF05800000001, 0x3E9FF82C00000001, 0x3E9FFC1600000001, 0x3E9FFE0B00000001, 0x3E9FFF0580000001, 0x3E9FFF82C0000001,
0x3E9FFFC160000001, 0x3E9FFFE0B0000001, 0x3E9FFFF058000001, 0x3E9FFFF82C000001, 0x3E9FFFFC16000001, 0x3E9FFFFE0B000001,
0x3E9FFFFF05800001, 0x3E9FFFFF82C00001, 0x3E9FFFFFC1600001, 0x3E9FFFFFE0B00001, 0x3E9FFFFFF0580001, 0x3E9FFFFFF82C0001,
0x3E9FFFFFFC160001, 0x3E9FFFFFFE0B0001, 0x3E9FFFFFFF058001, 0x3E9FFFFFFF82C001, 0x3E9FFFFFFFC16001, 0x3E9FFFFFFFE0B001,
0x3E9FFFFFFFF05801, 0x3E9FFFFFFFF82C01, 0x3E9FFFFFFFFC1601, 0x3E9FFFFFFFFE0B01, 0x3E9FFFFFFFFF0581, 0x3E9FFFFFFFFF82C1,
0x3E9FFFFFFFFFC161, 0x3E9FFFFFFFFFE0B1, 0x3E9FFFFFFFFFF059, 0x3E9FFFFFFFFFF82D, 0x3E9FFFFFFFFFFC17, 0x3E9FFFFFFFFFFE0C,
} }; static const ulbn_limb_t ulbnfft_len_inv_finv[ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = { {
0x0000000000000004, 0x8000000000000002, 0xC000000000000001, 0xE000000000000000, 0xF000000000000000, 0xF800000000000000,
0xFC00000000000000, 0xFE00000000000000, 0xFF00000000000000, 0xFF80000000000000, 0xFFC0000000000000, 0xFFE0000000000000,
0xFFF0000000000000, 0xFFF8000000000000, 0xFFFC000000000000, 0xFFFE000000000000, 0xFFFF000000000000, 0xFFFF800000000000,
0xFFFFC00000000000, 0xFFFFE00000000000, 0xFFFFF00000000000, 0xFFFFF80000000000, 0xFFFFFC0000000000, 0xFFFFFE0000000000,
0xFFFFFF0000000000, 0xFFFFFF8000000000, 0xFFFFFFC000000000, 0xFFFFFFE000000000, 0xFFFFFFF000000000, 0xFFFFFFF800000000,
0xFFFFFFFC00000000, 0xFFFFFFFE00000000, 0xFFFFFFFF00000000, 0xFFFFFFFF80000000, 0xFFFFFFFFC0000000, 0xFFFFFFFFE0000000,
0xFFFFFFFFF0000000, 0xFFFFFFFFF8000000, 0xFFFFFFFFFC000000, 0xFFFFFFFFFE000000, 0xFFFFFFFFFF000000, 0xFFFFFFFFFF800000,
0xFFFFFFFFFFC00000, 0xFFFFFFFFFFE00000, 0xFFFFFFFFFFF00000, 0xFFFFFFFFFFF80000, 0xFFFFFFFFFFFC0000, 0xFFFFFFFFFFFE0000,
0xFFFFFFFFFFFF0000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFFC000, 0xFFFFFFFFFFFFE000, 0xFFFFFFFFFFFFF000, 0xFFFFFFFFFFFFF800,
}, {           0x4, 0x8000000000000002, 0xC000000000000001, 0xE000000000000000, 0xF000000000000000, 0xF800000000000000,
0xFC00000000000000, 0xFE00000000000000, 0xFF00000000000000, 0xFF80000000000000, 0xFFC0000000000000, 0xFFE0000000000000,
0xFFF0000000000000, 0xFFF8000000000000, 0xFFFC000000000000, 0xFFFE000000000000, 0xFFFF000000000000, 0xFFFF800000000000,
0xFFFFC00000000000, 0xFFFFE00000000000, 0xFFFFF00000000000, 0xFFFFF80000000000, 0xFFFFFC0000000000, 0xFFFFFE0000000000,
0xFFFFFF0000000000, 0xFFFFFF8000000000, 0xFFFFFFC000000000, 0xFFFFFFE000000000, 0xFFFFFFF000000000, 0xFFFFFFF800000000,
0xFFFFFFFC00000000, 0xFFFFFFFE00000000, 0xFFFFFFFF00000000, 0xFFFFFFFF80000000, 0xFFFFFFFFC0000000, 0xFFFFFFFFE0000000,
0xFFFFFFFFF0000000, 0xFFFFFFFFF8000000, 0xFFFFFFFFFC000000, 0xFFFFFFFFFE000000, 0xFFFFFFFFFF000000, 0xFFFFFFFFFF800000,
0xFFFFFFFFFFC00000, 0xFFFFFFFFFFE00000, 0xFFFFFFFFFFF00000, 0xFFFFFFFFFFF80000, 0xFFFFFFFFFFFC0000, 0xFFFFFFFFFFFE0000,
0xFFFFFFFFFFFF0000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFFC000, 0xFFFFFFFFFFFFE000, 0xFFFFFFFFFFFFF000, 0xFFFFFFFFFFFFF800,
}, {           0x4, 0x8000000000000002, 0xC000000000000001, 0xE000000000000000, 0xF000000000000000, 0xF800000000000000,
0xFC00000000000000, 0xFE00000000000000, 0xFF00000000000000, 0xFF80000000000000, 0xFFC0000000000000, 0xFFE0000000000000,
0xFFF0000000000000, 0xFFF8000000000000, 0xFFFC000000000000, 0xFFFE000000000000, 0xFFFF000000000000, 0xFFFF800000000000,
0xFFFFC00000000000, 0xFFFFE00000000000, 0xFFFFF00000000000, 0xFFFFF80000000000, 0xFFFFFC0000000000, 0xFFFFFE0000000000,
0xFFFFFF0000000000, 0xFFFFFF8000000000, 0xFFFFFFC000000000, 0xFFFFFFE000000000, 0xFFFFFFF000000000, 0xFFFFFFF800000000,
0xFFFFFFFC00000000, 0xFFFFFFFE00000000, 0xFFFFFFFF00000000, 0xFFFFFFFF80000000, 0xFFFFFFFFC0000000, 0xFFFFFFFFE0000000,
0xFFFFFFFFF0000000, 0xFFFFFFFFF8000000, 0xFFFFFFFFFC000000, 0xFFFFFFFFFE000000, 0xFFFFFFFFFF000000, 0xFFFFFFFFFF800000,
0xFFFFFFFFFFC00000, 0xFFFFFFFFFFE00000, 0xFFFFFFFFFFF00000, 0xFFFFFFFFFFF80000, 0xFFFFFFFFFFFC0000, 0xFFFFFFFFFFFE0000,
0xFFFFFFFFFFFF0000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFFC000, 0xFFFFFFFFFFFFE000, 0xFFFFFFFFFFFFF000, 0xFFFFFFFFFFFFF800,
}, {           0x4, 0x8000000000000002, 0xC000000000000001, 0xE000000000000000, 0xF000000000000000, 0xF800000000000000,
0xFC00000000000000, 0xFE00000000000000, 0xFF00000000000000, 0xFF80000000000000, 0xFFC0000000000000, 0xFFE0000000000000,
0xFFF0000000000000, 0xFFF8000000000000, 0xFFFC000000000000, 0xFFFE000000000000, 0xFFFF000000000000, 0xFFFF800000000000,
0xFFFFC00000000000, 0xFFFFE00000000000, 0xFFFFF00000000000, 0xFFFFF80000000000, 0xFFFFFC0000000000, 0xFFFFFE0000000000,
0xFFFFFF0000000000, 0xFFFFFF8000000000, 0xFFFFFFC000000000, 0xFFFFFFE000000000, 0xFFFFFFF000000000, 0xFFFFFFF800000000,
0xFFFFFFFC00000000, 0xFFFFFFFE00000000, 0xFFFFFFFF00000000, 0xFFFFFFFF80000000, 0xFFFFFFFFC0000000, 0xFFFFFFFFE0000000,
0xFFFFFFFFF0000000, 0xFFFFFFFFF8000000, 0xFFFFFFFFFC000000, 0xFFFFFFFFFE000000, 0xFFFFFFFFFF000000, 0xFFFFFFFFFF800000,
0xFFFFFFFFFFC00000, 0xFFFFFFFFFFE00000, 0xFFFFFFFFFFF00000, 0xFFFFFFFFFFF80000, 0xFFFFFFFFFFFC0000, 0xFFFFFFFFFFFE0000,
0xFFFFFFFFFFFF0000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFFC000, 0xFFFFFFFFFFFFE000, 0xFFFFFFFFFFFFF000, 0xFFFFFFFFFFFFF800,
}, {           0x4, 0x8000000000000002, 0xC000000000000001, 0xE000000000000000, 0xF000000000000000, 0xF800000000000000,
0xFC00000000000000, 0xFE00000000000000, 0xFF00000000000000, 0xFF80000000000000, 0xFFC0000000000000, 0xFFE0000000000000,
0xFFF0000000000000, 0xFFF8000000000000, 0xFFFC000000000000, 0xFFFE000000000000, 0xFFFF000000000000, 0xFFFF800000000000,
0xFFFFC00000000000, 0xFFFFE00000000000, 0xFFFFF00000000000, 0xFFFFF80000000000, 0xFFFFFC0000000000, 0xFFFFFE0000000000,
0xFFFFFF0000000000, 0xFFFFFF8000000000, 0xFFFFFFC000000000, 0xFFFFFFE000000000, 0xFFFFFFF000000000, 0xFFFFFFF800000000,
0xFFFFFFFC00000000, 0xFFFFFFFE00000000, 0xFFFFFFFF00000000, 0xFFFFFFFF80000000, 0xFFFFFFFFC0000000, 0xFFFFFFFFE0000000,
0xFFFFFFFFF0000000, 0xFFFFFFFFF8000000, 0xFFFFFFFFFC000000, 0xFFFFFFFFFE000000, 0xFFFFFFFFFF000000, 0xFFFFFFFFFF800000,
0xFFFFFFFFFFC00000, 0xFFFFFFFFFFE00000, 0xFFFFFFFFFFF00000, 0xFFFFFFFFFFF80000, 0xFFFFFFFFFFFC0000, 0xFFFFFFFFFFFE0000,
0xFFFFFFFFFFFF0000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFFC000, 0xFFFFFFFFFFFFE000, 0xFFFFFFFFFFFFF000, 0xFFFFFFFFFFFFF800,
} }; /* clang-format on */
ULBN_PRIVATE void _ulbn_init_fft(void) {
  (void)0;
}
  #else /* it seems that we must init table on runtime */
    #define ULBNFFT_NMODS 5
    #define ULBNFFT_MOD_LOG2_MIN (ULBN_LIMB_BITS - 3) /* ceil(log2(mods)) */
    #define ULBNFFT_MOD_LOG2_MAX (ULBN_LIMB_BITS - 2) /* ceil(log2(mods)) */
    #define ULBNFFT_PROOT_2EXP (ULBNFFT_MOD_LOG2_MIN - 8)
ul_static_assert(
  ULBNFFT_PROOT_2EXP < ULBNFFT_MOD_LOG2_MIN && ULBNFFT_PROOT_2EXP > 0, "`ulbn_limb_t` is too small to support NTT"
);

static ulbn_limb_t ulbnfft_mods[ULBNFFT_NMODS];
static ulbn_limb_t ulbnfft_mods_div[ULBNFFT_NMODS];
static unsigned ulbnfft_int_bits[ULBNFFT_NMODS];

static ulbn_limb_t ulbnfft_mods_cr[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2];
static ulbn_limb_t ulbnfft_mods_cr_finv[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2];

static ulbn_limb_t ulbnfft_proot_pow[2][ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1];
static ulbn_limb_t ulbnfft_proot_pow_finv[2][ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1];

static ulbn_limb_t ulbnfft_len_inv[ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1];
static ulbn_limb_t ulbnfft_len_inv_finv[ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1];


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


ULBN_PRIVATE ulbn_limb_t ulbnfft_mulmod(ulbn_limb_t a, ulbn_limb_t b, ulbn_limb_t m, ulbn_limb_t m_finv);
ULBN_PRIVATE ulbn_limb_t ulbnfft_mod_init(ulbn_limb_t m) {
  ulbn_limb_t q, r;
  const ulbn_limb_t ah = ulbn_cast_limb(ULBN_LIMB_SHL(1u, ULBNFFT_MOD_LOG2_MIN));
  _ulbn_udiv_(q, r, ah, 0, m);
  (void)r;
  return q;
}
ULBN_PRIVATE ulbn_limb_t ulbnfft_mulmod2_init(ulbn_limb_t b, ulbn_limb_t m);


ULBN_PRIVATE void ulbnfft_init_mods(ulbn_rand_t* rng) {
  static ul_constexpr const ulbn_limb_t LOWER_GUARD = ULBN_LIMB_SHL(1, ULBNFFT_MOD_LOG2_MIN);
  static ul_constexpr const ulbn_limb_t STEP_NUM = ULBN_LIMB_SHL(1, ULBNFFT_PROOT_2EXP) << 1;

  ulbn_limb_t m = ULBN_LIMB_SHL(1, ULBNFFT_MOD_LOG2_MAX) - 1;
  int mods = ULBNFFT_NMODS;
  m &= ULBN_LIMB_SHL(ULBN_LIMB_MAX, ULBNFFT_PROOT_2EXP);
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
  for(mods = 0; mods < ULBNFFT_NMODS; ++mods)
    ulbnfft_mods_div[mods] = ulbnfft_mod_init(ulbnfft_mods[mods]);
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
    ulbnfft_int_bits[mods] = ulbn_bit_width(mul, muln) - 1;
  }
}
ULBN_PRIVATE void ulbnfft_init_proot(ulbn_rand_t* rng) {
  int mods, inverse;
  unsigned exp;
  ulbnfft_factors_t ptr;
  ulbn_limb_t proot[2];
  ulbn_limb_t m, mdiv, min_proot;

  ptr.len = ptr.cap = 0;
  ptr.factors = ul_nullptr;
  for(mods = 0; mods < ULBNFFT_NMODS; ++mods) {
    m = ulbnfft_mods[mods];
    mdiv = ulbnfft_mods_div[mods];

    ulbnfft_factorize(rng, &ptr, m - 1);
    min_proot = ulbnfft_get_proot(&ptr, m);

    proot[0] = ulbnfft_powmod_slow(min_proot, m >> ULBNFFT_PROOT_2EXP, m);
    proot[1] = ulbnfft_invmod_slow(proot[0], m);
    /* printf("proot0 = 0x%llX, proot1 = 0x%llX\n", (unsigned long long)proot[0], (unsigned long long)proot[1]); */

    for(inverse = 0; inverse < 2; ++inverse) {
      ulbn_limb_t c = proot[inverse];
      for(exp = 0; exp < ULBNFFT_PROOT_2EXP; ++exp) {
        ulbnfft_proot_pow[inverse][mods][ULBNFFT_PROOT_2EXP - exp] = c;
        ulbnfft_proot_pow_finv[inverse][mods][ULBNFFT_PROOT_2EXP - exp] = ulbnfft_mulmod2_init(c, m);
        c = ulbnfft_mulmod(c, c, m, mdiv);
      }
    }
  }
}
ULBN_PRIVATE void ulbnfft_init_mods_cr(void) {
  int inv, mods, cnt = 0;
  for(inv = 0; inv < ULBNFFT_NMODS; ++inv)
    for(mods = inv + 1; mods < ULBNFFT_NMODS; ++mods) {
      /* 1/{MODS[inv]} (mod {MODS[mods]}) */
      ulbnfft_mods_cr[cnt] = ulbnfft_invmod_slow(ulbnfft_mods[inv], ulbnfft_mods[mods]);
      ulbnfft_mods_cr_finv[cnt] = ulbnfft_mulmod2_init(ulbnfft_mods_cr[cnt], ulbnfft_mods[mods]);
      ++cnt;
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
ULBN_PRIVATE void ulbnfft_init(void) {
  ulbn_rand_t rng;

  ulbn_rand_init(&rng);
  ulbnfft_init_mods(&rng);
  ulbnfft_init_int_bits();
  ulbnfft_init_proot(&rng);
  ulbnfft_init_mods_cr();
  ulbnfft_init_len_inv();

    #if 0
  {
    unsigned i, j, k;

    printf("#define ULBNFFT_NMODS %d\n", ulbn_cast_int(ULBNFFT_NMODS));
    printf("#define ULBNFFT_MOD_LOG2_MIN %d\n", ulbn_cast_int(ULBNFFT_MOD_LOG2_MIN));
    printf("#define ULBNFFT_MOD_LOG2_MAX %d\n", ulbn_cast_int(ULBNFFT_MOD_LOG2_MAX));
    printf("#define ULBNFFT_PROOT_2EXP %d\n", ulbn_cast_int(ULBNFFT_PROOT_2EXP));

    printf("static const ulbn_limb_t ulbnfft_mods[ULBNFFT_NMODS] = {");
    for(i = 0; i < ULBNFFT_NMODS; ++i)
      printf("0x%llX, ", ul_static_cast(unsigned long long, ulbnfft_mods[i]));
    printf("};\n");

    printf("static const ulbn_limb_t ulbnfft_mods_div[ULBNFFT_NMODS] = {");
    for(i = 0; i < ULBNFFT_NMODS; ++i)
      printf("0x%llX, ", ul_static_cast(unsigned long long, ulbnfft_mods_div[i]));
    printf("};\n");

    printf("static const unsigned ulbnfft_int_bits[ULBNFFT_NMODS] = {");
    for(i = 0; i < ULBNFFT_NMODS; ++i)
      printf("%u, ", ulbnfft_int_bits[i]);
    printf("};\n");

    printf("static const ulbn_limb_t ulbnfft_mods_cr[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2] = {");
    for(i = 0; i < ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2; ++i)
      printf("0x%llX, ", ul_static_cast(unsigned long long, ulbnfft_mods_cr[i]));
    printf("};\n");

    printf("static const ulbn_limb_t ulbnfft_mods_cr_finv[ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2] = {");
    for(i = 0; i < ULBNFFT_NMODS * (ULBNFFT_NMODS - 1) / 2; ++i)
      printf("0x%llX, ", ul_static_cast(unsigned long long, ulbnfft_mods_cr_finv[i]));
    printf("};\n");

      #define _ULBNFFT_INIT_FMT "%08llX"
    printf("static const ulbn_limb_t ulbnfft_proot_pow[2][ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = {");
    for(i = 0; i < 2; ++i) {
      printf("{");
      for(j = 0; j < ULBNFFT_NMODS; ++j) {
        printf("{");
        for(k = 0; k <= ULBNFFT_PROOT_2EXP; ++k)
          printf("0x" _ULBNFFT_INIT_FMT ", ", ul_static_cast(unsigned long long, ulbnfft_proot_pow[i][j][k]));
        printf("}, \n");
      }
      printf("}, \n");
    }
    printf("};\n");

    printf("static const ulbn_limb_t ulbnfft_proot_pow_finv[2][ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = {");
    for(i = 0; i < 2; ++i) {
      printf("{");
      for(j = 0; j < ULBNFFT_NMODS; ++j) {
        printf("{");
        for(k = 0; k <= ULBNFFT_PROOT_2EXP; ++k)
          printf("0x" _ULBNFFT_INIT_FMT ", ", ul_static_cast(unsigned long long, ulbnfft_proot_pow_finv[i][j][k]));
        printf("}, \n");
      }
      printf("}, \n");
    }
    printf("};\n");

    printf("static const ulbn_limb_t ulbnfft_len_inv[ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = {");
    for(i = 0; i < ULBNFFT_NMODS; ++i) {
      printf("{");
      for(j = 0; j <= ULBNFFT_PROOT_2EXP; ++j)
        printf("0x" _ULBNFFT_INIT_FMT ", ", ul_static_cast(unsigned long long, ulbnfft_len_inv[i][j]));
      printf("}, \n");
    }
    printf("};\n");

    printf("static const ulbn_limb_t ulbnfft_len_inv_finv[ULBNFFT_NMODS][ULBNFFT_PROOT_2EXP + 1] = {");
    for(i = 0; i < ULBNFFT_NMODS; ++i) {
      printf("{");
      for(j = 0; j <= ULBNFFT_PROOT_2EXP; ++j)
        printf("0x" _ULBNFFT_INIT_FMT ", ", ul_static_cast(unsigned long long, ulbnfft_len_inv_finv[i][j]));
      printf("}, \n");
    }
    printf("};\n");
  }
    #endif
}

    #if defined(__cplusplus)
struct _ULBN_FFT_INIT {
  _ULBN_FFT_INIT() noexcept {
    ulbnfft_init();
  }
};
ULBN_PRIVATE void _ulbn_init_fft(void) {
  static _ULBN_FFT_INIT autoinit;
  (void)autoinit;
}
      #define _ULBN_FFT_AUTOINIT
    #endif /* defined(__cplusplus) */

    #if !defined(_ULBN_FFT_AUTOINIT) && defined(__has_attribute) && !defined(UL_PEDANTIC)
      #if __has_attribute(constructor)
ULBN_PRIVATE __attribute__((constructor)) void _ulbnfft_autoinit(void) {
  ulbnfft_init();
}
ULBN_PRIVATE void _ulbn_init_fft(void) {
  (void)0;
}
        #define _ULBN_FFT_AUTOINIT
      #endif
    #endif /* !defined(_ULBN_FFT_AUTOINIT) && defined(__has_attribute) && !defined(UL_PEDANTIC) */

    #if !defined(_ULBN_FFT_AUTOINIT)
static _ulbn_fft_inited = 0;
ULBN_PRIVATE void _ulbn_init_fft(void) {
  if(_ulbn_fft_inited == 0) {
    fprintf(
      stderr,
      "ulbn (fft): it looks like you're using a not modern platform,"
      "so `ulbnfft_init` is called automatically which is not thread-safe;"
      "it's recommand to replace this with a constant table generated by ulbnfft_init()\n"
    );
    ulbnfft_init();
    _ulbn_fft_inited = 1;
  }
}
    #endif /* !defined(_ULBN_FFT_AUTOINIT) */
  #endif   /* !(ULBN_LIMB_MAX == 0xFFFFFFFFu && _ULBN_IS_64BIT(ULBN_LIMB_MAX)) */


ul_static_assert(ULBNFFT_PROOT_2EXP < ULBNFFT_MOD_LOG2_MIN, "ULBNFFT_PROOT_2EXP < ULBNFFT_MOD_LOG2_MIN");
ul_static_assert(ULBNFFT_MOD_LOG2_MIN < ULBNFFT_MOD_LOG2_MAX, "ULBNFFT_MOD_LOG2_MIN < ULBNFFT_MOD_LOG2_MAX");

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
ULBN_PRIVATE ulbn_limb_t ulbnfft_mulmod2_init(ulbn_limb_t b, ulbn_limb_t m) {
  ulbn_limb_t q, r;
  _ulbn_udiv_(q, r, b, 0, m);
  (void)r;
  return q;
}

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
        carry[j - nlimb_to_put] = (u[j] >> shift) | (u[j + 1] << (ULBN_LIMB_BITS - shift));
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
  ulbn_assert(qp != rp);

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

/****************
 * <ulbn> Round *
 ****************/

/* return ap[0:an]*2 <=> mp[0:mn] */
ULBN_INTERNAL int ulbn_check_round(const ulbn_limb_t* ap, ulbn_usize_t an, const ulbn_limb_t* mp, ulbn_usize_t mn) {
  return -ulbn_cmpshl(mp, mn, ap, an, 1);
}

/* adjust half `round_mode` to normal */
ULBN_INTERNAL enum ULBN_ROUND_ENUM ulbn_adjust_half_round(enum ULBN_ROUND_ENUM round_mode, int is_even) {
  if(round_mode == ULBN_ROUND_HALF_ODD)
    return !is_even ? ULBN_ROUND_DOWN : ULBN_ROUND_UP;
  else if(round_mode == ULBN_ROUND_HALF_EVEN)
    return is_even ? ULBN_ROUND_DOWN : ULBN_ROUND_UP;
  else if(round_mode == ULBN_ROUND_HALF_DOWN)
    return ULBN_ROUND_DOWN;
  else /* if(round_mode == ULBN_ROUND_HALF_UP) */ {
    ulbn_assert(round_mode == ULBN_ROUND_HALF_UP);
    return ULBN_ROUND_UP;
  }
}
ULBN_INTERNAL int ulbn_round_direction(enum ULBN_ROUND_ENUM round_mode, int positive) {
  ulbn_assert(positive == 0 || positive == 1);
  if(round_mode == ULBN_ROUND_DOWN)
    return 0;
  else if(round_mode == ULBN_ROUND_UP)
    return positive ? 1 : -1;
  else if(round_mode == ULBN_ROUND_CEILING)
    return positive;
  else /* if(round_mode == ULBN_ROUND_FLOOR) */ {
    ulbn_assert(round_mode == ULBN_ROUND_FLOOR);
    return positive - 1;
  }
}

/**************************
 * <ulbn> Base conversion *
 **************************/

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

typedef struct ulbn_baseconv_t {
  const char* char_table;
  unsigned base_pow; /* the maximum power to make `b` <= ULBN_LIMB_MAX */
  int shift;         /* = _ulbn_ctz_(b) */
  ulbn_limb_t b;     /* = base**base_pow */
  ulbn_limb_t bi;    /* _ulbn_divinv1(b<<shift) */
  ulbn_limb_t base;
} ulbn_baseconv_t;
ULBN_INTERNAL void ulbn_prepare_baseconv(ulbn_baseconv_t* conv, ulbn_limb_t base) {
#if ULBN_LIMB_MAX == 0xFFu
  static const ulbn_limb_t table_b[] = { 0x80, 0xF3, 0x40, 0x7D, 0xD8, 0x31, 0x40, 0x51, 0x64, 0x79, 0x90, 0xA9,
                                         0xC4, 0xE1, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
                                         0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20, 0x21, 0x22, 0x23, 0x24 };
  static const unsigned char table_power[] = { 7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1,
                                               1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 };
  static const signed char table_shift[] = { 0, 0, 1, 1, 0, 2, 1, 1, 1, 1, 0, 0, 0, 0, 3, 3, 3, 3,
                                             3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2 };
  static const ulbn_limb_t table_bi[] = { 0xFF, 0xD,  0xFF, 0x6,  0x2F, 0x4E, 0xFF, 0x94, 0x47, 0xE,  0xC7, 0x83,
                                          0x4E, 0x23, 0xFF, 0xE1, 0xC7, 0xAF, 0x99, 0x86, 0x74, 0x64, 0x55, 0x47,
                                          0x3B, 0x2F, 0x24, 0x1A, 0x11, 0x8,  0xFF, 0xF0, 0xE1, 0xD4, 0xC7 };
  #define _ULBN_BASECONV_TABLE_DEFINED
#elif ULBN_LIMB_MAX == 0xFFFFu
  static const ulbn_limb_t table_b[] = { 0x8000, 0xE6A9, 0x4000, 0x3D09, 0xB640, 0x41A7, 0x8000, 0xE6A9, 0x2710,
                                         0x3931, 0x5100, 0x6F91, 0x9610, 0xC5C1, 0x1000, 0x1331, 0x16C8, 0x1ACB,
                                         0x1F40, 0x242D, 0x2998, 0x2F87, 0x3600, 0x3D09, 0x44A8, 0x4CE3, 0x55C0,
                                         0x5F45, 0x6978, 0x745F, 0x8000, 0x8C61, 0x9988, 0xA77B, 0xB640 };
  static const unsigned char table_power[] = { 15, 10, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3,
                                               3,  3,  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3 };
  static const signed char table_shift[] = { 0, 0, 1, 2, 0, 1, 0, 0, 2, 2, 1, 1, 0, 0, 3, 3, 3, 3,
                                             3, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0 };
  static const ulbn_limb_t table_bi[] = { 0xFFFF, 0x1C1F, 0xFFFF, 0xC6F,  0x6798, 0xF31D, 0xFFFF, 0x1C1F, 0xA36E,
                                          0x1E7A, 0x948B, 0x25B5, 0xB4B9, 0x4B66, 0xFFFF, 0xAADB, 0x6798, 0x31C0,
                                          0x624,  0xC4E6, 0x89E7, 0x58BA, 0x2F68, 0xC6F,  0xDD46, 0xAA2F, 0x7E22,
                                          0x57F3, 0x36B0, 0x1994, 0xFFFF, 0xD2D9, 0xAADB, 0x874E, 0x6798 };
  #define _ULBN_BASECONV_TABLE_DEFINED
#elif ULBN_LIMB_MAX == 0xFFFFFFFFu
  static const ulbn_limb_t table_b[] = { 0x80000000, 0xCFD41B91, 0x40000000, 0x48C27395, 0x81BF1000, 0x75DB9C97,
                                         0x40000000, 0xCFD41B91, 0x3B9ACA00, 0x8C8B6D2B, 0x19A10000, 0x309F1021,
                                         0x57F6C100, 0x98C29B81, 0x10000000, 0x18754571, 0x247DBC80, 0x3547667B,
                                         0x4C4B4000, 0x6B5A6E1D, 0x94ACE180, 0xCAF18367, 0xB640000,  0xE8D4A51,
                                         0x1269AE40, 0x17179149, 0x1CB91000, 0x23744899, 0x2B73A840, 0x34E63B41,
                                         0x40000000, 0x4CFA3CC1, 0x5C13D840, 0x6D91B519, 0x81BF1000 };
  static const unsigned char table_power[] = { 31, 20, 15, 13, 12, 11, 10, 10, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7,
                                               7,  7,  7,  7,  6,  6,  6,  6,  6, 6, 6, 6, 6, 6, 6, 6, 6 };
  static const signed char table_shift[] = { 0, 0, 1, 1, 0, 1, 1, 0, 2, 0, 3, 2, 1, 0, 3, 3, 2, 2,
                                             1, 1, 0, 0, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 0 };
  static const ulbn_limb_t table_bi[] = { 0xFFFFFFFF, 0x3B563C24, 0xFFFFFFFF, 0xC25C2684, 0xF91BD1B6, 0x1607A2CB,
                                          0xFFFFFFFF, 0x3B563C24, 0x12E0BE82, 0xD24CDE04, 0x3FA39AB5, 0x50F8AC5F,
                                          0x74843B1E, 0xAD0326C2, 0xFFFFFFFF, 0x4EF0B6BD, 0xC0FC48A1, 0x33838942,
                                          0xAD7F29AB, 0x313C3D15, 0xB8CCA9E0, 0x42ED6DE9, 0x67980E0B, 0x19799812,
                                          0xBCE85396, 0x62C103A9, 0x1D353D43, 0xCE1DECEA, 0x790FC511, 0x35B865A0,
                                          0xFFFFFFFF, 0xA9AED1B3, 0x63DFC229, 0x2B0FEE30, 0xF91BD1B6 };
  #define _ULBN_BASECONV_TABLE_DEFINED
#elif _ULBN_IS_64BIT(ULBN_LIMB_MAX)
  static const ulbn_limb_t table_b[] = { 0x8000000000000000, 0xA8B8B452291FE821, 0x4000000000000000, 0x6765C793FA10079D,
                                         0x41C21CB8E1000000, 0x3642798750226111, 0x8000000000000000, 0xA8B8B452291FE821,
                                         0x8AC7230489E80000, 0x4D28CB56C33FA539, 0x1ECA170C00000000, 0x780C7372621BD74D,
                                         0x1E39A5057D810000, 0x5B27AC993DF97701, 0x1000000000000000, 0x27B95E997E21D9F1,
                                         0x5DA0E1E53C5C8000, 0xD2AE3299C1C4AEDB, 0x16BCC41E90000000, 0x2D04B7FDD9C0EF49,
                                         0x5658597BCAA24000, 0xA0E2073737609371, 0xC29E98000000000,  0x14ADF4B7320334B9,
                                         0x226ED36478BFA000, 0x383D9170B85FF80B, 0x5A3C23E39C000000, 0x8E65137388122BCD,
                                         0xDD41BB36D259E000, 0xAEE5720EE830681,  0x1000000000000000, 0x172588AD4F5F0981,
                                         0x211E44F7D02C1000, 0x2EE56725F06E5C71, 0x41C21CB8E1000000 };
  static const unsigned char table_power[] = { 63, 40, 31, 27, 24, 22, 21, 20, 19, 18, 17, 17, 16, 16, 15, 15, 15, 15,
                                               14, 14, 14, 14, 13, 13, 13, 13, 13, 13, 13, 12, 12, 12, 12, 12, 12 };
  static const signed char table_shift[] = { 0, 0, 1, 1, 1, 2, 0, 0, 0, 1, 3, 1, 3, 1, 3, 2, 1, 0,
                                             3, 2, 1, 0, 4, 3, 2, 2, 1, 0, 0, 4, 3, 3, 2, 2, 1 };
  static const ulbn_limb_t table_bi[] = {
    0xFFFFFFFFFFFFFFFF, 0x846D550E37B5063D, 0xFFFFFFFFFFFFFFFF, 0x3CE9A36F23C0FC90, 0xF24F62335024A295,
    0x2DF495CCAA57147B, 0xFFFFFFFFFFFFFFFF, 0x846D550E37B5063D, 0xD83C94FB6D2AC34A, 0xA8ADF7AE45E7577B,
    0xA10C2BEC5DA8F8F,  0x10F4BECAFE412EC3, 0xF08480F672B4E86,  0x6779C7F90DC42F48, 0xFFFFFFFFFFFFFFFF,
    0x9C71E11BAB279323, 0x5DFAA697EC6F6A1C, 0x3711783F6BE7E9EC, 0x6849B86A12B9B01E, 0x6BF097BA5CA5E239,
    0x7B8015C8D7AF8F08, 0x975A24B3A3151B38, 0x50BD367972689DB1, 0x8C240C4AECB13BB5, 0xDBD2E56854E118C9,
    0x2351FFCAA9C7C4AE, 0x6B24188CA33B0636, 0xCC3DCEAF2B8BA99D, 0x2832E835C6C7D6B6, 0x76B6AA272E1873C5,
    0xFFFFFFFFFFFFFFFF, 0x61EAF5D402C7BF4F, 0xEEB658123FFB27EC, 0x5D5E3762E6FDF509, 0xF24F62335024A295
  };
  #define _ULBN_BASECONV_TABLE_DEFINED
#endif

#ifdef _ULBN_BASECONV_TABLE_DEFINED
  ulbn_assert(base >= 2 && base <= 36);
  conv->b = table_b[base - 2];
  conv->bi = table_bi[base - 2];
  conv->shift = ulbn_cast_int(table_shift[base - 2]);
  conv->base_pow = table_power[base - 2];
  conv->base = base;
#else
  ulbn_limb_t b_guard;
  b_guard = ulbn_cast_limb(ULBN_LIMB_MAX / base);
  conv->base_pow = 1;
  conv->base = base;
  for(conv->b = base; conv->b <= b_guard; conv->b *= base)
    ++conv->base_pow;
  conv->bi = ulbn_divinv1(conv->b);
#endif
}
ULBN_INTERNAL int ulbn_conv2print_generic(
  const ulbn_alloc_t* alloc, size_t desire_len, /* */
  ulbn_printer_t* printer, void* opaque,        /* */
  const ulbn_limb_t* ap, const ulbn_usize_t an, /* */
  const ulbn_baseconv_t* conv                   /* */
) {
  ulbn_limb_t* cp;
  size_t ccap = 0, ci = 0;

  ulbn_limb_t* tp;
  ulbn_usize_t tn = an;

  int err = ULBN_ERR_NOMEM;
  char buf[ULBN_LIMB_BITS];
  char *pbuf, *const buf_end = buf + ULBN_LIMB_BITS;
  ulbn_limb_t c;

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

    ulbn_divmod_inv1(tp, cp + (ci++), tp, tn, ulbn_cast_limb(conv->b << conv->shift), conv->bi, conv->shift);
    if(ul_likely(tp[tn - 1] == 0))
      --tn;
  } while(tn > 0);

  err = ULBN_ERR_EXTERNAL;
  c = cp[--ci];
  for(pbuf = buf_end; c; c /= conv->base)
    *--pbuf = conv->char_table[c % conv->base];
  if(desire_len / conv->base_pow >= ci) {
    desire_len -= conv->base_pow * ci;
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
    for(pbuf = buf + conv->base_pow; c; c /= conv->base)
      *--pbuf = conv->char_table[c % conv->base];
    memset(buf, conv->char_table[0], ul_static_cast(size_t, pbuf - buf));
    if(ul_unlikely(printer(opaque, buf, conv->base_pow)))
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
  const int shift = ulbn_cast_int(ULBN_LIMB_BITS - ulbn_cast_uint(_ulbn_clz_(ulbn_cast_limb(ULBN_LIMB_BITS))));
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
    ulbn_baseconv_t conv;
    if(bi->len < 0)
      fputc('-', fp);
    ulbn_prepare_baseconv(&conv, 10);
    conv.char_table = _ULBN_UPPER_TABLE;
    ulbn_conv2print_generic(
      ulbn_default_alloc(), 0, _ulbn_fileprinter, fp, _ulbi_limbs(bi), _ulbi_abs_size(bi->len), &conv
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
      limb = (limb << CHAR_BIT) | *q++;
    *dp++ = limb;
  }
  limb = 0;
  q = p - len;
  while(len--)
    limb = (limb << CHAR_BIT) | *q++;
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
    if(ro)
      err = ulbi_set_copy(alloc, ro, ao);
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

ul_static_assert('0' == 48, "not ASCII");
ul_static_assert('A' == 65, "not ASCII");
ul_static_assert('Z' == 90, "not ASCII");
ul_static_assert('a' == 97, "not ASCII");
ul_static_assert('z' == 122, "not ASCII");
ul_static_assert('_' == 95, "not ASCII");
ul_static_assert(ULBN_LIMB_MAX >= 36, "ulbn_limb_t is too small to hold base");
static ul_constexpr const unsigned char _ULBI_SETSTR_TABLE[] = {
  0,   1,  2,  3,  4,  5,  6,  7,  8,  9,  255, 255, 255, 255, 255, 255, /* \x30 - \x3F */
  255, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,  20,  21,  22,  23,  24,  /* \x40 - \x4F */
  25,  26, 27, 28, 29, 30, 31, 32, 33, 34, 35,  255, 255, 255, 255, 255, /* \x50 - \x5F */
  255, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,  20,  21,  22,  23,  24,  /* \x60 - \x6F */
  25,  26, 27, 28, 29, 30, 31, 32, 33, 34, 35,  255, 255, 255, 255, 255, /* \x70 - \x7F */
};
ULBN_PRIVATE int _ulbi_setstr_parse_short(
  const ulbn_alloc_t* alloc, ulbi_t* dst, const unsigned char* p, size_t len, ulbn_limb_t base
) {
  ulbn_limb_t intpart_l = 0, intpart_B = 1;
  const ulbn_limb_t B_guard = ulbn_cast_limb(ULBN_LIMB_MAX / base);
  unsigned c;
  int err;
  while(len-- != 0) {
    ulbn_assert(*p >= 0x30 && *p <= 0x7F);
    c = _ULBI_SETSTR_TABLE[*p++ - 0x30];
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
    while(len > 0 && _ULBI_SETSTR_TABLE[p[len - 1] - 0x30u] >= base) /* skip trailling seperate characters */
      --len;
    for(slen = 0; slen < len; ++slen)
      if(_ULBI_SETSTR_TABLE[p[slen] - 0x30u] < base)
        ++pow;
      else
        last_sep = slen;

    /* split the string into two part */
    pow_copy = pow - (pow >> 1);
    l_has_sep = 0;
    for(slen = 0;; ++slen) {
      ulbn_assert(slen < len);
      if(_ULBI_SETSTR_TABLE[p[slen] - 0x30u] < base) {
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
  const int ch_dot = (flag & ULBN_SET_STRING_ACCEPT_DECIMAL_PART) ? '.' : 0x100;
  const int ch_sep = (flag & ULBN_SET_STRING_ACCEPT_SEPARATOR) ? '_' : 0x100;
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
      if(len == 1) /* "0x" or "0X" */
        goto done;
      if(!((str[1] >= 'A' && str[1] <= 'Z') || (str[1] >= 'a' && str[1] <= 'z') || (str[1] >= '0' && str[1] <= '9')
           || str[1] == ch_dot)) /* the first character after 'x' or 'X' must be legal */
        goto done;
      ++str; /* eat "0x" or "0X" */
      --len;
    } else if(*str == 'o' || *str == 'O') {
      base = 8;
      if(len == 1) /* "0o" or "0O" */
        goto done;
      if(!((str[1] >= '0' && str[1] <= '7') || str[1] == ch_dot
         )) /* the first character after 'o' or 'O' must be legal */
        goto done;
      ++str; /* eat "0o" or "0O" */
      --len;
    } else if(*str == 'b' || *str == 'B') {
      base = 2;
      if(len == 1) /* "0b" or "0B" */
        goto done;
      if(!((str[1] == '0' || str[1] == '1') || str[1] == ch_dot
         )) /* the first character after 'b' or 'B' must be legal */
        goto done;
      ++str; /* eat "0b" or "0B" */
      --len;
    } else if(*str == '0') {
      goto done; /* "00" */
    } else if(*str >= '1' && *str <= '7' && (flag & ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX)) {
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
  parse_ptr = str;
  for(; len != 0; --len) {
    if(*str < 0x30 || ul_static_cast(unsigned char, *str) > 0x7F)
      break;
    if(*str == ch_sep)
      ++parse_sep;
    else {
      if(_ULBI_SETSTR_TABLE[*str - 0x30] >= ulbn_cast_uint(base))
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

  /* if !(flag & ULBN_SET_STRING_ACCEPT_DECIMAL_PART), and `ch_dot` = 0x100, then `*str` never equals to `ch_dot` */
  if(*str == ch_dot) {
    ++str;
    --len;
    parse_ptr = str;
    parse_pow = 0;
    parse_sep = 0;

    for(; len != 0; --len) {
      if(*str < 0x30 || ul_static_cast(unsigned char, *str) > 0x7F)
        break;
      if(*str == ch_sep)
        ++parse_sep;
      else if(_ULBI_SETSTR_TABLE[*str - 0x30] >= ulbn_cast_uint(base))
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
      if(!(*p >= '0' && *p <= '9'))
        break;
      if(ul_unlikely(expo > expo_limit)) {
        err = ULBN_ERR_EXCEED_RANGE;
        goto done;
      }
      expo *= 10;
      expo += ul_static_cast(unsigned char, *p - '0');
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
    ulbn_baseconv_t conv;
    ulbn_prepare_baseconv(&conv, ulbn_cast_limb(base));
    conv.char_table = char_table;
    err = ulbn_conv2print_generic(alloc, desire_len, printer, opaque, _ulbi_limbs(ao), ulbn_cast_usize(ao->len), &conv);
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
  ulbn_baseconv_t conv;
  ulbn_assert(desire_len == 0);
  ulbn_assert(ao->len > 0);
  ulbn_prepare_baseconv(&conv, ulbn_cast_limb(base));
  conv.char_table = char_table;
  return ulbn_conv2print_generic(alloc, desire_len, printer, opaque, _ulbi_limbs(ao), ulbn_cast_usize(ao->len), &conv);
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
    err = _ulbi_print_ex(alloc, printer, opaque, &ro, base, 0, _ULBN_UPPER_TABLE);
  else
    err = _ulbi_print_ex(alloc, printer, opaque, &ro, -base, 0, _ULBN_LOWER_TABLE);
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
