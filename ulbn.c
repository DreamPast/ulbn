#ifndef ULBN_H
  #include "ulbn.h"
#endif

#include <string.h>
#include <stdlib.h>

#ifndef ulbn_assert
  #include <assert.h>
  #define ulbn_assert(expr) assert(expr)
#endif /* ulbn_assert */

#ifndef ulbn_condexpr
  #define ulbn_condexpr(cond, expr) (ulbn_assert(cond), (expr))
#endif /* ulbn_condexpr */

#ifndef ul_assume
  #if defined(_MSC_VER)
    #define ul_assume(cond) __assume(cond)
  #endif
  #if !defined(ul_assume) && ul_has_builtin(__builtin_assume)
    #define ul_assume(cond) __builtin_assume(cond)
  #endif
  #if !defined(ul_assume) && ul_has_builtin(__builtin_unreachable) && ul_has_builtin(__builtin_expect)
    #define ul_assume(cond) (__builtin_expect(!(cond), 0) ? __builtin_unreachable() : (void)0)
  #endif
  #ifndef ul_assume
    #define ul_assume(cond) ((void)(cond))
  #endif
#endif /* ul_assume */

/* check if `x` is 64-bit integer */
#if defined(ULONG_MAX) && (ULONG_MAX >> 63) == 1
  #define _ULBN_IS_64BIT(x) ((x) == 0xFFFFFFFFFFFFFFFFul)
#elif defined(ULLONG_MAX) && (ULLONG_MAX >> 63) == 1
  #define _ULBN_IS_64BIT(x) ((x) == 0xFFFFFFFFFFFFFFFFull)
#else
  #define _ULBN_IS_64BIT(x) (0)
#endif /* _ULBN_IS_64BIT */

#define ulbn_safe_forward_overlap(d, dn, s, sn) ((d) <= (s) || (d) >= (s) + (sn))
#define ulbn_safe_backward_overlap(d, dn, s, sn) ((d) + (dn) <= (s) || ((d) >= (s) && (d) + (dn) >= (s) + (sn)))
#define ulbn_safe_overlap(d, dn, s, sn) ((d) + (dn) <= (s) || (s) + (sn) <= (d))

#define ulbn_assert_forward_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_forward_overlap(d, dn, s, sn))
#define ulbn_assert_backward_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_backward_overlap(d, dn, s, sn))
#define ulbn_assert_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_overlap(d, dn, s, sn))
#define ulbn_assert_same_or_not_overlap(d, dn, s, sn) \
  ulbn_assert((d) == ul_nullptr || (s) == ul_nullptr || (s) == (d) || ulbn_safe_overlap(d, dn, s, sn))

#define _ulbn_max_(a, b) ((a) > (b) ? (a) : (b))
#define _ulbn_min_(a, b) ((a) < (b) ? (a) : (b))
#define _ulbn_abs_(a) ((a) >= 0 ? (a) : -(a))
#define _ulbn_swap_(T, a, b) \
  do {                       \
    T __swap_tmp = (a);      \
    (a) = (b);               \
    (b) = __swap_tmp;        \
  } while(0)

#define _ulbn_same_sign(a, b) (((a) ^ (b)) >= 0)

#if(CHAR_BIT & 1) != 0
  #error "ulbn: CHAR_BIT must be even"
#endif

#define _ULBN_LIMB_BITS (sizeof(ulbn_limb_t) * CHAR_BIT)
#define _ULBN_LIMB_HALF_BITS (_ULBN_LIMB_BITS >> 1)
#define ULBN_LIMB_SHL(val, shift) ul_static_cast(ulbn_limb_t, ul_static_cast(ulbn_limb_t, val) << (shift))
#define _ULBN_LIMB_SIGNBIT (ULBN_LIMB_SHL(1, _ULBN_LIMB_BITS - 1))
#define _ULBN_LOWMASK ul_static_cast(ulbn_limb_t, ULBN_LIMB_SHL(1, _ULBN_LIMB_HALF_BITS) - 1u)
#define ULBN_LOWPART(x) ul_static_cast(ulbn_limb_t, (x) & ULBN_LOWMASK)
#define ULBN_HIGHPART(x) ul_static_cast(ulbn_limb_t, (x) >> ULBN_LIMB_HALF_BITS)

static ul_constexpr const size_t ULBN_LIMB_BITS = _ULBN_LIMB_BITS;
static ul_constexpr const size_t ULBN_LIMB_HALF_BITS = _ULBN_LIMB_HALF_BITS;
static ul_constexpr const ulbn_limb_t ULBN_LIMB_SIGNBIT = _ULBN_LIMB_SIGNBIT;
static ul_constexpr const ulbn_limb_t ULBN_LOWMASK = _ULBN_LOWMASK;

#define _ulbn_abs_size(n) ulbn_cast_usize((n) < 0 ? -(n) : (n))
#define _ulbn_to_ssize(pos, n) ((pos) ? ulbn_cast_ssize(n) : -ulbn_cast_ssize(n))

#define _ulbn_from_pos_slimb(v) ul_static_cast(ulbn_limb_t, v)
#define _ulbn_from_neg_slimb(v) ul_static_cast(ulbn_limb_t, ul_static_cast(ulbn_limb_t, -(v + 1)) + 1u)
#define _ulbn_from_pos_slong(v) ul_static_cast(ulbn_ulong_t, v)
#define _ulbn_from_neg_slong(v) ul_static_cast(ulbn_ulong_t, ul_static_cast(ulbn_ulong_t, -(v + 1)) + 1u)
#define _ulbn_from_pos_ssize(v) ul_static_cast(ulbn_usize_t, v)
#define _ulbn_from_neg_ssize(v) ul_static_cast(ulbn_usize_t, ul_static_cast(ulbn_usize_t, -(v + 1)) + 1u)

ul_static_assert(sizeof(size_t) >= sizeof(ulbn_usize_t), "usbn_usize_t cannot be larger than size_t");

/* The limitation of ulbn_usize_t, mainly to avoid overflow caused by the multiplication of ulbn_usize_t */
#define _ULBN_USIZE_LIMIT \
  _ulbn_min_(ul_static_cast(size_t, ~ul_static_cast(size_t, 0)) / sizeof(ulbn_limb_t), ULBN_USIZE_MAX)
#define _ULBN_SSIZE_LIMIT _ulbn_min_(_ULBN_USIZE_LIMIT / 2, ulbn_cast_usize(ULBN_SSIZE_MAX))
static ul_constexpr const size_t ULBN_USIZE_LIMIT = _ULBN_USIZE_LIMIT;
static ul_constexpr const ulbn_usize_t ULBN_SSIZE_LIMIT = _ULBN_SSIZE_LIMIT;

#ifndef ULBN_CHECK_USIZE_OVERFLOW
  #ifndef UL_HAS_STDINT_H
    #if defined(__GLIBC__) && (__GLIBC__ > 2 || (__GLIBC__ == 2 && __GLIBC_MINOR__ >= 1))
      #if defined(__GNUC__) || ((__GLIBC__ > 2) || ((__GLIBC__ == 2) && (__GLIBC_MINOR__ >= 5)))
        #define UL_HAS_STDINT_H
      #endif
    #endif
    #if defined(__MINGW32__) \
      && (__MINGW32_MAJOR_VERSION > 2 || (__MINGW32_MAJOR_VERSION == 2 && __MINGW32_MINOR_VERSION >= 0))
      #define UL_HAS_STDINT_H
    #endif
    #if defined(unix) || defined(__unix) || defined(_XOPEN_SOURCE) || defined(_POSIX_SOURCE)
      #include <unistd.h>
      #if defined(_POSIX_VERSION) && (_POSIX_VERSION >= 200100L)
        #define UL_HAS_STDINT_H
      #endif
    #endif
    #if(defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L) || (defined(__cplusplus) && __cplusplus >= 201103L)
      #define UL_HAS_STDINT_H
    #endif
    #if(defined(_MSC_VER) && _MSC_VER >= 1600) || (defined(__CYGWIN__) && defined(_STDINT_H))
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

  #if defined(SIZE_MAX) && ULBN_USIZE_MAX <= SIZE_MAX
    #define ULBN_CHECK_USIZE_OVERFLOW 0
  #else
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

#define ULBN_DO_IF_SSIZE_COND(cond, expr) \
  if(ul_unlikely(cond))                   \
  expr((void)0)
#define ULBN_RETURN_IF_SSIZE_COND(cond, ret) \
  if(ul_unlikely(cond))                      \
  return (ret)
#define ULBN_DO_IF_SSIZE_OVERFLOW(n, expr) ULBN_DO_IF_SSIZE_COND((n) > ULBN_SSIZE_LIMIT, expr)
#define ULBN_RETURN_IF_SSIZE_OVERFLOW(n, ret) ULBN_RETURN_IF_SSIZE_COND((n) > ULBN_SSIZE_LIMIT, ret)

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
ULBN_PUBLIC ulbn_alloc_t* ulbn_default_alloc(void) {
  static ulbn_alloc_t alloc = {&_ulbn_default_alloc, ul_nullptr};
  return &alloc;
}


ULBN_PRIVATE int _ulbn_clz_(ulbn_limb_t x) {
#if ul_has_builtin(__builtin_clz) && ULBN_LIMB_MAX <= UINT_MAX
  return ulbn_condexpr(x != 0, __builtin_clz(x) - ul_static_cast(int, sizeof(int) * CHAR_BIT - ULBN_LIMB_BITS));
#elif ul_has_builtin(__builtin_clz) && ULBN_LIMB_MAX == UINT_MAX
  return ulbn_condexpr(x != 0, __builtin_clz(x));
#elif ul_has_builtin(__builtin_clzl) && ULBN_LIMB_MAX == ULONG_MAX
  return ulbn_condexpr(x != 0, __builtin_clzl(x));
#elif ul_has_builtin(__builtin_clzll) && ULBN_LIMB_MAX == ULLONG_MAX
  return ulbn_condexpr(x != 0, __builtin_clzll(x));
#else
  int r = 0;

  #if ULBN_LIMB_MAX > 0xFFu
  static const ulbn_limb_t MASK8 = ULBN_LIMB_SHL(0xFF, ULBN_LIMB_BITS - 8);
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
    r += x & 1;
    x >>= 1;
  }
  return r;
#endif
}

ULBN_PRIVATE int _ulbn_clz_ulong(ulbn_ulong_t x) {
#if ul_has_builtin(__builtin_clz) && ULBN_ULONG_MAX <= UINT_MAX
  return ulbn_condexpr(
    x != 0, __builtin_clz(x) - ul_static_cast(int, sizeof(int) * CHAR_BIT - sizeof(ulbn_ulong_t) * CHAR_BIT)
  );
#elif ul_has_builtin(__builtin_clz) && ULBN_ULONG_MAX == UINT_MAX
  return ulbn_condexpr(x != 0, __builtin_clz(x));
#elif ul_has_builtin(__builtin_clzl) && ULBN_ULONG_MAX == ULONG_MAX
  return ulbn_condexpr(x != 0, __builtin_clzl(x));
#elif ul_has_builtin(__builtin_clzll) && ULBN_ULONG_MAX == ULLONG_MAX
  return ulbn_condexpr(x != 0, __builtin_clzll(x));
#else
  static const ulbn_ulong_t MASK =
    ul_static_cast(ulbn_ulong_t, ul_static_cast(ulbn_ulong_t, 1) << (sizeof(ulbn_ulong_t) * CHAR_BIT - 1));
  int r = 0;

  #if ULBN_ULONG_MAX > 0xFFu
  static const ulbn_ulong_t MASK8 =
    ul_static_cast(ulbn_ulong_t, ul_static_cast(ulbn_ulong_t, 0xFF) << (sizeof(ulbn_ulong_t) * CHAR_BIT - 8));
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

#define _ulbn_neg_(v) ul_static_cast(ulbn_limb_t, ul_static_cast(ulbn_limb_t, 0u) - (v))
#define _ulbn_add_(s1, s0, a1, a0, b1, b0) \
  do {                                     \
    const ulbn_limb_t __s = (a0) + (b0);   \
    (s1) = (a1) + (b1) + (__s < (a0));     \
    (s0) = __s;                            \
  } while(0)
#define _ulbn_sub_(d1, d0, a1, a0, b1, b0) \
  do {                                     \
    const ulbn_limb_t __d = (a0) - (b0);   \
    (d1) = (a1) - (b1) - ((a0) < (b0));    \
    (d0) = __d;                            \
  } while(0)

#ifdef ulbn_limb2_t
  #define _ulbn_umul_(p1, p0, u, v)                                \
    do {                                                           \
      ulbn_limb2_t __p = ul_static_cast(ulbn_limb2_t, (u)) * (v);  \
      (p1) = ul_static_cast(ulbn_limb_t, (__p) >> ULBN_LIMB_BITS); \
      (p0) = ul_static_cast(ulbn_limb_t, (__p));                   \
    } while(0)
  #define _ulbn_udiv_(q, r, n1, n0, d)                                                  \
    do {                                                                                \
      ulbn_limb2_t __n = (ul_static_cast(ulbn_limb2_t, (n1)) << ULBN_LIMB_BITS) | (n0); \
      (r) = ul_static_cast(ulbn_limb_t, __n % (d));                                     \
      (q) = ul_static_cast(ulbn_limb_t, __n / (d));                                     \
    } while(0)
#endif

#if !defined(_ulbn_umul_) && defined(_MSC_VER) && _ULBN_IS_64BIT(ULBN_LIMB_MAX)
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

#if !defined(_ulbn_udiv_) && defined(_MSC_VER) && _ULBN_IS_64BIT(ULBN_LIMB_MAX)
  #include <intrin.h>
  #if _MSC_VER >= 1929 && !defined(__clang__) && (defined(__x86_64__) || defined(_M_X64)) /* x86_64 */
    #pragma intrinsic(_udiv128)
    #define _ulbn_udiv_(q, r, n1, n0, d) ((q) = _udiv128((n1), (n0), (d), &(r)))
  #endif
#endif

#ifndef _ulbn_umul_
  #define _ulbn_umul_(p1, p0, u, v)                                                           \
    do {                                                                                      \
      const ulbn_limb_t __ul = ULBN_LOWPART(u);                                               \
      const ulbn_limb_t __uh = ULBN_HIGHPART(u);                                              \
      const ulbn_limb_t __vl = ULBN_LOWPART(v);                                               \
      const ulbn_limb_t __vh = ULBN_HIGHPART(v);                                              \
      ulbn_limb_t __x0 = ul_static_cast(ulbn_limb_t, __ul * __vl);                            \
      ulbn_limb_t __x1 = ul_static_cast(ulbn_limb_t, __ul * __vh);                            \
      ulbn_limb_t __x2 = ul_static_cast(ulbn_limb_t, __uh * __vl);                            \
      ulbn_limb_t __x3 = ul_static_cast(ulbn_limb_t, __uh * __vh);                            \
      __x1 += ULBN_HIGHPART(__x0);                                                            \
      __x1 += __x2;                                                                           \
      if(__x1 < __x2)                                                                         \
        __x3 += ULBN_LIMB_SHL(1, ULBN_LIMB_HALF_BITS);                                        \
      (p0) = ul_static_cast(ulbn_limb_t, (__x1 << ULBN_LIMB_HALF_BITS) | ULBN_LOWPART(__x0)); \
      (p1) = __x3 + ULBN_HIGHPART(__x1);                                                      \
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
  #define _ulbn_udiv_(q, r, n1, n0, d)                                                            \
    do {                                                                                          \
      if((n1) == 0) {                                                                             \
        (r) = (n0) % (d);                                                                         \
        (q) = (n0) / (d);                                                                         \
      } else {                                                                                    \
        const int __shift = _ulbn_clz_(d);                                                        \
        const ulbn_limb_t __U_n1 =                                                                \
          ((n1) << __shift) | ((n0) >> (ul_static_cast(int, ULBN_LIMB_BITS) - __shift - 1) >> 1); \
        const ulbn_limb_t __U_n0 = (n0) << __shift;                                               \
        const ulbn_limb_t __U_d = (d) << __shift;                                                 \
        ulbn_limb_t __U_r;                                                                        \
        _ulbn_udiv_norm_((q), __U_r, __U_n1, __U_n0, __U_d);                                      \
        (r) = __U_r >> __shift;                                                                   \
      }                                                                                           \
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
  n0 = _ulbn_neg_(1u);
  _ulbn_udiv_norm_(di, di, n1, n0, d1);
  return di;
}
#define ulbn_divinv1(d1) ulbn_condexpr((d1 & ULBN_LIMB_SIGNBIT) != 0 /* B/2 <= d1 < B */, _ulbn_divinv1(d1))
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
  n0 = _ulbn_neg_(1u);
  _ulbn_udiv_norm_(di, di, n1, n0, d1);

  /**
   * calc <B-1-d1, B-1-d0>//d1
   *
   * As 0 < -d0/d1 <= 2 - 2/B,
   * -2 <= <B-1-d1, B-1-d0>//d1 - <B-1-d1, B-1>//d1 <= 0
   */
  p = d1 * di + d0;
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
#define ulbn_divinv2(d1, d0) ulbn_condexpr((d1 & ULBN_LIMB_SIGNBIT) != 0 /* B/2 <= d1 < B */, _ulbn_divinv2(d1, d0))

#define _ulbn_udiv_2by1_(q, r, a1, a0, d, di)           \
  do {                                                  \
    ulbn_limb_t __q1, __q0, __r;                        \
    _ulbn_umul_(__q1, __q0, (a1), (di));                \
    _ulbn_add_(__q1, __q0, __q1, __q0, (a1) + 1, (a0)); \
    __r = (a0) - __q1 * (d);                            \
    if(__r > __q0) {                                    \
      --__q1;                                           \
      __r += (d);                                       \
    }                                                   \
    if(ul_unlikely(__r >= (d))) {                       \
      ++__q1;                                           \
      __r -= (d);                                       \
    }                                                   \
    (r) = __r;                                          \
    (q) = __q1;                                         \
  } while(0)
#define _ulbn_udiv_3by2_(q, r1, r0, a2, a1, a0, d1, d0, di) \
  do {                                                      \
    ulbn_limb_t __q1, __q0;                                 \
    ulbn_limb_t __r1, __r0;                                 \
    ulbn_limb_t __t1, __t0;                                 \
    _ulbn_umul_(__q1, __q0, (a2), (di));                    \
    _ulbn_add_(__q1, __q0, __q1, __q0, (a2), (a1));         \
    __r1 = (a1) - __q1 * (d1);                              \
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


ul_static_assert(_ULBN_LIMB_BITS <= ULBN_USIZE_MAX, "ulbn_usize_t must be able to hold at least ULBN_LIMB_BITS");
#define ULBN_BITS_OVERFLOW_USIZE (ULBN_USIZE_MAX / ULBN_LIMB_BITS)
ULBN_INTERNAL ulbn_usize_t ulbn_ctz(const ulbn_limb_t* p, ulbn_usize_t n, ulbn_usize_t* p_rh) {
  const ulbn_usize_t m = _ulbn_min_(n, ULBN_BITS_OVERFLOW_USIZE);
  ulbn_usize_t rl = 0, rh = 0;
  ulbn_usize_t i;

  for(i = 0; i < m; ++i) {
    if(p[i]) {
      rl += ul_static_cast(unsigned, _ulbn_ctz_(p[i]));
      goto done;
    }
    rl += ULBN_LIMB_BITS;
  }
  if(ul_unlikely(i < n))
    do {
      if(p[i]) {
        ulbn_usize_t r_temp = rl;
        rl += ul_static_cast(unsigned, _ulbn_ctz_(p[i]));
        rh += (rl < r_temp);
        goto done;
      }
      rl += ULBN_LIMB_BITS;
      rh += (rl < ULBN_LIMB_BITS);
    } while(++i < n);
done:
  if(ul_unlikely(p_rh))
    *p_rh = rh;
  return rl;
}
ULBN_INTERNAL ulbn_usize_t ulbn_cto(const ulbn_limb_t* p, ulbn_usize_t n, ulbn_usize_t* p_rh) {
  const ulbn_usize_t m = _ulbn_min_(n, ULBN_BITS_OVERFLOW_USIZE);
  ulbn_usize_t rl = 0, rh = 0;
  ulbn_usize_t i;

  for(i = 0; i < m; ++i) {
    if(p[i] != ULBN_LIMB_MAX) {
      rl += ul_static_cast(unsigned, _ulbn_ctz_(~p[i]));
      goto done;
    }
    rl += ULBN_LIMB_BITS;
  }
  if(ul_unlikely(i < n))
    do {
      if(p[i] != ULBN_LIMB_MAX) {
        ulbn_usize_t r_temp = rl;
        rl += ul_static_cast(unsigned, _ulbn_ctz_(~p[i]));
        rh += (rl < r_temp);
        goto done;
      }
      rl += ULBN_LIMB_BITS;
      rh += (rl < ULBN_LIMB_BITS);
    } while(++i < n);

done:
  if(ul_unlikely(p_rh))
    *p_rh = rh;
  return rl;
}
ULBN_INTERNAL ulbn_usize_t ulbn_popcount(const ulbn_limb_t* p, ulbn_usize_t n, ulbn_usize_t* p_rh) {
  const ulbn_usize_t m = _ulbn_min_(n, ULBN_BITS_OVERFLOW_USIZE);
  ulbn_usize_t rl = 0, rh = 0;
  ulbn_usize_t i;

  for(i = 0; i < m; ++i)
    rl += ul_static_cast(unsigned, _ulbn_popcount_(p[i]));
  if(ul_unlikely(i < n))
    do {
      ulbn_usize_t r_temp = rl;
      rl += ul_static_cast(unsigned, _ulbn_popcount_(p[i]));
      rh += (rl < r_temp);
    } while(++i < n);

  if(ul_unlikely(p_rh))
    *p_rh = rh;
  return rl;
}
ULBN_INTERNAL ulbn_usize_t ulbn_bit_width(const ulbn_limb_t* p, ulbn_usize_t n, ulbn_usize_t* p_rh) {
  static ul_constexpr const size_t USIZE_BITS = sizeof(ulbn_usize_t) * CHAR_BIT;
  static ul_constexpr const size_t USIZE_HALF_BITS = sizeof(ulbn_usize_t) * CHAR_BIT >> 1;
  ulbn_usize_t rl, rh;

  ulbn_assert(n > 0);
  if(ul_likely(n <= ULBN_BITS_OVERFLOW_USIZE)) {
    rl = n * ULBN_LIMB_BITS - ul_static_cast(unsigned, _ulbn_clz_(p[n - 1]));
    rh = 0;
  } else {
    ulbn_usize_t n_high = n >> USIZE_HALF_BITS;
    ulbn_usize_t n_low = n & ulbn_cast_usize((ulbn_cast_usize(1u) << USIZE_HALF_BITS) - 1u);
    const ulbn_usize_t v0 = n_low * ULBN_LIMB_BITS;
    const ulbn_usize_t v1 = n_high * ULBN_LIMB_BITS;
    rl = v0 + (v1 << (USIZE_BITS - USIZE_HALF_BITS));
    rh = (v1 >> USIZE_HALF_BITS) + (rl < v0);
  }

  if(p_rh)
    *p_rh = rh;
  return rl;
}


static const char _ULBN_UPPER_TABLE[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
static const char _ULBN_LOWER_TABLE[] = "0123456789abcdefghijklmnopqrstuvwxyz";
ULBN_INTERNAL const char* ulbn_string_table(int is_lower) {
  return is_lower ? _ULBN_LOWER_TABLE : _ULBN_UPPER_TABLE;
}

#if 1
ul_unused ULBN_INTERNAL void ulbn_dumplimb(FILE* fp, ulbn_limb_t l) {
  const char* TABLE = ulbn_string_table(0);
  size_t j = sizeof(l) * CHAR_BIT / 4;
  while(j--)
    putc(TABLE[(l >> (j << 2)) & 0xF], fp);
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

/* Normalize p[0:n], removing leading zeros, and return the remaining length.
  When p[0:n] = 0, the length is 0. */
ULBN_INTERNAL ulbn_usize_t ulbn_normalize(const ulbn_limb_t* p, ulbn_usize_t n) {
  while(n > 0 && p[n - 1] == 0)
    --n;
  return n;
}
/* Clear p[0:n] */
ULBN_INTERNAL void ulbn_fill0(ulbn_limb_t* p, ulbn_usize_t n) {
  memset(p, 0, ul_static_cast(size_t, n) * sizeof(ulbn_limb_t));
}
/* Fill p[0:n] with ~0 */
ULBN_INTERNAL void ulbn_fill1(ulbn_limb_t* p, ulbn_usize_t n) {
  memset(p, 0xFF, ul_static_cast(size_t, n) * sizeof(ulbn_limb_t));
}
/* Check if p[0:n] is 0 */
ULBN_INTERNAL int ulbn_is0(const ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
    if(p[i] != 0)
      return 0;
  return 1;
}

/* Copy src[0:n] to dst[0:n], ensuring src[] and dest[] do not overlap */
ULBN_INTERNAL void ulbn_copy(ulbn_limb_t* ul_restrict dst, const ulbn_limb_t* ul_restrict src, ulbn_usize_t n) {
  ulbn_assert_overlap(dst, n, src, n);
  memcpy(dst, src, ul_static_cast(size_t, n) * sizeof(*dst));
}
/* Copy src[0:n] to dst[0:n], ensuring dest is after src */
ULBN_INTERNAL void ulbn_fcopy(ulbn_limb_t* dst, const ulbn_limb_t* src, ulbn_usize_t n) {
  ulbn_assert_forward_overlap(dst, n, src, n);
  memcpy(dst, src, ul_static_cast(size_t, n) * sizeof(*dst));
}
/* Copy src[0:n] to dst[0:n], ensuring dest is before src */
ULBN_INTERNAL void ulbn_rcopy(ulbn_limb_t* dst, const ulbn_limb_t* src, ulbn_usize_t n) {
  ulbn_assert_backward_overlap(dst, n, src, n);
  memmove(dst, src, ul_static_cast(size_t, n) * sizeof(*dst));
}
#define ulbn_maycopy(dst, src, n) ((dst) != (src) ? ulbn_copy((dst), (src), (n)) : (void)0)

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
  return an != bn ? (an < bn ? -1 : 1) : ulbn_cmpn(ap, bp, an);
}

/* rp[0:an] = ap[0:an] + b, return carry (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_add1(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t b) {
  ulbn_usize_t i;

  ulbn_assert_forward_overlap(rp, an, ap, an);

  for(i = 0; i < an; ++i)
    b = ((rp[i] = ap[i] + b) < b);
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
    cy = ((r = a + cy) < cy);
    cy += ((r += b) < b);
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
    rp[i] = a - b;
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
    cy = ((b = bp[i] + cy) < cy);
    rp[i] = a - b;
    cy += (a < b);
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

  /* ulbn_assert(ulbn_cmp(ap, ulbn_normalize(ap, an), bp, ulbn_normalize(bp, bn)) >= 0); */
  ulbn_assert_forward_overlap(rp, an, ap, an);
  ulbn_assert_forward_overlap(rp, an, bp, bn);

  cy = ulbn_subn(rp, ap, bp, bn);
  return ulbn_sub1(rp + bn, ap + bn, an - bn, cy);
}


/* rp[0:n] = ap[0:n] << b, return overflow part (do not write to rp[n]), ensure 0 < b < {ULBN_LIMB_BITS} */
ULBN_INTERNAL ulbn_limb_t ulbn_shl(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t n, int b) {
  ulbn_usize_t i;
  ulbn_limb_t rh, rl, ret;
  const int br = ul_static_cast(int, ULBN_LIMB_BITS) - b;

  ulbn_assert(n > 0);
  ulbn_assert(0 < b && ul_static_cast(unsigned, b) < ULBN_LIMB_BITS);
  ulbn_assert_backward_overlap(rp, n, ap, n);

  rl = ap[n - 1];
  ret = rl >> br;
  rh = ul_static_cast(ulbn_limb_t, rl << b);
  for(i = n - 1; i > 0; --i) {
    rl = ap[i - 1];
    rp[i] = rh | (rl >> br);
    rh = ul_static_cast(ulbn_limb_t, rl << b);
  }
  rp[0] = rh;
  return ret;
}
/* rp[0:n] = ap[0:n] >> b, return overflow part (do not write to rp[-1]), ensure 0 < b < {ULBN_LIMB_BITS} */
ULBN_INTERNAL ulbn_limb_t ulbn_shr(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t n, int b) {
  ulbn_usize_t i;
  ulbn_limb_t rh, rl, ret;
  const int br = ul_static_cast(int, ULBN_LIMB_BITS) - b;

  ulbn_assert(n > 0);
  ulbn_assert(0 < b && ul_static_cast(unsigned, b) < ULBN_LIMB_BITS);
  ulbn_assert_forward_overlap(rp, n, ap, n);

  rh = ap[0];
  ret = ul_static_cast(ulbn_limb_t, rh << br);
  rl = rh >> b;
  for(i = 1; i < n; ++i) {
    rh = ap[i];
    rp[i - 1] = ul_static_cast(ulbn_limb_t, rl | (rh << br));
    rl = rh >> b;
  }
  rp[n - 1] = rl;
  return ret;
}


/* rp[0:an] = ap[0:an] * b, return carry (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_mul1(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t b) {
  ulbn_usize_t i;
  ulbn_limb_t ph, pl;
  ulbn_limb_t cy = 0;

  ulbn_assert_forward_overlap(rp, an + bn, ap, an);

  for(i = 0; i < an; ++i) {
    _ulbn_umul_(ph, pl, ap[i], b);
    cy = ph + ((pl += cy) < cy);
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
    cy = ph + ((pl += cy) < cy);
    r = rp[i];
    cy += (pl += r) < r;
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
    cy = ph + ((pl += cy) < cy);
    r = rp[i];
    rp[i] = r - pl;
    cy += r < pl;
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


#define _ULBN_TOOM_1_THRESHOLD 48
#define _ULBN_TOOM_2_THRESHOLD 128
ULBN_INTERNAL void ulbn_divmod_inv1(
  ulbn_limb_t* qp, ulbn_limb_t* rp,        /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,  /* */
  ulbn_limb_t d, ulbn_limb_t di, int shift /* */
);
ULBN_INTERNAL void ulbn_divmod_inv2(
  ulbn_limb_t* qp, ulbn_limb_t* rp,                         /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,                   /* */
  ulbn_limb_t d1, ulbn_limb_t d0, ulbn_limb_t di, int shift /* */
);
ULBN_INTERNAL void ulbn_divmod_inv(
  ulbn_limb_t* ul_restrict qp,                                       /* */
  ulbn_limb_t* ul_restrict rp, ulbn_usize_t rn, ulbn_limb_t a2,      /* */
  const ulbn_limb_t* ul_restrict dp, ulbn_usize_t dn, ulbn_limb_t di /* */
);
ULBN_PRIVATE void ulbn_mul(
  ulbn_alloc_t* alloc, ulbn_limb_t* ul_restrict rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,           /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn            /* */
);

ULBN_PRIVATE void _ulbn_divby3(ulbn_limb_t* qp, const ulbn_limb_t* ap, ulbn_usize_t an) {
#if ULBN_LIMB_MAX == 0xFFu
  static ul_constexpr const int D3_SHIFT = 6;
  static ul_constexpr const ulbn_limb_t D3_NORM = 0xC0u;
  static ul_constexpr const ulbn_limb_t D3_INV = 0x55u;
#elif ULBN_LIMB_MAX == 0xFFFFu
  static ul_constexpr const int D3_SHIFT = 14;
  static ul_constexpr const ulbn_limb_t D3_NORM = 0xC000u;
  static ul_constexpr const ulbn_limb_t D3_INV = 0x5555u;
#elif ULBN_LIMB_MAX == 0xFFFFFFFFu
  static ul_constexpr const int D3_SHIFT = 30;
  static ul_constexpr const ulbn_limb_t D3_NORM = 0xC0000000u;
  static ul_constexpr const ulbn_limb_t D3_INV = 0x55555555u;
#elif _ULBN_IS_64BIT(ULBN_LIMB_MAX)
  static ul_constexpr const int D3_SHIFT = 62;
  static ul_constexpr const ulbn_limb_t D3_NORM = 0xC000000000000000ull;
  static ul_constexpr const ulbn_limb_t D3_INV = 0x5555555555555555ull;
#else
  #ifdef __cplusplus
  static const int D3_SHIFT = _ulbn_clz_(3);
  static const ulbn_limb_t D3_NORM = ULBN_LIMB_SHL(3, D3_SHIFT);
  static const ulbn_limb_t D3_INV = _ulbn_divinv1(D3_NORM);
  #else
  const int D3_SHIFT = _ulbn_clz_(3);
  const ulbn_limb_t D3_NORM = ULBN_LIMB_SHL(3, D3_SHIFT);
  const ulbn_limb_t D3_INV = _ulbn_divinv1(D3_NORM);
  #endif
#endif
  static ulbn_limb_t R_POLYFILL;
  ulbn_divmod_inv1(qp, &R_POLYFILL, ap, an, D3_NORM, D3_INV, D3_SHIFT);
}

ULBN_PRIVATE int _ulbn_mul_toom_21(
  ulbn_alloc_t* alloc,                               /* */
  ulbn_limb_t* ul_restrict rp, const ulbn_usize_t m, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,            /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn             /* */
) {
  /**
   * Toom-2/1
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
  ulbn_alloc_t* alloc,                               /* */
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
  ulbn_sub(zp, zp, nz, rp, (m << 1) - (rp[(m << 1) - 1] == 0));
  /* `zp[0:nz]` -= z2 */
  ulbn_sub(zp, zp, nz, rp + (m << 1), an + bn - (rp[an + bn - 1] == 0) - (m << 1));
  nz = ulbn_normalize(zp, nz);
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

ULBN_PRIVATE int _ulbn_mul_toom_32(
  ulbn_alloc_t* alloc,                               /* */
  ulbn_limb_t* ul_restrict rp, const ulbn_usize_t m, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,            /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn             /* */
) {
  /*
    Toom-3/2

    v(  0) = (   0   0   0   1)
    v(  1) = (   1   1   1   1)
    v( -1) = (  -1   1  -1   1)
    v(inf) = (   1   0   0   0)
  */

  const ulbn_usize_t m2 = m << 1, am = an - m2, bm = bn - m, abm = am + bm;
  const ulbn_limb_t *const a0 = ap, *const a1 = ap + m, *const a2 = ap + m2;
  const ulbn_limb_t *const b0 = bp, *const b1 = bp + m;
  ulbn_limb_t* rinf = rp + m2 + m;

  ulbn_limb_t *ul_restrict v1, *ul_restrict vm1;
  ulbn_limb_t* ul_restrict t1;

  ulbn_usize_t n1, n2, nt;
  int sign;
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

  t1[m] = ulbn_add(t1, a0, m, a2, am);
  rp[m] = t1[m] + ulbn_add(rp, t1, m, a1, m);
  vm1[m] = ulbn_add(vm1, b0, m, b1, bm);
  ulbn_mul(alloc, v1, rp, m + 1, vm1, m + 1);

  n1 = ulbn_normalize(t1, m + 1);
  nt = ulbn_normalize(a1, m);
  if(ulbn_cmp(t1, n1, a1, nt) >= 0) {
    ulbn_sub(t1, t1, n1, a1, nt);
    n1 = ulbn_normalize(t1, n1);
    sign = 0;
  } else {
    ulbn_sub(t1, a1, nt, t1, n1);
    n1 = ulbn_normalize(t1, nt);
    sign = 1;
  }

  n2 = ulbn_normalize(b0, m);
  nt = ulbn_normalize(b1, bm);
  if(ulbn_cmp(b0, n2, b1, nt) >= 0) {
    ulbn_sub(rp, b0, n2, b1, nt);
    n2 = ulbn_normalize(rp, n2);
  } else {
    ulbn_sub(rp, b1, nt, b0, n2);
    n2 = ulbn_normalize(rp, nt);
    sign ^= 1;
  }

  if(n1 && n2) {
    ulbn_mul(alloc, vm1, t1, n1, rp, n2);
    ulbn_fill0(vm1 + n1 + n2, (m2 + 2) - (n1 + n2));
  } else
    ulbn_fill0(vm1, m2 + 2);

  ulbn_mul(alloc, rp, a0, m, b0, m);
  ulbn_mul(alloc, rinf, a2, am, b1, bm);

#if 0
  ulbn_dprint(stdout, "v0 = ", rp, m2);
  ulbn_dprint(stdout, "v1 = ", v1, m2 + 1);
  printf("vm1 = %c", sign ? '-' : '+');
  ulbn_dprint(stdout, ul_nullptr, vm1, m2 + 1);
  ulbn_dprint(stdout, "vinf = ", rinf, abm);
#endif

  /* t1 = v1 + vm1 = (0, 2, 0, 2) */
  /* v1 = v1 - vm1 = (2, 0, 2, 0) */
  if(sign == 0) {
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

#if 0
  ulbn_dprint(stdout, "v0 = ", rp, m2);
  ulbn_dprint(stdout, "v1 = ", v1, m2 + 1);
  ulbn_dprint(stdout, "t1 = ", vm1, m2 + 1);
  ulbn_dprint(stdout, "vinf = ", rinf, abm);
#endif

  ulbn_copy(rp + m2, t1, m);
  ulbn_assert(ulbn_normalize(t1, m2 + 1) <= m + abm);
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
  ulbn_alloc_t* alloc,                               /* */
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

  const ulbn_usize_t m2 = m << 1, am = an - m2, bm = bn - m2, abm = am + bm;
  const ulbn_limb_t *const a0 = ap, *const a1 = ap + m, *const a2 = ap + m2;
  const ulbn_limb_t *const b0 = bp, *const b1 = bp + m, *const b2 = bp + m2;
  ulbn_limb_t* rinf = rp + m2 + m2;

  ulbn_limb_t *ul_restrict v1, *ul_restrict vm1, *ul_restrict v2;
  ulbn_limb_t *ul_restrict t1, *ul_restrict t2;

  ulbn_usize_t n1, n2, nt;
  int sign;
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

  t1[m] = ulbn_add(t1, a1, m, a2, am);
  vm1[m] = t1[m] + ulbn_add(vm1, t1, m, a0, m);
  t2[m] = ulbn_add(t2, b1, m, b2, bm);
  v2[m] = t2[m] + ulbn_add(v2, t2, m, b0, m);
  ulbn_mul(alloc, v1, vm1, m + 1, v2, m + 1);

  t1[m] += ulbn_add(t1, t1, m, a2, am);
  t1[m] = (t1[m] << 1) | ulbn_shl(t1, t1, m, 1);
  t1[m] += ulbn_add(t1, t1, m, a0, m);
  t2[m] += ulbn_add(t2, t2, m, b2, bm);
  t2[m] = (t2[m] << 1) | ulbn_shl(t2, t2, m, 1);
  t2[m] += ulbn_add(t2, t2, m, b0, m);
  ulbn_mul(alloc, v2, t1, m + 1, t2, m + 1);

  t1[m] = ulbn_add(t1, a0, m, a2, am);
  n1 = ulbn_normalize(t1, m + 1);
  nt = ulbn_normalize(a1, m);
  if(ulbn_cmp(t1, n1, a1, nt) >= 0) {
    ulbn_sub(t1, t1, n1, a1, nt);
    n1 = ulbn_normalize(t1, n1);
    sign = 0;
  } else {
    ulbn_sub(t1, a1, nt, t1, n1);
    n1 = ulbn_normalize(t1, nt);
    sign = 1;
  }

  t2[m] = ulbn_add(t2, b0, m, b2, bm);
  n2 = ulbn_normalize(t2, m + 1);
  nt = ulbn_normalize(b1, m);
  if(ulbn_cmp(t2, n2, b1, nt) >= 0) {
    ulbn_sub(t2, t2, n2, b1, nt);
    n2 = ulbn_normalize(t2, n2);
  } else {
    ulbn_sub(t2, b1, nt, t2, n2);
    n2 = ulbn_normalize(t2, nt);
    sign ^= 1;
  }

  if(n1 && n2) {
    ulbn_mul(alloc, vm1, t1, n1, t2, n2);
    ulbn_fill0(vm1 + n1 + n2, (m2 + 2) - (n1 + n2));
  } else {
    ulbn_fill0(vm1, m2 + 2);
  }

#if 0
  ulbn_dprint(stdout, "v0 = ", rp, m2);
  ulbn_dprint(stdout, "v1 = ", v1, m2 + 1);
  ulbn_dprint(stdout, "vm1 = ", vm1, m2 + 1);
  ulbn_dprint(stdout, "v2 = ", v2, m2 + 1);
  ulbn_dprint(stdout, "vinf = ", rinf, abm);
#endif

  /* v2 = v2 - vm1 = (15, 9, 3, 3, 0) */
  /* vm1 = v1 - vm1 = (0, 2, 0, 2, 0) */
  if(sign == 0) {
    ulbn_sub(v2, v2, m2 + 1, vm1, m2 + 1);
    ulbn_sub(vm1, v1, m2 + 1, vm1, m2 + 1);
  } else {
    ulbn_add(v2, v2, m2 + 1, vm1, m2 + 1);
    ulbn_add(vm1, v1, m2 + 1, vm1, m2 + 1);
  }
  /* v2 = v2 / 3 = (5, 3, 1, 1, 0) */
  _ulbn_divby3(v2, v2, m2 + 1);
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

/* Note: If allocation fails, it falls back to using a version with less cache,
  eventually falling back to the school method (time complexity O(n^2)) */
ULBN_PRIVATE void ulbn_mul(
  ulbn_alloc_t* alloc, ulbn_limb_t* ul_restrict rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,           /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn            /* */
) {
  ulbn_usize_t m, m2;
#if ULBN_CONF_CHECK_ALLOCATION_FAILURE
  #define _ULBN_DO_IF_MUL_FAILED(x, expr) ULBN_DO_IF_ALLOC_COND((x) < 0, expr)
#else
  #define _ULBN_DO_IF_MUL_FAILED(x, expr) (x)
#endif

  ulbn_assert(an + bn >= an);

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
    _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_21(alloc, rp, m, ap, an, bp, bn), goto fallback_school;);
    return;
  }

  if(an <= _ULBN_TOOM_2_THRESHOLD) {
  fallback_toom22:
    /* if(bn > m) */
    _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_22(alloc, rp, m2, ap, an, bp, bn), goto fallback_school;);
    return;
  }

  m = (an + 2) / 3;
  if(bn > m + m) {
    _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_33(alloc, rp, m, ap, an, bp, bn), goto fallback_toom22;);
    return;
  }
  /* if(bn > m) */
  _ULBN_DO_IF_MUL_FAILED(_ulbn_mul_toom_32(alloc, rp, m, ap, an, bp, bn), goto fallback_toom22;);
  return;
#undef _ULBN_DO_IF_MUL_FAILED
}

/* rp[0:an+bn] = ap[0:an] * bp[0:bn]
  This version will automatically select the appropriate algorithm for computation. */
ULBN_INTERNAL int ulbn_mul_guard(
  ulbn_alloc_t* alloc, ulbn_limb_t* rp,   /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn  /* */
) {
  ulbn_limb_t *ul_restrict tap = ul_nullptr, *ul_restrict tbp = ul_nullptr;
  int err;

  ulbn_assert(an + bn >= an);
  if(ul_unlikely(rp == ap)) {
    tap = ulbn_allocT(ulbn_limb_t, alloc, an);
    ULBN_RETURN_IF_ALLOC_FAILED(tap, ULBN_ERR_NOMEM);
    ulbn_copy(tap, ap, an);
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
  rshift = ul_static_cast(int, ULBN_LIMB_BITS) - shift - 1;

  ai = ap[an - 1];
  a1 = (ai >> rshift) >> 1;

  /* ap'[i] = (ap[i] << shift) | (ap[i - 1] >> rshift) */
  for(i = an - 1; i > 0; --i) {
    a0 = ul_static_cast(ulbn_limb_t, ai << shift);
    ai = ap[i - 1];
    a0 |= (ai >> rshift) >> 1;
    _ulbn_udiv_2by1_(qp[i], a1, a1, a0, d, di);
  }

  a0 = ul_static_cast(ulbn_limb_t, ai << shift);
  _ulbn_udiv_2by1_(qp[0], a1, a1, a0, d, di);
  rp[0] = a1 >> shift;
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
  ulbn_assert(shift >= 0 && ul_static_cast(unsigned, shift) < ULBN_LIMB_BITS);
  rshift = ul_static_cast(int, ULBN_LIMB_BITS) - shift - 1;

  a2 = (ap[an - 1] >> rshift) >> 1;
  ai = ap[an - 2];
  a1 = ul_static_cast(ulbn_limb_t, (ap[an - 1] << shift) | ((ai >> rshift) >> 1));
  for(i = an - 2; i > 0; --i) {
    a0 = ul_static_cast(ulbn_limb_t, ai << shift);
    ai = ap[i - 1];
    a0 |= (ai >> rshift) >> 1;
    _ulbn_udiv_3by2_(qp[i], a2, a1, a2, a1, a0, d1, d0, di);
  }

  a0 = ul_static_cast(ulbn_limb_t, ai << shift);
  _ulbn_udiv_3by2_(qp[0], a2, a1, a2, a1, a0, d1, d0, di);
  rp[1] = a2 >> shift;
  rp[0] = ul_static_cast(ulbn_limb_t, ((a2 << rshift) << 1) | (a1 >> shift));
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
        a2 += d1 + ulbn_addn(rp + i, rp + i, dp, dn - 1);
        --q;
      }
    }

    qp[i] = q;
  } while(i-- > 0);

  rp[dn - 1] = a2;
}

ULBN_INTERNAL int ulbn_divmod1(
  ulbn_alloc_t* alloc, ulbn_limb_t* qp, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t d  /* */
) {
  ulbn_limb_t rp_buf[1];
  ulbn_limb_t* nqp = qp;
  int shift, err;

  ulbn_assert(d != 0);
  shift = _ulbn_clz_(d);

  d <<= shift;
  if(qp == ul_nullptr) {
    nqp = ulbn_allocT(ulbn_limb_t, alloc, an);
    ULBN_RETURN_IF_ALLOC_FAILED(nqp, ULBN_ERR_NOMEM);
  }
  ulbn_divmod_inv1(nqp, rp_buf, ap, an, d, ulbn_divinv1(d), shift);
  if(rp) {
    rp[0] = rp_buf[0];
    err = 0;
  } else
    err = rp_buf[0] ? ULBN_ERR_INEXACT : 0;
  if(ul_unlikely(nqp != qp))
    ulbn_deallocT(ulbn_limb_t, alloc, nqp, an);
  return err;
}

ULBN_PRIVATE int _ulbn_divmod_large(
  ulbn_alloc_t* alloc, ulbn_limb_t* qp, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,                /* */
  const ulbn_limb_t* dp, ulbn_usize_t dn, int shift      /* */
) {
  ulbn_limb_t a2 = 0;
  ulbn_limb_t *nrp = rp, *nqp = qp;
  ulbn_limb_t* tdp = ul_nullptr;
  int err;

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

  ulbn_divmod_inv(nqp, nrp, an, a2, dp, dn, ulbn_divinv2(dp[dn - 1], dp[dn - 2]));

  if(rp != ul_nullptr) {
    if(shift != 0)
      ulbn_shr(rp, nrp, dn, shift);
    else
      ulbn_maycopy(rp, nrp, dn);
    err = 0;
  } else
    err = ulbn_normalize(nrp, dn) == 0 ? 0 : ULBN_ERR_INEXACT;

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
  ulbn_alloc_t* alloc, ulbn_limb_t* qp, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,                /* */
  const ulbn_limb_t* dp, ulbn_usize_t dn                 /* */
) {
  ulbn_limb_t rp_buf[2] = {0, 0};
  int shift = _ulbn_clz_(dp[dn - 1]);
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
    const ulbn_limb_t d0 = ul_static_cast(ulbn_limb_t, dp[0] << shift);
    ulbn_limb_t* nqp = qp;

    /* `qp` can be equal to `ap`, but `qp` cannot be NULL */
    if(qp == ul_nullptr) {
      nqp = ulbn_allocT(ulbn_limb_t, alloc, an);
      ULBN_RETURN_IF_ALLOC_FAILED(nqp, ULBN_ERR_NOMEM);
    }
    if(dn == 1)
      ulbn_divmod_inv1(nqp, rp_buf, ap, an, d0, ulbn_divinv1(d0), shift);
    else {
      const ulbn_limb_t d1 = ul_static_cast(
        ulbn_limb_t, (dp[1] << shift) | (dp[0] >> (ul_static_cast(int, ULBN_LIMB_BITS) - shift - 1) >> 1)
      );
      ulbn_divmod_inv2(nqp, rp_buf, ap, an, d1, d0, ulbn_divinv2(d1, d0), shift);
    }

    if(rp) {
      rp[0] = rp_buf[0];
      if(dn == 2)
        rp[1] = rp_buf[1];
    } else
      rem = rp_buf[0] | rp_buf[1];
    if(qp != nqp)
      ulbn_deallocT(ulbn_limb_t, alloc, nqp, an);
    return rem ? ULBN_ERR_INEXACT : 0;
  }

  return _ulbn_divmod_large(alloc, qp, rp, ap, an, dp, dn, shift);
}


/* Convert ap[0:an] to base b. If allocation fails, return 0; otherwise, return the length after conversion */
ULBN_INTERNAL ulbn_usize_t ulbn_convbase(
  ulbn_alloc_t* alloc, ulbn_limb_t** p_cp, ulbn_usize_t* p_cn, /* */
  ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t b              /* */
) {
  ulbn_limb_t* cp = ul_nullptr;
  ulbn_usize_t cn = 0, ci = 0;
  ulbn_limb_t bi;
  int shift;

  ulbn_assert(b >= 2);

  shift = _ulbn_clz_(b);
  b <<= shift;
  bi = ulbn_divinv1(b);

  while(an > 0) {
    if(ul_unlikely(ci >= cn)) {
      ulbn_limb_t* ncp;
      ulbn_usize_t ncn;
      ncn = cn + (cn >> 1) + 1u;
      ULBN_DO_IF_ALLOC_COND(ncn < cn, {
        ncn = ULBN_USIZE_MAX;
        if(ul_unlikely(ncn == cn)) {
          ulbn_deallocT(ulbn_limb_t, alloc, cp, cn);
          return 0;
        }
      });
      ncp = ulbn_reallocT(ulbn_limb_t, alloc, cp, cn, ncn);
      ULBN_DO_IF_ALLOC_COND(ncp == ul_nullptr, {
        ulbn_deallocT(ulbn_limb_t, alloc, cp, cn);
        return 0;
      });
      cp = ncp;
      cn = ncn;
    }
    ulbn_divmod_inv1(ap, cp + (ci++), ap, an, b, bi, shift);
    if(ul_likely(ap[an - 1] == 0))
      --an;
  }
  *p_cp = cp;
  *p_cn = cn;
  return ci;
}
/**
 * Convert the base-b representation from `ulbn_convbase` to a string.
 *
 * \note To boost conversion speed, `ulbn_convbase` can use {b^B_pow} as the base.
 *=
 * \param ci The length of the base-b representation. (Return value of `ulbn_convbase`)
 * \param cp The base-b representation. (Alloced by `ulbn_convbase`)
 * \param op The output buffer.
 * \param on The length of the output buffer.
 * \param b The base casted to string.
 * \param B_pow The value that {B=b^B_pow}.
 * \param char_table The character table.
 *
 * \return String length;
 * \return If memory is insufficient, return 0;
 * \return If op[0:on] is not enough to hold the string, do not write and return required length.
 */
ULBN_INTERNAL ulbn_usize_t ulbn_conv2str(
  ulbn_usize_t ci, ulbn_limb_t* cp,                     /* */
  char* op, ulbn_usize_t on,                            /* */
  ulbn_limb_t b, unsigned B_pow, const char* char_table /* */
) {
  ulbn_usize_t i, n;
  ulbn_limb_t t;
  unsigned j;

  ulbn_assert(b >= 2);

  ULBN_RETURN_IF_USIZE_COND(ci >= ULBN_USIZE_MAX / B_pow, 0);
  n = (ci - 1) * B_pow;
  for(t = cp[ci - 1]; t; t /= b)
    ++n;
  if(n > on)
    return n;

  op += n;
  --ci;
  for(i = 0; i < ci; ++i) {
    t = cp[i];
    for(j = 0; j < B_pow; ++j) {
      *--op = char_table[cp[i] % b];
      cp[i] /= b;
    }
  }
  for(t = cp[ci]; t; t /= b)
    *--op = char_table[t % b];
  return n;
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
    al = (ap[i] ^ a_mask) + a_cy;
    a_cy = (al < a_cy);
    bl = (bp[i] ^ b_mask) + b_cy;
    b_cy = (bl < b_cy);
    rl = ((al & bl) ^ r_mask) + r_cy;
    rp[i] = rl;
    r_cy = (rl < r_cy);
  }
  ulbn_assert(b_cy == 0);
  for(; i < an; ++i) {
    al = (ap[i] ^ a_mask) + a_cy;
    a_cy = (al < a_cy);
    rl = ((al & b_mask) ^ r_mask) + r_cy;
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
    al = (ap[i] ^ a_mask) + a_cy;
    a_cy = (al < a_cy);
    bl = (bp[i] ^ b_mask) + b_cy;
    b_cy = (bl < b_cy);
    rl = ((al | bl) ^ r_mask) + r_cy;
    rp[i] = rl;
    r_cy = (rl < r_cy);
  }
  ulbn_assert(b_cy == 0);
  for(; i < an; ++i) {
    al = (ap[i] ^ a_mask) + a_cy;
    a_cy = (al < a_cy);
    rl = ((al | b_mask) ^ r_mask) + r_cy;
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
    al = (ap[i] ^ a_mask) + a_cy;
    a_cy = (al < a_cy);
    bl = (bp[i] ^ b_mask) + b_cy;
    b_cy = (bl < b_cy);
    rl = ((al ^ bl) ^ r_mask) + r_cy;
    rp[i] = rl;
    r_cy = (rl < r_cy);
  }
  ulbn_assert(b_cy == 0);
  for(; i < an; ++i) {
    al = (ap[i] ^ a_mask) + a_cy;
    a_cy = (al < a_cy);
    rl = ((al ^ b_mask) ^ r_mask) + r_cy;
    rp[i] = rl;
    r_cy = (rl < r_cy);
  }
  ulbn_assert(a_cy == 0);
  return r_cy;
}
/* In 2's complement, rp[0:an] = cy ? ~ap[0:an] : ap[0:an], return carry (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_com(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t cy) {
  ulbn_usize_t i;
  const ulbn_limb_t mask = _ulbn_neg_(cy);

  ulbn_assert(cy == 0 || cy == 1);
  ulbn_assert_forward_overlap(rp, an, ap, an);

  for(i = 0; i < an; ++i)
    cy = ((rp[i] = (ap[i] ^ mask) + cy) < cy);
  return cy;
}

/* Get (cy ? -p[0:n] : p[0:n])[k] in two's complement sense */
ULBN_INTERNAL ulbn_limb_t ulbn_limb(const ulbn_limb_t* p, ulbn_usize_t n, ulbn_limb_t cy, ulbn_usize_t k) {
  /* The method here is the same as `ulbn_neg_limb`, except positive numbers
   * need special handling */

  const ulbn_limb_t mask = _ulbn_neg_(cy);
  const ulbn_limb_t l = (k < n ? p[k] : 0) ^ mask;
  /* If it is a positive number, cy == 0, mask == 0, at this time i will be
    equal to ULBN_LIMB_MAX, and the loop will terminate directly */
  ulbn_usize_t i = ~mask & ULBN_USIZE_MAX;

  ulbn_assert(cy == 0 || cy == 1);

  while(i < k && p[i] == 0)
    ++i;
  /* If `cy`==0, there is no carry 1, it is masked out */
  return l + ((i == k) & cy);
}
/* return p[0:n] is power of 2 */
ULBN_INTERNAL int ulbn_is_2pow(const ulbn_limb_t* p, ulbn_usize_t n) {
  if(n == 0)
    return 1;
  return (p[n - 1] & (p[n - 1] - 1u)) == 0 && ulbn_is0(p, n - 1) != 0;
}


ul_static_assert(_ULBN_LIMB_BITS < ULBN_LIMB_MAX, "ULBN_LIMB_BITS is too large");
ul_static_assert(_ULBN_LIMB_BITS < INT_MAX, "ULBN_LIMB_BITS is too large");
ul_static_assert(ULBN_USIZE_MAX / _ULBN_LIMB_BITS <= _ULBN_SSIZE_LIMIT, "ULBN_LIMB_BITS is too small");
/* may return `ULBN_ERR_EXCEED_RANGE` */
ULBN_INTERNAL int ulbn_to_bit_info(ulbn_limb_t* limb, ulbn_usize_t n, ulbn_usize_t* p_idx) {
#if ULBN_LIMB_MAX >= ULBN_USIZE_MAX
  ulbn_limb_t q, r;

  if(ul_unlikely(n > 1))
    return ULBN_ERR_EXCEED_RANGE;
  if(n == 0) {
    *p_idx = 0;
    return 0;
  }
  q = limb[0] / ULBN_LIMB_BITS;
  r = limb[0] % ULBN_LIMB_BITS;
  #if ULBN_LIMB_MAX > ULBN_USIZE_MAX
  if(ul_unlikely(q > ULBN_USIZE_MAX))
    return ULBN_ERR_EXCEED_RANGE;
  #endif
  *p_idx = ul_static_cast(ulbn_usize_t, q);
  return ul_static_cast(int, r);
#else
  ulbn_limb_t q[(sizeof(ulbn_usize_t) * CHAR_BIT + ULBN_LIMB_BITS - 1u) / ULBN_LIMB_BITS];
  ulbn_limb_t r[1];
  ulbn_usize_t qn;
  ulbn_usize_t idx = 0;

  static const ulbn_usize_t N_LIMIT = (sizeof(ulbn_usize_t) * CHAR_BIT + ULBN_LIMB_BITS - 1u) / ULBN_LIMB_BITS;
  const int shift = ul_static_cast(
    int, ULBN_LIMB_BITS - ul_static_cast(unsigned, _ulbn_clz_(ul_static_cast(ulbn_limb_t, ULBN_LIMB_BITS)))
  );
  const ulbn_limb_t d_norm = ul_static_cast(ulbn_limb_t, ul_static_cast(ulbn_limb_t, ULBN_LIMB_BITS) << shift);
  const ulbn_limb_t d_inv = ulbn_divinv1(d_norm);

  if(n > N_LIMIT)
    return ULBN_ERR_EXCEED_RANGE;
  if(n == 0) {
    *p_idx = 0;
    return 0;
  } else if(n == 1) { /* fast path */
    *p_idx = limb[0] / ULBN_LIMB_BITS;
    return ul_static_cast(int, limb[0] % ULBN_LIMB_BITS);
  }

  ulbn_divmod_inv1(q, r, limb, n, d_norm, d_inv, shift);
  qn = ulbn_normalize(q, n);
  ulbn_assert(qn > 0);

  if(ul_unlikely(
       qn * ULBN_LIMB_BITS - ul_static_cast(unsigned, _ulbn_clz_(q[qn - 1])) > sizeof(ulbn_usize_t) * CHAR_BIT
     ))
    return ULBN_ERR_EXCEED_RANGE;

  do {
    idx <<= sizeof(ulbn_limb_t) * CHAR_BIT;
    idx |= q[--qn];
  } while(qn);
  *p_idx = idx;
  return ul_static_cast(int, r[0]);
#endif
}


ULBN_INTERNAL unsigned ulbn_rand_gen(ulbn_rand_t* rng) {
  ulbn_rand_uint_t state;
  unsigned ret, shift;
  state = rng->state;
  rng->state = state * 0x321Du + rng->inc;
  shift = state >> 28;
  ret = ul_static_cast(unsigned, (((state >> 10u) ^ state) >> 12u) & 0xFFFFu);
  ret = (ret >> shift) | (ret << ((0u - shift) & 15));
  return ret & 0xFFFFu;
}

#include <time.h>
ULBN_PUBLIC void ulbn_rand_init2(ulbn_rand_t* rng, ulbn_rand_uint_t seed) {
  rng->state = 0u;
  rng->inc = (0xBB75u << 1u) | 1u;
  rng->state = rng->state * 0x321Du + rng->inc;
  rng->state += seed;
  rng->state = rng->state * 0x321Du + rng->inc;

  rng->bits = 0;
  rng->cache = 0;
}
ULBN_PUBLIC ulbn_rand_uint_t ulbn_rand_init(ulbn_rand_t* rng) {
  ulbn_rand_uint_t seed;
  seed = ul_static_cast(ulbn_rand_uint_t, ul_reinterpret_cast(size_t, &seed));
  seed ^= ul_static_cast(ulbn_rand_uint_t, time(ul_nullptr));
  seed ^= ul_static_cast(ulbn_rand_uint_t, clock());
  ulbn_rand_init2(rng, seed);
  return seed;
}

ULBN_INTERNAL ulbn_limb_t ulbn_rand(ulbn_rand_t* rng, int n) {
  int b = rng->bits;
  unsigned c = rng->cache;
  ulbn_limb_t l = 0;

  ulbn_assert(n >= 0 && ul_static_cast(size_t, n) <= ULBN_LIMB_BITS);

#if ULBN_LIMB_MAX >= 0xFFFFu
  while(n >= 16) {
    l <<= 16;
    l |= ul_static_cast(ulbn_limb_t, ulbn_rand_gen(rng));
    n -= 16;
  }
#endif

  if(b < n) {
    l <<= b;
    l |= ul_static_cast(ulbn_limb_t, c);
    c = ulbn_rand_gen(rng);
    n -= b;
    b = 16;
  }

  l <<= n;
  l |= ul_static_cast(ulbn_limb_t, c & (ULBN_LIMB_SHL(1u, n) - 1u));
  rng->cache = c >> n;
  rng->bits = b - n;
  return l;
}
ULBN_INTERNAL void ulbn_rand_multi(ulbn_rand_t* rng, ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
    p[i] = ulbn_rand(rng, ULBN_LIMB_BITS);
}

ULBN_PUBLIC void ulbn_rand_fill(ulbn_rand_t* rng, void* dst, size_t n) {
  unsigned char* p = ul_reinterpret_cast(unsigned char*, dst);
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
    p[i] = ul_static_cast(unsigned char, ulbn_rand(rng, CHAR_BIT));
}


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
  v -= s * s;
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
  x = ULBN_LIMB_SHL(1, (ULBN_LIMB_BITS - ul_static_cast(unsigned, _ulbn_clz_(v)) + 3) >> 1);
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
  numl = (numl << ULBN_LIMB_HALF_BITS) | ULBN_HIGHPART(a0);
  s <<= 1;
  _ulbn_udiv_(q, u, numh, numl, s);
  s = (s << (ULBN_LIMB_HALF_BITS - 1u)) + q;
  rh = ULBN_HIGHPART(u);
  rl = (u << ULBN_LIMB_HALF_BITS) | ULBN_LOWPART(a0);
  if(ul_unlikely(q >> ULBN_LIMB_HALF_BITS) != 0)
    --rh;
  else {
    q *= q;
    rh -= (rl < q);
    rl -= q;
  }
  if(rh >= ULBN_LIMB_SIGNBIT) {
    --s;
    numh = s >> (ULBN_LIMB_BITS - 1);
    numl = s << 1 | 1u;
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
  ulbn_alloc_t* alloc, ulbn_limb_t* ul_restrict sp, /* */
  ulbn_limb_t* ul_restrict rp, ulbn_usize_t n,      /* */
  ulbn_limb_t* ul_restrict tp                       /* */
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
    cy = ulbn_subn(rp, rp, rp + n, nl << 1);
  }
  rh -= ulbn_sub1(rp + (nl << 1), rp + (nl << 1), n - (nl << 1), cy);
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
  ulbn_alloc_t* alloc, ulbn_limb_t* sp, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an                 /* */
) {
  ulbn_limb_t *nrp = rp, *nsp = sp, *tp;
  ulbn_limb_t rh;
  int shift, shift2, err = ULBN_ERR_NOMEM;
  const unsigned odd = ul_static_cast(unsigned, an & 1u);
  const ulbn_usize_t nh = an - (an >> 1), nr = (an >> 1) + 1u;

  ulbn_assert(an > 0 && an < ULBN_USIZE_MAX);
  ulbn_assert(ap != ul_nullptr);
  ulbn_assert(ap[an - 1] != 0);
  ulbn_assert_same_or_not_overlap(sp, an - (an >> 1), ap, an);
  ulbn_assert_same_or_not_overlap(sp, an - (an >> 1), rp, an - (an >> 1));
  ulbn_assert_same_or_not_overlap(rp, an - (an >> 1), ap, an);

  shift = (_ulbn_clz_(ap[an - 1]) >> 1) << 1;
  shift2 = shift + ul_static_cast(int, odd ? ULBN_LIMB_BITS : 0u);
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
      cr = nsp[0] & (ULBN_LIMB_SHL(1u, shift2 >> 1) - 1u);
      rh += ulbn_addmul1(nrp, nsp, nh, cr);
      rh += ulbn_addmul1(nrp, nsp, nh, cr);
      rh -= ulbn_sub1(nrp, nrp, nh, cr * cr);
      rp[nr - 1] = rh >> shift;
      if(nh > odd) {
        if(shift) {
          ulbn_shr(rp, nrp + odd, nh - odd, shift);
          rp[nh - 1 - odd] |= rh << (ul_static_cast(int, ULBN_LIMB_BITS) - shift);
        } else
          ulbn_copy(rp, nrp + odd, nh - odd);
      }
    } else {
      rp[nr - 1] = rh;
      ulbn_maycopy(rp, nrp, nh);
    }
  } else
    err = ulbn_normalize(nrp, nh) == 0 ? 0 : ULBN_ERR_INEXACT;
  if(sp) {
    if(shift2)
      ulbn_shr(sp, nsp, nh, shift2 >> 1);
    else
      ulbn_maycopy(sp, nsp, nh);
  }

  ulbn_deallocT(ulbn_limb_t, alloc, tp, nr);
cleanup:
  if(nrp != rp)
    ulbn_deallocT(ulbn_limb_t, alloc, nrp, nr);
  if(nsp != sp)
    ulbn_deallocT(ulbn_limb_t, alloc, nsp, nh);
  return err;
}


#if 0
ULBN_PRIVATE ulbn_limb_t _ulbn_pow_(ulbn_limb_t v, size_t e) {
  ulbn_limb_t r = 1u;
  for(; e; e >>= 1) {
    if(e & 1)
      r *= v;
    v *= v;
  }
  return r;
}
ULBN_PRIVATE ulbn_limb_t _ulbn_pow_adjust_(ulbn_limb_t v, size_t e) {
  ulbn_limb_t rh = 0, rl = 1;
  ulbn_limb_t vh = 0, vl = v;
  ulbn_limb_t th, tl;
  while(e) {
    if(e & 1) {
      _ulbn_umul_(th, tl, rl, vl);
      rh = th + rh * vl + rl * vh;
      rl = tl;
    }
    _ulbn_umul_(th, tl, vl, vl);
    vh = th + 2 * vl * vh;
    vl = tl;
    e >>= 1;
  }
  if(rh)
    return ULBN_LIMB_MAX;
  return rl;
}
ULBN_PRIVATE int _ulbn_check_root_too_small_(ulbn_limb_t x, size_t e, ulbn_limb_t v) {
  while(e-- > 0)
    v /= (x + 1);
  return v == 0;
}
/* Ensure v != 0 and e >= 2. Time complexity is at most O(log({ULBN_LIMB_BITS}) * log(e))*/
ULBN_PRIVATE ulbn_limb_t _ulbn_root_(ulbn_limb_t v, size_t e) {
  ulbn_limb_t x, y = 1;

  ulbn_assert(v != 0);
  ulbn_assert(e >= 2);
  ulbn_assert(ULBN_LIMB_BITS <= ~ul_static_cast(size_t, 0) - e + 1);
  x = ULBN_LIMB_SHL(1, (ULBN_LIMB_BITS - ul_static_cast(unsigned, _ulbn_clz_(v)) + e - 1) / e + 1);

  /*
    Newton's method:
    f(x) = x^e - v
    f'(x) = e * x^(e-1)
    x' = x - f(x)/f'(x) = x - (x^e - v)/(e * x^(e - 1)) = ((e-1)*x + v/x^(e-1)) / e
  */
  if(ul_unlikely(_ulbn_check_root_too_small_(x, e, v))) /* maybe overflow */
    while(x > y) {
      x = ul_static_cast(ulbn_limb_t, ((e - 1) * x + y) / e);
      y = v / _ulbn_pow_adjust_(x, e - 1);
    }
  else
    while(x > y) {
      x = ul_static_cast(ulbn_limb_t, ((e - 1) * x + y) / e);
      y = v / _ulbn_pow_(x, e - 1);
    }

  ulbn_assert(_ulbn_pow_(x, e) <= v && _ulbn_check_root_too_small_(x + 1, e, v));
  return x;
}
#endif


ULBN_PRIVATE ulbn_limb_t _ulbn_gcd_(ulbn_limb_t a, ulbn_limb_t b) {
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
  return a << shift;
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
    if(shl_shift > ul_static_cast(int, ULBN_LIMB_BITS)) {
      shl_shift -= ul_static_cast(int, ULBN_LIMB_BITS);
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

#if 0
    printf("ap = ");
    ulbn_dump(stdout, ap, an);
    printf("\tbp = ");
    ulbn_dump(stdout, bp, bn);
    putchar('\n');
#endif

    cmp = ulbn_cmp(ap, an, bp, bn);
    if(cmp == 0)
      break;
    if(cmp > 0) {
      ulbn_sub(ap, ap, an, bp, bn);
      an = ulbn_normalize(ap, an);
    } else {
      ulbn_sub(bp, bp, bn, ap, an);
      bn = ulbn_normalize(bp, bn);
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
  return ulbn_normalize(ap, shl_idx + an);
}


#if 0
/* return ap[0:an] <=> mp[0:mn]/2 */
ULBN_INTERNAL int ulbn_check_round(const ulbn_limb_t* ap, ulbn_usize_t an, const ulbn_limb_t* mp, ulbn_usize_t mn) {
  const int b = 1, br = ULBN_LIMB_BITS - 1;
  ulbn_limb_t ah, al;
  ulbn_limb_t m0;
  ulbn_usize_t i;

  ulbn_assert(an <= mn);
  if(an < mn - 1)
    return -1;
  else
    m0 = (an == mn) ? 0 : mp[an];

  al = mp[mn - 1];
  if((ah = (al >> br)) != m0)
    return ah > m0 ? 1 : -1;
  ah = ul_static_cast(ulbn_limb_t, al << b);
  for(i = an - 1; i > 0; --i) {
    al = ap[i - 1];
    ah |= (al >> br);
    if(ah != mp[i])
      return ah > mp[i] ? 1 : -1;
    ah = ul_static_cast(ulbn_limb_t, al << b);
  }
  if(ah == mp[0])
    return 0;
  return ah > mp[i] ? 1 : -1;
}
#endif

/***************
 * Big Integer *
 ***************/

ULBN_PUBLIC ulbi_t* ulbi_init(ulbi_t* o) {
  o->len = 0;
  o->cap = 0;
  o->limb = ul_nullptr;
  return o;
}
ULBN_PUBLIC int ulbi_init_reserve(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n) {
  ULBN_RETURN_IF_USIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
  if(n)
    o->limb = ulbn_allocT(ulbn_limb_t, alloc, n);
  else
    o->limb = ul_nullptr;
  o->len = 0;
  o->cap = n;
  return 0;
}
ULBN_PUBLIC ulbi_t* ulbi_set_zero(ulbi_t* dst) {
  dst->len = 0;
  return dst;
}

ULBN_PUBLIC void ulbi_deinit(ulbn_alloc_t* alloc, ulbi_t* o) {
  if(ul_likely(o->limb))
    ulbn_deallocT(ulbn_limb_t, alloc, o->limb, o->cap);
  o->len = 0;
  o->cap = 0;
  o->limb = ul_nullptr;
}
ULBN_PUBLIC int ulbi_shrink(ulbn_alloc_t* alloc, ulbi_t* o) {
  ulbn_limb_t* limb = ul_nullptr;
  ulbn_usize_t n = _ulbn_abs_size(o->len);
  if(n == 0) {
    if(ul_unlikely(o->limb))
      ulbn_deallocT(ulbn_limb_t, alloc, o->limb, o->cap);
  } else {
    limb = ulbn_reallocT(ulbn_limb_t, alloc, o->limb, o->cap, n);
    ULBN_RETURN_IF_ALLOC_FAILED(limb, ULBN_ERR_NOMEM);
  }
  o->limb = limb;
  o->cap = n;
  return 0;
}

ULBN_PRIVATE ulbn_limb_t* _ulbi_reserve(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n) {
  ulbn_usize_t new_cap;
  ulbn_limb_t* new_limb;

  ulbn_assert(n > o->cap);
  new_cap = o->cap + (o->cap >> 1);
  new_cap = _ulbn_max_(new_cap, n);
  ULBN_DO_IF_USIZE_OVERFLOW(new_cap, new_cap = n;);
  ULBN_DO_IF_USIZE_OVERFLOW(new_cap, return ul_nullptr;);
  new_limb = ulbn_reallocT(ulbn_limb_t, alloc, o->limb, o->cap, new_cap);
  ULBN_RETURN_IF_ALLOC_FAILED(new_limb, ul_nullptr);
  o->limb = new_limb;
  o->cap = new_cap;
  return new_limb;
}
#define _ulbi_res(alloc, o, n) (((n) <= (o)->cap) ? (o)->limb : _ulbi_reserve((alloc), (o), (n)))
#define _ulbi_limb(o) ((o)->limb)
ULBN_PUBLIC ulbn_limb_t* ulbi_reserve(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n) {
  return _ulbi_res(alloc, o, n);
}


ULBN_PUBLIC void ulbi_swap(ulbi_t* o1, ulbi_t* o2) {
  _ulbn_swap_(ulbi_t, *o1, *o2);
}
ULBN_PUBLIC int ulbi_neg(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao) {
  int err = ulbi_set_copy(alloc, ro, ao);
  ro->len = -ro->len;
  return err;
}
ULBN_PUBLIC int ulbi_abs(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao) {
  int err = ulbi_set_copy(alloc, ro, ao);
  ro->len = ulbn_cast_ssize(_ulbn_abs_size(ro->len));
  return err;
}


ULBN_PUBLIC int ulbi_set_copy(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* src) {
  if(dst != src) {
    ulbn_limb_t* limb;
    ulbn_usize_t n = _ulbn_abs_size(src->len);
    if(ul_likely(n)) {
      limb = _ulbi_res(alloc, dst, n);
      ULBN_RETURN_IF_ALLOC_FAILED(limb, ULBN_ERR_NOMEM);
      ulbn_copy(limb, _ulbi_limb(src), n);
    }
    dst->len = src->len;
  }
  return 0;
}
ULBN_PUBLIC void ulbi_set_move(ulbn_alloc_t* alloc, ulbi_t* dst, ulbi_t* src) {
  ulbi_deinit(alloc, dst);
  *dst = *src;
  ulbi_init(src);
}
ULBN_PUBLIC int ulbi_set_limb(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_limb_t limb) {
  if(limb == 0)
    dst->len = 0;
  else {
    ulbn_limb_t* ptr;
    ptr = _ulbi_res(alloc, dst, 1);
    ULBN_RETURN_IF_ALLOC_FAILED(ptr, ULBN_ERR_NOMEM);
    ptr[0] = limb;
    dst->len = 1;
  }
  return 0;
}
ULBN_PUBLIC int ulbi_set_slimb(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_slimb_t limb) {
  if(limb == 0)
    dst->len = 0;
  else {
    ulbn_limb_t* ptr;
    ptr = _ulbi_res(alloc, dst, 1);
    ULBN_RETURN_IF_ALLOC_FAILED(ptr, ULBN_ERR_NOMEM);
    if(limb < 0) {
      ptr[0] = _ulbn_from_neg_slimb(limb);
      dst->len = -1;
    } else {
      ptr[0] = _ulbn_from_pos_slimb(limb);
      dst->len = 1;
    }
  }
  return 0;
}
ul_static_assert(
  (sizeof(ulbn_ulong_t) * CHAR_BIT + _ULBN_LIMB_BITS - 1) / _ULBN_LIMB_BITS <= _ULBN_SSIZE_LIMIT,
  "ulbn_ulong_t is too large that `ulbi_t` cannot hold it"
);
ULBN_PUBLIC int ulbi_set_ulong(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ulong_t l) {
  ulbn_limb_t limbs[(sizeof(l) + sizeof(ulbn_limb_t) - 1) / sizeof(ulbn_limb_t)];
  ulbn_ssize_t len = 0;

#if ULBN_ULONG_MAX <= ULBN_LIMB_MAX
  if(l)
    limbs[len++] = ul_static_cast(ulbn_limb_t, l);
#else
  while(l) {
    limbs[len++] = ul_static_cast(ulbn_limb_t, l);
    l >>= ULBN_LIMB_BITS;
  }
#endif

  if(len != 0) {
    ulbn_limb_t* ptr;
    ptr = _ulbi_res(alloc, dst, ulbn_cast_usize(len));
    ULBN_RETURN_IF_ALLOC_FAILED(ptr, ULBN_ERR_NOMEM);
    ulbn_copy(ptr, limbs, ulbn_cast_usize(len));
  }
  dst->len = len;
  return 0;
}
ULBN_PUBLIC int ulbi_set_slong(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_slong_t l) {
  int err;
  if(l >= 0)
    err = ulbi_set_ulong(alloc, dst, _ulbn_from_pos_slong(l));
  else {
    err = ulbi_set_ulong(alloc, dst, _ulbn_from_neg_slong(l));
    dst->len = -dst->len;
  }
  return err;
}

ul_static_assert(
  (sizeof(ulbn_usize_t) * CHAR_BIT + _ULBN_LIMB_BITS - 1) / _ULBN_LIMB_BITS <= _ULBN_SSIZE_LIMIT,
  "ulbn_usize_t is too large that `ulbi_t` cannot hold it"
);
ULBN_PUBLIC int ulbi_set_usize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t l) {
  ulbn_limb_t limbs[(sizeof(l) + sizeof(ulbn_limb_t) - 1) / sizeof(ulbn_limb_t)];
  ulbn_ssize_t len = 0;

#if ULBN_USIZE_MAX <= ULBN_LIMB_MAX
  if(l)
    limbs[len++] = ul_static_cast(ulbn_limb_t, l);
#else
  while(l) {
    limbs[len++] = ul_static_cast(ulbn_limb_t, l);
    l >>= ULBN_LIMB_BITS;
  }
#endif

  if(len != 0) {
    ulbn_limb_t* ptr;
    ptr = _ulbi_res(alloc, dst, ulbn_cast_usize(len));
    ULBN_RETURN_IF_ALLOC_FAILED(ptr, ULBN_ERR_NOMEM);
    ulbn_copy(ptr, limbs, ulbn_cast_usize(len));
  }
  dst->len = len;
  return 0;
}
ULBN_PUBLIC int ulbi_set_ssize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ssize_t l) {
  int err;
  if(l >= 0)
    err = ulbi_set_usize(alloc, dst, _ulbn_from_pos_ssize(l));
  else {
    err = ulbi_set_usize(alloc, dst, _ulbn_from_neg_ssize(l));
    dst->len = -dst->len;
  }
  return err;
}

ul_static_assert(
  ULBN_USIZE_MAX / _ULBN_LIMB_BITS + 1 <= _ULBN_SSIZE_LIMIT,
  "`ulbn_ssize_t` is too small to hold the maximum number of bits in `ulbn_usize_t`"
);
ULBN_PUBLIC int ulbi_set_2exp_usize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t n) {
  ulbn_limb_t* p;
  const ulbn_usize_t idx = n / ULBN_LIMB_BITS;
  p = _ulbi_res(alloc, dst, idx + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(p, ULBN_ERR_NOMEM);
  ulbn_fill0(p, idx);
  p[idx] = ULBN_LIMB_SHL(1, n % ULBN_LIMB_BITS);
  dst->len = ulbn_cast_ssize(idx + 1);
  return 0;
}
ULBN_PUBLIC int ulbi_set_2exp(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* n) {
  ulbn_limb_t* p;
  ulbn_usize_t idx;
  int shift;

  if(n->len < 0) {
    dst->len = 0;
    return ULBN_ERR_INEXACT;
  }
  shift = ulbn_to_bit_info(_ulbi_limb(n), _ulbn_abs_size(n->len), &idx);
  if(ul_unlikely(shift < 0 || idx > ULBN_SSIZE_LIMIT - 1))
    return ULBN_ERR_EXCEED_RANGE;
  p = _ulbi_res(alloc, dst, idx + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(p, ULBN_ERR_NOMEM);
  ulbn_fill0(p, idx);
  p[idx] = ULBN_LIMB_SHL(1, shift);
  dst->len = ulbn_cast_ssize(idx + 1);
  return 0;
}

ULBN_PUBLIC int ulbi_set_string(ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, int base) {
  ulbn_limb_t GUARD;
  ulbn_limb_t l = 0, B = 1;
  unsigned x;
  char lim0, lim1, lim2;
  int err = 0;
  int neg = 0;

  dst->len = 0;
  if(str[0] == '-') {
    neg = 1;
    ++str;
  } else if(str[0] == '+')
    ++str;

  if(base == 0) {
    if(str[0] == '0')
      switch(str[1]) {
      case 'x':
      case 'X':
        base = 16;
        str += 2;
        break;
      case 'b':
      case 'B':
        base = 2;
        str += 2;
        break;
      case 'o':
      case 'O':
        base = 8;
        str += 2;
        break;
      default:
        if(str[1] >= '0' && str[1] <= '7') {
          base = 8;
          ++str;
        } else
          return 0;
      }
    else
      base = 10;
  }
  if(base < 2 || base > 36)
    return ULBN_ERR_EXCEED_RANGE;

  GUARD = ul_static_cast(ulbn_limb_t, ULBN_LIMB_MAX / ul_static_cast(unsigned, base));
  lim0 = base <= 10 ? ul_static_cast(char, '0' + base - 1) : '9';
  lim1 = ul_static_cast(char, base - 11 + 'A');
  lim2 = ul_static_cast(char, base - 11 + 'a');
  for(;; ++str) {
    if(B >= GUARD) {
      err = ulbi_mul_limb(alloc, dst, dst, B);
      ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
      err = ulbi_add_limb(alloc, dst, dst, l);
      ulbn_assert(err <= 0);
      ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
      l = 0;
      B = 1;
    }
    if(*str >= '0' && *str <= lim0)
      x = ul_static_cast(unsigned, *str - '0');
    else if(*str >= 'A' && *str <= lim1)
      x = ul_static_cast(unsigned, *str - 'A' + 10);
    else if(*str >= 'a' && *str <= lim2)
      x = ul_static_cast(unsigned, *str - 'a' + 10);
    else
      break;
    B *= ul_static_cast(unsigned char, base);
    l = ul_static_cast(ulbn_limb_t, l * ul_static_cast(unsigned char, base) + x);
  }
  if(B != 1) {
    err = ulbi_mul_limb(alloc, dst, dst, B);
    ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
    err = ulbi_add_limb(alloc, dst, dst, l);
  }
  ulbn_assert(err <= 0);
  if(neg)
    dst->len = -dst->len;
  return err;
}


ULBN_PUBLIC int ulbi_init_copy(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* src) {
  return ulbi_set_copy(alloc, ulbi_init(dst), src);
}
ULBN_PUBLIC void ulbi_init_move(ulbn_alloc_t* alloc, ulbi_t* dst, ulbi_t* src) {
  (void)alloc;
  *dst = *src;
  ulbi_init(src);
}
ULBN_PUBLIC int ulbi_init_limb(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_limb_t limb) {
  return ulbi_set_limb(alloc, ulbi_init(dst), limb);
}
ULBN_PUBLIC int ulbi_init_slimb(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_slimb_t limb) {
  return ulbi_set_slimb(alloc, ulbi_init(dst), limb);
}
ULBN_PUBLIC int ulbi_init_ulong(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ulong_t l) {
  return ulbi_set_ulong(alloc, ulbi_init(dst), l);
}
ULBN_PUBLIC int ulbi_init_slong(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_slong_t l) {
  return ulbi_set_slong(alloc, ulbi_init(dst), l);
}
ULBN_PUBLIC int ulbi_init_usize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t l) {
  return ulbi_set_usize(alloc, ulbi_init(dst), l);
}
ULBN_PUBLIC int ulbi_init_ssize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ssize_t l) {
  return ulbi_set_ssize(alloc, ulbi_init(dst), l);
}
ULBN_PUBLIC int ulbi_init_2exp_usize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t n) {
  return ulbi_set_2exp_usize(alloc, ulbi_init(dst), n);
}
ULBN_PUBLIC int ulbi_init_2exp(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* n) {
  return ulbi_set_2exp(alloc, ulbi_init(dst), n);
}
ULBN_PUBLIC int ulbi_init_string(ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, int base) {
  return ulbi_set_string(alloc, ulbi_init(dst), str, base);
}


ULBN_PUBLIC int ulbi_comp(const ulbi_t* ao, const ulbi_t* bo) {
  int a_positive = (ao->len >= 0), b_positive = (bo->len >= 0), cmp;
  if(a_positive != b_positive)
    return a_positive ? 1 : -1;
  cmp = ulbn_cmp(_ulbi_limb(ao), _ulbn_abs_size(ao->len), _ulbi_limb(bo), _ulbn_abs_size(bo->len));
  return a_positive ? cmp : -cmp;
}
ULBN_PUBLIC int ulbi_comp_limb(const ulbi_t* ao, ulbn_limb_t b) {
  const ulbn_ssize_t an = ao->len;
  if(an == 1) {
    const ulbn_limb_t a = _ulbi_limb(ao)[0];
    return a == b ? 0 : (a < b ? -1 : 1);
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
    b_fix = _ulbn_from_pos_slimb(b);
    c = 1;
  } else {
    b_fix = _ulbn_from_neg_slimb(b);
    c = -1;
    an = -an;
  }
  if(an == 1) {
    const ulbn_limb_t a = _ulbi_limb(ao)[0];
    return a == b_fix ? 0 : (a < b_fix ? -c : c);
  } else
    return an <= 0 ? -c : c;
}

ULBN_PRIVATE int _ulbi_comp_ulong(const ulbn_limb_t* ap, ulbn_ssize_t an, ulbn_ulong_t b) {
#if ULBN_ULONG_MAX <= ULBN_LIMB_MAX
  if(an == 1) {
    const ulbn_limb_t a = ap[0];
    return a == b ? 0 : (a < b ? -1 : 1);
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
  bits = ul_static_cast(unsigned, ul_static_cast(int, sizeof(ulbn_ulong_t) * CHAR_BIT) - _ulbn_clz_ulong(b));
  num = (bits - 1u) / ULBN_LIMB_BITS;
  bits = num * ULBN_LIMB_BITS;
  if(ul_static_cast(unsigned, an) != num + 1)
    return ul_static_cast(unsigned, an) < num + 1 ? -1 : 1;
  do {
    x = ul_static_cast(ulbn_limb_t, b >> bits);
    if(ap[num] != x)
      return ap[num] < x ? -1 : 1;
    bits -= ULBN_LIMB_BITS;
  } while(num--);
  return 0;
#endif
}
ULBN_PUBLIC int ulbi_comp_ulong(const ulbi_t* ao, ulbn_ulong_t b) {
  return _ulbi_comp_ulong(_ulbi_limb(ao), ao->len, b);
}
ULBN_PUBLIC int ulbi_comp_slong(const ulbi_t* ao, ulbn_slong_t b) {
  return b >= 0 ? _ulbi_comp_ulong(_ulbi_limb(ao), ao->len, _ulbn_from_pos_slong(b))
                : -_ulbi_comp_ulong(_ulbi_limb(ao), -ao->len, _ulbn_from_neg_slong(b));
}


ULBN_PUBLIC int ulbi_eq(const ulbi_t* ao, const ulbi_t* bo) {
  if(ao->len != bo->len)
    return 0;
  return ulbn_cmp(_ulbi_limb(ao), _ulbn_abs_size(ao->len), _ulbi_limb(bo), _ulbn_abs_size(bo->len)) == 0;
}
ULBN_PUBLIC int ulbi_eq_limb(const ulbi_t* ao, ulbn_limb_t b) {
  return b ? (ao->len == 1 && _ulbi_limb(ao)[0] == b) : (ao->len == 0);
}
ULBN_PUBLIC int ulbi_eq_slimb(const ulbi_t* ao, ulbn_slimb_t b) {
  if(b == 0)
    return ao->len == 0;
  else if(b > 0)
    return ao->len == 1 && _ulbi_limb(ao)[0] == _ulbn_from_pos_slimb(b);
  else
    return ao->len == -1 && _ulbi_limb(ao)[0] == _ulbn_from_neg_slimb(b);
}

ULBN_PRIVATE int _ulbi_eq_ulong(const ulbn_limb_t* ap, ulbn_ssize_t an, ulbn_ulong_t b) {
#if ULBN_ULONG_MAX < ULBN_LIMB_MAX
  return b ? (an == 1 && ap[0] == b) : (an == 0);
#else
  unsigned bits, num;

  if(an < 0)
    return 0;
  if(b == 0)
    return an == 0;

  bits = ul_static_cast(unsigned, ul_static_cast(int, sizeof(ulbn_ulong_t) * CHAR_BIT) - _ulbn_clz_ulong(b));
  num = (bits - 1u) / ULBN_LIMB_BITS;
  bits = num * ULBN_LIMB_BITS;
  if(ul_static_cast(unsigned, an) != num + 1)
    return 0;
  do {
    if(ap[num] != ul_static_cast(ulbn_limb_t, b >> bits))
      return 0;
    bits -= ULBN_LIMB_BITS;
  } while(num--);
  return 1;
#endif
}
ULBN_PUBLIC int ulbi_eq_ulong(const ulbi_t* ao, ulbn_ulong_t b) {
  return _ulbi_eq_ulong(_ulbi_limb(ao), ao->len, b);
}
ULBN_PUBLIC int ulbi_eq_slong(const ulbi_t* ao, ulbn_slong_t b) {
  return b >= 0 ? _ulbi_eq_ulong(_ulbi_limb(ao), ao->len, _ulbn_from_pos_slong(b))
                : _ulbi_eq_ulong(_ulbi_limb(ao), -ao->len, _ulbn_from_neg_slong(b));
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
  return o->len == 0 || (_ulbi_limb(o)[0] & 1) == 0;
}
ULBN_PUBLIC int ulbi_is_odd(const ulbi_t* o) {
  return o->len != 0 && (_ulbi_limb(o)[0] & 1) != 0;
}


/* ignore sign of `ao` and `bo` */
ULBN_PRIVATE int _ulbi_add_ignore_sign(
  ulbn_alloc_t* alloc, ulbi_t* ro,   /* */
  const ulbi_t* ao, ulbn_usize_t an, /* */
  const ulbi_t* bo, ulbn_usize_t bn  /* */
) {
  ulbn_limb_t* rp;

  if(an < bn) {
    _ulbn_swap_(const ulbi_t*, ao, bo);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }
  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);

  rp[an] = ulbn_add(rp, _ulbi_limb(ao), an, _ulbi_limb(bo), bn);
  an += (rp[an] != 0);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = ulbn_cast_ssize(an);
  return 0;
}
/* ignore sign of `ao` and `bo` */
ULBN_PRIVATE int _ulbi_sub_ignore_sign(
  ulbn_alloc_t* alloc, ulbi_t* ro,   /* */
  const ulbi_t* ao, ulbn_usize_t an, /* */
  const ulbi_t* bo, ulbn_usize_t bn  /* */
) {
  ulbn_usize_t rn;
  ulbn_limb_t* rp;
  int cmp = ulbn_cmp(_ulbi_limb(ao), an, _ulbi_limb(bo), bn);
  if(cmp == 0) {
    ro->len = 0;
    return 0;
  }

  rn = _ulbn_max_(an, bn);
  rp = _ulbi_res(alloc, ro, rn);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  if(cmp > 0) {
    ulbn_sub(rp, _ulbi_limb(ao), an, _ulbi_limb(bo), bn);
    ro->len = ulbn_cast_ssize(ulbn_normalize(rp, rn));
  } else {
    ulbn_sub(rp, _ulbi_limb(bo), bn, _ulbi_limb(ao), an);
    ro->len = -ulbn_cast_ssize(ulbn_normalize(rp, rn));
  }
  return 0;
}
ULBN_PUBLIC int ulbi_add(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  int positive = (ao->len >= 0), err;
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
  if(_ulbn_same_sign(ao->len, bo->len))
    err = _ulbi_add_ignore_sign(alloc, ro, ao, an, bo, bn);
  else
    err = _ulbi_sub_ignore_sign(alloc, ro, ao, an, bo, bn);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}
ULBN_PUBLIC int ulbi_sub(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  int positive = (ao->len >= 0), err;
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
  if(_ulbn_same_sign(ao->len, bo->len))
    err = _ulbi_sub_ignore_sign(alloc, ro, ao, an, bo, bn);
  else
    err = _ulbi_add_ignore_sign(alloc, ro, ao, an, bo, bn);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}

ULBN_PRIVATE int _ulbi_add_limb_ignore_sign(
  ulbn_alloc_t* alloc, ulbi_t* ro,   /* */
  const ulbi_t* ao, ulbn_usize_t an, /* */
  ulbn_limb_t b                      /* */
) {
  ulbn_limb_t* rp;

  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);

  rp[an] = ulbn_add1(rp, _ulbi_limb(ao), an, b);
  an += (rp[an] != 0);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = ulbn_cast_ssize(an);
  return 0;
}
ULBN_PRIVATE int _ulbi_sub_limb_ignore_sign(
  ulbn_alloc_t* alloc, ulbi_t* ro,   /* */
  const ulbi_t* ao, ulbn_usize_t an, /* */
  ulbn_limb_t b                      /* */
) {
  const ulbn_limb_t* ap;
  ulbn_limb_t* rp;

  rp = _ulbi_res(alloc, ro, _ulbn_max_(an, 1u));
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);

  ap = _ulbi_limb(ao);
  if(an >= 2) {
    ulbn_sub1(rp, _ulbi_limb(ao), an, b);
    ro->len = ulbn_cast_ssize(ulbn_normalize(rp, an));
  } else if(an == 1) {
    if(ap[0] >= b) {
      rp[0] = ap[0] - b;
      ro->len = (rp[0] != 0);
    } else {
      rp[0] = b - ap[0];
      ro->len = -1;
    }
  } else {
    rp[0] = b;
    ro->len = -(b != 0);
  }
  return 0;
}
ULBN_PUBLIC int ulbi_add_limb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  int positive = (ao->len >= 0), err;
  if(ao->len >= 0)
    err = _ulbi_add_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(ao->len), b);
  else
    err = _ulbi_sub_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(-ao->len), b);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}
ULBN_PUBLIC int ulbi_sub_limb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  int positive = (ao->len >= 0), err;
  if(ao->len >= 0)
    err = _ulbi_sub_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(ao->len), b);
  else
    err = _ulbi_add_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(-ao->len), b);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}
ULBN_PUBLIC int ulbi_limb_sub(ulbn_alloc_t* alloc, ulbi_t* ro, ulbn_limb_t a, const ulbi_t* bo) {
  int err;
  if(bo->len >= 0) {
    err = _ulbi_sub_limb_ignore_sign(alloc, ro, bo, ulbn_cast_usize(bo->len), a);
    ro->len = -ro->len;
  } else
    err = _ulbi_add_limb_ignore_sign(alloc, ro, bo, ulbn_cast_usize(-bo->len), a);
  return err;
}
ULBN_PUBLIC int ulbi_add_slimb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  return b >= 0 ? ulbi_add_limb(alloc, ro, ao, _ulbn_from_pos_slimb(b))
                : ulbi_sub_limb(alloc, ro, ao, _ulbn_from_neg_slimb(b));
}
ULBN_PUBLIC int ulbi_sub_slimb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  return b >= 0 ? ulbi_sub_limb(alloc, ro, ao, _ulbn_from_pos_slimb(b))
                : ulbi_add_limb(alloc, ro, ao, _ulbn_from_neg_slimb(b));
}
ULBN_PUBLIC int ulbi_slimb_sub(ulbn_alloc_t* alloc, ulbi_t* ro, ulbn_slimb_t a, const ulbi_t* bo) {
  int err;
  if(a >= 0)
    err = ulbi_limb_sub(alloc, ro, _ulbn_from_pos_slimb(a), bo);
  else {
    err = ulbi_add_limb(alloc, ro, bo, _ulbn_from_neg_slimb(a));
    ro->len = -ro->len;
  }
  return err;
}


ULBN_PUBLIC int ulbi_mul_limb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  int positive = (ao->len >= 0);
  ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_limb_t* rp;

  if(ul_unlikely(ao->len == 0 || b == 0)) {
    ro->len = 0;
    return 0;
  }
  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  rp[an] = ulbn_mul1(rp, _ulbi_limb(ao), an, b);
  an += (rp[an] != 0);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(positive, an);
  return 0;
}
ULBN_PUBLIC int ulbi_mul_slimb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  if(b >= 0) {
    return ulbi_mul_limb(alloc, ro, ao, _ulbn_from_pos_slimb(b));
  } else {
    const int err = ulbi_mul_limb(alloc, ro, ao, _ulbn_from_neg_slimb(b));
    ro->len = -ro->len;
    return err;
  }
}
ULBN_PUBLIC int ulbi_mul(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  int positive = _ulbn_same_sign(ao->len, bo->len), err;
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
  ulbn_limb_t* rp;
  ulbn_usize_t rn;

  if(ul_unlikely(an == 0 || bn == 0)) {
    ro->len = 0;
    return 0;
  }
  if(an < bn) {
    _ulbn_swap_(const ulbi_t*, ao, bo);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }
  rn = an + bn;
  rp = _ulbi_res(alloc, ro, rn);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  err = ulbn_mul_guard(alloc, rp, _ulbi_limb(ao), an, _ulbi_limb(bo), bn);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  rn -= (rp[rn - 1] == 0);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(positive, rn);
  return 0;
}


ULBN_PRIVATE int _ulbi_divmod(
  ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro,       /* */
  const ulbi_t* ao, ulbn_usize_t an, int a_positive, /* */
  const ulbi_t* bo, ulbn_usize_t bn, int b_positive  /* */
) {
  const int positive = (a_positive == b_positive);
  int err = 0;
  ulbn_limb_t *qp = ul_nullptr, *rp = ul_nullptr;

  if(ul_unlikely(bn == 0)) {
    if(qo)
      qo->len = 0;
    if(ro)
      ro->len = 0;
    return ULBN_ERR_DIV_BY_ZERO;
  }
  if(an < bn) {
    if(qo)
      qo->len = 0;
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

  err = ulbn_divmod_guard(alloc, qp, rp, _ulbi_limb(ao), an, _ulbi_limb(bo), bn);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  if(qo) {
    qo->len = ulbn_cast_ssize(ulbn_normalize(qp, an - bn + 1));
    qo->len = _ulbn_to_ssize(positive, qo->len);
  }
  if(ro) {
    ro->len = ulbn_cast_ssize(ulbn_normalize(rp, bn));
    ro->len = _ulbn_to_ssize(a_positive, ro->len);
  }
  return err;
}
ULBN_PUBLIC int ulbi_divmod(ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  return _ulbi_divmod(
    alloc, qo, ro,                             /* */
    ao, _ulbn_abs_size(ao->len), ao->len >= 0, /* */
    bo, _ulbn_abs_size(bo->len), bo->len >= 0  /* */
  );
}
ULBN_PUBLIC int ulbi_div(ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, const ulbi_t* bo) {
  return ulbi_divmod(alloc, qo, ul_nullptr, ao, bo);
}
ULBN_PUBLIC int ulbi_mod(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  return ulbi_divmod(alloc, ul_nullptr, ro, ao, bo);
}

ULBN_PUBLIC int ulbi_divmod_limb(ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_limb_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  int positive = (ao->len >= 0), err = 0;
  ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_limb_t *qp = ul_nullptr, *ap;

  if(ul_unlikely(b == 0)) {
    if(qo)
      qo->len = 0;
    if(ro)
      *ro = 0;
    return ULBN_ERR_DIV_BY_ZERO;
  }
  if(ul_unlikely(an == 0)) {
    if(qo)
      qo->len = 0;
    if(ro)
      *ro = 0;
    return 0;
  }

  if(qo) {
    qp = _ulbi_res(alloc, qo, an);
    ULBN_RETURN_IF_ALLOC_FAILED(qp, ULBN_ERR_NOMEM);
  }
  ap = _ulbi_limb(ao);

  if(an == 1) {
    ulbn_limb_t a = ap[0];
    ulbn_limb_t r = a % b;
    if(qp)
      qp[0] = a / b;
    if(ro)
      *ro = r;
    else
      err = r ? ULBN_ERR_INEXACT : 0;
  } else
    err = ulbn_divmod1(alloc, qp, ro, _ulbi_limb(ao), _ulbn_abs_size(ao->len), b);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  if(qo) {
    qo->len = ulbn_cast_ssize(ulbn_normalize(qp, an));
    qo->len = _ulbn_to_ssize(positive, qo->len);
  }
  if(ro && !positive && *ro != 0) {
    *ro = b - *ro;
    err = ULBN_ERR_INEXACT;
  }
  return err;
}
ULBN_PUBLIC int ulbi_div_limb(ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, ulbn_limb_t b) {
  return ulbi_divmod_limb(alloc, qo, ul_nullptr, ao, b);
}
ULBN_PUBLIC int ulbi_mod_limb(ulbn_alloc_t* alloc, ulbn_limb_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  return ulbi_divmod_limb(alloc, ul_nullptr, ro, ao, b);
}

ULBN_PUBLIC int ulbi_divmod_slimb(
  ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_slimb_t* ro, const ulbi_t* ao, ulbn_slimb_t _b
) {
  int positive = (ao->len >= 0) == (_b >= 0), a_positive = ao->len >= 0, err = 0;
  ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_limb_t *qp = ul_nullptr, *ap;
  const ulbn_limb_t b = _b >= 0 ? _ulbn_from_pos_slimb(_b) : _ulbn_from_neg_slimb(_b);
  ulbn_limb_t r;

  if(ul_unlikely(b == 0)) {
    if(qo)
      qo->len = 0;
    if(ro)
      *ro = 0;
    return ULBN_ERR_DIV_BY_ZERO;
  }
  if(ul_unlikely(an == 0)) {
    if(qo)
      qo->len = 0;
    if(ro)
      *ro = 0;
    return 0;
  }

  if(qo) {
    qp = _ulbi_res(alloc, qo, an);
    ULBN_RETURN_IF_ALLOC_FAILED(qp, ULBN_ERR_NOMEM);
  }
  ap = _ulbi_limb(ao);
  if(an == 1) {
    ulbn_limb_t a = ap[0];
    r = a % b;
    if(qp)
      qp[0] = a / b;
  } else {
    err = ulbn_divmod1(alloc, qp, &r, _ulbi_limb(ao), _ulbn_abs_size(ao->len), b);
    ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  }
  if(qo) {
    qo->len = ulbn_cast_ssize(ulbn_normalize(qp, an));
    qo->len = _ulbn_to_ssize(positive, qo->len);
  }
  if(ro)
    *ro = a_positive ? ul_static_cast(ulbn_slimb_t, r) : -ul_static_cast(ulbn_slimb_t, r);
  else
    err = r ? ULBN_ERR_INEXACT : 0;
  return err;
}
ULBN_PUBLIC int ulbi_div_slimb(ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, ulbn_slimb_t b) {
  return ulbi_divmod_slimb(alloc, qo, ul_nullptr, ao, b);
}
ULBN_PUBLIC int ulbi_mod_slimb(ulbn_alloc_t* alloc, ulbn_slimb_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  return ulbi_divmod_slimb(alloc, ul_nullptr, ro, ao, b);
}


ULBN_PUBLIC int ulbi_pow_usize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  ulbi_t B = ULBI_INIT, ta = ULBI_INIT;
  int err;

  if(ul_unlikely(ro == ao)) {
    err = ulbi_init_copy(alloc, &ta, ao);
    ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
    ao = &ta;
  }
  err = ulbi_set_limb(alloc, ro, 1);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  err = ulbi_set_copy(alloc, &B, ao);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);

  while(b) {
    if(b & 1) {
      err = ulbi_mul(alloc, ro, ro, &B);
      ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    }
    err = ulbi_mul(alloc, &B, &B, &B);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    b >>= 1;
  }

cleanup:
  ulbi_deinit(alloc, &B);
  ulbi_deinit(alloc, &ta);
  return err;
}
ULBN_PUBLIC int ulbi_pow(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbi_t B = ULBI_INIT, ta = ULBI_INIT;
  int err;
  ulbn_limb_t l, *p;
  ulbn_usize_t i = 0, n;
  unsigned j;

  if(ul_unlikely(b->len < 0)) {
    ro->len = 0;
    return ULBN_ERR_INEXACT;
  }

  if(ul_unlikely(ro == ao)) {
    err = ulbi_init_copy(alloc, &ta, ao);
    ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
    ao = &ta;
  }
  err = ulbi_set_limb(alloc, ro, 1);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  err = ulbi_set_copy(alloc, &B, ao);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);

  n = ulbn_cast_usize(b->len);
  p = _ulbi_limb(b);
  if(ul_likely(n)) {
    while(i + 1 < n) {
      l = p[i++];
      j = ul_static_cast(unsigned, ULBN_LIMB_BITS);
      while(j--) {
        if(l & 1) {
          err = ulbi_mul(alloc, ro, ro, &B);
          ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
        }
        err = ulbi_mul(alloc, &B, &B, &B);
        ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
        l >>= 1;
      }
    }
    l = p[i++];
    while(l) {
      if(l & 1) {
        err = ulbi_mul(alloc, ro, ro, &B);
        ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
      }
      err = ulbi_mul(alloc, &B, &B, &B);
      ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
      l >>= 1;
    }
  }

cleanup:
  ulbi_deinit(alloc, &B);
  ulbi_deinit(alloc, &ta);
  return err;
}
ULBN_PUBLIC int ulbi_sqrtrem(ulbn_alloc_t* alloc, ulbi_t* so, ulbi_t* ro, const ulbi_t* ao) {
  ulbn_limb_t *sp = ul_nullptr, *rp = ul_nullptr;
  ulbn_usize_t n;
  int err;

  if(ao->len == 0) {
    if(so)
      so->len = 0;
    if(ro)
      ro->len = 0;
    return 0;
  }
  if(ao->len < 0) {
    if(so)
      so->len = 0;
    if(ro)
      ro->len = 0;
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

  err = ulbn_sqrtrem_guard(alloc, sp, rp, _ulbi_limb(ao), n);
  if(so)
    so->len = ulbn_cast_ssize(ulbn_normalize(sp, n - (n >> 1)));
  if(ro)
    ro->len = ulbn_cast_ssize(ulbn_normalize(rp, (n >> 1) + 1u));
  return err;
}
ULBN_PUBLIC int ulbi_sqrt(ulbn_alloc_t* alloc, ulbi_t* so, const ulbi_t* ao) {
  return ulbi_sqrtrem(alloc, so, ul_nullptr, ao);
}
ULBN_PUBLIC int ulbi_rootrem(ulbn_alloc_t* alloc, ulbi_t* so, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* eo) {
  ulbi_t eo_n1[1] = {ULBI_INIT};
  ulbi_t xo[1] = {ULBI_INIT}, yo[1] = {ULBI_INIT}, to[1] = {ULBI_INIT};
  int err, cy;
  const int sign = ao->len < 0;

  /*
    Newton's method:
    f(x) = x^e - a
    f'(x) = e * x^(e-1)
    x' = x - f(x)/f'(x) = x - (x^e - a)/(e * x^(e - 1)) = ((e-1)*x + a/x^(e-1)) / e
  */

  if(eo->len == 0) {
    if(so)
      so->len = 0;
    if(ro)
      ro->len = 0;
    return ULBN_ERR_INVALID;
  }
  if(ao->len == 0) {
    if(so)
      so->len = 0;
    if(ro)
      ro->len = 0;
    return eo->len > 0 ? 0 : ULBN_ERR_DIV_BY_ZERO;
  }
  if(ao->len < 0 && ulbi_is_even(eo)) {
    if(so)
      so->len = 0;
    if(ro)
      ro->len = 0;
    return ULBN_ERR_INVALID;
  }
  if(ao->len == 1 && _ulbi_limb(ao)[0] == 1) {
    if(so)
      err = ulbi_set_slimb(alloc, so, ao->len > 0 ? 1 : -1);
    else
      err = 0;
    if(ro)
      ro->len = 0;
    return err;
  }
  if(eo->len == 1) {
    if(_ulbi_limb(eo)[0] == 1) {
      if(so)
        err = ulbi_set_copy(alloc, so, ao);
      else
        err = 0;
      if(ro)
        ro->len = 0;
      return err;
    }
    if(_ulbi_limb(eo)[0] == 2)
      return ulbi_sqrtrem(alloc, so, ro, ao);
  }
  if(eo->len < 0) {
    if(so)
      so->len = 0;
    if(ro)
      err = ulbi_set_copy(alloc, so, ao);
    else
      err = ULBN_ERR_INEXACT;
    return err;
  }

  /* e_n1 = e - 1, x = 2 ** ceil(bits_width(a) / e) + 1 */
  err = ulbi_sub_limb(alloc, eo_n1, eo, 1);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  err = ulbi_abs_bit_width(alloc, yo, ao);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  cy = ulbi_div(alloc, yo, yo, eo);
  ULBN_DO_IF_ALLOC_COND(cy < 0, goto cleanup;);
  err = ulbi_add_limb(alloc, yo, yo, 1 + (cy == ULBN_ERR_INEXACT));
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  err = ulbi_set_2exp(alloc, xo, yo);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
#if 0
  printf("bits = ");
  ulbi_print(alloc, yo, stdout, 10);
  putchar('\n');

  printf("e - 1 = ");
  ulbi_print(alloc, eo_n1, stdout, 10);
  putchar('\n');
#endif

  err = ulbi_set_limb(alloc, yo, 1);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  while(ulbi_comp(xo, yo) > 0) {
#if 0
    printf("x = ");
    ulbi_print(alloc, xo, stdout, 10);
    putchar('\t');

    printf("y = ");
    ulbi_print(alloc, yo, stdout, 10);
    putchar('\n');
#endif

    /* x = (x * (e - 1) + y) / e */
    /* y = abs(a) / (x ** (e - 1)) */
    err = ulbi_mul(alloc, xo, xo, eo_n1);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    err = ulbi_add(alloc, xo, xo, yo);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    err = ulbi_div(alloc, xo, xo, eo);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    err = ulbi_pow(alloc, to, xo, eo_n1);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    err = _ulbi_divmod(alloc, yo, ul_nullptr, ao, _ulbn_abs_size(ao->len), 1, to, ulbn_cast_usize(to->len), 1);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  }

  ulbn_assert(!ulbi_eq_limb(xo, 0));
  if(sign)
    xo->len = -xo->len;
  err = ulbi_mul(alloc, to, to, xo);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  if(ro) {
    err = ulbi_sub(alloc, ro, ao, to);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  } else
    err = ulbi_eq(to, ao) ? 0 : ULBN_ERR_INEXACT;
  if(so)
    ulbi_swap(so, xo);

cleanup:
  ulbi_deinit(alloc, eo_n1);
  ulbi_deinit(alloc, xo);
  ulbi_deinit(alloc, yo);
  ulbi_deinit(alloc, to);
  return err;
}
ULBN_PUBLIC int ulbi_root(ulbn_alloc_t* alloc, ulbi_t* so, const ulbi_t* ao, const ulbi_t* eo) {
  return ulbi_rootrem(alloc, so, ul_nullptr, ao, eo);
}


ULBN_PUBLIC int ulbi_and(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  ulbn_limb_t a_cy, b_cy, r_cy;
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
  ulbn_limb_t* rp;
  if(an < bn) {
    _ulbn_swap_(const ulbi_t*, ao, bo);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }
  a_cy = (ao->len < 0);
  b_cy = (bo->len < 0);
  r_cy = a_cy & b_cy;
  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  rp[an] = ulbn_and(rp, r_cy, _ulbi_limb(ao), an, a_cy, _ulbi_limb(bo), bn, b_cy);
  an = ulbn_normalize(rp, an + 1);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(!r_cy, an);
  return 0;
}
ULBN_PUBLIC int ulbi_or(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  ulbn_limb_t a_cy, b_cy, r_cy;
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
  ulbn_limb_t* rp;
  if(an < bn) {
    _ulbn_swap_(const ulbi_t*, ao, bo);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }
  a_cy = (ao->len < 0);
  b_cy = (bo->len < 0);
  r_cy = a_cy | b_cy;
  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  rp[an] = ulbn_or(rp, r_cy, _ulbi_limb(ao), an, a_cy, _ulbi_limb(bo), bn, b_cy);
  an = ulbn_normalize(rp, an + 1);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(!r_cy, an);
  return 0;
}
ULBN_PUBLIC int ulbi_xor(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  ulbn_limb_t a_cy, b_cy, r_cy;
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
  ulbn_limb_t* rp;
  if(an < bn) {
    _ulbn_swap_(const ulbi_t*, ao, bo);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }
  a_cy = (ao->len < 0);
  b_cy = (bo->len < 0);
  r_cy = a_cy ^ b_cy;
  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  rp[an] = ulbn_xor(rp, r_cy, _ulbi_limb(ao), an, a_cy, _ulbi_limb(bo), bn, b_cy);
  an = ulbn_normalize(rp, an + 1);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(!r_cy, an);
  return 0;
}
ULBN_PUBLIC int ulbi_com(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao) {
  ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_limb_t* rp;

  rp = _ulbi_res(alloc, ro, an + (ao->len >= 0));
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  if(ao->len >= 0) {
    rp[an] = ulbn_add1(rp, _ulbi_limb(ao), an, 1);
    an += (rp[an] != 0);
    ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
    ro->len = -ulbn_cast_ssize(an);
  } else {
    ulbn_sub1(rp, _ulbi_limb(ao), an, 1);
    an = ulbn_normalize(rp, an);
    ro->len = ulbn_cast_ssize(an);
  }
  return 0;
}

ul_static_assert(_ULBN_LIMB_BITS < _ULBN_LIMB_SIGNBIT, "ulbn_usize_t is too large");
ULBN_PRIVATE int _ulbi_sal(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbn_usize_t idx, const int shift) {
  const ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_usize_t rn;
  ulbn_limb_t* rp;

  if(an == 0) {
    ro->len = 0;
    return 0;
  }
  rn = an + idx;

  if(shift) {
    ULBN_RETURN_IF_SSIZE_COND(rn > ULBN_USIZE_LIMIT - 1, ULBN_ERR_EXCEED_RANGE);
    ++rn;
    rp = _ulbi_res(alloc, ro, rn);
    rp[rn - 1] = ulbn_shl(rp + idx, _ulbi_limb(ao), an, shift);
  } else {
    rp = _ulbi_res(alloc, ro, rn);
    ulbn_rcopy(rp + idx, _ulbi_limb(ao), an);
  }

  ulbn_fill0(rp, idx);
  rn = ulbn_normalize(rp, rn);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(ao->len >= 0, rn);
  return 0;
}
ULBN_PRIVATE int _ulbi_sar(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbn_usize_t idx, const int shift) {
  const int a_neg = ao->len < 0;
  const ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_usize_t rn;
  ulbn_usize_t i;
  ulbn_limb_t cy = 0;
  ulbn_limb_t* rp;
  const ulbn_limb_t* ap;

  if(an == 0) {
    ro->len = 0;
    return 0;
  }
  if(an <= idx) {
    if(a_neg) {
      rp = _ulbi_res(alloc, ro, 1u);
      ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
      rp[0] = 1;
    }
    ro->len = -a_neg;
    return 0;
  }

  rn = an - idx;
  rp = _ulbi_res(alloc, ro, rn + ul_static_cast(unsigned, a_neg));
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  ap = _ulbi_limb(ao);

  /* When right-shifting a negative number, we need to check if the bits being shifted out are non-zero.
    If any non-zero bits exist, we need to add 1. */
  if(a_neg)
    for(i = 0; i < idx; ++i)
      cy |= ap[i];

  if(shift)
    cy |= ulbn_shr(rp, ap + idx, rn, shift);
  else
    ulbn_fcopy(rp, ap + idx, rn);

  if(a_neg && cy)
    ulbn_add1(rp, rp, rn, 1);
  rn = ulbn_normalize(rp, rn);
  ro->len = _ulbn_to_ssize(!a_neg, rn);
  return 0;
}
ULBN_PUBLIC int ulbi_sal_usize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  const ulbn_usize_t idx = b / ULBN_LIMB_BITS;
  const int shift = ul_static_cast(int, b % ULBN_LIMB_BITS);
  return _ulbi_sal(alloc, ro, ao, idx, shift);
}
ULBN_PUBLIC int ulbi_sar_usize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  const ulbn_usize_t idx = b / ULBN_LIMB_BITS;
  const int shift = ul_static_cast(int, b % ULBN_LIMB_BITS);
  return _ulbi_sar(alloc, ro, ao, idx, shift);
}
ULBN_PUBLIC int ulbi_sal_ssize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t b) {
  return b >= 0 ? ulbi_sal_usize(alloc, ro, ao, _ulbn_from_pos_ssize(b))
                : ulbi_sar_usize(alloc, ro, ao, _ulbn_from_neg_ssize(b));
}
ULBN_PUBLIC int ulbi_sar_ssize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t b) {
  return b >= 0 ? ulbi_sar_usize(alloc, ro, ao, _ulbn_from_pos_ssize(b))
                : ulbi_sal_usize(alloc, ro, ao, _ulbn_from_neg_ssize(b));
}
ULBN_PUBLIC int ulbi_sal(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbn_usize_t idx;
  int shift;
  if(b->len >= 0) {
    shift = ulbn_to_bit_info(_ulbi_limb(b), ulbn_cast_usize(b->len), &idx);
    if(ul_unlikely(shift < 0 || idx > ULBN_SSIZE_LIMIT))
      return ULBN_ERR_EXCEED_RANGE;
    return _ulbi_sal(alloc, ro, ao, idx, shift);
  } else {
    shift = ulbn_to_bit_info(_ulbi_limb(b), ulbn_cast_usize(-b->len), &idx);
    if(ul_unlikely(shift < 0))
      return _ulbi_sar(alloc, ro, ao, ULBN_USIZE_MAX, shift);
    else
      return _ulbi_sar(alloc, ro, ao, idx, shift);
  }
}
ULBN_PUBLIC int ulbi_sar(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbn_usize_t idx;
  int shift;
  if(b->len >= 0) {
    shift = ulbn_to_bit_info(_ulbi_limb(b), ulbn_cast_usize(b->len), &idx);
    if(ul_unlikely(shift < 0))
      return _ulbi_sar(alloc, ro, ao, ULBN_USIZE_MAX, shift);
    else
      return _ulbi_sar(alloc, ro, ao, idx, shift);
  } else {
    shift = ulbn_to_bit_info(_ulbi_limb(b), ulbn_cast_usize(-b->len), &idx);
    if(ul_unlikely(shift < 0 || idx > ULBN_SSIZE_LIMIT))
      return ULBN_ERR_EXCEED_RANGE;
    return _ulbi_sal(alloc, ro, ao, idx, shift);
  }
}


ULBN_PRIVATE int _ulbi_testbit(const ulbi_t* o, ulbn_usize_t idx, int shift) {
  ulbn_assert(0 <= shift && ul_static_cast(unsigned, shift) < ULBN_LIMB_BITS);
  return (ulbn_limb(_ulbi_limb(o), _ulbn_abs_size(o->len), o->len < 0, idx) & ULBN_LIMB_SHL(1, shift)) != 0;
}
ULBN_PRIVATE int _ulbi_setbit(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t idx, int shift) {
  ulbn_usize_t n = _ulbn_abs_size(o->len);
  ulbn_limb_t* op;

  if(ul_likely(o->len >= 0)) {
    if(idx >= n) {
      op = _ulbi_res(alloc, o, idx + 1);
      ULBN_RETURN_IF_ALLOC_FAILED(op, ULBN_ERR_NOMEM);
      ulbn_fill0(op + n, idx - n);
      op[idx] = ULBN_LIMB_SHL(1, shift);
      ULBN_RETURN_IF_SSIZE_OVERFLOW(idx + 1, ULBN_ERR_EXCEED_RANGE);
      o->len = ulbn_cast_ssize(idx + 1);
    } else {
      op = _ulbi_limb(o);
      op[idx] |= ULBN_LIMB_SHL(1, shift);
    }
  } else {
    op = _ulbi_limb(o);
    ulbn_sub1(op + idx, op + idx, n - idx, ULBN_LIMB_SHL(1, shift));
    if(op[n - 1] == 0) {
      n = ulbn_normalize(op, n);
      o->len = -ulbn_cast_ssize(n);
    }
  }
  return 0;
}
ULBN_PRIVATE int _ulbi_resetbit(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t idx, int shift) {
  ulbn_usize_t n = _ulbn_abs_size(o->len);
  ulbn_limb_t* op;

  if(ul_likely(o->len >= 0)) {
    ulbn_assert(idx < n);
    op = _ulbi_limb(o);
    op[idx] &= ~ULBN_LIMB_SHL(1, shift);
    if(op[n - 1] == 0)
      n = ulbn_normalize(op, n - 1);
  } else {
    if(idx >= n) {
      op = _ulbi_res(alloc, o, idx + 1);
      ULBN_RETURN_IF_ALLOC_FAILED(op, ULBN_ERR_NOMEM);
      ulbn_fill0(op + n, idx - n);
      op[idx] = ULBN_LIMB_SHL(1, shift);
      n = idx + 1;
      ULBN_RETURN_IF_SSIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
    } else {
      op = _ulbi_res(alloc, o, n + 1);
      op[n] = ulbn_add1(op + idx, op + idx, n - idx, ULBN_LIMB_SHL(1, shift));
      if(op[n] != 0) {
        ++n;
        ULBN_RETURN_IF_SSIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
      }
    }
  }
  o->len = _ulbn_to_ssize(o->len >= 0, n);
  return 1;
}

ULBN_PUBLIC int ulbi_testbit_usize(const ulbi_t* o, ulbn_usize_t k) {
  return _ulbi_testbit(o, k / ULBN_LIMB_BITS, ul_static_cast(int, k % ULBN_LIMB_BITS));
}
ULBN_PUBLIC int ulbi_setbit_usize(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k) {
  ulbn_usize_t idx = k / ULBN_LIMB_BITS;
  int shift = ul_static_cast(int, k % ULBN_LIMB_BITS);
  return _ulbi_testbit(o, idx, shift) ? 1 : _ulbi_setbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_resetbit_usize(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k) {
  ulbn_usize_t idx = k / ULBN_LIMB_BITS;
  int shift = ul_static_cast(int, k % ULBN_LIMB_BITS);
  return !_ulbi_testbit(o, idx, shift) ? 0 : _ulbi_resetbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_combit_usize(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k) {
  ulbn_usize_t idx = k / ULBN_LIMB_BITS;
  int shift = ul_static_cast(int, k % ULBN_LIMB_BITS);
  return _ulbi_testbit(o, idx, shift) ? _ulbi_resetbit(alloc, o, idx, shift) : _ulbi_setbit(alloc, o, idx, shift);
}

ULBN_PUBLIC int ulbi_testbit(const ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limb(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return o->len >= 0 ? 0 : 1;
  return _ulbi_testbit(o, idx, shift);
}
ULBN_PUBLIC int ulbi_setbit(ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limb(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return o->len >= 0 ? ULBN_ERR_EXCEED_RANGE : 1;
  if(_ulbi_testbit(o, idx, shift))
    return 1;
  if(ul_unlikely(idx > ULBN_SSIZE_LIMIT - (o->len >= 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_setbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_resetbit(ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limb(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return o->len >= 0 ? 0 : ULBN_ERR_EXCEED_RANGE;
  if(!_ulbi_testbit(o, idx, shift))
    return 0;
  if(ul_unlikely(idx > ULBN_SSIZE_LIMIT - (o->len < 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_resetbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_combit(ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limb(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return ULBN_ERR_EXCEED_RANGE;
  if(ul_unlikely(idx > ULBN_SSIZE_LIMIT - 1))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_testbit(o, idx, shift) ? _ulbi_resetbit(alloc, o, idx, shift) : _ulbi_setbit(alloc, o, idx, shift);
}


ULBN_PRIVATE int _ulbi_as_uint(
  ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t idx, int shift, int need_com
) {
  const ulbn_usize_t n_desire = idx + (shift != 0);
  const ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_limb_t* rp;
  ulbn_usize_t rn;

  rn = _ulbn_min_(an, n_desire);
  if(!need_com) {
    const ulbn_limb_t* ap;
    rp = _ulbi_res(alloc, ro, rn);
    ULBN_RETURN_IF_ALLOC_COND(rn != 0 && rp == ul_nullptr, ULBN_ERR_NOMEM);
    ap = _ulbi_limb(ao);
    if(ap != rp)
      ulbn_copy(rp, ap, rn);
  } else {
    rp = _ulbi_res(alloc, ro, n_desire);
    ULBN_RETURN_IF_ALLOC_COND(n_desire != 0 && rp == ul_nullptr, ULBN_ERR_NOMEM);
    ulbn_com(rp, _ulbi_limb(ao), rn, 1);
    if(an < n_desire) {
      ulbn_fill1(rp + an, n_desire - an);
      goto fix_bits;
    }
  }

  if(an >= n_desire) {
  fix_bits:
    if(shift != 0)
      rp[idx] &= ULBN_LIMB_SHL(1, shift) - 1;
    rn = ulbn_normalize(rp, n_desire);
  }

  ULBN_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = ulbn_cast_ssize(rn);
  return 0;
}
ULBN_PRIVATE int _ulbi_as_int(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t idx, int shift) {
  const ulbn_limb_t* ap;
  int err, positive, need_com;

  positive = (_ulbi_testbit(ao, idx, shift) == 0);
  ap = _ulbi_limb(ao);
  if(ul_unlikely(!positive && idx < _ulbn_abs_size(ao->len))) {
    const ulbn_limb_t mask = ULBN_LIMB_SHL(1u, shift);
    if(ul_unlikely((ap[idx] & (ul_static_cast(ulbn_limb_t, mask << 1u) - 1u)) == mask) && ulbn_is0(ap, idx)) {
      ulbn_limb_t* rp;
      if(ul_unlikely(idx > ULBN_SSIZE_LIMIT - 1))
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
  if(ul_unlikely(need_com && idx > ULBN_SSIZE_LIMIT - (shift != 0)))
    return ULBN_ERR_EXCEED_RANGE;
  err = _ulbi_as_uint(alloc, ro, ao, idx, shift, positive ^ (ao->len >= 0));
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}

ULBN_PUBLIC int ulbi_as_uint_usize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  return _ulbi_as_uint(alloc, ro, ao, b / ULBN_LIMB_BITS, ul_static_cast(int, b % ULBN_LIMB_BITS), ao->len < 0);
}
ULBN_PUBLIC int ulbi_as_int_usize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  if(ul_unlikely(b == 0)) {
    ro->len = 0;
    return 0;
  }
  return _ulbi_as_int(alloc, ro, ao, (b - 1) / ULBN_LIMB_BITS, ul_static_cast(int, (b - 1) % ULBN_LIMB_BITS));
}

ULBN_PUBLIC int ulbi_as_uint(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbn_usize_t idx;
  int shift;
  if(b->len < 0)
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limb(b), ulbn_cast_usize(b->len), &idx);
  if(ul_unlikely(shift < 0)) {
    idx = ULBN_USIZE_MAX;
    shift = 0;
  }
  if(ul_unlikely(ao->len < 0 && idx > ULBN_SSIZE_LIMIT - (shift != 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_as_uint(alloc, ro, ao, idx, shift, ao->len < 0);
}
ULBN_PUBLIC int ulbi_as_int(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbn_usize_t idx;
  int shift;
  if(b->len < 0)
    return ULBN_ERR_EXCEED_RANGE;
  if(ul_unlikely(b->len == 0)) {
    ro->len = 0;
    return 0;
  }
  shift = ulbn_to_bit_info(_ulbi_limb(b), ulbn_cast_usize(b->len), &idx);
  if(ul_unlikely(shift < 0)) {
    idx = ULBN_USIZE_MAX;
    shift = 0;
  }
  if(shift == 0) {
    --idx;
    shift = ULBN_LIMB_BITS - 1;
  } else
    --shift;
  return _ulbi_as_int(alloc, ro, ao, idx, shift);
}


ULBN_PUBLIC int ulbi_is_2pow(const ulbi_t* o) {
  return ulbn_is_2pow(_ulbi_limb(o), _ulbn_abs_size(o->len));
}
ULBN_PUBLIC ulbn_usize_t ulbi_ctz_usize(const ulbi_t* ro, ulbn_usize_t* p_rh) {
  return ulbn_ctz(_ulbi_limb(ro), _ulbn_abs_size(ro->len), p_rh);
}
ULBN_PUBLIC ulbn_usize_t ulbi_cto_usize(const ulbi_t* ro, ulbn_usize_t* p_rh) {
  return ulbn_cto(_ulbi_limb(ro), _ulbn_abs_size(ro->len), p_rh);
}
ULBN_PUBLIC ulbn_usize_t ulbi_abs_popcount_usize(const ulbi_t* ro, ulbn_usize_t* p_rh) {
  return ulbn_popcount(_ulbi_limb(ro), _ulbn_abs_size(ro->len), p_rh);
}
ULBN_PUBLIC ulbn_usize_t ulbi_abs_bit_width_usize(const ulbi_t* ro, ulbn_usize_t* p_rh) {
  ulbn_usize_t n = _ulbn_abs_size(ro->len);
  if(n == 0) {
    if(p_rh)
      *p_rh = 0;
    return 0;
  } else
    return ulbn_bit_width(_ulbi_limb(ro), n, p_rh);
}

ULBN_PRIVATE int _ulbi_merge_usize2(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t h, ulbn_usize_t l) {
  ulbi_t tmp = ULBI_INIT;
  int err;

  err = ulbi_set_usize(alloc, dst, h);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  err = ulbi_sal_usize(alloc, dst, dst, sizeof(ulbn_usize_t) * CHAR_BIT);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);

  err = ulbi_set_usize(alloc, &tmp, l);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  err = ulbi_or(alloc, dst, dst, &tmp);
  ulbi_deinit(alloc, &tmp);
  return err;
}
ULBN_PUBLIC int ulbi_ctz(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro) {
  ulbn_usize_t l, h;
  l = ulbi_ctz_usize(ro, &h);
  return _ulbi_merge_usize2(alloc, dst, h, l);
}
ULBN_PUBLIC int ulbi_cto(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro) {
  ulbn_usize_t l, h;
  l = ulbi_cto_usize(ro, &h);
  return _ulbi_merge_usize2(alloc, dst, h, l);
}
ULBN_PUBLIC int ulbi_abs_popcount(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro) {
  ulbn_usize_t l, h;
  l = ulbi_abs_popcount_usize(ro, &h);
  return _ulbi_merge_usize2(alloc, dst, h, l);
}
ULBN_PUBLIC int ulbi_abs_bit_width(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro) {
  ulbn_usize_t l, h;
  l = ulbi_abs_bit_width_usize(ro, &h);
  return _ulbi_merge_usize2(alloc, dst, h, l);
}


ULBN_PUBLIC ulbn_limb_t ulbi_to_limb(const ulbi_t* src) {
  if(src->len == 0)
    return 0;
  return src->len > 0 ? _ulbi_limb(src)[0] : ul_static_cast(ulbn_limb_t, 0u - _ulbi_limb(src)[0]);
}
ULBN_PUBLIC ulbn_slimb_t ulbi_to_slimb(const ulbi_t* src) {
  union {
    ulbn_limb_t ul;
    ulbn_slimb_t sl;
  } u;
  u.ul = ulbi_to_limb(src);
  return u.sl;
}

ULBN_PRIVATE ulbn_ulong_t _ulbi_to_ulong(const ulbi_t* src) {
#if ULBN_LIMB_MAX >= ULBN_ULONG_MAX
  return src->len ? ul_static_cast(ulbn_ulong_t, _ulbi_limb(src)[0]) : 0u;
#else
  static ul_constexpr const ulbn_usize_t N_LIMIT =
    (sizeof(ulbn_ulong_t) * CHAR_BIT + ULBN_LIMB_BITS - 1) / ULBN_LIMB_BITS;
  ulbn_usize_t n = _ulbn_abs_size(src->len);
  const ulbn_limb_t* p = _ulbi_limb(src);
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
  ulbn_ulong_t x = _ulbi_to_ulong(src);
  return src->len >= 0 ? x : 0u - x;
}
ULBN_PUBLIC ulbn_slong_t ulbi_to_slong(const ulbi_t* src) {
  union {
    ulbn_ulong_t ul;
    ulbn_slong_t sl;
  } u;
  u.ul = ulbi_to_ulong(src);
  return u.sl;
}

ULBN_PRIVATE ulbn_usize_t _ulbi_to_usize(const ulbi_t* src) {
#if ULBN_LIMB_MAX >= ULBN_USIZE_MAX
  return src->len ? ul_static_cast(ulbn_usize_t, _ulbi_limb(src)[0]) : 0u;
#else
  static ul_constexpr const ulbn_usize_t N_LIMIT =
    (sizeof(ulbn_usize_t) * CHAR_BIT + ULBN_LIMB_BITS - 1) / ULBN_LIMB_BITS;
  ulbn_usize_t n = _ulbn_abs_size(src->len);
  const ulbn_limb_t* p = _ulbi_limb(src);
  ulbn_usize_t i;
  ulbn_usize_t r;

  if(n == 0)
    return 0u;
  n = _ulbn_min_(n, N_LIMIT);
  r = p[n - 1];
  for(i = n - 1; i > 0; --i)
    r = (r << ULBN_LIMB_BITS) | p[i - 1];
  return r;
#endif
}
ULBN_PUBLIC ulbn_usize_t ulbi_to_usize(const ulbi_t* src) {
  ulbn_usize_t x = _ulbi_to_usize(src);
  return src->len >= 0 ? x : 0u - x;
}
ULBN_PUBLIC ulbn_ssize_t ulbi_to_ssize(const ulbi_t* src) {
  union {
    ulbn_usize_t ul;
    ulbn_ssize_t sl;
  } u;
  u.ul = ulbi_to_usize(src);
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
  return _ulbi_limb(src)[0] < ULBN_LIMB_SIGNBIT;
#else
  if(src->len == 1)
    return _ulbi_limb(src)[0] < ULBN_LIMB_SIGNBIT;
  else
    return _ulbi_limb(src)[0] <= ULBN_LIMB_SIGNBIT;
#endif
}
ULBN_PUBLIC int ulbi_fit_ulong(const ulbi_t* src) {
  ulbn_usize_t h;
  return src->len >= 0 && ulbi_abs_bit_width_usize(src, &h) <= sizeof(ulbn_ulong_t) * CHAR_BIT && ul_likely(h == 0);
}
ULBN_PUBLIC int ulbi_fit_slong(const ulbi_t* src) {
  ulbn_usize_t h, l;
  l = ulbi_abs_bit_width_usize(src, &h);
  if(ul_unlikely(h != 0))
    return 0;
#if ULBN_SLONG_MIN == -ULBN_SLONG_MAX
  return l < sizeof(ulbn_slong_t) * CHAR_BIT;
#else
  if(ul_likely(l < sizeof(ulbn_slong_t) * CHAR_BIT))
    return 1;
  return l == sizeof(ulbn_slong_t) * CHAR_BIT && src->len < 0 && ulbi_is_2pow(src) != 0;
#endif
}
ULBN_PUBLIC int ulbi_fit_usize(const ulbi_t* src) {
  ulbn_usize_t h;
  return src->len >= 0 && ulbi_abs_bit_width_usize(src, &h) <= sizeof(ulbn_usize_t) * CHAR_BIT && ul_likely(h == 0);
}
ULBN_PUBLIC int ulbi_fit_ssize(const ulbi_t* src) {
  ulbn_usize_t h, l;
  l = ulbi_abs_bit_width_usize(src, &h);
  if(ul_unlikely(h != 0))
    return 0;
#if ULBN_SSIZE_MIN == -ULBN_SSIZE_MAX
  return l < sizeof(ulbn_ssize_t) * CHAR_BIT;
#else
  if(ul_likely(l < sizeof(ulbn_ssize_t) * CHAR_BIT))
    return 1;
  return l == sizeof(ulbn_ssize_t) * CHAR_BIT && src->len < 0 && ulbi_is_2pow(src) != 0;
#endif
}


ULBN_PRIVATE ulbn_limb_t _ulbi_tostr_base(int base, unsigned* pB_pow) {
#if ULBN_LIMB_MAX == 0xFFu
  static const ulbn_limb_t B_TABLE[] = {0x80, 0xF3, 0x40, 0x7D, 0xD8, 0x31, 0x40, 0x51, 0x64, 0x79, 0x90, 0xa9,
                                        0xC4, 0xE1, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
                                        0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20, 0x21, 0x22, 0x23, 0x24};
  static const unsigned B_pow[] = {7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1,
                                   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1};
  #define _ULBI_TOSTR_BASE_TABLE_DEFINED
#elif ULBN_LIMB_MAX == 0xFFFFu
  static const ulbn_limb_t B_TABLE[] = {0x8000, 0xE6A9, 0x4000, 0x3D09, 0xB640, 0x41A7, 0x8000, 0xE6A9, 0x2710,
                                        0x3931, 0x5100, 0x6F91, 0x9610, 0xC5C1, 0x1000, 0x1331, 0x16C8, 0x1ACB,
                                        0x1F40, 0x242D, 0x2998, 0x2F87, 0x3600, 0x3D09, 0x44A8, 0x4CE3, 0x55C0,
                                        0x5F45, 0x6978, 0x745F, 0x8000, 0x8C61, 0x9988, 0xA77B, 0xB640};
  static const unsigned B_pow[] = {15, 10, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3,
                                   3,  3,  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3};
  #define _ULBI_TOSTR_BASE_TABLE_DEFINED
#elif ULBN_LIMB_MAX == 0xFFFFFFFFu
  static const ulbn_limb_t B_TABLE[] = {0x80000000, 0xCFD41B91, 0x40000000, 0x48C27395, 0x81BF1000, 0x75DB9C97,
                                        0x40000000, 0xCFD41B91, 0x3B9ACA00, 0x8C8B6D2B, 0x19A10000, 0x309F1021,
                                        0x57F6C100, 0x98C29B81, 0x10000000, 0x18754571, 0x247DBC80, 0x3547667B,
                                        0x4C4B4000, 0x6B5A6E1D, 0x94ACE180, 0xCAF18367, 0x0B640000, 0x0E8D4A51,
                                        0x1269AE40, 0x17179149, 0x1CB91000, 0x23744899, 0x2B73A840, 0x34E63B41,
                                        0x40000000, 0x4CFA3CC1, 0x5C13D840, 0x6D91B519, 0x81BF1000};
  static const unsigned B_pow[] = {31, 20, 15, 13, 12, 11, 10, 10, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7,
                                   7,  7,  7,  7,  6,  6,  6,  6,  6, 6, 6, 6, 6, 6, 6, 6, 6};
  #define _ULBI_TOSTR_BASE_TABLE_DEFINED
#elif _ULBN_IS_64BIT(ULBN_LIMB_MAX)
  static const ulbn_limb_t B_TABLE[] = {0x8000000000000000, 0xA8B8B452291FE821, 0x4000000000000000, 0x6765C793FA10079D,
                                        0x41C21CB8E1000000, 0x3642798750226111, 0x8000000000000000, 0xA8B8B452291FE821,
                                        0x8AC7230489E80000, 0x4D28CB56C33FA539, 0x1ECA170C00000000, 0x780C7372621BD74D,
                                        0x1E39A5057D810000, 0x5B27AC993DF97701, 0x1000000000000000, 0x27B95E997E21D9F1,
                                        0x5DA0E1E53C5C8000, 0xD2AE3299C1C4AEDB, 0x16BCC41E90000000, 0x2D04B7FDD9C0EF49,
                                        0x5658597BCAA24000, 0xA0E2073737609371, 0x0C29E98000000000, 0x14ADF4B7320334B9,
                                        0x226ED36478BFA000, 0x383D9170B85FF80B, 0x5A3C23E39C000000, 0x8E65137388122BCD,
                                        0xDD41BB36D259E000, 0x0AEE5720EE830681, 0x1000000000000000, 0x172588AD4F5F0981,
                                        0x211E44F7D02C1000, 0x2EE56725F06E5C71, 0x41C21CB8E1000000};
  static const unsigned B_pow[] = {63, 40, 31, 27, 24, 22, 21, 20, 19, 18, 17, 17, 16, 16, 15, 15, 15, 15,
                                   14, 14, 14, 14, 13, 13, 13, 13, 13, 13, 13, 12, 12, 12, 12, 12, 12};
  #define _ULBI_TOSTR_BASE_TABLE_DEFINED
#endif

#ifdef _ULBI_TOSTR_BASE_TABLE_DEFINED
  *pB_pow = B_pow[base - 2];
  return B_TABLE[base - 2];
#else
  ulbn_limb_t B_guard, B;
  unsigned B_pow;
  B_guard = ul_static_cast(ulbn_limb_t, ULBN_LIMB_MAX / ul_static_cast(unsigned, base));
  B_pow = 1;
  for(B = ul_static_cast(ulbn_limb_t, base); B <= B_guard; B *= ul_static_cast(ulbn_limb_t, base))
    ++B_pow;
  *pB_pow = B_pow;
  return B;
#endif
}
ULBN_PUBLIC char* ulbi_tostr_alloc(
  ulbn_alloc_t* alloc, ulbn_usize_t* p_len,          /* */
  ulbn_alloc_func_t* alloc_func, void* alloc_opaque, /* */
  const ulbi_t* ao, int base                         /* */
) {
  const ulbn_usize_t an = _ulbn_abs_size(ao->len);
  const unsigned a_neg = ao->len < 0;
  char* buf = ul_nullptr;
  ulbn_limb_t* rp;

  ulbn_limb_t B;
  unsigned B_pow;

  ulbn_limb_t* cp = ul_nullptr;
  ulbn_usize_t ci, c_alloc = 0;
  ulbn_usize_t on = 0;

  if(base < 2 || base > 36)
    return ul_nullptr;
  if(an == 0) {
    buf = ul_reinterpret_cast(char*, alloc_func(alloc_opaque, ul_nullptr, 0, 2));
    ULBN_RETURN_IF_ALLOC_FAILED(buf, ul_nullptr);
    buf[0] = '0';
    buf[1] = 0;
    if(p_len)
      *p_len = 1;
    return buf;
  }

  rp = ulbn_allocT(ulbn_limb_t, alloc, an);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ul_nullptr);
  ulbn_copy(rp, _ulbi_limb(ao), an);

  B = _ulbi_tostr_base(base, &B_pow);
  ci = ulbn_convbase(alloc, &cp, &c_alloc, rp, an, B);
  ULBN_DO_IF_ALLOC_COND(ci == 0, { goto done; });

  on = ulbn_conv2str(ci, cp, ul_nullptr, 0, ul_static_cast(ulbn_limb_t, base), B_pow, ulbn_string_table(0));
  ULBN_DO_IF_ALLOC_COND(on == 0, { goto done; });
  buf = ul_reinterpret_cast(char*, alloc_func(alloc_opaque, ul_nullptr, 0, ul_static_cast(size_t, on) + 1 + a_neg));
  ULBN_DO_IF_ALLOC_COND(buf == ul_nullptr, { goto done; });
  if(ul_unlikely(a_neg))
    buf[0] = '-';
  ulbn_conv2str(ci, cp, buf + a_neg, on, ul_static_cast(ulbn_limb_t, base), B_pow, ulbn_string_table(0));
  on += a_neg;
  buf[on] = 0;

done:
  ulbn_deallocT(ulbn_limb_t, alloc, cp, c_alloc);
  ulbn_deallocT(ulbn_limb_t, alloc, rp, an);
  if(p_len)
    *p_len = on;
  return buf;
}
ULBN_PUBLIC int ulbi_print(ulbn_alloc_t* alloc, const ulbi_t* o, FILE* fp, int base) {
  char* str;
  ulbn_usize_t len;
  if(base < 2 || base > 36)
    return ULBN_ERR_EXCEED_RANGE;
  str = ulbi_tostr_alloc(alloc, &len, alloc->alloc_func, alloc->alloc_opaque, o, base);
  ULBN_RETURN_IF_ALLOC_FAILED(str, ULBN_ERR_NOMEM);
  fwrite(str, 1, len, fp);
  ulbn_deallocT(char, alloc, str, len + 1);
  return 0;
}


#if ULBN_CONF_HAS_DOUBLE
ULBN_PRIVATE int _ulbn_feq(double a, double b) {
  return a >= b && a <= b;
}
ULBN_PUBLIC int ulbi_set_double(ulbn_alloc_t* alloc, ulbi_t* dst, double x) {
  static ul_constexpr const double B = ul_static_cast(double, _ULBN_LIMB_SIGNBIT) * 2.0;
  static ul_constexpr const double Bi = 1.0 / (ul_static_cast(double, _ULBN_LIMB_SIGNBIT) * 2.0);
  ulbn_ssize_t ri, rn;
  ulbn_limb_t* rp;
  double xl;
  int positive;

  /* NaN, +Inf, -Inf or 0 */
  if(x != x || _ulbn_feq(x, x * 0.5)) {
    dst->len = 0;
    return _ulbn_feq(x, 0.0) ? 0 : ULBN_ERR_INVALID;
  }
  positive = x >= 0.0;
  if(!positive)
    x = -x;
  if(x < 1.0) {
    dst->len = 0;
    return ULBN_ERR_INEXACT;
  }
  for(rn = 1; x >= B; ++rn)
    x *= Bi;

  rp = _ulbi_res(alloc, dst, ulbn_cast_usize(rn));
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  for(ri = rn - 1; ri >= 0; --ri) {
    xl = floor(x);
    x -= xl;
    rp[ri] = ul_static_cast(ulbn_limb_t, xl);
    x = B * x;
  }
  dst->len = positive ? rn : -rn;
  return x <= 0 ? 0 : ULBN_ERR_INEXACT;
}
ULBN_PUBLIC int ulbi_init_double(ulbn_alloc_t* alloc, ulbi_t* dst, double x) {
  return ulbi_set_double(alloc, ulbi_init(dst), x);
}
ULBN_PUBLIC double ulbi_to_double(const ulbi_t* src) {
  static ul_constexpr const double B = ul_static_cast(double, _ULBN_LIMB_SIGNBIT) * 2.0;
  const ulbn_usize_t n = _ulbn_abs_size(src->len);
  ulbn_limb_t* p = _ulbi_limb(src);
  double r;
  ulbn_usize_t i = n;

  if(n == 0)
    return 0.0;
  r = ul_static_cast(double, p[--i]);
  while(i > 0)
    r = r * B + ul_static_cast(double, p[--i]);
  return src->len >= 0 ? r : -r;
}
  #include <float.h>
ULBN_PUBLIC int ulbi_fit_double(const ulbi_t* src) {
  ulbn_usize_t bitwidth, bitwidth_h;
  ulbn_usize_t ctz, ctz_h;

  bitwidth = ulbi_abs_bit_width_usize(src, &bitwidth_h);
  ctz = ulbi_ctz_usize(src, &ctz_h);

  #if ULBN_USIZE_MAX > DBL_MAX_EXP
  if(ul_unlikely(bitwidth_h != 0))
    return 0;
  if(bitwidth > DBL_MAX_EXP)
    return 0;
  #else
    #error "todo"
  #endif

  bitwidth_h -= ctz_h + (bitwidth < ctz);
  bitwidth -= ctz;

  #if ULBN_USIZE_MAX > DBL_MANT_DIG
  if(ul_unlikely(bitwidth_h != 0))
    return 0;
  if(bitwidth > DBL_MANT_DIG)
    return 0;
  #else
    #error "todo"
  #endif

  return 1;
}
#endif /* ULBN_CONF_HAS_DOUBLE */


ULBN_PRIVATE int _ulbi_set_rand(
  ulbn_alloc_t* alloc, ulbn_rand_t* rng,   /* */
  ulbi_t* dst, ulbn_usize_t idx, int shift /* */
) {
  ulbn_usize_t n = idx + (shift != 0);
  ulbn_limb_t* p;
  if(ul_unlikely(n == 0)) {
    dst->len = 0;
    return 0;
  }

  p = _ulbi_res(alloc, dst, n);
  ULBN_RETURN_IF_ALLOC_FAILED(p, ULBN_ERR_NOMEM);
  ulbn_rand_multi(rng, p, idx);
  if(shift != 0)
    p[idx] = ulbn_rand(rng, shift);
  n = ulbn_normalize(p, n);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
  dst->len = ulbn_cast_ssize(n);
  return 0;
}
ULBN_PUBLIC int ulbi_set_rand_usize(ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_usize_t n) {
  ulbn_usize_t idx = n / ULBN_LIMB_BITS;
  const int shift = ul_static_cast(int, n % ULBN_LIMB_BITS);
  return _ulbi_set_rand(alloc, rng, dst, idx, shift);
}
ULBN_PUBLIC int ulbi_set_rand(ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* n) {
  ulbn_usize_t idx;
  int shift;
  if(ul_unlikely(n->len < 0))
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limb(n), ulbn_cast_usize(n->len), &idx);
  if(ul_unlikely(shift < 0 || idx > ULBN_SSIZE_LIMIT - (shift != 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_set_rand(alloc, rng, dst, idx, shift);
}
ULBN_PUBLIC int ulbi_init_rand_usize(ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_usize_t n) {
  return ulbi_set_rand_usize(alloc, rng, ulbi_init(dst), n);
}
ULBN_PUBLIC int ulbi_init_rand(ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* n) {
  return ulbi_set_rand(alloc, rng, ulbi_init(dst), n);
}

ULBN_PUBLIC int ulbi_set_rand_range(ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* limit) {
  ulbi_t nbits = ULBI_INIT;
  ulbi_t threshold = ULBI_INIT;
  ulbi_t tlimit = ULBI_INIT;
  int err;

  if(ul_unlikely(limit->len <= 0)) {
    dst->len = 0;
    return ULBN_ERR_EXCEED_RANGE;
  }
  err = ulbi_abs_bit_width(alloc, &nbits, limit);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  if(ulbi_is_2pow(limit)) {
    err = ulbi_sub_limb(alloc, &nbits, &nbits, 1);
    ulbn_assert(err == 0);
    err = ulbi_set_rand(alloc, rng, dst, &nbits);
    goto cleanup;
  }

  err = ulbi_set_2exp(alloc, &threshold, &nbits);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  err = ulbi_sub(alloc, &threshold, &threshold, limit);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  ulbn_assert(threshold.len >= 0);
  err = ulbi_mod(alloc, &threshold, &threshold, limit);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);

  if(ul_unlikely(dst == limit)) {
    err = ulbi_set_copy(alloc, &tlimit, limit);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    limit = &tlimit;
  }

  do {
    err = ulbi_set_rand(alloc, rng, dst, &nbits);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  } while(ulbi_comp(dst, &threshold) < 0);
  err = ulbi_mod(alloc, dst, dst, limit);
cleanup:
  ulbi_deinit(alloc, &nbits);
  ulbi_deinit(alloc, &threshold);
  ulbi_deinit(alloc, &tlimit);
  return err;
}
ULBN_PUBLIC int ulbi_set_rand_range2(
  ulbn_alloc_t* alloc, ulbn_rand_t* rng,          /* */
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
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  if(ul_unlikely(lo == dst)) {
    err = ulbi_set_copy(alloc, &tlo, lo);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    lo = &tlo;
  }

  err = ulbi_set_rand_range(alloc, rng, dst, &limit);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  err = ulbi_add(alloc, dst, dst, lo);

cleanup:
  ulbi_deinit(alloc, &limit);
  ulbi_deinit(alloc, &tlo);
  return err;
}
ULBN_PUBLIC int ulbi_init_rand_range(ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* limit) {
  return ulbi_set_rand_range(alloc, rng, ulbi_init(dst), limit);
}
ULBN_PUBLIC int ulbi_init_rand_range2(
  ulbn_alloc_t* alloc, ulbn_rand_t* rng,          /* */
  ulbi_t* dst, const ulbi_t* lo, const ulbi_t* hi /* */
) {
  return ulbi_set_rand_range2(alloc, rng, ulbi_init(dst), lo, hi);
}

ULBN_PUBLIC int ulbi_gcd(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  ulbn_limb_t *ap, *bp;
  ulbn_usize_t an, bn;

  an = _ulbn_abs_size(ao->len);
  bn = _ulbn_abs_size(bo->len);
  if(ul_unlikely(an == 0))
    return ulbi_abs(alloc, ro, bo);
  if(ul_unlikely(bn == 0))
    return ulbi_abs(alloc, ro, ao);

  ap = _ulbi_res(alloc, ro, an);
  ULBN_RETURN_IF_ALLOC_FAILED(ap, ULBN_ERR_NOMEM);
  if(ro != ao)
    ulbn_copy(ap, _ulbi_limb(ao), an);

  bp = ulbn_allocT(ulbn_limb_t, alloc, bn);
  ULBN_RETURN_IF_ALLOC_FAILED(bp, ULBN_ERR_NOMEM);
  ulbn_copy(bp, _ulbi_limb(bo), bn);

  ro->len = ulbn_cast_ssize(ulbn_gcd(ap, an, bp, bn));
  ulbn_deallocT(ulbn_limb_t, alloc, bp, bn);
  return 0;
}
ULBN_PUBLIC int ulbi_gcd_limb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  ulbn_limb_t* ap;
  ulbn_usize_t an;

  an = _ulbn_abs_size(ao->len);
  if(ul_unlikely(an == 0))
    return ulbi_set_limb(alloc, ro, b);
  if(ul_unlikely(b == 0))
    return ulbi_abs(alloc, ro, ao);

  ap = _ulbi_res(alloc, ro, an);
  ULBN_RETURN_IF_ALLOC_FAILED(ap, ULBN_ERR_NOMEM);
  if(ro != ao)
    ulbn_copy(ap, _ulbi_limb(ao), an);

  ro->len = ulbn_cast_ssize(ulbn_gcd(ap, an, &b, 1));
  return 0;
}
ULBN_PUBLIC int ulbi_gcd_slimb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  if(b >= 0)
    return ulbi_gcd_limb(alloc, ro, ao, _ulbn_from_pos_slimb(b));
  else
    return ulbi_gcd_limb(alloc, ro, ao, _ulbn_from_neg_slimb(b));
}
ULBN_PUBLIC int ulbi_lcm(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  int err;
  err = ulbi_gcd(alloc, ro, ao, bo);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  /* if `a` and `b` are both 0, `ulbi_div` will return `ULBN_ERR_DIV_BY_ZERO`, and set `r` to 0 */
  err = ulbi_div(alloc, ro, ao, ro);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  err = ulbi_mul(alloc, ro, ro, bo);
  ro->len = _ulbn_abs_(ro->len);
  return err;
}
