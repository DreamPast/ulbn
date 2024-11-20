#ifndef ULBN_SOURCE
#define ULBN_SOURCE

#ifndef ULBN_HEADER
  #include "ulbn.h"
#endif
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>


#ifndef ulbn_assert
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

#define ulbn_safe_forward_overlap(d, dn, s, sn) ((d) <= (s) || (d) >= (s) + (sn))
#define ulbn_safe_backward_overlap(d, dn, s, sn) ((d) + (dn) <= (s) || ((d) >= (s) && (d) + (dn) >= (s) + (sn)))
#define ulbn_safe_overlap(d, dn, s, sn) ((d) + (dn) <= (s) || (s) + (sn) <= (d))

#define ulbn_assert_forward_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_forward_overlap(d, dn, s, sn))
#define ulbn_assert_backward_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_backward_overlap(d, dn, s, sn))
#define ulbn_assert_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_overlap(d, dn, s, sn))
#define ulbn_assert_same_or_not_overlap(d, dn, s, sn) \
  ulbn_assert((d) == ul_nullptr || (s) == ul_nullptr || (s) == (d) || ulbn_safe_overlap(d, dn, s, sn))


/* check if `x` is 64-bit integer */
#if defined(ULONG_MAX) && (ULONG_MAX >> 63) == 1
  #define _ULBN_IS_64BIT(x) ((x) == 0xFFFFFFFFFFFFFFFFul)
#elif defined(ULLONG_MAX) && (ULLONG_MAX >> 63) == 1
  #define _ULBN_IS_64BIT(x) ((x) == 0xFFFFFFFFFFFFFFFFull)
#else
  #define _ULBN_IS_64BIT(x) (0)
#endif /* _ULBN_IS_64BIT */

#if 0 != (CHAR_BIT & 1)
  #error "ulbn: CHAR_BIT must be even"
#endif

#define _ULBN_LIMB_BITS (sizeof(ulbn_limb_t) * CHAR_BIT)
#define _ULBN_LIMB_HALF_BITS (_ULBN_LIMB_BITS >> 1)
#define ULBN_LIMB_SHL(val, shift) ul_static_cast(ulbn_limb_t, ul_static_cast(ulbn_limb_t, val) << (shift))
#define _ULBN_LIMB_SIGNBIT (ULBN_LIMB_SHL(1, _ULBN_LIMB_BITS - 1))
#define _ULBN_LOWMASK ul_static_cast(ulbn_limb_t, ULBN_LIMB_SHL(1, _ULBN_LIMB_HALF_BITS) - 1u)
#define ULBN_LOWPART(x) ul_static_cast(ulbn_limb_t, (x) & ULBN_LOWMASK)
#define ULBN_HIGHPART(x) ul_static_cast(ulbn_limb_t, (x) >> ULBN_LIMB_HALF_BITS)

static ul_constexpr const ulbn_usize_t ULBN_LIMB_BITS = _ULBN_LIMB_BITS;
static ul_constexpr const size_t ULBN_LIMB_HALF_BITS = _ULBN_LIMB_HALF_BITS;
static ul_constexpr const ulbn_limb_t ULBN_LIMB_SIGNBIT = _ULBN_LIMB_SIGNBIT;
static ul_constexpr const ulbn_limb_t ULBN_LOWMASK = _ULBN_LOWMASK;

#define _ulbn_from_pos_slimb(v) ul_static_cast(ulbn_limb_t, v)
#define _ulbn_from_neg_slimb(v) ul_static_cast(ulbn_limb_t, ul_static_cast(ulbn_limb_t, -(v + 1)) + 1u)


#define _ULBN_SIZET_MAX ul_static_cast(size_t, ~ul_static_cast(size_t, 0))
#define _ULBN_ALLOC_LIMIT ul_static_cast(size_t, _ULBN_SIZET_MAX / sizeof(ulbn_limb_t))
/* The limitation of ulbn_usize_t, mainly to avoid overflow caused by the multiplication of ulbn_usize_t */
#define _ULBN_SSIZE_LIMIT ulbn_cast_usize(_ulbn_min_(_ULBN_USIZE_LIMIT / 2, ulbn_cast_usize(ULBN_SSIZE_MAX)))
#define _ULBN_USIZE_SHIFT_MASK ulbn_cast_usize(_ULBN_USIZE_SIGNBIT - 1u)

ul_static_assert(sizeof(size_t) >= sizeof(ulbn_usize_t), "usbn_usize_t cannot be larger than size_t");
ul_static_assert(ULBN_SHORT_LIMB_SIZE >= 1, "ULBN_SHORT_LIMB_SIZE is too small, must be at least 1");

static ul_constexpr const size_t ULBN_ALLOC_LIMIT = _ULBN_ALLOC_LIMIT;
static ul_constexpr const size_t ULBN_USIZE_LIMIT = _ULBN_USIZE_LIMIT;
static ul_constexpr const ulbn_usize_t ULBN_SSIZE_LIMIT = _ULBN_SSIZE_LIMIT;
static ul_constexpr const ulbn_usize_t ULBN_SHORT_LIMB_SIZE_VAL = ULBN_SHORT_LIMB_SIZE;

#define _ulbn_abs_size(n) ulbn_cast_usize((n) < 0 ? -(n) : (n))
#define _ulbn_to_ssize(pos, n) ((pos) ? ulbn_cast_ssize(n) : -ulbn_cast_ssize(n))
#define _ulbn_from_pos_ssize(v) ul_static_cast(ulbn_usize_t, v)
#define _ulbn_from_neg_ssize(v) ul_static_cast(ulbn_usize_t, ul_static_cast(ulbn_usize_t, -(v + 1)) + 1u)


#define _ulbn_from_pos_slong(v) ul_static_cast(ulbn_ulong_t, v)
#define _ulbn_from_neg_slong(v) ul_static_cast(ulbn_ulong_t, ul_static_cast(ulbn_ulong_t, -(v + 1)) + 1u)


#ifndef ULBN_CHECK_USIZE_OVERFLOW
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

#define ULBN_DO_IF_PUBLIC_COND(cond, expr) \
  if(ul_unlikely(cond))                    \
  expr((void)0)
#define ULBN_RETURN_IF_PUBLIC_COND(cond, ret) \
  if(ul_unlikely(cond))                       \
  return (ret)


#ifdef __cplusplus
extern "C" {
#endif


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
  static const ulbn_limb_t MASK8 = ULBN_LIMB_SHL(0xFF, _ULBN_LIMB_BITS - 8);
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

#define _ulbn_swap_(T, a, b) \
  do {                       \
    T __swap_tmp = (a);      \
    (a) = (b);               \
    (b) = __swap_tmp;        \
  } while(0)

#define _ulbn_same_sign(a, b) (((a) ^ (b)) >= 0)
#define _ulbn_abs_(a) ((a) >= 0 ? (a) : -(a))
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
  #define _ulbn_umul_(p1, p0, u, v)                                                             \
    do {                                                                                        \
      ulbn_limb2_t __p = ul_static_cast(ulbn_limb2_t, ul_static_cast(ulbn_limb2_t, (u)) * (v)); \
      (p1) = ul_static_cast(ulbn_limb_t, (__p) >> ULBN_LIMB_BITS);                              \
      (p0) = ul_static_cast(ulbn_limb_t, (__p));                                                \
    } while(0)
  #define _ulbn_udiv_(q, r, n1, n0, d)                                                                                \
    do {                                                                                                              \
      ulbn_limb2_t __n = ul_static_cast(ulbn_limb2_t, (ul_static_cast(ulbn_limb2_t, (n1)) << ULBN_LIMB_BITS) | (n0)); \
      (r) = ul_static_cast(ulbn_limb_t, __n % (d));                                                                   \
      (q) = ul_static_cast(ulbn_limb_t, __n / (d));                                                                   \
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
  return ulbn_fnorm(p, n) >= n;
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

#define _ULBN_MERGE_USIZE_LEN ((sizeof(ulbn_usize_t) * 2 + sizeof(ulbn_limb_t) - 1) / sizeof(ulbn_limb_t))
static ul_constexpr const ulbn_usize_t ULBN_MERGE_USIZE_LEN = _ULBN_MERGE_USIZE_LEN;
ULBN_INTERNAL ulbn_usize_t ulbn_merge_usize(ulbn_limb_t* buf, ulbn_usize_t rl, ulbn_usize_t rh) {
#if ULBN_USIZE_MAX == ULBN_LIMB_MAX
  buf[1] = rh;
  buf[0] = rl;
  return rh != 0 ? 2 : (rl != 0);
#elif ULBN_USIZE_MAX / ULBN_LIMB_MAX >= ULBN_LIMB_MAX \
  && ULBN_USIZE_MAX - ULBN_LIMB_MAX * ULBN_LIMB_MAX == 2u * ULBN_LIMB_MAX
  buf[3] = ul_static_cast(ulbn_limb_t, rh >> ULBN_LIMB_BITS);
  buf[2] = ul_static_cast(ulbn_limb_t, rh & ULBN_LIMB_MAX);
  buf[1] = ul_static_cast(ulbn_limb_t, rl >> ULBN_LIMB_BITS);
  buf[0] = ul_static_cast(ulbn_limb_t, rl & ULBN_LIMB_MAX);
  return ulbn_rnorm(buf, 4);
#elif ULBN_LIMB_MAX / ULBN_USIZE_MAX >= ULBN_USIZE_MAX \
  && ULBN_LIMB_MAX - ULBN_USIZE_MAX * ULBN_USIZE_MAX >= 2u * ULBN_USIZE_MAX
  buf[0] = ul_static_cast(ulbn_limb_t, rh) << (sizeof(ulbn_usize_t) * CHAR_BIT) | ul_static_cast(ulbn_limb_t, rl);
  return buf[0] != 0;
#else
  static ul_constexpr const ulbn_usize_t idx = sizeof(ulbn_usize_t) * CHAR_BIT / _ULBN_LIMB_BITS;
  static ul_constexpr const int shift = sizeof(ulbn_usize_t) * CHAR_BIT % _ULBN_LIMB_BITS;
  ulbn_usize_t len = 0;

  #if ULBN_USIZE_MAX <= ULBN_LIMB_MAX
  buf[len++] = ul_static_cast(ulbn_limb_t, rh);
  #else
  do {
    buf[len++] = ul_static_cast(ulbn_limb_t, rh);
    rh >>= ULBN_LIMB_BITS;
  } while(rh);
  #endif

  if(shift) {
    buf[idx + len] = ulbn_shl(buf + idx, buf, len, shift);
    len += idx + 1u;
  } else {
    ulbn_rcopy(buf + idx, buf, len);
    len += idx;
  }
  ulbn_fill0(buf, idx);

  #if ULBN_USIZE_MAX <= ULBN_LIMB_MAX
  buf[0] |= ul_static_cast(ulbn_limb_t, rl);
  #else
  do {
    ulbn_usize_t i = 0;
    do {
      buf[i++] |= ul_static_cast(ulbn_limb_t, rl);
      rl >>= ULBN_LIMB_BITS;
    } while(rl);
  } while(0);
  #endif

  return ulbn_rnorm(buf, len);
#endif
}


static const char _ULBN_UPPER_TABLE[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
#if 0
ul_unused ULBN_INTERNAL void ulbn_dumplimb(FILE* fp, ulbn_limb_t l) {
  size_t j = sizeof(l) * CHAR_BIT / 4;
  while(j--)
    putc(_ULBN_UPPER_TABLE[(l >> (j << 2)) & 0xF], fp);
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

/* Compare ap[0:n] and (bp[0:bn] << b), return direction (<0 means less than, =0 means equal, >0 means greater) */
ULBN_INTERNAL int ulbn_cmpshl(const ulbn_limb_t* ap, ulbn_usize_t an, const ulbn_limb_t* bp, ulbn_usize_t bn, int b) {
  const int br = ul_static_cast(int, _ULBN_LIMB_BITS) - b;
  ulbn_limb_t bh, bl;
  ulbn_limb_t a0;
  ulbn_usize_t i;

  ulbn_assert(0 < b && ul_static_cast(size_t, b) < ULBN_LIMB_BITS);

  if(an < bn)
    return -1;
  if(an - bn > 1)
    return 1;

  a0 = (an == bn ? 0 : ap[bn]);
  bl = bp[bn - 1];
  bh = bl >> br;
  if(bh != a0)
    return a0 < bh ? -1 : 1;
  bh = ul_static_cast(ulbn_limb_t, bl << b);
  for(i = bn - 1; i > 0; --i) {
    bl = bp[i - 1];
    bh |= bl >> br;
    if(bh != ap[i])
      return ap[i] < bh ? -1 : 1;
    bh = ul_static_cast(ulbn_limb_t, bl << b);
  }
  if(bh == ap[0])
    return 0;
  return ap[0] < bh ? -1 : 1;
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

  /* ulbn_assert(ulbn_cmp(ap, ulbn_rnorm(ap, an), bp, ulbn_rnorm(bp, bn)) >= 0); */
  ulbn_assert_forward_overlap(rp, an, ap, an);
  ulbn_assert_forward_overlap(rp, an, bp, bn);

  cy = ulbn_subn(rp, ap, bp, bn);
  return ulbn_sub1(rp + bn, ap + bn, an - bn, cy);
}


/* rp[0:n] = ap[0:n] + (bp[0:n] << b), return overflow part (do not write to rp[n]), ensure 0 < b < {ULBN_LIMB_BITS} */
ULBN_INTERNAL ulbn_limb_t ulbn_addshln(
  ulbn_limb_t* rp, const ulbn_limb_t* ap,      /* */
  const ulbn_limb_t* bp, ulbn_usize_t n, int b /* */
) {
  ulbn_usize_t i;
  ulbn_limb_t bl, r, limb = 0, cy = 0;
  const int br = ul_static_cast(int, ULBN_LIMB_BITS) - b;

  ulbn_assert(n > 0);
  ulbn_assert(0 < b && ul_static_cast(unsigned, b) < ULBN_LIMB_BITS);
  ulbn_assert_forward_overlap(rp, n, bp, n);

  for(i = 0; i < n; ++i) {
    bl = bp[i];
    limb |= bl << b;
    cy = ((r = ap[i] + cy) < cy);
    cy += ((r += limb) < limb);
    ulbn_assert(cy <= 1u);
    rp[i] = r;
    limb = bl >> br;
  }
  return limb + cy;
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
  const int br = ul_static_cast(int, ULBN_LIMB_BITS) - b;

  ulbn_assert(n > 0);
  ulbn_assert(0 < b && ul_static_cast(unsigned, b) < ULBN_LIMB_BITS);
  ulbn_assert_forward_overlap(rp, n, bp, n);

  for(i = 0; i < n; ++i) {
    bl = bp[i];
    limb |= bl << b;
    cy = ((limb += cy) < cy);
    cy += (ap[i] < limb);
    ulbn_assert(cy <= 1u);
    rp[i] = ap[i] - limb;
    limb = bl >> br;
  }
  return limb + cy;
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
#define _ULBN_TOOM_3_THRESHOLD 1024

#define _ULBN_TOOM_1_MIN_THRESHOLD 2
#define _ULBN_TOOM_2_MIN_THRESHOLD 4
#define _ULBN_TOOM_3_MIN_THRESHOLD 9
#if _ULBN_TOOM_1_THRESHOLD < _ULBN_TOOM_1_MIN_THRESHOLD
  #error "ulbn: toom-2 and toom-1.5 thresholds must be at least 2"
#endif
#if _ULBN_TOOM_2_THRESHOLD < _ULBN_TOOM_2_MIN_THRESHOLD
  #error "ulbn: toom-3 and toom-2.5 thresholds must be at least 4"
#endif
#if _ULBN_TOOM_3_THRESHOLD < _ULBN_TOOM_3_MIN_THRESHOLD
  #error "ulbn: toom-4 and toom-3.5 thresholds must be at least 9"
#endif

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
#ifdef __cplusplus
  #define ulbn_may_static static
#else
  #define ulbn_may_static
#endif

static ulbn_limb_t _ULBN_SHORT_DIV_R; /* write-only variable */
ULBN_PRIVATE void _ulbn_divby3(ulbn_limb_t* qp, const ulbn_limb_t* ap, ulbn_usize_t an, int dshift) {
#ifdef _ULBN_DEF_SHORT_DIV
  static ul_constexpr const int SHIFT = ul_static_cast(int, _ULBN_LIMB_BITS) - 2;
  static ul_constexpr const ulbn_limb_t NORM = _ULBN_DEF_SHORT_DIV(C, 0, 0, 0);
  static ul_constexpr const ulbn_limb_t INV = _ULBN_DEF_SHORT_DIV(5, 5, 5, 5);
#else
  ulbn_may_static const int SHIFT = _ulbn_clz_(3);
  ulbn_may_static const ulbn_limb_t NORM = ULBN_LIMB_SHL(3, SHIFT);
  ulbn_may_static const ulbn_limb_t INV = _ulbn_divinv1(NORM);
#endif
  ulbn_divmod_inv1(qp, &_ULBN_SHORT_DIV_R, ap, an, NORM, INV, SHIFT - dshift);
}
#if 0
ULBN_PRIVATE void _ulbn_divby5(ulbn_limb_t* qp, const ulbn_limb_t* ap, ulbn_usize_t an, int dshift) {
  #ifdef _ULBN_DEF_SHORT_DIV
  static ul_constexpr const int SHIFT = ul_static_cast(int, ULBN_LIMB_BITS) - 3;
  static ul_constexpr const ulbn_limb_t NORM = _ULBN_DEF_SHORT_DIV(A, 0, 0, 0);
  static ul_constexpr const ulbn_limb_t INV = _ULBN_DEF_SHORT_DIV(9, 9, 9, 9);
  #else
  ulbn_may_static const int SHIFT = _ulbn_clz_(5);
  ulbn_may_static const ulbn_limb_t NORM = ULBN_LIMB_SHL(5, SHIFT);
  ulbn_may_static const ulbn_limb_t INV = _ulbn_divinv1(NORM);
  #endif
  ulbn_divmod_inv1(qp, &_ULBN_SHORT_DIV_R, ap, an, NORM, INV, SHIFT - dshift);
}
#endif
ULBN_PRIVATE void _ulbn_divby9(ulbn_limb_t* qp, const ulbn_limb_t* ap, ulbn_usize_t an, int dshift) {
#ifdef _ULBN_DEF_SHORT_DIV
  static ul_constexpr const int SHIFT = ul_static_cast(int, _ULBN_LIMB_BITS) - 4;
  static ul_constexpr const ulbn_limb_t NORM = _ULBN_DEF_SHORT_DIV(9, 0, 0, 0);
  static ul_constexpr const ulbn_limb_t INV = _ULBN_DEF_SHORT_DIV(C, 7, 1, C);
#else
  ulbn_may_static const int SHIFT = _ulbn_clz_(15);
  ulbn_may_static const ulbn_limb_t NORM = ULBN_LIMB_SHL(15, SHIFT);
  ulbn_may_static const ulbn_limb_t INV = _ulbn_divinv1(NORM);
#endif
  ulbn_divmod_inv1(qp, &_ULBN_SHORT_DIV_R, ap, an, NORM, INV, SHIFT - dshift);
}
ULBN_PRIVATE void _ulbn_divby15(ulbn_limb_t* qp, const ulbn_limb_t* ap, ulbn_usize_t an, int dshift) {
#ifdef _ULBN_DEF_SHORT_DIV
  static ul_constexpr const int SHIFT = ul_static_cast(int, _ULBN_LIMB_BITS) - 4;
  static ul_constexpr const ulbn_limb_t NORM = _ULBN_DEF_SHORT_DIV(F, 0, 0, 0);
  static ul_constexpr const ulbn_limb_t INV = _ULBN_DEF_SHORT_DIV(1, 1, 1, 1);
#else
  ulbn_may_static const int SHIFT = _ulbn_clz_(15);
  ulbn_may_static const ulbn_limb_t NORM = ULBN_LIMB_SHL(15, SHIFT);
  ulbn_may_static const ulbn_limb_t INV = _ulbn_divinv1(NORM);
#endif
  ulbn_divmod_inv1(qp, &_ULBN_SHORT_DIV_R, ap, an, NORM, INV, SHIFT - dshift);
}
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
  ulbn_sub(zp, zp, nz, rp, (m << 1) - (rp[(m << 1) - 1] == 0));
  /* `zp[0:nz]` -= z2 */
  ulbn_sub(zp, zp, nz, rp + (m << 1), an + bn - (rp[an + bn - 1] == 0) - (m << 1));
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

  const ulbn_usize_t m2 = m << 1, am = an - m2, bm = bn - m, abm = am + bm;
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
  rp[m] = t1[m] + ulbn_add(rp, t1, m, a1, m);
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

  const ulbn_usize_t m2 = m << 1, am = an - m2, bm = bn - m2, abm = am + bm;
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
  vm1[m] = t1[m] + ulbn_add(vm1, t1, m, a0, m);
  /* t2 = b1 + b2 */
  t2[m] = ulbn_add(t2, b1, m, b2, bm);
  /* v2 = t2 + b0 = b0 + b1 + b2 */
  v2[m] = t2[m] + ulbn_add(v2, t2, m, b0, m);
  /* v1 = vm1 * v2 = (a0 + a1 + a2) * (b0 + b1 + b2) */
  ulbn_mul(alloc, v1, vm1, m + 1, v2, m + 1);

  /* t1 = t1 + a2 = a1 + 2*a2 */
  t1[m] += ulbn_add(t1, t1, m, a2, am);
  /* t1 = t1 << 1 = 2*a1 + 4*a2 */
  t1[m] = ul_static_cast(ulbn_limb_t, (t1[m] << 1) | ulbn_shl(t1, t1, m, 1));
  /* t1 = t1 + a0 = a0 + 2*a1 + 4*a2 */
  t1[m] += ulbn_add(t1, t1, m, a0, m);
  /* t2 = t2 + b2 = b1 + 2*b2 */
  t2[m] += ulbn_add(t2, t2, m, b2, bm);
  /* t2 = t2 << 1 = 2*b1 + 4*b2 */
  t2[m] = ul_static_cast(ulbn_limb_t, (t2[m] << 1) | ulbn_shl(t2, t2, m, 1));
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
  vm1[m] = t1[m] + t2[m] + ulbn_add(vm1, t1, m, t2, m);
  /* vm2 = t3 + b1 = b0 + b1 + b2 */
  vm2[m] = t3[m] + ulbn_add(vm2, t3, m, b1, m);
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
  vm2[m] = t1[m] + t2[m] + ulbn_add(vm2, t1, m, t2, m);
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
    ulbn_neg(vm1, vm1, m2 + 2, ul_static_cast(ulbn_limb_t, vm1_sign));
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
    ulbn_neg(vm2, vm2, m2 + 2, ul_static_cast(ulbn_limb_t, vm2_sign));
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

/* Note: If allocation fails, it falls back to using a version with less cache,
  eventually falling back to the school method (time complexity O(n^2)) */
ULBN_PRIVATE void ulbn_mul(
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
  goto fallback_toom3;
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
  const ulbn_alloc_t* alloc, ulbn_limb_t* qp, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t d        /* */
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
  const ulbn_alloc_t* alloc, ulbn_limb_t* qp, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an,                      /* */
  const ulbn_limb_t* dp, ulbn_usize_t dn, int shift            /* */
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


typedef struct ulbn_baseconv_t {
  ulbn_limb_t b;     /* = base**base_pow */
  ulbn_limb_t bi;    /* _ulbn_divinv1(b<<shift) */
  unsigned base_pow; /* the maximum power to make `b` <= ULBN_LIMB_MAX */
  int shift;         /* = _ulbn_ctz_(b) */
  ulbn_limb_t base;
  const char* char_table;
} ulbn_baseconv_t;
ULBN_INTERNAL ulbn_baseconv_t ulbn_prepare_baseconv(ulbn_limb_t base) {
#if ULBN_LIMB_MAX == 0xFFu
  static const ulbn_limb_t table_b[] = {0x80, 0xF3, 0x40, 0x7D, 0xD8, 0x31, 0x40, 0x51, 0x64, 0x79, 0x90, 0xA9,
                                        0xC4, 0xE1, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
                                        0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20, 0x21, 0x22, 0x23, 0x24};
  static const unsigned char table_power[] = {7, 5, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1,
                                              1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1};
  static const signed char table_shift[] = {0, 0, 1, 1, 0, 2, 1, 1, 1, 1, 0, 0, 0, 0, 3, 3, 3, 3,
                                            3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2};
  static const ulbn_limb_t table_bi[] = {0xFF, 0xD,  0xFF, 0x6,  0x2F, 0x4E, 0xFF, 0x94, 0x47, 0xE,  0xC7, 0x83,
                                         0x4E, 0x23, 0xFF, 0xE1, 0xC7, 0xAF, 0x99, 0x86, 0x74, 0x64, 0x55, 0x47,
                                         0x3B, 0x2F, 0x24, 0x1A, 0x11, 0x8,  0xFF, 0xF0, 0xE1, 0xD4, 0xC7};
  #define _ULBN_BASECONV_TABLE_DEFINED
#elif ULBN_LIMB_MAX == 0xFFFFu
  static const ulbn_limb_t table_b[] = {0x8000, 0xE6A9, 0x4000, 0x3D09, 0xB640, 0x41A7, 0x8000, 0xE6A9, 0x2710,
                                        0x3931, 0x5100, 0x6F91, 0x9610, 0xC5C1, 0x1000, 0x1331, 0x16C8, 0x1ACB,
                                        0x1F40, 0x242D, 0x2998, 0x2F87, 0x3600, 0x3D09, 0x44A8, 0x4CE3, 0x55C0,
                                        0x5F45, 0x6978, 0x745F, 0x8000, 0x8C61, 0x9988, 0xA77B, 0xB640};
  static const unsigned char table_power[] = {15, 10, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3,
                                              3,  3,  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3};
  static const signed char table_shift[] = {0, 0, 1, 2, 0, 1, 0, 0, 2, 2, 1, 1, 0, 0, 3, 3, 3, 3,
                                            3, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0};
  static const ulbn_limb_t table_bi[] = {0xFFFF, 0x1C1F, 0xFFFF, 0xC6F,  0x6798, 0xF31D, 0xFFFF, 0x1C1F, 0xA36E,
                                         0x1E7A, 0x948B, 0x25B5, 0xB4B9, 0x4B66, 0xFFFF, 0xAADB, 0x6798, 0x31C0,
                                         0x624,  0xC4E6, 0x89E7, 0x58BA, 0x2F68, 0xC6F,  0xDD46, 0xAA2F, 0x7E22,
                                         0x57F3, 0x36B0, 0x1994, 0xFFFF, 0xD2D9, 0xAADB, 0x874E, 0x6798};
  #define _ULBN_BASECONV_TABLE_DEFINED
#elif ULBN_LIMB_MAX == 0xFFFFFFFFu
  static const ulbn_limb_t table_b[] = {0x80000000, 0xCFD41B91, 0x40000000, 0x48C27395, 0x81BF1000, 0x75DB9C97,
                                        0x40000000, 0xCFD41B91, 0x3B9ACA00, 0x8C8B6D2B, 0x19A10000, 0x309F1021,
                                        0x57F6C100, 0x98C29B81, 0x10000000, 0x18754571, 0x247DBC80, 0x3547667B,
                                        0x4C4B4000, 0x6B5A6E1D, 0x94ACE180, 0xCAF18367, 0xB640000,  0xE8D4A51,
                                        0x1269AE40, 0x17179149, 0x1CB91000, 0x23744899, 0x2B73A840, 0x34E63B41,
                                        0x40000000, 0x4CFA3CC1, 0x5C13D840, 0x6D91B519, 0x81BF1000};
  static const unsigned char table_power[] = {31, 20, 15, 13, 12, 11, 10, 10, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7,
                                              7,  7,  7,  7,  6,  6,  6,  6,  6, 6, 6, 6, 6, 6, 6, 6, 6};
  static const signed char table_shift[] = {0, 0, 1, 1, 0, 1, 1, 0, 2, 0, 3, 2, 1, 0, 3, 3, 2, 2,
                                            1, 1, 0, 0, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 0};
  static const ulbn_limb_t table_bi[] = {0xFFFFFFFF, 0x3B563C24, 0xFFFFFFFF, 0xC25C2684, 0xF91BD1B6, 0x1607A2CB,
                                         0xFFFFFFFF, 0x3B563C24, 0x12E0BE82, 0xD24CDE04, 0x3FA39AB5, 0x50F8AC5F,
                                         0x74843B1E, 0xAD0326C2, 0xFFFFFFFF, 0x4EF0B6BD, 0xC0FC48A1, 0x33838942,
                                         0xAD7F29AB, 0x313C3D15, 0xB8CCA9E0, 0x42ED6DE9, 0x67980E0B, 0x19799812,
                                         0xBCE85396, 0x62C103A9, 0x1D353D43, 0xCE1DECEA, 0x790FC511, 0x35B865A0,
                                         0xFFFFFFFF, 0xA9AED1B3, 0x63DFC229, 0x2B0FEE30, 0xF91BD1B6};
  #define _ULBN_BASECONV_TABLE_DEFINED
#elif _ULBN_IS_64BIT(ULBN_LIMB_MAX)
  static const ulbn_limb_t table_b[] = {0x8000000000000000, 0xA8B8B452291FE821, 0x4000000000000000, 0x6765C793FA10079D,
                                        0x41C21CB8E1000000, 0x3642798750226111, 0x8000000000000000, 0xA8B8B452291FE821,
                                        0x8AC7230489E80000, 0x4D28CB56C33FA539, 0x1ECA170C00000000, 0x780C7372621BD74D,
                                        0x1E39A5057D810000, 0x5B27AC993DF97701, 0x1000000000000000, 0x27B95E997E21D9F1,
                                        0x5DA0E1E53C5C8000, 0xD2AE3299C1C4AEDB, 0x16BCC41E90000000, 0x2D04B7FDD9C0EF49,
                                        0x5658597BCAA24000, 0xA0E2073737609371, 0xC29E98000000000,  0x14ADF4B7320334B9,
                                        0x226ED36478BFA000, 0x383D9170B85FF80B, 0x5A3C23E39C000000, 0x8E65137388122BCD,
                                        0xDD41BB36D259E000, 0xAEE5720EE830681,  0x1000000000000000, 0x172588AD4F5F0981,
                                        0x211E44F7D02C1000, 0x2EE56725F06E5C71, 0x41C21CB8E1000000};
  static const unsigned char table_power[] = {63, 40, 31, 27, 24, 22, 21, 20, 19, 18, 17, 17, 16, 16, 15, 15, 15, 15,
                                              14, 14, 14, 14, 13, 13, 13, 13, 13, 13, 13, 12, 12, 12, 12, 12, 12};
  static const signed char table_shift[] = {0, 0, 1, 1, 1, 2, 0, 0, 0, 1, 3, 1, 3, 1, 3, 2, 1, 0,
                                            3, 2, 1, 0, 4, 3, 2, 2, 1, 0, 0, 4, 3, 3, 2, 2, 1};
  static const ulbn_limb_t table_bi[] = {0xFFFFFFFFFFFFFFFF, 0x846D550E37B5063D, 0xFFFFFFFFFFFFFFFF, 0x3CE9A36F23C0FC90,
                                         0xF24F62335024A295, 0x2DF495CCAA57147B, 0xFFFFFFFFFFFFFFFF, 0x846D550E37B5063D,
                                         0xD83C94FB6D2AC34A, 0xA8ADF7AE45E7577B, 0xA10C2BEC5DA8F8F,  0x10F4BECAFE412EC3,
                                         0xF08480F672B4E86,  0x6779C7F90DC42F48, 0xFFFFFFFFFFFFFFFF, 0x9C71E11BAB279323,
                                         0x5DFAA697EC6F6A1C, 0x3711783F6BE7E9EC, 0x6849B86A12B9B01E, 0x6BF097BA5CA5E239,
                                         0x7B8015C8D7AF8F08, 0x975A24B3A3151B38, 0x50BD367972689DB1, 0x8C240C4AECB13BB5,
                                         0xDBD2E56854E118C9, 0x2351FFCAA9C7C4AE, 0x6B24188CA33B0636, 0xCC3DCEAF2B8BA99D,
                                         0x2832E835C6C7D6B6, 0x76B6AA272E1873C5, 0xFFFFFFFFFFFFFFFF, 0x61EAF5D402C7BF4F,
                                         0xEEB658123FFB27EC, 0x5D5E3762E6FDF509, 0xF24F62335024A295};
  #define _ULBN_BASECONV_TABLE_DEFINED
#endif

  ulbn_baseconv_t conv;
#ifdef _ULBN_BASECONV_TABLE_DEFINED
  ulbn_assert(base >= 2 && base <= 36);
  conv.b = table_b[base - 2];
  conv.bi = table_bi[base - 2];
  conv.shift = table_shift[base - 2];
  conv.base_pow = table_power[base - 2];
  conv.base = base;
#else
  ulbn_limb_t b_guard;
  b_guard = ul_static_cast(ulbn_limb_t, ULBN_LIMB_MAX / base);
  conv.base_pow = 1;
  conv.base = base;
  for(conv.b = base; conv.b <= b_guard; conv.b *= base)
    ++conv.base_pow;
  conv.bi = ulbn_divinv1(conv.b);
#endif
  conv.char_table = _ULBN_UPPER_TABLE;
  return conv;
}
ULBN_INTERNAL int ulbn_conv2print_generic(
  const ulbn_alloc_t* alloc, size_t desire_len, /* */
  ulbn_printer_t* printer, void* opaque,        /* */
  const ulbn_limb_t* ap, const ulbn_usize_t an, /* */
  ulbn_baseconv_t conv                          /* */
) {
  ulbn_limb_t* cp;
  size_t ccap = 0, ci = 0;

  ulbn_limb_t* tp;
  ulbn_usize_t tn = an;

  int err = ULBN_ERR_NOMEM;
  char buf[_ULBN_LIMB_BITS];
  char *pbuf, *const buf_end = buf + ULBN_LIMB_BITS;
  ulbn_limb_t c;
  size_t writen;

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

    ulbn_divmod_inv1(tp, cp + (ci++), tp, tn, ul_static_cast(ulbn_limb_t, conv.b << conv.shift), conv.bi, conv.shift);
    if(ul_likely(tp[tn - 1] == 0))
      --tn;
  } while(tn > 0);

  err = ULBN_ERR_EXTERNAL;
  c = cp[--ci];
  for(pbuf = buf_end; c; c /= conv.base)
    *--pbuf = conv.char_table[c % conv.base];
  writen = ul_static_cast(size_t, buf_end - pbuf);
  if(ul_unlikely(desire_len / conv.base_pow >= ci)) {
    size_t diff = desire_len - conv.base_pow * ci;
    if(diff > writen) {
      char tbuf[8];
      diff -= writen;
      memset(tbuf, conv.char_table[0], 8);
      while(diff > 8) {
        err = printer(opaque, tbuf, 8);
        if(ul_unlikely(err))
          goto cleanup;
        diff -= 8;
      }
      err = printer(opaque, tbuf, diff);
      if(ul_unlikely(err))
        goto cleanup;
    }
  }
  if(ul_unlikely(printer(opaque, pbuf, ul_static_cast(size_t, buf_end - pbuf))))
    goto cleanup;

  while(ci > 0) {
    c = cp[--ci];
    for(pbuf = buf + conv.base_pow; c; c /= conv.base)
      *--pbuf = conv.char_table[c % conv.base];
    memset(buf, conv.char_table[0], ul_static_cast(size_t, pbuf - buf));
    if(ul_unlikely(printer(opaque, buf, conv.base_pow)))
      goto cleanup;
  }
  err = 0;

cleanup:
  ulbn_deallocT(ulbn_limb_t, alloc, cp, ccap);
  ulbn_deallocT(ulbn_limb_t, alloc, tp, an);
  return err;
}

ULBN_INTERNAL ulbn_usize_t ulbn_measure_conv2_size(ulbn_usize_t rl, ulbn_usize_t rh, int base, int inv) {
  /* Store log2(base) as a fraction, only allowing overestimation */
#if ULBN_LIMB_MAX >= 0xFFFFFFFF
  static const ulbn_limb_t table_log2[][2] = {
    /* clang-format off */
    {0x1, 0x1},              {0x333A379, 0x51318AD},  {0x1, 0x2},             {0x2A30F19, 0x61F703B},
    {0x333A379, 0x846BC26},  {0x1A90993, 0x4A93B18},  {0x1, 0x3},             {0x333A379, 0xA26315A},
    {0x2A30F19, 0x8C27F54},  {0x42C29E7, 0xE6F3D3D},  {0x333A379, 0xB7A5F9F}, {0x1F11ECF, 0x72F905A},
    {0x1A90993, 0x65244AB},  {0x1695FAD, 0x583D8FF},  {0x1, 0x4},             {0x1E3B74B, 0x7B92BCF},
    {0x333A379, 0xD59D4D3},  {0x4F22C47, 0x15029C67}, {0x38DED52, 0xF5CA3A3}, {0xFC4D6E, 0x4543147},
    {0x42C29E7, 0x129B6724}, {0x24269CB, 0xA387CFA},  {0x333A379, 0xEAE0318}, {0x2A30F19, 0xC3EE076},
    {0x1F11ECF, 0x920AF29},  {0x333A379, 0xF394A07},  {0x1A90993, 0x7FB4E3E}, {0xE9F3DE2, 0x470898E1},
    {0x1695FAD, 0x6ED38AC},  {0x376B249, 0x1128DE40}, {0x1, 0x5},             {0x21F31B1, 0xAB415CD},
    {0x1E3B74B, 0x99CE31A},  {0x1D61D65, 0x96B5A1B},  {0x333A379, 0x108D784C}
    /* clang-format on */
  };
#elif ULBN_LIMB_MAX >= 0xFFFF
  static const ulbn_limb_t table_log2[][2] = {
    {1, 1},         {15601, 24727}, {1, 2},         {21306, 49471}, {15601, 40328}, {2964, 8321},   {1, 3},
    {15601, 49454}, {8651, 28738},  {4856, 16799},  {15601, 55929}, {5458, 20197},  {2964, 11285},  {15659, 61178},
    {1, 4},         {12451, 50893}, {15601, 65055}, {11701, 49705}, {8651, 37389},  {13433, 59002}, {4856, 21655},
    {5963, 26974},  {14271, 65432}, {10653, 49471}, {5458, 25655},  {10179, 48400}, {2964, 14249},  {10738, 52165},
    {11610, 56969}, {10676, 52891}, {1, 5},         {10159, 51246}, {12451, 63344}, {3473, 17814},  {7468, 38609}
  };
#else
  static const ulbn_limb_t table_log2[][2] = {
    {1, 1},    {147, 233}, {1, 2},    {59, 137}, {94, 243}, {26, 73},  {1, 3},    {47, 149}, {59, 196},
    {37, 128}, {41, 147},  {67, 248}, {26, 99},  {43, 168}, {1, 4},    {57, 233}, {47, 196}, {4, 17},
    {59, 255}, {28, 123},  {37, 165}, {21, 95},  {41, 188}, {45, 209}, {47, 221}, {49, 233}, {26, 125},
    {50, 243}, {43, 211},  {22, 109}, {1, 5},    {45, 227}, {34, 173}, {23, 118}, {47, 243}
    /* clang-format off */
    /* clang-format on */
  };
#endif

  ulbn_limb_t buf[_ULBN_MERGE_USIZE_LEN + 1];
  ulbn_usize_t len;
  ulbn_limb_t d;
  int shift;

  ulbn_assert(2 <= base && base <= 36);
  ulbn_assert(inv == 0 || inv == 1);

  len = ulbn_merge_usize(buf, rl, rh);
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

#if ULBN_USIZE_MAX <= ULBN_LIMB_MAX
  #if ULBN_USIZE_MAX < ULBN_LIMB_MAX
  if(ul_unlikely(buf[0] > ULBN_USIZE_MAX))
    return ULBN_USIZE_MAX;
  #endif
  return ul_static_cast(ulbn_usize_t, buf[0]);
#else
  do {
    ulbn_usize_t ret = 0;
    if(ul_unlikely(len * CHAR_BIT - ul_static_cast(size_t, _ulbn_clz_(buf[len - 1])) > sizeof(ulbn_usize_t) * CHAR_BIT))
      return ULBN_USIZE_MAX;
    do {
      ret <<= ULBN_LIMB_BITS - 1;
      ret <<= 1;
      ret |= buf[--len];
    } while(len > 0);
    return ret;
  } while(0);
#endif
}

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


ULBN_PRIVATE void ulbn_and_nocy(
  ulbn_limb_t* rp, const ulbn_limb_t* ap, const ulbn_limb_t* bp, ulbn_limb_t b_rev_mask, ulbn_usize_t n
) {
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
    rp[i] = ap[i] & (bp[i] ^ b_rev_mask);
}
ULBN_PRIVATE void ulbn_or_nocy(
  ulbn_limb_t* rp, const ulbn_limb_t* ap, const ulbn_limb_t* bp, ulbn_limb_t b_rev_mask, ulbn_usize_t n
) {
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
    rp[i] = ap[i] | (bp[i] ^ b_rev_mask);
}
ULBN_PRIVATE void ulbn_xor_nocy(
  ulbn_limb_t* rp, const ulbn_limb_t* ap, const ulbn_limb_t* bp, ulbn_limb_t b_rev_mask, ulbn_usize_t n
) {
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
    rp[i] = ap[i] ^ bp[i] ^ b_rev_mask;
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
/* In 2's complement, rp[0:an] = cy ? -ap[0:an] : ap[0:an], return carry (do not write to rp[an]) */
ULBN_INTERNAL ulbn_limb_t ulbn_neg(ulbn_limb_t* rp, const ulbn_limb_t* ap, ulbn_usize_t an, ulbn_limb_t cy) {
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
    equal to k, and the loop will terminate directly */
  ulbn_usize_t i = ~mask & k;

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
ULBN_INTERNAL int ulbn_to_bit_info(const ulbn_limb_t* limb, ulbn_usize_t n, ulbn_usize_t* p_idx) {
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
  qn = ulbn_rnorm(q, n);
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
  numl = ul_static_cast(ulbn_limb_t, (numl << ULBN_LIMB_HALF_BITS) | ULBN_HIGHPART(a0));
  s <<= 1;
  _ulbn_udiv_(q, u, numh, numl, s);
  s = ul_static_cast(ulbn_limb_t, (s << (ULBN_LIMB_HALF_BITS - 1u)) + q);
  rh = ULBN_HIGHPART(u);
  rl = ul_static_cast(ulbn_limb_t, (u << ULBN_LIMB_HALF_BITS) | ULBN_LOWPART(a0));
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
    numl = ul_static_cast(ulbn_limb_t, ul_static_cast(ulbn_limb_t, s << 1u) | 1u);
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
  const ulbn_alloc_t* alloc, ulbn_limb_t* sp, ulbn_limb_t* rp, /* */
  const ulbn_limb_t* ap, ulbn_usize_t an                       /* */
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
  return ul_static_cast(ulbn_limb_t, a << shift);
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


/* return ap[0:an]*2 <=> mp[0:mn] */
ULBN_INTERNAL int ulbn_check_round(const ulbn_limb_t* ap, ulbn_usize_t an, const ulbn_limb_t* mp, ulbn_usize_t mn) {
  return -ulbn_cmpshl(mp, mn, ap, an, 1);
}


/***************
 * Big Integer *
 ***************/


ULBN_PUBLIC ulbi_t* ulbi_init(ulbi_t* o) {
  o->len = 0;
  o->cap = ULBN_SHORT_LIMB_SIZE_VAL;
  return o;
}
ULBN_PUBLIC int ulbi_init_reserve(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n) {
  ULBN_RETURN_IF_USIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
  o->cap = ULBN_SHORT_LIMB_SIZE_VAL;
  o->len = 0;
  if(n > ULBN_SHORT_LIMB_SIZE_VAL) {
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
  ulbn_assert(n > ULBN_SHORT_LIMB_SIZE_VAL);
#if ULBN_CONF_ONLY_ALLOCATE_NEEDED
  new_cap = n;
#else
  new_cap = o->cap + (o->cap >> 1);
  new_cap = _ulbn_max_(new_cap, n);
  ULBN_DO_IF_USIZE_OVERFLOW(new_cap, new_cap = n;);
#endif
  ULBN_DO_IF_USIZE_OVERFLOW(new_cap, return ul_nullptr;);

  if(o->cap > ULBN_SHORT_LIMB_SIZE_VAL) {
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
#define _ulbi_limbs(o) ((o)->cap <= ULBN_SHORT_LIMB_SIZE_VAL ? (o)->u.shrt : (o)->u.lng)
#define _ulbi_res(alloc, o, n) (((n) <= (o)->cap) ? _ulbi_limbs(o) : _ulbi_reserve((alloc), (o), (n)))
ULBN_PUBLIC ulbn_limb_t* ulbi_reserve(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n) {
  return _ulbi_res(alloc, o, n);
}


#define _ulbi_set_zero(dst) ((dst)->len = 0)
#define _ulbi_may_set_zero(dst) ((dst) && _ulbi_set_zero(dst))
ULBN_PUBLIC ulbi_t* ulbi_set_zero(ulbi_t* dst) {
  _ulbi_set_zero(dst);
  return dst;
}
ULBN_PUBLIC ulbi_t* ulbi_init_limb(ulbi_t* dst, ulbn_limb_t limb) {
  dst->cap = ULBN_SHORT_LIMB_SIZE_VAL;
  if(limb == 0)
    _ulbi_set_zero(dst);
  else {
    dst->u.shrt[0] = limb;
    dst->len = 1;
  }
  return dst;
}
ULBN_PUBLIC ulbi_t* ulbi_init_slimb(ulbi_t* dst, ulbn_slimb_t slimb) {
  dst->cap = ULBN_SHORT_LIMB_SIZE_VAL;
  if(slimb == 0)
    _ulbi_set_zero(dst);
  else {
    if(slimb < 0) {
      dst->u.shrt[0] = _ulbn_from_neg_slimb(slimb);
      dst->len = -1;
    } else {
      dst->u.shrt[0] = _ulbn_from_pos_slimb(slimb);
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
      _ulbi_limbs(dst)[0] = _ulbn_from_neg_slimb(slimb);
      dst->len = -1;
    } else {
      _ulbi_limbs(dst)[0] = _ulbn_from_pos_slimb(slimb);
      dst->len = 1;
    }
  }
}


ULBN_PUBLIC void ulbi_deinit(const ulbn_alloc_t* alloc, ulbi_t* o) {
  if(o->cap > ULBN_SHORT_LIMB_SIZE_VAL)
    ulbn_deallocT(ulbn_limb_t, alloc, o->u.lng, o->cap);
  _ulbi_set_zero(o);
  o->cap = ULBN_SHORT_LIMB_SIZE_VAL;
}
ULBN_PUBLIC int ulbi_shrink(const ulbn_alloc_t* alloc, ulbi_t* o) {
  const ulbn_usize_t n = _ulbn_abs_size(o->len);
  if(o->cap <= ULBN_SHORT_LIMB_SIZE_VAL)
    return 0;
  if(n <= ULBN_SHORT_LIMB_SIZE_VAL) {
    ulbn_limb_t temp[ULBN_SHORT_LIMB_SIZE];
    memcpy(temp, o->u.lng, sizeof(temp));
    ulbn_deallocT(ulbn_limb_t, alloc, o->u.lng, o->cap);
    memcpy(o->u.shrt, temp, sizeof(temp));
    o->cap = ULBN_SHORT_LIMB_SIZE_VAL;
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


ULBN_PUBLIC void ulbi_swap(ulbi_t* o1, ulbi_t* o2) {
  _ulbn_swap_(ulbi_t, *o1, *o2);
}
ULBN_PUBLIC int ulbi_neg(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao) {
  int err = ulbi_set_copy(alloc, ro, ao);
  ro->len = -ro->len;
  return err;
}
ULBN_PUBLIC int ulbi_abs(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao) {
  int err = ulbi_set_copy(alloc, ro, ao);
  ro->len = ulbn_cast_ssize(_ulbn_abs_size(ro->len));
  return err;
}


ULBN_PUBLIC int ulbi_set_copy(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* src) {
  if(dst != src) {
    ulbn_limb_t* limb;
    ulbn_usize_t n = _ulbn_abs_size(src->len);
    if(n <= ULBN_SHORT_LIMB_SIZE_VAL) {
      limb = _ulbi_limbs(dst);
      ulbn_copy(limb, _ulbi_limbs(src), n);
    } else {
      limb = _ulbi_res(alloc, dst, n);
      ULBN_RETURN_IF_ALLOC_FAILED(limb, ULBN_ERR_NOMEM);
      ulbn_copy(limb, _ulbi_limbs(src), n);
    }
    dst->len = src->len;
  }
  return 0;
}
ULBN_PUBLIC void ulbi_set_move(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbi_t* src) {
  ulbi_deinit(alloc, dst);
  *dst = *src;
  ulbi_init(src);
}
ul_static_assert(
  (sizeof(ulbn_ulong_t) * CHAR_BIT + _ULBN_LIMB_BITS - 1) / _ULBN_LIMB_BITS <= _ULBN_SSIZE_LIMIT,
  "ulbn_ulong_t is too large that `ulbi_t` cannot hold it"
);
ULBN_PUBLIC int ulbi_set_ulong(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ulong_t l) {
  ulbn_limb_t limbs[(sizeof(l) + sizeof(ulbn_limb_t) - 1) / sizeof(ulbn_limb_t)];

  if(l == 0)
    _ulbi_set_zero(dst);
  else {
    ulbn_limb_t* ptr;
    ulbn_ssize_t len = 0;

#if ULBN_ULONG_MAX <= ULBN_LIMB_MAX
    limbs[len++] = ul_static_cast(ulbn_limb_t, l);
#else
    do {
      limbs[len++] = ul_static_cast(ulbn_limb_t, l);
      l >>= ULBN_LIMB_BITS;
    } while(l);
#endif
    ptr = _ulbi_res(alloc, dst, ulbn_cast_usize(len));
    ULBN_RETURN_IF_ALLOC_FAILED(ptr, ULBN_ERR_NOMEM);
    ulbn_copy(ptr, limbs, ulbn_cast_usize(len));
    dst->len = len;
  }
  return 0;
}
ULBN_PUBLIC int ulbi_set_slong(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_slong_t l) {
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
ULBN_PUBLIC int ulbi_set_usize(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t l) {
  ulbn_limb_t limbs[(sizeof(l) + sizeof(ulbn_limb_t) - 1) / sizeof(ulbn_limb_t)];

  if(l == 0)
    _ulbi_set_zero(dst);
  else {
    ulbn_ssize_t len = 0;
    ulbn_limb_t* ptr;

#if ULBN_USIZE_MAX <= ULBN_LIMB_MAX
    limbs[len++] = ul_static_cast(ulbn_limb_t, l);
#else
    do {
      limbs[len++] = ul_static_cast(ulbn_limb_t, l);
      l >>= ULBN_LIMB_BITS;
    } while(l);
#endif

    ptr = _ulbi_res(alloc, dst, ulbn_cast_usize(len));
    ULBN_RETURN_IF_ALLOC_FAILED(ptr, ULBN_ERR_NOMEM);
    ulbn_copy(ptr, limbs, ulbn_cast_usize(len));
    dst->len = len;
  }
  return 0;
}
ULBN_PUBLIC int ulbi_set_ssize(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ssize_t l) {
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
ULBN_PUBLIC int ulbi_set_2exp_usize(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t n) {
  ulbn_limb_t* p;
  const ulbn_usize_t idx = n / ULBN_LIMB_BITS;
  p = _ulbi_res(alloc, dst, idx + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(p, ULBN_ERR_NOMEM);
  ulbn_fill0(p, idx);
  p[idx] = ULBN_LIMB_SHL(1, n % ULBN_LIMB_BITS);
  dst->len = ulbn_cast_ssize(idx + 1);
  return 0;
}
ULBN_PUBLIC int ulbi_set_2exp(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* n) {
  ulbn_limb_t* p;
  ulbn_usize_t idx;
  int shift;

  if(n->len < 0) {
    _ulbi_set_zero(dst);
    return ULBN_ERR_INEXACT;
  }
  shift = ulbn_to_bit_info(_ulbi_limbs(n), _ulbn_abs_size(n->len), &idx);
  if(ul_unlikely(shift < 0 || idx > ULBN_SSIZE_LIMIT - 1))
    return ULBN_ERR_EXCEED_RANGE;
  p = _ulbi_res(alloc, dst, idx + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(p, ULBN_ERR_NOMEM);
  ulbn_fill0(p, idx);
  p[idx] = ULBN_LIMB_SHL(1, shift);
  dst->len = ulbn_cast_ssize(idx + 1);
  return 0;
}

ul_static_assert('0' == 48, "not ASCII");
ul_static_assert('A' == 65, "not ASCII");
ul_static_assert('Z' == 90, "not ASCII");
ul_static_assert('a' == 97, "not ASCII");
ul_static_assert('z' == 122, "not ASCII");
ul_static_assert(ULBN_LIMB_MAX >= 36, "ulbn_limb_t is too small to hold base");
ULBN_PRIVATE int _ulbi_mul_base_exp(const ulbn_alloc_t* alloc, ulbi_t* obj, int base, ulbn_usize_t expo) {
  ulbi_t temp;
  int err;
  int shift = -1;

  ulbn_assert(base >= 2 && base <= 36);

  if(ul_likely(base == 16))
    shift = 4;
  else if(base == 8)
    shift = 3;
  else if(base == 4)
    shift = 2;
  else if(base == 2)
    return ulbi_sal_usize(alloc, obj, obj, expo);

  if(shift >= 0) {
    if(ul_unlikely(expo > ULBN_USIZE_MAX / ul_static_cast(unsigned char, shift))) {
      err = ulbi_init_usize(alloc, &temp, expo);
      ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
      err = ulbi_mul_limb(alloc, &temp, &temp, ul_static_cast(ulbn_limb_t, shift));
      if(ul_likely(err >= 0))
        err = ulbi_sal(alloc, obj, obj, &temp);
      ulbi_deinit(alloc, &temp);
    } else
      err = ulbi_sal_usize(alloc, obj, obj, expo * ul_static_cast(unsigned char, shift));
  } else {
    ulbi_init_limb(&temp, ul_static_cast(ulbn_limb_t, base));
    err = ulbi_pow_usize(alloc, &temp, &temp, expo);
    if(ul_likely(err >= 0))
      err = ulbi_mul(alloc, obj, obj, &temp);
    ulbi_deinit(alloc, &temp);
  }
  return err;
}
ULBN_PRIVATE int _ulbi_div_base_exp(const ulbn_alloc_t* alloc, ulbi_t* obj, int base, ulbn_usize_t expo) {
  ulbi_t temp;
  int err;
  int shift = -1;

  ulbn_assert(base >= 2 && base <= 36);

  if(ul_likely(base == 16))
    shift = 4;
  else if(base == 8)
    shift = 3;
  else if(base == 4)
    shift = 2;
  else if(base == 2)
    return ulbi_sal_usize(alloc, obj, obj, expo);

  if(shift >= 0) {
    if(ul_unlikely(expo > ULBN_USIZE_MAX / ul_static_cast(unsigned char, shift))) {
      err = ulbi_init_usize(alloc, &temp, expo);
      ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
      err = ulbi_mul_limb(alloc, &temp, &temp, ul_static_cast(ulbn_limb_t, shift));
      if(ul_likely(err >= 0))
        err = ulbi_div_2exp(alloc, obj, obj, &temp);
      ulbi_deinit(alloc, &temp);
    } else
      err = ulbi_div_2exp_usize(alloc, obj, obj, expo * ul_static_cast(unsigned char, shift));
  } else {
    ulbi_init_limb(&temp, ul_static_cast(ulbn_limb_t, base));
    err = ulbi_pow_usize(alloc, &temp, &temp, expo);
    if(ul_likely(err >= 0))
      err = ulbi_div(alloc, obj, obj, &temp);
    ulbi_deinit(alloc, &temp);
  }

  ulbn_assert(err < 0 || err == 0 || err == ULBN_ERR_INEXACT);
  return err;
}
ULBN_PUBLIC int ulbi_set_string_ex(const ulbn_alloc_t* alloc, ulbi_t* dst, const char** pstr, int base, int flag) {
  static ul_constexpr const unsigned char _TABLE[] = {
    0,   1,  2,  3,  4,  5,  6,  7,  8,  9,  255, 255, 255, 255, 255, 255, /* \x30 - \x3F */
    255, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,  20,  21,  22,  23,  24,  /* \x40 - \x4F */
    25,  26, 27, 28, 29, 30, 31, 32, 33, 34, 35,  255, 255, 255, 255, 255, /* \x50 - \x5F */
    255, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,  20,  21,  22,  23,  24,  /* \x60 - \x6F */
    25,  26, 27, 28, 29, 30, 31, 32, 33, 34, 35,  255, 255, 255, 255, 255, /* \x70 - \x7F */
  };

  ulbn_limb_t B_GUARD;
  const char* str = *pstr;
  const int CH_SEP = (flag & ULBN_SET_STRING_ACCEPT_SEPARATOR) ? '_' : 0x100;
  const int CH_DOT = (flag & ULBN_SET_STRING_ACCEPT_DECIMAL_PART) ? '.' : 0x100;
  unsigned x;
  int err = 0, neg = 0;

  ulbn_limb_t intpart_l = 0, intpart_B = 1;

  const char* frac_start = ul_nullptr;
  const char* frac_end = ul_nullptr;
  const char* frac_end2;
  ulbi_t frac = ULBI_INIT;
  ulbn_limb_t fracpart_l = 0, fracpart_B = 1;
  ulbn_usize_t frac_expo;

  ulbn_usize_t expo = 0;
  int expo_neg = 0;
  int expo_base = 0;

#if 1
  #define _ULBI_CHECK(B, l, bi)                    \
    if((B) >= B_GUARD) {                           \
      err = ulbi_mul_limb(alloc, (bi), (bi), (B)); \
      ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;); \
      err = ulbi_add_limb(alloc, (bi), (bi), (l)); \
      ulbn_assert(err <= 0);                       \
      ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;); \
      (l) = 0;                                     \
      (B) = 1;                                     \
    }                                              \
    (void)0
  #define _ULBI_NEXT(B, l, x)                   \
    ulbn_assert((B) < B_GUARD);                 \
    (B) *= ul_static_cast(unsigned char, base); \
    (l) = ul_static_cast(ulbn_limb_t, (l) * ul_static_cast(unsigned char, base) + x)
  #define _ULBI_END(B, l, bi)                      \
    if((B) != 1) {                                 \
      err = ulbi_mul_limb(alloc, (bi), (bi), (B)); \
      ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;); \
      err = ulbi_add_limb(alloc, (bi), (bi), (l)); \
    }                                              \
    (void)0
  #define _ULBI_INRANGE(ch) (ul_static_cast(unsigned char, (ch)) - 0x30u < 0x50u)
  #define _ULBI_TAB(ch) _TABLE[ul_static_cast(unsigned char, (ch)) - 0x30u]
#endif

  /* remove preffix */

  _ulbi_set_zero(dst);
  if(str[0] == '-') {
    neg = 1;
    ++str;
  } else if(str[0] == '+')
    ++str;
  if(*str == 0) {
    --str;
    goto done;
  }

  if(base == 0) {
    if(str[0] == '0') {
      if(str[1] == 0) { /* "0" */
        ++str;          /* eat "0" */
        goto done;
      } else if(str[1] == 'x' || str[1] == 'X') {
        if(str[2] == 0) { /* "0x" or "0X" */
          ++str;          /* eat "0" */
          goto done;
        } else if((str[2] >= '0' && str[2] <= '9') || (str[2] >= 'a' && str[2] <= 'f')
                  || (str[2] >= 'A' && str[2] <= 'F') || str[2] == CH_DOT) {
          /* eat "0x"/"0X", and accpet the preffix */
          base = 16;
          str += 2;
        } else {
          ++str; /* eat "0" */
          goto done;
        }
      } else if(str[1] == 'b' || str[1] == 'B') {
        if(str[2] == 0) { /* "0x" or "0X" */
          ++str;          /* eat "0" */
          goto done;
        } else if(str[2] == '0' || str[2] == '1' || str[2] == CH_DOT) {
          /* eat "0b"/"0B", and accpet the preffix */
          base = 2;
          str += 2;
        } else {
          ++str; /* eat "0" */
          goto done;
        }
      } else if(str[1] == 'o' || str[1] == 'O') {
        if(str[2] == 0) {
          ++str; /* eat "0" */
          goto done;
        } else if(str[2] >= '0' && str[2] <= '7') {
          base = 8;
          str += 2;
        } else {
          ++str; /* eat "0" */
          goto done;
        }
      } else if(str[1] == '0') { /* "00" */
        ++str;
        goto done;
      } else if((str[1] >= '1' && str[1] <= '7') && (flag & ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX)) {
        base = 8;
        ++str;
      } else if(str[1] == CH_DOT) { /* "0."... */
        base = 10;
        ++str; /* eat "0" only */
      } else {
        ++str; /* eat "0" only */
        goto done;
      }
    } else {
      base = 10;
    }
  }
  if(base < 2 || base > 36) {
    err = ULBN_ERR_EXCEED_RANGE;
    goto done;
  }

  /* parse integer part */

  B_GUARD = ul_static_cast(ulbn_limb_t, ULBN_LIMB_MAX / ul_static_cast(unsigned, base));
  for(;; ++str) {
    _ULBI_CHECK(intpart_B, intpart_l, dst);
    if(!_ULBI_INRANGE(*str) || (x = _ULBI_TAB(*str)) >= ul_static_cast(unsigned, base)) {
      if(*str == CH_SEP)
        continue;
      else
        break;
    }
    _ULBI_NEXT(intpart_B, intpart_l, x);
  }
  _ULBI_END(intpart_B, intpart_l, dst);

  if(*str == CH_DOT) {
    frac_start = ++str;
    for(;;)
      if((_ULBI_INRANGE(*str) && _ULBI_TAB(*str) < ul_static_cast(unsigned, base)) || *str == CH_SEP)
        ++str;
      else
        break;
    frac_end = str;
  }

  /* parse exponent part */

  if(*str == 'e' || *str == 'E' || *str == 'p' || *str == 'P') {
    const ulbn_usize_t EXPO_LIMIT = (ULBN_USIZE_MAX - 9) / 10;

    if(*str == 'e' || *str == 'E') {
      if(!(flag & ULBN_SET_STRING_ACCEPT_DEC_EXPONENT))
        goto handle_frac;
      if(!(flag & ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH) && base != 10)
        goto handle_frac;
      expo_base = 10;
    } else {
      if(!(flag & ULBN_SET_STRING_ACCEPT_HEX_EXPONENT))
        goto handle_frac;
      if(!(flag & ULBN_SET_STRING_ALLOW_EXPONENT_MISMATCH) && base != 16)
        goto handle_frac;
      expo_base = 2;
    }
    ++str;

    if(*str == '+')
      ++str;
    else if(*str == '-') {
      ++str;
      expo_neg = 1;
    }

    for(;; ++str)
      if(*str >= '0' && *str <= '9') {
        if(ul_likely(expo <= EXPO_LIMIT)) {
          expo *= 10u;
          expo += ul_static_cast(unsigned char, *str - '0');
        } else {
          err = ULBN_ERR_EXCEED_RANGE;
          goto done;
        }
      } else
        break;
  }

handle_frac: /* parse fractional part */
  while(frac_start < frac_end && frac_end[-1] == '0')
    --frac_end;
  if(frac_start == frac_end) {
    if(ul_unlikely(expo_neg) && expo)
      err = _ulbi_div_base_exp(alloc, dst, base, expo);
    goto done;
  }

  if(expo == 0) {
    err = ULBN_ERR_INEXACT;
    goto done;
  }
  if(ul_unlikely(expo_neg)) {
    err = _ulbi_div_base_exp(alloc, dst, base, expo);
    if(err == 0)
      err = ULBN_ERR_INEXACT;
    goto done;
  }

  if(ul_unlikely(expo_base != base)) {
    frac_expo = 0;
    for(; frac_start < frac_end; ++frac_start) {
      _ULBI_CHECK(fracpart_B, fracpart_l, &frac);
      if(*frac_start == CH_SEP)
        continue;
      x = _TABLE[ul_static_cast(unsigned char, *frac_start) - 0x30u];
      _ULBI_NEXT(fracpart_B, fracpart_l, x);
      ++frac_expo;
    }
    _ULBI_END(fracpart_B, fracpart_l, &frac);

    err = _ulbi_mul_base_exp(alloc, dst, base, expo);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;);
    err = _ulbi_mul_base_exp(alloc, &frac, expo_base, expo);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;);
    err = _ulbi_div_base_exp(alloc, &frac, base, frac_expo);
    if(ul_likely(err >= 0)) {
      int nerr = ulbi_add(alloc, dst, dst, &frac);
      ULBN_DO_IF_PUBLIC_COND(nerr < 0, err = nerr;);
    }
    goto done;
  }

  err = _ulbi_mul_base_exp(alloc, dst, base, expo);
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;);

  if(ul_static_cast(size_t, frac_end - frac_start) > expo)
    frac_end2 = frac_start + expo;
  else
    frac_end2 = frac_end;
  for(; frac_start < frac_end2; ++frac_start) {
    _ULBI_CHECK(fracpart_B, fracpart_l, &frac);
    x = _TABLE[ul_static_cast(unsigned char, *frac_start) - 0x30u];
    _ULBI_NEXT(fracpart_B, fracpart_l, x);
    --expo;
  }
  _ULBI_END(fracpart_B, fracpart_l, &frac);

  if(expo) {
    err = _ulbi_mul_base_exp(alloc, &frac, base, expo);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;);
  }
  err = ulbi_add(alloc, dst, dst, &frac);
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto done;);
  err = frac_end2 != frac_end ? ULBN_ERR_INEXACT : 0;

done:
  ulbi_deinit(alloc, &frac);
  *pstr = str;
  if(neg) {
    dst->len = -dst->len;
    if(err == 0 && dst->len == 0)
      err = ULBN_ERR_INEXACT;
  }
  return err;
#undef _ULBI_CHECK
#undef _ULBI_END
#undef _ULBI_NEXT
#undef _ULBI_INRANGE
#undef _ULBI_TAB
}
ULBN_PUBLIC int ulbi_set_string(const ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, int base) {
  int err = ulbi_set_string_ex(alloc, dst, &str, base, ULBN_SET_STRING_ACCEPT_OCT_IMPLICIT_PREFIX);
  if(err < 0)
    return err;
  return *str == 0 ? 0 : ULBN_ERR_INVALID;
}

ULBN_PUBLIC int ulbi_set_data(
  const ulbn_alloc_t* alloc, ulbi_t* dst,          /* */
  const void* limbs, size_t len, int is_big_endian /* */
) {
  const unsigned char* p = ul_reinterpret_cast(const unsigned char*, limbs);
  ulbn_limb_t* dp;
  size_t wlen;

#if ULBN_LIMB_MAX < UCHAR_MAX
  #error "ulbn: `ulbn_limb_t` cannot be smaller than `unsigned char`"
#endif

#if ULBN_LIMB_MAX != UCHAR_MAX
  const unsigned char* q;
  unsigned sz;
  ulbn_limb_t limb = 0;
#endif

  if(!is_big_endian)
    while(len > 0 && p[len - 1] == 0)
      --len;
  else
    while(len > 0 && p[0] == 0) {
      ++p;
      --len;
    }
#if ULBN_LIMB_MAX == UCHAR_MAX
  wlen = len;
#else
  wlen = len / sizeof(ulbn_limb_t) + (len % sizeof(ulbn_limb_t) != 0);
#endif
  if(ul_unlikely(wlen > ULBN_SSIZE_LIMIT))
    return ULBN_ERR_EXCEED_RANGE;
  dp = _ulbi_res(alloc, dst, ulbn_cast_usize(wlen));
  ULBN_RETURN_IF_ALLOC_FAILED(dp, ULBN_ERR_NOMEM);

#if ULBN_LIMB_MAX == UCHAR_MAX
  if(!is_big_endian)
    memcpy(dp, p, len);
  else
    for(p += len; len--;)
      *dp++ = *--p;
#else
  if(!is_big_endian) {
    limb = 0;
    while(len >= sizeof(ulbn_limb_t)) {
      q = p + sizeof(ulbn_limb_t);
      for(sz = sizeof(ulbn_limb_t); sz--;)
        limb = (limb << CHAR_BIT) | *--q;
      *dp++ = limb;
      len -= sizeof(ulbn_limb_t);
    }
    limb = 0;
    p += len;
    while(len--)
      limb = (limb << CHAR_BIT) | *p++;
    if(limb)
      *dp++ = limb;
  } else {
    p += len;
    while(len >= sizeof(ulbn_limb_t)) {
      for(sz = sizeof(ulbn_limb_t); sz--;)
        limb = (limb << CHAR_BIT) | *--p;
      *dp++ = limb;
      len -= sizeof(ulbn_limb_t);
    }
    limb = 0;
    while(len--)
      limb = (limb << CHAR_BIT) | *--p;
    if(limb)
      *dp++ = limb;
  }
#endif

  dst->len = ulbn_cast_ssize(ulbn_rnorm(_ulbi_limbs(dst), ulbn_cast_usize(wlen)));
  return 0;
}


ULBN_PUBLIC int ulbi_init_copy(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* src) {
  return ulbi_set_copy(alloc, ulbi_init(dst), src);
}
ULBN_PUBLIC void ulbi_init_move(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbi_t* src) {
  (void)alloc;
  *dst = *src;
  ulbi_init(src);
}
ULBN_PUBLIC int ulbi_init_ulong(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ulong_t l) {
  return ulbi_set_ulong(alloc, ulbi_init(dst), l);
}
ULBN_PUBLIC int ulbi_init_slong(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_slong_t l) {
  return ulbi_set_slong(alloc, ulbi_init(dst), l);
}
ULBN_PUBLIC int ulbi_init_usize(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t l) {
  return ulbi_set_usize(alloc, ulbi_init(dst), l);
}
ULBN_PUBLIC int ulbi_init_ssize(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ssize_t l) {
  return ulbi_set_ssize(alloc, ulbi_init(dst), l);
}
ULBN_PUBLIC int ulbi_init_2exp_usize(const ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t n) {
  return ulbi_set_2exp_usize(alloc, ulbi_init(dst), n);
}
ULBN_PUBLIC int ulbi_init_2exp(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* n) {
  return ulbi_set_2exp(alloc, ulbi_init(dst), n);
}
ULBN_PUBLIC int ulbi_init_string(const ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, int base) {
  return ulbi_set_string(alloc, ulbi_init(dst), str, base);
}
ULBN_PUBLIC int ulbi_init_data(
  const ulbn_alloc_t* alloc, ulbi_t* dst,          /* */
  const void* limbs, size_t len, int is_big_endian /* */
) {
  return ulbi_set_data(alloc, ulbi_init(dst), limbs, len, is_big_endian);
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
      ulbn_default_alloc(), 0, _ulbn_fileprinter, fp, _ulbi_limbs(bi), _ulbn_abs_size(bi->len),
      ulbn_prepare_baseconv(10)
    );
  }
  fputc('\n', fp);
}
#endif


ULBN_PUBLIC int ulbi_comp(const ulbi_t* ao, const ulbi_t* bo) {
  int a_positive = (ao->len >= 0), cmp;
  if(ao->len != bo->len)
    return ao->len < bo->len ? -1 : 1;
  cmp = ulbn_cmpn(_ulbi_limbs(ao), _ulbi_limbs(bo), _ulbn_abs_size(bo->len));
  return a_positive ? cmp : -cmp;
}
ULBN_PUBLIC int ulbi_comp_limb(const ulbi_t* ao, ulbn_limb_t b) {
  const ulbn_ssize_t an = ao->len;
  if(an == 1) {
    const ulbn_limb_t a = _ulbi_limbs(ao)[0];
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
    const ulbn_limb_t a = _ulbi_limbs(ao)[0];
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
  return _ulbi_comp_ulong(_ulbi_limbs(ao), ao->len, b);
}
ULBN_PUBLIC int ulbi_comp_slong(const ulbi_t* ao, ulbn_slong_t b) {
  return b >= 0 ? _ulbi_comp_ulong(_ulbi_limbs(ao), ao->len, _ulbn_from_pos_slong(b))
                : -_ulbi_comp_ulong(_ulbi_limbs(ao), -ao->len, _ulbn_from_neg_slong(b));
}


ULBN_PUBLIC int ulbi_eq(const ulbi_t* ao, const ulbi_t* bo) {
  if(ao->len != bo->len)
    return 0;
  return ulbn_cmp(_ulbi_limbs(ao), _ulbn_abs_size(ao->len), _ulbi_limbs(bo), _ulbn_abs_size(bo->len)) == 0;
}
ULBN_PUBLIC int ulbi_eq_limb(const ulbi_t* ao, ulbn_limb_t b) {
  return b ? (ao->len == 1 && _ulbi_limbs(ao)[0] == b) : (ao->len == 0);
}
ULBN_PUBLIC int ulbi_eq_slimb(const ulbi_t* ao, ulbn_slimb_t b) {
  if(b == 0)
    return ao->len == 0;
  else if(b > 0)
    return ao->len == 1 && _ulbi_limbs(ao)[0] == _ulbn_from_pos_slimb(b);
  else
    return ao->len == -1 && _ulbi_limbs(ao)[0] == _ulbn_from_neg_slimb(b);
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
  return _ulbi_eq_ulong(_ulbi_limbs(ao), ao->len, b);
}
ULBN_PUBLIC int ulbi_eq_slong(const ulbi_t* ao, ulbn_slong_t b) {
  return b >= 0 ? _ulbi_eq_ulong(_ulbi_limbs(ao), ao->len, _ulbn_from_pos_slong(b))
                : _ulbi_eq_ulong(_ulbi_limbs(ao), -ao->len, _ulbn_from_neg_slong(b));
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
  ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
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
  int cmp = ulbn_cmp(_ulbi_limbs(ao), an, _ulbi_limbs(bo), bn);
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
  int positive = (ao->len >= 0), err;
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
  if(_ulbn_same_sign(ao->len, bo->len))
    err = _ulbi_add_ignore_sign(alloc, ro, ao, an, bo, bn);
  else
    err = _ulbi_sub_ignore_sign(alloc, ro, ao, an, bo, bn);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}
ULBN_PUBLIC int ulbi_sub(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
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
  const ulbn_alloc_t* alloc, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_usize_t an,     /* */
  ulbn_limb_t b                          /* */
) {
  ulbn_limb_t* rp;

  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);

  rp[an] = ulbn_add1(rp, _ulbi_limbs(ao), an, b);
  an += (rp[an] != 0);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
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
ULBN_PUBLIC int ulbi_add_limb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  int positive = (ao->len >= 0), err;
  if(ao->len >= 0)
    err = _ulbi_add_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(ao->len), b);
  else
    err = _ulbi_sub_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(-ao->len), b);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}
ULBN_PUBLIC int ulbi_sub_limb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  int positive = (ao->len >= 0), err;
  if(ao->len >= 0)
    err = _ulbi_sub_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(ao->len), b);
  else
    err = _ulbi_add_limb_ignore_sign(alloc, ro, ao, ulbn_cast_usize(-ao->len), b);
  ro->len = _ulbn_to_ssize(positive, ro->len);
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
  return b >= 0 ? ulbi_add_limb(alloc, ro, ao, _ulbn_from_pos_slimb(b))
                : ulbi_sub_limb(alloc, ro, ao, _ulbn_from_neg_slimb(b));
}
ULBN_PUBLIC int ulbi_sub_slimb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  return b >= 0 ? ulbi_sub_limb(alloc, ro, ao, _ulbn_from_pos_slimb(b))
                : ulbi_add_limb(alloc, ro, ao, _ulbn_from_neg_slimb(b));
}
ULBN_PUBLIC int ulbi_slimb_sub(const ulbn_alloc_t* alloc, ulbi_t* ro, ulbn_slimb_t a, const ulbi_t* bo) {
  int err;
  if(a >= 0)
    err = ulbi_limb_sub(alloc, ro, _ulbn_from_pos_slimb(a), bo);
  else {
    err = ulbi_add_limb(alloc, ro, bo, _ulbn_from_neg_slimb(a));
    ro->len = -ro->len;
  }
  return err;
}


ULBN_PUBLIC int ulbi_mul_limb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  int positive = (ao->len >= 0);
  ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_limb_t* rp;

  if(ul_unlikely(ao->len == 0 || b == 0)) {
    _ulbi_set_zero(ro);
    return 0;
  }
  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  rp[an] = ulbn_mul1(rp, _ulbi_limbs(ao), an, b);
  an += (rp[an] != 0);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(positive, an);
  return 0;
}
ULBN_PUBLIC int ulbi_mul_slimb(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  if(b >= 0) {
    return ulbi_mul_limb(alloc, ro, ao, _ulbn_from_pos_slimb(b));
  } else {
    const int err = ulbi_mul_limb(alloc, ro, ao, _ulbn_from_neg_slimb(b));
    ro->len = -ro->len;
    return err;
  }
}
ULBN_PUBLIC int ulbi_mul(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  int positive = _ulbn_same_sign(ao->len, bo->len), err;
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
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
  ULBN_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(positive, rn);
  return 0;
}


ULBN_PRIVATE int _ulbi_divmod(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_usize_t an, int a_positive, /* */
  const ulbi_t* bo, ulbn_usize_t bn, int b_positive  /* */
) {
  const int positive = (a_positive == b_positive);
  int err = 0;
  ulbn_limb_t *qp = ul_nullptr, *rp = ul_nullptr;

  if(ul_unlikely(bn == 0)) {
    _ulbi_may_set_zero(qo);
    _ulbi_may_set_zero(ro);
    return ULBN_ERR_DIV_BY_ZERO;
  }
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
    qo->len = _ulbn_to_ssize(positive, qo->len);
  }
  if(ro) {
    ro->len = ulbn_cast_ssize(ulbn_rnorm(rp, bn));
    ro->len = _ulbn_to_ssize(a_positive, ro->len);
  }
  return err;
}
ULBN_PUBLIC int ulbi_divmod(const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  return _ulbi_divmod(
    alloc, qo, ro,                             /* */
    ao, _ulbn_abs_size(ao->len), ao->len >= 0, /* */
    bo, _ulbn_abs_size(bo->len), bo->len >= 0  /* */
  );
}
ULBN_PUBLIC int ulbi_div(const ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, const ulbi_t* bo) {
  return ulbi_divmod(alloc, qo, ul_nullptr, ao, bo);
}
ULBN_PUBLIC int ulbi_mod(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  return ulbi_divmod(alloc, ul_nullptr, ro, ao, bo);
}

ULBN_PUBLIC int ulbi_divmod_limb(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_limb_t* ro, /* */
  const ulbi_t* ao, ulbn_limb_t b                         /* */
) {
  int positive = (ao->len >= 0), err = 0;
  ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_limb_t* qp = ul_nullptr;
  const ulbn_limb_t* ap;

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

  if(qo) {
    qp = _ulbi_res(alloc, qo, an);
    ULBN_RETURN_IF_ALLOC_FAILED(qp, ULBN_ERR_NOMEM);
  }
  ap = _ulbi_limbs(ao);

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
    err = ulbn_divmod1(alloc, qp, ro, _ulbi_limbs(ao), _ulbn_abs_size(ao->len), b);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  if(qo) {
    qo->len = ulbn_cast_ssize(ulbn_rnorm(qp, an));
    qo->len = _ulbn_to_ssize(positive, qo->len);
  }
  if(ro && !positive && *ro != 0) {
    *ro = b - *ro;
    err = ULBN_ERR_INEXACT;
  }
  return err;
}
ULBN_PUBLIC int ulbi_div_limb(const ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, ulbn_limb_t b) {
  return ulbi_divmod_limb(alloc, qo, ul_nullptr, ao, b);
}
ULBN_PUBLIC int ulbi_mod_limb(const ulbn_alloc_t* alloc, ulbn_limb_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  return ulbi_divmod_limb(alloc, ul_nullptr, ro, ao, b);
}

ULBN_PUBLIC int ulbi_divmod_slimb(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_slimb_t* ro, /* */
  const ulbi_t* ao, ulbn_slimb_t _b                        /* */
) {
  int positive = (ao->len >= 0) == (_b >= 0), a_positive = ao->len >= 0, err = 0;
  ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_limb_t* qp = ul_nullptr;
  const ulbn_limb_t* ap;
  const ulbn_limb_t b = _b >= 0 ? _ulbn_from_pos_slimb(_b) : _ulbn_from_neg_slimb(_b);
  ulbn_limb_t r;

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

  if(qo) {
    qp = _ulbi_res(alloc, qo, an);
    ULBN_RETURN_IF_ALLOC_FAILED(qp, ULBN_ERR_NOMEM);
  }
  ap = _ulbi_limbs(ao);
  if(an == 1) {
    ulbn_limb_t a = ap[0];
    r = a % b;
    if(qp)
      qp[0] = a / b;
  } else {
    err = ulbn_divmod1(alloc, qp, &r, _ulbi_limbs(ao), _ulbn_abs_size(ao->len), b);
    ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  }
  if(qo) {
    qo->len = ulbn_cast_ssize(ulbn_rnorm(qp, an));
    qo->len = _ulbn_to_ssize(positive, qo->len);
  }
  if(ro)
    *ro = a_positive ? ul_static_cast(ulbn_slimb_t, r) : -ul_static_cast(ulbn_slimb_t, r);
  else
    err = r ? ULBN_ERR_INEXACT : 0;
  return err;
}
ULBN_PUBLIC int ulbi_div_slimb(const ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, ulbn_slimb_t b) {
  return ulbi_divmod_slimb(alloc, qo, ul_nullptr, ao, b);
}
ULBN_PUBLIC int ulbi_mod_slimb(const ulbn_alloc_t* alloc, ulbn_slimb_t* ro, const ulbi_t* ao, ulbn_slimb_t b) {
  return ulbi_divmod_slimb(alloc, ul_nullptr, ro, ao, b);
}

ULBN_PUBLIC int ulbi_divmod_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, const ulbi_t* bo,                /* */
  enum ULBN_ROUND_ENUM round_mode                    /* */
) {
  ulbi_t tqo[1] = {ULBI_INIT}, tro[1] = {ULBI_INIT};
  int err, op = 0;

  if(round_mode == ULBN_ROUND_DOWN)
    return ulbi_divmod(alloc, qo, ro, ao, bo);
  if(round_mode < ULBN_ROUND_DOWN || round_mode > ULBN_ROUND_FAIL) {
    _ulbi_may_set_zero(qo);
    _ulbi_may_set_zero(ro);
    return ULBN_ERR_INVALID;
  }

  err = _ulbi_divmod(
    alloc, tqo, tro,                           /* */
    ao, _ulbn_abs_size(ao->len), ao->len >= 0, /* */
    bo, _ulbn_abs_size(bo->len), bo->len >= 0  /* */
  );
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  if(err == ULBN_ERR_DIV_BY_ZERO || tro->len == 0)
    goto do_op;
  else if(round_mode == ULBN_ROUND_FAIL) {
    err = ULBN_ERR_INEXACT;
    goto do_op;
  }

  if(round_mode > ULBN_ROUND_CEILING)
    switch(ulbn_check_round(_ulbi_limbs(tro), _ulbn_abs_size(tro->len), _ulbi_limbs(bo), _ulbn_abs_size(bo->len))) {
    case -1:
      round_mode = ULBN_ROUND_DOWN;
      break;
    case 1:
      round_mode = ULBN_ROUND_UP;
      break;
    default:
      if(round_mode == ULBN_ROUND_HALF_ODD)
        round_mode = ulbi_is_odd(tqo) ? ULBN_ROUND_DOWN : ULBN_ROUND_UP;
      else if(round_mode == ULBN_ROUND_HALF_EVEN)
        round_mode = ulbi_is_even(tqo) ? ULBN_ROUND_DOWN : ULBN_ROUND_UP;
      else if(round_mode == ULBN_ROUND_HALF_DOWN)
        round_mode = ULBN_ROUND_DOWN;
      else /* if(round_mode == ULBN_ROUND_HALF_UP) */
        round_mode = ULBN_ROUND_UP;
    }

  if(round_mode == ULBN_ROUND_DOWN)
    op = 0;
  else if(round_mode == ULBN_ROUND_UP)
    op = _ulbn_same_sign(ao->len, bo->len) ? 1 : -1;
  else if(round_mode == ULBN_ROUND_CEILING)
    op = _ulbn_same_sign(ao->len, bo->len);
  else /* if(round_mode == ULBN_ROUND_FLOOR) */
    op = _ulbn_same_sign(ao->len, bo->len) - 1;

do_op:
  if(qo) {
    if(op == 0)
      ulbi_swap(qo, tqo);
    else {
      if(op == 1)
        err = ulbi_add_limb(alloc, qo, tqo, 1);
      else
        err = ulbi_sub_limb(alloc, qo, tqo, 1);
      ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    }
  }
  if(ro) {
    if(op == 0)
      ulbi_swap(ro, tro);
    else if(op == 1)
      err = ulbi_sub(alloc, ro, tro, bo);
    else
      err = ulbi_add(alloc, ro, tro, bo);
  } else
    err = (tro->len == 0 ? 0 : ULBN_ERR_INEXACT);

cleanup:
  ulbi_deinit(alloc, tqo);
  ulbi_deinit(alloc, tro);
  return err;
}
ULBN_PUBLIC int ulbi_div_ex(
  const ulbn_alloc_t* alloc, ulbi_t* qo, /* */
  const ulbi_t* ao, const ulbi_t* bo,    /* */
  enum ULBN_ROUND_ENUM round_mode        /* */
) {
  return ulbi_divmod_ex(alloc, qo, ul_nullptr, ao, bo, round_mode);
}
ULBN_PUBLIC int ulbi_mod_ex(
  const ulbn_alloc_t* alloc, ulbi_t* ro, /* */
  const ulbi_t* ao, const ulbi_t* bo,    /* */
  enum ULBN_ROUND_ENUM round_mode        /* */
) {
  return ulbi_divmod_ex(alloc, ul_nullptr, ro, ao, bo, round_mode);
}


ULBN_PRIVATE int _ulbi_divmod_2exp(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro,        /* */
  const ulbi_t* ao, const ulbn_usize_t idx, const int shift /* */
) {
  const int a_pos = ao->len >= 0;
  const ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_usize_t qn;
  ulbn_limb_t cy = 0;
  ulbn_limb_t *qp, *rp;
  const ulbn_limb_t* ap;
  int err = 0, rempty;

  if(an == 0) {
    _ulbi_may_set_zero(qo);
    _ulbi_may_set_zero(ro);
    return 0;
  }
  if(an <= idx) {
    _ulbi_may_set_zero(qo);
    if(ro)
      err = ulbi_set_copy(alloc, ro, ao);
    else
      err = an ? ULBN_ERR_INEXACT : 0;
    return err;
  }

  if(ul_unlikely(qo == ro))
    qo = ul_nullptr;
  rempty = !ulbn_is0(_ulbi_limbs(ao), idx);
  qn = an - idx;

  if(ro) {
    rp = _ulbi_res(alloc, ro, idx + (shift != 0));
    ULBN_RETURN_IF_ALLOC_COND(rp == ul_nullptr && (idx + (shift != 0)) != 0, ULBN_ERR_NOMEM);
    ap = _ulbi_limbs(ao);
    ulbn_maycopy(rp, ap, idx);
  }

  if(shift)
    cy = _ulbi_limbs(ao)[idx] & ul_static_cast(ulbn_limb_t, ULBN_LIMB_SHL(2u, shift - 1) - 1u);
  if(qo) {
    qp = _ulbi_res(alloc, qo, qn);
    ULBN_RETURN_IF_ALLOC_FAILED(qp, ULBN_ERR_NOMEM);
    ap = _ulbi_limbs(ao);
    if(shift)
      ulbn_shr(qp, ap + idx, qn, shift);
    else
      ulbn_fcopy(qp, ap + idx, qn);
    qn = ulbn_rnorm(qp, qn);
    qo->len = _ulbn_to_ssize(a_pos, qn);
  }

  if(ro) {
    rp = _ulbi_limbs(ro);
    if(cy) {
      rp[idx] = cy;
      ro->len = _ulbn_to_ssize(a_pos, idx + 1);
    } else {
      const ulbn_usize_t rn = ulbn_rnorm(rp, idx);
      ro->len = _ulbn_to_ssize(a_pos, rn);
    }
  } else
    err = ul_static_cast(ulbn_limb_t, rempty) | cy ? ULBN_ERR_INEXACT : 0;
  return err;
}

ULBN_PUBLIC int ulbi_divmod_2exp_usize(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_usize_t e                   /* */
) {
  return _ulbi_divmod_2exp(alloc, qo, ro, ao, e / ULBN_LIMB_BITS, ul_static_cast(int, e % ULBN_LIMB_BITS));
}
ULBN_PUBLIC int ulbi_div_2exp_usize(const ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, ulbn_usize_t e) {
  return ulbi_divmod_2exp_usize(alloc, qo, ul_nullptr, ao, e);
}
ULBN_PUBLIC int ulbi_mod_2exp_usize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t e) {
  return ulbi_divmod_2exp_usize(alloc, ul_nullptr, ro, ao, e);
}

ULBN_PUBLIC int ulbi_divmod_2exp_ssize(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, ulbn_ssize_t e                   /* */
) {
  int err;
  if(e >= 0)
    return ulbi_divmod_2exp_usize(alloc, qo, ro, ao, ulbn_cast_usize(e));
  err = ulbi_sal_usize(alloc, qo, ao, _ulbn_from_neg_ssize(e));
  _ulbi_may_set_zero(ro);
  return err;
}
ULBN_PUBLIC int ulbi_div_2exp_ssize(const ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, ulbn_ssize_t e) {
  return ulbi_divmod_2exp_ssize(alloc, qo, ul_nullptr, ao, e);
}
ULBN_PUBLIC int ulbi_mod_2exp_ssize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t e) {
  return ulbi_divmod_2exp_ssize(alloc, ul_nullptr, ro, ao, e);
}

ULBN_PRIVATE int _ulbi_sal(
  const ulbn_alloc_t* alloc, ulbi_t* ro,                    /* */
  const ulbi_t* ao, const ulbn_usize_t idx, const int shift /* */
);
ULBN_PUBLIC int ulbi_divmod_2exp(
  const ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, /* */
  const ulbi_t* ao, const ulbi_t* eo                 /* */
) {
  ulbn_usize_t idx;
  int shift, err;

  shift = ulbn_to_bit_info(_ulbi_limbs(eo), _ulbn_abs_size(eo->len), &idx);
  if(shift < 0) {
    if(eo->len < 0)
      return ULBN_ERR_EXCEED_RANGE;
    shift = 0;
    idx = ULBN_USIZE_MAX;
  }

  if(eo->len >= 0)
    return _ulbi_divmod_2exp(alloc, qo, ro, ao, idx, shift);
  else {
    err = _ulbi_sal(alloc, qo, ao, idx, shift);
    _ulbi_may_set_zero(ro);
    return err;
  }
}
ULBN_PUBLIC int ulbi_div_2exp(const ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, const ulbi_t* eo) {
  return ulbi_divmod_2exp(alloc, qo, ul_nullptr, ao, eo);
}
ULBN_PUBLIC int ulbi_mod_2exp(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* eo) {
  return ulbi_divmod_2exp(alloc, ul_nullptr, ro, ao, eo);
}


ULBN_PUBLIC int ulbi_pow_usize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
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
ULBN_PUBLIC int ulbi_pow_ssize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t b) {
  if(ao->len == 0) {
    _ulbi_set_zero(ro);
    return ul_unlikely(b < 0) ? ULBN_ERR_DIV_BY_ZERO : 0;
  }
  if(ul_unlikely(b < 0)) {
    _ulbi_set_zero(ro);
    return ULBN_ERR_INEXACT;
  }
  return ulbi_pow_usize(alloc, ro, ao, ulbn_cast_usize(b));
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
      j = ul_static_cast(unsigned, ULBN_LIMB_BITS);
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

  /* e_n1 = e - 1, x = 2 ** ceil(bits_width(a) / e) + 1 */
  err = ulbi_sub_limb(alloc, eo_n1, eo, 1);
  ulbn_assert(err != ULBN_ERR_EXCEED_RANGE);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  err = ulbi_abs_bit_width(alloc, yo, ao);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  cy = ulbi_div(alloc, yo, yo, eo);
  ULBN_DO_IF_ALLOC_COND(cy < 0, goto cleanup;);
  err = ulbi_add_limb(alloc, yo, yo, 1 + (cy == ULBN_ERR_INEXACT));
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
  err = ulbi_set_2exp(alloc, xo, yo);
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
#if 0
  ulbi_dprint(stdout, "bits = ", yo);
  ulbi_dprint(stdout, "e - 1 = ", eo_n1);
  putchar('\n');
#endif

  ulbi_set_limb(yo, 1);
  while(ulbi_comp(xo, yo) > 0) {
#if 0
    ulbi_dprint(stdout, "x = ", xo);
    ulbi_dprint(stdout, "y = ", yo);
#endif

    /* x = (x * (e - 1) + y) / e */
    /* y = abs(a) / (x ** (e - 1)) */
    err = ulbi_mul(alloc, xo, xo, eo_n1);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    err = ulbi_add(alloc, xo, xo, yo);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    err = ulbi_div(alloc, xo, xo, eo);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
    err = ulbi_pow(alloc, to, xo, eo_n1);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    err = _ulbi_divmod(alloc, yo, ul_nullptr, ao, _ulbn_abs_size(ao->len), 1, to, ulbn_cast_usize(to->len), 1);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  }

  ulbn_assert(!ulbi_eq_limb(xo, 0));
  if(sign)
    xo->len = -xo->len;
  err = ulbi_mul(alloc, to, to, xo);
  ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
  if(ro) {
    err = ulbi_sub(alloc, ro, ao, to);
    ulbn_assert(err != ULBN_ERR_EXCEED_RANGE);
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
ULBN_PUBLIC int ulbi_root(const ulbn_alloc_t* alloc, ulbi_t* so, const ulbi_t* ao, const ulbi_t* eo) {
  return ulbi_rootrem(alloc, so, ul_nullptr, ao, eo);
}


ULBN_PUBLIC int ulbi_and(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
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
      rp[sep] = ap[sep] & _ulbn_neg_(bp[sep]);
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
      rp[sep] = _ulbn_neg_(ap[sep]) & bp[sep];
      if(sep < bn)
        ulbn_and_nocy(rp + sep + 1, bp + sep + 1, ap + sep + 1, ULBN_LIMB_MAX, bn - sep - 1);
      ro->len = ulbn_cast_ssize(ulbn_rnorm(rp, bn));
    }
  } else {
    rp = _ulbi_res(alloc, ro, an + 1);
    ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
    rp[an] = ulbn_and(rp, 1, _ulbi_limbs(ao), an, 1, _ulbi_limbs(bo), bn, 1);
    an = ulbn_rnorm(rp, an + 1);
    ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
    ro->len = -ulbn_cast_ssize(an);
  }
  return 0;
}
ULBN_PUBLIC int ulbi_or(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
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
    ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
    ro->len = -ulbn_cast_ssize(an);
  }
  return 0;
}
ULBN_PUBLIC int ulbi_xor(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  ulbn_limb_t a_cy, b_cy;
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
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
    const ulbn_limb_t r_cy = a_cy ^ b_cy;
    rp = _ulbi_res(alloc, ro, an + 1);
    ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
    rp[an] = ulbn_xor(rp, r_cy, _ulbi_limbs(ao), an, a_cy, _ulbi_limbs(bo), bn, b_cy);
    an = ulbn_rnorm(rp, an + 1);
    ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
    ro->len = _ulbn_to_ssize(!r_cy, an);
  }
  return 0;
}
ULBN_PUBLIC int ulbi_com(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao) {
  ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_limb_t* rp;

  rp = _ulbi_res(alloc, ro, an + (ao->len >= 0));
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
  if(ao->len >= 0) {
    rp[an] = ulbn_add1(rp, _ulbi_limbs(ao), an, 1);
    an += (rp[an] != 0);
    ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
    ro->len = -ulbn_cast_ssize(an);
  } else {
    ulbn_sub1(rp, _ulbi_limbs(ao), an, 1);
    an = ulbn_rnorm(rp, an);
    ro->len = ulbn_cast_ssize(an);
  }
  return 0;
}

ul_static_assert(_ULBN_LIMB_BITS < _ULBN_LIMB_SIGNBIT, "ulbn_usize_t is too large");
ULBN_PRIVATE int _ulbi_sal(
  const ulbn_alloc_t* alloc, ulbi_t* ro,                    /* */
  const ulbi_t* ao, const ulbn_usize_t idx, const int shift /* */
) {
  const ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_usize_t rn;
  ulbn_limb_t* rp;

  if(an == 0) {
    _ulbi_set_zero(ro);
    return 0;
  }
  rn = an + idx;

  if(shift) {
    ULBN_RETURN_IF_SSIZE_COND(rn > ULBN_USIZE_LIMIT - 1, ULBN_ERR_EXCEED_RANGE);
    ++rn;
    rp = _ulbi_res(alloc, ro, rn);
    rp[rn - 1] = ulbn_shl(rp + idx, _ulbi_limbs(ao), an, shift);
  } else {
    rp = _ulbi_res(alloc, ro, rn);
    ulbn_rcopy(rp + idx, _ulbi_limbs(ao), an);
  }

  ulbn_fill0(rp, idx);
  rn = ulbn_rnorm(rp, rn);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(ao->len >= 0, rn);
  return 0;
}
ULBN_PRIVATE int _ulbi_sar(
  const ulbn_alloc_t* alloc, ulbi_t* ro,                    /* */
  const ulbi_t* ao, const ulbn_usize_t idx, const int shift /* */
) {
  const int a_neg = ao->len < 0;
  const ulbn_usize_t an = _ulbn_abs_size(ao->len);
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
    ro->len = -a_neg;
    return 0;
  }

  rn = an - idx;
  rp = _ulbi_res(alloc, ro, rn + ul_static_cast(unsigned, a_neg));
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
  ro->len = _ulbn_to_ssize(!a_neg, rn);
  return 0;
}
ULBN_PUBLIC int ulbi_sal_usize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  const ulbn_usize_t idx = b / ULBN_LIMB_BITS;
  const int shift = ul_static_cast(int, b % ULBN_LIMB_BITS);
  return _ulbi_sal(alloc, ro, ao, idx, shift);
}
ULBN_PUBLIC int ulbi_sar_usize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  const ulbn_usize_t idx = b / ULBN_LIMB_BITS;
  const int shift = ul_static_cast(int, b % ULBN_LIMB_BITS);
  return _ulbi_sar(alloc, ro, ao, idx, shift);
}
ULBN_PUBLIC int ulbi_sal_ssize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t b) {
  return b >= 0 ? ulbi_sal_usize(alloc, ro, ao, _ulbn_from_pos_ssize(b))
                : ulbi_sar_usize(alloc, ro, ao, _ulbn_from_neg_ssize(b));
}
ULBN_PUBLIC int ulbi_sar_ssize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t b) {
  return b >= 0 ? ulbi_sar_usize(alloc, ro, ao, _ulbn_from_pos_ssize(b))
                : ulbi_sal_usize(alloc, ro, ao, _ulbn_from_neg_ssize(b));
}
ULBN_PUBLIC int ulbi_sal(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbn_usize_t idx;
  int shift;
  if(b->len >= 0) {
    shift = ulbn_to_bit_info(_ulbi_limbs(b), ulbn_cast_usize(b->len), &idx);
    if(ul_unlikely(shift < 0 || idx > ULBN_SSIZE_LIMIT))
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
    if(ul_unlikely(shift < 0 || idx > ULBN_SSIZE_LIMIT))
      return ULBN_ERR_EXCEED_RANGE;
    return _ulbi_sal(alloc, ro, ao, idx, shift);
  }
}


ULBN_PRIVATE int _ulbi_testbit(const ulbi_t* o, ulbn_usize_t idx, int shift) {
  ulbn_assert(0 <= shift && ul_static_cast(unsigned, shift) < ULBN_LIMB_BITS);
  return (ulbn_limb(_ulbi_limbs(o), _ulbn_abs_size(o->len), o->len < 0, idx) & ULBN_LIMB_SHL(1, shift)) != 0;
}
ULBN_PRIVATE int _ulbi_setbit(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t idx, int shift) {
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
  ulbn_usize_t n = _ulbn_abs_size(o->len);
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
ULBN_PUBLIC int ulbi_setbit_usize(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k) {
  ulbn_usize_t idx = k / ULBN_LIMB_BITS;
  int shift = ul_static_cast(int, k % ULBN_LIMB_BITS);
  return _ulbi_testbit(o, idx, shift) ? 1 : _ulbi_setbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_resetbit_usize(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k) {
  ulbn_usize_t idx = k / ULBN_LIMB_BITS;
  int shift = ul_static_cast(int, k % ULBN_LIMB_BITS);
  return !_ulbi_testbit(o, idx, shift) ? 0 : _ulbi_resetbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_combit_usize(const ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k) {
  ulbn_usize_t idx = k / ULBN_LIMB_BITS;
  int shift = ul_static_cast(int, k % ULBN_LIMB_BITS);
  return _ulbi_testbit(o, idx, shift) ? _ulbi_resetbit(alloc, o, idx, shift) : _ulbi_setbit(alloc, o, idx, shift);
}

ULBN_PUBLIC int ulbi_testbit(const ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limbs(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return o->len >= 0 ? 0 : 1;
  return _ulbi_testbit(o, idx, shift);
}
ULBN_PUBLIC int ulbi_setbit(const ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limbs(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return o->len >= 0 ? ULBN_ERR_EXCEED_RANGE : 1;
  if(_ulbi_testbit(o, idx, shift))
    return 1;
  if(ul_unlikely(idx > ULBN_SSIZE_LIMIT - (o->len >= 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_setbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_resetbit(const ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limbs(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return o->len >= 0 ? 0 : ULBN_ERR_EXCEED_RANGE;
  if(!_ulbi_testbit(o, idx, shift))
    return 0;
  if(ul_unlikely(idx > ULBN_SSIZE_LIMIT - (o->len < 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_resetbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_combit(const ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k) {
  ulbn_usize_t idx;
  int shift;

  if(ul_unlikely(k->len < 0))
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limbs(k), ulbn_cast_usize(k->len), &idx);
  if(ul_unlikely(shift < 0))
    return ULBN_ERR_EXCEED_RANGE;
  if(ul_unlikely(idx > ULBN_SSIZE_LIMIT - 1))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_testbit(o, idx, shift) ? _ulbi_resetbit(alloc, o, idx, shift) : _ulbi_setbit(alloc, o, idx, shift);
}


ULBN_PRIVATE int _ulbi_as_uint(
  const ulbn_alloc_t* alloc, ulbi_t* ro,                      /* */
  const ulbi_t* ao, ulbn_usize_t idx, int shift, int need_com /* */
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

  ULBN_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = ulbn_cast_ssize(rn);
  return 0;
}
ULBN_PRIVATE int _ulbi_as_int(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t idx, int shift) {
  const ulbn_limb_t* ap;
  int err, positive, need_com;

  positive = (_ulbi_testbit(ao, idx, shift) == 0);
  ap = _ulbi_limbs(ao);
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

ULBN_PUBLIC int ulbi_as_uint_usize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  return _ulbi_as_uint(alloc, ro, ao, b / ULBN_LIMB_BITS, ul_static_cast(int, b % ULBN_LIMB_BITS), ao->len < 0);
}
ULBN_PUBLIC int ulbi_as_int_usize(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  if(ul_unlikely(b == 0)) {
    _ulbi_set_zero(ro);
    return 0;
  }
  return _ulbi_as_int(alloc, ro, ao, (b - 1) / ULBN_LIMB_BITS, ul_static_cast(int, (b - 1) % ULBN_LIMB_BITS));
}

ULBN_PUBLIC int ulbi_as_uint(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbn_usize_t idx;
  int shift;
  if(b->len < 0)
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limbs(b), ulbn_cast_usize(b->len), &idx);
  if(ul_unlikely(shift < 0)) {
    idx = ULBN_USIZE_MAX;
    shift = 0;
  }
  if(ul_unlikely(ao->len < 0 && idx > ULBN_SSIZE_LIMIT - (shift != 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_as_uint(alloc, ro, ao, idx, shift, ao->len < 0);
}
ULBN_PUBLIC int ulbi_as_int(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b) {
  ulbn_usize_t idx;
  int shift;
  if(b->len < 0)
    return ULBN_ERR_EXCEED_RANGE;
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
    shift = ULBN_LIMB_BITS - 1;
  } else
    --shift;
  return _ulbi_as_int(alloc, ro, ao, idx, shift);
}


ULBN_PUBLIC int ulbi_is_2pow(const ulbi_t* o) {
  return ulbn_is_2pow(_ulbi_limbs(o), _ulbn_abs_size(o->len));
}
ULBN_PUBLIC ulbn_usize_t ulbi_ctz_usize(const ulbi_t* ro, ulbn_usize_t* p_rh) {
  return ulbn_ctz(_ulbi_limbs(ro), _ulbn_abs_size(ro->len), p_rh);
}
ULBN_PUBLIC ulbn_usize_t ulbi_cto_usize(const ulbi_t* ro, ulbn_usize_t* p_rh) {
  return ulbn_cto(_ulbi_limbs(ro), _ulbn_abs_size(ro->len), p_rh);
}
ULBN_PUBLIC ulbn_usize_t ulbi_abs_popcount_usize(const ulbi_t* ro, ulbn_usize_t* p_rh) {
  return ulbn_popcount(_ulbi_limbs(ro), _ulbn_abs_size(ro->len), p_rh);
}
ULBN_PUBLIC ulbn_usize_t ulbi_abs_bit_width_usize(const ulbi_t* ro, ulbn_usize_t* p_rh) {
  ulbn_usize_t n = _ulbn_abs_size(ro->len);
  if(n == 0) {
    if(p_rh)
      *p_rh = 0;
    return 0;
  } else
    return ulbn_bit_width(_ulbi_limbs(ro), n, p_rh);
}

ULBN_PUBLIC int ulbi_ctz(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro) {
  ulbn_usize_t rl, rh;
  ulbn_limb_t* ptr = _ulbi_res(alloc, dst, ULBN_MERGE_USIZE_LEN);
  if(ul_unlikely(ptr == ul_nullptr))
    return ULBN_ERR_NOMEM;
  rl = ulbn_ctz(_ulbi_limbs(ro), _ulbn_abs_size(ro->len), &rh);
  dst->len = ulbn_cast_ssize(ulbn_merge_usize(ptr, rl, rh));
  return 0;
}
ULBN_PUBLIC int ulbi_cto(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro) {
  ulbn_usize_t rl, rh;
  ulbn_limb_t* ptr = _ulbi_res(alloc, dst, ULBN_MERGE_USIZE_LEN);
  if(ul_unlikely(ptr == ul_nullptr))
    return ULBN_ERR_NOMEM;
  rl = ulbn_cto(_ulbi_limbs(ro), _ulbn_abs_size(ro->len), &rh);
  dst->len = ulbn_cast_ssize(ulbn_merge_usize(ptr, rl, rh));
  return 0;
}
ULBN_PUBLIC int ulbi_abs_popcount(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro) {
  ulbn_usize_t rl, rh;
  ulbn_limb_t* ptr = _ulbi_res(alloc, dst, ULBN_MERGE_USIZE_LEN);
  if(ul_unlikely(ptr == ul_nullptr))
    return ULBN_ERR_NOMEM;
  rl = ulbn_popcount(_ulbi_limbs(ro), _ulbn_abs_size(ro->len), &rh);
  dst->len = ulbn_cast_ssize(ulbn_merge_usize(ptr, rl, rh));
  return 0;
}
ULBN_PUBLIC int ulbi_abs_bit_width(const ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro) {
  ulbn_usize_t rl, rh;
  ulbn_limb_t* ptr;

  if(ro->len == 0) {
    _ulbi_set_zero(dst);
    return 0;
  }

  ptr = _ulbi_res(alloc, dst, ULBN_MERGE_USIZE_LEN);
  if(ul_unlikely(ptr == ul_nullptr))
    return ULBN_ERR_NOMEM;
  rl = ulbn_bit_width(_ulbi_limbs(ro), _ulbn_abs_size(ro->len), &rh);
  dst->len = ulbn_cast_ssize(ulbn_merge_usize(ptr, rl, rh));
  return 0;
}


ULBN_PUBLIC ulbn_limb_t ulbi_to_limb(const ulbi_t* src) {
  if(src->len == 0)
    return 0;
  return src->len > 0 ? _ulbi_limbs(src)[0] : ul_static_cast(ulbn_limb_t, 0u - _ulbi_limbs(src)[0]);
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
  return src->len ? ul_static_cast(ulbn_ulong_t, _ulbi_limbs(src)[0]) : 0u;
#else
  static ul_constexpr const ulbn_usize_t N_LIMIT =
    (sizeof(ulbn_ulong_t) * CHAR_BIT + ULBN_LIMB_BITS - 1) / ULBN_LIMB_BITS;
  ulbn_usize_t n = _ulbn_abs_size(src->len);
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
  return src->len ? ul_static_cast(ulbn_usize_t, _ulbi_limbs(src)[0]) : 0u;
#else
  static ul_constexpr const ulbn_usize_t N_LIMIT =
    (sizeof(ulbn_usize_t) * CHAR_BIT + ULBN_LIMB_BITS - 1) / ULBN_LIMB_BITS;
  ulbn_usize_t n = _ulbn_abs_size(src->len);
  const ulbn_limb_t* p = _ulbi_limbs(src);
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
  return _ulbi_limbs(src)[0] < ULBN_LIMB_SIGNBIT;
#else
  if(src->len == 1)
    return _ulbi_limbs(src)[0] < ULBN_LIMB_SIGNBIT;
  else
    return _ulbi_limbs(src)[0] <= ULBN_LIMB_SIGNBIT;
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


ULBN_PRIVATE int _ulbi_write0(ulbn_printer_t* printer, void* opaque, size_t len) {
  static const char ONLY_ZERO[9] = "00000000";
  while(len >= 8) {
    if(ul_unlikely(printer(opaque, ONLY_ZERO, 8)))
      return ULBN_ERR_EXTERNAL;
    len -= 8;
  }
  if(ul_unlikely(printer(opaque, ONLY_ZERO, len)))
    return ULBN_ERR_EXTERNAL;
  return 0;
}
#define ULBN_CONV2PRINT_GENERIC_THRESHOLD 2048
ULBN_PRIVATE int _ulbi_print_ex(
  const ulbn_alloc_t* alloc,              /* */
  ulbn_printer_t* printer, void* opaque,  /* */
  ulbi_t* ao, int base, size_t desire_len /* */
) {
  ulbn_usize_t bitw_low, bitw_high;
  ulbn_usize_t pow;
  ulbi_t qo[1] = {ULBI_INIT}, _do[1] = {ULBI_INIT};
  int err;

  ulbn_assert(ao->len > 0);

  while(ao->len > ULBN_CONV2PRINT_GENERIC_THRESHOLD) {
    bitw_low = ulbn_bit_width(_ulbi_limbs(ao), ulbn_cast_usize(ao->len), &bitw_high);
    ++bitw_low;
    bitw_high += (bitw_low == 0);
    pow = ulbn_measure_conv2_size(bitw_low, bitw_high, base, 0) >> 1;
    if(ul_unlikely(pow == ULBN_USIZE_MAX))
      return ULBN_ERR_EXCEED_RANGE;
    ulbi_set_limb(_do, ul_static_cast(ulbn_limb_t, base));
    err = ulbi_pow_usize(alloc, _do, _do, pow);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);

    err = ulbi_divmod(alloc, qo, ao, ao, _do);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    ulbi_deinit(alloc, _do);

    err = _ulbi_print_ex(alloc, printer, opaque, qo, base, desire_len > pow ? desire_len - pow : 0);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    desire_len = pow;
  }

  if(ao->len != 0)
    err = ulbn_conv2print_generic(
      alloc, desire_len, printer, opaque, _ulbi_limbs(ao), ulbn_cast_usize(ao->len),
      ulbn_prepare_baseconv(ul_static_cast(ulbn_limb_t, base))
    );
  else
    err = _ulbi_write0(printer, opaque, desire_len);

cleanup:
  ulbi_deinit(alloc, qo);
  ulbi_deinit(alloc, _do);
  return err;
}

ULBN_PUBLIC int ulbi_print_ex(
  const ulbn_alloc_t* alloc,             /* */
  ulbn_printer_t* printer, void* opaque, /* */
  const ulbi_t* ao, int base             /* */
) {
  ulbi_t ro[1] = {ULBI_INIT};
  int err;

  if(ul_unlikely(base < 2 || base > 36))
    return ULBN_ERR_EXCEED_RANGE;
  if(ao->len == 0)
    return ul_unlikely(printer(opaque, "0", 1)) ? ULBN_ERR_EXTERNAL : 0;
  if(ao->len < 0 && ul_unlikely(printer(opaque, "-", 1)))
    return ULBN_ERR_EXTERNAL;

  err = ulbi_abs(alloc, ro, ao);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  err = _ulbi_print_ex(alloc, printer, opaque, ro, base, 0);
  ulbi_deinit(alloc, ro);
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
  const ulbn_usize_t an = _ulbn_abs_size(ao->len);
  _ulbn_strprinter_t printer;
  int err;

  *p_len = 0;
  *p_alloced = 0;

  if(ul_unlikely(base < 2 || base > 36))
    return ul_nullptr;
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


#if ULBN_CONF_HAS_DOUBLE
ULBN_PRIVATE int _ulbn_feq(double a, double b) {
  return a >= b && a <= b;
}
ULBN_PUBLIC int ulbi_set_double(const ulbn_alloc_t* alloc, ulbi_t* dst, double x) {
  static ul_constexpr const double B = ul_static_cast(double, _ULBN_LIMB_SIGNBIT) * 2.0;
  static ul_constexpr const double Bi = 1.0 / (ul_static_cast(double, _ULBN_LIMB_SIGNBIT) * 2.0);
  ulbn_ssize_t ri, rn;
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
ULBN_PUBLIC int ulbi_init_double(const ulbn_alloc_t* alloc, ulbi_t* dst, double x) {
  return ulbi_set_double(alloc, ulbi_init(dst), x);
}
ULBN_PUBLIC double ulbi_to_double(const ulbi_t* src) {
  static ul_constexpr const double B = ul_static_cast(double, _ULBN_LIMB_SIGNBIT) * 2.0;
  const ulbn_usize_t n = _ulbn_abs_size(src->len);
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
    p[idx] = ulbn_rand(rng, shift);
  n = ulbn_rnorm(p, n);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
  dst->len = ulbn_cast_ssize(n);
  return 0;
}
ULBN_PUBLIC int ulbi_set_rand_usize(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_usize_t n) {
  ulbn_usize_t idx = n / ULBN_LIMB_BITS;
  const int shift = ul_static_cast(int, n % ULBN_LIMB_BITS);
  return _ulbi_set_rand(alloc, rng, dst, idx, shift);
}
ULBN_PUBLIC int ulbi_set_rand(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* n) {
  ulbn_usize_t idx;
  int shift;
  if(ul_unlikely(n->len < 0))
    return ULBN_ERR_EXCEED_RANGE;
  shift = ulbn_to_bit_info(_ulbi_limbs(n), ulbn_cast_usize(n->len), &idx);
  if(ul_unlikely(shift < 0 || idx > ULBN_SSIZE_LIMIT - (shift != 0)))
    return ULBN_ERR_EXCEED_RANGE;
  return _ulbi_set_rand(alloc, rng, dst, idx, shift);
}
ULBN_PUBLIC int ulbi_init_rand_usize(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_usize_t n) {
  return ulbi_set_rand_usize(alloc, rng, ulbi_init(dst), n);
}
ULBN_PUBLIC int ulbi_init_rand(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* n) {
  return ulbi_set_rand(alloc, rng, ulbi_init(dst), n);
}

ULBN_PUBLIC int ulbi_set_rand_range(const ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* limit) {
  ulbi_t nbits = ULBI_INIT;
  ulbi_t threshold = ULBI_INIT;
  ulbi_t tlimit = ULBI_INIT;
  int err;

  if(ul_unlikely(limit->len <= 0)) {
    _ulbi_set_zero(dst);
    return ULBN_ERR_EXCEED_RANGE;
  }
  err = ulbi_abs_bit_width(alloc, &nbits, limit);
  ulbn_assert(err != ULBN_ERR_EXCEED_RANGE);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  if(ulbi_is_2pow(limit)) {
    err = ulbi_sub_limb(alloc, &nbits, &nbits, 1);
    ulbn_assert(err == 0);
    err = ulbi_set_rand(alloc, rng, dst, &nbits);
    goto cleanup;
  }

  err = ulbi_set_2exp(alloc, &threshold, &nbits);
  ulbn_assert(err != ULBN_ERR_EXCEED_RANGE);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  err = ulbi_sub(alloc, &threshold, &threshold, limit);
  ulbn_assert(err != ULBN_ERR_EXCEED_RANGE);
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
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
  } while(ulbi_comp(dst, &threshold) < 0);
  err = ulbi_mod(alloc, dst, dst, limit);
cleanup:
  ulbi_deinit(alloc, &nbits);
  ulbi_deinit(alloc, &threshold);
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

ULBN_PUBLIC int ulbi_gcd(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
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

  an = _ulbn_abs_size(ao->len);
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
    return ulbi_gcd_limb(alloc, ro, ao, _ulbn_from_pos_slimb(b));
  else
    return ulbi_gcd_limb(alloc, ro, ao, _ulbn_from_neg_slimb(b));
}
ULBN_PUBLIC int ulbi_lcm(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
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

ULBN_PUBLIC int ulbi_gcdext(
  const ulbn_alloc_t* alloc, ulbi_t* ro, ulbi_t* uo, ulbi_t* vo, /* */
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
  ulbi_t tuo[1] = {ULBI_INIT};
  ulbi_t wo[1] = {ULBI_INIT}, xo[1] = {ULBI_INIT};
  ulbi_t qo[1] = {ULBI_INIT}, tro[1] = {ULBI_INIT};
  ulbi_t to[1] = {ULBI_INIT};
  ulbi_t bo[1] = {ULBI_INIT};
  int err;
  const int a_sign = ao->len < 0, b_sign = _bo->len < 0;

  if(ro == ul_nullptr)
    ro = tro;
  if(uo == ul_nullptr || ul_unlikely(uo == ro))
    uo = tuo;
  if(ul_unlikely(vo == uo || vo == ro))
    vo = ul_nullptr;

  err = ulbi_abs(alloc, ro, ao);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  err = ulbi_abs(alloc, bo, _bo);
  ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
  ulbi_set_limb(uo, 1);
  ulbi_set_limb(xo, 1);

  while(bo->len != 0) {
    err = ulbi_divmod(alloc, qo, ro, ro, bo);
    ULBN_DO_IF_ALLOC_COND(err < 0, goto cleanup;);
#if 0
    ulbi_dprint(stdout, "qo = ", qo);
    ulbi_dprint(stdout, "ro = ", ro);
#endif

    ulbi_swap(ro, bo);

    err = ulbi_mul(alloc, to, qo, wo);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    err = ulbi_sub(alloc, uo, uo, to);
    ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
    ulbi_swap(uo, wo);

#if 0
    ulbi_dprint(stdout, "uo = ", uo);
    ulbi_dprint(stdout, "wo = ", wo);
#endif

    if(vo) {
      err = ulbi_mul(alloc, to, qo, xo);
      ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
      err = ulbi_sub(alloc, vo, vo, to);
      ULBN_DO_IF_PUBLIC_COND(err < 0, goto cleanup;);
      ulbi_swap(vo, xo);

#if 0
      ulbi_dprint(stdout, "vo = ", vo);
      ulbi_dprint(stdout, "xo = ", xo);
#endif
    }
  }

  if(a_sign)
    uo->len = -uo->len;
  if(b_sign) {
    if(vo)
      vo->len = -vo->len;
  }
  if(ro == tro)
    err = ulbi_eq_limb(ro, 1) ? 0 : ULBN_ERR_INVALID;

cleanup:
  ulbi_deinit(alloc, tuo);
  ulbi_deinit(alloc, wo);
  ulbi_deinit(alloc, xo);
  ulbi_deinit(alloc, qo);
  ulbi_deinit(alloc, tro);
  ulbi_deinit(alloc, to);
  ulbi_deinit(alloc, bo);
  return err;
}
ULBN_PUBLIC int ulbi_invert(const ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* mo) {
  return ulbi_gcdext(alloc, ul_nullptr, ro, ul_nullptr, ao, mo);
}


#ifdef __cplusplus
}
#endif

#endif /* ULBN_SOURCE */
