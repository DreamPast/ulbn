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

#define ulbn_safe_forward_overlap(d, dn, s, sn) ((d) <= (s) || (d) >= (s) + (sn))
#define ulbn_safe_backward_overlap(d, dn, s, sn) ((d) + (dn) <= (s) || ((d) >= (s) && (d) + (dn) >= (s) + (sn)))
#define ulbn_safe_overlap(d, dn, s, sn) ((d) + (dn) <= (s) || (s) + (sn) <= (d))

#define ulbn_assert_forward_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_forward_overlap(d, dn, s, sn))
#define ulbn_assert_backward_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_backward_overlap(d, dn, s, sn))
#define ulbn_assert_overlap(d, dn, s, sn) ulbn_assert(ulbn_safe_overlap(d, dn, s, sn))

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
ULBN_PRIVATE int _ulbn_feq(double a, double b) {
  return a >= b && a <= b;
}

#define ULBN_LIMB_BITS (sizeof(ulbn_limb_t) * CHAR_BIT)
#define ULBN_LIMB_HALF_BITS (ULBN_LIMB_BITS >> 1)
#define ULBN_LIMB_SHL(val, shift) ul_static_cast(ulbn_limb_t, ul_static_cast(ulbn_limb_t, val) << (shift))
#define ULBN_LIMB_SIGNBIT (ULBN_LIMB_SHL(1, ULBN_LIMB_BITS - 1))
#define ULBN_LOWMASK ul_static_cast(ulbn_limb_t, ULBN_LIMB_SHL(1, ULBN_LIMB_HALF_BITS) - 1u)
#define ULBN_LOWPART(x) ul_static_cast(ulbn_limb_t, (x) & ULBN_LOWMASK)
#define ULBN_HIGHPART(x) ul_static_cast(ulbn_limb_t, (x) >> ULBN_LIMB_HALF_BITS)

#define ULBN_LIMB_USIZE_LIMIT (ULBN_USIZE_MAX / ULBN_LIMB_BITS)

#define _ulbn_abs_size(n) ulbn_cast_usize((n) < 0 ? -(n) : (n))
#define _ulbn_to_ssize(pos, n) ((pos) ? ulbn_cast_ssize(n) : -ulbn_cast_ssize(n))
ul_static_assert(sizeof(size_t) >= sizeof(ulbn_usize_t), "usbn_usize_t cannot be larger than size_t");
ul_static_assert(
  sizeof(ulbn_usize_t) >= sizeof(ulbn_ssize_t) && ULBN_USIZE_MAX / 2 >= ULBN_USIZE_SMAX,
  "ulbn_usize_t must be able to hold all positive value of ulbn_ssize_t"
);
ul_unused static const size_t _ULBN_ALLOC_MAX = ~ul_static_cast(size_t, 0) / sizeof(ulbn_limb_t);

#if ULBN_CONF_CHECK_USIZE_OVERFLOW
  #define ULBN_DO_IF_USIZE_COND(cond, expr) \
    if(ul_unlikely(cond))                   \
    expr((void)0)
  #define ULBN_RETURN_IF_USIZE_COND(cond, ret) \
    if(ul_unlikely(cond))                      \
    return (ret)
#else /* !ULBN_CONF_CHECK_USIZE_OVERFLOW */
  #define ULBN_DO_IF_USIZE_COND(cond, expr) ((void)0)
  #define ULBN_RETURN_IF_USIZE_COND(cond, ret) ((void)0)
#endif
#define ULBN_DO_IF_USIZE_OVERFLOW(n, exp) ULBN_DO_IF_USIZE_COND((n) > _ULBN_ALLOC_MAX, exp)
#define ULBN_RETURN_IF_USIZE_OVERFLOW(n, ret) ULBN_RETURN_IF_USIZE_COND((n) > _ULBN_ALLOC_MAX, ret)

#if ULBN_CONF_CHECK_SSIZE_OVERFLOW
  #define ULBN_RETURN_IF_SSIZE_OVERFLOW(n, ret) \
    if(ul_unlikely((n) > ULBN_USIZE_SMAX))      \
    return ret
#else /* !ULBN_CONF_CHECK_SSIZE_OVERFLOW */
  #define ULBN_RETURN_IF_SSIZE_OVERFLOW(n, ret) ((void)0)
#endif

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
  ulbn_assert(x != 0);
  #if ULBN_LIMB_MAX > 0xFFu
  while(!(x & ULBN_LIMB_SHL(0xFF, ULBN_LIMB_BITS - 8))) {
    r += 8;
    x <<= 8;
  }
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

#define _ulbn_from_pos_slimb(v) ul_static_cast(ulbn_limb_t, v)
#define _ulbn_from_neg_slimb(v) ul_static_cast(ulbn_limb_t, ul_static_cast(ulbn_limb_t, -(v + 1)) + 1u)

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

#ifndef _ulbn_umul_
  #define _ulbn_umul_(p1, p0, u, v)                                                                              \
    do {                                                                                                         \
      const ulbn_limb_t __ul = ULBN_LOWPART(u);                                                                  \
      const ulbn_limb_t __uh = ULBN_HIGHPART(u);                                                                 \
      const ulbn_limb_t __vl = ULBN_LOWPART(v);                                                                  \
      const ulbn_limb_t __vh = ULBN_HIGHPART(v);                                                                 \
      ulbn_limb_t __x0 = ul_static_cast(ulbn_limb_t, __ul * __vl);                                               \
      ulbn_limb_t __x1 = ul_static_cast(ulbn_limb_t, __ul * __vh);                                               \
      ulbn_limb_t __x2 = ul_static_cast(ulbn_limb_t, __uh * __vl);                                               \
      ulbn_limb_t __x3 = ul_static_cast(ulbn_limb_t, __uh * __vh);                                               \
      __x1 += ULBN_HIGHPART(__x0);                                                                               \
      __x1 += __x2;                                                                                              \
      if(__x1 < __x2)                                                                                            \
        __x3 += ULBN_LIMB_SHL(1, ULBN_LIMB_HALF_BITS);                                                           \
      (p0) = ul_static_cast(ulbn_limb_t, (__x1 << (ULBN_LIMB_BITS - ULBN_LIMB_HALF_BITS)) | ULBN_LOWPART(__x0)); \
      (p1) = __x3 + ULBN_HIGHPART(__x1);                                                                         \
    } while(0)
#endif /* _ulbn_umul_ */

#ifndef _ulbn_udiv_
  #define _ulbn_udiv_(q, r, n1, n0, d)                                   \
    do {                                                                 \
      const ulbn_limb_t __dh = ULBN_HIGHPART(d);                         \
      const ulbn_limb_t __dl = ULBN_LOWPART(d);                          \
      ulbn_limb_t __qh, __ql, __r, __m;                                  \
      ulbn_assert((n1) < (d));                                           \
      ulbn_assert((__dh) > 0);                                           \
                                                                         \
      __qh = (n1) / __dh;                                                \
      __r = (n1) - __qh * __dh;                                          \
      __m = __qh * __dl;                                                 \
      __r = ULBN_LIMB_SHL(__r, ULBN_LIMB_BITS >> 1) | ULBN_HIGHPART(n0); \
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
      __r = ULBN_LIMB_SHL(__r, ULBN_LIMB_BITS >> 1) | ULBN_LOWPART(n0);  \
      if(__r < __m) {                                                    \
        --__ql, __r += (d);                                              \
        if(__r >= (d) && __r < __m)                                      \
          --__ql, __r += (d);                                            \
      }                                                                  \
      __r -= __m;                                                        \
                                                                         \
      (r) = __r;                                                         \
      (q) = ULBN_LIMB_SHL(__qh, ULBN_LIMB_BITS >> 1) | __ql;             \
    } while(0)
#endif /* _ulbn_udiv_ */

#if 0
/* Ensure v != 0. Time complexity is at most O(log({ULBN_LIMB_BITS}))*/
ULBN_PRIVATE ulbn_limb_t _ulbn_sqrt_(ulbn_limb_t v) {
  #if 1
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
  #else
  return ul_static_cast(ulbn_limb_t, floor(sqrt(ul_static_cast(double, v))));
  #endif
}
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

static const char _ULBN_UPPER_TABLE[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
static const char _ULBN_LOWER_TABLE[] = "0123456789abcdefghijklmnopqrstuvwxyz";
ULBN_INTERNAL const char* ulbn_string_table(int is_lower) {
  return is_lower ? _ULBN_LOWER_TABLE : _ULBN_UPPER_TABLE;
}

#if 0
ULBN_INTERNAL void ulbn_dumplimb(FILE* fp, ulbn_limb_t l) {
  const char* TABLE = ulbn_string_table(0);
  size_t j = sizeof(l) * CHAR_BIT / 4;
  while(j--)
    putc(TABLE[(l >> (j << 2)) & 0xF], fp);
}
ULBN_INTERNAL void ulbn_dump(FILE* fp, const ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_usize_t i;
  for(i = n; i > 0; --i) {
    ulbn_dumplimb(fp, p[i - 1]);
    if(i != 1)
      fputc('_', stdout);
  }
}
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


/* Normalize p[0:n], removing leading zeros, and return the remaining length.
  When p[0:n] = 0, the length is 0. */
ULBN_INTERNAL ulbn_usize_t ulbn_normalize(ulbn_limb_t* p, ulbn_usize_t n) {
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
#define ulbn_maycopy(dst, src, n) ((dst) == (src) ? (void)0 : ulbn_copy((dst), (src), (n)))

/* Compare ap[0:n] and bp[0:n], return direction (<0 means less than, =0 means equal, >0 means greater) */
ULBN_INTERNAL int ulbn_cmpn(const ulbn_limb_t* ap, const ulbn_limb_t* bp, ulbn_usize_t n) {
  ulbn_usize_t i;
  for(i = 0; i < n; ++i)
    if(ap[i] != bp[i])
      return ap[i] < bp[i] ? -1 : 1;
  return 0;
}
/* Compare ap[0:an] and bp[0:bn], return direction (<0 means less than, =0 means equal, >0 means greater) */
ULBN_INTERNAL int ulbn_cmp(const ulbn_limb_t* ap, ulbn_usize_t an, const ulbn_limb_t* bp, ulbn_usize_t bn) {
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
  ulbn_assert_backward_overlap(rp, _ulbn_max_(an, bn), ap, an);
  ulbn_assert_backward_overlap(rp, _ulbn_max_(an, bn), bp, bn);

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

  ulbn_assert(ulbn_cmp(ap, an, bp, bn) >= 0);
  ulbn_assert_backward_overlap(rp, an, ap, an);
  ulbn_assert_backward_overlap(rp, an, bp, bn);

  cy = ulbn_subn(rp, ap, bp, bn);
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
  ulbn_assert(an + bn >= an);
  ulbn_assert_overlap(rp, an + bn, ap, an);
  ulbn_assert_overlap(rp, an + bn, bp, bn);

  rp[an] = ulbn_mul1(rp, ap, an, bp[0]);
  for(i = 1; i < bn; ++i)
    rp[an + i] = ulbn_addmul1(rp + i, ap, an, bp[i]);
}

#if 0
ULBN_PRIVATE void _ulbn_mul(
  ulbn_alloc_t* alloc, ulbn_limb_t* rp, /* */
  ulbn_limb_t* ap, ulbn_usize_t an, /* */
  ulbn_limb_t* bp, ulbn_usize_t bn  /* */
);

  #define _ulbn_mul_toom_11(rp, ap, an, bp, bn) ulbn_mul_school((rp), (ap), (an), (bp), (bn))
  #define _ULBN_TOOM_11_THRESHOLD 64
  #define _ULBN_TOOM_N1_THRESHOLD 7

ULBN_PRIVATE void _ulbn_mul_toom_21(
  ulbn_limb_t* rp,                        /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn  /* */
) { }

ULBN_PRIVATE void _ulbn_mul_toom_22(
  ulbn_limb_t* rp,                        /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn  /* */
) { }

ULBN_PRIVATE void _ulbn_mul(
  ulbn_alloc_t* alloc, ulbn_limb_t* rp, /* */
  ulbn_limb_t* ap, ulbn_usize_t an, /* */
  ulbn_limb_t* bp, ulbn_usize_t bn  /* */
) { }
#endif

/* rp[0:an+bn] = ap[0:an] * bp[0:bn]
  This version will automatically select the appropriate algorithm for computation. */
ULBN_INTERNAL int ulbn_mul(
  ulbn_alloc_t* alloc, ulbn_limb_t* rp,   /* */
  const ulbn_limb_t* ap, ulbn_usize_t an, /* */
  const ulbn_limb_t* bp, ulbn_usize_t bn  /* */
) {
  ulbn_limb_t *tap = ul_nullptr, *tbp = ul_nullptr;
  /* todo: add cook-reduction and fft-multiplication */

  ulbn_assert(an + bn >= an);
  if(ul_unlikely(rp == ap)) {
    tap = ulbn_allocT(ulbn_limb_t, alloc, an);
    ULBN_RETURN_IF_ALLOC_FAILED(tap, ULBN_ERR_NOMEM);
    ulbn_copy(tap, ap, an);
    ap = tap;
  }
  if(ul_unlikely(rp == bp)) {
    tbp = ulbn_allocT(ulbn_limb_t, alloc, bn);
    ULBN_RETURN_IF_ALLOC_FAILED(tbp, ULBN_ERR_NOMEM);
    ulbn_copy(tbp, bp, bn);
    bp = tbp;
  }

  ulbn_mul_school(rp, ap, an, bp, bn);

  if(ul_unlikely(tap != ul_nullptr))
    ulbn_deallocT(ulbn_limb_t, alloc, tap, an);
  if(ul_unlikely(tbp != ul_nullptr))
    ulbn_deallocT(ulbn_limb_t, alloc, tbp, bn);

  return 0;
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

/* Let B to be 2^{ULBN_LIMB_BITS}, di = (B^2-1)//d1 - B */
ULBN_INTERNAL ulbn_limb_t ulbn_divinv1(ulbn_limb_t d1) {
  /*
   * di = (B^2-1)//d1 - B
   * di = <B-1-d1, B-1>//d1
   */
  ulbn_limb_t n1, n0, di;

  /* B/2 <= d1 < B */
  ulbn_assert((d1 & ULBN_LIMB_SIGNBIT) != 0);

  n1 = _ulbn_neg_(d1 + 1u);
  n0 = _ulbn_neg_(1u);
  _ulbn_udiv_(di, di, n1, n0, d1);
  return di;
}
/* Let B to be 2^{ULBN_LIMB_BITS}, di = (B^3-1)//(d1*B+d0) - B */
ULBN_INTERNAL ulbn_limb_t ulbn_divinv2(ulbn_limb_t d1, ulbn_limb_t d0) {
  /*
   * di = (B^3-1 - <d1,d0,0>)//<d1, d0>
   * di = <B-1-d1, B-1-d0, B-1>//<d1, d0>
   */
  ulbn_limb_t n1, n0, di;
  ulbn_limb_t p, t1, t0;

  /* B/2 <= d1 < B */
  ulbn_assert((d1 & ULBN_LIMB_SIGNBIT) != 0);

  /*
   * di = (B^2-1)//d1 - B
   * di = <B-1-d1, B-1>//d1
   */
  n1 = _ulbn_neg_(d1 + 1u);
  n0 = _ulbn_neg_(1u);
  _ulbn_udiv_(di, di, n1, n0, d1);

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
    (q) = __q1;                                             \
    (r1) = __r1;                                            \
    (r0) = __r0;                                            \
  } while(0)

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
    ULBN_RETURN_IF_ALLOC_FAILED(tdp, ULBN_ERR_NOMEM);
    ulbn_shl(tdp, dp, dn, shift);
    dp = tdp;
  } else if(ul_unlikely(dp == qp) || ul_unlikely(dp == ap) || ul_unlikely(dp == rp)) {
    tdp = ulbn_allocT(ulbn_limb_t, alloc, dn);
    ULBN_RETURN_IF_ALLOC_FAILED(tdp, ULBN_ERR_NOMEM);
    ulbn_copy(tdp, dp, dn);
    dp = tdp;
  }

  /* check if the remainder can be calculated in place */
  if(ap != rp) {
    nrp = ulbn_allocT(ulbn_limb_t, alloc, an);
    ULBN_RETURN_IF_ALLOC_FAILED(nrp, ULBN_ERR_NOMEM);
  }
  ulbn_assert(nrp != ul_nullptr);
  if(shift)
    a2 = ulbn_shl(nrp, ap, an, shift);
  else if(ap != rp)
    ulbn_copy(nrp, ap, an);

  if(qp == ul_nullptr) {
    nqp = ulbn_allocT(ulbn_limb_t, alloc, an - dn + 1);
    ULBN_RETURN_IF_ALLOC_FAILED(nqp, ULBN_ERR_NOMEM);
  }

  ulbn_divmod_inv(nqp, nrp, an, a2, dp, dn, ulbn_divinv2(dp[dn - 1], dp[dn - 2]));

  if(rp != ul_nullptr) {
    if(shift != 0)
      ulbn_shr(rp, nrp, dn, shift);
    else if(rp != nrp)
      ulbn_copy(rp, nrp, dn);
    err = 0;
  } else
    err = ulbn_normalize(nrp, dn) == 0 ? 0 : ULBN_ERR_INEXACT;

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
ULBN_INTERNAL int ulbn_divmod(
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
  ulbn_assert(ap == dp || ulbn_safe_overlap(ap, an, dp, dn));
  ulbn_assert(rp == ap || rp == ul_nullptr || ulbn_safe_overlap(rp, dn, ap, an));
  ulbn_assert(rp == dp || rp == ul_nullptr || ulbn_safe_overlap(rp, dn, dp, dn));
  ulbn_assert(qp == ap || qp == ul_nullptr || ulbn_safe_overlap(qp, an - dn + 1, ap, an));
  ulbn_assert(qp == dp || qp == ul_nullptr || ulbn_safe_overlap(qp, an - dn + 1, dp, dn));
  ulbn_assert(qp == rp || qp == ul_nullptr || rp == ul_nullptr || ulbn_safe_overlap(qp, an - dn + 1, rp, dn));

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
  ulbn_usize_t i = ~mask & ULBN_LIMB_MAX;

  ulbn_assert(cy == 0 || cy == 1);

  while(i < k && p[i] == 0)
    ++i;
  /* If `cy`==0, there is no carry 1, it is masked out */
  return l + ((i == k) & cy);
}
/* return p[0:n] is power of 2 */
ULBN_INTERNAL int ulbn_is_2pow(const ulbn_limb_t* p, ulbn_usize_t n) {
  ulbn_usize_t i;
  for(i = 0; i < n && !p[i]; ++i) { }
  return i + 1 == n && (p[i] & (p[i] - 1u)) == 0;
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
    ulbn_reallocT(ulbn_limb_t, alloc, o->limb, o->cap, 0);
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
  ULBN_RETURN_IF_USIZE_OVERFLOW(n, ul_nullptr);
  new_cap = o->cap + (o->cap >> 1);
  new_cap = _ulbn_max_(new_cap, n);
  ULBN_DO_IF_USIZE_OVERFLOW(new_cap, new_cap = n);
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
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  ro->len = -ro->len;
  return err;
}
ULBN_PUBLIC int ulbi_abs(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao) {
  int err = ulbi_set_copy(alloc, ro, ao);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  ro->len = ulbn_cast_ssize(_ulbn_abs_size(ro->len));
  return err;
}


ULBN_PUBLIC int ulbi_set_copy(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* src) {
  if(dst != src) {
    ulbn_usize_t n;
    ulbn_limb_t* limb;
    n = _ulbn_abs_size(src->len);
    if(n) {
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
ul_static_assert(sizeof(ulbn_ulong_t) * CHAR_BIT <= ULBN_SSIZE_MAX, "ulbn_ulong_t is too large");
ULBN_PUBLIC int ulbi_set_ulong(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ulong_t l) {
  ulbn_limb_t limbs[(sizeof(l) + sizeof(ulbn_limb_t) - 1) / sizeof(ulbn_limb_t)];
  ulbn_ssize_t len = 0;

#if ULBN_ULONG_MAX < ULBN_LIMB_MAX
  #error "ulbn_ulong_t is too small"
#elif ULBN_ULONG_MAX == ULBN_LIMB_MAX
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
ul_static_assert(
  -ULBN_SLONG_MAX - 1 == ULBN_SLONG_MIN || -ULBN_SLONG_MAX == ULBN_SLONG_MIN,
  "Neither two's complement nor one's complement"
);
ULBN_PUBLIC int ulbi_set_slong(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_slong_t l) {
  int err;
  if(l >= 0)
    err = ulbi_set_ulong(alloc, dst, ul_static_cast(ulbn_ulong_t, l));
  else {
    err = ulbi_set_ulong(alloc, dst, ul_static_cast(ulbn_ulong_t, -(l + 1)) + 1u);
    dst->len = -dst->len;
  }
  return err;
}
ULBN_PUBLIC int ulbi_set_double(ulbn_alloc_t* alloc, ulbi_t* dst, double x) {
  const double B = ul_static_cast(double, ULBN_LIMB_SIGNBIT) * 2.0;
  const double Bi = 1.0 / B;
  ulbn_ssize_t ri, rn;
  ulbn_limb_t* rp;
  double xl;
  int positive;

  /* NaN or +Inf or -Inf */
  if(x != x || _ulbn_feq(x, x * 0.5)) {
    dst->len = 0;
    return ULBN_ERR_INVALID;
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
ULBN_PUBLIC int ulbi_set_2exp(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t n) {
  ulbn_limb_t* p;
  const ulbn_usize_t idx = n / ULBN_LIMB_BITS;
  ULBN_RETURN_IF_SSIZE_OVERFLOW(idx + 1, ULBN_ERR_EXCEED_RANGE);
  p = _ulbi_res(alloc, dst, idx + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(p, ULBN_ERR_NOMEM);
  ulbn_fill0(p, idx + 1);
  p[idx] = ULBN_LIMB_SHL(1, n % ULBN_LIMB_BITS);
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
    B *= ul_static_cast(ulbn_limb_t, base);
    l = ul_static_cast(ulbn_limb_t, l * ul_static_cast(ulbn_limb_t, base) + x);
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
ULBN_PUBLIC int ulbi_init_double(ulbn_alloc_t* alloc, ulbi_t* dst, double x) {
  return ulbi_set_double(alloc, ulbi_init(dst), x);
}
ULBN_PUBLIC int ulbi_init_2exp(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t n) {
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
  if(b > 0)
    return ao->len == 1 && _ulbi_limb(ao)[0] == _ulbn_from_pos_slimb(b);
  else
    return ao->len == -1 && _ulbi_limb(ao)[0] == _ulbn_from_neg_slimb(b);
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
  if(o->len == 0)
    return 1;
  return (_ulbi_limb(o)[0] & 1) == 0;
}
ULBN_PUBLIC int ulbi_is_odd(const ulbi_t* o) {
  if(o->len == 0)
    return 0;
  return (_ulbi_limb(o)[0] & 1) != 0;
}


/* ignore sign of `ao` and `bo` */
ULBN_PRIVATE int _ulbi_add(
  ulbn_alloc_t* alloc, ulbi_t* ro,   /* */
  const ulbi_t* ao, ulbn_usize_t an, /* */
  const ulbi_t* bo, ulbn_usize_t bn  /* */
) {
  ulbn_limb_t cy;
  ulbn_limb_t* rp;

  if(an < bn) {
    _ulbn_swap_(const ulbi_t*, ao, bo);
    _ulbn_swap_(ulbn_usize_t, an, bn);
  }
  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);

  cy = ulbn_add(rp, _ulbi_limb(ao), an, _ulbi_limb(bo), bn);
  rp[an] = cy;
  an += ul_static_cast(unsigned, cy);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = ulbn_cast_ssize(an);
  return 0;
}
/* ignore sign of `ao` and `bo` */
ULBN_PRIVATE int _ulbi_sub(
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
    err = _ulbi_add(alloc, ro, ao, an, bo, bn);
  else
    err = _ulbi_sub(alloc, ro, ao, an, bo, bn);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}
ULBN_PUBLIC int ulbi_sub(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  int positive = (ao->len >= 0), err;
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
  if(_ulbn_same_sign(ao->len, bo->len))
    err = _ulbi_sub(alloc, ro, ao, an, bo, bn);
  else
    err = _ulbi_add(alloc, ro, ao, an, bo, bn);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}

ULBN_PRIVATE int _ulbi_add_limb(
  ulbn_alloc_t* alloc, ulbi_t* ro,   /* */
  const ulbi_t* ao, ulbn_usize_t an, /* */
  ulbn_limb_t b                      /* */
) {
  ulbn_limb_t cy;
  ulbn_limb_t* rp;

  rp = _ulbi_res(alloc, ro, an + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);

  cy = ulbn_add1(rp, _ulbi_limb(ao), an, b);
  rp[an] = cy;
  an += (cy != 0);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
  ro->len = ulbn_cast_ssize(an);
  return 0;
}
ULBN_PRIVATE int _ulbi_sub_limb(
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
    err = _ulbi_add_limb(alloc, ro, ao, ulbn_cast_usize(ao->len), b);
  else
    err = _ulbi_sub_limb(alloc, ro, ao, ulbn_cast_usize(-ao->len), b);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}
ULBN_PUBLIC int ulbi_sub_limb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b) {
  int positive = (ao->len >= 0), err;
  if(ao->len >= 0)
    err = _ulbi_sub_limb(alloc, ro, ao, ulbn_cast_usize(ao->len), b);
  else
    err = _ulbi_add_limb(alloc, ro, ao, ulbn_cast_usize(-ao->len), b);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}
ULBN_PUBLIC int ulbi_limb_sub(ulbn_alloc_t* alloc, ulbi_t* ro, ulbn_limb_t a, const ulbi_t* bo) {
  int err;
  if(bo->len >= 0) {
    err = _ulbi_sub_limb(alloc, ro, bo, ulbn_cast_usize(bo->len), a);
    ro->len = -ro->len;
  } else
    err = _ulbi_add_limb(alloc, ro, bo, ulbn_cast_usize(-bo->len), a);
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
  err = ulbn_mul(alloc, rp, _ulbi_limb(ao), an, _ulbi_limb(bo), bn);
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  rn -= (rp[rn - 1] == 0);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(positive, rn);
  return 0;
}


ULBN_PUBLIC int ulbi_divmod(ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo) {
  int positive = _ulbn_same_sign(ao->len, bo->len), a_positive = (ao->len >= 0), err = 0;
  ulbn_usize_t an = _ulbn_abs_size(ao->len), bn = _ulbn_abs_size(bo->len);
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

  err = ulbn_divmod(alloc, qp, rp, _ulbi_limb(ao), _ulbn_abs_size(ao->len), _ulbi_limb(bo), _ulbn_abs_size(bo->len));
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
    ULBN_RETURN_IF_SSIZE_OVERFLOW(an, ULBN_ERR_EXCEED_RANGE);
    an += ul_static_cast(unsigned, rp[an]);
    ro->len = -ulbn_cast_ssize(an);
  } else {
    ulbn_sub1(rp, _ulbi_limb(ao), an, 1);
    an = ulbn_normalize(rp, an);
    ro->len = ulbn_cast_ssize(an);
  }
  return 0;
}

ULBN_PUBLIC int ulbi_sal(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  const ulbn_usize_t idx = b / ULBN_LIMB_BITS;
  const ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_usize_t rn;
  ulbn_limb_t* rp;
  int shift = ul_static_cast(int, b % ULBN_LIMB_BITS);

  if(an == 0) {
    ro->len = 0;
    return 0;
  }

  rn = an + idx;
  ULBN_RETURN_IF_USIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  rp = _ulbi_res(alloc, ro, rn + 1);
  ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);

  ulbn_fill0(rp, idx);
  if(shift)
    rp[rn++] = ulbn_shl(rp + idx, _ulbi_limb(ao), an, shift);
  else
    ulbn_rcopy(rp + idx, _ulbi_limb(ao), an);
  rn = ulbn_normalize(rp, rn);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(ao->len >= 0, rn);
  return 0;
}
ULBN_PUBLIC int ulbi_sar(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  const int a_neg = ao->len < 0;
  const ulbn_usize_t idx = b / ULBN_LIMB_BITS;
  const ulbn_usize_t an = _ulbn_abs_size(ao->len);
  ulbn_usize_t rn;
  ulbn_usize_t i;
  ulbn_limb_t cy = 0;
  ulbn_limb_t* rp;
  const ulbn_limb_t* ap;
  int shift = ul_static_cast(int, b % ULBN_LIMB_BITS);

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

  if(a_neg && cy) {
    rp[rn] = ulbn_add1(rp, rp, rn, 1);
    ++rn;
  }
  rn = ulbn_normalize(rp, rn);
  ULBN_RETURN_IF_SSIZE_OVERFLOW(rn, ULBN_ERR_EXCEED_RANGE);
  ro->len = _ulbn_to_ssize(!a_neg, rn);
  return 0;
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
      ULBN_RETURN_IF_USIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
    } else {
      op = _ulbi_res(alloc, o, n + 1);
      op[n] = ulbn_add1(op + idx, op + idx, n - idx, ULBN_LIMB_SHL(1, shift));
      if(op[n] != 0) {
        ++n;
        ULBN_RETURN_IF_USIZE_OVERFLOW(n, ULBN_ERR_EXCEED_RANGE);
      }
    }
  }
  o->len = _ulbn_to_ssize(o->len >= 0, n);
  return 1;
}
ULBN_PRIVATE int _ulbi_testbit(const ulbi_t* o, ulbn_usize_t idx, int shift) {
  ulbn_assert(0 <= shift && ul_static_cast(unsigned, shift) < ULBN_LIMB_BITS);
  return (ulbn_limb(_ulbi_limb(o), _ulbn_abs_size(o->len), o->len < 0, idx) & ULBN_LIMB_SHL(1, shift)) != 0;
}

ULBN_PUBLIC int ulbi_testbit(const ulbi_t* o, ulbn_usize_t k) {
  return _ulbi_testbit(o, k / ULBN_LIMB_BITS, ul_static_cast(int, k % ULBN_LIMB_BITS));
}
ULBN_PUBLIC int ulbi_setbit(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k) {
  ulbn_usize_t idx = k / ULBN_LIMB_BITS;
  int shift = ul_static_cast(int, k % ULBN_LIMB_BITS);
  return _ulbi_testbit(o, idx, shift) ? 1 : _ulbi_setbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_resetbit(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k) {
  ulbn_usize_t idx = k / ULBN_LIMB_BITS;
  int shift = ul_static_cast(int, k % ULBN_LIMB_BITS);
  return !_ulbi_testbit(o, idx, shift) ? 0 : _ulbi_resetbit(alloc, o, idx, shift);
}
ULBN_PUBLIC int ulbi_combit(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k) {
  ulbn_usize_t idx = k / ULBN_LIMB_BITS;
  int shift = ul_static_cast(int, k % ULBN_LIMB_BITS);
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

  ro->len = ulbn_cast_ssize(rn);
  return 0;
}
ULBN_PUBLIC int ulbi_as_uint(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  return _ulbi_as_uint(alloc, ro, ao, b / ULBN_LIMB_BITS, ul_static_cast(int, b % ULBN_LIMB_BITS), ao->len < 0);
}
ULBN_PUBLIC int ulbi_as_int(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b) {
  const ulbn_usize_t idx = (b - 1) / ULBN_LIMB_BITS;
  const int shift = ul_static_cast(int, (b - 1) % ULBN_LIMB_BITS);
  const ulbn_limb_t* ap;
  int err, positive;

  if(ul_unlikely(b == 0)) {
    ro->len = 0;
    return 0;
  }
  positive = (_ulbi_testbit(ao, idx, shift) == 0);

  ap = _ulbi_limb(ao);
  if(ul_unlikely(!positive && idx < _ulbn_abs_size(ao->len))) {
    const ulbn_limb_t mask = ULBN_LIMB_SHL(1u, shift);
    if(ul_unlikely((ap[idx] & (ul_static_cast(ulbn_limb_t, mask << 1u) - 1u)) == mask) && ulbn_is0(ap, idx)) {
      ulbn_limb_t* rp = _ulbi_res(alloc, ro, idx + 1);
      ULBN_RETURN_IF_ALLOC_FAILED(rp, ULBN_ERR_NOMEM);
      ulbn_fill0(rp, idx);
      rp[idx] = ULBN_LIMB_SHL(1u, shift);
      ro->len = -ulbn_cast_ssize(idx + 1);
      return 0;
    }
  }

  err = _ulbi_as_uint(alloc, ro, ao, idx, shift, positive ^ (ao->len >= 0));
  ULBN_RETURN_IF_ALLOC_COND(err < 0, err);
  ro->len = _ulbn_to_ssize(positive, ro->len);
  return err;
}


ULBN_PUBLIC int ulbi_is_2pow(const ulbi_t* o) {
  return ulbn_is_2pow(_ulbi_limb(o), _ulbn_abs_size(o->len));
}
ULBN_PUBLIC ulbn_usize_t ulbi_ctz(const ulbi_t* ro, ulbn_usize_t* p_rh) {
  const ulbn_usize_t n = _ulbn_abs_size(ro->len), m = _ulbn_min_(n, ULBN_LIMB_USIZE_LIMIT);
  ulbn_usize_t rl = 0, rh = 0;
  ulbn_usize_t i;
  const ulbn_limb_t* rp = _ulbi_limb(ro);

  for(i = 0; i < m; ++i) {
    if(rp[i]) {
      rl += ul_static_cast(unsigned, _ulbn_ctz_(rp[i]));
      goto done;
    }
    rl += ULBN_LIMB_BITS;
  }
#if ULBN_CONF_CHECK_BITS_OVERFLOW
  for(; ul_unlikely(i < n); ++i) {
    if(rp[i]) {
      ulbn_usize_t r_temp = rl;
      rl += ul_static_cast(unsigned, _ulbn_ctz_(rp[i]));
      rh = (rl < r_temp);
      goto done;
    }
    rl += ULBN_LIMB_BITS;
    rh += (rl < ULBN_LIMB_BITS);
  }
#endif /* ULBN_CONF_CHECK_BITS_OVERFLOW */

done:
  if(ul_unlikely(p_rh))
    *p_rh = rh;
  return rl;
}
ULBN_PUBLIC ulbn_usize_t ulbi_cto(const ulbi_t* ro, ulbn_usize_t* p_rh) {
  const ulbn_usize_t n = _ulbn_abs_size(ro->len), m = _ulbn_min_(n, ULBN_LIMB_USIZE_LIMIT);
  ulbn_usize_t rl = 0, rh = 0;
  ulbn_usize_t i;
  const ulbn_limb_t* rp = _ulbi_limb(ro);

  for(i = 0; i < m; ++i) {
    if(rp[i] != ULBN_LIMB_MAX) {
      rl += ul_static_cast(unsigned, _ulbn_ctz_(~rp[i]));
      goto done;
    }
    rl += ULBN_LIMB_BITS;
  }
#if ULBN_CONF_CHECK_BITS_OVERFLOW
  for(; ul_unlikely(i < n); ++i) {
    if(rp[i] != ULBN_LIMB_MAX) {
      ulbn_usize_t r_temp = rl;
      rl += ul_static_cast(unsigned, _ulbn_ctz_(~rp[i]));
      rh = (rl < r_temp);
      goto done;
    }
    rl += ULBN_LIMB_BITS;
    rh += (rl < ULBN_LIMB_BITS);
  }
#endif /* ULBN_CONF_CHECK_BITS_OVERFLOW */

done:
  if(ul_unlikely(p_rh))
    *p_rh = rh;
  return rl;
}
ULBN_PUBLIC ulbn_usize_t ulbi_abs_popcount(const ulbi_t* ro, ulbn_usize_t* p_rh) {
  const ulbn_usize_t n = _ulbn_abs_size(ro->len), m = _ulbn_min_(n, ULBN_LIMB_USIZE_LIMIT);
  ulbn_usize_t rl = 0, rh = 0;
  ulbn_usize_t i;
  const ulbn_limb_t* rp = _ulbi_limb(ro);

  for(i = 0; i < m; ++i)
    rl += ul_static_cast(unsigned, _ulbn_popcount_(rp[i]));
#if ULBN_CONF_CHECK_BITS_OVERFLOW
  for(; ul_unlikely(i < n); ++i) {
    ulbn_usize_t r_temp = rl;
    rl += ul_static_cast(unsigned, _ulbn_popcount_(rp[i]));
    rh += (rl < r_temp);
  }
#endif /* ULBN_CONF_CHECK_BITS_OVERFLOW */

  if(ul_unlikely(p_rh))
    *p_rh = rh;
  return rl;
}
ULBN_PUBLIC ulbn_usize_t ulbi_abs_floor_log2(const ulbi_t* ro, ulbn_usize_t* p_rh) {
#if ULBN_CONF_CHECK_BITS_OVERFLOW
  static const ulbn_usize_t LIMIT = ULBN_USIZE_MAX / ULBN_LIMB_BITS;
  static const size_t USIZE_BITS = sizeof(ulbn_usize_t) * CHAR_BIT;
  static const size_t USIZE_HALF_BITS = USIZE_BITS >> 1;
#endif /* ULBN_CONF_CHECK_BITS_OVERFLOW */

  ulbn_usize_t n = _ulbn_abs_size(ro->len);
  ulbn_usize_t rl, rh;

  if(n == 0) {
    rl = 0;
    rh = 0;
  } else {
#if ULBN_CONF_CHECK_BITS_OVERFLOW
    if(ul_likely(n <= LIMIT)) {
      rl = n * ULBN_LIMB_BITS - ul_static_cast(unsigned, _ulbn_clz_(_ulbi_limb(ro)[n - 1]));
      rh = 0;
    } else {
      ulbn_usize_t n_high = n >> USIZE_HALF_BITS;
      ulbn_usize_t n_low = n & ulbn_cast_usize((ulbn_cast_usize(1u) << USIZE_HALF_BITS) - 1u);
      const ulbn_usize_t v0 = n_low * ULBN_LIMB_BITS;
      const ulbn_usize_t v1 = n_high * ULBN_LIMB_BITS;
      rl = v0 + (v1 << (USIZE_BITS - USIZE_HALF_BITS));
      rh = (v1 >> USIZE_HALF_BITS) + (rl < v0);
    }
#else
    rl = n * ULBN_LIMB_BITS - ul_static_cast(unsigned, _ulbn_clz_(_ulbi_limb(ro)[n - 1]));
    rh = 0;
#endif /* ULBN_CONF_CHECK_BITS_OVERFLOW */
  }

  if(p_rh)
    *p_rh = rh;
  return rl;
}


ULBN_PUBLIC ulbn_limb_t ulbi_to_limb(const ulbi_t* src) {
  if(src->len == 0)
    return 0;
  return src->len > 0 ? _ulbi_limb(src)[0] : ul_static_cast(ulbn_limb_t, 0u - _ulbi_limb(src)[0]);
}
ULBN_PUBLIC ulbn_ulong_t ulbi_to_abs_ulong(const ulbi_t* src) {
#if ULBN_LIMB_MAX >= ULBN_ULONG_MAX
  return src->len ? ul_static_cast(ulbn_ulong_t, _ulbi_limb(src)[0]) : 0u;
#else
  ulbn_usize_t n = _ulbn_abs_size(src->len);
  const ulbn_limb_t* p = _ulbi_limb(src);
  ulbn_usize_t i;
  ulbn_ulong_t r;

  if(n == 0)
    return 0u;
  n = _ulbn_min_(
    n, ul_static_cast(ulbn_usize_t, (sizeof(ulbn_ulong_t) * CHAR_BIT + ULBN_LIMB_BITS - 1) / ULBN_LIMB_BITS)
  );
  r = p[n - 1];
  for(i = n - 1; i > 0; --i)
    r = (r << ULBN_LIMB_BITS) | p[i - 1];
  return r;
#endif
}
ULBN_PUBLIC ulbn_ulong_t ulbi_to_ulong(const ulbi_t* src) {
  ulbn_ulong_t x = ulbi_to_abs_ulong(src);
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
ULBN_PUBLIC double ulbi_to_double(const ulbi_t* src) {
  static const double B = ul_static_cast(double, ULBN_LIMB_SIGNBIT) * 2.0;
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


ULBN_PUBLIC char* ulbi_tostr_alloc(
  ulbn_alloc_t* alloc, ulbn_usize_t* p_len,          /* */
  ulbn_alloc_func_t* alloc_func, void* alloc_opaque, /* */
  const ulbi_t* ao, int base                         /* */
) {
  const ulbn_usize_t an = _ulbn_abs_size(ao->len);
  const unsigned a_neg = ao->len < 0;
  char* buf = ul_nullptr;
  ulbn_limb_t* rp;

  ulbn_limb_t B_guard, B;
  unsigned B_pow;

  ulbn_limb_t* cp = ul_nullptr;
  ulbn_usize_t cn, c_alloc = 0;
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

  B_guard = ul_static_cast(ulbn_limb_t, ULBN_LIMB_MAX / ul_static_cast(unsigned, base));
  B_pow = 1;
  for(B = ul_static_cast(ulbn_limb_t, base); B <= B_guard; B *= ul_static_cast(ulbn_limb_t, base))
    ++B_pow;
  cn = ulbn_convbase(alloc, &cp, &c_alloc, rp, an, B);
  ULBN_DO_IF_ALLOC_COND(cn == 0, { goto done; });

  on = ulbn_conv2str(cn, cp, ul_nullptr, 0, ul_static_cast(ulbn_limb_t, base), B_pow, ulbn_string_table(0));
  ULBN_DO_IF_ALLOC_COND(on == 0, { goto done; });
  buf = ul_reinterpret_cast(
    char*, alloc_func(alloc_opaque, ul_nullptr, 0, (ul_static_cast(size_t, on) + 1 + a_neg) * sizeof(ulbn_limb_t))
  );
  ULBN_DO_IF_ALLOC_COND(buf == ul_nullptr, { goto done; });
  if(ul_unlikely(a_neg))
    buf[0] = '-';
  ulbn_conv2str(cn, cp, buf + a_neg, on, ul_static_cast(ulbn_limb_t, base), B_pow, ulbn_string_table(0));
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
  ulbn_reallocT(char, alloc, str, len + 1, 0);
  return 0;
}
