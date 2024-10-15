#ifndef ULBN_H
#define ULBN_H

#if !defined(ul_unused) && defined(__has_attribute)
  #if __has_attribute(unused)
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

#ifndef ul_inline
  #if defined(__cplusplus) || (defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L)
    #define ul_inline inline
  #else
    #define ul_inline
  #endif
#endif /* ul_inline */

#ifdef __has_builtin
  #if __has_builtin(__builtin_expect)
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

#ifndef ul_static_cast
  #ifdef __cplusplus
    #define ul_static_cast(T, val) static_cast<T>(val)
  #else
    #define ul_static_cast(T, val) ((T)(val))
  #endif
#endif /* ul_static_cast */

#ifndef ul_reinterpret_cast
  #ifdef __cplusplus
    #define ul_reinterpret_cast(T, val) reinterpret_cast<T>(val)
  #else
    #define ul_reinterpret_cast(T, val) ((T)(val))
  #endif
#endif /* ul_reinterpret_cast */

#if !defined(ul_offsetof) && defined(__has_builtin)
  #if __has_builtin(__builtin_offsetof)
    #define ul_offsetof(type, field) __builtin_offsetof(type, field)
  #endif
#endif /* ul_offsetof */
#ifndef ul_offsetof
  #define ul_offsetof(type, field) offsetof(type, field)
#endif /* ul_offsetof */

#ifndef ul_has_builtin
  #if defined(__has_builtin)
    #define ul_has_builtin(x) __has_builtin(x)
  #else
    #define ul_has_builtin(x) 0
  #endif
#endif /* ul_has_builtin */

#ifndef UL_JOIN
  #define __UL_JOIN2(X, Y) X##Y
  #define __UL_JOIN(X, Y) __UL_JOIN2(X, Y)
  #define UL_JOIN(X, Y) __UL_JOIN(X, Y)
#endif /* UL_JOIN */

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

#ifndef ul_nullptr
  #define ul_nullptr NULL
#endif /* ul_nullptr */

#ifndef ul_restrict
  #if defined(_MSC_VER)
    #define ul_restrict __restrict
  #elif defined(__GNUC__) && __GNUC__ > 3
    #define ul_restrict __restrict__
  #elif defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 199901L)
    #define ul_restrict restrict
  #else
    #define ul_restrict
  #endif
#endif /* ul_restrict */

#include <limits.h>
#include <math.h>
#include <stdio.h>

#define ULBN_PUBLIC
#define ULBN_INTERNAL static
#define ULBN_PRIVATE static

#ifdef __cplusplus
extern "C" {
#endif

#if 1
typedef unsigned long ulbn_limb_t;
typedef signed long ulbn_slimb_t;
  #define ULBN_LIMB_MAX ULONG_MAX
#else
typedef unsigned char ulbn_limb_t;
typedef signed char ulbn_slimb_t;
  #define ULBN_LIMB_MAX UCHAR_MAX
#endif

#if defined(ULLONG_MAX) && ULLONG_MAX / ULBN_LIMB_MAX >= ULBN_LIMB_MAX
  #define ulbn_limb2_t unsigned long long
#endif


typedef unsigned long ulbn_bits_t;
typedef signed long ulbn_ssize_t;
typedef unsigned long ulbn_usize_t;
#define ULBN_USIZE_MAX ULONG_MAX
#define ULBN_SSIZE_MAX LONG_MAX
#define ULBN_SSIZE_MIN LONG_MIN

#define ULBN_USIZE_SMAX ulbn_cast_usize(ULBN_SSIZE_MAX)
#define ulbn_cast_usize(n) ul_static_cast(ulbn_usize_t, (n))
#define ulbn_cast_ssize(n) ul_static_cast(ulbn_ssize_t, (n))


#if defined(ULLONG_MAX)
typedef unsigned long long ulbn_ulong_t;
typedef signed long long ulbn_slong_t;
  #define ULBN_ULONG_BITS (sizeof(ulbn_ulong_t) * CHAR_BIT)
  #define ULBN_ULONG_MAX ULLONG_MAX
  #define ULBN_SLONG_MAX LLONG_MAX
  #define ULBN_SLONG_MIN LLONG_MIN
#else
typedef unsigned long ulbn_ulong_t;
typedef signed long ulbn_slong_t;
  #define ULBN_ULONG_BITS (sizeof(ulbn_ulong_t) * CHAR_BIT)
  #define ULBN_ULONG_MAX ULONG_MAX
  #define ULBN_SLONG_MAX LONG_MAX
  #define ULBN_SLONG_MIN LONG_MIN
#endif


/**
 * @def ULBN_CONF_CHECK_OVERFLOW
 * @brief Configuration: Whether to check for unsigned length integer overflow
 * @note This option is automatically disabled if the maximum value of ulbn_usize_t is less than SIZE_MAX
 */
#ifndef ULBN_CONF_CHECK_USIZE_OVERFLOW
  #if defined(SIZE_MAX) && ULBN_USIZE_MAX <= SIZE_MAX
    #define ULBN_CONF_CHECK_USIZE_OVERFLOW 0
  #else
    #define ULBN_CONF_CHECK_USIZE_OVERFLOW 1
  #endif
#endif

/**
 * @def ULBN_CONF_CHECK_OVERFLOW
 * @brief Configuration: Whether to check for signed length integer overflow
 */
#ifndef ULBN_CONF_CHECK_SSIZE_OVERFLOW
  #define ULBN_CONF_CHECK_SSIZE_OVERFLOW 1
#endif /* ULBN_CONF_CHECK_SSIZE_OVERFLOW */

/**
 * @def ULBN_CONF_CHECK_ALLOCATION_FAILURE
 * @brief Configuration: Whether to check for memory allocation failure
 * @note On Linux, it is usually not necessary to check for allocation failure, as realloc seems to never return NULL
 */
#ifndef ULBN_CONF_CHECK_ALLOCATION_FAILURE
  #ifdef __linux__
    #define ULBN_CONF_CHECK_ALLOCATION_FAILURE 0
  #else
    #define ULBN_CONF_CHECK_ALLOCATION_FAILURE 1
  #endif
#endif /* ULBN_CONF_CHECK_ALLOCATION_FAILURE */

/**
 * @def ULBN_CONF_CHECK_BITS_OVERFLOW
 * @brief Configuration: Whether to check for bits overflow
 */
#ifndef ULBN_CONF_CHECK_BITS_OVERFLOW
  #define ULBN_CONF_CHECK_BITS_OVERFLOW 1
#endif /* ULBN_CONF_CHECK_BITS_OVERFLOW */

/**
 * @def ULBN_CONF_HAS_DOUBLE
 * @brief Configuration: Whether to enable double precision floating point number
 */
#ifndef ULBN_CONF_HAS_DOUBLE
  #define ULBN_CONF_HAS_DOUBLE 1
#endif /* ULBN_CONF_HAS_DOUBLE */


/* <0 indicates a system error, >0 indicates a mathematical error
This error directly corresponds to the IEEE754 error code */
enum ULBN_MATH_ERROR_ENUM {
  /**
   * @brief Unauthorized out-of-range error
   * @note This is usually triggered by `ulbi_t`
   */
  ULBN_ERR_EXCEED_RANGE = -2,
  /**
   * @brief Memory error
   */
  ULBN_ERR_NOMEM = -1,

  ULBN_ERR_SUCCESS = 0,
  /**
   * @brief Pole error
   * @details The calculation results in infinity or undefined
   * @example 1/0, atan(pi/2)
   */
  ULBN_ERR_DIV_BY_ZERO = 2,
  /**
   * @brief Inexact result.
   * @note This error occurs very frequently and can usually be ignored.
   */
  ULBN_ERR_INEXACT = 4,
  /**
   * @brief Domain error
   * @example log(-1)
   */
  ULBN_ERR_INVALID = 8,
  /**
   * @brief Overflow error
   * @details The result is finite but rounded to infinity, or rounded down to the maximum finite value
   */
  ULBN_ERR_OVERFLOW = 16,
  /**
   * @brief Underflow error
   * @details The result is non-zero but rounded to zero
   */
  ULBN_ERR_UNDERFLOW = 32
};

typedef void* ulbn_alloc_func_t(void* opaque, void* ptr, size_t on, size_t nn);
typedef struct ulbn_alloc_t {
  ulbn_alloc_func_t* alloc_func;
  void* alloc_opaque;
} ulbn_alloc_t;
ULBN_PUBLIC ulbn_alloc_t* ulbn_default_alloc(void);


#if UINT_MAX >= 0xFFFFFFFFu
typedef unsigned ulbn_rand_uint_t;
#else
typedef unsigned long ulbn_rand_uint_t;
#endif
/* [PCG Random Number Generators](https://www.pcg-random.org/) */
typedef struct ulbn_rand_t {
  ulbn_rand_uint_t state;
  ulbn_rand_uint_t inc;

  unsigned cache;
  int bits;
} ulbn_rand_t;
ULBN_PUBLIC void ulbn_rand_init(ulbn_rand_t* rng);
ULBN_PUBLIC void ulbn_rand_init2(ulbn_rand_t* rng, ulbn_rand_uint_t seed);


typedef struct ulbi_t {
  ulbn_ssize_t len;
  ulbn_usize_t cap;
  ulbn_limb_t* ul_restrict limb;
} ulbi_t;
#define ULBI_INIT {0, 0, ul_nullptr}


/**
 * @brief Initialize a big integer
 * @note This function never fails
 * @return `o`
 */
ULBN_PUBLIC ulbi_t* ulbi_init(ulbi_t* o);
/**
 * @brief Initialize a big integer and reserve space
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_reserve(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n);
/**
 * @brief Set `dst` to zero
 * @note This function never fails
 */
ULBN_PUBLIC ulbi_t* ulbi_set_zero(ulbi_t* dst);

/**
 * @brief Deinitialize a big integer
 * @note After this, `o` will become 0. `o` is still usable but memory is freed
 */
ULBN_PUBLIC void ulbi_deinit(ulbn_alloc_t* alloc, ulbi_t* o);
/**
 * @brief Shrink the memory of `o`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory (in this case `o` remains unchanged, so this error can be ignored)
 */
ULBN_PUBLIC int ulbi_shrink(ulbn_alloc_t* alloc, ulbi_t* o);
/**
 * @brief Reserve space for at least `n` limbs in `o`
 * @return Non-null pointer if allocation is successful;
 * @return `NULL` if out of memory (handled as `ULBN_ERR_NOMEM`)
 */
ULBN_PUBLIC ulbn_limb_t* ulbi_reserve(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t n);


/**
 * @brief Swap `o1` and `o2`
 */
ULBN_PUBLIC void ulbi_swap(ulbi_t* o1, ulbi_t* o2);
/**
 * @brief `ro` = -`ao`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_neg(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao);
/**
 * @brief `ro` = abs(`ao`)
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_abs(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao);


/**
 * @brief Copy `src` to `dst`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_set_copy(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* src);
/**
 * @brief Move `src` to `dst`
 * @note This function never fails; after this `src` will be as if `ulbi_deinit` was called
 */
ULBN_PUBLIC void ulbi_set_move(ulbn_alloc_t* alloc, ulbi_t* dst, ulbi_t* src);
/**
 * @brief Set `dst` to `limb`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_set_limb(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_limb_t limb);
/**
 * @brief Set `dst` to `slimb`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_set_slimb(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_slimb_t slimb);
/**
 * @brief Set `dst` to `l`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_set_ulong(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ulong_t l);
/**
 * @brief Set `dst` to `l`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_set_slong(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_slong_t l);
/**
 * @brief Set `dst` to `l`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_set_usize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t l);
/**
 * @brief Set `dst` to `l`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_set_ssize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ssize_t l);
/**
 * @brief Set `dst` to 2^n
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_set_2exp_usize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t n);
/**
 * @brief Set `dst` to 2^n
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_INEXACT` if `n` is negative
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_set_2exp(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* n);
/**
 * @brief Set `dst` to the integer represented by `str` in base `base`
 * @note This function stops parsing when it encounters the first illegal character
 * @param base 0 means automatic detection;
 *  otherwise, it should be greater than or equal to 2 and less than or equal to 36
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `base` is invalid
 */
ULBN_PUBLIC int ulbi_set_string(ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, int base);


/**
 * @brief Initializes `dst` as a copy of `src`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_copy(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* src);
/**
 * @brief Initialize `dst` as a move from `src`
 * @note This function never fails; after this `src` will be as if `ulbi_deinit` was called
 */
ULBN_PUBLIC void ulbi_init_move(ulbn_alloc_t* alloc, ulbi_t* dst, ulbi_t* src);
/**
 * @brief Initialize `dst` with `limb`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_limb(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_limb_t limb);
/**
 * @brief Initialize `dst` with `slimb`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_slimb(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_slimb_t limb);
/**
 * @brief Initialize `dst` with `l`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_ulong(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ulong_t l);
/**
 * @brief Initialize `dst` with `l`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_slong(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_slong_t l);
/**
 * @brief Initialize `dst` with `l`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_usize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t l);
/**
 * @brief Initialize `dst` with `l`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_ssize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_ssize_t l);
/**
 * @brief Initialize `dst` with 2^n
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_2exp_usize(ulbn_alloc_t* alloc, ulbi_t* dst, ulbn_usize_t n);
/**
 * @brief Initialize `dst` with 2^n
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if `n` is too large;
 * @return `ULBN_ERR_INEXACT` if `n` is negative
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_2exp(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* n);
/**
 * @brief Initialize `dst` with the integer represented by `str` in base `base`
 * @note This function stops parsing when it encounters the first illegal character
 * @param base 0 means automatic detection;
 *  otherwise, it should be greater than or equal to 2 and less than or equal to 36
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if `base` is invalid
 */
ULBN_PUBLIC int ulbi_init_string(ulbn_alloc_t* alloc, ulbi_t* dst, const char* str, int base);


/**
 * @brief `ao` <=> `bo`
 * @return <0 if `ao` < `bo`;
 * @return 0 if `ao` == `bo`;
 * @return >0 if `ao` > `bo`
 */
ULBN_PUBLIC int ulbi_comp(const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ao` <=> `b`
 * @return <0 if `ao` < `b`;
 * @return 0 if `ao` == `b`;
 * @return >0 if `ao` > `b`
 */
ULBN_PUBLIC int ulbi_comp_limb(const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief `ao` <=> `b`
 * @return <0 if `ao` < `b`;
 * @return 0 if `ao` == `b`;
 * @return >0 if `ao` > `b`
 */
ULBN_PUBLIC int ulbi_comp_slimb(const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief `ao` <=> `b`
 * @return <0 if `ao` < `b`;
 * @return 0 if `ao` == `b`;
 * @return >0 if `ao` > `b`
 */
ULBN_PUBLIC int ulbi_comp_ulong(const ulbi_t* ao, ulbn_ulong_t b);
/**
 * @brief `ao` <=> `b`
 * @return <0 if `ao` < `b`;
 * @return 0 if `ao` == `b`;
 * @return >0 if `ao` > `b`
 */
ULBN_PUBLIC int ulbi_comp_slong(const ulbi_t* ao, ulbn_slong_t b);

/**
 * @brief Return `ao` == `bo`
 */
ULBN_PUBLIC int ulbi_eq(const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief Return `ao` == `b`
 */
ULBN_PUBLIC int ulbi_eq_limb(const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief Return `ao` == `b`
 */
ULBN_PUBLIC int ulbi_eq_slimb(const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief Return `ao` == `b`
 */
ULBN_PUBLIC int ulbi_eq_ulong(const ulbi_t* ao, ulbn_ulong_t b);
/**
 * @brief Return `ao` == `b`
 */
ULBN_PUBLIC int ulbi_eq_slong(const ulbi_t* ao, ulbn_slong_t b);


/**
 * @brief Get the sign of `o`
 * @return `1` if `o` is positive;
 * @return `-1` if `o` is negative;
 * @return `0` if `o` is zero
 */
ULBN_PUBLIC int ulbi_sign(const ulbi_t* o);
/**
 * @brief Check if `o` is zero
 * @return `1` if `o` is zero;
 * @return `0` if `o` is not zero
 */
ULBN_PUBLIC int ulbi_is_zero(const ulbi_t* o);
/**
 * @brief Check if `o` is even
 * @return `1` if `o` is even;
 * @return `0` if `o` is not even
 */
ULBN_PUBLIC int ulbi_is_even(const ulbi_t* o);
/**
 * @brief Check if `o` is odd
 * @return `1` if `o` is odd;
 * @return `0` if `o` is not odd
 */
ULBN_PUBLIC int ulbi_is_odd(const ulbi_t* o);


/**
 * @brief `ro` = `ao` + `bo`
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_add(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ro` = `ao` - `bo`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_sub(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);

/**
 * @brief `ro` = `ao` + `b`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_add_limb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief `ro` = `ao` - `b`
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_sub_limb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief `ro` = `a` - `bo`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_limb_sub(ulbn_alloc_t* alloc, ulbi_t* ro, ulbn_limb_t a, const ulbi_t* bo);

/**
 * @brief `ro` = `ao` + `b`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_add_slimb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief `ro` = `ao` - `b`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_sub_slimb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief `ro` = `a` - `bo`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_slimb_sub(ulbn_alloc_t* alloc, ulbi_t* ro, ulbn_slimb_t a, const ulbi_t* bo);


/**
 * @brief `ro` = `ao` * `b`
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_mul_limb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief `ro` = `ao` * `b`
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_mul_slimb(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief `ro` = `ao` * `bo`
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_mul(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);


/**
 * @brief `qo` = `ao` / `bo`, `ro` = `ao` % `bo`
 * @note `qo` and `ro` is allowed to be `NULL`
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if `ro` is NULL and the remainder is not zero;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_divmod(ulbn_alloc_t* alloc, ulbi_t* qo, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `qo` = `ao` / `bo`
 * @note `qo` is allowed to be `NULL`
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if the remainder is not zero;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_div(ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ro` = `ao` % `bo`
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_mod(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);

/**
 * @brief `qo` = `ao` / `b`, `ro` = The smallest non-negative number congruent to (`ao` % `b`) under modulo `b`
 * @note `qo` and `ro` is allowed to be `NULL`;
 * @note The representation of `ro` is different from `ulbi_divmod` because `ro` cannot store negative values
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if `ro` is NULL and the remainder is not zero;
 * @return `ULBN_ERR_INEXACT` if `ro` is not NULL but the remainder is negative;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_divmod_limb(ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_limb_t* ro, const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief `qo` = `ao` / `b`
 * @note `qo` is allowed to be `NULL`
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if the remainder is not zero;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_div_limb(ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, ulbn_limb_t b);
/**
 * @brief `ro` = The smallest non-negative number congruent to (`ao` % `b`) under modulo `b`
 * @note The representation of `ro` is different from `ulbi_divmod` because `ro` cannot store negative values
 * @return `ULBN_ERR_INEXACT` if `ro` is NULL and the remainder is not zero;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_mod_limb(ulbn_alloc_t* alloc, ulbn_limb_t* ro, const ulbi_t* ao, ulbn_limb_t b);

/**
 * @brief `qo` = `ao` / `b`, `ro` = `ao` % `b`
 * @note `qo` and `ro` is allowed to be `NULL`;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if `ro` is NULL and the remainder is not zero;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_divmod_slimb(ulbn_alloc_t* alloc, ulbi_t* qo, ulbn_slimb_t* ro, const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief `qo` = `ao` / `b`
 * @note `qo` is allowed to be `NULL`
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_INEXACT` if the remainder is not zero;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_div_slimb(ulbn_alloc_t* alloc, ulbi_t* qo, const ulbi_t* ao, ulbn_slimb_t b);
/**
 * @brief `ro` = `ao` % `b`
 * @return `ULBN_ERR_INEXACT` if `ro` is NULL and the remainder is not zero;
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_mod_slimb(ulbn_alloc_t* alloc, ulbn_slimb_t* ro, const ulbi_t* ao, ulbn_slimb_t b);


/**
 * @brief `ro` = `ao` ** b
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_pow(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b);


/**
 * @brief `ro` = `ao` & `bo`
 * @note The calculation is performed in the sense of two's complement
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_and(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ro` = `ao` | `bo`
 * @note The calculation is performed in the sense of two's complement
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_or(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ro` = `ao` ^ `bo`
 * @note The calculation is performed in the sense of two's complement
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_xor(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* bo);
/**
 * @brief `ro` = ~`ao`
 * @note The calculation is performed in the sense of two's complement
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_com(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao);


/**
 * @brief `ro` = `ao` << `b`
 * @note The calculation is performed in the sense of two's complement
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_sal_usize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b);
/**
 * @brief `ro` = `ao` >> `b`
 * @note The calculation is performed in the sense of two's complement
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_sar_usize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b);

/**
 * @brief `ro` = `ao` << `b`
 * @note The calculation is performed in the sense of two's complement
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_sal_ssize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t b);
/**
 * @brief `ro` = `ao` >> `b`
 * @note The calculation is performed in the sense of two's complement
 * @return `0` if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_sar_ssize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_ssize_t b);

/**
 * @brief `ro` = `ao` << `b`
 * @note The calculation is performed in the sense of two's complement
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_sal(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b);
/**
 * @brief `ro` = `ao` >> `b`
 * @note The calculation is performed in the sense of two's complement
 * @return `0` if successful;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_sar(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b);


/**
 * @brief Test whether the k-th bit is 1 in the sense of two's complement
 * @return 0 if the k-th bit is 0;
 * @return 1 if the k-th bit is 1
 */
ULBN_PUBLIC int ulbi_testbit_usize(const ulbi_t* o, ulbn_usize_t k);
/**
 * @brief Sets the k-th bit to 1 in two's complement representation
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return the original value of the k-th bit otherwise
 */
ULBN_PUBLIC int ulbi_setbit_usize(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k);
/**
 * @brief Set the k-th bit to 0 in two's complement representation
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return the original value of the k-th bit otherwise
 */
ULBN_PUBLIC int ulbi_resetbit_usize(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k);
/**
 * @brief Flip the k-th bit in two's complement representation
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if the result is out of range;
 * @return the original value of the k-th bit otherwise
 */
ULBN_PUBLIC int ulbi_combit_usize(ulbn_alloc_t* alloc, ulbi_t* o, ulbn_usize_t k);

/**
 * @brief Test whether the k-th bit is 1 in the sense of two's complement
 * @return 0 if the k-th bit is 0;
 * @return 1 if the k-th bit is 1
 */
ULBN_PUBLIC int ulbi_testbit(const ulbi_t* o, const ulbi_t* k);
/**
 * @brief Sets the k-th bit to 1 in two's complement representation
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if out of range;
 * @return the original value of the k-th bit otherwise
 */
ULBN_PUBLIC int ulbi_setbit(ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k);
/**
 * @brief Set the k-th bit to 0 in two's complement representation
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if out of range;
 * @return the original value of the k-th bit otherwise
 */
ULBN_PUBLIC int ulbi_resetbit(ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k);
/**
 * @brief Flip the k-th bit in two's complement representation
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if out of range;
 * @return the original value of the k-th bit otherwise
 */
ULBN_PUBLIC int ulbi_combit(ulbn_alloc_t* alloc, ulbi_t* o, const ulbi_t* k);


/**
 * @brief Converts `ao` to a number within the range of an n-bit unsigned binary number
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_as_uint_usize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b);
/**
 * @brief Converts `ao` to a number within the range of an n-bit signed binary number
 * @note If `b` == 2, the valid range of the number is -1 and 0
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_as_int_usize(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, ulbn_usize_t b);

/**
 * @brief Converts `ao` to a number within the range of an n-bit unsigned binary number
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if out of range;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_as_uint(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b);
/**
 * @brief Converts `ao` to a number within the range of an n-bit unsigned binary number
 * @return `ULBN_ERR_NOMEM` if out of memory;
 * @return `ULBN_ERR_EXCEED_RANGE` if out of range;
 * @return `0` otherwise
 */
ULBN_PUBLIC int ulbi_as_int(ulbn_alloc_t* alloc, ulbi_t* ro, const ulbi_t* ao, const ulbi_t* b);


/**
 * @brief Check if `o` is a power of 2
 */
ULBN_PUBLIC int ulbi_is_2pow(const ulbi_t* o);
/**
 * @brief Returns the number of trailing zeros in the two's complement representation of `o`
 * @note If `ro` == 0, return 0
 * @note Since the number may exceed `ulbn_usize_t`, the higher part will be stored in `p_rh` (if not NULL)
 * @return The lower part of the count
 */
ULBN_PUBLIC ulbn_usize_t ulbi_ctz_usize(const ulbi_t* ro, ulbn_usize_t* p_rh);
/**
 * @brief Returns the number of trailing ones in the two's complement representation of `o`
 * @note If `ro` == 0, return 0
 * @note Since the number may exceed `ulbn_usize_t`, the higher part will be stored in `p_rh` (if not NULL)
 * @return The lower part of the count
 */
ULBN_PUBLIC ulbn_usize_t ulbi_cto_usize(const ulbi_t* ro, ulbn_usize_t* p_rh);
/**
 * @brief Returns the number of 1s in the binary representation of the absolute value of `ro`
 * @note Since the number may exceed `ulbn_usize_t`, the higher part will be stored in `p_rh` (if not NULL)
 * @return The lower part of the count
 */
ULBN_PUBLIC ulbn_usize_t ulbi_abs_popcount_usize(const ulbi_t* ro, ulbn_usize_t* p_rh);
/**
 * @brief Get the minimum number of bits required to represent the absolute value of `ro`
 * @note If `ro` == 0, return 0
 * @note Since the number may exceed `ulbn_usize_t`, the higher part will be stored in `p_rh` (if not NULL)
 * @return The lower part of the count
 */
ULBN_PUBLIC ulbn_usize_t ulbi_abs_bit_width_usize(const ulbi_t* ro, ulbn_usize_t* p_rh);

/**
 * @brief Gets the number of trailing zeros in the two's complement representation of `o`
 * @note If `ro` == 0, return 0
 * @return 0 if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_ctz(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro);
/**
 * @brief Returns the number of trailing ones in the two's complement representation of `o`
 * @note If `ro` == 0, return 0
 * @return 0 if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_cto(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro);
/**
 * @brief Returns the number of 1s in the binary representation of the absolute value of `ro`
 * @return 0 if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_abs_popcount(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro);
/**
 * @brief Get the minimum number of bits required to represent the absolute value of `ro`
 * @return 0 if successful;
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_abs_bit_width(ulbn_alloc_t* alloc, ulbi_t* dst, const ulbi_t* ro);


/**
 * @brief Converts `src` to `ulbn_limb_t` type
 */
ULBN_PUBLIC ulbn_limb_t ulbi_to_limb(const ulbi_t* src);
/**
 * @brief Converts `src` to `ulbn_slimb_t` type
 */
ULBN_PUBLIC ulbn_slimb_t ulbi_to_slimb(const ulbi_t* src);
/**
 * @brief Converts `src` to `ulbn_ulong_t` type
 */
ULBN_PUBLIC ulbn_ulong_t ulbi_to_ulong(const ulbi_t* src);
/**
 * @brief Converts `src` to `ulbn_slong_t` type
 */
ULBN_PUBLIC ulbn_slong_t ulbi_to_slong(const ulbi_t* src);
/**
 * @brief Converts `src` to `ulbn_usize_t` type
 */
ULBN_PUBLIC ulbn_usize_t ulbi_to_usize(const ulbi_t* src);
/**
 * @brief Converts `src` to `ulbn_ssize_t` type
 */
ULBN_PUBLIC ulbn_ssize_t ulbi_to_ssize(const ulbi_t* src);

/**
 * @brief Check if `src` can be represented as `ulbn_limb_t`
 */
ULBN_PUBLIC int ulbi_fit_limb(const ulbi_t* src);
/**
 * @brief Check if `src` can be represented as `ulbn_slimb_t`
 */
ULBN_PUBLIC int ulbi_fit_slimb(const ulbi_t* src);
/**
 * @brief Check if `src` can be represented as `ulbn_ulong_t`
 */
ULBN_PUBLIC int ulbi_fit_ulong(const ulbi_t* src);
/**
 * @brief Check if `src` can be represented as `ulbn_slong_t`
 */
ULBN_PUBLIC int ulbi_fit_slong(const ulbi_t* src);
/**
 * @brief Check if `src` can be represented as `ulbn_usize_t`
 */
ULBN_PUBLIC int ulbi_fit_usize(const ulbi_t* src);
/**
 * @brief Check if `src` can be represented as `ulbn_ssize_t`
 */
ULBN_PUBLIC int ulbi_fit_ssize(const ulbi_t* src);


/**
 * @brief Converts `ao` to a string
 *
 * @param p_len If not `NULL`, the length of the string will be written into it
 * @param alloc_func Allocation function, ensuring the passed `ptr` is used for the returned string
 * @param alloc_opaque Parameter for the allocation function
 * @param base String base (2 <= base <= 36)
 *
 * @return String if successful (allocated by alloc_func);
 * @return `NULL` if memory is insufficient (considered as `ULBN_ERR_NOMEM`);
 * @return `NULL` if the base is invalid (considered as `ULBN_ERR_EXCEED_RANGE`)
 */
ULBN_PUBLIC char* ulbi_tostr_alloc(
  ulbn_alloc_t* alloc, ulbn_usize_t* p_len,          /* */
  ulbn_alloc_func_t* alloc_func, void* alloc_opaque, /* */
  const ulbi_t* ao, int base
);
/**
 * @brief Print `o` to `fp`
 *
 * @param base String base (2 <= base <= 36)
 *
 * @return `ULBN_ERR_NOMEM` if memory is insufficient;
 * @return `ULBN_ERR_EXCEED_RANGE` if `base` is invalid;
 * @return `0` if successful
 */
ULBN_PUBLIC int ulbi_print(ulbn_alloc_t* alloc, const ulbi_t* o, FILE* fp, int base);

#if ULBN_CONF_HAS_DOUBLE
/**
 * @brief Set `dst` to `x`
 * @return `0` if `x` can be exactly represented as an integer;
 * @return `ULBN_ERR_INEXACT` if `x` cannot be exactly represented as an integer (in this case `x` will be truncated);
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_set_double(ulbn_alloc_t* alloc, ulbi_t* dst, double x);
/**
 * @brief Initialize `dst` with `x`
 * @return `0` if `x` can be exactly represented as an integer;
 * @return `ULBN_ERR_INEXACT` if `x` cannot be exactly represented as an integer (in this case `x` will be truncated);
 * @return `ULBN_ERR_NOMEM` if out of memory
 */
ULBN_PUBLIC int ulbi_init_double(ulbn_alloc_t* alloc, ulbi_t* dst, double x);
/**
 * @brief Converts `src` to `double` type
 */
ULBN_PUBLIC double ulbi_to_double(const ulbi_t* src);
#endif /* ULBN_CONF_HAS_DOUBLE */


/**
 * @brief Set `dst` to a random number in the range [0, 2**n)
 */
ULBN_PUBLIC int ulbi_set_rand_usize(ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_usize_t n);
/**
 * @brief Set `dst` to a random number in the range [0, 2**n)
 */
ULBN_PUBLIC int ulbi_set_rand(ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* n);
/**
 * @brief Initialize `dst` with a random number in the range [0, 2**n)
 */
ULBN_PUBLIC int ulbi_init_rand_usize(ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, ulbn_usize_t n);
/**
 * @brief Initialize `dst` with a random number in the range [0, 2**n)
 */
ULBN_PUBLIC int ulbi_init_rand(ulbn_alloc_t* alloc, ulbn_rand_t* rng, ulbi_t* dst, const ulbi_t* n);


#ifdef __cplusplus
}
#endif

#endif /* ULBN_H */
