typedef unsigned char ulbn_limb_t;
typedef signed char ulbn_slimb_t;
#define ULBN_LIMB_MAX UCHAR_MAX
#define ULBN_SLIMB_MAX SCHAR_MAX
#define ULBN_SLIMB_MIN SCHAR_MIN

typedef unsigned char ulbn_usize_t;
typedef signed char ulbn_ssize_t;
#define ULBN_USIZE_MAX UCHAR_MAX
#define ULBN_SSIZE_MAX SCHAR_MAX
#define ULBN_SSIZE_MIN SCHAR_MIN

#include "ulbn.h"
#include <stddef.h>
#include <stdlib.h>
#include <string.h>


#define T_API ul_unused static


#if (defined(__GNUC__) && __GNUC__ >= 3) || defined(__clang__)
  #define T_FUNC __func__
#elif defined(_MSC_VER)
  #define T_FUNC __FUNCTION__
#else
  #define T_FUNC "<unknown>"
#endif
T_API void __t_assert(const char* file, int line, const char* func) {
  fprintf(stderr, "Assetion failed on %s:%d (%s): ", file, line, func);
}
#define __T_ASSERT_ARG const char *file, int line, const char *func
#define __T_ASSERT_MACRO __FILE__, __LINE__, T_FUNC
#define __T_ASSERT __t_assert(file, line, func)

T_API void _t_assert(const char* msg, __T_ASSERT_ARG) {
  __T_ASSERT;
  fprintf(stderr, "%s\n", msg);
  abort();
}
#define t_assert(cond) (ul_unlikely(!(cond)) ? _t_assert(#cond, __T_ASSERT_MACRO) : (void)0)

T_API const char* _t_bn_err(int err) {
  switch(err) {
  case ULBN_ERR_EXTERNAL:
    return "external error (-3)";
  case ULBN_ERR_EXCEED_RANGE:
    return "exceed range (-2)";
  case ULBN_ERR_NOMEM:
    return "out of memory (-1)";
  case ULBN_ERR_SUCCESS:
    return "success (0)";
  case ULBN_ERR_DIV_BY_ZERO:
    return "div by zero (2)";
  case ULBN_ERR_INEXACT:
    return "inexact (4)";
  case ULBN_ERR_INVALID:
    return "invalid (8)";
  case ULBN_ERR_OVERFLOW:
    return "overflow (16)";
  case ULBN_ERR_UNDERFLOW:
    return "underflow (32)";
  default:
    return ul_nullptr;
  }
}
T_API void _t_assert_err(int run_err, int expect_err, __T_ASSERT_ARG) {
  if(run_err != expect_err) {
    const char* msg;
    __T_ASSERT;
    fprintf(stderr, "expect error [");
    msg = _t_bn_err(expect_err);
    if(msg)
      fprintf(stderr, "%s", msg);
    else
      fprintf(stderr, "%d", expect_err);
    fprintf(stderr, "] but get [");
    msg = _t_bn_err(run_err);
    if(msg)
      fprintf(stderr, "%s", msg);
    else
      fprintf(stderr, "%d", run_err);
    fprintf(stderr, "]\n");
    abort();
  }
}
#define t_assert_err(run_err, expect_err) _t_assert_err(run_err, expect_err, __T_ASSERT_MACRO)


static const size_t t_sizet_max = ~ul_static_cast(size_t, 0);

static size_t alloc_mem = 0;
T_API void* _t_alloc_func(void* opaque, void* ptr, size_t on, size_t nn) {
  (void)opaque;
  if(nn == 0) {
    t_assert(on != 0);
    t_assert(ptr != ul_nullptr);
    t_assert(alloc_mem >= on);
    free(ptr);
    alloc_mem -= on;
    return ul_nullptr;
  } else {
    t_assert(alloc_mem >= on);
    t_assert(on <= nn || alloc_mem <= t_sizet_max - nn + on);
    ptr = realloc(ptr, nn);
    t_assert(ptr != ul_nullptr);
    alloc_mem += nn - on;
    return ptr;
  }
}
static const ulbn_alloc_t _alloc = { _t_alloc_func, ul_nullptr };
static const ulbn_alloc_t* const alloc = &_alloc;


static ulbn_rand_t _rng;
static ulbn_rand_t* rng = &_rng;


static ulbi_t t_bi_slots[16];
static unsigned t_bi_slots_used = 0;
T_API ulbi_t* t_bix(void) {
  ulbi_t* ret = &t_bi_slots[(t_bi_slots_used++) & 0xF];
  ulbi_deinit(alloc, ret);
  return ret;
}
T_API ulbi_t* t_bi(const char* str) {
  ulbi_t* ret = t_bix();
  t_assert_err(ulbi_set_string(alloc, ret, str, 10), 0);
  return ret;
}


static ulbn_usize_t USIZE_LIMIT;
static ulbn_usize_t BI_LEN_LIMIT;
static const unsigned char LIMB_BITS = sizeof(ulbn_limb_t) * CHAR_BIT;
T_API void t_startup(void) {
  unsigned i;
  ulbn_startup();
  alloc_mem = 0;
  for(i = 0; i < 16; ++i)
    ulbi_init(&t_bi_slots[i]);
  USIZE_LIMIT = ulbn_usize_limit();
  BI_LEN_LIMIT = ulbi_len_limit();
  ulbn_rand_init(rng);
}
T_API void t_shutdown(void) {
  unsigned i;
  for(i = 0; i < 16; ++i)
    ulbi_deinit(alloc, &t_bi_slots[i]);
  t_assert(alloc_mem == 0);
}


T_API ulbi_t* t_bi_fill(ulbi_t* bi, size_t num) {
  char* mem = ul_reinterpret_cast(char*, malloc(num));
  memset(mem, 0xFF, num);
  t_assert_err(ulbi_set_bytes_unsigned_le(alloc, bi, mem, num), 0);
  free(mem);
  return bi;
}
T_API ulbi_t* t_bi_max(ulbi_t* bi) {
  return t_bi_fill(bi, ul_static_cast(size_t, BI_LEN_LIMIT));
}


#define T_MAIN(func) \
  int main(void) {   \
    t_startup();     \
    func();          \
    t_shutdown();    \
  }
