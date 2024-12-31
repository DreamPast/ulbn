#include "test.h"

static void testAdd(void) {
  ulbi_t ao = ULBI_INIT, bo = ULBI_INIT, ro = ULBI_INIT;
  /* ulbn_ulong_t, ulbn_slong_t */
  {
    ulbi_set_ulong(&ao, ULBN_ULONG_MAX);
    t_assert_err(ulbi_add_slimb(alloc, &ao, &ao, 1), 0);
    t_assert(ulbi_comp_ulong(&ao, ULBN_ULONG_MAX) > 0);

    ulbi_set_slong(&ao, ULBN_SLONG_MAX);
    t_assert_err(ulbi_add_slimb(alloc, &ao, &ao, 1), 0);
    t_assert(ulbi_comp_slong(&ao, ULBN_SLONG_MAX) > 0);

    ulbi_set_slong(&ao, ULBN_SLONG_MIN);
    t_assert_err(ulbi_add_slimb(alloc, &ao, &ao, -1), 0);
    t_assert(ulbi_comp_slong(&ao, ULBN_SLONG_MIN) < 0);
  }
  /* overflow */
  {
    t_bi_max(&ao);
    ulbi_set_copy(alloc, &bo, &ao);
    t_assert_err(ulbi_add(alloc, &ro, &ao, &bo), ULBN_ERR_EXCEED_RANGE);
  }
  /* overlap */
  {
    ulbi_set_slong(&ao, ULBN_SLONG_MAX);
    ulbi_set_slong(&bo, ULBN_SLONG_MAX);
    t_assert_err(ulbi_add(alloc, &ro, &ao, &bo), 0);

    ulbi_set_slong(&ao, ULBN_SLONG_MAX);
    ulbi_set_slong(&bo, ULBN_SLONG_MAX);
    t_assert_err(ulbi_add(alloc, &ao, &ao, &bo), 0);
    t_assert(ulbi_eq(&ao, &ro));

    ulbi_set_slong(&ao, ULBN_SLONG_MAX);
    ulbi_set_slong(&bo, ULBN_SLONG_MAX);
    t_assert_err(ulbi_add(alloc, &bo, &ao, &bo), 0);
    t_assert(ulbi_eq(&bo, &ro));

    ulbi_set_slong(&ao, ULBN_SLONG_MAX);
    t_assert_err(ulbi_add(alloc, &ao, &ao, &ao), 0);
    t_assert(ulbi_eq(&ao, &ro));
  }
  ulbi_deinit(alloc, &ao);
  ulbi_deinit(alloc, &bo);
  ulbi_deinit(alloc, &ro);
}

static void testSub(void) {
  ulbi_t ao = ULBI_INIT, bo = ULBI_INIT, ro = ULBI_INIT;
  /* ulbn_ulong_t, ulbn_slong_t */
  {
    ulbi_set_ulong(&ao, ULBN_ULONG_MAX);
    t_assert_err(ulbi_sub_slimb(alloc, &ao, &ao, -1), 0);
    t_assert(ulbi_comp_ulong(&ao, ULBN_ULONG_MAX) > 0);

    ulbi_set_slong(&ao, ULBN_SLONG_MAX);
    t_assert_err(ulbi_sub_slimb(alloc, &ao, &ao, -1), 0);
    t_assert(ulbi_comp_slong(&ao, ULBN_SLONG_MAX) > 0);

    ulbi_set_slong(&ao, ULBN_SLONG_MIN);
    t_assert_err(ulbi_sub_slimb(alloc, &ao, &ao, 1), 0);
    t_assert(ulbi_comp_slong(&ao, ULBN_SLONG_MIN) < 0);
  }
  /* overlap */
  {
    ulbi_set_slong(&ao, ULBN_SLONG_MAX);
    ulbi_set_slong(&bo, ULBN_SLONG_MIN);
    t_assert_err(ulbi_sub(alloc, &ro, &ao, &bo), 0);

    ulbi_set_slong(&ao, ULBN_SLONG_MAX);
    ulbi_set_slong(&bo, ULBN_SLONG_MIN);
    t_assert_err(ulbi_sub(alloc, &ao, &ao, &bo), 0);
    t_assert(ulbi_eq(&ao, &ro));

    ulbi_set_slong(&ao, ULBN_SLONG_MAX);
    ulbi_set_slong(&bo, ULBN_SLONG_MIN);
    t_assert_err(ulbi_sub(alloc, &bo, &ao, &bo), 0);
    t_assert(ulbi_eq(&bo, &ro));

    ulbi_set_slong(&ao, ULBN_SLONG_MAX);
    t_assert_err(ulbi_sub(alloc, &ao, &ao, &ao), 0);
    t_assert(ulbi_eq_slimb(&ao, 0));
  }
  ulbi_deinit(alloc, &ao);
  ulbi_deinit(alloc, &bo);
  ulbi_deinit(alloc, &ro);
}

static void testMultiplication(void) {
  ulbi_t ao = ULBI_INIT, bo = ULBI_INIT, ro = ULBI_INIT;
  /* overflow */
  {
    t_bi_max(&ao);
    t_bi_max(&bo);
    t_assert_err(ulbi_mul(alloc, &ro, &ao, &bo), ULBN_ERR_EXCEED_RANGE);
  }
  /* overlap */
  {
    t_bi_fill(&ao, ul_static_cast(size_t, SSIZE_LIMIT / 2));
    t_bi_fill(&bo, ul_static_cast(size_t, SSIZE_LIMIT / 2));
    t_assert_err(ulbi_mul(alloc, &ro, &ao, &bo), 0);

    t_assert_err(ulbi_mul(alloc, &ao, &ao, &bo), 0);
    t_assert(ulbi_eq(&ao, &ro));

    t_assert_err(ulbi_mul(alloc, &bo, &bo, &bo), 0);
    t_assert(ulbi_eq(&bo, &ro));
  }
  ulbi_deinit(alloc, &ao);
  ulbi_deinit(alloc, &bo);
  ulbi_deinit(alloc, &ro);
}

static void testDivisionModulo(void) {
  ulbi_t ao = ULBI_INIT, bo = ULBI_INIT, qo = ULBI_INIT, ro = ULBI_INIT;
  /* divide by zero */
  { t_assert_err(ulbi_divmod_slimb(alloc, &qo, ul_nullptr, &ao, 0), ULBN_ERR_DIV_BY_ZERO); }
  /* overlop */
  { /* a == b */
    ulbi_set_slong(&ao, 17);
    t_assert(ulbi_divmod(alloc, ul_nullptr, ul_nullptr, &ao, &ao) == 0);

    ulbi_set_slong(&ao, 17);
    t_assert(ulbi_divmod(alloc, ul_nullptr, &ro, &ao, &ao) == 0);
    t_assert(ulbi_eq_slong(&ro, 0));

    ulbi_set_slong(&ao, 17);
    t_assert(ulbi_divmod(alloc, &qo, ul_nullptr, &ao, &ao) == 0);
    t_assert(ulbi_eq_slong(&qo, 1));


    ulbi_set_slong(&ao, 17);
    t_assert(ulbi_divmod(alloc, ul_nullptr, &ao, &ao, &ao) == 0);
    t_assert(ulbi_eq_slong(&ao, 0));

    ulbi_set_slong(&ao, 17);
    t_assert(ulbi_divmod(alloc, &ao, ul_nullptr, &ao, &ao) == 0);
    t_assert(ulbi_eq_slong(&ao, 1));

    ulbi_set_slong(&ao, 17);
    t_assert(ulbi_divmod(alloc, &ao, &ao, &ao, &ao) == 0);
    t_assert(ulbi_eq_slong(&ao, 1) || ulbi_eq_slong(&ao, 0));
  }
  { /* q == a */
    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &qo, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&qo, 1) && ulbi_eq_slong(&ro, 4));
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ro, 4));
    t_assert_err(ulbi_divmod(alloc, &qo, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&qo, 1));

    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &ao, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ao, 1) && ulbi_eq_slong(&ro, 4));
    ulbi_set_slong(&ao, 17);
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ro, 4));
    ulbi_set_slong(&ao, 17);
    t_assert_err(ulbi_divmod(alloc, &ao, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&ao, 1));

    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &ao, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ao, 1) && ulbi_eq_slong(&ro, 4));
    ulbi_set_slong(&ao, 17);
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ro, 4));
    ulbi_set_slong(&ao, 17);
    t_assert_err(ulbi_divmod(alloc, &ao, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&ao, 1));
  }
  { /* r == a */
    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &qo, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&qo, 1) && ulbi_eq_slong(&ro, 4));
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ro, 4));
    t_assert_err(ulbi_divmod(alloc, &qo, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&qo, 1));

    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &qo, &ao, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&qo, 1) && ulbi_eq_slong(&ao, 4));
    ulbi_set_slong(&ao, 17);
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &ao, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ao, 4));
    ulbi_set_slong(&ao, 17);
    t_assert_err(ulbi_divmod(alloc, &qo, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&qo, 1));

    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &qo, &ao, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&qo, 1) && ulbi_eq_slong(&ao, 4));
    ulbi_set_slong(&ao, 17);
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &ao, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ao, 4));
    ulbi_set_slong(&ao, 17);
    t_assert_err(ulbi_divmod(alloc, &qo, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&qo, 1));
  }
  { /* q == b */
    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &qo, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&qo, 1) && ulbi_eq_slong(&ro, 4));
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ro, 4));
    t_assert_err(ulbi_divmod(alloc, &qo, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&qo, 1));

    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &bo, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&bo, 1) && ulbi_eq_slong(&ro, 4));
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ro, 4));
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &bo, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&bo, 1));

    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &bo, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&bo, 1) && ulbi_eq_slong(&ro, 4));
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ro, 4));
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &bo, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&bo, 1));
  }
  { /* r == b */
    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &qo, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&qo, 1) && ulbi_eq_slong(&ro, 4));
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &ro, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&ro, 4));
    t_assert_err(ulbi_divmod(alloc, &qo, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&qo, 1));

    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &qo, &bo, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&qo, 1) && ulbi_eq_slong(&bo, 4));
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &bo, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&bo, 4));
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &qo, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&qo, 1));

    ulbi_set_slong(&ao, 17);
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &qo, &bo, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&qo, 1) && ulbi_eq_slong(&bo, 4));
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, ul_nullptr, &bo, &ao, &bo), 0);
    t_assert(ulbi_eq_slong(&bo, 4));
    ulbi_set_slong(&bo, 13);
    t_assert_err(ulbi_divmod(alloc, &qo, ul_nullptr, &ao, &bo), ULBN_ERR_INEXACT);
    t_assert(ulbi_eq_slong(&qo, 1));
  }
  ulbi_deinit(alloc, &ao);
  ulbi_deinit(alloc, &bo);
  ulbi_deinit(alloc, &qo);
  ulbi_deinit(alloc, &ro);
}

static void testPow(void) {
  ulbi_t ro = ULBI_INIT, ao = ULBI_INIT, bo = ULBI_INIT;
  /* overflow */
  {
    t_bi_max(&ao);
    ulbi_set_limb(&bo, ULBN_LIMB_MAX);
    t_assert_err(ulbi_pow(alloc, &ro, &ao, &bo), ULBN_ERR_EXCEED_RANGE);

    t_assert_err(ulbi_add_limb(alloc, &bo, &bo, 1), 0);
    t_assert_err(ulbi_pow(alloc, &ro, &ao, &bo), ULBN_ERR_EXCEED_RANGE);

    t_assert_err(ulbi_mul_limb(alloc, &bo, &bo, ULBN_LIMB_MAX), 0);
    t_assert_err(ulbi_pow(alloc, &ro, &ao, &bo), ULBN_ERR_EXCEED_RANGE);

    t_assert_err(ulbi_add_limb(alloc, &bo, &bo, 1), 0);
    t_assert_err(ulbi_pow(alloc, &ro, &ao, &bo), ULBN_ERR_EXCEED_RANGE);
  }
  ulbi_deinit(alloc, &ro);
  ulbi_deinit(alloc, &ao);
  ulbi_deinit(alloc, &bo);
}

static void test(void) {
  testAdd();
  testSub();
  testMultiplication();
  testDivisionModulo();
  testPow();
}

T_MAIN(test)
