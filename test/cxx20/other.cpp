#include "test.hpp"

void testException() {
  puts("======Test Exception");

  T_assert(ul::bn::Exception(ULBN_ERR_NOMEM) == ULBN_ERR_NOMEM);
  T_assert(ul::bn::Exception(ULBN_ERR_EXCEED_RANGE) == ULBN_ERR_EXCEED_RANGE);
  T_assert(ul::bn::Exception(ULBN_ERR_SUCCESS) == ULBN_ERR_SUCCESS);
  T_assert(ul::bn::Exception(ULBN_ERR_DIV_BY_ZERO) == ULBN_ERR_DIV_BY_ZERO);
  T_assert(ul::bn::Exception(ULBN_ERR_INEXACT) == ULBN_ERR_INEXACT);
  T_assert(ul::bn::Exception(ULBN_ERR_INVALID) == ULBN_ERR_INVALID);
  T_assert(ul::bn::Exception(ULBN_ERR_OVERFLOW) == ULBN_ERR_OVERFLOW);
  T_assert(ul::bn::Exception(ULBN_ERR_UNDERFLOW) == ULBN_ERR_UNDERFLOW);
  T_assert(ul::bn::Exception(-100) == -100);
}
void testOther() {
  puts("===Test Other");

  auto ctx = ulbn_default_alloc();

  {  // ulbi_divmod_limb: b = 0
    ulbn_limb_t r;
    BigInt q;
    T_assert(ulbi_divmod_limb(ctx, q.get(), &r, (0_bi).get(), 0) == ULBN_ERR_DIV_BY_ZERO);
    T_assert(q == 0 && r == 0);
  }

  {  // ulbi_divmod_slimb: b = 0
    ulbn_slimb_t r;
    BigInt q;
    T_assert(ulbi_divmod_slimb(ctx, q.get(), &r, (0_bi).get(), 0) == ULBN_ERR_DIV_BY_ZERO);
    T_assert(q == 0 && r == 0);
  }

  {  // ulbi_divmod: bn == 0
    BigInt q, r;
    T_assert(ulbi_divmod(ctx, q.get(), r.get(), (0_bi).get(), (0_bi).get()) == ULBN_ERR_DIV_BY_ZERO);
    T_assert(q == 0 && r == 0);
  }

  {  // ulbi_divmod: qo == ro
    BigInt r;
    T_assert(ulbi_divmod(ctx, r.get(), r.get(), (12_bi).get(), (12_bi).get()) == 0);
    T_assert(r == 0);
  }

  {  // ulbi_init_2exp_usize
    for(uint8_t i = 0; i <= 16; ++i) {
      ulbi_t x[1];
      T_assert(ulbi_init_2exp_bits(ctx, x, i) == 0);
      T_assert(BigInt(x) == (1 << i));
      ulbi_deinit(ctx, x);
    }
  }

  {  // ulbi_init_move
    BigInt x = 12;
    ulbi_t y[1];
    ulbi_init_move(ctx, y, x.get());
    T_assert(x == 0 && ulbi_eq_slimb(y, 12));
    ulbi_deinit(ctx, y);
  }

  {  // ulbi_init_string, ulbi_set_string: base = -1
    ulbi_t x[1];
    T_assert(ulbi_init_string(ctx, x, "12", -1) == ULBN_ERR_BAD_ARGUMENT);
    ulbi_deinit(ctx, x);
  }

  {  // ulbi_set_move
    BigInt x = 12;
    BigInt y;
    y = std::move(x);
    T_assert(x == 0 && y == 12);
  }

  {  // ulbi_swap
    BigInt x = 12, y = 13;
    x.swap(y);
    T_assert(x == 13 && y == 12);
  }

  {  // ulbi_reserve, ulbi_shrink, ulbi_set_zero
    BigInt x = BigInt::fromReserve(12);
    T_assert(x == 0);
    x.shrink();
    T_assert(x == 0);

    x = 12;
    x.shrink();
    T_assert(x == 12);

    ulbi_set_zero(x.get());
    x.shrink();
    T_assert(x == 0);
  }

  {  // ulbi_init_reserve
    ulbi_t x[1];
    ulbi_init_reserve(ctx, x, 12);
    ulbi_deinit(ctx, x);
    T_assert(ulbi_is_zero(x));
    ulbi_init_reserve(ctx, x, 0);
    ulbi_deinit(ctx, x);
    T_assert(ulbi_is_zero(x));
  }
}

void test() {
  testException();
  testOther();
}

int main() {
  testIt(test);
  return 0;
}
