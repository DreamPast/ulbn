#include <stdexcept>
#include <string>
#include <unordered_map>

#include "ulbn.h"

namespace ul {
namespace bn {

class Exception: public std::runtime_error {
public:
  explicit Exception(int err): std::runtime_error(_make_message(err)), _error(err) { }

  int get_error() const {
    return _error;
  }

  friend bool operator==(Exception lhs, Exception rhs) {
    return lhs.get_error() == rhs.get_error();
  }
  friend bool operator==(Exception lhs, int rhs) {
    return lhs.get_error() == rhs;
  }
  friend bool operator==(int lhs, Exception rhs) {
    return rhs.get_error() == lhs;
  }

private:
  static std::string _make_message(int err) {
    switch(err) {
    case ULBN_ERR_EXCEED_RANGE:
      return "unauthorized out-of-range error";
    case ULBN_ERR_NOMEM:
      return "memory error";
    case ULBN_ERR_SUCCESS:
      return "success";
    case ULBN_ERR_DIV_BY_ZERO:
      return "pole error";
    case ULBN_ERR_INEXACT:
      return "inexact result";
    case ULBN_ERR_INVALID:
      return "domain error";
    case ULBN_ERR_OVERFLOW:
      return "overflow error";
    case ULBN_ERR_UNDERFLOW:
      return "underflow error";
    default:
      return "<unknown error>";
    };
  }
  int _error;
};

template<class T>
concept FitSlong = requires {
  requires std::is_integral_v<T>;
  requires std::is_signed_v<T>;
  requires sizeof(T) <= sizeof(ulbn_slong_t);
  requires std::is_convertible_v<T, ulbn_slong_t>;
};
template<class T>
concept FitUlong = requires {
  requires std::is_integral_v<T>;
  requires std::is_unsigned_v<T>;
  requires sizeof(T) <= sizeof(ulbn_ulong_t);
  requires std::is_convertible_v<T, ulbn_ulong_t>;
};
template<class T>
concept FitLimb = requires {
  requires std::is_integral_v<T>;
  requires std::is_unsigned_v<T>;
  requires sizeof(T) <= sizeof(ulbn_limb_t);
  requires std::is_convertible_v<T, ulbn_limb_t>;
};
template<class T>
concept FitSlimb = requires {
  requires std::is_integral_v<T>;
  requires std::is_signed_v<T>;
  requires sizeof(T) <= sizeof(ulbn_slimb_t);
  requires std::is_convertible_v<T, ulbn_slimb_t>;
};
template<class T>
concept FitUsize = requires {
  requires std::is_integral_v<T>;
  requires std::is_unsigned_v<T>;
  requires sizeof(T) <= sizeof(ulbn_usize_t);
  requires std::is_convertible_v<T, ulbn_usize_t>;
};
template<class T>
concept FitSsize = requires {
  requires std::is_integral_v<T>;
  requires std::is_signed_v<T>;
  requires sizeof(T) <= sizeof(ulbn_ssize_t);
  requires std::is_convertible_v<T, ulbn_ssize_t>;
};
#if ULBN_CONF_HAS_DOUBLE
template<class T>
concept FitDouble = requires {
  requires std::is_floating_point_v<T>;
  requires sizeof(T) <= sizeof(double);
  requires std::is_convertible_v<T, double>;
};
#endif /* ULBN_CONF_HAS_DOUBLE */

class BigInt {
public:
  BigInt() noexcept {
    ulbi_init(_value);
  }
  ~BigInt() noexcept {
    ulbi_deinit(_ctx(), _value);
  }

  BigInt(const BigInt& other) {
    _check(ulbi_init_copy(_ctx(), _value, other._value));
  }
  BigInt(BigInt&& other) noexcept {
    ulbi_init_move(_ctx(), _value, other._value);
  }
  BigInt& operator=(const BigInt& other) {
    _check(ulbi_set_copy(_ctx(), _value, other._value));
    return *this;
  }
  BigInt& operator=(BigInt&& other) noexcept {
    ulbi_set_move(_ctx(), _value, other._value);
    return *this;
  }

  BigInt(const char* str, int base = 0) {
    _check(ulbi_init_string(_ctx(), _value, str, base));
  }
  BigInt(const std::string& str, int base = 0) {
    _check(ulbi_init_string(_ctx(), _value, str.c_str(), base));
  }
  BigInt& operator=(const char* str) {
    _check(ulbi_set_string(_ctx(), _value, str, 0));
    return *this;
  }
  BigInt& operator=(const std::string& str) {
    _check(ulbi_set_string(_ctx(), _value, str.c_str(), 0));
    return *this;
  }

  BigInt(const ulbi_t* src) {
    _check(ulbi_init_copy(_ctx(), _value, src));
  }
  BigInt& operator=(const ulbi_t* src) {
    _check(ulbi_set_copy(_ctx(), _value, src));
    return *this;
  }

  template<FitSlong T>
  BigInt(T value) {
    _check(ulbi_init_slong(_ctx(), _value, static_cast<ulbn_slong_t>(value)));
  }
  template<FitUlong T>
  BigInt(T value) {
    _check(ulbi_init_ulong(_ctx(), _value, static_cast<ulbn_ulong_t>(value)));
  }
  template<FitSlong T>
  BigInt& operator=(T value) {
    _check(ulbi_set_slong(_ctx(), _value, static_cast<ulbn_slong_t>(value)));
    return *this;
  }
  template<FitUlong T>
  BigInt& operator=(T value) {
    _check(ulbi_set_ulong(_ctx(), _value, static_cast<ulbn_ulong_t>(value)));
    return *this;
  }

  BigInt(ulbn_limb_t limb) {
    _check(ulbi_init_limb(_ctx(), _value, limb));
  }
  BigInt(ulbn_slimb_t slimb) {
    _check(ulbi_init_slimb(_ctx(), _value, slimb));
  }
  BigInt& operator=(ulbn_limb_t limb) {
    _check(ulbi_set_limb(_ctx(), _value, limb));
    return *this;
  }
  BigInt& operator=(ulbn_slimb_t slimb) {
    _check(ulbi_set_slimb(_ctx(), _value, slimb));
    return *this;
  }


  BigInt& move_from(ulbi_t* src) noexcept {
    ulbi_set_move(_ctx(), _value, src);
    return *this;
  }
  BigInt& move_from(BigInt& src) noexcept {
    ulbi_set_move(_ctx(), _value, src._value);
    return *this;
  }

  static BigInt from_2exp(ulbn_usize_t n) {
    BigInt ret;
    _check(ulbi_set_2exp(_ctx(), ret._value, n));
    return ret;
  }
  static BigInt from_reserve(ulbn_usize_t n) {
    BigInt ret;
    _check(ulbi_reserve(_ctx(), ret._value, n) ? 0 : ULBN_ERR_NOMEM);
    return ret;
  }


  BigInt& operator+=(const BigInt& other) {
    _check(ulbi_add(_ctx(), _value, _value, other._value));
    return *this;
  }
  template<FitLimb T>
  BigInt& operator+=(T value) {
    _check(ulbi_add_limb(_ctx(), _value, _value, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator+=(T value) {
    _check(ulbi_add_slimb(_ctx(), _value, _value, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }

  friend BigInt operator+(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_add(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator+(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_add_limb(_ctx(), ret._value, lhs._value, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator+(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_add_slimb(_ctx(), ret._value, lhs._value, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator+(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_add_limb(_ctx(), ret._value, rhs._value, static_cast<ulbn_limb_t>(lhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator+(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_add_slimb(_ctx(), ret._value, rhs._value, static_cast<ulbn_slimb_t>(lhs)));
    return ret;
  }

  BigInt& operator-=(const BigInt& other) {
    _check(ulbi_sub(_ctx(), _value, _value, other._value));
    return *this;
  }
  template<FitLimb T>
  BigInt& operator-=(T value) {
    _check(ulbi_sub_limb(_ctx(), _value, _value, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator-=(T value) {
    _check(ulbi_sub_slimb(_ctx(), _value, _value, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }

  friend BigInt operator-(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_sub(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator-(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_sub_limb(_ctx(), ret._value, lhs._value, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator-(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_sub_slimb(_ctx(), ret._value, lhs._value, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator-(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_limb_sub(_ctx(), ret._value, static_cast<ulbn_limb_t>(lhs), rhs._value));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator-(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_slimb_sub(_ctx(), ret._value, static_cast<ulbn_slimb_t>(lhs), rhs._value));
    return ret;
  }


  BigInt& operator++() {
    _check(ulbi_add_limb(_ctx(), _value, _value, 1));
    return *this;
  }
  BigInt operator++(int) {
    BigInt ret(*this);
    _check(ulbi_add_limb(_ctx(), _value, _value, 1));
    return ret;
  }
  BigInt& operator--() {
    _check(ulbi_sub_limb(_ctx(), _value, _value, 1));
    return *this;
  }
  BigInt operator--(int) {
    BigInt ret(*this);
    _check(ulbi_sub_limb(_ctx(), _value, _value, 1));
    return ret;
  }


  BigInt operator+() const {
    return *this;
  }
  BigInt operator-() const {
    BigInt ret;
    _check(ulbi_neg(_ctx(), ret._value, _value));
    return ret;
  }
  BigInt abs() const {
    BigInt ret;
    _check(ulbi_abs(_ctx(), ret._value, _value));
    return ret;
  }


  BigInt& operator*=(const BigInt& other) {
    _check(ulbi_mul(_ctx(), _value, _value, other._value));
    return *this;
  }
  friend BigInt operator*(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_mul(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }

  template<FitLimb T>
  BigInt& operator*=(T value) {
    _check(ulbi_mul_limb(_ctx(), _value, _value, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator*=(T value) {
    _check(ulbi_mul_slimb(_ctx(), _value, _value, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }
  template<FitLimb T>
  friend BigInt operator*(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_mul_limb(_ctx(), ret._value, lhs._value, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator*(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_mul_limb(_ctx(), ret._value, rhs._value, static_cast<ulbn_limb_t>(lhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator*(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_mul_slimb(_ctx(), ret._value, lhs._value, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator*(T lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_mul_slimb(_ctx(), ret._value, rhs._value, static_cast<ulbn_slimb_t>(lhs)));
    return ret;
  }


  BigInt& operator/=(const BigInt& other) {
    _check(ulbi_div(_ctx(), _value, _value, other._value));
    return *this;
  }
  template<FitLimb T>
  BigInt& operator/=(T value) {
    _check(ulbi_div_limb(_ctx(), _value, _value, static_cast<ulbn_limb_t>(value)));
    return *this;
  }
  template<FitSlimb T>
  BigInt& operator/=(T value) {
    _check(ulbi_div_slimb(_ctx(), _value, _value, static_cast<ulbn_slimb_t>(value)));
    return *this;
  }
  friend BigInt operator/(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_div(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }
  template<FitLimb T>
  friend BigInt operator/(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_div_limb(_ctx(), ret._value, lhs._value, static_cast<ulbn_limb_t>(rhs)));
    return ret;
  }
  template<FitSlimb T>
  friend BigInt operator/(const BigInt& lhs, T rhs) {
    BigInt ret;
    _check(ulbi_div_slimb(_ctx(), ret._value, lhs._value, static_cast<ulbn_slimb_t>(rhs)));
    return ret;
  }

  BigInt& operator%=(const BigInt& other) {
    _check(ulbi_mod(_ctx(), _value, _value, other._value));
    return *this;
  }
  friend BigInt operator%(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_mod(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }

  std::pair<BigInt, BigInt> divmod(const BigInt& other) const {
    BigInt q, r;
    _check(ulbi_divmod(_ctx(), q._value, r._value, _value, other._value));
    return {q, r};
  }

  friend std::strong_ordering operator<=>(const BigInt& lhs, const BigInt& rhs) {
    return ulbi_comp(lhs._value, rhs._value) <=> 0;
  }

  template<FitLimb T>
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) {
    return ulbi_comp_limb(lhs._value, static_cast<ulbn_limb_t>(rhs)) <=> 0;
  }
  template<FitSlimb T>
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) {
    return ulbi_comp_slimb(lhs._value, static_cast<ulbn_slimb_t>(rhs)) <=> 0;
  }
  template<FitUlong T>
    requires(!FitLimb<T>)
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) {
    return ulbi_comp_ulong(lhs._value, static_cast<ulbn_ulong_t>(rhs)) <=> 0;
  }
  template<FitSlong T>
    requires(!FitSlimb<T>)
  friend std::strong_ordering operator<=>(const BigInt& lhs, T rhs) {
    return ulbi_comp_slong(lhs._value, static_cast<ulbn_slong_t>(rhs)) <=> 0;
  }

  template<FitLimb T>
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) {
    return (-ulbi_comp_limb(rhs._value, static_cast<ulbn_limb_t>(lhs))) <=> 0;
  }
  template<FitSlimb T>
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) {
    return (-ulbi_comp_slimb(rhs._value, static_cast<ulbn_slimb_t>(lhs))) <=> 0;
  }
  template<FitUlong T>
    requires(!FitLimb<T>)
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) {
    return (-ulbi_comp_ulong(rhs._value, static_cast<ulbn_ulong_t>(lhs))) <=> 0;
  }
  template<FitSlong T>
    requires(!FitSlimb<T>)
  friend std::strong_ordering operator<=>(T lhs, const BigInt& rhs) {
    return (-ulbi_comp_slong(rhs._value, static_cast<ulbn_slong_t>(lhs))) <=> 0;
  }

  friend bool operator==(const BigInt& lhs, const BigInt& rhs) {
    return ulbi_eq(lhs._value, rhs._value) != 0;
  }
  template<FitLimb T>
  friend bool operator==(const BigInt& lhs, T rhs) {
    return ulbi_eq_limb(lhs._value, static_cast<ulbn_limb_t>(rhs)) != 0;
  }
  template<FitSlimb T>
  friend bool operator==(const BigInt& lhs, T rhs) {
    return ulbi_eq_slimb(lhs._value, static_cast<ulbn_slimb_t>(rhs)) != 0;
  }
  template<FitUlong T>
    requires(!FitLimb<T>)
  friend bool operator==(const BigInt& lhs, T rhs) {
    return ulbi_eq_ulong(lhs._value, static_cast<ulbn_ulong_t>(rhs)) != 0;
  }
  template<FitSlong T>
    requires(!FitSlimb<T>)
  friend bool operator==(const BigInt& lhs, T rhs) {
    return ulbi_eq_slong(lhs._value, static_cast<ulbn_slong_t>(rhs)) != 0;
  }

  template<FitLimb T>
  friend bool operator==(T lhs, const BigInt& rhs) {
    return ulbi_eq_limb(rhs._value, static_cast<ulbn_limb_t>(lhs)) != 0;
  }
  template<FitSlimb T>
  friend bool operator==(T lhs, const BigInt& rhs) {
    return ulbi_eq_slimb(rhs._value, static_cast<ulbn_slimb_t>(lhs)) != 0;
  }
  template<FitUlong T>
    requires(!FitLimb<T>)
  friend bool operator==(T lhs, const BigInt& rhs) {
    return ulbi_eq_ulong(rhs._value, static_cast<ulbn_ulong_t>(lhs)) != 0;
  }
  template<FitSlong T>
    requires(!FitSlimb<T>)
  friend bool operator==(T lhs, const BigInt& rhs) {
    return ulbi_eq_slong(rhs._value, static_cast<ulbn_slong_t>(lhs)) != 0;
  }


  explicit operator bool() const {
    return !ulbi_is_zero(_value);
  }
  bool operator!() const {
    return ulbi_is_zero(_value) != 0;
  }


  BigInt& operator&=(const BigInt& other) {
    _check(ulbi_and(_ctx(), _value, _value, other._value));
    return *this;
  }
  BigInt& operator|=(const BigInt& other) {
    _check(ulbi_or(_ctx(), _value, _value, other._value));
    return *this;
  }
  BigInt& operator^=(const BigInt& other) {
    _check(ulbi_xor(_ctx(), _value, _value, other._value));
    return *this;
  }
  friend BigInt operator&(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_and(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }
  friend BigInt operator|(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_or(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }
  friend BigInt operator^(const BigInt& lhs, const BigInt& rhs) {
    BigInt ret;
    _check(ulbi_xor(_ctx(), ret._value, lhs._value, rhs._value));
    return ret;
  }

  BigInt operator~() const {
    BigInt ret;
    _check(ulbi_com(_ctx(), ret._value, _value));
    return ret;
  }

  template<FitUsize T>
  BigInt& operator<<=(T shift) {
    _check(ulbi_sal_usize(_ctx(), _value, _value, static_cast<ulbn_usize_t>(shift)));
    return *this;
  }
  template<FitSsize T>
  BigInt& operator<<=(T shift) {
    _check(ulbi_sal_ssize(_ctx(), _value, _value, static_cast<ulbn_ssize_t>(shift)));
    return *this;
  }
  BigInt& operator<<=(const BigInt& shift) {
    _check(ulbi_sal(_ctx(), _value, _value, shift._value));
    return *this;
  }
  template<FitUsize T>
  friend BigInt operator<<(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sal_usize(_ctx(), ret._value, lhs._value, static_cast<ulbn_usize_t>(shift)));
    return ret;
  }
  template<FitSsize T>
  friend BigInt operator<<(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sal_ssize(_ctx(), ret._value, lhs._value, static_cast<ulbn_ssize_t>(shift)));
    return ret;
  }
  friend BigInt operator<<(const BigInt& lhs, const BigInt& shift) {
    BigInt ret;
    _check(ulbi_sal(_ctx(), ret._value, lhs._value, shift._value));
    return ret;
  }

  template<FitUsize T>
  BigInt& operator>>=(T shift) {
    _check(ulbi_sar_usize(_ctx(), _value, _value, static_cast<ulbn_usize_t>(shift)));
    return *this;
  }
  template<FitSsize T>
  BigInt& operator>>=(T shift) {
    _check(ulbi_sar_ssize(_ctx(), _value, _value, static_cast<ulbn_ssize_t>(shift)));
    return *this;
  }
  BigInt& operator>>=(const BigInt& shift) {
    _check(ulbi_sar(_ctx(), _value, _value, shift._value));
    return *this;
  }
  template<FitUsize T>
  friend BigInt operator>>(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sar_usize(_ctx(), ret._value, lhs._value, static_cast<ulbn_usize_t>(shift)));
    return ret;
  }
  template<FitSsize T>
  friend BigInt operator>>(const BigInt& lhs, T shift) {
    BigInt ret;
    _check(ulbi_sar_ssize(_ctx(), ret._value, lhs._value, static_cast<ulbn_ssize_t>(shift)));
    return ret;
  }
  friend BigInt operator>>(const BigInt& lhs, const BigInt& shift) {
    BigInt ret;
    _check(ulbi_sar(_ctx(), ret._value, lhs._value, shift._value));
    return ret;
  }

  BigInt pow(ulbn_usize_t e) const {
    BigInt ret;
    _check(ulbi_pow(_ctx(), ret._value, _value, e));
    return ret;
  }

  BigInt& shrink() {
    _check(ulbi_shrink(_ctx(), _value));
    return *this;
  }
  BigInt& reserve(ulbn_usize_t n) {
    _check(ulbi_reserve(_ctx(), _value, n) == nullptr ? ULBN_ERR_NOMEM : 0);
    return *this;
  }

  BigInt& swap(BigInt& other) {
    ulbi_swap(_value, other._value);
    return *this;
  }

  bool is_zero() const {
    return ulbi_is_zero(_value);
  }
  bool is_odd() const {
    return ulbi_is_odd(_value);
  }
  bool is_even() const {
    return ulbi_is_even(_value);
  }
  int sign() const {
    return ulbi_sign(_value);
  }

  bool fitUlong() const {
    return ulbi_fit_ulong(_value);
  }
  bool fitSlong() const {
    return ulbi_fit_slong(_value);
  }
  bool fitLimb() const {
    return ulbi_fit_limb(_value);
  }
  bool fitSlimb() const {
    return ulbi_fit_slimb(_value);
  }
  bool fitUsize() const {
    return ulbi_fit_usize(_value);
  }
  bool fitSsize() const {
    return ulbi_fit_ssize(_value);
  }

  ulbn_ulong_t toUlong() const {
    return ulbi_to_ulong(_value);
  }
  ulbn_slong_t toSlong() const {
    return ulbi_to_slong(_value);
  }
  ulbn_limb_t toLimb() const {
    return ulbi_to_limb(_value);
  }
  ulbn_slimb_t toSlimb() const {
    return ulbi_to_slimb(_value);
  }
  ulbn_usize_t toUsize() const {
    return ulbi_to_usize(_value);
  }
  ulbn_ssize_t toSsize() const {
    return ulbi_to_ssize(_value);
  }

  explicit operator ulbn_ulong_t() const {
    return toUlong();
  }
  explicit operator ulbn_slong_t() const {
    return toSlong();
  }

  std::string toString(int base = 10) const {
    std::string ret;
    ulbn_usize_t len;
    char* ret_ptr;

    ret_ptr = ulbi_tostr_alloc(
      _ctx(), &len,
      [](void* opaque, void* ptr, size_t on, size_t nn) -> void* {
        (void)on;
        (void)ptr;
        std::string* o = reinterpret_cast<std::string*>(opaque);
        o->resize(nn);
        return o->data();
      },
      &ret, _value, base
    );
    if(ul_unlikely(ret_ptr == nullptr))
      throw Exception((base < 2 || base > 36) ? ULBN_ERR_EXCEED_RANGE : ULBN_ERR_NOMEM);
    ret.resize(len);
    return ret;
  }

  friend std::ostream& operator<<(std::ostream& ost, const BigInt& value) {
    return ost << value.toString();
  }
  void print(FILE* fp = stdout, int base = 10) {
    _check(ulbi_print(_ctx(), _value, fp, base));
  }

  ulbi_t* get() noexcept {
    return _value;
  }
  const ulbi_t* get() const noexcept {
    return _value;
  }

  bool testBit(ulbn_usize_t n) const noexcept {
    return ulbi_testbit_usize(_value, n) != 0;
  }
  BigInt& setBit(ulbn_usize_t n) {
    _check(ulbi_setbit_usize(_ctx(), _value, n));
    return *this;
  }
  BigInt& resetBit(ulbn_usize_t n) {
    _check(ulbi_resetbit_usize(_ctx(), _value, n));
    return *this;
  }
  BigInt& comBit(ulbn_usize_t n) {
    _check(ulbi_combit_usize(_ctx(), _value, n));
    return *this;
  }

  bool testBit(const BigInt& n) const noexcept {
    return ulbi_testbit(_value, n._value) != 0;
  }
  BigInt& setBit(const BigInt& n) {
    _check(ulbi_setbit(_ctx(), _value, n._value));
    return *this;
  }
  BigInt& resetBit(const BigInt& n) {
    _check(ulbi_resetbit(_ctx(), _value, n._value));
    return *this;
  }
  BigInt& comBit(const BigInt& n) {
    _check(ulbi_combit(_ctx(), _value, n._value));
    return *this;
  }


  BigInt asUint(ulbn_usize_t n) const {
    BigInt ret;
    _check(ulbi_as_uint_usize(_ctx(), ret._value, _value, n));
    return ret;
  }
  BigInt asInt(ulbn_usize_t n) const {
    BigInt ret;
    _check(ulbi_as_int_usize(_ctx(), ret._value, _value, n));
    return ret;
  }

  BigInt asUint(const BigInt& n) const {
    BigInt ret;
    _check(ulbi_as_uint(_ctx(), ret._value, _value, n._value));
    return ret;
  }
  BigInt asInt(const BigInt& n) const {
    BigInt ret;
    _check(ulbi_as_int(_ctx(), ret._value, _value, n._value));
    return ret;
  }


  bool is2Pow() const {
    return ulbi_is_2pow(_value);
  }
  BigInt ctz() const {
    BigInt ret;
    _check(ulbi_ctz(_ctx(), ret._value, _value));
    return ret;
  }
  BigInt cto() const {
    BigInt ret;
    _check(ulbi_cto(_ctx(), ret._value, _value));
    return ret;
  }
  BigInt absPopcount() const {
    BigInt ret;
    _check(ulbi_abs_popcount(_ctx(), ret._value, _value));
    return ret;
  }
  BigInt absBitWidth() const {
    BigInt ret;
    _check(ulbi_abs_bit_width(_ctx(), ret._value, _value));
    return ret;
  }

#if ULBN_CONF_HAS_DOUBLE
  template<FitDouble T>
  explicit BigInt(T value) {
    _check(ulbi_init_double(_ctx(), _value, static_cast<double>(value)));
  }
  template<FitDouble T>
  BigInt& operator=(T value) {
    _check(ulbi_set_double(_ctx(), _value, static_cast<double>(value)));
    return *this;
  }
  double toDouble() const {
    return ulbi_to_double(_value);
  }
  explicit operator double() const {
    return toDouble();
  }
#endif /* ULBN_CONF_HAS_DOUBLE */


private:
  static ulbn_alloc_t* _ctx() {
    static ulbn_alloc_t* ctx = ulbn_default_alloc();
    return ctx;
  }
  static int _check(int err) {
    if(err < 0 || err == ULBN_ERR_DIV_BY_ZERO)
      throw Exception(err);
    return err;
  }

  ulbi_t _value[1];
};

BigInt operator""_bi(const char* str) {
  return BigInt(str);
}
BigInt operator""_bi(const char* str, size_t len) {
  (void)len;
  return BigInt(str);
}
// BigInt operator""_bi(unsigned long long val) {
//   return BigInt(val);
// }

}  // namespace bn
}  // namespace ul
