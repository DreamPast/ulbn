# ulbn: High-precision Number Library

[English](./README.md) [简体中文](./README_zh_CN.md)

## Dependencies

No external dependencies needed.

### ulbn.h/ulbn.c

Minimum C89/C++98, with macros to suggest optimizations for some code.

`CHAR_BIT` need to be even.

### ulbn.hpp

Depends on the following C++20 features:

- Concepts and constranints
- Three-way comparison

### test.cpp

Depends on the following assumptions for modern platforms:

- Signed integers are stored in two's complement form
- `double` has 52 bits of precision (IEEE754)
- `char` is 8-bits, and `int64_t` exists

Depends on the following C++20 features:

- `<bit>` header file

## Roadmap

- [ ] High-precision integers
  - [x] Arithmetic
    - [ ] Faster multiplicatin
      - [x] Karatsuba algorithm (Toom-2)
      - [x] Toom-3 algorithm
      - [x] Toom-4 algorithm
      - [ ] FFT
    - [ ] Faster base conversion
  - [x] Comparison
  - [x] Bitwise Operation
  - [x] Root
  - [ ] Number theory functions
    - [x] GCD/LCM
    - [ ] Extended GCD
    - [ ] Prime number determination
    - [ ] Prime number search
    - [ ] Factorization
- [ ] High-precision fractions
- [ ] High-precision floating point number
- [ ] High-precision decimal floating point number