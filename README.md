# ulbn: High-precision Number Library

[English](./README.md) [简体中文](./README_zh_CN.md)

## Features

- C89/C++98 compatible (optional C++20 headers available)
- Minimal hardware assumptions
- Avoids most UB (Undefined Behavior)
- Strict boundary checks
- Custom memory allocator support
- Most functions are optimized
- No external dependencies

## Dependencies

No external dependencies needed.

### ulbn.h/ulbn.c

Minimum C89/C++98, with macros to suggest optimizations for some code.

Hardware Assumptions:

- Requires `CHAR_BIT` to be even

### ulbn.hpp

Depends on the following C++20 features:

- Concepts and constranints
- Three-way comparison
- `<bit>` header file

### test.cpp

Depends on the following assumptions for modern platforms:

- Signed integers are stored in two's complement form
- `double` has 52 bits of precision (IEEE754)
- `char` is 8-bits, and `int64_t` exists

## Roadmap

- [ ] High-precision integers
  - [x] Arithmetic
    - [ ] Faster multiplicatin
      - [x] Karatsuba algorithm (Toom-2)
      - [x] Toom-3 algorithm
      - [x] Toom-4 algorithm
      - [ ] FFT
    - [ ] Faster base conversion
      - [ ] Faster input
      - [x] Faster output
  - [x] Comparison
  - [x] Bitwise Operation
  - [x] Root
  - [ ] Number theory functions
    - [x] GCD/LCM
    - [x] Extended GCD
    - [ ] Prime number determination
    - [ ] Prime number search
    - [ ] Factorization
- [ ] High-precision fractions
- [ ] High-precision floating point number
- [ ] High-precision decimal floating point number