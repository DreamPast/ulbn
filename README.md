# ulbn: High-precision Number Library

[English](./README.md) [简体中文](./README_zh_CN.md)

## Features

- C89/C++98 compatible (optional C++20 headers available)
- Minimal hardware assumptions
- Avoids most UB (Undefined Behavior)
- Strict boundary checks
- Custom memory allocator support
- Almost all functions reach time complexity of O(n*log(n))
- No external dependencies

## Dependencies

No external dependencies needed.

### ulbn.h/ulbn.c

Minimum C89/C++98, with macros to suggest optimizations for some code.

Hardware Assumptions:

- Requires `CHAR_BIT` to be even

### ulbn.hpp

Requires the following C++20 features:

- Concepts and constranints
- Three-way comparison
- std::endian
- std::span
- std::format (optional)

According to [cppreference](https://en.cppreference.com/), the minimum compiler requirements is:
- GCC 10 (May, 7, 2020)
- Clang 10 (March, 24, 2020)
- MSVC 19.26 (May, 19, 2020)

### test

Requires the following assumptions for modern platforms:

- Signed integers are stored in two's complement form
- `float` has 23 bits of precision (IEEE754)
- `double` has 52 bits of precision (IEEE754)
- `char` is 8-bits
- `int64_t` exists
- The platform is little-endian or big-endian
- \<bit\>
- std::format (optional)

## Roadmap

- [ ] High-precision integers
  - [x] Arithmetic
    - [x] Faster multiplicatin
      - [x] Karatsuba algorithm (Toom-2)
      - [x] Toom-3 algorithm
      - [x] Toom-4 algorithm
      - [x] FFT
    - [x] Faster base conversion
      - [x] Faster input
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