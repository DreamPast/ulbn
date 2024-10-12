# ulbn: High-precision Number Library

[English](./README.md) [简体中文](./README_zh_CN.md)

## Dependencies

No external dependencies needed.

### ulbn.h/ulbn.c

Minimum C89/C++98, with macros to suggest optimizations for some code.

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

- `<bit` header file

## Roadmap

- [ ] High-precision integers
  - [x] Arithmetic
    - [ ] Faster multiplicatin
    - [ ] Faster base conversion
  - [x] Comparison
  - [x] Bitwise Operation
  - [ ] Square root
  - [ ] Number theory functions
- [ ] High-precision fractions
- [ ] High-precision floating point number
- [ ] High-precision decimal floating point number