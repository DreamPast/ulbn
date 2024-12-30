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

## Requirements

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

## How to use

### ulbn.h

Add "ulbn.h" and "ulbn.c" to your project.

```c
#include "ulbn.h"
#include <stdio.h>

int main(void) {
  const ulbn_alloc_t* alloc = ulbn_default_alloc(); /* get default allocator */
  ulbi_t ro, ao, bo;
  int err;

  /* first, we must initialize them */
  ulbi_init(&ro);
  ulbi_init(&ao);
  ulbi_init(&bo);


  ulbi_set_slimb(&ao, 99);              /* set ao = 99, `ulbi_set_slimb` doesn't make errors */
  ulbi_set_slimb(&bo, 99);              /* set bo = 99, `ulbi_set_slimb` doesn't make errors */
  err = ulbi_add(alloc, &ro, &ao, &bo); /* ro = ao + bo */
  if(err) {
    fprintf(stderr, "error: %d\n", err);
    return 1;
  }
  ulbi_print(alloc, stdout, &ro, 10); /* print ro */
  putchar('\n');


  err = ulbi_add_slimb(alloc, &ro, &ao, 99); /* some functions have a simpler version */
  if(err) {
    fprintf(stderr, "error: %d\n", err);
    return 1;
  }
  ulbi_print(alloc, stdout, &ro, 10); /* print ro */
  putchar('\n');


  err = ulbi_pow(alloc, &ro, &ao, &bo); /* we can try larger number */
  if(err) {
    fprintf(stderr, "error: %d\n", err);
    return 1;
  }
  ulbi_print(alloc, stdout, &ro, 10); /* print ro */
  putchar('\n');


  /* finally, don't forget to deinitialize them */
  ulbi_deinit(alloc, &ro);
  ulbi_deinit(alloc, &ao);
  ulbi_deinit(alloc, &bo);

  return 0;
}

#include "ulbn.c" /* we can include source code directly */

```

### ulbn.hpp

Add "ulbn.hpp", "ulbn.h" and "ulbn.c" to your project, and make sure your compiler support C++20.

```cpp
#include "ulbn.hpp"
#include <iostream>

int main() {
  // In C++, we don't need to explicitly manage memory and check errors.
  // With the help of operator overloading, we can use high precision more conveniently.
  using ul::bn::BigInt;
  BigInt ro, ao, bo;

  ao = 99;
  bo = 99;
  ro = ao + bo;
  std::cout << ro << '\n';

  ro = ao + 99;
  std::cout << ro << '\n';

  ro = ao.pow(bo);
  std::cout << ro << '\n';

  return 0;
}

#include "ulbn.c" // we can include source code directly

```

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