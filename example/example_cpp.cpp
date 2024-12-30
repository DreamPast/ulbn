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
