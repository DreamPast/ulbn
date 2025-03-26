#  ulbn: 高精度数字库

[English](./README.md) [简体中文](./README_zh_CN.md)

## 特色

- C89/C++98兼容（也有可选的C++20头文件）
- 只依赖于很少的硬件假设
- 规避了绝大部分的UB行为
- 严格的边界检查
- 可使用自定义的内存分配器
- 几乎所有函数的时间复杂度达到了O(n*log(n))
- 无外置依赖

## 要求

项目文件均无外部依赖

### ulbn.h和ulbn.c

最低C89/C++98，利用宏对部分代码进行优化建议

硬件假设：

- 要求`sizeof(ulbn_limb_t)`或者`CHAR_BIT`是偶数
- 要求整数除法向0舍入（自C99/C++98开始保证此要求，但在更早的版本中这是实现定义的）

### ulbn.hpp

要求C++20的以下特性：

- 约束与概念
- 三路比较
- std::endian
- std::span
- std::format（可选）

根据[cppreference](https://zh.cppreference.com)，最低的常见编译器要求为：
- GCC 10（2020年5月7日）
- Clang 10（2020年3月24日）
- MSVC 19.26（2020年5月19日）

### test

要求以下对于现代平台的假设：

- 以补码形式存储有符号整数
- float的有效位数为23（IEEE754标准）
- double的有效位数为52（IEEE754标准）
- char为8比特，并且使用ASCII
- int64_t存在
- 平台要么大端，要么小端
- \<bit\>
- std::format（可选）

## 如何使用

### ulbn.h

添加"ulbn.h"和"ulbn.c"到项目中。

```c
#include "ulbn.h"
#include <stdio.h>

int main(void) {
  const ulbn_alloc_t* alloc = ulbn_default_alloc(); /* 获得默认分配器 */
  ulbi_t ro, ao, bo;
  int err;

  /* 初始化库 */
  ulbn_startup(); 
  /* 首先，我们需要初始化它们 */
  ulbi_init(&ro);
  ulbi_init(&ao);
  ulbi_init(&bo);


  ulbi_set_slimb(&ao, 99);              /* 设置ao为99，`ulbi_set_slimb`不会产生错误 */
  ulbi_set_slimb(&bo, 99);              /* 设置bo为99，`ulbi_set_slimb`不会产生错误 */
  err = ulbi_add(alloc, &ro, &ao, &bo); /* ro = ao + bo */
  if(err) {
    fprintf(stderr, "error: %d\n", err);
    return 1;
  }
  ulbi_print(alloc, stdout, &ro, 10); /* 输出ro */
  putchar('\n');


  err = ulbi_add_slimb(alloc, &ro, &ao, 99); /* 一些函数有更简单的版本 */
  if(err) {
    fprintf(stderr, "error: %d\n", err);
    return 1;
  }
  ulbi_print(alloc, stdout, &ro, 10); /* 输出ro */
  putchar('\n');


  err = ulbi_pow(alloc, &ro, &ao, &bo); /* 我们可以试试大一点的数字 */
  if(err) {
    fprintf(stderr, "error: %d\n", err);
    return 1;
  }
  ulbi_print(alloc, stdout, &ro, 10); /* 输出ro */
  putchar('\n');


  /* 最终，我们需要解分配它们 */
  ulbi_deinit(alloc, &ro);
  ulbi_deinit(alloc, &ao);
  ulbi_deinit(alloc, &bo);

  return 0;
}

#include "ulbn.c" /* 我们可以直接引用源代码 */

```

### ulbn.hpp

添加"ulbn.hpp"、"ulbn.h"、"ulbn.c"到项目中，并且确保编译器支持C++20。

```cpp
#include "ulbn.hpp"
#include <iostream>

int main() {
  // 在C++中，我们不需要显式管理内存以及检查错误。
  // 在函数重载的帮助下，我们可以更自然地使用高精度。
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

#include "ulbn.c" // 我们可以直接引用源代码

```



## 路线图

- [ ] 高精度整数
  - [x] 算术
    - [x] 更快的乘法
      - [x] Karatsuba算法（Toom-2）
      - [x] Toom-3算法
      - [x] Toom-4算法
      - [x] FFT
    - [x] 更快的进制转换
      - [x] 更快的输入
      - [x] 更快的输出
  - [x] 比较
  - [x] 比特位操作
  - [x] 开根号
  - [ ] 数论函数
    - [x] GCD/LCM
    - [x] 扩展GCD
    - [ ] 素数判定
    - [ ] 素数搜索
    - [ ] 因数分解
- [ ] 高精度分数
- [ ] 高精度浮点数
- [ ] 高精度十进制浮点数