#  ulbn: 高精度数字库

[English](./README.md) [简体中文](./README_zh_CN.md)

## 特色

- C89/C++98兼容（也有可选的C++20头文件）
- 只依赖于很少的硬件假设
- 规避了绝大部分的UB行为
- 严格的边界检查
- 可使用自定义的内存分配器
- 大部分函数进行了一定优化
- 无外置依赖

## 依赖

项目文件均无外部依赖

### ulbn.h和ulbn.c

最低C89/C++98，利用宏对部分代码进行优化建议

硬件假设：

- 要求`CHAR_BIT`是偶数

### ulbn.hpp

要求C++20的以下特性：

- 约束与概念
- 三路比较
- std::endian
- std::span
- std::format（可选）

根据[cppreference](https://zh.cppreference.com)，最低编译器要求为：
- GCC 10（2020年5月7日）
- Clang 10（2020年3月24日）
- MSVC 19.26（2020年5月19日）

### test

要求以下对于现代平台的假设：

- 以补码形式存储有符号整数
- float的有效位数为23（IEEE754标准）
- double的有效位数为52（IEEE754标准）
- char为8比特
- int64_t存在
- 平台要么大端，要么小端
- \<bit\>
- std::format（可选）

## 路线图

- [ ] 高精度整数
  - [x] 算术
    - [ ] 更快的乘法
      - [x] Karatsuba算法（Toom-2）
      - [x] Toom-3算法
      - [x] Toom-4算法
      - [ ] FFT
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