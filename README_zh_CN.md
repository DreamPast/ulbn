#  ulbn: 高精度数字库

[English](./README.md) [简体中文](./README_zh_CN.md)

## 依赖

项目文件均无外部依赖

### ulbn.h和ulbn.c

最低C89/C++98，利用宏对部分代码进行优化建议

### ulbn.hpp

依赖C++20的以下特性：

- 约束与概念
- 三路比较

### test.cpp

依赖以下对于现代平台的假设：

- 以补码形式存储有符号整数
- double的有效位数为52（IEEE754标准）
- char为8比特，且存在int64_t

依赖C++20的以下特性：

- \<bit\>头文件

## 路线图

- [ ] 高精度整数
  - [x] 算术
    - [ ] 更快的乘法
    - [ ] 更快的进制转换
  - [x] 比较
  - [x] 比特位操作
  - [ ] 开根号
  - [ ] 数论函数
  
- [ ] 高精度分数
- [ ] 高精度浮点数
- [ ] 高精度十进制浮点数