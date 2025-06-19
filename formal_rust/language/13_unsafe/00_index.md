# Unsafe Rust主题索引

## 目录结构

### 1. 理论基础
1. [形式化Unsafe系统](01_formal_unsafe_system.md)
2. [Unsafe理论](02_unsafe_theory.md)
3. [Unsafe实现](03_unsafe_implementation.md)
4. [Unsafe应用](04_unsafe_applications.md)

### 2. 参考资料
5. [代码示例](05_examples.md)
6. [定理证明](06_theorems.md)
7. [参考文献](07_references.md)

## 主题概述

Unsafe Rust允许绕过编译器的安全检查，用于系统编程、FFI接口和性能优化。本主题涵盖：

- **Unsafe基础**：unsafe关键字、unsafe块、unsafe函数
- **原始指针**：裸指针、指针算术、内存访问
- **FFI接口**：外部函数接口、C语言互操作、ABI约定
- **内存安全**：内存布局、对齐要求、未定义行为

## 核心概念

### Unsafe基础
- unsafe关键字使用
- unsafe块和函数
- unsafe trait实现
- 安全抽象设计

### 原始指针
- 裸指针类型
- 指针算术操作
- 内存访问模式
- 指针生命周期

### FFI接口
- 外部函数声明
- C语言互操作
- ABI约定和调用
- 类型转换和映射

### 内存安全
- 内存布局控制
- 对齐要求保证
- 未定义行为避免
- 内存安全证明

## 交叉引用

- 与[所有权系统](../01_ownership_borrowing/00_index.md)的绕过检查
- 与[类型系统](../02_type_system/00_index.md)的原始类型
- 与[并发系统](../05_concurrency/00_index.md)的原子操作
- 与[编译系统](../20_compiler_internals/00_index.md)的代码生成

## 数学符号说明

本文档使用以下数学符号：
- $U$：Unsafe代码
- $P$：原始指针
- $M$：内存
- $F$：外部函数
- $\bot$：未定义行为
- $\vdash$：安全推导
- $\rightarrow$：指针解引用
- $\circ$：内存操作 