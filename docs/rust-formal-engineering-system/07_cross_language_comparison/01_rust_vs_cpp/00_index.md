# Rust vs C++ 比较

## 📊 目录

- [Rust vs C++ 比较](#rust-vs-c-比较)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心对比维度](#核心对比维度)
    - [内存安全](#内存安全)
    - [性能](#性能)
    - [并发安全](#并发安全)
    - [类型系统](#类型系统)
    - [生态系统](#生态系统)
  - [适用场景对比](#适用场景对比)
    - [Rust 优势场景](#rust-优势场景)
    - [C++ 优势场景](#c-优势场景)
  - [迁移指南](#迁移指南)
    - [从 C++ 到 Rust](#从-c-到-rust)
    - [互操作性](#互操作性)
  - [实践与样例](#实践与样例)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 对比 Rust 与 C++ 在系统编程、性能、安全性等方面的差异。
- 提供从 C++ 迁移到 Rust 的指导与最佳实践。

## 核心对比维度

### 内存安全

- **Rust**：编译时内存安全，所有权系统防止悬垂指针、缓冲区溢出
- **C++**：手动内存管理，容易出现内存泄漏、悬垂指针等问题

### 性能

- **Rust**：零成本抽象，与 C++ 相当的性能
- **C++**：成熟的优化器，丰富的性能调优工具

### 并发安全

- **Rust**：编译时并发安全，`Send`/`Sync` 标记
- **C++**：运行时并发安全，需要手动管理锁和同步

### 类型系统

- **Rust**：强类型系统，模式匹配，代数数据类型
- **C++**：模板系统，多重继承，虚函数

### 生态系统

- **Rust**：现代包管理器 Cargo，丰富的 crates.io 生态
- **C++**：传统构建系统，分散的库生态

## 适用场景对比

### Rust 优势场景

- 系统编程：操作系统、嵌入式系统
- 网络服务：高并发服务器、微服务
- 安全关键应用：加密库、安全工具
- 新项目：从零开始的项目

### C++ 优势场景

- 遗留系统：现有 C++ 代码库
- 游戏开发：成熟的游戏引擎生态
- 高性能计算：GPU 计算、科学计算
- 跨平台库：需要与 C 库互操作

## 迁移指南

### 从 C++ 到 Rust

1. 理解所有权概念
2. 学习 Rust 的类型系统
3. 掌握错误处理模式
4. 熟悉 Cargo 包管理
5. 逐步迁移模块

### 互操作性

- 使用 `extern "C"` 进行 FFI
- 通过 `bindgen` 生成绑定
- 使用 `cc` crate 编译 C/C++ 代码

## 实践与样例

- 对比实现：参见 [crates/c63_rust_vs_cpp](../../../crates/c63_rust_vs_cpp/)
- 系统编程：[crates/c05_threads](../../../crates/c05_threads/)
- 网络编程：[crates/c10_networks](../../../crates/c10_networks/)

## 相关索引

- 理论基础（内存安全）：[`../../01_theoretical_foundations/02_memory_safety/00_index.md`](../../01_theoretical_foundations/02_memory_safety/00_index.md)
- 编程范式（并发）：[`../../02_programming_paradigms/05_concurrent/00_index.md`](../../02_programming_paradigms/05_concurrent/00_index.md)
- 应用领域（系统编程）：[`../../04_application_domains/00_index.md`](../../04_application_domains/00_index.md)

## 导航

- 返回跨语言比较：[`../00_index.md`](../00_index.md)
- Rust vs Go：[`../02_rust_vs_go/00_index.md`](../02_rust_vs_go/00_index.md)
- Rust vs Python：[`../03_rust_vs_python/00_index.md`](../03_rust_vs_python/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
