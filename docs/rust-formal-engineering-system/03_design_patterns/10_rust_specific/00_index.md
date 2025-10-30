> ⚠️ **待完善** - 此文件为占位符，内容待完善
> **最后更新**: 2025-10-31
> **预期完成**: 待定

---

﻿# Rust 特定模式（Rust-Specific Patterns）索引

## 📊 目录

- [Rust 特定模式（Rust-Specific Patterns）索引](#rust-特定模式rust-specific-patterns索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心模式](#核心模式)
  - [Rust 化要点](#rust-化要点)
  - [术语（Terminology）](#术语terminology)
  - [实践与样例（Practice）](#实践与样例practice)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 介绍 Rust 语言特有的设计模式与惯用法。
- 提供 Rust 生态系统中的最佳实践与常见模式。

## 核心模式

- 所有权模式（Ownership Patterns）：所有权转移与借用
- 生命周期模式（Lifetime Patterns）：生命周期管理
- 错误处理模式（Error Handling Patterns）：`Result` 与 `Option` 使用
- 异步模式（Async Patterns）：`async/await` 与 Future
- 宏模式（Macro Patterns）：声明宏与过程宏
- 特征模式（Trait Patterns）：trait 对象与泛型约束
- 枚举模式（Enum Patterns）：代数数据类型
- 模式匹配模式（Pattern Matching）：`match` 表达式
- 迭代器模式（Iterator Patterns）：函数式编程
- 并发模式（Concurrency Patterns）：`Send`/`Sync` 标记

## Rust 化要点

- 所有权系统：零成本内存安全
- 类型系统：编译时保证
- 零成本抽象：运行时无开销
- 函数式编程：不可变优先

## 术语（Terminology）

- Rust 特定模式（Rust-Specific Patterns）
- 所有权（Ownership）、生命周期（Lifetime）
- 错误处理（Error Handling）、异步（Async）
- 宏（Macro）、特征（Trait）
- 枚举（Enum）、模式匹配（Pattern Matching）

## 实践与样例（Practice）

- Rust 模式实现：参见 [crates/c01_ownership_borrow_scope](../../../crates/c01_ownership_borrow_scope/)
- 泛型与 trait：[crates/c04_generic](../../../crates/c04_generic/)
- 控制与函数：[crates/c03_control_fn](../../../crates/c03_control_fn/)

### 文件级清单（精选）

- `crates/c01_ownership_borrow_scope/src/`：
  - `ownership_patterns.rs`：所有权模式
  - `lifetime_patterns.rs`：生命周期模式
  - `borrowing_patterns.rs`：借用模式
- `crates/c04_generic/src/`：
  - `trait_patterns.rs`：特征模式
  - `enum_patterns.rs`：枚举模式
  - `pattern_matching.rs`：模式匹配
- `crates/c03_control_fn/src/`：
  - `error_handling.rs`：错误处理模式
  - `iterator_patterns.rs`：迭代器模式
  - `macro_patterns.rs`：宏模式

## 相关索引

- 理论基础（所有权与借用）：[`../../01_theoretical_foundations/03_ownership_borrowing/00_index.md`](../../01_theoretical_foundations/03_ownership_borrowing/00_index.md)
- 理论基础（生命周期管理）：[`../../01_theoretical_foundations/06_lifetime_management/00_index.md`](../../01_theoretical_foundations/06_lifetime_management/00_index.md)
- 编程范式（函数式）：[`../../02_programming_paradigms/03_functional/00_index.md`](../../02_programming_paradigms/03_functional/00_index.md)

## 导航

- 返回设计模式：[`../00_index.md`](../00_index.md)
- 性能模式：[`../09_performance/00_index.md`](../09_performance/00_index.md)
- 理论基础：[`../../01_theoretical_foundations/00_index.md`](../../01_theoretical_foundations/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
