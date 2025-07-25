# 12 术语表 Glossary

## 概述

本章汇总Rust所有权、借用、生命周期等相关核心术语，提供简明定义，便于查阅和理解。

## 术语列表

- **所有权（Ownership）**：每个值有唯一所有者，离开作用域自动释放。
- **借用（Borrowing）**：通过引用访问值而不取得所有权。
- **可变借用（Mutable Borrow）**：对值的唯一可变引用，允许修改。
- **不可变借用（Immutable Borrow）**：对值的只读引用，可有多个。
- **生命周期（Lifetime）**：引用或值在内存中的有效时间区间。
- **作用域（Scope）**：变量或引用的可见范围。
- **Copy类型**：可按位复制的类型，赋值后原值依然有效。
- **Move语义**：所有权转移，原变量失效。
- **Drop特性**：作用域结束时自动释放资源的机制。
- **RAII**：资源获取即初始化，自动管理资源生命周期。
- **RefCell**：单线程内部可变性容器，运行时借用检查。
- **Mutex**：多线程可变性容器，保证并发安全。
- **Arc**：原子引用计数智能指针，实现多线程共享所有权。
- **Weak**：非拥有型弱引用，打破循环依赖防止内存泄漏。
- **悬垂引用（Dangling Reference）**：指向已释放内存的引用，Rust编译器禁止。
- **仿射类型（Affine Type）**：每个值最多用一次，Rust所有权的理论基础。
- **分离逻辑（Separation Logic）**：用于证明并发内存安全的数学工具。

## 交叉引用

- [所有权与变量系统](./01_variable_and_ownership.md)
- [生命周期与作用域分析](./02_lifetime_and_scope.md)
- [内存管理与平衡机制](./05_memory_management_and_balance.md)

## 总结

术语表有助于快速查阅和理解Rust内存安全相关概念，是理论学习和工程实践的重要参考。
