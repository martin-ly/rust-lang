# 所有权与借用（Ownership & Borrowing）索引

## 目的

- 深入理解 Rust 所有权系统的设计原理与实现细节。
- 掌握借用检查器的工作原理与最佳实践。

## 核心概念

- 所有权规则：每个值有且仅有一个所有者，所有者离开作用域时值被释放
- 借用机制：通过引用（`&`/`&mut`）临时借用值，不转移所有权
- 借用检查：编译时检查借用规则，防止数据竞争和悬垂指针
- 生命周期：确保引用的有效性，防止悬垂引用

## 与 Rust 的关联

- 内存安全：通过所有权系统实现零成本的内存安全
- 并发安全：借用规则天然防止数据竞争
- 性能优化：移动语义避免不必要的深拷贝

## 术语（Terminology）

- 所有权（Ownership）、借用（Borrowing）、引用（Reference）
- 移动（Move）、复制（Copy）、克隆（Clone）
- 生命周期（Lifetime）、作用域（Scope）
- 借用检查器（Borrow Checker）

## 形式化与证明（Formalization）

- 所有权不变式：`∀v. |owners(v)| = 1`
- 借用规则：`¬(∃r1, r2. mutable(r1) ∧ mutable(r2) ∧ alias(r1, r2))`
- 生命周期约束：`lifetime(r) ⊆ lifetime(*r)`

## 实践与样例（Practice）

- 所有权基础：参见 [crates/c01_ownership_borrow_scope](../../../crates/c01_ownership_borrow_scope/)
- 并发编程：[crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)

## 相关索引

- 内存安全：[`../02_memory_safety/00_index.md`](../02_memory_safety/00_index.md)
- 生命周期管理：[`../06_lifetime_management/00_index.md`](../06_lifetime_management/00_index.md)
- 并发模型：[`../04_concurrency_models/00_index.md`](../04_concurrency_models/00_index.md)

## 导航

- 返回理论基础：[`../00_index.md`](../00_index.md)
- 编程范式：[`../../02_programming_paradigms/00_index.md`](../../02_programming_paradigms/00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
