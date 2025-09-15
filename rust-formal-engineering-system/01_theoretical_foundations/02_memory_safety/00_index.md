# 内存安全（Memory Safety）索引

## 目的

- 梳理 Rust 内存安全的理论基础与实现机制。
- 对比传统语言的内存管理方式，突出 Rust 的零成本安全特性。

## 核心概念

- 所有权系统：单一所有权、移动语义、借用检查
- 生命周期：引用有效性、作用域管理、别名控制
- 内存布局：栈/堆分配、零成本抽象、内存对齐
- 安全保证：无悬垂指针、无缓冲区溢出、无数据竞争

## 与 Rust 的关联

- 编译时检查：通过类型系统在编译期保证内存安全
- 零成本抽象：运行时无额外开销，性能与 C/C++ 相当
- 所有权转移：通过移动语义避免深拷贝，提高性能

## 术语（Terminology）

- 所有权（Ownership）、借用（Borrowing）、生命周期（Lifetime）
- 移动（Move）、复制（Copy）、克隆（Clone）
- 悬垂指针（Dangling Pointer）、内存泄漏（Memory Leak）
- 数据竞争（Data Race）、别名（Aliasing）

## 形式化与证明（Formalization）

- 所有权不变式：每个值有且仅有一个所有者
- 借用规则：不可变借用与可变借用不能同时存在
- 生命周期约束：引用的生命周期不能超过被引用值的生命周期

## 实践与样例（Practice）

- 所有权与借用：参见 [crates/c01_ownership_borrow_scope](../../../crates/c01_ownership_borrow_scope/)
- 并发与线程安全：[crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)

## 相关索引

- 类型系统：[`../01_type_system/00_index.md`](../01_type_system/00_index.md)
- 所有权与借用：[`../03_ownership_borrowing/00_index.md`](../03_ownership_borrowing/00_index.md)
- 生命周期管理：[`../06_lifetime_management/00_index.md`](../06_lifetime_management/00_index.md)

## 导航

- 返回理论基础：[`../00_index.md`](../00_index.md)
- 编程范式：[`../../02_programming_paradigms/00_index.md`](../../02_programming_paradigms/00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
