# 所有权与借用（Ownership & Borrowing）索引

## 目的

- 深入理解 Rust 所有权系统的设计原理与实现细节。
- 掌握借用检查器的工作原理与最佳实践。
- 建立从理论到实践的完整知识体系。

## 核心概念

### 所有权系统

- **单一所有权**：每个值有且仅有一个所有者，所有者离开作用域时值被释放
- **移动语义**：所有权从一个变量转移到另一个，原变量变为未初始化状态
- **复制语义**：实现 `Copy` trait 的类型自动进行位拷贝
- **克隆语义**：显式调用 `clone()` 进行深拷贝

### 借用机制

- **不可变借用**：通过 `&T` 临时借用值，可以有多个，但不能与可变借用共存
- **可变借用**：通过 `&mut T` 临时借用值，只能有一个，且不能与其他借用共存
- **借用检查**：编译时静态分析，防止数据竞争和悬垂指针
- **生命周期**：确保引用的有效性，防止悬垂引用

### 智能指针

- **`Box<T>`**：堆分配的单一所有权指针
- **`Rc<T>`**：引用计数的共享所有权（单线程）
- **`Arc<T>`**：原子引用计数的共享所有权（多线程）
- **`RefCell<T>`**：运行时的借用检查（单线程）
- **`Mutex<T>`**：互斥锁保护的共享数据（多线程）

## 理论基础

### 形式化语义

所有权系统基于以下形式化规则：

1. **所有权不变式**：

   ```text
   ∀ value ∈ memory, |owners(value)| = 1
   ```

2. **借用规则**：

   ```text
   ∀ reference r, valid(r) ⟹ (immutable_borrows(r) ∩ mutable_borrows(r) = ∅)
   ```

3. **生命周期约束**：

   ```text
   ∀ reference r with lifetime 'a, lifetime(r) ⊆ lifetime(borrowed_value)
   ```

### 内存安全保证

- **无悬垂指针**：通过生命周期检查保证引用有效性
- **无内存泄漏**：通过所有权转移和 RAII 自动管理
- **无数据竞争**：通过借用规则和 `Send`/`Sync` 标记保证线程安全

## 与 Rust 的关联

### 编译时保证

- **零运行时开销**：所有权检查在编译时完成，运行时无额外成本
- **内存安全**：编译时保证无内存错误，无需垃圾回收
- **并发安全**：通过所有权和借用规则避免数据竞争

### 性能优化

- **移动语义**：避免不必要的深拷贝，提高性能
- **零成本抽象**：所有权系统不影响运行时性能
- **栈分配优先**：默认栈分配，按需堆分配

## 术语（Terminology）

### 核心术语

- **所有权（Ownership）**：值的唯一拥有关系
- **借用（Borrowing）**：临时获取值的引用
- **引用（Reference）**：指向值的指针，不拥有值
- **生命周期（Lifetime）**：引用的有效作用域
- **作用域（Scope）**：变量的可见范围

### 操作术语

- **移动（Move）**：所有权从一个变量转移到另一个
- **复制（Copy）**：创建值的位拷贝
- **克隆（Clone）**：创建值的深拷贝
- **借用（Borrow）**：获取值的引用

### 工具术语

- **借用检查器（Borrow Checker）**：编译时检查借用规则的组件
- **生命周期检查器（Lifetime Checker）**：检查引用有效性的组件
- **所有权分析器（Ownership Analyzer）**：分析所有权转移的工具

## 形式化与证明（Formalization）

- 所有权不变式：`∀v. |owners(v)| = 1`
- 借用规则：`¬(∃r1, r2. mutable(r1) ∧ mutable(r2) ∧ alias(r1, r2))`
- 生命周期约束：`lifetime(r) ⊆ lifetime(*r)`

## 实践与样例（Practice）

### 基础示例

- **所有权基础**：参见 [crates/c01_ownership_borrow_scope](../../../crates/c01_ownership_borrow_scope/)
- **借用规则**：理解不可变借用与可变借用的互斥性
- **生命周期**：掌握生命周期参数和生命周期省略

### 高级应用

- **并发编程**：[crates/c05_threads](../../../crates/c05_threads/)
- **异步编程**：[crates/c06_async](../../../crates/c06_async/)
- **智能指针使用**：理解不同智能指针的适用场景

### 常见模式

```rust
// 所有权转移示例
let s1 = String::from("hello");
let s2 = s1; // s1 被移动，不再可用
// println!("{}", s1); // 编译错误

// 借用示例
let s = String::from("hello");
let r1 = &s; // 不可变借用
let r2 = &s; // 另一个不可变借用
// let r3 = &mut s; // 编译错误：不可变借用与可变借用不能共存

// 生命周期示例
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

## 设计原则

### Rust 化改造

- **优先移动**：默认移动语义，避免不必要的复制
- **借用优先**：优先使用借用而非所有权转移
- **生命周期显式**：在需要时显式标注生命周期参数
- **智能指针适度**：仅在必要时使用智能指针

### 最佳实践

- **最小作用域**：变量在最小必要作用域中声明
- **明确所有权**：明确谁拥有数据，谁借用数据
- **避免循环引用**：使用 `Weak<T>` 打破循环引用
- **错误处理**：使用 `Result` 和 `Option` 处理可能的失败

## 相关索引

- **类型系统**：[`../01_type_system/00_index.md`](../01_type_system/00_index.md) - 类型与所有权的结合
- **内存安全**：[`../02_memory_safety/00_index.md`](../02_memory_safety/00_index.md) - 内存安全的理论基础
- **生命周期管理**：[`../06_lifetime_management/00_index.md`](../06_lifetime_management/00_index.md) - 生命周期的高级主题
- **并发模型**：[`../04_concurrency_models/00_index.md`](../04_concurrency_models/00_index.md) - 并发中的所有权

## 导航

- **返回理论基础**：[`../00_index.md`](../00_index.md)
- **编程范式**：[`../../02_programming_paradigms/00_index.md`](../../02_programming_paradigms/00_index.md)
- **设计模式**：[`../../03_design_patterns/00_index.md`](../../03_design_patterns/00_index.md)
- **质量保障**：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
- **返回项目根**：[`../../README.md`](../../README.md)
