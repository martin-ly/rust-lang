# 高级示例（Advanced Examples）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-11
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [高级示例（Advanced Examples）索引](#高级示例advanced-examples索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [🆕 Rust 1.91.0 新特性](#-rust-1910-新特性)
    - [模式匹配绑定顺序改进](#模式匹配绑定顺序改进)
  - [📚 核心示例](#-核心示例)
    - [1. 高级类型系统（Advanced Type System）](#1-高级类型系统advanced-type-system)
    - [2. 宏系统（Macro System）](#2-宏系统macro-system)
    - [3. 异步编程（Async Programming）](#3-异步编程async-programming)
    - [4. 并发编程（Concurrent Programming）](#4-并发编程concurrent-programming)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c04_generic/src/`](#cratesc04_genericsrc)
      - [`crates/c05_threads/src/`](#cratesc05_threadssrc)
  - [📚 内容文档](#-内容文档)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块提供 Rust 高级概念和技术的实用示例，涵盖高级类型系统、宏系统、异步编程和并发编程等核心主题。所有示例均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **高级特性**: 深入讲解 Rust 的高级特性
- **实用示例**: 提供可直接运行的代码示例
- **最佳实践**: 基于 Rust 社区最新实践
- **易于理解**: 提供详细注释和说明

## 🆕 Rust 1.91.0 新特性

### 模式匹配绑定顺序改进

**特性说明**：Rust 1.91.0 对模式匹配的绑定顺序进行了重构，提升了语义一致性和安全性。

**改进示例**：

```rust
// Rust 1.91 改进：模式匹配绑定顺序
fn pattern_matching_example() {
    let value = Some(42);

    // 新的绑定顺序确保语义一致性
    match value {
        Some(x) if x > 0 => {
            // x 在这里已经正确绑定
            println!("Positive: {}", x);
        }
        Some(x) => {
            // x 的绑定顺序已优化
            println!("Value: {}", x);
        }
        None => println!("None"),
    }

    // 复杂模式匹配示例
    let tuple = (Some(1), Some(2));
    match tuple {
        (Some(a), Some(b)) if a < b => {
            // a 和 b 的绑定顺序已优化
            println!("Ordered: {} < {}", a, b);
        }
        (Some(a), Some(b)) => {
            // 绑定顺序保证语义一致性
            println!("Values: {}, {}", a, b);
        }
        _ => println!("Other"),
    }
}
```

**形式化意义**：

- 改进了模式匹配的形式化语义
- 增强了类型系统的形式化保证
- 修复了潜在的逻辑错误和语义不一致问题

**相关资源**：

- [形式化论证集合](../../FORMAL_PROOFS_2025_11_11.md#定理2模式匹配绑定顺序的语义一致性)
- [知识图谱](../../KNOWLEDGE_GRAPH_2025_11_11.md#13-模式匹配绑定顺序重构)
- [理论基础](../../01_theoretical_foundations/01_type_system/advanced_theory/00_index.md#rust-1910-新特性)

## 📚 核心示例

### 1. 高级类型系统（Advanced Type System）

**推荐资源**: Rust Book, Rustonomicon, Type-Driven Development

- **高级泛型**: 泛型约束、泛型生命周期、泛型关联类型
- **关联类型**: Trait 关联类型、GAT（Generic Associated Types）
- **高级生命周期**: 生命周期省略、生命周期子类型、高阶生命周期
- **类型级编程**: 类型函数、类型级计算、依赖类型

**相关资源**:

- [Rust Book - Advanced Types](https://doc.rust-lang.org/book/ch19-04-advanced-types.html)
- [Rustonomicon](https://doc.rust-lang.org/nomicon/)
- [GAT RFC](https://github.com/rust-lang/rfcs/blob/master/text/1598-generic_associated_types.md)

### 2. 宏系统（Macro System）

**推荐库**: `proc-macro2`, `syn`, `quote`, `darling`

- **声明宏**: `macro_rules!` 宏定义和使用
- **过程宏**: 派生宏、属性宏、函数式宏
- **派生宏**: 自动实现 Trait（如 `Debug`, `Clone`）
- **属性宏**: 自定义属性宏（如 `#[derive]`）

**相关资源**:

- [Rust Book - Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [proc-macro2 文档](https://docs.rs/proc-macro2/)
- [syn 文档](https://docs.rs/syn/)

### 3. 异步编程（Async Programming）

**推荐库**: `tokio`, `async-std`, `futures`, `async-trait`

- **Future 实现**: 自定义 Future 类型
- **异步流**: `Stream` trait 和异步迭代
- **异步迭代器**: `AsyncIterator` 和异步生成器
- **异步错误处理**: 异步环境下的错误处理模式

**相关资源**:

- [Tokio 文档](https://tokio.rs/)
- [async-std 文档](https://docs.rs/async-std/)
- [futures 文档](https://docs.rs/futures/)

### 4. 并发编程（Concurrent Programming）

**推荐库**: `crossbeam`, `parking_lot`, `rayon`, `std::sync`

- **高级同步原语**: 自定义锁、条件变量、屏障
- **无锁数据结构**: 无锁队列、无锁栈、原子操作
- **工作窃取**: 工作窃取队列、任务调度
- **并发模式**: Actor 模式、CSP 模式、数据并行

**相关资源**:

- [crossbeam 文档](https://docs.rs/crossbeam/)
- [parking_lot 文档](https://docs.rs/parking_lot/)
- [rayon 文档](https://docs.rs/rayon/)

## 💻 实践与样例

### 代码示例位置

- **高级示例**: [crates/c04_generic](../../../crates/c04_generic/)
- **并发编程**: [crates/c05_threads](../../../crates/c05_threads/)
- **异步编程**: [crates/c06_async](../../../crates/c06_async/)

### 文件级清单（精选）

#### `crates/c04_generic/src/`

- `advanced_generics.rs` - 高级泛型示例
- `associated_types.rs` - 关联类型示例
- `type_level_programming.rs` - 类型级编程示例

#### `crates/c05_threads/src/`

- `advanced_synchronization.rs` - 高级同步原语
- `lockfree_structures.rs` - 无锁数据结构
- `work_stealing.rs` - 工作窃取示例

---

## 📚 内容文档

- **[异步编程高级示例](./01_async_programming.md)** - 异步编程的实践示例 ✅

## 🔗 相关索引

- **理论基础（Trait 系统）**: [`../../01_theoretical_foundations/05_trait_system/00_index.md`](../../01_theoretical_foundations/05_trait_system/00_index.md)
- **理论基础（宏系统）**: [`../../01_theoretical_foundations/08_macro_system/00_index.md`](../../01_theoretical_foundations/08_macro_system/00_index.md)
- **编程范式（异步）**: [`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)

---

## 🧭 导航

- **返回实用示例**: [`../00_index.md`](../00_index.md)
- **基础示例**: [`../01_basic_examples/00_index.md`](../01_basic_examples/00_index.md)
- **真实案例**: [`../03_real_world_cases/00_index.md`](../03_real_world_cases/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
