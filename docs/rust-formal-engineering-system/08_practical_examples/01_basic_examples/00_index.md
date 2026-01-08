# 基础示例（Basic Examples）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [基础示例（Basic Examples）索引](#基础示例basic-examples索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心示例](#-核心示例)
    - [1. 所有权与借用（Ownership \& Borrowing）](#1-所有权与借用ownership--borrowing)
    - [2. 类型系统（Type System）](#2-类型系统type-system)
    - [3. 错误处理（Error Handling）](#3-错误处理error-handling)
    - [4. 集合与迭代器（Collections \& Iterators）](#4-集合与迭代器collections--iterators)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c01_ownership_borrow_scope/src/`](#cratesc01_ownership_borrow_scopesrc)
      - [`crates/c03_control_fn/src/`](#cratesc03_control_fnsrc)
    - [快速开始示例](#快速开始示例)
  - [📚 内容文档](#-内容文档)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块提供 Rust 基础概念和语法的实用示例，涵盖所有权、类型系统、错误处理和集合操作等核心主题。所有示例均基于 Rust 1.91.0，适合初学者快速上手。

### 核心价值

- **基础扎实**: 覆盖 Rust 核心概念
- **易于理解**: 提供清晰的示例和注释
- **循序渐进**: 从简单到复杂的学习路径
- **实用性强**: 所有示例均可直接运行

## 📚 核心示例

### 1. 所有权与借用（Ownership & Borrowing）

**推荐资源**: Rust Book Chapter 4, Rust by Example

- **所有权转移**: 所有权转移和移动语义
- **借用规则**: 引用和借用规则
- **生命周期**: 生命周期标注和省略
- **引用与解引用**: 引用类型和解引用操作

**相关资源**:

- [Rust Book - Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Rust by Example - Ownership](https://doc.rust-lang.org/rust-by-example/scope/move.html)

### 2. 类型系统（Type System）

**推荐资源**: Rust Book Chapter 3, Rustonomicon

- **基本类型**: 整数、浮点数、布尔值、字符
- **复合类型**: 元组、数组、切片
- **枚举与模式匹配**: 枚举类型和模式匹配（Rust 1.91 改进）
- **结构体与实现**: 结构体定义和方法实现

**相关资源**:

- [Rust Book - Types](https://doc.rust-lang.org/book/ch03-00-common-programming-concepts.html)
- [Rust Book - Pattern Matching](https://doc.rust-lang.org/book/ch18-00-patterns.html)

### 3. 错误处理（Error Handling）

**推荐库**: `thiserror`, `anyhow`, `eyre`

- **Result 类型**: `Result<T, E>` 类型使用
- **Option 类型**: `Option<T>` 类型使用
- **错误传播**: `?` 操作符和错误传播
- **自定义错误类型**: 自定义错误类型实现

**相关资源**:

- [Rust Book - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [thiserror 文档](https://docs.rs/thiserror/)
- [anyhow 文档](https://docs.rs/anyhow/)

### 4. 集合与迭代器（Collections & Iterators）

**推荐库**: `std::collections`, `itertools`

- **向量操作**: `Vec<T>` 常用操作
- **哈希映射**: `HashMap<K, V>` 使用示例
- **迭代器使用**: 迭代器方法和链式调用
- **函数式编程**: 函数式编程风格示例

**相关资源**:

- [Rust Book - Collections](https://doc.rust-lang.org/book/ch08-00-common-collections.html)
- [Rust Book - Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html)
- [itertools 文档](https://docs.rs/itertools/)

## 💻 实践与样例

### 代码示例位置

- **基础示例**: [crates/c01_ownership_borrow_scope](../../../crates/c01_ownership_borrow_scope/)
- **控制与函数**: [crates/c03_control_fn](../../../crates/c03_control_fn/)
- **泛型与 trait**: [crates/c04_generic](../../../crates/c04_generic/)

### 文件级清单（精选）

#### `crates/c01_ownership_borrow_scope/src/`

- `ownership.rs` - 所有权示例
- `borrowing.rs` - 借用示例
- `lifetimes.rs` - 生命周期示例

#### `crates/c03_control_fn/src/`

- `control_flow.rs` - 控制流示例
- `functions.rs` - 函数示例
- `error_handling.rs` - 错误处理示例

### 快速开始示例

```rust
// 所有权示例
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 的所有权转移到 s2
    // println!("{}", s1);  // 错误：s1 不再有效
    println!("{}", s2);  // 正确
}
```

```rust
// 错误处理示例
use std::fs::File;
use std::io::Read;

fn read_file() -> Result<String, std::io::Error> {
    let mut file = File::open("hello.txt")?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}
```

---

## 📚 内容文档

- **[所有权与借用基础示例](./01_ownership_and_borrowing.md)** - 所有权和借用的实践示例 ✅

## 🔗 相关索引

- **理论基础（所有权与借用）**: [`../../01_theoretical_foundations/03_ownership_borrowing/00_index.md`](../../01_theoretical_foundations/03_ownership_borrowing/00_index.md)
- **理论基础（类型系统）**: [`../../01_theoretical_foundations/01_type_system/00_index.md`](../../01_theoretical_foundations/01_type_system/00_index.md)
- **编程范式（函数式）**: [`../../02_programming_paradigms/03_functional/00_index.md`](../../02_programming_paradigms/03_functional/00_index.md)

---

## 🧭 导航

- **返回实用示例**: [`../00_index.md`](../00_index.md)
- **高级示例**: [`../02_advanced_examples/00_index.md`](../02_advanced_examples/00_index.md)
- **真实案例**: [`../03_real_world_cases/00_index.md`](../03_real_world_cases/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
