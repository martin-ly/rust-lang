# 型变理论

> **创建日期**: 2025-01-27
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: 🔄 进行中

---

## 📊 目录

- [型变理论](#型变理论)
  - [📊 目录](#-目录)
  - [🎯 研究目标](#-研究目标)
    - [核心问题](#核心问题)
    - [预期成果](#预期成果)
  - [📚 理论基础](#-理论基础)
    - [子类型关系](#子类型关系)
    - [型变的基本概念](#型变的基本概念)
    - [Rust 中的型变](#rust-中的型变)
    - [相关概念](#相关概念)
    - [理论背景](#理论背景)
  - [🔬 形式化定义](#-形式化定义)
    - [1. 协变 (Covariance)](#1-协变-covariance)
    - [2. 逆变 (Contravariance)](#2-逆变-contravariance)
    - [3. 不变 (Invariance)](#3-不变-invariance)
    - [4. 型变规则](#4-型变规则)
  - [✅ 证明目标](#-证明目标)
    - [待证明的性质](#待证明的性质)
    - [证明方法](#证明方法)
  - [💻 代码示例](#-代码示例)
    - [示例 1: 协变类型](#示例-1-协变类型)
    - [示例 2: 逆变类型](#示例-2-逆变类型)
    - [示例 3: 不变类型](#示例-3-不变类型)
    - [示例 4: PhantomData 与型变](#示例-4-phantomdata-与型变)
  - [📖 参考文献](#-参考文献)
    - [学术论文](#学术论文)
    - [官方文档](#官方文档)
    - [相关代码](#相关代码)
    - [工具资源](#工具资源)
  - [🔄 研究进展](#-研究进展)
    - [已完成 ✅](#已完成-)
    - [进行中 🔄](#进行中-)
    - [计划中 📋](#计划中-)

---

## 🎯 研究目标

本研究的目的是深入理解 Rust 的型变（Variance）理论，并形式化定义型变规则。

### 核心问题

1. **型变的形式化定义**: 如何用数学语言精确描述型变？
2. **型变规则推导**: Rust 的型变规则如何推导？
3. **型变与内存安全**: 型变如何保证内存安全？

### 预期成果

- 型变的完整形式化定义
- 型变规则的推导证明
- 型变与内存安全的关系证明

---

## 📚 理论基础

### 子类型关系

**子类型 (Subtyping)**: 一种类型间的关系，表示一个类型是另一个类型的"子集"或"更具体版本"。子类型关系允许在需要父类型的地方使用子类型。

**形式化**: 若 $S$ 是 $T$ 的子类型，记作 $S <: T$，则任何需要类型 $T$ 的地方都可以使用类型 $S$。

**性质**:

- **自反性**: $\forall T. T <: T$
- **传递性**: $\forall S, T, U. S <: T \land T <: U \Rightarrow S <: U$

### 型变的基本概念

**型变 (Variance)**: 描述了当类型参数之间存在子类型关系时，包含这些参数的泛型类型之间会形成什么样的子类型关系。型变决定了泛型类型的子类型关系如何从类型参数的子类型关系推导出来。

**核心问题**: 给定 $S <: T$，泛型类型 $F[S]$ 和 $F[T]$ 之间是什么关系？

**型变种类**:

- **协变 (Covariance)**: $S <: T \Rightarrow F[S] <: F[T]$
- **逆变 (Contravariance)**: $S <: T \Rightarrow F[T] <: F[S]$
- **不变 (Invariance)**: $S <: T$ 不导致 $F[S]$ 和 $F[T]$ 之间的子类型关系

### Rust 中的型变

在 Rust 中，型变最常通过**生命周期**来体现。如果生命周期 `'long` 长于 `'short`（写作 `'long: 'short`），那么 `'long` 就是 `'short` 的一个子类型。

**生命周期型变**: Rust 中的型变主要通过生命周期参数体现，类型参数的型变相对较少。

**内存安全**: Rust 的型变规则设计是为了保证内存安全，防止悬垂引用和数据竞争。

### 相关概念

**协变 (Covariance)**: 如果 $S <: T$，则 $F[S] <: F[T]$。协变允许在需要 $F[T]$ 的地方使用 $F[S]$。

**逆变 (Contravariance)**: 如果 $S <: T$，则 $F[T] <: F[S]$。逆变允许在需要 $F[S]$ 的地方使用 $F[T]$。

**不变 (Invariance)**: $S <: T$ 不导致 $F[S]$ 和 $F[T]$ 之间的子类型关系。不变要求类型完全匹配。

**双变 (Bivariance)**: 如果 $S <: T$ 和 $T <: S$ 都导致 $F[S] <: F[T]$ 和 $F[T] <: F[S]$，则 $F$ 是双变的。Rust 中不存在双变。

**生命周期子类型**: 在 Rust 中，较长的生命周期是较短生命周期的子类型。例如，`'static` 是所有生命周期的子类型。

**函数类型型变**: 函数类型的参数是逆变的，返回值是协变的。这保证了函数调用的类型安全。

### 理论背景

**子类型理论 (Subtyping Theory)**: 型变理论基于子类型理论，子类型理论研究类型之间的子类型关系。

**类型系统安全**: 型变规则必须保证类型系统的安全性，防止类型错误。

**内存安全**: Rust 的型变规则设计是为了保证内存安全，防止悬垂引用和数据竞争。

**函数类型语义**: 函数类型的型变规则基于函数调用的语义，参数逆变和返回值协变保证了函数调用的类型安全。

---

## 🔬 形式化定义

### 1. 协变 (Covariance)

**定义 1.1 (协变)**: 对于参数化类型构造器 $F[T]$，如果 $S <: T \Rightarrow F[S] <: F[T]$，则 $F$ 对参数 $T$ 是**协变的**。

**形式化表示**:
$$\text{Cov}[F] \Leftrightarrow \forall S, T. S <: T \Rightarrow F[S] <: F[T]$$

**Rust 示例**:

- `&'a T` 在 `'a` 上是协变的
- `Box<T>` 在 $T$ 上是协变的
- `Vec<T>` 在 $T$ 上是协变的

**定理 1 (协变安全性)**:
如果 $F$ 对 $T$ 是协变的，且 $S <: T$，则 $F[S]$ 可以安全地替换 $F[T]$。

**证明思路**:

- 协变保证 $F[S] <: F[T]$
- 子类型关系保证类型安全

### 2. 逆变 (Contravariance)

**定义 2.1 (逆变)**: 对于参数化类型构造器 $F[T]$，如果 $S <: T \Rightarrow F[T] <: F[S]$，则 $F$ 对参数 $T$ 是**逆变的**。

**形式化表示**:
$$\text{Contra}[F] \Leftrightarrow \forall S, T. S <: T \Rightarrow F[T] <: F[S]$$

**Rust 示例**:

- `fn(T) -> R` 在参数类型 $T$ 上是逆变的
- 函数指针的参数位置是逆变的

**定理 2 (逆变安全性)**:
如果 $F$ 对 $T$ 是逆变的，且 $S <: T$，则 $F[T]$ 可以安全地替换 $F[S]$。

**证明思路**:

- 逆变保证 $F[T] <: F[S]$
- 函数参数逆变保证了函数调用的类型安全

### 3. 不变 (Invariance)

**定义 3.1 (不变)**: 对于参数化类型构造器 $F[T]$，如果 $S <: T \land S \neq T \Rightarrow F[S] \not<: F[T] \land F[T] \not<: F[S]$，则 $F$ 对参数 $T$ 是**不变的**。

**形式化表示**:
$$\text{Inv}[F] \Leftrightarrow \forall S, T. (S <: T \land S \neq T) \Rightarrow (F[S] \not<: F[T] \land F[T] \not<: F[S])$$

**Rust 示例**:

- `&mut T` 在 $T$ 上是不变的
- `Cell<T>` 在 $T$ 上是不变的
- `UnsafeCell<T>` 在 $T$ 上是不变的

**定理 3 (不变安全性)**:
如果 $F$ 对 $T$ 是不变的，则 $F[S]$ 和 $F[T]$ 之间没有子类型关系，即使 $S <: T$。

**证明思路**:

- 不变要求类型完全匹配
- 这保证了内存安全，防止悬垂引用

**定理 4 (函数类型型变)**:
函数类型 `fn(T) -> U` 在参数 $T$ 上是逆变的，在返回值 $U$ 上是协变的。

**证明思路**:

- 参数逆变：如果 $S <: T$，则 `fn(T) -> U` 可以替换 `fn(S) -> U`
- 返回值协变：如果 $U <: V$，则 `fn(T) -> U` 可以替换 `fn(T) -> V`

### 4. 型变规则

**定理 1 (型变规则)**: Rust 的型变规则由类型参数的使用方式决定：

1. **输出位置**（返回类型）是协变的
2. **输入位置**（参数类型）是逆变的
3. **输入和输出位置都存在**时，类型是不变的
4. **PhantomData<T>** 在 $T$ 上是协变的

**证明思路**:

- 输出位置的协变性保证返回值的类型安全
- 输入位置的逆变性保证参数的类型安全
- 同时出现在输入和输出位置时，不变性保证类型安全

---

## ✅ 证明目标

### 待证明的性质

1. **型变规则正确性**: 型变规则保证类型安全
2. **型变推导**: 编译器正确推导型变
3. **内存安全**: 型变规则保证内存安全

### 证明方法

- **类型系统证明**: 证明型变规则的类型系统保证
- **语义证明**: 证明型变的语义正确性
- **安全性证明**: 证明型变规则的安全性

---

## 💻 代码示例

### 示例 1: 协变类型

```rust
fn covariant_example() {
    let long: &'static str = "hello";
    let short: &'a str = long;  // 协变：'static : 'a

    let box_long: Box<&'static str> = Box::new("hello");
    let box_short: Box<&'a str> = box_long;  // 协变
}
```

**形式化描述**:

- `&'a T` 在 `'a` 上是协变的
- `'static : 'a \Rightarrow &'static T <: &'a T`
- `Box<T>` 在 $T$ 上是协变的

### 示例 2: 逆变类型

```rust
fn contravariant_example() {
    fn takes_str(s: &str) {
        println!("{}", s);
    }

    fn takes_static(s: &'static str) {
        println!("{}", s);
    }

    // 逆变：函数参数位置
    let f1: fn(&str) = takes_str;
    let f2: fn(&'static str) = f1;  // 逆变：&str <: &'static str
}
```

**形式化描述**:

- `fn(T) -> R` 在参数类型 $T$ 上是逆变的
- `&str <: &'static str \Rightarrow fn(&'static str) <: fn(&str)`

### 示例 3: 不变类型

```rust
fn invariant_example() {
    let mut x: &mut i32 = &mut 42;
    // let y: &mut &'static i32 = x;  // 错误：&mut T 是不变的

    use std::cell::Cell;
    let cell: Cell<&'static str> = Cell::new("hello");
    // let cell2: Cell<&'a str> = cell;  // 错误：Cell<T> 是不变的
}
```

**形式化描述**:

- `&mut T` 在 $T$ 上是不变的
- `Cell<T>` 在 $T$ 上是不变的
- 不变性保证内存安全

### 示例 4: PhantomData 与型变

```rust
use std::marker::PhantomData;

struct CovariantWrapper<T> {
    data: PhantomData<T>,
}

struct InvariantWrapper<T> {
    data: T,
}

fn phantom_example() {
    let cov: CovariantWrapper<&'static str> = CovariantWrapper {
        data: PhantomData,
    };
    let cov2: CovariantWrapper<&'a str> = cov;  // 协变：PhantomData 是协变的

    let inv: InvariantWrapper<&'static str> = InvariantWrapper {
        data: "hello",
    };
    // let inv2: InvariantWrapper<&'a str> = inv;  // 错误：不变
}
```

**形式化描述**:

- `PhantomData<T>` 在 $T$ 上是协变的
- 使用 `PhantomData` 可以控制类型的型变行为

---

## 📖 参考文献

### 学术论文

1. **Types and Programming Languages**
   - 作者: Benjamin C. Pierce
   - 年份: 2002
   - 摘要: 类型系统的经典教科书，包含型变理论

2. **Variance and Subtyping in Rust**
   - 作者: Rust 团队
   - 摘要: Rust 型变系统的设计和实现

### 官方文档

- [Rust Reference - Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping.html)
- [型变参考文档](../../../crates/c02_type_system/docs/tier_03_references/02_类型型变参考.md)
- [高级类型特性 - 型变](../../../docs/docs/language/ref/28_advanced_type_features/06_variance_and_subtyping.md)

### 相关代码

- [型变实现](../../../crates/c02_type_system/src/)
- [型变示例](../../../crates/c02_type_system/examples/)
- [形式化工程系统 - 型变](../../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/06_variance.md)

### 工具资源

- [Rust Analyzer](https://rust-analyzer.github.io/): 提供型变检查
- [Chalk](https://github.com/rust-lang/chalk): Rust Trait 系统的形式化模型，包含型变

---

## 🔄 研究进展

### 已完成 ✅

- [x] 研究目标定义
- [x] 理论基础整理（包括理论背景和相关概念）
- [x] 初步形式化定义
- [x] 添加协变安全性定理（定理 1）
- [x] 添加逆变安全性定理（定理 2）
- [x] 添加不变安全性定理（定理 3）
- [x] 添加函数类型型变定理（定理 4）

### 进行中 🔄

- [ ] 完整的形式化定义
- [ ] 型变规则推导证明
- [ ] 型变与内存安全的关系证明

### 计划中 📋

- [ ] 与类型系统的集成
- [ ] 实际应用案例
- [ ] 与其他语言对比

---

**维护者**: Rust Type Theory Research Group
**最后更新**: 2025-11-15
**状态**: 🔄 **进行中**
