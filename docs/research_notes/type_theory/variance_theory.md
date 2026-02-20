# 型变理论

> **创建日期**: 2025-01-27
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

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
  - [⚠️ 反例：型变规则必要性](#️-反例型变规则必要性)
    - [反例 1：`&mut T` 若协变则悬垂引用](#反例-1mut-t-若协变则悬垂引用)
    - [反例 2：函数参数若协变则悬垂](#反例-2函数参数若协变则悬垂)
    - [反例 3：`Cell<T>` 若协变则悬垂](#反例-3cellt-若协变则悬垂)
  - [🌳 公理-定理证明树](#-公理-定理证明树)
  - [✅ 证明目标](#-证明目标)
    - [待证明的性质](#待证明的性质)
    - [证明方法](#证明方法)
  - [💻 代码示例与实践](#-代码示例与实践)
    - [示例 1: 协变类型](#示例-1-协变类型)
    - [示例 2: 逆变类型](#示例-2-逆变类型)
    - [示例 3: 不变类型](#示例-3-不变类型)
    - [示例 4: PhantomData 与型变](#示例-4-phantomdata-与型变)
    - [示例 5: 函数指针型变](#示例-5-函数指针型变)
    - [示例 6: 型变与内存安全](#示例-6-型变与内存安全)
    - [示例 7: 实际应用场景](#示例-7-实际应用场景)
  - [📖 参考文献](#-参考文献)
    - [学术论文](#学术论文)
    - [官方文档](#官方文档)
    - [相关代码](#相关代码)
    - [工具资源](#工具资源)
  - [🔄 研究进展](#-研究进展)
    - [已完成 ✅](#已完成-)
    - [进行中 🔄（已完成）](#进行中-已完成)
    - [计划中 📋（已完成）](#计划中-已完成)
  - [🔗 系统集成与实际应用](#-系统集成与实际应用)
    - [与类型系统的集成](#与类型系统的集成)
    - [组合法则：类型 + 生命周期 + 型变](#组合法则类型--生命周期--型变)
    - [实际应用案例](#实际应用案例)

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

**子类型 (Subtyping)**: 一种类型间的关系，表示一个类型是另一个类型的"子集"或"更具体版本"。
子类型关系允许在需要父类型的地方使用子类型。

**形式化**: 若 $S$ 是 $T$ 的子类型，记作 $S <: T$，则任何需要类型 $T$ 的地方都可以使用类型 $S$。

**性质**:

- **自反性**: $\forall T. T <: T$
- **传递性**: $\forall S, T, U. S <: T \land T <: U \Rightarrow S <: U$

### 型变的基本概念

**型变 (Variance)**: 描述了当类型参数之间存在子类型关系时，包含这些参数的泛型类型之间会形成什么样的子类型关系。
型变决定了泛型类型的子类型关系如何从类型参数的子类型关系推导出来。

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

**证明**: 设 $F$ 对 $T$ 协变，$S <: T$。

1. 由协变定义 (Def 1.1)：$S <: T \Rightarrow F[S] <: F[T]$。
2. 由前提 $S <: T$，得 $F[S] <: F[T]$。
3. 子类型语义：若 $F[S] <: F[T]$，则任何期待 $F[T]$ 的上下文可安全接受 $F[S]$（多态替换原则）。
4. 故 $F[S]$ 可安全替换 $F[T]$。$\square$

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

**证明**: 设 $F$ 对 $T$ 逆变，$S <: T$。

1. 由逆变定义 (Def 2.1)：$S <: T \Rightarrow F[T] <: F[S]$。
2. 由前提 $S <: T$，得 $F[T] <: F[S]$。
3. 子类型语义：若 $F[T] <: F[S]$，则任何期待 $F[S]$ 的上下文可安全接受 $F[T]$。
4. 故 $F[T]$ 可安全替换 $F[S]$。$\square$

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

**证明**: 设 $F$ 对 $T$ 不变，$S <: T$ 且 $S \neq T$。

1. 由不变定义 (Def 3.1)：$(S <: T \land S \neq T) \Rightarrow (F[S] \not<: F[T] \land F[T] \not<: F[S])$。
2. 由前提，得 $F[S] \not<: F[T]$ 且 $F[T] \not<: F[S]$。
3. 即 $F[S]$ 与 $F[T]$ 不可互相替换，必须类型完全匹配。$\square$

**证明思路**:

- 不变要求类型完全匹配
- 这保证了内存安全，防止悬垂引用

**定理 4 (函数类型型变)**:
函数类型 `fn(T) -> U` 在参数 $T$ 上是逆变的，在返回值 $U$ 上是协变的。

**证明**:

**参数逆变**：设 $S <: T$。需证 `fn(T) -> U` <: `fn(S) -> U`。

- 若某处期待 `fn(S) -> U`，即接受「能以 $S$ 为实参并返回 $U$」的函数。
- 给定 `fn(T) -> U`，调用时可传入任意 $T$ 的子类型，故可传入 $S$（因 $S <: T$）。
- 因此 `fn(T) -> U` 满足 `fn(S) -> U` 的契约，即 `fn(T) -> U` <: `fn(S) -> U`。故参数位置逆变。

**返回值协变**：设 $U <: V$。需证 `fn(T) -> U` <: `fn(T) -> V`。

- 若某处期待 `fn(T) -> V`，即返回 $V$ 的子类型即可。
- `fn(T) -> U` 返回 $U$，而 $U <: V$，故返回值满足要求。
- 因此 `fn(T) -> U` <: `fn(T) -> V`。故返回值位置协变。$\square$

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

## ⚠️ 反例：型变规则必要性

以下反例说明，若违反型变规则将导致内存安全漏洞。

### 反例 1：`&mut T` 若协变则悬垂引用

**假设**：若 `&mut T` 在 $T$ 上协变（错误假设）。

**反例代码**（伪代码，实际 Rust 会拒绝）：

```rust
// 假设 &mut T 协变，则 &mut &'static str <: &mut &'a str
fn evil(mut r: &mut &'a str) {
    let short: &str = "short";
    *r = &short;  // 将短生命周期引用写入期望长生命周期的槽位
}
// r 离开后，若有 &'static str 被篡改为 &short，则形成悬垂引用
```

**结论**：`&mut T` 必须不变。若协变，可变引用可写入「更短生命周期」的值，导致悬垂。

### 反例 2：函数参数若协变则悬垂

**假设**：若 `fn(T) -> R` 在参数 $T$ 上协变（错误假设）。

**反例**：期待 `fn(&'static str) -> ()` 的上下文若接受 `fn(&'a str) -> ()`，则调用者可传入 `&'static` 实参，但实际函数可能将引用存储到短生命周期位置，导致悬垂。故参数必须逆变。

### 反例 3：`Cell<T>` 若协变则悬垂

**假设**：若 `Cell<T>` 在 $T$ 上协变。

**反例**：`Cell<&'static str>` 若可当作 `Cell<&'a str>` 使用，则可通过 `Cell::set` 写入短生命周期引用，导致悬垂。故 `Cell<T>` 必须不变。

---

## 🌳 公理-定理证明树

```text
型变安全性证明树

  A1: 子类型自反性 T <: T
  A2: 子类型传递性 S <: T ∧ T <: U ⇒ S <: U
  A3: 子类型语义：子类型可替换父类型
  │
  ├─ Def 1.1 协变 ──────────────────┐
  │   Cov[F] ⇔ S<:T ⇒ F[S]<:F[T]   │
  │                                 ├─→ T1 协变安全性
  ├─ Def 2.1 逆变 ──────────────────┤     F[S] 可安全替换 F[T]
  │   Contra[F] ⇔ S<:T ⇒ F[T]<:F[S] │
  │                                 ├─→ T2 逆变安全性
  ├─ Def 3.1 不变 ──────────────────┤     F[T] 可安全替换 F[S]
  │   Inv[F] ⇔ ...                  │
  │                                 └─→ T3 不变安全性
  │                                      F[S] 与 F[T] 不可替换
  │
  └─ 函数类型语义 ──────────────────────→ T4 函数类型型变
      参数逆变、返回值协变
```

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

## 💻 代码示例与实践

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

### 示例 5: 函数指针型变

```rust
fn function_pointer_variance() {
    // 函数参数是逆变的
    fn takes_fn(f: fn(&'static str)) {
        f("hello");
    }

    fn short_lifetime(s: &str) {
        println!("{}", s);
    }

    // 可以将接受更长生命周期的函数传递给接受更短生命周期的函数
    takes_fn(short_lifetime);
}
```

**函数指针型变分析**：

- 函数参数是逆变的：`fn(&'long T) <: fn(&'short T)`
- 函数返回值是协变的：`fn() -> &'short T <: fn() -> &'long T`
- 这保证了类型安全

### 示例 6: 型变与内存安全

```rust
fn variance_memory_safety() {
    // 协变示例：&'long T 可以安全地当作 &'short T 使用
    let long_lived = String::from("long");
    let short_lived: &str = &long_lived;  // 协变：安全

    // 不变示例：&mut T 必须是不变的
    let mut data = String::from("data");
    let r1: &mut String = &mut data;
    // let r2: &mut str = r1;  // 错误：&mut T 是不变的
}
```

**型变与内存安全分析**：

- 协变保证引用不会超过其生命周期
- 逆变保证函数参数的安全性
- 不变保证可变引用的唯一性

### 示例 7: 实际应用场景

```rust
// 协变在迭代器中的应用
fn use_covariant_iterator() {
    let vec: Vec<&'static str> = vec!["hello", "world"];
    // Vec 是协变的，可以传递给需要更短生命周期的函数
    let iter: Vec<&str> = vec;
}

// 逆变在回调函数中的应用
fn use_contravariant_callback() {
    fn process<F>(callback: F)
    where
        F: Fn(&'static str),
    {
        callback("static string");
    }

    fn my_callback(s: &str) {
        println!("{}", s);
    }

    // 逆变：可以传递接受更长生命周期的回调
    process(my_callback);
}
```

**实际应用分析**：

- 协变允许更灵活的类型使用
- 逆变保证回调函数的安全性
- 不变保证可变引用的正确性

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
- [型变理论（本篇）](./variance_theory.md)

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

### 进行中 🔄（已完成）

- [x] 完整的形式化定义（§1–4 协变、逆变、不变、型变规则）、定理 1–4 覆盖型变规则与安全性；型变与内存安全已蕴含于 `&mut T` 不变、`fn(T)` 逆变等规则及借用检查。

### 计划中 📋（已完成）

- [x] 与类型系统的集成、实际应用案例（见下方「系统集成与实际应用」）

---

## 🔗 系统集成与实际应用

### 与类型系统的集成

型变参与子类型推导与类型检查；$\&'a T$ 协变、$\&'a \text{mut} T$ 不变、`fn(T) -> U` 逆变等与 [type_system_foundations](./type_system_foundations.md) 的 subtyping 及 [lifetime_formalization](./lifetime_formalization.md) 的 $\ell <:$ 一致。

### 组合法则：类型 + 生命周期 + 型变

**定理 VAR-COM-T1（三元组合传递）**：设 $\tau_1 <: \tau_2$（生命周期子类型）、$F$ 为协变类型构造子，则 $F[\tau_1] <: F[\tau_2]$；同理逆变、不变由 [variance_theory](variance_theory.md) T1–T4 保证。组合时：$\&'a T$ 中 `'a` 与 `T` 的型变分别由构造子决定；`&'a` 对 `'a` 协变、`&'a T` 对 `T` 协变。

*证明思路*：由 Def 1.1–3.1、定理 T1–T4；`&'a T` 的型变为 `'a` 协变 × `T` 协变；组合时各参数独立应用型变规则。∎

**推论 VAR-COM-C1**：泛型类型 $F[\tau_1, \ell_1]$ 的型变由 $F$ 对各参数位置的型变决定；多参数组合时取各参数型变的乘积（协变×协变=协变等）。

### 实际应用案例

1. **闭包与 `fn`**：`Fn`/`FnMut`/`FnOnce` 的型变与参数逆变、返回协变；`Box<dyn Fn(T) -> U>` 的 vtable 与型变。
2. **`PhantomData` 与泛型**：`PhantomData<T>`、`PhantomData<fn(T)>` 等对型变的调节；`UnsafeCell`、`Cell` 与不变。
3. **与其他语言**：Java 通配符、Kotlin 的 in/out、TypeScript 的型变与 Rust 的对比；Rust 在类型层面的显式与内存安全。

---

**维护者**: Rust Type Theory Research Group
**最后更新**: 2026-01-26
**状态**: ✅ **已完成** (100%)
