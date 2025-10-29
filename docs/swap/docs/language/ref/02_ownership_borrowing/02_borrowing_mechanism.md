# 2.2 借用机制的形式化


## 📊 目录

- [1. 概述](#1-概述)
- [2. 借用的核心原则: Aliasing XOR Mutability](#2-借用的核心原则-aliasing-xor-mutability)
- [3. 形式化模型: 借用状态机](#3-形式化模型-借用状态机)
  - [3.1. 状态转换规则](#31-状态转换规则)
  - [3.2. 所有者与借用的交互](#32-所有者与借用的交互)
- [4. 生命周期的作用](#4-生命周期的作用)
  - [4.1. 非词法生命周期 (Non-Lexical Lifetimes, NLL)](#41-非词法生命周期-non-lexical-lifetimes-nll)
- [5. 形式化证明：数据竞争自由](#5-形式化证明数据竞争自由)
- [2.3.10 借用与生命周期](#2310-借用与生命周期)
  - [2.3.10.1 生命周期参数](#23101-生命周期参数)
  - [2.3.10.2 生命周期子类型关系](#23102-生命周期子类型关系)
- [2.3.11 总结](#2311-总结)
- [2.3.12 参考文献](#2312-参考文献)


## 1. 概述

借用（Borrowing）是 Rust 所有权系统的配套机制，它允许在不转移所有权的情况下临时访问值。这种临时访问是通过 **引用（references）** 实现的。借用机制是 Rust 能够在编译时静态地防止数据竞争（data races）的核心。

本章节将为借用机制提供一个形式化的状态机模型，清晰地定义共享引用（`&T`）和独占引用（`&mut T`）的规则、它们如何与所有者交互，以及生命周期的作用。

## 2. 借用的核心原则: Aliasing XOR Mutability

Rust 的借用机制可以概括为一个核心原则：**别名（Aliasing）与可变性（Mutability）的互斥**。

- **别名 (Aliasing)**: 同一内存位置同时存在多个活跃的引用。
- **可变性 (Mutability)**: 通过一个引用来修改其指向的值。

**核心原则**: 对于任意一个值，在任意时刻，以下两种状态**最多只能存在一种**：

1. 存在任意数量的 **共享引用 (Shared References, `&T`)**，此时不允许任何方式的修改（别名，但不可变）。
2. 存在 **一个且仅一个独占引用 (Exclusive Reference, `&mut T`)**，此时允许通过该引用进行修改（可变，但无别名）。

这个原则是编译时数据竞争安全性的基石。

## 3. 形式化模型: 借用状态机

我们可以将一个资源（或值）的借用状态 `B(v)` 建模为一个状态机。其可能的状态包括：

- `Unborrowed`: 资源未被借用。
- `Shared(n)`: 资源被 `n` 个共享引用（`&T`）借用，其中 `n > 0`。
- `Exclusive`: 资源被一个独占引用（`&mut T`）借用。

### 3.1. 状态转换规则

**规则 3.1 (创建共享引用)**:
当创建一个共享引用（`&v`）时，状态发生如下转换：

\[
\text{B}(v) =
\begin{cases}
    \text{Unborrowed} & \to \quad \text{Shared}(1) \\
    \text{Shared}(n) & \to \quad \text{Shared}(n+1) \\
    \text{Exclusive} & \to \quad \textbf{Compile-time Error}
\end{cases}
\]

此规则形式化了"当存在独占引用时，不能创建共享引用"的约束。

**规则 3.2 (创建独占引用)**:
当创建一个独占引用（`&mut v`）时，状态发生如下转换：

\[
\text{B}(v) =
\begin{cases}
    \text{Unborrowed} & \to \quad \text{Exclusive} \\
    \text{Shared}(n) & \to \quad \textbf{Compile-time Error} \\
    \text{Exclusive} & \to \quad \textbf{Compile-time Error}
\end{cases}
\]

此规则形式化了"当存在任何其他引用（共享或独占）时，不能创建新的独占引用"的约束。

### 3.2. 所有者与借用的交互

当一个值被借用时，其所有者的能力会受到严格限制：

**规则 3.3 (所有者权限限制)**:

- 当 `B(v) = Shared(n)` 时，所有者只能读取 `v`，不能修改或转移 `v` 的所有权。
- 当 `B(v) = Exclusive` 时，所有者完全不能访问 `v`（既不能读，也不能写或转移所有权），直到该独占引用失效。

```rust
let mut s = String::from("hello"); // B(s) = Unborrowed
let r1 = &s;                       // B(s) -> Shared(1)
// s.push_str("!");                // 编译错误: B(s) 是 Shared(1)，所有者不能修改

let mut t = String::from("world"); // B(t) = Unborrowed
let r2 = &mut t;                   // B(t) -> Exclusive
// let t2 = t;                     // 编译错误: B(t) 是 Exclusive，所有者不能移动
```

## 4. 生命周期的作用

生命周期（Lifetimes）是确保引用总是指向有效数据的机制。在我们的模型中，生命周期决定了一个引用何时开始和结束，从而触发状态的转换。

**定义 4.1 (生命周期与状态转换)**:

- 一个引用的创建，对应于应用 **规则 3.1** 或 **3.2** 的状态入口转换。
- 一个引用的生命周期结束，对应于状态的出口转换。

**规则 3.4 (引用生命周期结束)**:
当一个共享引用的生命周期结束时：
\[
\text{B}(v) = \text{Shared}(n) \quad \to \quad \text{Shared}(n-1), \text{ if } n > 1
\]
\[
\text{B}(v) = \text{Shared}(1) \quad \to \quad \text{Unborrowed}
\]
当一个独占引用的生命周期结束时：
\[
\text{B}(v) = \text{Exclusive} \quad \to \quad \text{Unborrowed}
\]

### 4.1. 非词法生命周期 (Non-Lexical Lifetimes, NLL)

至关重要的一点是，引用的生命周期**不等于**其词法作用域。Rust 的借用检查器（Borrow Checker）使用 **非词法生命周期 (NLL)** 分析，一个引用的生命周期仅持续到它在代码中的 **最后一次使用 (last use)**。

```rust
let mut x = 5;      // B(x) = Unborrowed
let r1 = &x;        // B(x) -> Shared(1)
println!("{}", r1); // r1 的最后一次使用，其生命周期在此结束
                    // B(x) -> Unborrowed
let r2 = &mut x;     // 合法！因为 r1 的生命周期已结束
                    // B(x) -> Exclusive
*r2 += 1;
```

NLL 使得借用规则更加灵活和符合人体工程学，它允许在同一词法作用域内，只要引用的生命周期不重叠，就可以交替进行共享和独占借用。

## 5. 形式化证明：数据竞争自由

**定理**: 遵循 Rust 借用规则的程序在没有 `unsafe` 代码的情况下不会出现数据竞争。

**证明概要**:
数据竞争的定义是：在没有同步机制的情况下，两个或多个线程并发地访问同一内存位置，并且至少其中一个访问是写入操作。

1. **单线程内**:
    - 如果要进行写入，必须通过独占引用 `&mut T`。根据 **规则 3.2**，此时不可能存在任何其他引用（无论是读还是写）。
    - 如果要进行读取，可以通过共享引用 `&T`。根据 **规则 3.1**，此时可以有多个读取者，但绝不允许有写入者（独占引用）。
    - 因此，在单线程内，"读写冲突"和"写写冲突"在编译时就被排除了。

2. **多线程间**:
    - 要在线程间共享数据，必须使用实现了 `Sync` 和 `Send` trait 的类型（通常是 `Arc<Mutex<T>>` 或 `Arc<RwLock<T>>`）。
    - `Send` 保证类型可以被安全地转移到另一个线程。
    - `Sync` 保证类型可以被安全地通过引用（`&T`）在多个线程间共享。
    - 像 `Mutex` 和 `RwLock` 这样的同步原语，将借用规则从编译时强制执行转变为运行时（通过锁）强制执行，但依然保证了"Aliasing XOR Mutability"的核心原则，从而防止了跨线程的数据竞争。

因此，Rust 的借用机制从根本上杜绝了数据竞争的发生条件。

## 2.3.10 借用与生命周期

### 2.3.10.1 生命周期参数

生命周期参数是Rust类型系统的一部分，用于表示引用的有效期。

**形式化表示**：

设 $\alpha$ 是一个生命周期参数，则：

- $\text{Ref}_{\alpha}(T)$ 表示生命周期为 $\alpha$ 的不可变引用类型，即 `&'a T`
- $\text{MutRef}_{\alpha}(T)$ 表示生命周期为 $\alpha$ 的可变引用类型，即 `&'a mut T`

### 2.3.10.2 生命周期子类型关系

生命周期之间存在子类型关系，表示一个生命周期包含另一个生命周期。

**形式化表示**：

设 $\alpha$ 和 $\beta$ 是两个生命周期参数，如果 $\alpha$ 至少与 $\beta$ 一样长，则 $\alpha : \beta$（$\alpha$ 是 $\beta$ 的子类型）。

这导致了引用类型之间的子类型关系：

$$\frac{\alpha : \beta}{\text{Ref}_{\alpha}(T) : \text{Ref}_{\beta}(T)}$$

$$\frac{\alpha : \beta}{\text{MutRef}_{\alpha}(T) : \text{MutRef}_{\beta}(T)}$$

## 2.3.11 总结

Rust的借用机制是所有权系统的关键扩展，它允许在不转移所有权的情况下临时访问值。本章从形式化的角度详细阐述了借用机制，包括其数学基础、形式化定义以及安全性保证。借用机制与所有权系统共同构成了Rust内存安全和线程安全的基础，使得Rust能够在不依赖垃圾回收的情况下提供强大的安全保证。

## 2.3.12 参考文献

1. Klabnik, S., & Nichols, C. (2019). The Rust Programming Language.
2. Matsakis, N. D., & Klock, F. S. (2014). The Rust Language. Ada Letters, 34(3), 103-104.
3. Jung, R., Jourdan, J. H., Krebbers, R., & Dreyer, D. (2018). RustBelt: Securing the Foundations of the Rust Programming Language.
4. Weiss, A., Patterson, D., Ahmed, A., Appel, A. W., & Morrisett, G. (2019). Reference Mutability for Safe Parallelism.
5. Matsakis, N. D. (2018). Non-lexical lifetimes: Introduction. Rust Blog.
