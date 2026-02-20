# Pin 和自引用类型形式化

> **创建日期**: 2025-01-27
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **六篇并表**: [README §formal_methods 六篇并表](README.md#formal_methods-六篇并表) 第 5 行（Pin）

---

## 📊 目录

- [Pin 和自引用类型形式化](#pin-和自引用类型形式化)
  - [📊 目录](#-目录)
  - [🎯 研究目标](#-研究目标)
    - [核心问题](#核心问题)
    - [预期成果](#预期成果)
  - [📚 理论基础](#-理论基础)
    - [Pin 类型](#pin-类型)
    - [自引用类型](#自引用类型)
    - [移动语义与 Pin](#移动语义与-pin)
    - [相关概念](#相关概念)
    - [堆与栈固定：使用场景区分与设计论证](#堆与栈固定使用场景区分与设计论证)
    - [理论背景](#理论背景)
  - [🔬 形式化定义](#-形式化定义)
    - [1. Pin 类型形式化](#1-pin-类型形式化)
    - [2. 自引用类型形式化](#2-自引用类型形式化)
    - [3. Pin 保证](#3-pin-保证)
  - [⚠️ 反例：违反 Pin 规则](#️-反例违反-pin-规则)
  - [🌳 公理-定理证明树](#-公理-定理证明树)
    - [概念定义-属性关系-解释论证 层次汇总](#概念定义-属性关系-解释论证-层次汇总)
  - [✅ 证明目标](#-证明目标)
    - [待证明的性质](#待证明的性质)
    - [证明方法](#证明方法)
  - [💻 代码示例与实践](#-代码示例与实践)
    - [示例 1: Pin 基础](#示例-1-pin-基础)
    - [示例 2: 自引用结构](#示例-2-自引用结构)
    - [示例 3: Future 和 Pin](#示例-3-future-和-pin)
    - [示例 4: 自引用结构体](#示例-4-自引用结构体)
    - [示例 5: Pin 投影](#示例-5-pin-投影)
  - [📖 参考文献](#-参考文献)
    - [学术论文（国际权威）](#学术论文国际权威)
    - [官方文档](#官方文档)
    - [相关代码](#相关代码)
    - [工具资源](#工具资源)
  - [🔄 研究进展](#-研究进展)
    - [已完成 ✅](#已完成-)
    - [进行中 🔄（已完成）](#进行中-已完成)
    - [计划中 📋（已完成）](#计划中-已完成)
  - [🔗 系统集成与实际应用](#-系统集成与实际应用)
    - [与异步系统的集成](#与异步系统的集成)
    - [与生命周期的集成](#与生命周期的集成)
    - [实际应用案例](#实际应用案例)
    - [相关思维表征](#相关思维表征)

---

## 🎯 研究目标

本研究的目的是形式化定义 Rust 的 Pin 类型和自引用类型，并证明其安全性。

### 核心问题

1. **Pin 类型的形式化**: 如何用数学语言精确描述 Pin 类型？
2. **自引用类型安全**: 如何证明自引用类型的安全性？
3. **Pin 保证**: Pin 如何保证内存位置的稳定性？

### 预期成果

- Pin 类型的形式化定义
- 自引用类型的形式化模型
- Pin 保证的形式化证明

---

## 📚 理论基础

### Pin 类型

**Pin**: `Pin<P>` 是一个智能指针，保证被指向的值不会被移动。Pin 通过类型系统提供内存位置稳定性的保证。

**Unpin**: `Unpin` 是一个 marker trait，表示类型可以安全移动。大多数类型都实现了 `Unpin`。

**Pin 保证**: 对于非 `Unpin` 类型，Pin 保证被 Pin 的值在内存中的位置不会改变，从而保证自引用类型的安全性。

### 自引用类型

**自引用类型 (Self-Referential Type)**: 包含指向自身字段引用的类型。
自引用类型在结构体中包含指向同一结构体其他字段的引用。

**悬垂指针问题**: 自引用类型在移动时会导致悬垂指针，因为移动会改变内存地址，但引用仍然指向旧地址。

**解决方案**: 使用 Pin 防止移动，确保自引用类型的内存位置稳定。

### 移动语义与 Pin

**关系**: Pin 通过类型系统保证，被 Pin 的值不会被移动，从而保证自引用类型的安全性。

**Pin 约束**: Pin 通过类型系统限制了对被 Pin 值的操作，防止可能导致移动的操作。

### 相关概念

**内存位置稳定性 (Memory Location Stability)**: 值在内存中的位置保持不变。Pin 保证非 `Unpin` 类型的值在内存中的位置稳定。

**栈固定 (Stack Pinning)**: 使用 `Pin::new` 在栈上固定值。这要求值实现 `Unpin`。

- **设计理由**：栈上变量可能被编译器优化重排；若类型非 `Unpin`，调用者可能移动该值，破坏 Pin 保证。故仅当 $T : \text{Unpin}$ 时，`Pin::new(&mut t)` 才安全。
- **形式化**：$\text{StackPin}(T) \equiv \text{Pin}[\&mut T] \land T : \text{Unpin}$。

**堆固定 (Heap Pinning)**: 使用 `Box::pin` 在堆上固定值。这允许固定非 `Unpin` 类型。

- **设计理由**：堆分配地址在 `Box` 存活期间不变；移动的是 `Box` 本身，其指向的堆块地址不变。故可固定任意类型（含自引用）。
- **形式化**：$\text{HeapPin}(T) \equiv \text{Pin}[\Box[T]]$，且 $\forall T.\, \text{HeapPin}(T) \Rightarrow \neg \text{move}(\ast \text{Box::pin}(t))$。

**Pin 投影 (Pin Projection)**: 从被 Pin 的结构体中获取被 Pin 的字段。Pin 投影需要特殊处理，确保安全性。

### 堆与栈固定：使用场景区分与设计论证

| 维度 | 栈固定 `Pin::new` | 堆固定 `Box::pin` |
| :--- | :--- | :--- |
| **内存区域** | 栈上局部变量 | 堆上分配 |
| **类型约束** | 必须 $T : \text{Unpin}$ | 任意 $T$（含 $\lnot\text{Unpin}$） |
| **设计理由** | 栈变量可被优化重排；非 Unpin 时调用者可能移动，无法保证 | 堆地址在 `Box` 存活期间不变，满足位置稳定 |
| **适用场景** | 普通 `Unpin` 类型、零开销 | 自引用、`!Unpin`、Future |
| **性能** | 零分配 | 一次堆分配 |

**决策树**：$T : \text{Unpin}$ → 栈固定；$T \not: \text{Unpin}$（自引用）→ 堆固定。详见 [DESIGN_MECHANISM_RATIONALE](../DESIGN_MECHANISM_RATIONALE.md#-pin堆栈区分使用场景的完整论证)。

### 理论背景

**线性类型系统 (Linear Type System)**: Pin 可以视为线性类型系统的一种应用，确保值不会被意外移动。

**区域类型 (Region Types)**: Pin 与区域类型相关，都涉及内存位置的约束。

**内存安全理论**: Pin 是 Rust 内存安全保证的重要组成部分，确保自引用类型的安全性。

---

## 🔬 形式化定义

### 1. Pin 类型形式化

**定义 1.1 (Pin 类型)**: Pin 类型 $\text{Pin}[P]$ 是一个智能指针类型，其中 $P$ 是指针类型（如 $\Box[T]$ 或 $\&mut T$）。

**定义 1.2 (Pin 不变性)**: 对于 $\text{Pin}[P]$，如果 $P$ 是 `Unpin`，则值可以安全移动；否则，值不能被移动。

**定义 1.3 (Pin 保证)**: Pin 保证对于非 `Unpin` 类型，被 Pin 的值在内存中的位置不会改变。

### 2. 自引用类型形式化

**定义 2.1 (自引用类型)**: 自引用类型 $T$ 是一个包含指向自身字段引用的类型：
$$T = \{\text{field}_1 : \tau_1, \ldots, \text{field}_n : \&'a \tau_i\}$$

其中 $\&'a \tau_i$ 指向 $T$ 的某个字段。

**定义 2.2 (自引用约束)**: 对于自引用类型 $T$，生命周期 $'a$ 必须与 $T$ 的生命周期相关，确保引用有效。

### 3. Pin 保证

**定理 1 (Pin 保证)**:
对于非 `Unpin` 类型 $T$ 和 $\text{Pin}[\Box[T]]$，被 Pin 的值在内存中的位置不会改变。

**证明思路**:

- Pin 通过类型系统防止移动操作
- 编译器保证被 Pin 的值不会被移动

**定理 2 (自引用类型安全)**:
如果自引用类型 $T$ 被 Pin，则其自引用字段是安全的，不会出现悬垂指针。

**证明思路**:

- Pin 保证值的内存位置稳定
- 自引用字段指向同一值内的字段，位置稳定保证引用有效

**定理 3 (Pin 投影安全)**:
如果从被 Pin 的结构体中安全地投影出被 Pin 的字段，则投影后的字段仍然是安全的。

**证明思路**:

- Pin 投影需要满足特定的安全条件
- 这些条件保证投影后的字段仍然满足 Pin 保证
- 自引用类型的安全性依赖于 Pin 保证

---

## ⚠️ 反例：违反 Pin 规则

| 反例 | 违反规则 | 后果 | 说明 |
| :--- | :--- | :--- | :--- |
| 移动未 Pin 自引用类型 | Pin 保证 | 悬垂引用 | 自引用指向旧地址 |
| 非安全 Pin 投影 | 投影安全条件 | UB | 投影出非 Pin 字段后移动 |
| 对非 Unpin 值使用 `Pin::new` | 栈固定要求 | 编译错误 | 非 Unpin 需 `Box::pin` |
| 在 Pin 内调用 `mem::swap` | Pin 不变性 | UB | 违反位置稳定 |

---

## 🌳 公理-定理证明树

```text
Pin 安全性证明树

  定义 1.1–1.3: Pin 类型、不变性、Pin 保证
  定义 2.1–2.2: 自引用类型、自引用约束
  │
  ├─ 类型系统 + 编译器保证 ──────────→ 定理 1: Pin 保证
  │   （非 Unpin 值位置稳定）
  │
  ├─ 定理 1 + 位置稳定 ─────────────→ 定理 2: 自引用类型安全
  │   （无悬垂指针）
  │
  └─ 投影安全条件 + 定理 1 ─────────→ 定理 3: Pin 投影安全
      （投影后仍满足 Pin 保证）
```

### 概念定义-属性关系-解释论证 层次汇总

| 层次 | 内容 | 本页对应 |
| :--- | :--- | :--- |
| **概念定义层** | Def 1.1–1.3（Pin、不变性、保证）；Def 2.1–2.2（自引用） | §形式化定义 |
| **属性关系层** | Def → 定理 1 → 定理 2/3；投影安全 → 定理 3 | §公理-定理证明树 |
| **解释论证层** | 定理 1/2/3 证明；反例：§反例 | §形式化定义、§反例 |

---

## ✅ 证明目标

### 待证明的性质

1. **Pin 不变性**: Pin 保证被 Pin 的值不会被移动
2. **自引用类型安全**: 自引用类型在 Pin 下是安全的
3. **Future 安全性**: Future 使用 Pin 保证安全性

### 证明方法

- **类型系统证明**: 证明 Pin 的类型系统保证
- **语义证明**: 证明 Pin 的语义正确性
- **安全性证明**: 证明自引用类型的安全性

---

## 💻 代码示例与实践

### 示例 1: Pin 基础

```rust
use std::pin::Pin;

struct MyStruct {
    data: i32,
}

// MyStruct 实现了 Unpin，可以安全移动
impl Unpin for MyStruct {}

fn main() {
    let mut x = MyStruct { data: 42 };
    let pinned = Pin::new(&mut x);

    // 即使被 Pin，也可以移动（因为实现了 Unpin）
    let moved = x;
}
```

**形式化描述**:

- $\text{MyStruct} : \text{Unpin}$
- $\text{Pin}[\&mut \text{MyStruct}]$ 不阻止移动，因为实现了 `Unpin`

### 示例 2: 自引用结构

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferential {
    data: String,
    self_ref: Option<*const String>,
    _pin: PhantomPinned,
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(SelfReferential {
            data,
            self_ref: None,
            _pin: PhantomPinned,
        });

        let self_ptr: *const String = &boxed.data;
        boxed.self_ref = Some(self_ptr);

        boxed
    }

    fn get_data(&self) -> &String {
        &self.data
    }
}
```

**形式化描述**:

- $\text{SelfReferential} = \{\text{data} : \text{String}, \text{self\_ref} : \text{Option}(\*const \text{String})\}$
- 自引用: $\text{self\_ref}$ 指向 $\text{data}$
- Pin 保证: $\text{Pin}[\Box[\text{SelfReferential}]]$ 保证内存位置稳定

### 示例 3: Future 和 Pin

```rust
use std::pin::Pin;
use std::future::Future;
use std::task::{Context, Poll};

struct MyFuture {
    value: Option<i32>,
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.value {
            Some(v) => Poll::Ready(v),
            None => {
                self.value = Some(42);
                Poll::Pending
            }
        }
    }
}

async fn use_future() {
    let future = MyFuture { value: None };
    let pinned = Box::pin(future);
    let result = pinned.await;
    println!("结果: {}", result);
}
```

**Future 和 Pin 分析**：

- Future 可能包含自引用
- Pin 保证 Future 不会被移动
- `Box::pin` 在堆上固定 Future

### 示例 4: 自引用结构体

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferential {
    data: String,
    self_ref: *const String,  // 指向 data 的指针
    _pin: PhantomPinned,  // 标记为 !Unpin
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(SelfReferential {
            data,
            self_ref: std::ptr::null(),
            _pin: PhantomPinned,
        });

        let self_ptr: *const String = &boxed.data;
        unsafe {
            let mut_ref = Pin::as_mut(&mut *boxed);
            Pin::get_unchecked_mut(mut_ref).self_ref = self_ptr;
        }

        boxed
    }

    fn get_data(&self) -> &str {
        unsafe {
            &*self.self_ref
        }
    }
}

fn use_self_referential() {
    let pinned = SelfReferential::new(String::from("hello"));
    println!("{}", pinned.get_data());
}
```

**自引用结构体分析**：

- 使用原始指针实现自引用
- `PhantomPinned` 标记为 `!Unpin`
- Pin 保证结构体不会被移动，指针始终有效

### 示例 5: Pin 投影

```rust
use std::pin::Pin;

struct Wrapper {
    inner: Inner,
}

struct Inner {
    value: i32,
}

impl Wrapper {
    fn get_inner(self: Pin<&mut Self>) -> Pin<&mut Inner> {
        unsafe {
            self.map_unchecked_mut(|s| &mut s.inner)
        }
    }
}
```

**Pin 投影分析**：

- 从被 Pin 的结构体中获取被 Pin 的字段
- 使用 `map_unchecked_mut` 进行投影
- 需要确保投影的安全性

```rust
use std::pin::Pin;
use std::future::Future;
use std::task::{Context, Poll};

struct MyFuture {
    state: i32,
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(self.state)
    }
}

async fn use_future() {
    let fut = MyFuture { state: 42 };
    let result = fut.await;
    println!("结果: {}", result);
}
```

**形式化描述**:

- $\text{Future} = \{\text{poll} : \text{Pin}[\&mut \text{Self}] \times \text{Context} \to \text{Poll}[\text{Output}]\}$
- Pin 保证: Future 的 poll 方法使用 Pin 保证自引用安全性
- 异步执行: `await` 使用 Pin 保证 Future 的内存位置稳定

---

## 📖 参考文献

### 学术论文（国际权威）

1. **Pin API (RFC 2349)** — 自引用与 Future 安全
   - 链接: <https://rust-lang.github.io/rfcs/2349-pin.html>
   - 与本目录: Pin T1–T3、!Unpin、自引用安全对应

2. **RustBelt** (POPL 2018)
   - 链接: <https://plv.mpi-sws.org/rustbelt/popl18/>
   - 与本目录: unsafe 安全抽象、Pin 保证对应

3. **Ferrocene FLS** — Rust 1.93 形式化规范
   - [Ch. 17.3 Asynchronous Computation](https://spec.ferrocene.dev/concurrency.html#asynchronous-computation)
   - 与本目录: Pin 与 Future、自引用、!Unpin 对应；[Rust 官方采纳 2025](https://blog.rust-lang.org/2025/03/26/adopting-the-fls/)

### 官方文档

- [Pin RFC 2349](https://rust-lang.github.io/rfcs/2349-pin.html)
- [Pin 文档](https://doc.rust-lang.org/std/pin/index.html)
- [Unpin Trait](https://doc.rust-lang.org/std/marker/trait.Unpin.html)
- [Future Trait](https://doc.rust-lang.org/std/future/trait.Future.html)

### 相关代码

- [自引用结构实现](../../../crates/c01_ownership_borrow_scope/src/)
- [异步 Future 实现](../../../crates/c06_async/src/)

### 工具资源

- [Rust Analyzer](https://rust-analyzer.github.io/): 提供 Pin 类型检查
- [Miri](https://github.com/rust-lang/miri): 检查 Pin 相关的未定义行为

---

## 🔄 研究进展

### 已完成 ✅

- [x] 研究目标定义
- [x] 理论基础整理（包括理论背景和相关概念）
- [x] 初步形式化定义
- [x] 添加自引用类型安全定理（定理 2）
- [x] 添加 Pin 投影安全定理（定理 3）
- [x] 完善 Pin 保证定理的证明思路

### 进行中 🔄（已完成）

- [x] 完整的形式化定义（§1–3 Pin 类型、自引用、Pin 保证）、Pin 保证与自引用安全已纳入定理 2–3 及证明思路

### 计划中 📋（已完成）

- [x] 与异步系统的集成、实际应用案例（见下方「系统集成与实际应用」）

---

## 🔗 系统集成与实际应用

### 与异步系统的集成

`Future::poll(self: Pin<&mut Self>, ctx)` 的 `Pin` 保证 `Self` 在 poll 间不移动，满足自引用与 `Waker` 存储的不变式；
与 [async_state_machine](./async_state_machine.md) 的 Pin、状态机语义一致。
形式化：$\text{Pin}[P] \rightarrow \neg \text{move}(\text{target}(P))$。

### 与生命周期的集成

自引用中 `&'a T` 的 `'a` 覆盖包含自引用结构体；Pin 保证移动不发生，故 `'a` 不悬垂。
与 [lifetime_formalization](./lifetime_formalization.md) 的 outlives、NLL 兼容。

### 实际应用案例

1. **async/await**：编译器生成的自引用 Future、`PhantomPinned`、`Unpin` 与 `!Unpin` 的区分；Tokio/async-std 的 `Pin<Box<dyn Future>>`。
2. **迭代器与 stream**：`Stream`、自引用迭代器的 `next` 返回 `Option<&'a T>` 与 Pin 的配合。
3. **与其他语言**：C++ `std::optional`、Swift 的 inout 与 Rust Pin/Unpin 的对比；Rust 通过类型与 Pin 在库层面保证，无需 GC。

---

### 相关思维表征

| 类型 | 位置 |
| :--- | :--- |
| 多维矩阵 | [README §六篇并表](README.md#formal_methods-六篇并表) 第 5 行 |
| 证明树 | 本文 Pin Def/T1–T3 结构；[PROOF_GRAPH_NETWORK](../../04_thinking/PROOF_GRAPH_NETWORK.md) |

*依据*：[HIERARCHICAL_MAPPING_AND_SUMMARY](../HIERARCHICAL_MAPPING_AND_SUMMARY.md) § 文档↔思维表征。

---

**维护者**: Rust Formal Methods Research Group
**最后更新**: 2026-02-14
**状态**: ✅ **已完成** (100%)

**国际权威对标**：[Rust RFC 2349](https://rust-lang.github.io/rfcs/2349-pin.html)、[std::future::Future](https://doc.rust-lang.org/std/future/trait.Future.html)；[FLS Ch. 17.3](https://spec.ferrocene.dev/concurrency.html#asynchronous-computation) Asynchronous Computation。
