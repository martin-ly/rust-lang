# Return Type Notation（RTN）预研：为 AFIT/RPITIT 返回类型添加边界

> **代码状态**: ✅ 含 nightly 可编译示例
>
> **EN**: Return Type Notation Preview
> **Summary**: Preview of Return Type Notation (RTN), a mechanism to add bounds to the return types of `async fn` in traits (AFIT) and return-position `impl Trait` in traits (RPITIT).
>
> **状态**: 🧪 Nightly 实验性
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **Feature gate**: `#![feature(return_type_notation)]`
> **跟踪版本**: nightly 1.98.0
> **预计稳定**: 待定（2026 项目目标 [Prepare TAIT + RTN for stabilization](https://rust-lang.github.io/rust-project-goals/2026/rtn.html) 推进中；完整稳定化受下一代 trait solver 工作阻塞，目标今年晚些时候）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×Ana — 分析返回类型标注预览特性
> **定位**: 澄清 **Return Type Notation (RTN)** 与 **`use<..>` 精确捕获**是两个不同的特性；RTN 解决的是「如何为 trait 中 `async fn` / RPITIT 的返回类型添加 `Send` 等边界」的问题。
> **前置概念**: [Lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) · [Async](../../03_advanced/01_async/02_async.md) · [Traits](../../02_intermediate/00_traits/01_traits.md) · [Async Closures](../../03_advanced/01_async/24_async_closures.md)
> **后置概念**: [Version Tracking](../00_version_tracking/05_rust_version_tracking.md) · [Async Drop Preview](18_async_drop_preview.md)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>
---

> **来源**:
>
> · [TRPL](https://doc.rust-lang.org/book/title-page.html) ·
> [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) ·
> [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) ·
> [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> [RFC 3654 — Return Type Notation](https://rust-lang.github.io/rfcs/3654-return-type-notation.html) ·
> [Tracking Issue #109417](https://github.com/rust-lang/rust/issues/109417) ·
> [Rust Project Goals 2026 — Prepare TAIT + RTN for stabilization](https://rust-lang.github.io/rust-project-goals/2026/rtn.html) ·
> [Async Working Group](https://rust-lang.github.io/async-fundamentals-initiative/) ·
> [Rust Reference — Impl Trait](https://doc.rust-lang.org/reference/types/impl-trait.html)
> **前置依赖**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> **前置依赖**: [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md)

---

## 📑 目录

- [Return Type Notation（RTN）预研：为 AFIT/RPITIT 返回类型添加边界](#return-type-notationrtn预研为-afitrpitit-返回类型添加边界)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 问题：AFIT/RPITIT 的返回类型无法命名](#11-问题afitrpitit-的返回类型无法命名)
    - [1.2 RTN 语法：`T::method(..): Send`](#12-rtn-语法tmethod-send)
    - [1.3 RTN 与 `use<..>` 精确捕获的区别](#13-rtn-与-use-精确捕获的区别)
  - [二、技术细节](#二技术细节)
    - [2.1 语法形式与语义](#21-语法形式与语义)
    - [2.2 当前限制](#22-当前限制)
    - [2.3 与 async closures 的关联](#23-与-async-closures-的关联)
  - [三、使用模式](#三使用模式)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、演进路线](#五演进路线)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念文件](#相关概念文件)
  - [权威来源索引](#权威来源索引)
  - [十、边界测试：Return Type Notation 预览的编译错误](#十边界测试return-type-notation-预览的编译错误)
    - [10.1 边界测试：RTN 在类型位置使用（编译错误）](#101-边界测试rtn-在类型位置使用编译错误)
    - [10.2 边界测试：RTN 用于非 AFIT/RPITIT 方法（编译错误）](#102-边界测试rtn-用于非-afitrpitit-方法编译错误)
    - [10.3 边界测试：RTN 与 const/type 泛型方法（编译错误）](#103-边界测试rtn-与-consttype-泛型方法编译错误)
    - [10.4 边界测试：RTN 与缺少 `feature(return_type_notation)`（编译错误）](#104-边界测试rtn-与缺少-featurereturn_type_notation编译错误)
    - [补充定理链](#补充定理链)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：Return Type Notation（RTN）解决的是什么问题？（理解层）](#测验-1return-type-notationrtn解决的是什么问题理解层)
    - [测验 2：RTN 的语法 `T::method(..): Send` 中 `..` 表示什么？（理解层）](#测验-2rtn-的语法-tmethod-send-中--表示什么理解层)
    - [测验 3：RTN 与 `use<..>` 精确捕获有什么区别？（理解层）](#测验-3rtn-与-use-精确捕获有什么区别理解层)
    - [测验 4：RTN 当前支持在哪些位置使用？（理解层）](#测验-4rtn-当前支持在哪些位置使用理解层)
    - [测验 5：这个特性对 API 设计有什么影响？（理解层）](#测验-5这个特性对-api-设计有什么影响理解层)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)

---

## 一、核心概念

### 1.1 问题：AFIT/RPITIT 的返回类型无法命名

Rust 1.75 稳定了 `async fn` in traits（AFIT）和 return-position `impl Trait` in traits（RPITIT）。它们把返回类型隐藏为不透明类型：

```rust
#![feature(return_type_notation)]

trait HealthCheck {
    async fn check(&mut self) -> bool;
}
```

调用者想把这个返回的 `Future` 传给 `tokio::spawn` 时，需要 `Send + 'static` 边界。但返回类型没有名字，传统写法 `T::CheckFuture: Send` 不适用。

> **核心痛点**
>
> 1. **返回类型匿名**：AFIT/RPITIT 的返回类型由编译器生成，没有显式关联类型名。
> 2. **无法加边界**：`where T::check: Send` 在稳定 Rust 中不合法。
> 3. **Send 边界传播困难**：库作者被迫在 trait 定义里提前加 `+ Send`，限制实现者自由。

[来源: [RFC 3654 — Return Type Notation](https://rust-lang.github.io/rfcs/3654-return-type-notation.html)]

---

### 1.2 RTN 语法：`T::method(..): Send`

Return Type Notation（RTN）提供了一种引用（Reference） trait 方法返回类型并为其添加边界的方式：

```rust
#![feature(return_type_notation)]

use std::future::Future;

trait HealthCheck {
    async fn check(&mut self) -> bool;
}

// 调用者：要求 HealthCheck::check 返回的 Future 是 Send + 'static
fn spawn_check<T: HealthCheck>(mut hc: T)
where
    T::check(..): Send + 'static,
{
    tokio::spawn(async move { hc.check().await });
}
```

`T::check(..)` 表示「调用 `T::check` 返回的类型」。`..` 占位符表示方法的泛型（Generics）参数由编译器推导。

等价的关联类型 bound 写法：

```rust
fn spawn_check<T: HealthCheck<check(..): Send + 'static>>(mut hc: T) {
    tokio::spawn(async move { hc.check().await });
}
```

[来源: [Inside Rust Blog — Return type notation MVP: Call for testing!](https://blog.rust-lang.org/inside-rust/2024/09/26/rtn-call-for-testing.html)]

---

### 1.3 RTN 与 `use<..>` 精确捕获的区别

| 特性 | Return Type Notation (RTN) | Precise Capturing (`use<..>`) |
|:---|:---|:---|
| **解决什么问题** | 为 AFIT/RPITIT 的返回类型添加 `Send` 等边界 | 控制 `impl Trait` / `async fn` 不透明类型捕获哪些泛型（Generics）参数 |
| **语法示例** | `T::method(..): Send` | `fn f(x: &str) -> impl Trait + use<>` |
| **RFC** | [RFC 3654](https://rust-lang.github.io/rfcs/3654-return-type-notation.html) | [RFC 3617](https://rust-lang.github.io/rfcs/3617-precise-capturing.html) |
| **稳定状态** | Nightly 实验性 | **Stable**（Rust 1.82.0+） |
| **Feature gate** | `#![feature(return_type_notation)]` | 无需 feature gate |
| **常见误用** | 与 `use<..>` 混淆，以为 RTN 是“精确捕获” | 在不需要时显式写 `use<..>` |

> **关键区分**: `use<..>` 告诉编译器「我的不透明类型捕获/不捕获哪些参数」；RTN 告诉编译器「调用这个 trait 方法返回的类型需要满足什么边界」。两者互补，但不是同一回事。

[来源: [RFC 3617 — Precise Capturing](https://rust-lang.github.io/rfcs/3617-precise-capturing.html)]

---

## 二、技术细节

### 2.1 语法形式与语义

RTN 引入了一种新的类型写法 `<T as Trait>::method(..)`，简写为 `T::method(..)`：

```rust
#![feature(return_type_notation)]

trait Factory {
    fn make(&self) -> impl Iterator<Item = u32>;
}

// 形式 1：where 子句中作为 Self 类型
fn use_factory<T: Factory>()
where
    T::make(..): DoubleEndedIterator,
{
    // ...
}

// 形式 2：关联类型 bound 写法
fn use_factory2<T: Factory<make(..): DoubleEndedIterator>>() {
    // ...
}
```

语义规则：

- `..` 表示方法的所有泛型（Generics）参数由调用处推导；目前仅支持生命周期（Lifetimes）泛型。
- RTN 类型只能出现在 bound/where 子句的 `Self` 位置；不能作为普通类型使用（如结构体（Struct）字段）。

[来源: [RFC 3654 — Return Type Notation](https://rust-lang.github.io/rfcs/3654-return-type-notation.html)]

---

### 2.2 当前限制

截至 nightly 1.98.0：

1. **仅支持 AFIT 和 RPITIT**：方法必须是 `async fn` 或返回 `-> impl Trait`。
2. **仅支持生命周期（Lifetimes）泛型**：方法可以有生命周期参数，但不能有 const 或 type 泛型（Generics）。
3. **仅能在 bound/where 子句中使用**：不能写成 `let x: T::method(..)` 或结构体（Struct）字段类型。
4. **需要 feature gate**：必须在 crate 根启用 `#![feature(return_type_notation)]`。

```rust
#![feature(return_type_notation)]

trait Bad {
    fn plain(&self) -> i32; // 不是 AFIT/RPITIT
}

// ❌ 编译错误：RTN 不支持普通返回类型
fn bad<T: Bad>()
where
    T::plain(..): Send,
{}
```

[来源: [Tracking Issue #109417](https://github.com/rust-lang/rust/issues/109417)]

---

### 2.3 与 async closures 的关联

Async closures（Rust 1.85.0 stable）稳定后，社区希望 RTN 也能用于 async closure 类型，以便在泛型（Generics）约束中表达「async closure 返回的 Future 是 Send」。相关设计仍在 RFC 阶段，是 2026 年「Prepare TAIT + RTN for stabilization」项目目标的一部分。

[来源: [Rust Project Goals 2026 — RTN](https://rust-lang.github.io/rust-project-goals/2026/rtn.html)]

---

## 三、使用模式

```rust
#![feature(return_type_notation)]

use std::future::Future;

trait Service {
    async fn call(&self, request: Vec<u8>) -> Vec<u8>;
}

// 模式 1：在 where 子句中为 AFIT 返回类型加 Send bound
fn spawn_service<T: Service>(svc: T, req: Vec<u8>)
where
    T::call(..): Send + 'static,
{
    tokio::spawn(async move { svc.call(req).await });
}

// 模式 2：在 trait alias / 组合 trait 中复用
trait SendService: Service<call(..): Send + 'static> {}
impl<T: Service<call(..): Send + 'static>> SendService for T {}
```

> **最佳实践**: 在 public async trait 中不要提前加 `+ Send`；让调用者通过 RTN 按需约束。这样 `SingleThreaded` 实现和 `Send` 实现可以共存。

[来源: [RFC 3654 — Return Type Notation](https://rust-lang.github.io/rfcs/3654-return-type-notation.html)]

---

## 四、反命题与边界分析

### 4.1 反命题树

```text
命题: "AFIT/RPITIT 返回类型不能加边界"
└── ❌ 错误 — RTN 提供了 T::method(..) 语法

命题: "RTN 已经稳定"
└── ❌ 错误 — 仍在 nightly，feature gate return_type_notation

命题: "RTN 和 use<..> 是同一个特性"
└── ❌ 错误 — RTN 加 bound，use<..> 控制捕获集合

命题: "public async trait 应该预先把返回 Future 约束为 Send"
└── ⚠️ 不推荐 — 应通过 RTN 让调用者按需约束，保持实现灵活性
```

---

### 4.2 边界极限

| 边界 | 说明 |
|:---|:---|
| 不能用于普通方法 | 仅 AFIT / RPITIT 支持 RTN |
| 不能用于 type/const 泛型方法 | 当前实现仅支持生命周期（Lifetimes）泛型 |
| 不能在类型位置使用 | 不能作为字段类型、局部变量类型 |
| 需要 nightly | 稳定版使用会报 `feature(return_type_notation)` 错误 |

---

## 五、演进路线

```text
2023-12: RFC 3654 合并
2024-09: Nightly MVP 发布，开始社区测试
2025-02: Rust 1.85 发布 Edition 2024（不含 RTN）
2026-05: Rust Project Goals 2026 将 "Prepare TAIT + RTN for stabilization" 列为目标
未来:    完成下一代 trait solver 集成后，TAIT + RTN 一起稳定
```

[来源: [Rust Project Goals 2026 — RTN](https://rust-lang.github.io/rust-project-goals/2026/rtn.html)]

---

## 六、来源与延伸阅读

- [RFC 3654 — Return Type Notation](https://rust-lang.github.io/rfcs/3654-return-type-notation.html)
- [Tracking Issue #109417](https://github.com/rust-lang/rust/issues/109417)
- [Inside Rust Blog — Return type notation MVP: Call for testing!](https://blog.rust-lang.org/inside-rust/2024/09/26/rtn-call-for-testing.html)
- [Rust Project Goals 2026 — Prepare TAIT + RTN for stabilization](https://rust-lang.github.io/rust-project-goals/2026/rtn.html)
- [RFC 3617 — Precise Capturing](https://rust-lang.github.io/rfcs/3617-precise-capturing.html)（区分 RTN 与 `use<..>`）

---

## 相关概念

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| Async Closures | [](../../03_advanced/01_async/24_async_closures.md) | RTN 未来可能扩展至 async closures |
| AFIT / RPITIT | [](../../03_advanced/01_async/02_async.md) | RTN 的主要应用场景 |
| Precise Capturing | [](../../02_intermediate/04_types_and_conversions/20_type_system_advanced.md) | 与 RTN 互补但不同 |
| Version Tracking | [](../00_version_tracking/05_rust_version_tracking.md) | 稳定化时间线 |

---

## 权威来源索引

- [RFC 3654](https://rust-lang.github.io/rfcs/3654-return-type-notation.html)
- [Tracking Issue #109417](https://github.com/rust-lang/rust/issues/109417)
- [Rust Project Goals 2026 / RTN](https://rust-lang.github.io/rust-project-goals/2026/rtn.html)
- [Inside Rust Blog — RTN Call for Testing](https://blog.rust-lang.org/inside-rust/2024/09/26/rtn-call-for-testing.html)

---

## 十、边界测试：Return Type Notation 预览的编译错误

### 10.1 边界测试：RTN 在类型位置使用（编译错误）

```rust,compile_fail
#![feature(return_type_notation)]

trait HealthCheck {
    async fn check(&mut self) -> bool;
}

struct Holder<T: HealthCheck> {
    // ❌ RTN 目前不能作为普通类型使用
    fut: T::check(..),
}
```

**错误信息**: `RTN types are not yet allowed in this position`

---

### 10.2 边界测试：RTN 用于非 AFIT/RPITIT 方法（编译错误）

```rust,compile_fail
#![feature(return_type_notation)]

trait Plain {
    fn value(&self) -> i32;
}

fn bad<T: Plain>()
where
    T::value(..): Send,
{}
```

**错误信息**: `return type notation is not allowed for methods that do not return impl Trait or async`

---

### 10.3 边界测试：RTN 与 const/type 泛型方法（编译错误）

```rust,compile_fail
#![feature(return_type_notation)]

trait Factory {
    fn make<T>(&self) -> impl Iterator<Item = T>;
}

fn bad<F: Factory>()
where
    F::make<T>(..): Send, // ❌ 当前不支持 type 泛型
{}
```

**错误信息**: `return type notation with generic type/const parameters is not yet supported`

---

### 10.4 边界测试：RTN 与缺少 `feature(return_type_notation)`（编译错误）

```rust,compile_fail
// ❌ 缺少 #![feature(return_type_notation)]

trait HealthCheck {
    async fn check(&mut self) -> bool;
}

fn bad<T: HealthCheck>()
where
    T::check(..): Send,
{}
```

**错误信息**: `return type notation is experimental (see issue #109417)`

---

### 补充定理链

> RTN 的存在性定理：若 trait 方法 `m` 返回一个不透明类型（AFIT/RPITIT），则存在一种语法 `T::m(..)` 可以在 where 子句中引用（Reference）该返回类型并添加边界。
> 限制定理：RTN 目前不支持非不透明返回类型、type/const 泛型方法以及类型位置。

---

## 嵌入式测验（Embedded Quiz）

### 测验 1：Return Type Notation（RTN）解决的是什么问题？（理解层）

<details>
<summary>点击展开答案</summary>

RTN 解决的是 AFIT/RPITIT 返回类型匿名、无法直接添加 `Send` 等边界的问题。通过 `T::method(..): Send` 语法，调用者可以在 where 子句中约束 trait 方法返回的不透明类型。

</details>

### 测验 2：RTN 的语法 `T::method(..): Send` 中 `..` 表示什么？（理解层）

<details>
<summary>点击展开答案</summary>

`..` 是占位符，表示方法的所有泛型参数（目前仅支持生命周期（Lifetimes））由编译器根据上下文推导。它不是一个具体的参数列表。

</details>

### 测验 3：RTN 与 `use<..>` 精确捕获有什么区别？（理解层）

<details>
<summary>点击展开答案</summary>

- RTN（`T::method(..): Send`）用于为 trait 方法的返回类型添加边界。
- `use<..>` 精确捕获用于控制 `impl Trait` / `async fn` 不透明类型捕获哪些泛型参数。
- RTN 仍在 nightly；`use<..>` 已在 Rust 1.82 stable。

</details>

### 测验 4：RTN 当前支持在哪些位置使用？（理解层）

<details>
<summary>点击展开答案</summary>

目前 RTN 只能作为 where 子句或关联类型 bound 中的 `Self` 类型使用。不能作为结构体（Struct）字段类型、局部变量类型或函数返回类型使用。

</details>

### 测验 5：这个特性对 API 设计有什么影响？（理解层）

<details>
<summary>点击展开答案</summary>

库作者不必在 trait 定义中提前把 `async fn` 返回的 Future 约束为 `Send`。调用者按需通过 RTN 添加约束，使得单线程实现和多线程实现可以共用同一 trait。

</details>

---

## 认知路径

### 核心推理链

`async fn in trait` 稳定 → 返回类型匿名 → 调用者无法加 `Send` bound → 需要 RTN → RTN 提供 `T::method(..): Send` 语法 → 调用者按需约束 → trait 实现保持灵活。

### 反命题与边界

- ❌ "RTN 已经稳定" — 仍在 nightly。
- ❌ "RTN 就是 `use<..>`" — 两者不同。
- ❌ "RTN 可以用于任何方法" — 仅 AFIT/RPITIT。
- ✅ "RTN 让 async trait 的 API 设计更灵活" — 正确。

---

> **文档版本**: 2.0
> **Rust 版本**: nightly 1.98.0
> **最后更新**: 2026-06-23
> **状态**: ✅ 权威来源对齐 — 区分 RTN 与 precise capturing
