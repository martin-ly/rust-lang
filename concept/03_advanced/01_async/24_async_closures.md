> **受众**: [专家]
> **内容分级**: [专家级]
>
# Async Closures（异步闭包）

> **EN**: Async Closures
> **Summary**: Stable Rust 1.85.0+ 引入的 `async || {}` 闭包（Closures）语法，`AsyncFn`/`AsyncFnMut`/`AsyncFnOnce` trait 家族已进入标准库 prelude。
>
> **特性状态**: ✅ **Stable since Rust 1.85.0**（2025-02-20）
> **所属 Edition**: Rust 2024 / 2021（语法可用，但 `AsyncFn*` 在 prelude 中的暴露随 2024 edition 默认生效）
> **权威来源**: · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [System F](https://en.wikipedia.org/wiki/System_F) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> - [RFC 3668 — Async Closures](https://rust-lang.github.io/rfcs/3668-async-closures.html)
> - [Rust Reference — Closure expressions / Async closures](https://doc.rust-lang.org/reference/expressions/closure-expr.html#async-closures)
> - [TRPL Ch17 — Asynchronous Programming](https://doc.rust-lang.org/book/ch17-00-async-await.html)
> - [Rust 1.85.0 Release Notes](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html)
>
> **Bloom 层级**: 应用 → 分析
> **权威来源**: 本文件为 `concept/` 权威页。
> **前置概念**: Closures、async/await、Future、Pin
> **后置概念**: RTN (Return Type Notation)、AFIDT、`dyn AsyncFn`

---

---

> **过渡**: 从 Async Closures（异步闭包） 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。
> **过渡**: 在建立 Async Closures（异步闭包） 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。
> **过渡**: 最后，将 Async Closures（异步闭包） 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **反向推理 1**: 如果程序在 Async Closures（异步闭包） 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 Async Closures（异步闭包） 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。

## 1. 为什么需要 async closures？

在 Rust 1.85 之前，表达“一个异步（Async）闭包（Closures）”通常写成：

```rust
// 旧写法：闭包返回一个 Future
fn make_callback() -> impl FnOnce() -> Pin<Box<dyn Future<Output = i32> + Send>> {
    || Box::pin(async move {
        tokio::time::sleep(Duration::from_secs(1)).await;
        42
    })
}
```

这种写法的问题：

1. **语法冗余**：闭包（Closures） + `async move` 块两层嵌套。
2. **捕获不精确**：`async move` 会强制把捕获变量 move 进 Future，无法像同步闭包（Closures）那样按使用自动推断借用（Borrowing）。
3. **类型表达困难**：返回 `impl Fn() -> impl Future` 在 trait bound、高阶回调中非常冗长。

Rust 1.85 引入 `async || {}` 语法后，上述代码可简化为：(Source: [Rust Reference — Async Closures](https://doc.rust-lang.org/reference/expressions/closure-expr.html#async-closures), [Rust 1.85.0 Release Notes](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html))

```rust
fn make_callback() -> impl AsyncFnOnce() -> i32 {
    async || {
        tokio::time::sleep(Duration::from_secs(1)).await;
        42
    }
}
```

> **关键洞察**：`async || {}` 不是“返回 Future 的闭包（Closures）”，而是**真正的异步（Async）闭包**——调用它返回一个 Future，且捕获语义与同步闭包一致。

---

## 2. 语法与捕获语义

### 2.1 基础语法

```rust
use std::time::Duration;

// 无参数
let f = async || {
    println!("hello");
    42
};

// 有参数、有返回类型标注
let add = async |a: i32, b: i32| -> i32 {
    tokio::time::sleep(Duration::from_millis(10)).await;
    a + b
};

// 调用：返回 Future，需要 await
let result = add(1, 2).await;
```

### 2.2 捕获模式

async closures 的捕获规则**与同步闭包一致**：编译器根据闭包体对捕获变量的使用方式，自动选择借用（Borrowing）或移动。

```rust
async fn capture_examples() {
    let data = vec![1, 2, 3];

    // 1. 引用捕获（默认）：data 被不可变借用
    let f = async || {
        println!("{:?}", data);
    };
    println!("{:?}", data); // ✅ data 仍可用
    f().await;

    // 2. 移动捕获：显式 move
    let data2 = vec![4, 5, 6];
    let g = async move || {
        println!("{:?}", data2);
    };
    // data2 不再可用
    g().await;

    // 3. 借用捕获允许在异步上下文中保持引用
    let s = String::from("hello");
    let h = async || {
        println!("{}", s); // s 被借用，而不是 move
    };
    h().await;
    println!("{}", s); // ✅ s 仍可用
}
```

> ⚠️ 注意：async closure 体本身是一个 async block，调用时才产生 Future。捕获发生在闭包（Closures）创建时，Future 内部再引用（Reference）这些捕获。

### 2.3 与 `|x| async move {}` 的对比

| 维度 | `\|x\| async move {}` | `async \|x\| {}` |
|---|---|---|
| 稳定版本 | 任何版本 | **Rust 1.85.0+** |
| 语法层级 | 闭包（Closures） + 内部 async 块 | 单一 async 闭包 |
| 捕获 | 强制 `move` | 自动推断（可 `move`） |
| 返回类型 | `impl Fn(...) -> impl Future` | `impl AsyncFn(...) -> T` |
| 借用（Borrowing）捕获 | ❌ 困难 | ✅ 原生支持 |
| dyn 兼容 | `Fn` trait 是 dyn-compatible | `AsyncFn` **当前不是** dyn-compatible |

### 2.4 异步可调用体谱系

除了 `async || {}`，Rust 还提供多种“异步（Async）可调用”形式，它们的捕获方式与返回类型各不相同：

| 形式 | 语法 | 捕获方式 | 返回类型 | 典型场景 |
|---|---|---|---|---|
| `async fn` | `async fn f() -> T` | 按值传参 | `impl Future<Output = T>` | 具名函数 |
| `async` 块 | `async { ... }` | 按引用（Reference）捕获环境 | `impl Future<Output = T>` | 局部异步（Async）逻辑 |
| `async move` 块 | `async move { ... }` | 按值 move 环境 | `impl Future<Output = T>`（可能 `'static`） | 转移所有权（Ownership） |
| `async` 闭包（Closures） | `async \|x\| { ... }` | 按引用（Reference）捕获（默认） | `impl AsyncFn(...) -> T` | 高阶异步（Async）函数参数 |
| `async move` 闭包（Closures） | `async move \|x\| { ... }` | 按值 move 捕获 | `impl AsyncFnOnce(...) -> T` | 单次 / 可 `spawn` |
| 普通闭包（Closures）返回 async 块 | `\|x\| async move { ... }` | 闭包按引用（Reference）捕获，async 块按值 move | `impl Fn(...) -> impl Future` | 旧生态 API |

> 💡 关键直觉：`async \|x\| {}` ≠ `\|x\| async move {}`。前者返回的 `Future` 可借用（Borrowing）闭包（Closures）自身，后者返回的 `Future` 拥有闭包捕获。

---

## 3. AsyncFn trait 家族

Rust 为标准库增加了三个新 trait：(Source: [std::ops::AsyncFn](https://doc.rust-lang.org/std/ops/trait.AsyncFn.html), [RFC 3668](https://rust-lang.github.io/rfcs/3668-async-closures.html))

- `AsyncFn(Args) -> Output`
- `AsyncFnMut(Args) -> Output`
- `AsyncFnOnce(Args) -> Output`

在 **Rust 2024 edition** 中，它们已加入 prelude，通常无需显式 `use`；在 2021 edition 中需要 `use std::ops::{AsyncFn, AsyncFnMut, AsyncFnOnce}`。

```rust
// Rust 2024 edition：无需 use
fn accept_async_callback<F>(f: F) -> impl Future<Output = i32>
where
    F: AsyncFn(i32) -> i32,
{
    async move { f(21).await }
}
```

### 3.1 trait 层级

```text
        AsyncFn<Args>
             │
             ▼
        AsyncFnMut<Args>
             │
             ▼
        AsyncFnOnce<Args>
```

- `AsyncFn`：可多次不可变调用（`&self`）。
- `AsyncFnMut`：可多次可变调用（`&mut self`）。
- `AsyncFnOnce`：可消费式调用一次（`self`）。

### 3.2 使用场景：高阶异步函数

```rust
async fn process_items<T, F>(items: Vec<T>, predicate: F) -> Vec<T>
where
    T: Clone,
    F: AsyncFn(&T) -> bool,
{
    let mut results = Vec::new();
    for item in &items {
        if predicate(item).await {
            results.push(item.clone());
        }
    }
    results
}

// 使用
let evens = process_items(vec![1, 2, 3, 4], async |x| *x % 2 == 0).await;
```

### 3.3 形式化 trait 草图

标准库中的实际定义更复杂，但核心形状可简化为：

```rust,ignore
use std::future::Future;

pub trait AsyncFn<Args>: AsyncFnMut<Args> {
    type Output;
    type CallRefFuture<'a>: Future<Output = Self::Output>
    where
        Self: 'a;

    fn async_call(&self, args: Args) -> Self::CallRefFuture<'_>;
}

pub trait AsyncFnMut<Args>: AsyncFnOnce<Args> {
    fn async_call_mut(&mut self, args: Args) -> Self::CallRefFuture<'_>;
}

pub trait AsyncFnOnce<Args> {
    type Output;
    type CallOnceFuture: Future<Output = Self::Output>;
    fn async_call_once(self, args: Args) -> Self::CallOnceFuture;
}
```

`CallRefFuture<'a>` 是泛型（Generics）关联类型（GAT），它允许返回的 `Future` 借用（Borrowing） `&self`。这正是 `AsyncFn` 与 `Fn` 的本质差异：同步 `Fn` 只能返回一个已经构造好的值，无法让返回值携带 `self` 的生命周期（Lifetimes）。

---

## 4. 实际应用模式

### 4.1 事件处理器

```rust
use tokio::sync::mpsc;

struct AsyncHandler<T> {
    handler: Box<dyn AsyncFn(T) + Send + Sync>,
}

// ❌ 当前不能这样写：AsyncFn 不是 dyn-compatible
// 应使用泛型或 impl trait
struct AsyncHandlerFixed<T, F> {
    handler: F,
    _phantom: std::marker::PhantomData<T>,
}

impl<T, F> AsyncHandlerFixed<T, F>
where
    F: AsyncFn(T) + Send + Sync,
{
    fn new(handler: F) -> Self {
        Self {
            handler,
            _phantom: std::marker::PhantomData,
        }
    }

    async fn handle(&self, event: T) {
        (self.handler)(event).await;
    }
}
```

### 4.2 中间件链

```rust
#[derive(Clone)]
struct Request {
    path: String,
    headers: Vec<(String, String)>,
}

#[derive(Clone)]
struct Response {
    status: u16,
    body: String,
}

type Next = Box<dyn Fn(Request) -> std::pin::Pin<Box<dyn std::future::Future<Output = Response> + Send>> + Send + Sync>;

async fn middleware_chain(
    req: Request,
    final_handler: impl AsyncFn(Request) -> Response + Send + Sync + Clone,
) -> Response {
    let next: Next = Box::new(move |req: Request| {
        let handler = final_handler.clone();
        Box::pin(async move { handler(req).await })
    });

    // 实际中间件会包装 next
    next(req).await
}
```

> 💡 设计提示：由于 `AsyncFn` 暂不支持 `dyn`，生产级中间件通常仍用泛型（Generics） `impl AsyncFn(...)` 或返回 `Pin<Box<dyn Future>>` 的传统闭包（Closures）。

### 4.3 并行处理：Tokio JoinSet

```rust,ignore
use tokio::task::JoinSet;

async fn parallel_map<F>(items: Vec<i32>, f: F) -> Vec<i32>
where
    F: AsyncFn(i32) -> i32 + Clone + Send + Sync + 'static,
{
    let mut set = JoinSet::new();

    for item in items {
        let f = f.clone();
        set.spawn(async move { f(item).await });
    }

    let mut results = Vec::new();
    while let Some(res) = set.join_next().await {
        results.push(res.unwrap());
    }
    results
}
```

每次 `f.clone()` 产生一个独立副本，从而满足 `tokio::spawn` 对 `'static` 的要求。

### 4.4 框架实战：Axum 处理函数

```rust,ignore
use axum::{routing::get, Router};
use std::time::Duration;

#[tokio::main]
async fn main() {
    let auth_checker = async |token: &str| -> bool {
        tokio::time::sleep(Duration::from_millis(5)).await;
        token == "valid-token"
    };

    let app = Router::new()
        .route("/", get(|| async { "Hello, World!" }));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

---

## 5. 限制与边界

### 5.1 不是 dyn-compatible

```rust,compile_fail
fn make_dyn() -> Box<dyn AsyncFn(i32) -> bool> {
    Box::new(async |x| x > 0)
}
```

原因：`AsyncFn` 包含关联类型 `CallRefFuture<'a>`，使其不符合 object-safe（dyn-compatible）条件。(Source: [Rust Reference — Object Safety](https://doc.rust-lang.org/reference/items/traits.html#object-safety))

**替代方案**：

```rust
fn make_dyn() -> Box<dyn Fn(i32) -> std::pin::Pin<Box<dyn std::future::Future<Output = bool> + Send>>> {
    Box::new(|x| Box::pin(async move { x > 0 }))
}
```

### 5.2 Send 约束与 RTN

如果需要在 trait bound 中表达“返回的 Future 是 `Send`”，目前需要 **Return Type Notation (RTN)**，该特性仍在 nightly / RFC 阶段：

```rust,ignore
// RTN 语法（ nightly，尚未 stable ）
F: AsyncFn(i32) -> bool + AsyncFn(i32) -> Send,
```

在 stable Rust 1.85–1.96 中，通常通过 `async move` + 闭包或泛型（Generics）边界间接保证 Send。

### 5.3 递归调用

```rust,compile_fail
let f = async || {
    f().await; // ❌ 递归类型可能无限展开
};
```

需要显式装箱（`Box::pin`）或改用 `async_recursion` 等 crate。

### 5.4 与 `tokio::spawn` 的生命周期冲突

`AsyncFn` 返回的 `Future` 可能借用（Borrowing）闭包自身或其捕获的环境，因此通常不是 `'static`，不能直接交给 `tokio::spawn`。

```rust,compile_fail
async fn bad_spawn() {
    let local = String::from("hello");

    let f = async |x: i32| {
        format!("{} {}", local, x) // 按引用捕获 local
    };

    tokio::spawn(async {
        let result = f(42).await; // ❌ Future 借用 local，不是 'static
        println!("{}", result);
    });
}
```

**修复**：使用 `async move ||` 转移所有权（Ownership），或用 `Arc` 共享 `'static` 数据。

```rust,ignore
async fn good_spawn() {
    let local = String::from("hello");

    let f = async move |x: i32| { // move 捕获 local
        format!("{} {}", local, x)
    };

    tokio::spawn(async {
        let result = f(42).await;
        println!("{}", result);
    });
}
```

### 5.5 `async move ||` 的 FnOnce 语义

`async move ||` 按值捕获非 `Copy` 环境时，闭包本身会被消耗，只能调用一次。

```rust,compile_fail
async fn bad_once() {
    let data = vec![1, 2, 3];

    let f = async move |x: i32| {
        data.push(x);
        data.len()
    };

    let len1 = f(4).await; // ✅ 第一次调用
    let len2 = f(5).await; // ❌ 编译错误：f 已被消耗
}
```

若需多次调用，应改用 `async ||`（按引用（Reference）捕获）或在 `async move ||` 中捕获 `Arc<Mutex<T>>` 等共享所有权（Ownership）类型。

---

## 6. 版本演进与前沿

```text
Future trait          (1.36)
  → async/await 语法   (1.39)
    → Future/IntoFuture in prelude      (2024 edition / 1.85)
      → AFIT: async fn in trait          (1.75.0)
        → AsyncFn traits + async closures stable  (1.85.0)
          → AFIDT: async fn in dyn trait   (nightly 实验中，暂无稳定时间表；dyn Trait 仍需 async_trait，跟踪 rust-lang/rust#133882)
            → RTN: Return Type Notation     (nightly / RFC)
              → Async Drop                  (nightly)
                → Gen blocks / AsyncIterator  (nightly)
```

> **状态标注模板**：
>
> - ✅ `async closures` — **stable 1.85.0**
> - 🧪 `AFIDT` — nightly 实验中，暂无稳定时间表；`dyn Trait` 场景继续使用 `async_trait`，跟踪 issue [#133882](https://github.com/rust-lang/rust/issues/133882)
> - 🧪 `RTN` — nightly / RFC 阶段
> - 🧪 `Async Drop` — nightly，跟踪 issue [#126494](https://github.com/rust-lang/rust/issues/126494)
> - 🧪 `Gen blocks` — nightly，需 `#![feature(gen_blocks, yield_expr)]`

---

## 7. 与官方资源的映射

| 本文件覆盖点 | 官方对应章节 |
|---|---|
| async closure 语法 | [TRPL Ch17](https://doc.rust-lang.org/book/ch17-00-async-await.html) |
| `AsyncFn` trait 语义 | [Rust Reference — Closure expressions](https://doc.rust-lang.org/reference/expressions/closure-expr.html#async-closures) |
| RFC 设计动机 | [RFC 3668](https://rust-lang.github.io/rfcs/3668-async-closures.html) |
| 稳定化公告 | [Rust 1.85.0 Release](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html) |
| async 生态与运行时（Runtime） | [Async Book](https://rust-lang.github.io/async-book/index.html)（rewrite 中，状态 WIP） |

---

## 8. 认知路径

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| async closures 提供原生异步闭包 ⟹ 简化高阶异步回调 | 掌握旧写法 `\|x\| async move {}` | 能用 `async \|x\| {}` 编写更简洁的异步回调 | 高 |
| 借用（Borrowing）捕获支持 ⟹ 生命周期（Lifetimes）推断更精确 | 理解同步闭包捕获规则 | 能在异步（Async）场景中安全借用环境变量 | 高 |
| `AsyncFn` 非 dyn-compatible ⟹ 不能直接用 `Box<dyn AsyncFn>` | 理解 trait object safety | 能用泛型（Generics）或传统闭包绕过 | 高 |

### 反命题与边界

> **反命题**: "async closures 可以完全替代 `async move {}`" —— 错误。`dyn AsyncFn` 暂不可用，某些场景仍需传统闭包或 `async_trait`。

---

## 9. 练习

### 练习 1：改写

将以下旧写法改写为 async closure：

```rust,ignore
let process = |items: Vec<i32>| -> Pin<Box<dyn Future<Output = i32> + Send>> {
    Box::pin(async move {
        items.iter().sum()
    })
};
```

<details>
<summary>参考答案</summary>

```rust,ignore
let process = async |items: Vec<i32>| -> i32 {
    items.iter().sum()
};
```

</details>

### 练习 2：判断正误

1. async closures 需要 nightly feature gate。（❌，1.85.0+ stable）
2. `AsyncFn` traits 在 Rust 2024 edition 中已进入 prelude。（✅）
3. `Box<dyn AsyncFn(i32) -> bool>` 当前合法。（❌，非 dyn-compatible）

---

## 10. 相关概念

- [Async/Await（异步编程）](02_async.md)
- [Pin 与 Unpin](06_pin_unpin.md)
- [L2 闭包类型](../../02_intermediate/04_types_and_conversions/07_closure_types.md)
- [Rust 2024 Edition](../../../knowledge/06_ecosystem/02_edition_2024.md)

---

> **权威来源**:
>
> [RFC 3668](https://rust-lang.github.io/rfcs/3668-async-closures.html),
> [Rust Reference](https://doc.rust-lang.org/reference/expressions/closure-expr.html#async-closures),
> [TRPL Ch17](https://doc.rust-lang.org/book/ch17-00-async-await.html),
> [Rust 1.85.0 Release Notes](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html)
>
> **文档版本**: 2.0
> **对应 Rust 版本**: 1.85.0+ (Edition 2024 / 2021)
> **最后更新**: 2026-06-28
> **状态**: ✅ 权威来源对齐完成（对齐 Rust 1.97.0 stable）
