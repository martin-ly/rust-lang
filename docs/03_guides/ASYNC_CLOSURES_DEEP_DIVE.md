# Async Closures 深度指南

> **Bloom 层级**: L3 (Application) — L4 (Analysis)
> **对应 Rust 版本**: 1.95.0+ stable
> **最后更新**: 2026-05-20

---

## 📑 目录
>
- [Async Closures 深度指南](#async-closures-深度指南)
  - [📑 目录](#-目录)
  - [概述](#概述)
  - [一、历史背景：为什么需要 AsyncFn？](#一历史背景为什么需要-asyncfn)
    - [1.1 旧时代的困境](#11-旧时代的困境)
    - [1.2 异步闭包的诞生](#12-异步闭包的诞生)
  - [二、AsyncFn Trait 家族](#二asyncfn-trait-家族)
    - [2.1 三层 trait 体系](#21-三层-trait-体系)
    - [2.2 自动实现规则](#22-自动实现规则)
    - [2.3 关键区别：AsyncFn vs Fn + Future](#23-关键区别asyncfn-vs-fn--future)
  - [三、捕获语义深度解析](#三捕获语义深度解析)
    - [3.1 捕获模式](#31-捕获模式)
    - [3.2 生命周期陷阱](#32-生命周期陷阱)
    - [3.3 与 `async move` 闭包的对比](#33-与-async-move-闭包的对比)
  - [四、框架实战：Axum 与 Tokio](#四框架实战axum-与-tokio)
    - [4.1 Axum Handler 中的异步闭包](#41-axum-handler-中的异步闭包)
    - [4.2 泛型服务抽象](#42-泛型服务抽象)
    - [4.3 Tokio 任务中的异步闭包](#43-tokio-任务中的异步闭包)
  - [五、高级模式](#五高级模式)
    - [5.1 类型擦除与动态分发](#51-类型擦除与动态分发)
    - [5.2 递归异步闭包](#52-递归异步闭包)
    - [5.3 组合子模式](#53-组合子模式)
  - [六、常见陷阱与调试](#六常见陷阱与调试)
    - [6.1 陷阱 1：混淆 `async fn` 与 `AsyncFn` 边界](#61-陷阱-1混淆-async-fn-与-asyncfn-边界)
    - [6.2 陷阱 2：`Send` 边界传递](#62-陷阱-2send-边界传递)
    - [6.3 陷阱 3：生命周期与 `Box<dyn>`](#63-陷阱-3生命周期与-boxdyn)
  - [七、版本兼容与迁移](#七版本兼容与迁移)
    - [7.1 渐进式采用](#71-渐进式采用)
    - [7.2 最低版本要求](#72-最低版本要求)
  - [八、延伸阅读](#八延伸阅读)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 概述
>
> **[来源: Rust Official Docs]**

Rust 1.95.0 稳定了**异步闭包（Async Closures）** 和对应的 `AsyncFn` trait 家族，这是 Rust 异步编程生态的里程碑式进展。在此之前，Rust 开发者只能使用 `async move || {}` 形式的异步闭包，它们在类型系统和trait边界方面存在诸多限制。

本指南深度解析异步闭包的语法、语义、类型系统以及在主流框架中的实战应用。

[来源: Rust 1.95 Release Notes / RFC 3668]

---

## 一、历史背景：为什么需要 AsyncFn？
>
> **[来源: Rust Official Docs]**

### 1.1 旧时代的困境
>
> **[来源: Rust Official Docs]**

在 Rust 1.95 之前，传递异步逻辑的唯一方式是 `impl Fn() -> impl Future`：

```rust
// 旧方式：函数返回 Future
async fn old_style<F, Fut>(f: F)
where
    F: FnOnce(i32) -> Fut,
    Fut: Future<Output = i32>,
{
    let result = f(42).await;
}
```

这种方式的问题：

- **类型爆炸**：每个异步闭包都会生成一个独特的 `Future` 类型
- **无法存储**：`impl Future` 不能放入 `Box<dyn>` 或结构体字段
- **组合困难**：无法像 `Fn` 那样进行高阶组合

### 1.2 异步闭包的诞生

Rust 1.95 引入了原生异步闭包语法：

```rust
let closure = async |x: i32| -> i32 {
    tokio::time::sleep(Duration::from_millis(10)).await;
    x * 2
};
```

这个闭包的类型直接实现 `AsyncFn(i32) -> i32`，无需中间 `Future` 类型。

[来源: The Rust Programming Language (2024 Edition), Chapter 13.2]

---

## 二、AsyncFn Trait 家族

### 2.1 三层 trait 体系

| Trait | 调用次数 | 捕获语义 | 对应同步 trait |
|-------|---------|---------|--------------|
| `AsyncFn` | 多次 | 不可变借用 | `Fn` |
| `AsyncFnMut` | 多次 | 可变借用 | `FnMut` |
| `AsyncFnOnce` | 一次 | 移动/消耗 | `FnOnce` |

```rust
/// AsyncFn: 可多次异步调用，不修改捕获状态
pub async fn call_repeatedly<F>(f: F)
where
    F: AsyncFn(i32) -> i32,
{
    for i in 0..3 {
        println!("result: {}", f(i).await);
    }
}

/// AsyncFnMut: 可多次调用，可能修改内部状态
pub async fn call_with_state<F>(mut f: F)
where
    F: AsyncFnMut(i32) -> i32,
{
    println!("{}", f(1).await); // 第 1 次
    println!("{}", f(2).await); // 第 2 次，f 的内部状态可能已改变
}

/// AsyncFnOnce: 只能调用一次，消耗所有权
pub async fn call_once<F>(f: F)
where
    F: AsyncFnOnce(i32) -> String,
{
    let msg = f(42).await;
    println!("{}", msg);
    // f 已消耗，不能再调用
}
```

### 2.2 自动实现规则

```rust
// 所有 async fn 自动实现 AsyncFn
async fn plain_async(x: i32) -> i32 { x + 1 }
// plain_async 实现了 AsyncFn(i32) -> i32

// async || 闭包自动实现对应 trait
let c1 = async |x: i32| x + 1;           // impl AsyncFn
let mut c2 = async |x: i32| { count += x; count }; // impl AsyncFnMut
let c3 = async |x: i32| -> String { s }; // impl AsyncFnOnce (消耗 s)
```

### 2.3 关键区别：AsyncFn vs Fn + Future

```rust
// 旧方式: Fn() -> impl Future
fn old_closure() -> impl Fn(i32) -> Pin<Box<dyn Future<Output = i32> + Send>>> {
    |x| Box::pin(async move { x * 2 })
}

// 新方式: AsyncFn
fn new_closure() -> impl AsyncFn(i32) -> i32 {
    async |x| x * 2
}
```

| 特性 | `Fn() -> Future` | `AsyncFn` |
|------|-----------------|-----------|
| 语法 | 手动 `async move` | 原生 `async \|x\|` |
| 类型擦除 | 困难 | 原生支持 |
| 编译器优化 | 间接调用 | 直接内联 |
| 错误信息 | 复杂嵌套 | 清晰直接 |

[来源: Rust Reference, Async Closures]

---

## 三、捕获语义深度解析

### 3.1 捕获模式

异步闭包的捕获规则与同步闭包一致，但捕获的是**生成 Future 所需的状态**，而非 Future 本身：

```rust
let multiplier = 10;

// 捕获 multiplier 的不可变引用
let c1 = async |x: i32| x * multiplier;

// 捕获 multiplier 的所有权（通过 move）
let c2 = async move |x: i32| x * multiplier;

// 捕获 Vec 的所有权
let data = vec![1, 2, 3];
let c3 = async move |idx: usize| -> Option<i32> {
    tokio::time::sleep(Duration::from_millis(1)).await;
    data.get(idx).copied()
};
```

### 3.2 生命周期陷阱

```rust
let local = String::from("hello");

// ❌ 错误：闭包捕获了 local 的引用，但闭包比 local 活得久
let bad: Box<dyn AsyncFn() -> String> = Box::new(async || local.clone());

// ✅ 正确：使用 move 转移所有权
let good: Box<dyn AsyncFn() -> String> = Box::new(async move || local.clone());
```

### 3.3 与 `async move` 闭包的对比

```rust
let s = String::from("data");

// 旧方式：async move ||
// 闭包本身同步创建，调用时生成 Future
let old = async move || {
    println!("{}", s);
    s.len()
};

// 新方式：async ||
// 闭包直接是异步的，调用即进入异步上下文
let new = async || {
    println!("{}", s);
    s.len()
};

// 关键区别：
// old() 返回一个 Future，需要 .await
// new() 也是返回 Future，但类型系统知道它是 AsyncFn
```

[来源: Rust Internals, "Async Closures: Design Notes"]

---

## 四、框架实战：Axum 与 Tokio

### 4.1 Axum Handler 中的异步闭包

```rust
use axum::{routing::get, Router};
use std::time::Duration;

#[tokio::main]
async fn main() {
    // 使用 async 闭包定义中间件逻辑
    let auth_checker = async |token: &str| -> bool {
        tokio::time::sleep(Duration::from_millis(5)).await;
        token == "valid-token"
    };

    let app = Router::new()
        .route("/", get(|| async { "Hello, World!" }));

    // 将异步闭包传给服务层
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

### 4.2 泛型服务抽象

```rust
use axum::{extract::Request, middleware::Next, response::Response};

/// 通用的异步中间件工厂
pub fn async_middleware<F>(predicate: F) -> impl AsyncFn(Request, Next) -> Response
where
    F: AsyncFn(&str) -> bool + Clone + Send + Sync + 'static,
{
    async move |req: Request, next: Next| {
        // 从 header 提取 token
        let token = req.headers()
            .get("authorization")
            .and_then(|h| h.to_str().ok())
            .unwrap_or("");

        if predicate(token).await {
            next.run(req).await
        } else {
            Response::builder()
                .status(401)
                .body("Unauthorized".into())
                .unwrap()
        }
    }
}
```

### 4.3 Tokio 任务中的异步闭包

```rust
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

[来源: Axum Documentation / Tokio Documentation]

---

## 五、高级模式

### 5.1 类型擦除与动态分发

```rust
use std::pin::Pin;
use std::future::Future;

/// 将 AsyncFn 装箱为 trait object
pub type BoxedAsyncFn<I, O> = Box<
    dyn AsyncFn(I) -> O + Send + Sync,
>;

pub fn make_handler() -> BoxedAsyncFn<i32, i32> {
    Box::new(async |x| x * 2)
}

/// 在 HashMap 中存储异步处理函数
use std::collections::HashMap;

pub struct AsyncRouter {
    handlers: HashMap<String, BoxedAsyncFn<String, String>>,
}
```

### 5.2 递归异步闭包

```rust
use std::rc::Rc;
use std::cell::RefCell;

/// 递归计算斐波那契（教学示例，非生产推荐）
async fn async_fib() -> impl AsyncFn(u32) -> u32 {
    let memo = Rc::new(RefCell::new(vec![0u32, 1]));

    async move |n: u32| -> u32 {
        let mut memo = memo.borrow_mut();
        for i in memo.len()..=n as usize {
            let next = memo[i - 1] + memo[i - 2];
            memo.push(next);
        }
        memo[n as usize]
    }
}
```

### 5.3 组合子模式

```rust
/// 两个 AsyncFn 的串联组合
pub fn compose<A, B, C>(
    f: impl AsyncFn(A) -> B + Clone,
    g: impl AsyncFn(B) -> C + Clone,
) -> impl AsyncFn(A) -> C {
    async move |x| {
        let intermediate = f(x).await;
        g(intermediate).await
    }
}

/// 使用示例
let double = async |x: i32| x * 2;
let to_string = async |x: i32| x.to_string();
let double_then_string = compose(double, to_string);

assert_eq!(double_then_string(21).await, "42");
```

[来源: Rust Design Patterns, "Combinators"]

---

## 六、常见陷阱与调试

### 6.1 陷阱 1：混淆 `async fn` 与 `AsyncFn` 边界

```rust
// ❌ 错误：async fn 不等同于 AsyncFn 参数
fn takes_async_fn(f: impl AsyncFn(i32) -> i32) {}

fn caller() {
    async fn my_fn(x: i32) -> i32 { x }
    // my_fn 实现了 AsyncFn，但需要显式传递
    takes_async_fn(my_fn); // ✅ 正确
}
```

### 6.2 陷阱 2：`Send` 边界传递

```rust
// ❌ 错误：闭包捕获了 !Send 类型
let rc = std::rc::Rc::new(42);
let bad = async move |x: i32| x + *rc; // Rc 不是 Send

// spawn 要求 Future 是 Send
// tokio::spawn(bad(1)); // 编译错误

// ✅ 正确：使用 Arc
let arc = std::sync::Arc::new(42);
let good = async move |x: i32| x + *arc;
tokio::spawn(good(1)); // OK
```

### 6.3 陷阱 3：生命周期与 `Box<dyn>`

```rust
let data = vec![1, 2, 3];

// ❌ 错误：借用生命周期不够长
let bad: Box<dyn AsyncFn() -> i32> = Box::new(async || data.len());

// ✅ 正确：move 所有权
let good: Box<dyn AsyncFn() -> i32 + Send> = Box::new(async move || data.len());
```

---

## 七、版本兼容与迁移

### 7.1 渐进式采用

```rust
// 同时支持新旧两种写法的抽象
pub trait AsyncCallback<I, O>: AsyncFn(I) -> O {}
impl<T, I, O> AsyncCallback<I, O> for T where T: AsyncFn(I) -> O {}

// 旧代码迁移路径
// Before:
// fn handler<F, Fut>(f: F) where F: Fn(i32) -> Fut, Fut: Future<Output = i32> {}

// After:
fn handler<F>(f: F) where F: AsyncFn(i32) -> i32 {}
```

### 7.2 最低版本要求

| 特性 | 稳定版本 | 说明 |
|------|---------|------|
| `async \|\|` 语法 | 1.95.0 | 需要 Edition 2024 |
| `AsyncFn` trait | 1.95.0 | 核心 trait |
| `AsyncFnMut` | 1.95.0 | 可变版本 |
| `AsyncFnOnce` | 1.95.0 | 消费版本 |

[来源: Rust Edition Guide 2024]

---

## 八、延伸阅读

- [RFC 3668: Async Closures](https://rust-lang.github.io/rfcs/3668-async-closures.html)
- [The Rust Programming Language (2024 Edition), Chapter 13](https://doc.rust-lang.org/book/ch13-01-closures.html)
- [Rust Reference: Async Closures](https://doc.rust-lang.org/reference/expressions/closure-expr.html)
- [Axum Documentation: Handlers](https://docs.rs/axum/latest/axum/handler/index.html)
- [Tokio Documentation: Spawning](https://docs.rs/tokio/latest/tokio/task/fn.spawn.html)

---

> **总结**: `AsyncFn` trait 家族将 Rust 的异步编程从"Future 类型体操"提升到了原生闭包抽象层面。在 1.95+ 项目中，优先使用 `async \|x\| {}` 语法和 `impl AsyncFn` 边界，可获得更清晰的类型签名和更好的编译器优化。

---

- [Parent README](../README.md)

---

## 相关概念

- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Asynchronous I/O]**

> **[来源: TRPL Ch. 17 - Async]**

> **[来源: Tokio Documentation]**

> **[来源: RFC 2394 - Async/Await]**

> **[来源: Wikipedia - Asynchronous I/O]**
> **[来源: TRPL Ch. 17 - Async]**
> **[来源: Tokio Documentation]**
> **[来源: RFC 2394 - Async/Await]**
