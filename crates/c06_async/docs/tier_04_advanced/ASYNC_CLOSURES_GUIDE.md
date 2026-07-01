# Async Closures 深度指南

> **状态**: ✅ **Stable since Rust 1.85.0**（2025-02-20）
> **RFC**: [RFC 3668](https://rust-lang.github.io/rfcs/3668-async-closures.html)
> **相关 Traits**: `AsyncFn`, `AsyncFnMut`, `AsyncFnOnce` (1.85.0 stable, Rust 2024 prelude)

---

## 目录

- [Async Closures 深度指南](#async-closures-深度指南)
  - [目录](#目录)
  - [一、问题域：旧范式的痛点](#一问题域旧范式的痛点)
    - [1.1 旧范式：`|x| async move { ... }`](#11-旧范式x-async-move---)
    - [1.2 三大痛点](#12-三大痛点)
  - [二、解决方案：`async || {}`](#二解决方案async--)
    - [2.1 语法与语义](#21-语法与语义)
    - [2.2 AsyncFn trait family](#22-asyncfn-trait-family)
    - [2.3 核心优势](#23-核心优势)
  - [三、应用场景](#三应用场景)
    - [3.1 异步过滤器](#31-异步过滤器)
    - [3.2 中间件链](#32-中间件链)
    - [3.3 事件处理](#33-事件处理)
  - [四、限制与反例](#四限制与反例)
    - [❌ 不是 dyn-compatible](#-不是-dyn-compatible)
    - [❌ 与旧闭包的互操作](#-与旧闭包的互操作)
    - [❌ Send bound 仍需要 RTN](#-send-bound-仍需要-rtn)
  - [五、决策树](#五决策树)
  - [六、权威来源](#六权威来源)

## 一、问题域：旧范式的痛点

### 1.1 旧范式：`|x| async move { ... }`

```rust
// 旧方式：返回 impl Future，无法表达 borrow-from-capture
let old_closure = |s: String| async move {
    println!("{}", s);
    s.len()
};
// 问题：s 被 move 进 Future，调用时所有权转移
```
### 1.2 三大痛点

| 痛点 | 说明 | 影响 |
|------|------|------|
| **所有权强制转移** | `async move` 捕获整个环境 | 无法借用局部变量 |
| **Send bound 地狱** | `Fn() -> impl Future + Send` 难以表达 | 与 tokio::spawn 集成困难 |
| **不是真正的闭包** | 返回的是 Future 而非异步闭包 | 无法用于 `filter`/`map` 等适配器 |

---

## 二、解决方案：`async || {}`

### 2.1 语法与语义

```rust
// async closures stable since 1.85.0，无需 feature gate

// ✅ 新方式：真正的异步闭包
let new_closure = async |s: &str| {
    println!("{}", s);
    s.len()
};
// 优势：s 被借用而非 move，生命周期推断更精确
```
### 2.2 AsyncFn trait family

```rust
// 1.85.0+ stable 的三个 trait（Rust 2024 prelude）
pub trait AsyncFn<Args> {
    type Output;
    type CallRefFuture<'a>: Future<Output = Self::Output> where Self: 'a;
    fn async_call(&self, args: Args) -> Self::CallRefFuture<'_>;
}

pub trait AsyncFnMut<Args> { /* ... */ }
pub trait AsyncFnOnce<Args> { /* ... */ }
```
### 2.3 核心优势

```rust
// 1. 借用捕获
let prefix = "Hello".to_string();
let greet = async |name: &str| {
    println!("{} {}", prefix, name);  // prefix 被借用，不是 move
};

// 2. 自动实现：所有 async fn 和返回 Future 的函数
async fn native_async(x: i32) -> i32 { x * 2 }
// native_async 自动实现 AsyncFn(i32) -> i32

// 3. 与迭代器适配器结合
// items.filter(async |x| x.is_valid().await)
```
---

## 三、应用场景

### 3.1 异步过滤器

```rust
async fn filter_valid(users: Vec<User>) -> Vec<User> {
    users.into_iter()
        .filter(async |u| u.is_active().await)
        .collect()
}
```
### 3.2 中间件链

```rust
async fn middleware_chain<F>(req: Request, handler: F) -> Response
where
    F: AsyncFn(Request) -> Response,
{
    log_request(&req).await;
    let resp = handler.async_call((req,)).await;
    log_response(&resp).await;
    resp
}
```
### 3.3 事件处理

```rust
let on_click = async |event: ClickEvent| {
    let data = fetch_data(event.id).await;
    update_ui(data).await;
};
```
---

## 四、限制与反例

### ❌ 不是 dyn-compatible

```rust
// 编译错误：AsyncFn 不是 dyn-compatible
fn make_dyn() -> Box<dyn AsyncFn(i32) -> bool> {
    Box::new(async |x| x > 0)
}
```
**原因**: `AsyncFn` 有关联类型 `CallRefFuture`，vtable 无法表示。

**解决**: 使用泛型或 `impl AsyncFn`。

### ❌ 与旧闭包的互操作

```rust
fn takes_async_fn<F: AsyncFn(i32) -> bool>(f: F) {}

fn old_style(x: i32) -> impl Future<Output = bool> {
    async move { x > 0 }
}

// 可能不直接兼容，需要显式转换
```
### ❌ Send bound 仍需要 RTN

```rust
// 当前无法直接表达：
fn spawn_handler<F>(f: F)
where
    F: AsyncFn(Request) -> Response + Send,
    // Response 的 Future 也需要 Send，但无法在此约束
{
    tokio::spawn(async move { f.async_call((req,)).await });
}
```
**解决**: 等待 RTN (Return Type Notation) 稳定。

---

## 五、决策树

```text
需要异步回调？
├── 接受者要求 dyn Trait？
│   ├── 是 → 使用 async_trait 宏（当前唯一选择）
│   └── 否 → 使用泛型 + AsyncFn
│       └── 需要借用捕获？
│           ├── 是 → async || {} (1.85.0+ stable)
│           └── 否 → |x| async move {} (stable)
└── 不需要回调 → 直接 async fn
```
---

## 六、权威来源

- [RFC 3668: Async Closures](https://rust-lang.github.io/rfcs/3668-async-closures.html)
- [rust-lang/rust#132706](https://github.com/rust-lang/rust/pull/132706)
- [Async Fundamentals Initiative](https://rust-lang.github.io/async-fundamentals-initiative/)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.85.0+ (Edition 2024 / 2021)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
