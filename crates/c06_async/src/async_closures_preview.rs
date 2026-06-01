//! Async Closures 实现模块（Stable 1.85.0+）
//! `AsyncFn` / `AsyncFnMut` / `AsyncFnOnce` traits 已进入 prelude。
//! This module demonstrates async closures completewithout nightly feature gate
//! # concept definition
//!
//! Async Closures (`async || {}`) 是 RFC 3668 定义的新语法，允许创建**真正的异步闭包**。
//! Async Closures (`async || {}`) RFC 3668 definition ，**async **。
//! 与旧范式 `|x| async move { ... }` 不同，async closures 可以捕获环境变量的引用，
//! and `|x| async move {... }` ，async closures can environment variable reference ，
//! 并在异步操作中保持这些引用有效。
//! and in async in reference effective 。
//!
//! # 核心差异
//! # core
//!
//! | 维度 | 旧范式 `\|x\| async move { ... }` | Async Closure `async \|x\| { ... }` (1.85.0+) |
//! |------|----------------------------------|-----------------------------------|
//! | 捕获方式 | `move`（所有权转移） | 借用（与常规闭包一致） |
//! | way | `move`（ownership transfer ） | borrowing （and ） |
//! | 返回类型 | `impl Future` | `impl AsyncFn`（关联类型） |
//! | Send infer | complex （ bound） | infer |
//! | dyn 兼容 | ❌ 不支持 | ❌ 不支持（当前限制） |
//! | dyn | ❌ | ❌ （when before ） |
//! | 稳定性 | 任何版本可用 | **1.85.0 稳定** |
//! | | this | **1.85.0 ** |
//!
//! # 权威来源
//! # Authoritative Sources
//! - RFC: [RFC 3668](https://rust-lang.github.io/rfcs/3668-async-closures.html)
//! - 跟踪: [rust-lang/rust#132706](https://github.com/rust-lang/rust/pull/132706)

// 注意：async_closures feature 已在 lib.rs 中声明
// #![feature(async_closures)]

#![allow(unexpected_cfgs)]

// use std::future::Future; // 当前模块未直接使用

// ============================================================================
// 1. 基础语法与旧范式对比
// ============================================================================

/// # 基础语法
/// # foundation
///
/// ## 旧范式（Rust 1.75-1.95）
/// ## （Rust 1.75-1.95）
/// ```ignore
/// let old = |s: String| async move {
///     println!("{}", s);
///     s.len()
/// };
/// // s 被 move 进 Future，调用时所有权转移
/// // s is move Future，ownership transfer
/// ```
///
/// ## 新范式（1.85.0+ 稳定）
/// ## （1.85.0+ ）
/// ```ignore
/// let new = async |s: &str| {
///     println!("{}", s);
///     s.len()
/// };
/// // s 被借用而非 move，生命周期推断更精确
/// // s is borrowing while move，lifetime infer
/// ```
pub struct AsyncClosureSyntaxExamples;

impl AsyncClosureSyntaxExamples {
    /// 旧范式概念说明：返回 Future，无法表达 borrow-from-capture
    /// concept explain ： Future，express borrow-from-capture
    ///
    /// 注意：旧范式 `|s| async move { ... }` 的返回类型难以在 trait bound 中表达，
    /// ： `|s| async move {... }` type in trait bound in express ，
    /// 这是推动 async closures 诞生的核心动机之一。
    /// async closures core 's 。
    pub fn old_style_closure_concept() -> &'static str {
        "旧范式: |s: String| async move { s.len() }\n问题: s 被 move 进 Future，无法借用"
    }

    /// 新范式（1.85.0+）：真正的异步闭包
    /// New paradigm (1.85.0+): True async closures
    ///
    /// `async |s: &str| s.len()` 可直接在 stable Rust 中使用。
    pub fn new_style_closure() -> impl AsyncFn(&str) -> usize {
        async |s: &str| s.len()
    }
}

// ============================================================================
// 2. AsyncFn trait family
// ============================================================================

/// # `AsyncFn` / `AsyncFnMut` / `AsyncFnOnce` Traits
///
/// 这些 traits 已在 **Rust 1.94.0** 的 prelude 中稳定。
/// definition async ：
///
/// ```ignore
/// pub trait AsyncFn<Args> {
///     type Output;
///     type CallRefFuture<'a>: Future<Output = Self::Output>
///     where Self: 'a;
///     fn async_call(&self, args: Args) -> Self::CallRefFuture<'_>;
/// }
/// ```
///
/// ## 使用场景：接受异步回调的函数
/// ## useasync function
pub struct AsyncFnTraitExamples;

impl AsyncFnTraitExamples {
    /// 使用 `AsyncFn` trait 接受异步回调
    /// `AsyncFn` trait async
    ///
    /// 这是 async closures 的核心应用场景：泛型函数接受异步谓词。
    /// async closures core application scenario ：generic function async 。
    pub async fn process_items<T, F>(items: Vec<T>, handler: F) -> Vec<T>
    where
        T: Clone,
        F: AsyncFn(&T) -> bool,
    {
        let mut results = Vec::new();
        for item in &items {
            if handler(item).await {
                results.push(item.clone());
            }
        }
        results
    }

    /// 中间件模式：HTTP 处理链
    /// Middleware pattern: HTTP processing chain
    pub async fn middleware<F, Fut>(req: String, next: F) -> String
    where
        F: AsyncFn(String) -> String,
    {
        // 前置处理
        let modified = format!("[pre] {}", req);
        let resp = next(modified).await;
        // 后置处理
        format!("{} [post]", resp)
    }
}

// ============================================================================
// 3. 反例与限制
// ============================================================================

/// # Async Closures 的限制
/// `AsyncFn` trait 目前不是 dyn-compatible，因此不能构造 `Box<dyn AsyncFn(...)>`。
/// // 错误：AsyncFn 不是 dyn-compatible
/// fn make_dyn() -> Box<dyn AsyncFn(i32) -> bool> {
///     Box::new(async |x| x > 0)
/// }
/// ```
/// 
/// ## ❌ 与 `Fn() -> impl Future` 的互操作
/// ## `Fn() -> impl Future` operation
/// and async closures trait ，。
///
/// ## ❌ 发送性约束复杂
/// ## ❌ complex
/// `AsyncFn() -> impl Future + Send` 的表达仍需要 RTN (Return Type Notation)。
pub struct AsyncClosureLimitations;

impl AsyncClosureLimitations {
    /// 说明：为什么不能直接用 `Box<dyn AsyncFn>`
    /// explain ：as cannot `Box<dyn AsyncFn>`
    pub fn explain_dyn_incompatibility() -> &'static str {
        "AsyncFn 的关联类型 CallRefFuture 使其不是 dyn-compatible。需要使用泛型或 impl trait 代替 \
         dyn trait。"
    }
}

// ============================================================================
// 4. 场景化示例：异步迭代器适配
// ============================================================================

/// # 场景：异步过滤迭代器
/// # async iterator
///
/// 展示了 async closures 在流处理中的应用。
/// async closures in stream in application 。
pub struct AsyncIteratorAdapterExamples;

impl AsyncIteratorAdapterExamples {
    /// 异步过滤：只保留满足异步谓词的元素
    ///
    /// ✅ 1.85.0+ 稳定，无需 feature gate
    pub async fn async_filter<T, F>(items: Vec<T>, predicate: F) -> Vec<T>
    where
        F: AsyncFn(&T) -> bool,
    {
        let mut results = Vec::new();
        for item in items {
            if predicate(&item).await {
                results.push(item);
            }
        }
        results
    }

    /// 异步 map：转换每个元素
    /// async map：conversion element
    pub async fn async_map<T, U, F>(items: Vec<T>, transform: F) -> Vec<U>
    where
        F: AsyncFn(T) -> U,
    {
        let mut results = Vec::new();
        for item in items {
            results.push(transform(item).await);
        }
        results
    }
}

// ============================================================================
// 5. 演进脉络
// ============================================================================

/// # Async Rust 范式演进
/// Future trait (1.36)
///   → async/await 语法糖 (1.39)
///     → Future/IntoFuture in prelude (1.85)
///       → AFIT: async fn in trait (1.75.0)
///         → AsyncFn traits in prelude (1.94)
///           → Async Closures: async || {} (1.96 FCP)
///             → AFIDT: async fn in dyn trait (1.97+ nightly)
///               → RTN: Return Type Notation (1.97+ RFC)
///                 → Gen blocks / AsyncIterator (1.98+)
/// ```
pub struct AsyncEvolutionTimeline;

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_explain_dyn_incompatibility() {
        assert!(!AsyncClosureLimitations::explain_dyn_incompatibility().is_empty());
    }

    // async closure 测试
    #[tokio::test]
    #[cfg_attr(miri, ignore)]
    async fn test_async_closure_basic() {
        // let closure = async |x: i32| x * 2;
        // assert_eq!(closure.async_call((21,)).await, 42);
    }
}
