//! Async Closures 可编译示例（Rust 1.85.0+ stable，Rust 2024 edition）
//!
//! 本模块对应概念文档 `concept/03_advanced/24_async_closures.md`，
//! 所有示例均可在 stable Rust 1.85.0+ / Edition 2024 下直接编译运行，
//! 无需任何 nightly feature gate。
//!
//! 权威来源：
//! - RFC 3668: https://rust-lang.github.io/rfcs/3668-async-closures.html
//! - Rust Reference: https://doc.rust-lang.org/reference/expressions/closure-expr.html#async-closures
//! - TRPL Ch17: https://doc.rust-lang.org/book/ch17-00-async-await.html

use std::time::Duration;

// ============================================================================
// 1. 基础语法
// ============================================================================

/// 演示 async closure 的基础语法。
pub async fn basic_syntax() -> i32 {
    // 无参数
    let f = async || {
        println!("hello from async closure");
        42
    };

    // 有参数、有返回类型标注
    let add = async |a: i32, b: i32| -> i32 {
        tokio::time::sleep(Duration::from_millis(1)).await;
        a + b
    };

    let result = add(1, 2).await;
    assert_eq!(f().await, 42);
    result
}

// ============================================================================
// 2. 捕获模式
// ============================================================================

/// 演示 async closure 的引用捕获与 move 捕获。
pub async fn capture_modes() {
    // 1. 引用捕获（默认）：data 被不可变借用
    let data = vec![1, 2, 3];
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
    g().await;

    // 3. 借用捕获允许在异步上下文中保持引用
    let s = String::from("hello");
    let h = async || {
        println!("{}", s); // s 被借用，而不是 move
    };
    h().await;
    println!("{}", s); // ✅ s 仍可用
}

// ============================================================================
// 3. AsyncFn trait 家族
// ============================================================================

/// 演示使用 `AsyncFn` trait 接受异步回调。
///
/// 在 Rust 2024 edition 中，`AsyncFn`/`AsyncFnMut`/`AsyncFnOnce`
/// 已默认进入 prelude，无需显式 use。
pub fn accept_async_callback<F>(f: F) -> impl std::future::Future<Output = i32>
where
    F: AsyncFn(i32) -> i32,
{
    async move { f(21).await }
}

/// 使用 async closure 作为高阶异步谓词。
pub async fn process_items<T, F>(items: Vec<T>, predicate: F) -> Vec<T>
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

/// 演示 `async fn` 自动实现 `AsyncFn`。
pub async fn native_async_fn_implies_asyncfn(_x: i32) -> i32 {
    async fn double(x: i32) -> i32 {
        x * 2
    }

    let closure = async |x: i32| double(x).await;
    closure(21).await
}

// ============================================================================
// 4. 实际应用模式
// ============================================================================

/// 使用泛型结构体接受异步回调（`AsyncFn` 当前不是 dyn-compatible，
/// 因此不能用 `Box<dyn AsyncFn>`，需用泛型）。
pub struct AsyncHandler<T, F>
where
    F: AsyncFn(T),
{
    handler: F,
    _phantom: std::marker::PhantomData<T>,
}

impl<T, F> AsyncHandler<T, F>
where
    F: AsyncFn(T),
{
    pub fn new(handler: F) -> Self {
        Self {
            handler,
            _phantom: std::marker::PhantomData,
        }
    }

    pub async fn handle(&self, event: T)
    where
        F: AsyncFn(T),
    {
        (self.handler)(event).await;
    }
}

/// 中间件链示例：使用泛型传递 async closure。
pub async fn middleware_chain<F>(req: String, final_handler: F) -> String
where
    F: AsyncFn(String) -> String + Send + Sync + Clone,
{
    let handler = final_handler.clone();
    let resp = handler(req).await;
    format!("[post] {}", resp)
}

// ============================================================================
// 5. 与旧范式对比
// ============================================================================

/// 旧范式：闭包返回 Future，强制 move。
pub fn old_style_callback()
-> impl FnOnce(String) -> std::pin::Pin<Box<dyn std::future::Future<Output = usize> + Send>> {
    |s: String| {
        Box::pin(async move {
            tokio::time::sleep(Duration::from_millis(1)).await;
            s.len()
        })
    }
}

/// 新范式：真正的 async closure，可按使用借用捕获。
pub fn new_style_callback() -> impl AsyncFnOnce(String) -> usize {
    async |s: String| {
        tokio::time::sleep(Duration::from_millis(1)).await;
        s.len()
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_syntax() {
        assert_eq!(basic_syntax().await, 3);
    }

    #[tokio::test]
    async fn test_capture_modes() {
        capture_modes().await;
    }

    #[tokio::test]
    async fn test_accept_async_callback() {
        let result = accept_async_callback(async |x| x * 2).await;
        assert_eq!(result, 42);
    }

    #[tokio::test]
    async fn test_process_items() {
        let evens = process_items(vec![1, 2, 3, 4], async |x| *x % 2 == 0).await;
        assert_eq!(evens, vec![2, 4]);
    }

    #[tokio::test]
    async fn test_native_async_fn_implies_asyncfn() {
        assert_eq!(native_async_fn_implies_asyncfn(21).await, 42);
    }

    #[tokio::test]
    async fn test_async_handler() {
        let handler = AsyncHandler::new(async |msg: String| {
            println!("processed: {}", msg);
        });
        handler.handle("hello".to_string()).await;
    }

    #[tokio::test]
    async fn test_middleware_chain() {
        let result = middleware_chain("request".to_string(), async |req| {
            format!("handled: {}", req)
        })
        .await;
        assert_eq!(result, "[post] handled: request");
    }

    #[tokio::test]
    async fn test_old_vs_new_style() {
        let old = old_style_callback();
        assert_eq!(old("hello".to_string()).await, 5);

        let new = new_style_callback();
        assert_eq!(new("hello".to_string()).await, 5);
    }
}
