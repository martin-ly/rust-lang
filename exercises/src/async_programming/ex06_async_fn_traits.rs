//! # 练习 6: `AsyncFn` / `AsyncFnMut` / `AsyncFnOnce` 异步闭包 trait (Rust 1.95)
//!
//! **难度**: Hard  
//! **考点**: `AsyncFn` trait 家族、异步闭包类型擦除、`impl AsyncFn` 边界
//!
//! ## 背景
//!
//! Rust 1.95 稳定了异步闭包（`async |x| ...`）和对应的 `AsyncFn` trait 家族：
//! - `AsyncFn`：可以多次异步调用（类似 `Fn`，但每次调用返回 `Future`）
//! - `AsyncFnMut`：可以多次异步调用，但可能修改捕获状态
//! - `AsyncFnOnce`：只能异步调用一次，消耗所有权
//!
//! 这与同步的 `Fn`/`FnMut`/`FnOnce` 不同：异步闭包捕获的是调用时生成的 `Future`
//! 所需的状态，而不是调用本身的结果。
//!
//! ## 要求
//!
//! - 使用 `impl AsyncFn` 作为泛型参数边界
//! - 对比 `async fn` 与 `AsyncFn` trait 的适用场景
//! - 理解异步闭包的捕获语义


/// 使用 `AsyncFn` trait 对一个值进行异步转换
///
/// # 示例
///
/// ```ignore
/// let doubler = async |x: i32| x * 2;
/// let result = apply_async(doubler, 21).await;
/// assert_eq!(result, 42);
/// ```
pub async fn apply_async<F>(f: F, input: i32) -> i32
where
    F: AsyncFn(i32) -> i32,
{
    // TODO: 调用异步闭包 f 并 await 结果
    f(input).await
}

/// 使用 `AsyncFnMut` trait 对多个值进行异步映射
///
/// 异步闭包 `f` 可能被多次调用，因此使用 `AsyncFnMut` 边界。
pub async fn map_async<F>(mut f: F, inputs: Vec<i32>) -> Vec<i32>
where
    F: AsyncFnMut(i32) -> i32,
{
    let mut results = Vec::with_capacity(inputs.len());
    for input in inputs {
        results.push(f(input).await);
    }
    results
}

/// 使用异步闭包实现一个异步的谓词过滤器
///
/// # 示例
///
/// ```ignore
/// let is_even = async |x: &i32| x % 2 == 0;
/// let evens = filter_async(vec![1, 2, 3, 4, 5], is_even).await;
/// assert_eq!(evens, vec![2, 4]);
/// ```
pub async fn filter_async<F>(items: Vec<i32>, f: F) -> Vec<i32>
where
    F: AsyncFn(&i32) -> bool,
{
    let mut results = Vec::new();
    for item in &items {
        if f(item).await {
            results.push(*item);
        }
    }
    results
}

/// 判断以下说法是否正确
///
/// 1. "`AsyncFn` 是 `Fn` 的超集，所有 `Fn` 都自动实现 `AsyncFn`。" → false
/// 2. "异步闭包 `async |x| x + 1` 返回的类型实现了 `AsyncFnOnce`。" → true
/// 3. "`AsyncFn` 的每次调用都会产生一个新的 `Future`，这些 `Future` 可以同时执行。" → true
/// 4. "`impl AsyncFn(i32) -> i32` 可以作为函数参数类型。" → true
pub fn async_fn_quiz() -> [bool; 4] {
    [false, true, true, true]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_apply_async() {
        let doubler = async |x: i32| x * 2;
        assert_eq!(apply_async(doubler, 21).await, 42);
    }

    #[tokio::test]
    async fn test_map_async() {
        let add_one = async |x: i32| x + 1;
        let inputs = vec![1, 2, 3];
        let results = map_async(add_one, inputs).await;
        assert_eq!(results, vec![2, 3, 4]);
    }

    #[tokio::test]
    async fn test_filter_async() {
        let is_even = async |x: &i32| x % 2 == 0;
        let items = vec![1, 2, 3, 4, 5];
        let evens = filter_async(items, is_even).await;
        assert_eq!(evens, vec![2, 4]);
    }

    #[test]
    fn test_async_fn_quiz() {
        assert_eq!(async_fn_quiz(), [false, true, true, true]);
    }

    #[tokio::test]
    async fn test_async_closure_captures() {
        let multiplier = 10;
        let f = async |x: i32| x * multiplier;
        assert_eq!(apply_async(f, 5).await, 50);
    }
}
