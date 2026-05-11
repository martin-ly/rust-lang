//! Rust 1.97 特性跟踪模块 —— 异步编程
#![allow(clippy::incompatible_msrv)]

use futures::executor::block_on;

/// # Rust 1.97 特性演示
///
/// 展示 `std::pin::pin!` 和 `std::iter::repeat_n` 在异步场景中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `pin!` 在栈上固定异步 Future
    pub fn pin_async_future() -> i32 {
        let future = async { 42 };
        let pinned = std::pin::pin!(future);
        block_on(pinned)
    }

    /// 使用 `repeat_n` 生成异步任务批次
    pub fn generate_async_batch(task_id: u32, count: usize) -> Vec<u32> {
        std::iter::repeat_n(task_id, count).collect()
    }

    /// 结合 pin! 与 repeat_n 管理异步资源
    pub fn pin_and_repeat<T: Clone>(value: T, count: usize) -> Vec<T> {
        let pinned = std::pin::pin!(value.clone());
        let _ = pinned.clone();
        std::iter::repeat_n(value, count).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pin_async_future() {
        assert_eq!(Rust197Features::pin_async_future(), 42);
    }

    #[test]
    fn test_generate_async_batch() {
        assert_eq!(Rust197Features::generate_async_batch(7, 3), vec![7, 7, 7]);
        assert!(Rust197Features::generate_async_batch(1, 0).is_empty());
    }

    #[test]
    fn test_pin_and_repeat() {
        assert_eq!(
            Rust197Features::pin_and_repeat("task".to_string(), 2),
            vec!["task", "task"]
        );
    }
}
