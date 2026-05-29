//! Rust 1.97 特性跟踪模块 —— 异步编程
#![allow(clippy::incompatible_msrv)]

use std::future::Future;
use std::task::{Context, Poll, Waker};

/// # Rust 1.97 异步特性演示
///
/// Rust 1.97 稳定化的核心异步 API：
/// - `AsyncFn*` trait family 加入 prelude（所有 edition）
/// - `std::task::Waker::noop` — 无操作 Waker，用于不需要唤醒的上下文
pub struct Rust197AsyncFeatures;

impl Rust197AsyncFeatures {
    /// 使用 `Waker::noop()` 创建一个不需要唤醒的 Context
    ///
    /// 适用于同步轮询（polling）场景，例如测试或已知不会阻塞的 Future。
    pub fn poll_with_noop_waker<F>(future: F) -> Poll<F::Output>
    where
        F: Future,
    {
        let waker = Waker::noop();
        let mut cx = Context::from_waker(waker);
        let mut pinned = std::pin::pin!(future);
        pinned.as_mut().poll(&mut cx)
    }

    /// 演示 `AsyncFn` trait 的使用（Rust 1.97+ 在 prelude 中可用）
    ///
    /// `AsyncFn` 允许像调用普通闭包一样调用异步闭包。
    pub async fn call_async_closure<F>(f: F, arg: i32) -> i32
    where
        F: AsyncFn(i32) -> i32,
    {
        f(arg).await
    }

    /// 演示 `AsyncFnMut` trait 的使用
    pub async fn call_async_mut_closure<F>(mut f: F, arg: i32) -> i32
    where
        F: AsyncFnMut(i32) -> i32,
    {
        f(arg).await
    }

    /// 演示 `AsyncFnOnce` trait 的使用
    pub async fn call_async_once_closure<F>(f: F, arg: i32) -> i32
    where
        F: AsyncFnOnce(i32) -> i32,
    {
        f(arg).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_poll_with_noop_waker() {
        let fut = async { 42 };
        match Rust197AsyncFeatures::poll_with_noop_waker(fut) {
            Poll::Ready(v) => assert_eq!(v, 42),
            Poll::Pending => panic!("simple future should be ready immediately"),
        }
    }

    #[tokio::test]
    async fn test_call_async_closure() {
        let closure = async |x: i32| x * 2;
        let result = Rust197AsyncFeatures::call_async_closure(closure, 21).await;
        assert_eq!(result, 42);
    }

    #[tokio::test]
    async fn test_call_async_mut_closure() {
        let mut count = 0;
        let closure = async |x: i32| {
            count += x;
            count
        };
        let result = Rust197AsyncFeatures::call_async_mut_closure(closure, 10).await;
        assert_eq!(result, 10);
    }

    #[tokio::test]
    async fn test_call_async_once_closure() {
        let closure = async |x: i32| x + 1;
        let result = Rust197AsyncFeatures::call_async_once_closure(closure, 41).await;
        assert_eq!(result, 42);
    }
}
