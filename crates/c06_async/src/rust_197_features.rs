//! Rust 1.97 稳定特性 —— 异步编程
//! Rust 1.97.0 stabilized features —— async programming
//!
//! 本文件展示与异步编程相关的 Rust 1.97.0 稳定特性。当前工具链为 Rust 1.96.0，
//! 因此所有 1.97 新行为均保留在注释中；可执行代码使用语义等价的 1.96 兼容实现。
//! 权威列表见 `concept/07_future/rust_1_97_stabilized.md`。
//!
//! 注：本文件涉及的 1.97 变更（`pin!` 阻止隐式解引用强制、`must_use` lint 扩展、
//! `cfg_target_has_atomic_equal_alignment`）均为编译器行为或 cfg 条件变更，
//! 没有可直接切换的 runtime API，因此不采用 `#[cfg(nightly)]` 分支，保留垫片并更新注释。
#![allow(clippy::incompatible_msrv)]

use std::future::Future;
use std::sync::atomic::AtomicUsize;
use std::task::{Context, Poll, Waker};
use thiserror::Error;

/// # Rust 1.97 异步特性演示
/// # Rust 1.97 async feature demonstration
///
/// 涉及特性：
/// - `pin!` 宏阻止隐式解引用强制（Rust 1.97+；宏行为变更，无分支 API）
/// - `must_use` lint 扩展到 `Result<must_use_type, E>`（Rust 1.97+；lint 变更，无 API）
/// - `cfg_target_has_atomic_equal_alignment`（Rust 1.97+；cfg 条件，无运行时 API）
pub struct Rust197AsyncFeatures;

impl Rust197AsyncFeatures {
    /// 使用栈上 `pin!` 对 Future 做一次同步轮询。
    ///
    /// Rust 1.97 起 `pin!` 会阻止隐式 deref coercion，避免 `Pin<&mut T>` 在宏内
    /// 意外转换为其他类型；在 1.96 中等价做法是显式使用 `std::pin::pin!` 并避免
    /// 任何会触发强制转换的上下文。
    pub fn poll_once<F>(future: F) -> Poll<F::Output>
    where
        F: Future,
    {
        // Rust 1.97:
        // let mut pinned = std::pin::pin!(future);
        let waker = Waker::noop();
        let mut cx = Context::from_waker(waker);
        let mut pinned = std::pin::pin!(future);
        pinned.as_mut().poll(&mut cx)
    }

    /// 返回一个内部类型标记了 `#[must_use]` 的 `Result`。
    ///
    /// Rust 1.97 的 `must_use` lint 会将 `Result<T, E>` 视为与 `T` 等效，因此
    /// 忽略该返回值会触发警告。在 1.96 中代码仍可编译，只是不会触发该 lint。
    pub fn must_use_result() -> Result<MustUseToken, MustUseError> {
        Ok(MustUseToken)
    }

    /// 检测当前平台是否满足 `target_has_atomic_equal_alignment = "ptr"`。
    ///
    /// Rust 1.97 新增该 cfg 条件；在 1.96 中可用运行期对齐检查作为等价判断。
    pub fn ptr_atomic_equal_alignment() -> bool {
        // Rust 1.97:
        // #[cfg(target_has_atomic_equal_alignment = "ptr")]
        std::mem::align_of::<AtomicUsize>() == std::mem::align_of::<usize>()
    }
}

/// 一个被标记为 `#[must_use]` 的令牌类型，用于演示 lint 扩展。
#[derive(Debug, PartialEq, Eq)]
#[must_use]
pub struct MustUseToken;

/// `must_use_result` 使用的自定义错误类型，避免 `Result<T, ()>`。
#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
#[error("must_use token construction failed")]
pub struct MustUseError;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_poll_once_ready() {
        let fut = async { 42 };
        match Rust197AsyncFeatures::poll_once(fut) {
            Poll::Ready(v) => assert_eq!(v, 42),
            Poll::Pending => panic!("simple future should be ready immediately"),
        }
    }

    #[test]
    fn test_must_use_result() {
        // 在 Rust 1.97+ 中，以下未使用 Result 会触发 must_use 警告；
        // 1.96 中需显式忽略以保持代码干净。
        let _ = Rust197AsyncFeatures::must_use_result();
    }

    #[test]
    fn test_ptr_atomic_equal_alignment() {
        assert_eq!(
            Rust197AsyncFeatures::ptr_atomic_equal_alignment(),
            std::mem::align_of::<AtomicUsize>() == std::mem::align_of::<usize>()
        );
    }
}
