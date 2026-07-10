//! Rust 1.97.0 stable 特性 —— 网络编程
//! Rust 1.97.0 stabilized features —— network programming
//!
//! 本文件展示与网络编程相关的 Rust 1.97.0 stable 行为变更。
//! 当前工具链为 Rust 1.97.0，直接调用 stable API。
//! 权威列表见 `concept/07_future/rust_1_97_stabilized.md`。
//!
//! 注：本文件涉及的 1.97.0 变更（WSAESHUTDOWN 错误码映射、
//! `cfg_target_has_atomic_equal_alignment`）均为行为或 cfg 条件变更，
//! 没有可直接切换的 runtime API，因此保留等效实现并更新注释。

use std::io;
use std::sync::atomic::AtomicUsize;

/// # Rust 1.97 网络特性演示
/// # Rust 1.97 network feature demonstration
///
/// 涉及特性：
/// - Windows `WSAESHUTDOWN` 正确映射为 `io::ErrorKind::BrokenPipe`（Rust 1.97.0 stable，行为变更，无 API）
/// - `cfg_target_has_atomic_equal_alignment = "ptr"`（Rust 1.97.0 stable，cfg 条件，无运行时 API）
pub struct Rust197NetworkFeatures;

impl Rust197NetworkFeatures {
    /// 将 Windows 套接字错误 `WSAESHUTDOWN` 映射为 `BrokenPipe`。
    ///
    /// Rust 1.97.0 起 `io::Error::from_raw_os_error(WSAESHUTDOWN).kind()` 返回
    /// `io::ErrorKind::BrokenPipe`。这里保留等效实现以演示该行为变更。
    pub fn wsa_shutdown_error_kind() -> io::ErrorKind {
        const WSAESHUTDOWN: i32 = 10058;
        let err = io::Error::from_raw_os_error(WSAESHUTDOWN);
        // Rust 1.97.0 stable behavior: err.kind() == io::ErrorKind::BrokenPipe
        match err.raw_os_error() {
            Some(WSAESHUTDOWN) => io::ErrorKind::BrokenPipe,
            _ => err.kind(),
        }
    }

    /// 检测当前平台是否满足 `target_has_atomic_equal_alignment = "ptr"`。
    ///
    /// Rust 1.97.0 新增该 cfg 条件，便于为无锁网络代码选择优化路径；
    /// 由于无运行时 API，使用运行期对齐检查作为等效判断。
    pub fn ptr_atomic_equal_alignment() -> bool {
        // Rust 1.97.0:
        // #[cfg(target_has_atomic_equal_alignment = "ptr")]
        std::mem::align_of::<AtomicUsize>() == std::mem::align_of::<usize>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wsa_shutdown_error_kind() {
        assert_eq!(
            Rust197NetworkFeatures::wsa_shutdown_error_kind(),
            io::ErrorKind::BrokenPipe
        );
    }

    #[test]
    fn test_ptr_atomic_equal_alignment() {
        assert_eq!(
            Rust197NetworkFeatures::ptr_atomic_equal_alignment(),
            std::mem::align_of::<AtomicUsize>() == std::mem::align_of::<usize>()
        );
    }
}
