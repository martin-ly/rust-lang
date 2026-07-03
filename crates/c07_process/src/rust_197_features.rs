//! Rust 1.97 稳定特性 —— 进程与 FFI
//! Rust 1.97.0 stabilized features —— process and FFI
//!
//! 本文件展示与进程管理、FFI 和系统编程相关的 Rust 1.97.0 稳定特性。
//! 当前工具链为 Rust 1.96.0，所有 1.97 新 API 调用均保留在 `#[cfg(nightly)]` 分支；
//! 可执行代码使用语义等价的 1.96 兼容实现。
//! 权威列表见 `concept/07_future/rust_1_97_stabilized.md`。
#![allow(clippy::incompatible_msrv)]
#![allow(unexpected_cfgs)]
#![allow(clippy::borrowed_box)]

use std::io;

/// # Rust 1.97 进程/FFI 特性演示
/// # Rust 1.97 process/FFI feature demonstration
///
/// 涉及特性：
/// - `std::ptr::fn_addr_eq`（Rust 1.97+）：可移植的函数指针地址比较
/// - Windows `WSAESHUTDOWN` 正确映射为 `io::ErrorKind::BrokenPipe`（Rust 1.97+，行为变更，无 API）
pub struct Rust197ProcessFeatures;

impl Rust197ProcessFeatures {
    /// 比较两个函数指针的地址是否相等。
    ///
    /// Rust 1.97 使用 `std::ptr::fn_addr_eq(f1, f2)` 处理 provenance 问题；
    /// 在 1.96 中可转换为裸指针 `*const ()` 后比较。
    #[allow(clippy::fn_to_numeric_cast_any)]
    #[cfg(nightly)]
    pub fn function_pointers_equal<A, R>(f1: fn(A) -> R, f2: fn(A) -> R) -> bool {
        std::ptr::fn_addr_eq(f1, f2)
    }

    #[allow(clippy::fn_to_numeric_cast_any)]
    #[cfg(not(nightly))]
    pub fn function_pointers_equal<A, R>(f1: fn(A) -> R, f2: fn(A) -> R) -> bool {
        std::ptr::eq(f1 as *const (), f2 as *const ())
    }

    /// 将 Windows 套接字错误 `WSAESHUTDOWN` 映射为 `BrokenPipe`。
    ///
    /// Rust 1.97 起 `io::Error::from_raw_os_error(WSAESHUTDOWN).kind()` 会返回
    /// `io::ErrorKind::BrokenPipe`。在 1.96 中等价做法是检查原始错误码并手动映射。
    pub fn wsa_shutdown_error_kind() -> io::ErrorKind {
        const WSAESHUTDOWN: i32 = 10058;
        let err = io::Error::from_raw_os_error(WSAESHUTDOWN);
        // Rust 1.97:
        // err.kind() == io::ErrorKind::BrokenPipe
        match err.raw_os_error() {
            Some(WSAESHUTDOWN) => io::ErrorKind::BrokenPipe,
            _ => err.kind(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn add_one(x: i32) -> i32 {
        x + 1
    }
    fn add_two(x: i32) -> i32 {
        x + 2
    }

    #[test]
    fn test_function_pointers_equal() {
        assert!(Rust197ProcessFeatures::function_pointers_equal(
            add_one, add_one
        ));
        assert!(!Rust197ProcessFeatures::function_pointers_equal(
            add_one, add_two
        ));
    }

    #[test]
    fn test_wsa_shutdown_error_kind() {
        assert_eq!(
            Rust197ProcessFeatures::wsa_shutdown_error_kind(),
            io::ErrorKind::BrokenPipe
        );
    }
}
