//! Rust 191.0 新特性实现模块 —— c06_async
//!
//! 本模块展示了 Rust 191.0 (2025-10-30) 的关键语言特性和工具链改进。
//!
//! - `c_variadic`: C 风格变参函数声明稳定
//! - `aarch64_windows_tier1`: `aarch64-pc-windows-msvc` 晋升 Tier 1
//!
//! # 版本信息
//! - Rust 版本: 191.0
//! - 稳定日期: 2025-10-30
//! - Edition: 2024

// ============================================================================
// 1. C 风格变参函数声明稳定
// ============================================================================

/// # C 风格变参函数（C Variadic Functions）
///
/// Rust 1.91.0 稳定了 C 风格变参函数的声明，允许 Rust 函数接受可变数量的参数，
/// 使用 C ABI 与 C 的 `...` 语法兼容。
///
/// ## 声明方式
/// ```ignore
/// unsafe extern "C" fn printf(fmt: *const c_char, ...) { }
/// ```
///
/// ## 使用场景
/// - 实现 C 标准库函数（如 `printf`、`scanf`）的 Rust 包装
/// - 与使用变参的 C 库直接交互
/// - 编写兼容 C 的插件接口
///
/// ## 限制
/// - 仅在 `extern "C"` 函数中可用
/// - 必须使用 `unsafe`（因为编译器无法验证变参类型安全）
/// - 变参访问需通过 `core::ffi::VaList`（或 `std` 中的等效类型）
///
/// **注意**：截至 Rust 1.95.0 stable，`c_variadic` 特性尚未完全稳定。
/// 以下代码需要 nightly 工具链才能编译。
///
/// ```ignore
/// use std::ffi::{c_char, c_int, VaList};
///
/// unsafe extern "C" fn rust_printf(fmt: *const c_char, mut args: ...) -> c_int {
///     let mut ap: VaList = args.clone();
///     let _ = ap.arg::<c_int>();
///     0
/// }
/// ```
pub fn c_variadic_doc_placeholder() -> &'static str {
    "c_variadic requires nightly Rust; see documentation above"
}

#[test]
fn test_c_variadic_placeholder() {
    assert_eq!(c_variadic_doc_placeholder(), "c_variadic requires nightly Rust; see documentation above");
}

// ============================================================================
// 2. `aarch64-pc-windows-msvc` 晋升 Tier 1
// ============================================================================

/// # `aarch64-pc-windows-msvc` 晋升 Tier 1
///
/// Rust 1.91.0 将 `aarch64-pc-windows-msvc`（Windows on ARM64）
/// 提升为 **Tier 1 支持平台**，意味着：
/// - 所有稳定版都提供预编译二进制
/// - 通过完整 CI 测试
/// - 保证与 x86_64 Windows 相同的稳定性
///
/// ## 影响
/// - Windows ARM 设备（如 Surface Pro X、Snapdragon X Elite PC）
///   可直接使用官方 Rust 工具链，无需交叉编译
/// - `cargo build --target aarch64-pc-windows-msvc` 获得一级支持
///
/// ## 交叉编译对比
/// | 平台 | Tier | 预编译二进制 | 测试覆盖 |
/// |------|------|-------------|---------|
/// | x86_64-pc-windows-msvc | 1 | ✅ | ✅ |
/// | aarch64-pc-windows-msvc | 1 | ✅ (1.91+) | ✅ |
/// | i686-pc-windows-msvc | 1 | ✅ | ✅ |
pub fn aarch64_tier1_status() -> &'static str {
    "aarch64-pc-windows-msvc is Tier 1 since Rust 1.91.0"
}

#[test]
#[cfg(target_arch = "aarch64")]
#[cfg(target_os = "windows")]
fn test_aarch64_windows_native() {
    assert_eq!(aarch64_tier1_status(), "aarch64-pc-windows-msvc is Tier 1 since Rust 1.91.0");
}
