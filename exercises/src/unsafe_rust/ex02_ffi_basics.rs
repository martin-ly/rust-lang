//! # 练习 2: FFI 边界安全封装 / Exercise 2: FFI Boundary Safe Wrapping
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: `extern "C"`、原始指针解引用、C 字符串与 Rust 字符串的安全转换
//!   `extern "C"`, raw pointer dereference, safe C string to Rust string conversion
//!
//! ## 题目描述 / Problem Description
//!
//! C 标准库提供 `strlen` 函数用于计算以空字符结尾的 C 字符串长度。
//! The C standard library provides `strlen` to calculate the length of a NUL-terminated C string.
//! 其签名如下 / Its signature is:
//!
//! ```c
//! size_t strlen(const char *s);
//! ```
//!
//! 请完成以下任务 / Please complete the following tasks:
//! 1. 声明 `strlen` 的 FFI 绑定 / Declare the FFI binding for `strlen`
//! 2. 封装一个安全的 Rust 函数 `c_string_length`，接受 `&CStr` 并返回长度
//!    Wrap a safe Rust function `c_string_length` accepting `&CStr` and returning length
//! 3. 封装一个更高级的函数 `rust_string_to_c_length`，接受 `&str` 并返回其 C 字符串长度
//!    Wrap a higher-level function `rust_string_to_c_length` accepting `&str` and returning C string length
//!
//! ## 要求 / Requirements
//!
//! - 所有 `unsafe` 操作必须限制在 FFI 边界层
//!   All `unsafe` operations must be confined to the FFI boundary layer
//! - 公开 API 必须是 safe 的
//!   Public API must be safe
//! - 正确处理 C 字符串的生命周期和空终止符
//!   Correctly handle C string lifetimes and null terminators
//!
//! ## 提示 / Hints
//!
//! - `std::ffi::CStr` 已经保证了内部不包含内部 NUL 字节且以 NUL 结尾
//!   `std::ffi::CStr` already guarantees no interior NUL bytes and NUL termination
//! - `CStr::as_ptr()` 返回 `*const c_char`，可直接传递给 `strlen`
//!   `CStr::as_ptr()` returns `*const c_char`, directly passable to `strlen`
//! - `libc::c_char` 的类型在不同平台下可能是 `i8` 或 `u8`
//!   `libc::c_char` may be `i8` or `u8` depending on platform

use std::ffi::CStr;
use std::os::raw::c_char;

// C 标准库 `strlen` 的 FFI 声明
// FFI declaration for C standard library `strlen`
// SAFETY: `s` 必须指向一个以 NUL 结尾的有效 C 字符串
// SAFETY: `s` must point to a valid NUL-terminated C string
unsafe extern "C" {
    fn strlen(s: *const c_char) -> usize;
}

/// 安全地计算 C 字符串的长度（不包含结尾 NUL）
/// Safely calculates the length of a C string (excluding terminating NUL)
///
/// # 安全性说明 / Safety Note
///
/// 由于 `CStr` 类型已经保证了内部数据是有效的以 NUL 结尾的 C 字符串，
/// Since `CStr` already guarantees valid NUL-terminated C string data,
/// 因此调用 `strlen` 是安全的。
/// calling `strlen` is safe.
pub fn c_string_length(s: &CStr) -> usize {
    // SAFETY: CStr 保证指针指向以 NUL 结尾的有效 C 字符串
    // SAFETY: CStr guarantees pointer points to a valid NUL-terminated C string
    unsafe { strlen(s.as_ptr()) }
}

/// 将 Rust 字符串转换为临时 C 字符串，并计算其 C 长度
/// Converts a Rust string to a temporary C string and calculates its C length
///
/// 注意：此函数展示了如何通过 `CString` 进行中转。
/// Note: This function demonstrates conversion via `CString`.
/// 实际生产代码中应直接使用 `CString` 或保持 `CStr` 引用。
/// In production, use `CString` directly or keep `CStr` references.
pub fn rust_string_to_c_length(s: &str) -> usize {
    let c_string =
        std::ffi::CString::new(s).expect("字符串中包含 NUL 字节 / String contains NUL bytes");
    c_string_length(&c_string)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_c_string_length_ascii() {
        let cstr = c"hello";
        assert_eq!(c_string_length(cstr), 5);
    }

    #[test]
    fn test_c_string_length_empty() {
        let cstr = c"";
        assert_eq!(c_string_length(cstr), 0);
    }

    #[test]
    fn test_rust_string_to_c_length() {
        assert_eq!(rust_string_to_c_length("Rust"), 4);
        assert_eq!(rust_string_to_c_length("FFI边界"), 9); // UTF-8 编码，3字节/中文字符 / UTF-8, 3 bytes per CJK char
    }

    #[test]
    #[should_panic(expected = "字符串中包含 NUL 字节")]
    fn test_rust_string_with_nul_panics() {
        let _ = rust_string_to_c_length("hello\0world");
    }
}
