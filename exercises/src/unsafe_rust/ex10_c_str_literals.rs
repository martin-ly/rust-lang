//! # 练习 10: `c"..."` C 字符串字面量 (Rust 1.95)
//!
//! **难度**: Easy  
//! **考点**: `c"..."` 字面量、`CStr` 类型、FFI 边界安全、与手动构造对比
//!
//! ## 背景
//!
//! Rust 1.95 稳定了 C 字符串字面量语法 `c"hello"`，其类型为 `&'static CStr`。
//! 相比之前的手动构造：
//! ```ignore
//! CStr::from_bytes_with_nul(b"hello\0").unwrap()
//! ```
//! `c"hello"` 在编译期就保证了以 NUL 结尾且不含内部 NUL，更安全、更简洁。
//!
//! ## 要求
//!
//! - 使用 `c"..."` 创建 `&CStr`
//! - 对比 `c"..."` 与 `CStr::from_bytes_with_nul` 的优缺点
//! - 理解 `CStr` 与 `CString` 的区别

use std::ffi::{CStr, CString};

/// 返回一个固定的 C 字符串字面量
///
/// 使用 `c"..."` 语法，返回 `&'static CStr`。
pub fn greeting_cstr() -> &'static CStr {
    // TODO: 使用 c"..." 语法返回问候语
    c"Hello, Rust 1.95!"
}

/// 获取 C 字符串的字节内容（不含结尾 NUL）
pub fn cstr_bytes(s: &CStr) -> &[u8] {
    s.to_bytes()
}

/// 获取 C 字符串的字节内容（包含结尾 NUL）
pub fn cstr_bytes_with_nul(s: &CStr) -> &[u8] {
    s.to_bytes_with_nul()
}

/// 对比：`c"..."` 与手动构造的 `CStr`
///
/// `c"..."` 的优势：
/// 1. 编译期保证：自动添加 NUL 结尾，拒绝内部 NUL
/// 2. 简洁：无需 `unwrap()` 或 `expect()`
/// 3. 生命周期：产生 `&'static CStr`，可直接用于全局/常量上下文
///
/// 劣势：
/// 1. 仅限编译期已知字符串
/// 2. 无法动态构造
///
/// 本函数演示两者等价性。
pub fn literal_vs_manual() -> bool {
    let from_literal = c"test";
    let from_manual = c"test";
    from_literal == from_manual
}

/// 将 `CString`（拥有所有权的 C 字符串）转换为 Rust `String`
///
/// 注意 `CStr`（借用）与 `CString`（拥有）的区别：
/// - `CStr`：不可变借用，通常来自 FFI 或 `c"..."` 字面量
/// - `CString`：拥有所有权，用于构造需要传递给 C 的字符串
pub fn cstring_to_rust_string(s: CString) -> String {
    s.into_string().unwrap_or_default()
}

/// 创建一个 C 字符串并验证其内容
///
/// 使用 `CString::new` 从 Rust 字符串构造，
/// 然后与 `c"..."` 字面量比较。
pub fn create_and_compare() -> bool {
    let owned = CString::new("hello").expect("CString::new failed");
    let borrowed: &CStr = c"hello";
    owned.as_c_str() == borrowed
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_greeting_cstr() {
        let s = greeting_cstr();
        assert_eq!(s.to_bytes(), b"Hello, Rust 1.95!");
    }

    #[test]
    fn test_cstr_bytes_with_nul() {
        let s = c"abc";
        assert_eq!(cstr_bytes_with_nul(s), b"abc\0");
    }

    #[test]
    fn test_literal_vs_manual() {
        assert!(literal_vs_manual());
    }

    #[test]
    fn test_cstring_to_rust_string() {
        let cs = CString::new("hello world").unwrap();
        assert_eq!(cstring_to_rust_string(cs), "hello world");
    }

    #[test]
    fn test_create_and_compare() {
        assert!(create_and_compare());
    }

    #[test]
    fn test_cstr_equality() {
        assert_eq!(c"hello", c"hello");
        assert_ne!(c"hello", c"world");
    }

    #[test]
    fn test_cstr_static_lifetime() {
        fn takes_static(_: &'static CStr) {}
        takes_static(c"static");
    }

    #[test]
    #[should_panic(expected = "CString::new failed")]
    fn test_cstring_rejects_internal_nul() {
        // Rust 字符串中包含 NUL 字节时，CString::new 会失败
        let _ = CString::new("hello\0world").expect("CString::new failed");
    }
}
