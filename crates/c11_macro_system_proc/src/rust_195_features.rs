//! Rust 1.95 特性 —— 过程宏场景
//! Rust 1.95 feature —— scenario
#![allow(dead_code)]

use std::ffi::CStr;

/// # 真实 Rust 1.95 特性演示
/// # real Rust 1.95 feature demonstration
pub struct RealRust195Features;

impl RealRust195Features {
    /// 在宏上下文中使用 `const {}` 块
    /// in on under in `const {}`
    pub fn const_block_in_macro_context() -> usize {
        const { 42 }
    }

    /// 使用 `c"proc_macro"` 表示过程宏名称
    /// `c"proc_macro"` represent
    pub fn c_str_for_proc_macro() -> &'static CStr {
        c"proc_macro"
    }
}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_const_block_in_macro_context() {
        assert_eq!(RealRust195Features::const_block_in_macro_context(), 42);
    }

    #[test]
    fn test_c_str_for_proc_macro() {
        assert_eq!(
            RealRust195Features::c_str_for_proc_macro().to_str(),
            Ok("proc_macro")
        );
    }
}
