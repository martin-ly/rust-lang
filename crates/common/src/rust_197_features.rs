//! Rust 1.97.0 stable 特性 —— 通用工具演示
//! Rust 1.97.0 stable features —— common utilities demonstration
//!
//! 本文件直接调用 Rust 1.97.0 stable API 演示相关语义，不再保留 nightly 分支与等效实现。
//!
//! This module directly uses Rust 1.97.0 stable APIs; no `#[cfg(nightly)]` shims
//! or equivalent fallback implementations are kept.

use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;
use std::num::NonZeroU32;

/// # Rust 1.97 通用特性演示
/// # Rust 1.97 common feature demonstration
///
/// 跨 crate 通用的 Rust 1.97.0 stable API：
/// - `ptr::fn_addr_eq` — 函数指针地址比较
/// - `NonZero*::midpoint` / `NonZero*::isqrt`
/// - `BuildHasherDefault::new` const stable
/// - `mem::size_of_val` / `align_of_val` const stable
pub struct Rust197CommonFeatures;

impl Rust197CommonFeatures {
    /// 比较两个函数指针是否指向同一地址。
    ///
    /// Rust 1.97.0 stable 提供 `std::ptr::fn_addr_eq`，处理比较时可能涉及的 provenance 问题。
    pub fn compare_fn_pointers(a: fn(), b: fn()) -> bool {
        std::ptr::fn_addr_eq(a, b)
    }

    /// 计算两个非零整数的中点，结果仍为非零。
    ///
    /// Rust 1.97.0 stable 提供 `NonZeroU32::midpoint`。
    pub fn nonzero_midpoint(a: NonZeroU32, b: NonZeroU32) -> NonZeroU32 {
        a.midpoint(b)
    }

    /// 计算非零整数的整数平方根，结果仍为非零。
    ///
    /// Rust 1.97.0 stable 提供 `NonZeroU32::isqrt`。
    pub fn nonzero_sqrt(n: NonZeroU32) -> NonZeroU32 {
        n.isqrt()
    }

    /// 演示在 const 上下文中获取值的大小。
    ///
    /// Rust 1.97.0 将 `std::mem::size_of_val` 在 const 上下文稳定化。
    pub const fn const_size_of_val<T>(val: &T) -> usize {
        std::mem::size_of_val(val)
    }

    /// 演示在 const 上下文中获取值的对齐。
    ///
    /// Rust 1.97.0 将 `std::mem::align_of_val` 在 const 上下文稳定化。
    pub const fn const_align_of_val<T>(val: &T) -> usize {
        std::mem::align_of_val(val)
    }

    /// 演示在 const 上下文中构造默认哈希器。
    ///
    /// Rust 1.97.0 将 `BuildHasherDefault::new` 稳定为 `const fn`。
    pub const fn const_build_hasher_default() -> BuildHasherDefault<DefaultHasher> {
        BuildHasherDefault::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_fn() {}

    #[test]
    fn test_compare_fn_pointers_same() {
        assert!(Rust197CommonFeatures::compare_fn_pointers(
            sample_fn, sample_fn
        ));
    }

    #[test]
    fn test_compare_fn_pointers_same_value() {
        // 两个相同的函数指针应该相等
        // Two references to the same function pointer should compare equal.
        assert!(Rust197CommonFeatures::compare_fn_pointers(
            sample_fn, sample_fn
        ));
    }

    #[test]
    fn test_nonzero_midpoint() {
        let a = NonZeroU32::new(10).unwrap();
        let b = NonZeroU32::new(20).unwrap();
        assert_eq!(Rust197CommonFeatures::nonzero_midpoint(a, b).get(), 15);
    }

    #[test]
    fn test_nonzero_sqrt() {
        let n = NonZeroU32::new(25).unwrap();
        assert_eq!(Rust197CommonFeatures::nonzero_sqrt(n).get(), 5);
    }

    #[test]
    fn test_const_size_of_val() {
        let x = 42u64;
        assert_eq!(Rust197CommonFeatures::const_size_of_val(&x), 8);
    }

    #[test]
    fn test_const_align_of_val() {
        let x = 42u64;
        assert_eq!(Rust197CommonFeatures::const_align_of_val(&x), 8);
    }

    #[test]
    fn test_const_build_hasher_default() {
        let _hasher = Rust197CommonFeatures::const_build_hasher_default();
    }
}
