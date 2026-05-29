//! Rust 1.97 特性跟踪模块 —— 通用工具
#![allow(clippy::incompatible_msrv)]

use std::num::NonZeroU32;

/// # Rust 1.97 通用特性演示
///
/// 跨 crate 通用的 Rust 1.97 API：
/// - `ptr::fn_addr_eq` — 函数指针地址比较
/// - `NonZero*::midpoint` / `NonZero*::isqrt`
/// - `BuildHasherDefault::new` const stable
/// - `mem::size_of_val` / `align_of_val` const stable
pub struct Rust197CommonFeatures;

impl Rust197CommonFeatures {
    /// 使用 `ptr::fn_addr_eq` 比较两个函数指针是否指向同一地址
    ///
    /// 替代不稳定的 `==` 比较，提供定义明确的函数指针等价性检查。
    pub fn compare_fn_pointers(a: fn(), b: fn()) -> bool {
        std::ptr::fn_addr_eq(a, b)
    }

    /// 使用 `NonZeroU32::midpoint` 计算非零整数中点
    pub fn nonzero_midpoint(a: NonZeroU32, b: NonZeroU32) -> NonZeroU32 {
        a.midpoint(b)
    }

    /// 使用 `NonZeroU32::isqrt` 计算非零整数平方根
    pub fn nonzero_sqrt(n: NonZeroU32) -> NonZeroU32 {
        n.isqrt()
    }

    /// 演示 `mem::size_of_val` 在 const 上下文中的使用
    pub const fn const_size_of_val<T>(val: &T) -> usize {
        std::mem::size_of_val(val)
    }

    /// 演示 `mem::align_of_val` 在 const 上下文中的使用
    pub const fn const_align_of_val<T>(val: &T) -> usize {
        std::mem::align_of_val(val)
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
}
