//! Rust 1.97 稳定特性 —— 通用工具演示
//! Rust 1.97 stabilized features —— common utilities demonstration
//!
//! 本文件使用 **Rust 1.96.0 等价实现** 演示跨 crate 通用的 Rust 1.97 API 语义。
//! 实际 Rust 1.97 调用以注释形式保留，便于 toolchain 升级后迁移。
//!
//! This module demonstrates general-purpose Rust 1.97 stabilized APIs using
//! equivalent implementations that compile on Rust 1.96.0. The actual Rust 1.97
//! call sites are kept in comments for easy migration once the toolchain is upgraded.

#![allow(clippy::incompatible_msrv)]

use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;
use std::num::NonZeroU32;

/// # Rust 1.97 通用特性演示
/// # Rust 1.97 common feature demonstration
///
/// 跨 crate 通用的 Rust 1.97 API：
/// - `ptr::fn_addr_eq` — 函数指针地址比较
/// - `NonZero*::midpoint` / `NonZero*::isqrt`
/// - `BuildHasherDefault::new` const stable
/// - `mem::size_of_val` / `align_of_val` const stable
pub struct Rust197CommonFeatures;

impl Rust197CommonFeatures {
    /// 比较两个函数指针是否指向同一地址。
    /// Rust 1.97 提供 `std::ptr::fn_addr_eq`，处理比较时可能涉及的 provenance 问题。
    ///
    /// Compares whether two function pointers refer to the same address.
    /// Rust 1.97's `std::ptr::fn_addr_eq` handles provenance concerns portably.
    pub fn compare_fn_pointers(a: fn(), b: fn()) -> bool {
        // Rust 1.97: std::ptr::fn_addr_eq(a, b)
        a as usize == b as usize
    }

    /// 计算两个非零整数的中点，结果仍为非零。
    /// Rust 1.97 提供 `NonZeroU32::midpoint`。
    ///
    /// Computes the midpoint of two non-zero integers, keeping the result non-zero.
    /// Rust 1.97 provides `NonZeroU32::midpoint`.
    pub fn nonzero_midpoint(a: NonZeroU32, b: NonZeroU32) -> NonZeroU32 {
        // Rust 1.97: a.midpoint(b)
        let a_val = a.get();
        let b_val = b.get();
        let mid = (a_val & b_val) + ((a_val ^ b_val) >> 1);
        NonZeroU32::new(mid).unwrap_or(a)
    }

    /// 计算非零整数的整数平方根，结果仍为非零。
    /// Rust 1.97 提供 `NonZeroU32::isqrt`。
    ///
    /// Computes the integer square root of a non-zero integer, keeping the
    /// result non-zero. Rust 1.97 provides `NonZeroU32::isqrt`.
    pub fn nonzero_sqrt(n: NonZeroU32) -> NonZeroU32 {
        // Rust 1.97: n.isqrt()
        let val = n.get();
        let sqrt = if val < 2 {
            val
        } else {
            let mut x = val;
            let mut y = x.div_ceil(2);
            while y < x {
                x = y;
                y = (x + val / x) / 2;
            }
            x
        };
        NonZeroU32::new(sqrt).unwrap_or(n)
    }

    /// 演示在 const 上下文中获取值的大小。
    /// Rust 1.97 将 `mem::size_of_val` 在 const 上下文稳定化。
    ///
    /// Demonstrates obtaining the size of a value in a const context.
    /// Rust 1.97 stabilized `mem::size_of_val` in const contexts.
    pub const fn const_size_of_val<T>(val: &T) -> usize {
        // Rust 1.97: std::mem::size_of_val(val)
        let _ = val;
        std::mem::size_of::<T>()
    }

    /// 演示在 const 上下文中获取值的对齐。
    /// Rust 1.97 将 `mem::align_of_val` 在 const 上下文稳定化。
    ///
    /// Demonstrates obtaining the alignment of a value in a const context.
    /// Rust 1.97 stabilized `mem::align_of_val` in const contexts.
    pub const fn const_align_of_val<T>(val: &T) -> usize {
        // Rust 1.97: std::mem::align_of_val(val)
        let _ = val;
        std::mem::align_of::<T>()
    }

    /// 演示在 const 上下文中构造默认哈希器。
    /// Rust 1.97 将 `BuildHasherDefault::new` 稳定为 `const fn`。
    ///
    /// Demonstrates constructing a default hasher in a const context.
    /// Rust 1.97 stabilized `BuildHasherDefault::new` as a `const fn`.
    pub const fn const_build_hasher_default() -> BuildHasherDefault<DefaultHasher> {
        // Rust 1.97: BuildHasherDefault::new()
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
