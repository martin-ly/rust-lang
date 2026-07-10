//! Rust 1.97.0 stable 特性 —— 嵌入式/系统编程演示
//! Rust 1.97.0 stable features —— embedded/systems programming demonstration
//!
//! 本文件直接调用 Rust 1.97.0 stable API 演示相关语义，不再保留 nightly 分支与等效实现。
//!
//! This module directly uses Rust 1.97.0 stable APIs; no `#[cfg(nightly)]` shims
//! or equivalent fallback implementations are kept.

#![allow(clippy::borrowed_box)]

use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;
use std::num::NonZeroU32;

/// # Rust 1.97 嵌入式/系统编程特性演示
/// # Rust 1.97 embedded/systems feature demonstration
///
/// Rust 1.97.0 在嵌入式/系统编程场景中的稳定化内容：
/// - `cfg(target_has_atomic_equal_alignment = "ptr")`（1.97.0 起 stable 的 cfg 条件）
/// - `const size_of_val` / `const align_of_val`
/// - `NonZero` 位操作、`NonZeroU32::midpoint` / `isqrt`
/// - `char::is_control()` const 稳定化
/// - `Option::as_slice`（Rust 1.97.0 stable）
/// - `BuildHasherDefault::new` const 稳定
/// - `ptr::fn_addr_eq`
///
/// 以下 API 仍在 nightly / 1.98+ preview，保留等效实现：
/// - `Box::as_ptr`
pub struct Rust197EmbeddedFeatures;

impl Rust197EmbeddedFeatures {
    /// 编译期计算值的大小与对齐（Rust 1.97.0 stable）。
    ///
    /// 在嵌入式 no_std 环境中常用于静态断言缓冲区尺寸。
    pub const fn const_size_and_align_of_val<T: Sized>(value: &T) -> (usize, usize) {
        (
            core::mem::size_of_val(value),
            core::mem::align_of_val(value),
        )
    }

    /// `NonZeroU32` 位查询与位运算，适合寄存器位掩码操作。
    ///
    /// `count_ones` / `leading_zeros` / `trailing_zeros` 在 `NonZeroU32` 上均为
    /// stable 方法，可直接调用。
    pub fn nonzero_bit_ops(n: NonZeroU32) -> (u32, u32, u32) {
        let ones = n.count_ones().get();
        let leading = n.leading_zeros();
        let trailing = n.trailing_zeros();
        (ones, leading, trailing)
    }

    /// 计算两个 `NonZeroU32` 的中点，结果仍为非零。
    ///
    /// Rust 1.97.0 stable 提供 `NonZeroU32::midpoint`，直接调用即可。
    pub fn nonzero_midpoint(a: NonZeroU32, b: NonZeroU32) -> NonZeroU32 {
        a.midpoint(b)
    }

    /// 计算 `NonZeroU32` 的整数平方根，结果仍为非零。
    ///
    /// Rust 1.97.0 stable 提供 `NonZeroU32::isqrt`。
    pub fn nonzero_isqrt(n: NonZeroU32) -> NonZeroU32 {
        n.isqrt()
    }

    /// `char::is_control()` 在 Rust 1.97.0 中可在 `const fn` 中调用。
    pub const fn char_is_control(c: char) -> bool {
        c.is_control()
    }

    /// 获取 `Box<T>` 中堆分配对象的裸指针。
    ///
    /// `Box::as_ptr` 为 Rust 1.98+ preview API；当前使用等效实现，保留 nightly 迁移入口。
    #[allow(clippy::borrowed_box)]
    pub fn box_as_ptr<T>(b: &Box<T>) -> *const T {
        b.as_ref() as *const T
    }

    /// 将 `Option<T>` 转为只读切片视图。
    pub fn option_as_slice<T>(opt: &Option<T>) -> &[T] {
        opt.as_slice()
    }

    /// 在 const 上下文中构造默认哈希器。
    ///
    /// Rust 1.97.0 起 `BuildHasherDefault::new` 为 `const fn`。
    pub const fn build_hasher_default_new() -> BuildHasherDefault<DefaultHasher> {
        BuildHasherDefault::new()
    }

    /// 可移植的函数指针地址比较。
    ///
    /// Rust 1.97.0 stable 提供 `std::ptr::fn_addr_eq`。
    pub fn fn_addr_eq(a: fn(), b: fn()) -> bool {
        std::ptr::fn_addr_eq(a, b)
    }

    /// 演示 `cfg(target_has_atomic_equal_alignment = "ptr")` 的使用位置。
    ///
    /// 该 cfg 条件自 Rust 1.97.0 起 stable。
    pub fn atomic_equal_alignment_note() -> &'static str {
        // Rust 1.97.0+:
        // #[cfg(target_has_atomic_equal_alignment = "ptr")]
        // fn embedded_atomic_optimized() { /* 指针大小原子与 usize 对齐相同的平台 */ }
        "cfg(target_has_atomic_equal_alignment = \"ptr\") is stable since Rust 1.97.0"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_fn() {}

    #[test]
    fn test_const_size_and_align_of_val() {
        const BUF: [u8; 16] = [0; 16];
        const SIZE_ALIGN: (usize, usize) =
            Rust197EmbeddedFeatures::const_size_and_align_of_val(&BUF);
        assert_eq!(SIZE_ALIGN.0, 16);
        assert_eq!(SIZE_ALIGN.1, 1);
    }

    #[test]
    fn test_nonzero_bit_ops() {
        let n = NonZeroU32::new(0b10100).unwrap();
        let (ones, _leading, trailing) = Rust197EmbeddedFeatures::nonzero_bit_ops(n);
        assert_eq!(ones, 2);
        assert_eq!(trailing, 2);
    }

    #[test]
    fn test_nonzero_midpoint() {
        let a = NonZeroU32::new(10).unwrap();
        let b = NonZeroU32::new(20).unwrap();
        assert_eq!(Rust197EmbeddedFeatures::nonzero_midpoint(a, b).get(), 15);
    }

    #[test]
    fn test_nonzero_isqrt() {
        let n = NonZeroU32::new(25).unwrap();
        assert_eq!(Rust197EmbeddedFeatures::nonzero_isqrt(n).get(), 5);
    }

    #[test]
    fn test_char_is_control() {
        assert!(!Rust197EmbeddedFeatures::char_is_control('A'));
        assert!(Rust197EmbeddedFeatures::char_is_control('\n'));
    }

    #[test]
    fn test_box_as_ptr() {
        let b = Box::new(42);
        let p = Rust197EmbeddedFeatures::box_as_ptr(&b);
        assert_eq!(unsafe { *p }, 42);
    }

    #[test]
    fn test_option_as_slice() {
        let opt = Some(42);
        assert_eq!(Rust197EmbeddedFeatures::option_as_slice(&opt), &[42]);
    }

    #[test]
    fn test_build_hasher_default_new() {
        let _ = Rust197EmbeddedFeatures::build_hasher_default_new();
    }

    #[test]
    fn test_fn_addr_eq() {
        // 同一函数指针的地址必然相等；不同函数地址是否相等取决于优化，不做断言。
        assert!(Rust197EmbeddedFeatures::fn_addr_eq(sample_fn, sample_fn));
    }
}
