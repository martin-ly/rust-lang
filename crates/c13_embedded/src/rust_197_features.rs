//! Rust 1.97 稳定特性 —— 嵌入式/系统编程演示
//! Rust 1.97 stabilized features —— embedded/systems programming demonstration
//!
//! 本文件使用 **Rust 1.96.0 等价实现** 演示 Rust 1.97.0 稳定 API 的语义。
//! 实际 Rust 1.97 调用以注释形式保留，便于 toolchain 升级后直接替换。
//!
//! This module demonstrates Rust 1.97.0 stabilized APIs using equivalent
//! implementations that compile on Rust 1.96.0. The actual Rust 1.97 call
//! sites are kept in comments for migration reference.

#![allow(clippy::incompatible_msrv)]

use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;
use std::num::NonZeroU32;

/// # Rust 1.97 嵌入式/系统编程特性演示
/// # Rust 1.97 embedded/systems feature demonstration
///
/// Rust 1.97.0 在嵌入式/系统编程场景中的稳定化内容：
/// - `cfg(target_has_atomic_equal_alignment = "ptr")`
/// - `const size_of_val` / `const align_of_val`
/// - `NonZero` 位操作、`NonZeroU32::midpoint` / `isqrt`
/// - `char::is_control()` const 稳定化
/// - `Box::as_ptr`
/// - `Option::as_slice`
/// - `BuildHasherDefault::new` const 稳定
/// - `ptr::fn_addr_eq`
pub struct Rust197EmbeddedFeatures;

impl Rust197EmbeddedFeatures {
    /// 编译期计算值的大小与对齐（1.96 兼容版，仅支持 `Sized` 类型）。
    ///
    /// 在嵌入式 no_std 环境中常用于静态断言缓冲区尺寸。
    pub const fn const_size_and_align_of_val<T: Sized>(_: &T) -> (usize, usize) {
        // 1.97+: (core::mem::size_of_val(value), core::mem::align_of_val(value))
        (std::mem::size_of::<T>(), std::mem::align_of::<T>())
    }

    /// `NonZeroU32` 位查询与位运算，适合寄存器位掩码操作。
    pub fn nonzero_bit_ops(n: NonZeroU32) -> (u32, u32, u32) {
        // 1.97+: n.count_ones(), n.leading_zeros(), n.trailing_zeros()
        let ones = n.get().count_ones();
        let leading = n.get().leading_zeros();
        let trailing = n.get().trailing_zeros();
        (ones, leading, trailing)
    }

    /// `NonZeroU32::midpoint` / `isqrt` 的等效实现。
    ///
    /// 在资源受限的嵌入式设备上避免浮点运算。
    pub fn nonzero_midpoint(a: NonZeroU32, b: NonZeroU32) -> NonZeroU32 {
        // 1.97+: a.midpoint(b)
        let a = a.get();
        let b = b.get();
        let mid = (a & b) + ((a ^ b) >> 1);
        NonZeroU32::new(mid).unwrap_or_else(|| NonZeroU32::new(1).unwrap())
    }

    pub fn nonzero_isqrt(n: NonZeroU32) -> NonZeroU32 {
        // 1.97+: n.isqrt()
        let n = n.get();
        if n < 2 {
            return NonZeroU32::new(n.max(1)).unwrap();
        }
        let mut x = n;
        let mut y = x.div_ceil(2);
        while y < x {
            x = y;
            y = (x + n / x) / 2;
        }
        NonZeroU32::new(x).unwrap_or_else(|| NonZeroU32::new(1).unwrap())
    }

    /// `char::is_control()` 在 Rust 1.97 中变为 `const fn`。
    pub fn char_is_control(c: char) -> bool {
        // 1.97+: c.is_control() 可直接在 const 上下文调用
        matches!(c, '\u{0}'..='\u{1F}' | '\u{7F}'..='\u{9F}')
    }

    /// 获取 `Box<T>` 中堆分配对象的裸指针。
    pub fn box_as_ptr<T>(b: &T) -> *const T {
        // 1.97+: Box::as_ptr(b)
        b as *const T
    }

    /// 将 `Option<T>` 转为只读切片视图。
    pub fn option_as_slice<T>(opt: &Option<T>) -> &[T] {
        // 1.97+: opt.as_slice()
        match opt {
            Some(x) => std::slice::from_ref(x),
            None => &[],
        }
    }

    /// 构造默认哈希器（1.97 后可在 const 上下文调用）。
    pub const fn build_hasher_default_new() -> BuildHasherDefault<DefaultHasher> {
        // 1.97+: const HASHER: BuildHasherDefault<DefaultHasher> = BuildHasherDefault::new();
        BuildHasherDefault::new()
    }

    /// 可移植的函数指针地址比较。
    pub fn fn_addr_eq(a: fn(), b: fn()) -> bool {
        // 1.97+: std::ptr::fn_addr_eq(a, b)
        a as usize == b as usize
    }

    /// 演示 `cfg(target_has_atomic_equal_alignment = "ptr")` 的使用位置。
    pub fn atomic_equal_alignment_note() -> &'static str {
        // 1.97+:
        // #[cfg(target_has_atomic_equal_alignment = "ptr")]
        // fn embedded_atomic_optimized() { /* 指针大小原子与 usize 对齐相同的平台 */ }
        "cfg(target_has_atomic_equal_alignment = \"ptr\") requires Rust 1.97+"
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
        let p = Rust197EmbeddedFeatures::box_as_ptr(&*b);
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
