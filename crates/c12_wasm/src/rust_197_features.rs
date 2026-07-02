//! Rust 1.97 稳定特性 —— WASM 目标演示
//! Rust 1.97 stabilized features —— WASM target demonstration
//!
//! 本文件使用 **Rust 1.96.0 等价实现** 演示 Rust 1.97.0 稳定 API 的语义。
//! 实际 Rust 1.97 调用以注释形式保留，便于 toolchain 升级到 1.97 后直接替换。
//!
//! This module demonstrates Rust 1.97.0 stabilized APIs using equivalent
//! implementations that compile on Rust 1.96.0. The actual Rust 1.97 call
//! sites are kept in comments for easy migration once the toolchain is upgraded.

#![allow(clippy::incompatible_msrv)]

use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;
use std::num::NonZeroU32;

/// # Rust 1.97 WASM 相关特性演示
/// # Rust 1.97 WASM feature demonstration
///
/// 涵盖的稳定 API（按 Rust 1.97.0 官方列表）：
/// - `NonZero` 位操作：`count_ones`, `leading_zeros`, `trailing_zeros`, `bitand`, `bitor`, `bitxor`
/// - `char::is_control()` const 稳定化
/// - `Box::as_ptr`
/// - `Option::as_slice` / `as_mut_slice`
/// - `const size_of_val` / `align_of_val`
/// - `cfg(target_has_atomic_equal_alignment = "ptr")`
/// - `BuildHasherDefault::new` const 稳定
pub struct Rust197WasmFeatures;

impl Rust197WasmFeatures {
    /// `NonZeroU32` 位查询与位运算。
    ///
    /// Rust 1.97 在 `NonZeroU*` / `NonZeroI*` 上稳定了位模式查询方法，
    /// 便于在 WASM 等目标上直接操作非零整数的位表示。
    pub fn nonzero_bit_ops(n: NonZeroU32) -> (u32, u32, u32, u32, u32, u32) {
        // 1.97+: n.count_ones(), n.leading_zeros(), n.trailing_zeros()
        let ones = n.get().count_ones();
        let leading = n.get().leading_zeros();
        let trailing = n.get().trailing_zeros();

        let mask = NonZeroU32::new(0b1010).unwrap();
        // 1.97+: n & mask, n | mask, n ^ mask 直接返回 NonZeroU32
        let and = n.get() & mask.get();
        let or = n.get() | mask.get();
        let xor = n.get() ^ mask.get();
        (ones, leading, trailing, and, or, xor)
    }

    /// `char::is_control()` 在 Rust 1.97 中变为 `const fn`，
    /// 使得字符分类可在编译期常量/静态项中使用。
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

    /// 编译期计算值的大小与对齐（1.96 兼容版，仅支持 `Sized` 类型）。
    pub const fn const_size_and_align_of_val<T: Sized>(_: &T) -> (usize, usize) {
        // 1.97+: (std::mem::size_of_val(value), std::mem::align_of_val(value))
        (std::mem::size_of::<T>(), std::mem::align_of::<T>())
    }

    /// 构造默认哈希器（1.97 后可在 const 上下文调用）。
    pub const fn build_hasher_default_new() -> BuildHasherDefault<DefaultHasher> {
        // 1.97+: const HASHER: BuildHasherDefault<DefaultHasher> = BuildHasherDefault::new();
        BuildHasherDefault::new()
    }

    /// 演示 `cfg(target_has_atomic_equal_alignment = "ptr")` 的使用位置。
    pub fn atomic_equal_alignment_note() -> &'static str {
        // 1.97+:
        // #[cfg(target_has_atomic_equal_alignment = "ptr")]
        // fn wasm_atomic_optimized() { /* 指针大小原子与 usize 对齐相同的平台 */ }
        "cfg(target_has_atomic_equal_alignment = \"ptr\") requires Rust 1.97+"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nonzero_bit_ops() {
        let n = NonZeroU32::new(0b10100).unwrap();
        let (ones, leading, trailing, and, or, xor) = Rust197WasmFeatures::nonzero_bit_ops(n);
        assert_eq!(ones, 2);
        assert_eq!(trailing, 2);
        assert_eq!(and, 0b10100 & 0b1010);
        assert_eq!(or, 0b10100 | 0b1010);
        assert_eq!(xor, 0b10100 ^ 0b1010);
        assert!(leading > 0);
    }

    #[test]
    fn test_char_is_control() {
        assert!(!Rust197WasmFeatures::char_is_control(' '));
        assert!(Rust197WasmFeatures::char_is_control('\0'));
        assert!(Rust197WasmFeatures::char_is_control('\n'));
    }

    #[test]
    fn test_box_as_ptr() {
        let b = Box::new(42);
        let p = Rust197WasmFeatures::box_as_ptr(&*b);
        assert_eq!(unsafe { *p }, 42);
    }

    #[test]
    fn test_option_as_slice() {
        let opt = Some(42);
        assert_eq!(Rust197WasmFeatures::option_as_slice(&opt), &[42]);
        let none: Option<i32> = None;
        assert!(Rust197WasmFeatures::option_as_slice(&none).is_empty());
    }

    #[test]
    fn test_const_size_and_align_of_val() {
        const BUF: [u8; 10] = [0; 10];
        const SIZE_ALIGN: (usize, usize) = Rust197WasmFeatures::const_size_and_align_of_val(&BUF);
        assert_eq!(SIZE_ALIGN.0, 10);
        assert_eq!(SIZE_ALIGN.1, 1);
    }

    #[test]
    fn test_build_hasher_default_new() {
        let _ = Rust197WasmFeatures::build_hasher_default_new();
    }
}
