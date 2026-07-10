//! Rust 1.97.0 stable 特性 —— WASM 目标演示
//! Rust 1.97.0 stabilized features —— WASM target demonstration
//!
//! 本文件使用 Rust 1.97.0 stable API 演示相关特性语义。
//! 当前工具链为 Rust 1.97.0，直接调用 stable API。
//!
//! This module demonstrates Rust 1.97.0 stable APIs directly.

#![allow(clippy::borrowed_box)]

use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;
use std::num::NonZeroU32;

/// # Rust 1.97 WASM 相关特性演示
/// # Rust 1.97 WASM feature demonstration
///
/// 涵盖的稳定 API（按 Rust 1.97.0 官方列表）：
/// - `NonZero` 位操作：`count_ones`, `leading_zeros`, `trailing_zeros`
///   （位运算 `BitAnd`/`BitXor` 在 1.97.0 尚未稳定，仍使用原始值运算）
/// - `char::is_control()` const 稳定化（Rust 1.97.0 stable）
/// - `Box::as_ptr`（尚未稳定，保留等效实现）
/// - `Option::as_slice` / `as_mut_slice`（Rust 1.97.0 stable）
/// - `const size_of_val` / `align_of_val`（Rust 1.97.0 stable）
/// - `cfg(target_has_atomic_equal_alignment = "ptr")`（Rust 1.97.0 stable cfg 条件，无运行时 API）
/// - `BuildHasherDefault::new` const 稳定化（Rust 1.97.0 stable）
pub struct Rust197WasmFeatures;

impl Rust197WasmFeatures {
    /// `NonZeroU32` 位查询与位运算。
    ///
    /// Rust 1.97.0 在 `NonZeroU*` / `NonZeroI*` 上稳定了位模式查询方法，
    /// 便于在 WASM 等目标上直接操作非零整数的位表示。
    /// `BitAnd` 与 `BitXor` 在 1.97.0 尚未稳定，因此仍对原始值进行运算；
    /// `BitOr` 已稳定，可直接对 `NonZeroU32` 运算。
    pub fn nonzero_bit_ops(n: NonZeroU32) -> (u32, u32, u32, u32, u32, u32) {
        // `count_ones` 返回 NonZero<u32>，其余返回 u32；统一取原始值。
        let ones = n.count_ones().get();
        let leading = n.leading_zeros();
        let trailing = n.trailing_zeros();

        let mask = NonZeroU32::new(0b1010).unwrap();
        // BitAnd/BitXor for NonZeroU32 在 Rust 1.97.0 尚未稳定，需对原始值运算。
        let and = n.get() & mask.get();
        let or = (n | mask).get();
        let xor = n.get() ^ mask.get();
        (ones, leading, trailing, and, or, xor)
    }

    /// `char::is_control()` 在 Rust 1.97.0 中变为 `const fn`，
    /// 使得字符分类可在编译期常量/静态项中使用。
    pub const fn char_is_control(c: char) -> bool {
        c.is_control()
    }

    /// 获取 `Box<T>` 中堆分配对象的裸指针。
    ///
    /// `Box::as_ptr` 在 Rust 1.97.0 尚未稳定，这里使用 `as_ref()` 转换作为等效实现。
    pub fn box_as_ptr<T>(b: &Box<T>) -> *const T {
        b.as_ref() as *const T
    }

    /// 将 `Option<T>` 转为只读切片视图。
    pub fn option_as_slice<T>(opt: &Option<T>) -> &[T] {
        opt.as_slice()
    }

    /// 编译期计算值的大小与对齐（Rust 1.97.0 stable）。
    pub const fn const_size_and_align_of_val<T: Sized>(value: &T) -> (usize, usize) {
        (std::mem::size_of_val(value), std::mem::align_of_val(value))
    }

    /// 构造默认哈希器（Rust 1.97.0 后可在 const 上下文调用）。
    pub const fn build_hasher_default_new() -> BuildHasherDefault<DefaultHasher> {
        BuildHasherDefault::new()
    }

    /// 演示 `cfg(target_has_atomic_equal_alignment = "ptr")` 的使用位置。
    pub fn atomic_equal_alignment_note() -> &'static str {
        // Rust 1.97.0:
        // #[cfg(target_has_atomic_equal_alignment = "ptr")]
        // fn wasm_atomic_optimized() { /* 指针大小原子与 usize 对齐相同的平台 */ }
        "cfg(target_has_atomic_equal_alignment = \"ptr\") is stable in Rust 1.97.0"
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
        let p = Rust197WasmFeatures::box_as_ptr(&b);
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
