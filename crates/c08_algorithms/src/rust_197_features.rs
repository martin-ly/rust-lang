//! Rust 1.97.0 stable 特性 —— 算法与数据结构
//!
//! 本文件覆盖 Rust 1.97.0 已稳定的标准库新 API，直接调用 stable API。
//! 1.98+ 前瞻内容请见同目录 `rust_198_features.rs`。

use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;
use std::num::NonZeroU32;

/// Rust 1.97 算法/数据结构特性演示。
pub struct Rust197AlgorithmFeatures;

impl Rust197AlgorithmFeatures {
    /// `NonZero` 整数新增位查询方法：`highest_one` / `lowest_one` / `bit_width`。
    ///
    /// 这些 API 避免了在查询前对零值进行特殊处理，因为 `NonZero` 类型本身已保证非零。
    /// Rust 1.97.0 stable。
    pub fn nonzero_bit_ops() {
        let n = NonZeroU32::new(0b10100).unwrap();
        assert_eq!(n.highest_one(), 4); // 最高 set bit 的索引
        assert_eq!(n.lowest_one(), 2); // 最低 set bit 的索引
        assert_eq!(n.bit_width().get(), 5); // 表示 self 所需的最少位数；返回 NonZeroU32
    }

    /// `char::is_control()` 在 Rust 1.97 中变为 `const fn`。
    ///
    /// 使得字符分类可在编译期常量/静态项中使用。
    pub const fn char_is_control(c: char) -> bool {
        c.is_control()
    }

    /// 将 `Option<T>` 转为只读切片视图：`Some(x)` -> `[x]`，`None` -> `[]`。
    ///
    /// Rust 1.97.0 stable。
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

    /// 演示 `cfg(target_has_atomic_primitive_alignment = "ptr")` 的使用位置。
    ///
    /// Rust 1.97.0 新增该 cfg 条件，用于在编译期选择指针大小原子与 `usize` 对齐相同的优化路径。
    pub fn atomic_equal_alignment_note() -> &'static str {
        // Rust 1.97.0:
        // #[cfg(target_has_atomic_primitive_alignment = "ptr")]
        // fn optimized() { /* 指针大小原子与 usize 对齐相同的平台 */ }
        "cfg(target_has_atomic_primitive_alignment = \"ptr\") is stable in Rust 1.97.0"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nonzero_bit_ops() {
        Rust197AlgorithmFeatures::nonzero_bit_ops();
    }

    #[test]
    fn test_char_is_control() {
        assert!(!Rust197AlgorithmFeatures::char_is_control(' '));
        assert!(Rust197AlgorithmFeatures::char_is_control('\0'));
        assert!(Rust197AlgorithmFeatures::char_is_control('\n'));
    }

    #[test]
    fn test_option_as_slice() {
        let opt = Some(42);
        assert_eq!(Rust197AlgorithmFeatures::option_as_slice(&opt), &[42]);
        let none: Option<i32> = None;
        assert!(Rust197AlgorithmFeatures::option_as_slice(&none).is_empty());
    }

    #[test]
    fn test_const_size_and_align_of_val() {
        const BUF: [u8; 10] = [0; 10];
        const SIZE_ALIGN: (usize, usize) =
            Rust197AlgorithmFeatures::const_size_and_align_of_val(&BUF);
        assert_eq!(SIZE_ALIGN.0, 10);
        assert_eq!(SIZE_ALIGN.1, 1);
    }

    #[test]
    fn test_build_hasher_default_new() {
        let _ = Rust197AlgorithmFeatures::build_hasher_default_new();
    }
}
