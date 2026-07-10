//! Rust 1.97.0 stable 特性 —— 设计模式
//! Rust 1.97.0 stabilized features —— design patterns
//!
//! 本文件展示与设计模式（Null Object、Value Object、Factory）相关的 Rust 1.97.0 stable API。
//! 当前工具链为 Rust 1.97.0，直接调用 stable API。
//! 权威列表见 `concept/07_future/rust_1_97_stabilized.md`。

use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;
use std::num::NonZeroU32;

/// # Rust 1.97 设计模式特性演示
/// # Rust 1.97 design-pattern feature demonstration
///
/// 涉及特性：
/// - `Option::as_slice` / `as_mut_slice`（Rust 1.97.0 stable）：Null Object 模式
/// - `NonZeroU32` 位操作 `highest_one` / `lowest_one` / `bit_width`（Rust 1.97.0 stable）
/// - `NonZeroU32::midpoint` / `isqrt`（Rust 1.97.0 stable）
/// - `BuildHasherDefault::new` 成为 `const fn`（Rust 1.97.0 stable）
pub struct Rust197DesignPatternFeatures;

impl Rust197DesignPatternFeatures {
    /// 将 `Option<T>` 视为切片：`Some(x)` -> `[x]`，`None` -> `[]`。
    pub fn option_as_slice<T>(opt: &Option<T>) -> &[T] {
        opt.as_slice()
    }

    /// 将 `Option<T>` 视为可变切片：`Some(x)` -> `[x]`，`None` -> `[]`。
    pub fn option_as_mut_slice<T>(opt: &mut Option<T>) -> &mut [T] {
        opt.as_mut_slice()
    }

    /// 返回 `NonZeroU32` 最高设置位的位索引。
    pub fn nonzero_highest_one(n: NonZeroU32) -> u32 {
        n.highest_one()
    }

    /// 返回 `NonZeroU32` 最低设置位的位索引。
    pub fn nonzero_lowest_one(n: NonZeroU32) -> u32 {
        n.lowest_one()
    }

    /// 返回表示 `NonZeroU32` 所需的最少位数。
    pub fn nonzero_bit_width(n: NonZeroU32) -> NonZeroU32 {
        n.bit_width()
    }

    /// 计算两个 `NonZeroU32` 的中点，结果仍为非零。
    pub fn nonzero_midpoint(a: NonZeroU32, b: NonZeroU32) -> NonZeroU32 {
        a.midpoint(b)
    }

    /// 计算 `NonZeroU32` 的整数平方根，结果仍为非零。
    pub fn nonzero_isqrt(n: NonZeroU32) -> NonZeroU32 {
        n.isqrt()
    }

    /// 构造默认哈希器。
    ///
    /// Rust 1.97.0 起 `BuildHasherDefault::new` 是 `const fn`，可写为：
    /// `pub const HASHER: BuildHasherDefault<DefaultHasher> = BuildHasherDefault::new();`
    pub const fn default_hasher() -> BuildHasherDefault<DefaultHasher> {
        BuildHasherDefault::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_option_as_slice() {
        let some = Some(42);
        assert_eq!(Rust197DesignPatternFeatures::option_as_slice(&some), &[42]);
        let none: Option<i32> = None;
        assert!(Rust197DesignPatternFeatures::option_as_slice(&none).is_empty());
    }

    #[test]
    fn test_option_as_mut_slice() {
        let mut some = Some(42);
        let slice = Rust197DesignPatternFeatures::option_as_mut_slice(&mut some);
        assert_eq!(slice, &mut [42]);
        slice[0] = 100;
        assert_eq!(some, Some(100));

        let mut none: Option<i32> = None;
        assert!(Rust197DesignPatternFeatures::option_as_mut_slice(&mut none).is_empty());
    }

    #[test]
    fn test_nonzero_bit_operations() {
        let n = NonZeroU32::new(0b00010100).unwrap(); // 20
        assert_eq!(Rust197DesignPatternFeatures::nonzero_highest_one(n), 4);
        assert_eq!(Rust197DesignPatternFeatures::nonzero_lowest_one(n), 2);
        assert_eq!(Rust197DesignPatternFeatures::nonzero_bit_width(n).get(), 5);
    }

    #[test]
    fn test_nonzero_midpoint() {
        let a = NonZeroU32::new(10).unwrap();
        let b = NonZeroU32::new(20).unwrap();
        assert_eq!(
            Rust197DesignPatternFeatures::nonzero_midpoint(a, b).get(),
            15
        );
    }

    #[test]
    fn test_nonzero_isqrt() {
        let n = NonZeroU32::new(25).unwrap();
        assert_eq!(Rust197DesignPatternFeatures::nonzero_isqrt(n).get(), 5);
    }

    #[test]
    fn test_default_hasher() {
        let _ = Rust197DesignPatternFeatures::default_hasher();
    }
}
