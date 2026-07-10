//! Rust 1.97.0 stable 特性 —— 类型系统
//!
//! 本模块演示 Rust 1.97.0 稳定化的类型/数值相关 API。

use std::num::NonZeroU32;

/// Rust 1.97 类型系统特性演示
///
/// 涉及特性：
/// - `NonZero` 位操作：`highest_one`、`lowest_one`、`bit_width`
/// - `NonZeroU32::midpoint` / `isqrt`
/// - `char::is_control` const 稳定
/// - `BuildHasherDefault::new` const 稳定
/// - `ptr::fn_addr_eq`
pub struct Rust197Features;

impl Rust197Features {
    /// 返回 `NonZeroU32` 最高置位位的位置
    pub fn nonzero_highest_one(n: NonZeroU32) -> u32 {
        n.highest_one()
    }

    /// 返回 `NonZeroU32` 最低置位位的位置
    pub fn nonzero_lowest_one(n: NonZeroU32) -> u32 {
        n.lowest_one()
    }

    /// 返回表示 `NonZeroU32` 所需的有效位宽
    pub fn nonzero_bit_width(n: NonZeroU32) -> NonZeroU32 {
        n.bit_width()
    }

    /// 计算两个 `NonZeroU32` 的无溢出中点
    pub fn nonzero_midpoint(a: NonZeroU32, b: NonZeroU32) -> NonZeroU32 {
        a.midpoint(b)
    }

    /// 计算 `NonZeroU32` 的整数平方根
    pub fn nonzero_isqrt(n: NonZeroU32) -> NonZeroU32 {
        n.isqrt()
    }

    /// 编译期判断字符是否为控制字符
    pub const fn is_control(c: char) -> bool {
        c.is_control()
    }

    /// 构造默认哈希器
    pub const fn build_hasher_default_new()
    -> std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher> {
        std::hash::BuildHasherDefault::new()
    }

    /// 可移植的函数指针地址比较
    pub fn fn_addr_eq(f: fn(), g: fn()) -> bool {
        std::ptr::fn_addr_eq(f, g)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nonzero_bit_ops() {
        let n = NonZeroU32::new(0b00010100).unwrap(); // 20
        assert_eq!(Rust197Features::nonzero_highest_one(n), 4);
        assert_eq!(Rust197Features::nonzero_lowest_one(n), 2);
        assert_eq!(Rust197Features::nonzero_bit_width(n).get(), 5);
    }

    #[test]
    fn test_nonzero_midpoint() {
        let a = NonZeroU32::new(10).unwrap();
        let b = NonZeroU32::new(20).unwrap();
        assert_eq!(Rust197Features::nonzero_midpoint(a, b).get(), 15);
    }

    #[test]
    fn test_nonzero_isqrt() {
        let n = NonZeroU32::new(25).unwrap();
        assert_eq!(Rust197Features::nonzero_isqrt(n).get(), 5);
    }

    #[test]
    fn test_is_control() {
        assert!(Rust197Features::is_control('\n'));
        assert!(Rust197Features::is_control('\u{7F}'));
        assert!(!Rust197Features::is_control(' '));
        assert!(!Rust197Features::is_control('a'));
    }

    #[test]
    fn test_build_hasher_default_new() {
        let _ = Rust197Features::build_hasher_default_new();
    }

    #[test]
    fn test_fn_addr_eq() {
        // 使用 #[inline(never)] 与不同体，避免编译器将两个空函数合并为同一地址。
        #[inline(never)]
        fn a() {
            std::hint::black_box(1);
        }
        #[inline(never)]
        fn b() {
            std::hint::black_box(2);
        }
        assert!(Rust197Features::fn_addr_eq(a, a));
        assert!(!Rust197Features::fn_addr_eq(a, b));
    }
}
