//! Rust 1.97 Nightly 前瞻/候选特性 —— 类型系统
//!
//! 本模块演示 Rust 1.97 中稳定化的类型/数值相关 API。
//! 实际代码使用等价的 Rust 1.96.1 兼容实现；1.97 原生调用以 `#[cfg(nightly)]`
//! 分支保留，可通过 `RUSTFLAGS="--cfg nightly" cargo build` 启用。
#![allow(clippy::incompatible_msrv)]
#![allow(unexpected_cfgs)]
#![allow(clippy::borrowed_box)]

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
    #[cfg(nightly)]
    pub fn nonzero_highest_one(n: NonZeroU32) -> u32 {
        n.highest_one()
    }

    #[cfg(not(nightly))]
    pub fn nonzero_highest_one(n: NonZeroU32) -> u32 {
        n.get().ilog2()
    }

    /// 返回 `NonZeroU32` 最低置位位的位置
    #[cfg(nightly)]
    pub fn nonzero_lowest_one(n: NonZeroU32) -> u32 {
        n.lowest_one()
    }

    #[cfg(not(nightly))]
    pub fn nonzero_lowest_one(n: NonZeroU32) -> u32 {
        n.get().trailing_zeros()
    }

    /// 返回表示 `NonZeroU32` 所需的有效位宽
    #[cfg(nightly)]
    pub fn nonzero_bit_width(n: NonZeroU32) -> NonZeroU32 {
        n.bit_width()
    }

    #[cfg(not(nightly))]
    pub fn nonzero_bit_width(n: NonZeroU32) -> NonZeroU32 {
        // `n` 非零，因此 `ilog2() + 1 >= 1`，unwrap 安全。
        NonZeroU32::new(n.get().ilog2() + 1).unwrap()
    }

    /// 计算两个 `NonZeroU32` 的无溢出中点
    #[cfg(nightly)]
    pub fn nonzero_midpoint(a: NonZeroU32, b: NonZeroU32) -> NonZeroU32 {
        a.midpoint(b)
    }

    #[cfg(not(nightly))]
    pub fn nonzero_midpoint(a: NonZeroU32, b: NonZeroU32) -> NonZeroU32 {
        // 两个非零无符号数的中点仍为非零，unwrap 安全。
        NonZeroU32::new(a.get().midpoint(b.get())).unwrap()
    }

    /// 计算 `NonZeroU32` 的整数平方根
    #[cfg(nightly)]
    pub fn nonzero_isqrt(n: NonZeroU32) -> NonZeroU32 {
        n.isqrt()
    }

    #[cfg(not(nightly))]
    pub fn nonzero_isqrt(n: NonZeroU32) -> NonZeroU32 {
        // 非零整数的 isqrt 仍为非零，unwrap 安全。
        NonZeroU32::new(n.get().isqrt()).unwrap()
    }

    /// 编译期判断字符是否为控制字符
    #[cfg(nightly)]
    pub const fn is_control(c: char) -> bool {
        c.is_control()
    }

    #[cfg(not(nightly))]
    pub const fn is_control(c: char) -> bool {
        matches!(c, '\u{0}'..='\u{1F}' | '\u{7F}'..='\u{9F}')
    }

    /// 构造默认哈希器
    #[cfg(nightly)]
    pub const fn build_hasher_default_new()
    -> std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher> {
        std::hash::BuildHasherDefault::new()
    }

    #[cfg(not(nightly))]
    pub fn build_hasher_default_new()
    -> std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher> {
        std::hash::BuildHasherDefault::new()
    }

    /// 可移植的函数指针地址比较
    #[cfg(nightly)]
    pub fn fn_addr_eq(f: fn(), g: fn()) -> bool {
        std::ptr::fn_addr_eq(f, g)
    }

    #[cfg(not(nightly))]
    pub fn fn_addr_eq(f: fn(), g: fn()) -> bool {
        f as usize == g as usize
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
