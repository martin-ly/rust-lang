//! Rust 1.97 特性跟踪模块 —— 类型系统
#![allow(clippy::incompatible_msrv)]

use std::num::NonZeroU32;

/// # Rust 1.97 特性演示
///
/// Rust 1.97 稳定化的核心类型系统 API：
/// - `{float}::midpoint` / `{integer}::midpoint` / `NonZero*::midpoint`
/// - `<int>::isqrt` / `<uint>::isqrt` / `NonZero::isqrt`
/// - `BuildHasherDefault::new`
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `f64::midpoint` 计算两个浮点数的中点
    pub fn float_midpoint(a: f64, b: f64) -> f64 {
        a.midpoint(b)
    }

    /// 使用 `u32::midpoint` 计算无符号整数中点（无溢出）
    pub fn uint_midpoint(a: u32, b: u32) -> u32 {
        a.midpoint(b)
    }

    /// 使用 `NonZeroU32::midpoint` 计算非零整数中点
    pub fn nonzero_midpoint(a: NonZeroU32, b: NonZeroU32) -> NonZeroU32 {
        a.midpoint(b)
    }

    /// 使用 `u32::isqrt` 计算整数平方根
    pub fn integer_sqrt(n: u32) -> u32 {
        n.isqrt()
    }

    /// 使用 `i32::checked_isqrt` 安全计算有符号整数平方根
    pub fn checked_integer_sqrt(n: i32) -> Option<i32> {
        n.checked_isqrt()
    }

    /// 使用 `NonZeroU32::isqrt` 计算非零整数平方根
    pub fn nonzero_sqrt(n: NonZeroU32) -> NonZeroU32 {
        n.isqrt()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_float_midpoint() {
        assert_eq!(Rust197Features::float_midpoint(0.0, 10.0), 5.0);
        assert_eq!(Rust197Features::float_midpoint(1.0, 3.0), 2.0);
    }

    #[test]
    fn test_uint_midpoint() {
        assert_eq!(Rust197Features::uint_midpoint(0, 10), 5);
        assert_eq!(Rust197Features::uint_midpoint(u32::MAX, u32::MAX), u32::MAX);
    }

    #[test]
    fn test_nonzero_midpoint() {
        let a = NonZeroU32::new(10).unwrap();
        let b = NonZeroU32::new(20).unwrap();
        assert_eq!(Rust197Features::nonzero_midpoint(a, b).get(), 15);
    }

    #[test]
    fn test_integer_sqrt() {
        assert_eq!(Rust197Features::integer_sqrt(16), 4);
        assert_eq!(Rust197Features::integer_sqrt(15), 3);
        assert_eq!(Rust197Features::integer_sqrt(0), 0);
    }

    #[test]
    fn test_checked_integer_sqrt() {
        assert_eq!(Rust197Features::checked_integer_sqrt(16), Some(4));
        assert_eq!(Rust197Features::checked_integer_sqrt(-1), None);
    }

    #[test]
    fn test_nonzero_sqrt() {
        let n = NonZeroU32::new(25).unwrap();
        assert_eq!(Rust197Features::nonzero_sqrt(n).get(), 5);
    }
}
