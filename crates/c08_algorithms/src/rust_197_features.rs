//! Rust 1.97 特性跟踪模块 —— 算法
//! Rust 1.97 featurestracingmodule algorithm
#![allow(clippy::incompatible_msrv)]

use std::num::NonZeroU32;

/// # Rust 1.97 算法特性演示
/// # Rust 1.97 algorithm feature demonstration
///
/// Rust 1.97 稳定化的核心数值/算法 API：
/// Rust 1.97 core /algorithm API：
/// - `{float}::midpoint` / `{integer}::midpoint` / `NonZero*::midpoint`
/// - `<int>::isqrt` / `<uint>::isqrt` / `NonZero::isqrt`
/// - `pointer::byte_offset_from` / `wrapping_byte_sub`
pub struct Rust197AlgorithmFeatures;

impl Rust197AlgorithmFeatures {
    /// 使用 `f64::midpoint` 计算两个浮点数的中点（避免溢出）
    /// `f64::midpoint` point in point （）
    ///
    /// 与 `(a + b) / 2.0` 不同，`midpoint` 正确处理溢出和 NaN。
    /// and `(a + b) / 2.0` ，`midpoint` and NaN。
    pub fn float_midpoint(a: f64, b: f64) -> f64 {
        a.midpoint(b)
    }

    /// 使用 `u32::midpoint` 计算无符号整数中点（无溢出）
    /// `u32::midpoint` symbol in point （）
    ///
    /// 与 `(a + b) / 2` 不同，`midpoint` 使用 `(a & b) + ((a ^ b) >> 1)` 避免溢出。
    /// and `(a + b) / 2` ，`midpoint` `(a & b) + ((a ^ b) >> 1)` 。
    pub fn uint_midpoint(a: u32, b: u32) -> u32 {
        a.midpoint(b)
    }

    /// 使用 `i32::midpoint` 计算有符号整数中点
    /// `i32::midpoint` symbol in point
    pub fn int_midpoint(a: i32, b: i32) -> i32 {
        a.midpoint(b)
    }

    /// 使用 `u32::isqrt` 计算整数平方根
    ///
    /// 返回 floor(sqrt(n))，即不大于 sqrt(n) 的最大整数。
    /// floor(sqrt(n))， sqrt(n) maximum 。
    pub fn integer_sqrt(n: u32) -> u32 {
        n.isqrt()
    }

    /// 使用 `i32::checked_isqrt` 安全计算有符号整数平方根
    ///
    /// 对负数返回 `None`，避免 panic。
    /// to `None`， panic。
    pub fn checked_signed_sqrt(n: i32) -> Option<i32> {
        n.checked_isqrt()
    }

    /// 使用 `NonZeroU32::isqrt` 计算非零整数的平方根
    pub fn nonzero_sqrt(n: NonZeroU32) -> NonZeroU32 {
        n.isqrt()
    }

    /// 二分搜索辅助：使用 midpoint 计算中间索引
    /// binary search ： midpoint in
    pub fn binary_search_mid(low: usize, high: usize) -> usize {
        // 避免 (low + high) / 2 的溢出
        low.midpoint(high)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_float_midpoint() {
        assert_eq!(Rust197AlgorithmFeatures::float_midpoint(0.0, 10.0), 5.0);
        assert_eq!(Rust197AlgorithmFeatures::float_midpoint(1.0, 3.0), 2.0);
    }

    #[test]
    fn test_uint_midpoint_no_overflow() {
        // (u32::MAX + u32::MAX) / 2 会溢出，但 midpoint 不会
        assert_eq!(
            Rust197AlgorithmFeatures::uint_midpoint(u32::MAX, u32::MAX),
            u32::MAX
        );
    }

    #[test]
    fn test_int_midpoint() {
        assert_eq!(Rust197AlgorithmFeatures::int_midpoint(-10, 10), 0);
        assert_eq!(Rust197AlgorithmFeatures::int_midpoint(0, 5), 2);
    }

    #[test]
    fn test_integer_sqrt() {
        assert_eq!(Rust197AlgorithmFeatures::integer_sqrt(16), 4);
        assert_eq!(Rust197AlgorithmFeatures::integer_sqrt(15), 3);
        assert_eq!(Rust197AlgorithmFeatures::integer_sqrt(0), 0);
        assert_eq!(Rust197AlgorithmFeatures::integer_sqrt(1), 1);
    }

    #[test]
    fn test_checked_signed_sqrt() {
        assert_eq!(Rust197AlgorithmFeatures::checked_signed_sqrt(16), Some(4));
        assert_eq!(Rust197AlgorithmFeatures::checked_signed_sqrt(-1), None);
    }

    #[test]
    fn test_nonzero_sqrt() {
        let n = NonZeroU32::new(25).unwrap();
        assert_eq!(Rust197AlgorithmFeatures::nonzero_sqrt(n).get(), 5);
    }

    #[test]
    fn test_binary_search_mid() {
        assert_eq!(Rust197AlgorithmFeatures::binary_search_mid(0, 10), 5);
        assert_eq!(
            Rust197AlgorithmFeatures::binary_search_mid(0, usize::MAX),
            usize::MAX / 2
        );
    }
}
