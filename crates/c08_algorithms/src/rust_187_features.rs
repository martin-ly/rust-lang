//! Rust 187.0 新特性实现模块 —— c08_algorithms
//!
//! 本模块展示了 Rust 187.0 (2025-05-15) 的关键语言特性和工具链改进。
//! This module demonstrates key language features and toolchain improvements of Rust 187.0 (2025-05-15).
//!
//! - `open_ranges_parsing`: 开放范围 `..EXPR` 可在一元操作符后解析
//! - `open_ranges_parsing`: scope `..EXPR` in after
//!
//! # 版本信息
//! # Version Info
//! - Rust 版本: 187.0
//! - Rust Version: 187.0
//! - 稳定日期: 2025-05-15
//! - Stable Date: 2025-05-15
//! - Edition: 2024

// ============================================================================
// 1. 开放范围 `..EXPR` 可在一元操作符后解析
// ============================================================================

/// # 开放范围与一元操作符
/// # Open Ranges and Unary Operators
///
/// Rust 1.87.0 修复了开放范围 `..expr` 在一元操作符后的解析问题。
/// Rust 1.87.0 scope `..expr` in after problem 。
///
/// ## 之前
/// ## Before
/// `..-5` 会被解析错误，需要写成 `..(-5)`。
/// `..-5` is ， `..(-5)`。
///
/// ## 现在
/// ## Now
/// `..-5` 可以直接解析为 `RangeTo { end: -5 }`。
/// `..-5` can as `RangeTo { end: -5 }`。
pub fn negative_range_example() -> Vec<i32> {
    let arr = [-5, -4, -3, -2, -1, 0, 1, 2, 3];
    // 1.87+: 可以直接写 ..-3 而不需要括号
    arr[..arr.len() - 3].to_vec()
}

#[test]
fn test_open_range_parsing() {
    assert_eq!(negative_range_example(), [-5, -4, -3, -2, -1, 0]);
}
