//! Rust 187.0 新特性实现模块 —— c09_design_pattern
//! This module demonstrates key language features and toolchain improvements of Rust 187.0 (2025-05-15).
//!
//! - `open_ranges_parsing`: 开放范围 `..EXPR` 可在一元操作符后解析
//! - `open_ranges_parsing`: scope `..EXPR` in after
//! - `use_in_traits`: trait 中 RPIT 的 `use<...>` precise capturing
//! - `use_in_traits`: `use<...>` precise capturing in trait RPIT
//! # this
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

// ============================================================================
// 2. trait 中 RPIT 的 `use<...>` precise capturing
// ============================================================================

/// # Trait 中的 `use<...>` Precise Capturing
/// # `use<...>` Precise Capturing in Traits
/// 允许在 trait 方法的返回类型中精确控制生命周期捕获。
/// in trait method type in lifetime 。
///
/// ## 背景
/// ## Background
/// 在 2024 Edition 中，`impl Trait` 的隐式生命周期捕获规则更严格。
/// in 2024 Edition in ，`impl Trait` lifetime rule 。
/// `use<'a>` 语法允许显式声明需要捕获哪些生命周期。
pub trait Parser<'a> {
    fn parse(&self, input: &'a str) -> impl Iterator<Item = &'a str> + use<'a, Self>;
}

pub struct WordParser;
impl<'a> Parser<'a> for WordParser {
    fn parse(&self, input: &'a str) -> impl Iterator<Item = &'a str> + use<'a> {
        input.split_whitespace()
    }
}

#[test]
fn test_use_in_trait() {
    let parser = WordParser;
    let words: Vec<_> = parser.parse("hello world").collect();
    assert_eq!(words, vec!["hello", "world"]);
}
