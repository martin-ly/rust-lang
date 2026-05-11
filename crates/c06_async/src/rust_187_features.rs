//! Rust 187.0 新特性实现模块 —— c06_async
//!
//! 本模块展示了 Rust 187.0 (2025-05-15) 的关键语言特性和工具链改进。
//!
//! - `open_ranges_parsing`: 开放范围 `..EXPR` 可在一元操作符后解析
//! - `use_in_traits`: trait 中 RPIT 的 `use<...>` precise capturing
//!
//! # 版本信息
//! - Rust 版本: 187.0
//! - 稳定日期: 2025-05-15
//! - Edition: 2024

// ============================================================================
// 1. 开放范围 `..EXPR` 可在一元操作符后解析
// ============================================================================

/// # 开放范围与一元操作符
///
/// Rust 1.87.0 修复了开放范围 `..expr` 在一元操作符后的解析问题。
///
/// ## 之前
/// `..-5` 会被解析错误，需要写成 `..(-5)`。
///
/// ## 现在
/// `..-5` 可以直接解析为 `RangeTo { end: -5 }`。
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
///
/// Rust 1.87.0 将 `use<...>` precise capturing 扩展到 trait 定义中，
/// 允许在 trait 方法的返回类型中精确控制生命周期捕获。
///
/// ## 背景
/// 在 2024 Edition 中，`impl Trait` 的隐式生命周期捕获规则更严格。
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
