//! Rust 187.0 新特性实现模块 —— c11_macro_system
//!
//! 本模块展示了 Rust 187.0 (2025-05-15) 的关键语言特性和工具链改进。
//!
//! - `use_in_traits`: trait 中 RPIT 的 `use<...>` precise capturing
//!
//! # 版本信息
//! - Rust 版本: 187.0
//! - 稳定日期: 2025-05-15
//! - Edition: 2024

// ============================================================================
// 1. trait 中 RPIT 的 `use<...>` precise capturing
// ============================================================================

/// # Trait 中的 `use<...>` Precise Capturing
///
/// Rust 1.87.0 将 `use<...>` precise capturing 扩展到 trait 定义中，
/// 允许在 trait 方法的返回类型中精确控制生命周期捕获。
///
/// ## 背景
/// 在 2024 Edition 中，`impl Trait` 的隐式生命周期捕获规则更严格。
/// `use<'a>` 语法允许显式声明需要捕获哪些生命周期。
/// 字符串解析器 trait 示例
pub trait Parser<'a> {
    /// 将输入字符串解析为单词迭代器
    fn parse(&self, input: &'a str) -> impl Iterator<Item = &'a str> + use<'a, Self>;
}

/// 简单的空白分词解析器
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
