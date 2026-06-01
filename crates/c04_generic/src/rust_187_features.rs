//! Rust 187.0 新特性实现模块 —— c04_generic
//! Rust 187.0 feature module —— c04_generic
//! # 版本信息
//! # this
//! - Rust 版本: 187.0
//! - Rust this : 187.0
//! - Rust 版this: 187.0
//! - 稳定日期: 2025-05-15
//! - date : 2025-05-15
//! - 稳定date: 2025-05-15
//! - date: 2025-05-15

// ============================================================================
// 1. trait 中 RPIT 的 `use<...>` precise capturing
// ============================================================================

/// Rust 1.87.0 will `use<...>` precise capturing 扩展to trait definitionin，
/// ## 背景
/// ## background
/// `use<'a>` 语法允许显式声明需要捕获哪些生命周期。
/// `use<'a>` lifetime 。
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
