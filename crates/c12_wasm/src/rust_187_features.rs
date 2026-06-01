//! Rust 187.0 新特性实现模块 —— c12_wasm
//! Rust 187.0 feature module —— c12_wasm
//! - `open_ranges_parsing`: 开放范围 `..EXPR` 可在一元操作符后解析
//! - `open_ranges_parsing`: scope `..EXPR` in operation after
//! - `open_ranges_parsing`: scope `..EXPR` in after
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
// 1. 开放范围 `..EXPR` 可在一元操作符后解析
// ============================================================================

/// # 开放范围与一元操作符
/// # scope and operation
/// # scope and
/// ## 之前
/// ## 's before
/// `..-5` 会被解析错误，需要写成 `..(-5)`。
/// `..-5` is ， `..(-5)`。
/// ## 现在
/// ## present
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

/// Rust 1.87.0 will `use<...>` precise capturing 扩展to trait definitionin，
/// ## 背景
/// ## background
/// `use<'a>` 语法允许显式声明需要捕获哪些生命周期。
/// `use<'a>` syntax allow lifetime 。
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
