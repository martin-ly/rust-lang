//! Rust 188.0 新特性实现模块 —— c09_design_pattern
//!
//! 本模块展示了 Rust 188.0 (2025-06-26) 的关键语言特性和工具链改进。
//!
//! - `let_chains`: Let Chains 在 2024 Edition 中稳定
//!
//! # 版本信息
//! - Rust 版本: 188.0
//! - 稳定日期: 2025-06-26
//! - Edition: 2024

// ============================================================================
// 1. Let Chains 在 2024 Edition 中稳定
// ============================================================================

/// # Let Chains 稳定化
///
/// Rust 1.88.0 在 2024 Edition 中稳定了 let chains，
/// 允许在 `if` 和 `while` 条件中将 `let` 模式与布尔表达式混合使用。
///
/// ## 语法
/// `if let Some(x) = opt && x > 0 { ... }`
///
/// ## 之前
/// 需要使用嵌套 `if let` 或 `match`。
///
/// ## 现在
/// 可以直接链式组合多个 let 条件和布尔条件。
///
/// ## 限制
/// - 仅在 Edition 2024 中可用
/// - 不支持 `||`（或）与 `let` 混合（因语义复杂）
pub fn process_option_chain(opt: Option<i32>) -> Option<i32> {
    if let Some(x) = opt
        && x > 0
        && x < 100
    {
        Some(x * 2)
    } else {
        None
    }
}

pub fn while_let_chain_example() -> usize {
    let mut count = 0;
    let mut iter = [Some(1), Some(2), None, Some(3)].into_iter();
    while let Some(x) = iter.next()
        && let Some(y) = x
        && y > 0
    {
        count += y as usize;
    }
    count
}

#[test]
fn test_let_chains() {
    assert_eq!(process_option_chain(Some(42)), Some(84));
    assert_eq!(process_option_chain(Some(-1)), None);
    assert_eq!(process_option_chain(None), None);
    assert_eq!(while_let_chain_example(), 3);
}
