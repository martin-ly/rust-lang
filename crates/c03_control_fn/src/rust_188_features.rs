//! Rust 188.0 新特性实现模块 —— c03_control_fn
//! Rust 188.0 feature module —— c03_control_fn
//! - `let_chains`: Let Chains 在 2024 Edition 中稳定
//! - `let_chains`: Let Chains stabilized in 2024 Edition
//! - `let_chains`: Let Chains in 2024 Edition in稳定
//! - `let_chains`: Let Chains in 2024 Edition instable
//! # 版本信息
//! # Version Information
//! # this
//! - Rust 版本: 188.0
//! - Rust version: 188.0
//! - Rust this : 188.0
//! - Rust 版this: 188.0
//! - 稳定日期: 2025-06-26
//! - Stabilization date: 2025-06-26
//! - date : 2025-06-26
//! - 稳定date: 2025-06-26
//! - stabledate: 2025-06-26
//! - date: 2025-06-26

// ============================================================================
// 1. Let Chains 在 2024 Edition 中稳定
// ============================================================================

/// # Let Chains 稳定化
/// # Let Chains Stabilization
/// ## 语法
/// ## Syntax
/// ##
/// ## 之前
/// ## Before
/// ## 's before
/// 需要使用嵌套 `if let` 或 `match`。
/// Requires nested `if let` or `match`.
/// `if let` or `match`。
/// ## 现在
/// ## Now
/// ## present
/// 可以直接链式组合多个 let 条件和布尔条件。
/// Can directly chain multiple let conditions and boolean conditions.
/// can combination let condition and condition 。
/// ## 限制
/// ## Limitations
/// ##
/// - 仅在 Edition 2024 中可用
/// - Only available in Edition 2024
/// - in Edition 2024 in
/// - 仅in Edition 2024 in可用
/// - 不支持 `||`（或）与 `let` 混合（因语义复杂）
/// - Does not support `||` (or) mixed with `let` (due to semantic complexity)
/// - `||`（or ）and `let` （because complex ）
pub fn process_option_chain(opt: Option<i32>) -> Option<i32> {
    if let Some(x) = opt && x > 0 && x < 100 {
        Some(x * 2)
    } else {
        None
    }
}

pub fn while_let_chain_example() -> usize {
    let mut count = 0;
    let mut iter = [Some(1), Some(2), None, Some(3)].into_iter();
    while let Some(x) = iter.next() && let Some(y) = x && y > 0 {
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
