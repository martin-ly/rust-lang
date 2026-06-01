//! Rust 187.0 新特性实现模块 —— c03_control_fn
//! Rust 187.0 feature module —— c03_control_fn
//! - `open_ranges_parsing`: 开放范围 `..EXPR` 可在一元操作符后解析
//! - `open_ranges_parsing`: scope `..EXPR` in after
//! # 版本信息
//! # Version Information
//! # this
//! - Rust 版本: 187.0
//! - Rust version: 187.0
//! - Rust this : 187.0
//! - Rust 版this: 187.0
//! - 稳定日期: 2025-05-15
//! - Stabilization date: 2025-05-15
//! - date : 2025-05-15
//! - 稳定date: 2025-05-15
//! - stabledate: 2025-05-15
//! - date: 2025-05-15

// ============================================================================
// 1. 开放范围 `..EXPR` 可在一元操作符后解析
// ============================================================================

/// # 开放范围与一元操作符
/// # scope and
/// ## 之前
/// ## Before
/// ## 's before
/// `..-5` 会被解析错误，需要写成 `..(-5)`。
/// `..-5` is ， `..(-5)`。
/// ## 现在
/// ## Now
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
