//! Rust 189.0 新特性实现模块 —— c08_algorithms
//!
//! 本模块展示了 Rust 189.0 (2025-08-07) 的关键语言特性和工具链改进。
//! This module demonstrates key language features and toolchain improvements of Rust 189.0 (2025-08-07).
//!
//! - `explicit_inferred_const`: 显式推断 const 参数
//! - `explicit_inferred_const`: Explicit inferred const parameters
//! # this
//! - Rust 版本: 189.0
//! - Rust Version: 189.0
//! - 稳定日期: 2025-08-07
//! - Stable Date: 2025-08-07
//! - Edition: 2024

// ============================================================================
// 1. 显式推断 const 参数
// ============================================================================

/// # 显式推断 const 参数
/// # Explicit Inferred Const Parameters
///
/// Rust 1.89.0 允许在 turbofish 语法中显式使用 `_` 来让编译器推断 const 泛型参数。
/// Rust 1.89.0 in turbofish in `_` infer const generic parameter 。
///
/// ## 语法
/// ## Syntax
/// `foo::<_, N>(...)` — `_` 表示"让编译器推断这个 const 参数"
/// `foo::<_, N>(...)` — `_` represent "infer const parameter "
///
/// ## 使用场景
/// ## Usage Scenarios
/// - 只需显式指定部分 const 参数时
/// - part const parameter
/// - 提高代码可读性，避免写出冗余的 const 表达式
/// - ， const express
pub fn array_sum<T, const N: usize>(arr: [T; N]) -> T
where
    T: Default + std::ops::Add<Output = T> + Copy,
{
    let mut sum = T::default();
    for &item in &arr {
        sum = sum + item;
    }
    sum
}

#[test]
fn test_explicit_inferred_const() {
    // 1.89+: 可以使用 turbofish 显式推断类型和 const 参数
    let result = array_sum::<_, 3>([1, 2, 3]);
    assert_eq!(result, 6);
}
