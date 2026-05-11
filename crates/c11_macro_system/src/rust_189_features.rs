//! Rust 189.0 新特性实现模块 —— c11_macro_system
//!
//! 本模块展示了 Rust 189.0 (2025-08-07) 的关键语言特性和工具链改进。
//!
//! - `explicit_inferred_const`: 显式推断 const 参数
//!
//! # 版本信息
//! - Rust 版本: 189.0
//! - 稳定日期: 2025-08-07
//! - Edition: 2024

// ============================================================================
// 1. 显式推断 const 参数
// ============================================================================

/// # 显式推断 const 参数
///
/// Rust 1.89.0 允许在 turbofish 语法中显式使用 `_` 来让编译器推断 const 泛型参数。
///
/// ## 语法
/// `foo::<_, N>(...)` — `_` 表示"让编译器推断这个 const 参数"
///
/// ## 使用场景
/// - 只需显式指定部分 const 参数时
/// - 提高代码可读性，避免写出冗余的 const 表达式
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
