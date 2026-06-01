//! Rust 189.0 新特性实现模块 —— c04_generic
//! Rust 189.0 feature module —— c04_generic
//! - `explicit_inferred_const`: 显式推断 const 参数
//! - `explicit_inferred_const`: Explicitly inferred const parameters
//! - `explicit_inferred_const`: 显式infer const parameter
//! # 版本信息
//! # Version Information
//! # this
//! - Rust 版本: 189.0
//! - Rust version: 189.0
//! - Rust this : 189.0
//! - Rust 版this: 189.0
//! - 稳定日期: 2025-08-07
//! - Stabilization date: 2025-08-07
//! - date : 2025-08-07
//! - 稳定date: 2025-08-07
//! - stabledate: 2025-08-07
//! - date: 2025-08-07

// ============================================================================
// 1. 显式推断 const 参数
// ============================================================================

/// # 显式推断 const 参数
/// # Explicit Inferred Const Parameters
/// # infer const parameter
/// # 显式infer const parameter
/// Rust 1.89.0 允许在 turbofish 语法中显式使用 `_` 来让编译器推断 const 泛型参数。
/// Rust 1.89.0 allows explicitly using `_` in turbofish syntax to let the compiler infer const generic parameters.
/// Rust 1.89.0 in turbofish in `_` infer const generic parameter 。
/// Rust 1.89.0 Allowsin turbofish 语法in显式Use `_` 来让编译器infer const generic parameter。
/// ## 语法
/// ## Syntax
/// ##
/// `foo::<_, N>(...)` — `_` 表示"让编译器推断这个 const 参数"
/// `foo::<_, N>(...)` — `_` means "let the compiler infer this const parameter"
/// `foo::<_, N>(...)` — `_` represent "infer const parameter "
/// ## 使用场景
/// ## Use Cases
/// ## scenario
/// - 只需显式指定部分 const 参数时
/// - When only partially specifying const parameters
/// - part const parameter
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
