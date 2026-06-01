//! Rust 189.0 新特性实现模块 —— c10_networks
//! Rust 189.0 feature module —— c10_networks
//! - `repr128`: `#[repr(u128/i128)]` 稳定
//! - `explicit_inferred_const`: 显式推断 const 参数
//! - `explicit_inferred_const`: 显式infer const parameter
//! # 版本信息
//! # this
//! - Rust 版本: 189.0
//! - Rust this : 189.0
//! - Rust 版this: 189.0
//! - 稳定日期: 2025-08-07
//! - date : 2025-08-07
//! - 稳定date: 2025-08-07
//! - date: 2025-08-07

// ============================================================================
// 1. `#[repr(u128/i128)]` 稳定
// ============================================================================

/// # `#[repr(u128/i128)]` 稳定
/// 允许枚举类型使用 128 位整数作为底层表示。
/// enum type 128 as represent 。
/// ## 使用场景
/// ## scenario
/// - 与使用 128 位标识符的外部协议/格式交互
/// - and 128 outside /
/// ## 限制
/// ##
/// - 仅在支持 128 位整数的平台上有效
/// - in 128 platform on effective
/// - FFI 中使用需谨慎，因为 C 标准没有固定大小的 128 位整数类型
/// - FFI in ，because C standard 128 type
#[repr(u128)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LargeId {
    System = 0x0001_0000_0000_0000_0000_0000_0000_0000,
    User = 0x0002_0000_0000_0000_0000_0000_0000_0000,
    Reserved = 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF,
}

impl LargeId {
    pub fn is_system(self) -> bool {
        self == LargeId::System
    }
    pub fn raw(self) -> u128 {
        self as u128
    }
}

#[test]
fn test_repr128() {
    assert!(LargeId::System.is_system());
    assert_eq!(
        LargeId::User.raw(),
        0x0002_0000_0000_0000_0000_0000_0000_0000
    );
}

// ============================================================================
// 2. 显式推断 const 参数
// ============================================================================

/// # 显式推断 const 参数
/// # infer const parameter
/// # 显式infer const parameter
/// Rust 1.89.0 允许在 turbofish 语法中显式使用 `_` 来让编译器推断 const 泛型参数。
/// Rust 1.89.0 in turbofish in `_` infer const generic parameter 。
/// Rust 1.89.0 Allowsin turbofish 语法in显式Use `_` 来让编译器infer const generic parameter。
/// ## 语法
/// ##
/// `foo::<_, N>(...)` — `_` 表示"让编译器推断这个 const 参数"
/// `foo::<_, N>(...)` — `_` represent "infer const parameter "
/// ## 使用场景
/// ## scenario
/// - 只需显式指定部分 const 参数时
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
