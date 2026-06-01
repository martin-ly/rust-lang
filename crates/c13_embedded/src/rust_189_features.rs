//! Rust 189.0 新特性实现模块 —— c13_embedded
//! Rust 189.0 feature module —— c13_embedded
//! - `repr128`: `#[repr(u128/i128)]` 稳定
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
