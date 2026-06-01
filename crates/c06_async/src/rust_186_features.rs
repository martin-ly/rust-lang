//! Rust 186.0 新特性实现模块 —— c06_async
//! Rust 186.0 feature module —— c06_async
//!
//! 本模块展示了 Rust 186.0 (2025-04-03) 的关键语言特性和工具链改进。
//! This module demonstrates key language features and toolchain improvements of Rust 186.0 (2025-04-03).
//!
//! - `target_feature_safe`: 安全函数上的 `#[target_feature]`
//! - `target_feature_safe`: `#[target_feature]` on safe functions
//! # this
//! - Rust 版本: 186.0
//! - Rust Version: 186.0
//! - 稳定日期: 2025-04-03
//! - Stable Date: 2025-04-03
//! - Edition: 2024

// ============================================================================
// 1. 安全函数上的 `#[target_feature]`
// ============================================================================

/// # 安全函数的 `#[target_feature]`
/// # `#[target_feature]` on Safe Functions
/// Rust 1.86.0 in function on ``#[target_feature]``，
/// 前提是调用者通过 `is_x86_feature_detected!` 等宏确保目标平台支持该特性。
/// prerequisite `is_x86_feature_detected!` etc. goal platform this feature 。
///
/// ## 之前限制
/// ## 's before
/// 1.86 之前，``#[target_feature]`` 只能用于 `unsafe fn`，
/// because to feature function UB。
///
/// ## 现在
/// ## Now
/// 安全函数 + ``#[target_feature]`` 组合允许，但调用点必须在 `unsafe` 块中。
/// function + ``#[target_feature]`` combination ，but point must in `unsafe` in 。
///
/// # Safety
///
/// 调用者必须通过 `is_x86_feature_detected!("sse2")` 等方式
/// must `is_x86_feature_detected!("sse2")` method
/// goal platform SSE2 feature ，this function definition as 。
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse2")]
pub fn safe_simd_add(a: [f64; 2], b: [f64; 2]) -> [f64; 2] {
    // SSE2 矢量加法（伪代码示意）
    [a[0] + b[0], a[1] + b[1]]
}

#[test]
#[cfg(target_arch = "x86_64")]
fn test_safe_target_feature() {
    if is_x86_feature_detected!("sse2") {
        let result = unsafe { safe_simd_add([1.0, 2.0], [3.0, 4.0]) };
        assert_eq!(result, [4.0, 6.0]);
    }
}
