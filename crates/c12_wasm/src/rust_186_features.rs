//! Rust 186.0 新特性实现模块 —— c12_wasm
//! Rust 186.0 feature module —— c12_wasm
//! - `target_feature_safe`: 安全functionon `#[target_feature]`
//! # 版本信息
//! # this
//! - Rust 版本: 186.0
//! - Rust this : 186.0
//! - Rust 版this: 186.0
//! - 稳定日期: 2025-04-03
//! - date : 2025-04-03
//! - 稳定date: 2025-04-03
//! - date: 2025-04-03

// ============================================================================
// 1. 安全函数上的 `#[target_feature]`
// ============================================================================

/// # 安全function `#[target_feature]`
/// Rust 1.86.0 允许在安全函数上使用 ``#[target_feature]``，
/// Rust 1.86.0 allow in function on ``#[target_feature]``，
/// Rust 1.86.0 in function on ``#[target_feature]``，
/// ## 之前限制
/// ## 's before
/// 1.86 之前，``#[target_feature]`` 只能用于 `unsafe fn`，
/// 1.86 'sbefore，``#[target_feature]`` 只能Used for `unsafe fn`，
/// 因为调用未启用对应特性的函数是 UB。
/// because to feature function UB。
/// ## 现在
/// ## present
/// 安全函数 + ``#[target_feature]`` 组合允许，但调用点必须在 `unsafe` 块中。
/// function + ``#[target_feature]`` combination allow ，but point must in `unsafe` in 。
/// function + ``#[target_feature]`` combination ，but point must in `unsafe` in 。
///
/// 调用者必须通过 `is_x86_feature_detected!("sse2")` 等方式
/// 确保目标平台支持 SSE2 特性，否则调用此函数是未定义行为。
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
