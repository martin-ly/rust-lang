//! # Rust 1.68 特性跟踪模块
//! # Rust 1.68 feature module
//!
//! 本模块收录 Rust 1.68.0（2023-03-09 stable）引入的类型系统相关特性，
//! 作为 `c02_type_system` crate 的版本对齐参考资料。
//!
//! ## 包含内容
//! - `impl From<bool> for {integer}` — 布尔到整数转换
//! - `impl From<bool> for {f32, f64}` — 布尔到浮点转换
//! - `VecDeque::new` 在 const 上下文中的支持
//!
//! # Version Information
//! - 稳定日期: 2023-03-09
//! - Stable date: 2023-03-09

// ============================================================================
// 1. `impl From<bool> for {f32, f64}` — 布尔到浮点转换 (1.68.0 stable)
// ============================================================================

/// # 布尔到浮点转换 (`From<bool> for f32/f64`)
/// # Bool to float conversion (`From<bool> for f32/f64`)
///
/// 允许将 `bool` 直接转换为浮点数值：`false` → `0.0`，`true` → `1.0`。
///
/// ## 类型系统意义
/// - `bool` 已实现 `From<bool> for {integer}`（同为 1.68.0 stable）
/// - 1.68 补全了对浮点类型的对称转换，便于数值计算与特征工程
///
/// ## 应用场景
/// - 机器学习特征向量构建（0.0/1.0 特征）
/// - 概率计算中的指示函数
/// - 传感器数据处理（布尔状态 → 浮点信号）
pub struct BoolToFloatConversionExamples;

impl BoolToFloatConversionExamples {
    /// 将布尔数组转换为 f64 特征向量
    pub fn bool_vector_to_features(flags: &[bool]) -> Vec<f64> {
        flags.iter().map(|&b| f64::from(b)).collect()
    }

    /// 条件概率指示函数: P(A) ≈ mean(indicator_A)
    pub fn indicator(probability: f64, condition: bool) -> f64 {
        if condition {
            probability
        } else {
            f64::from(false)
        }
    }

    /// 传感器布尔状态转换为模拟信号强度
    pub fn sensor_status_to_signal(active: bool, base_strength: f64) -> f64 {
        f64::from(active) * base_strength
    }
}

// ============================================================================
// 2. `VecDeque::new` 的 const 上下文支持 (1.68.0 stable)
// ============================================================================

use std::collections::VecDeque;

/// 允许在编译期初始化双端队列常量。
///
/// ## 类型系统意义
/// 使得更多数据结构可以在编译期构造，减少运行时初始化开销。
///
/// ## 限制
/// `VecDeque::new` 在 const 上下文可初始化，但修改仍需运行时或 `LazyLock` 等机制。
pub struct ConstVecDequeExamples;

impl ConstVecDequeExamples {
    pub const EMPTY_QUEUE: VecDeque<i32> = VecDeque::new();

    pub fn build_static_config() -> VecDeque<&'static str> {
        VecDeque::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bool_to_float_conversions() {
        assert_eq!(f32::from(false), 0.0);
        assert_eq!(f32::from(true), 1.0);
        assert_eq!(f64::from(false), 0.0);
        assert_eq!(f64::from(true), 1.0);

        let features = BoolToFloatConversionExamples::bool_vector_to_features(&[true, false, true]);
        assert_eq!(features, vec![1.0, 0.0, 1.0]);
    }

    #[test]
    fn const_vecdeque_new() {
        // 验证 const 上下文可以调用 VecDeque::new
        let _q: VecDeque<i32> = ConstVecDequeExamples::EMPTY_QUEUE;
    }
}
