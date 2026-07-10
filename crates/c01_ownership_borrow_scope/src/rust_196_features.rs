//! # Rust 1.96.0 特性 — 所有权与内存管理模块
//! **历史稳定 patch**: Rust 1.96.1（基于 Rust 1.96.0 特性集）
//!
//! 本模块展示 Rust 1.96.0/1.96.1 中与所有权、借用、内存安全直接相关的稳定特性：
//! - `ManuallyDrop` 常量作为模式 — 修复 1.94.0 回归，允许 match 中使用 ManuallyDrop 常量
//! - `From<T> for AssertUnwindSafe<T>` — 值直接构造 panic 安全包装器
//! - `core::range::Range` 的 Copy 语义 — 与所有权系统交互的可复用范围
//!
//! # 版本信息
//! - Rust 版本: 1.96.0/1.96.1+ stable
//! - 稳定日期: 2026-05-28
//! - Edition: 2024

use std::mem::ManuallyDrop;
use std::panic::AssertUnwindSafe;

// ============================================================================
// 1. ManuallyDrop 常量作为模式 (1.96 stable, 修复 1.94.0 回归)
// ============================================================================

/// # `ManuallyDrop` 常量模式匹配
///
/// Rust 1.96 修复了一个 1.94.0 引入的回归：允许在 match 模式中使用 `ManuallyDrop` 常量。
/// 这在需要区分不同"标记值"的低级内存管理场景中非常有用。
///
/// ## 应用场景
/// - 自定义内存分配器的标记分类
/// - 嵌入式系统中的状态码匹配
/// - 与 C FFI 交互时的常量标签
pub struct ManuallyDropPatternExamples;

impl ManuallyDropPatternExamples {
    /// 内存块类型标记
    const TAG_SMALL: ManuallyDrop<u32> = ManuallyDrop::new(0x01);
    const TAG_MEDIUM: ManuallyDrop<u32> = ManuallyDrop::new(0x02);
    const TAG_LARGE: ManuallyDrop<u32> = ManuallyDrop::new(0x03);

    /// 根据 ManuallyDrop 标记分类内存块大小
    pub fn classify_block_size(tag: ManuallyDrop<u32>) -> &'static str {
        match tag {
            Self::TAG_SMALL => "small (<= 1KB)",
            Self::TAG_MEDIUM => "medium (1KB - 1MB)",
            Self::TAG_LARGE => "large (> 1MB)",
            _ => "unknown",
        }
    }

    /// 使用 ManuallyDrop 标记进行资源类型分类
    pub fn classify_resource(handle: ManuallyDrop<u64>) -> &'static str {
        const RESOURCE_FILE: ManuallyDrop<u64> = ManuallyDrop::new(0xF1_0E);
        const RESOURCE_SOCKET: ManuallyDrop<u64> = ManuallyDrop::new(0x50_0A);
        const RESOURCE_PIPE: ManuallyDrop<u64> = ManuallyDrop::new(0x00_A0);

        match handle {
            RESOURCE_FILE => "file descriptor",
            RESOURCE_SOCKET => "network socket",
            RESOURCE_PIPE => "named pipe",
            _ => "other resource",
        }
    }
}

// ============================================================================
// 2. From<T> for AssertUnwindSafe<T> (1.96 stable)
// ============================================================================

/// # `From<T>` 实现用于 `AssertUnwindSafe<T>`
///
/// Rust 1.96 稳定了 `From<T> for AssertUnwindSafe<T>`，允许从值直接构造
/// panic 安全包装器，无需显式写闭包或包装函数。
///
/// ## 所有权语义
/// - `AssertUnwindSafe::from(value)` 获取 `value` 的所有权
/// - 与 `AssertUnwindSafe(value)` 构造器等价，但支持泛型边界推导
pub struct AssertUnwindSafeExamples;

impl AssertUnwindSafeExamples {
    /// 从值直接构造 AssertUnwindSafe
    pub fn wrap_value<T: std::panic::UnwindSafe>(value: T) -> AssertUnwindSafe<T> {
        AssertUnwindSafe::from(value)
    }

    /// 在 catch_unwind 中使用 From 构造
    pub fn safe_operation(data: Vec<u8>) -> Result<Vec<u8>, Box<dyn std::any::Any + Send>> {
        std::panic::catch_unwind(AssertUnwindSafe::from(|| {
            // 执行可能 panic 的操作
            data.into_iter()
                .map(|b| b.wrapping_mul(2))
                .collect::<Vec<u8>>()
        }))
    }

    /// 将原始指针包装为 panic-safe
    ///
    /// # Safety
    /// 调用者必须保证指针在 unwind 过程中保持有效
    pub unsafe fn wrap_raw_pointer<T: std::panic::RefUnwindSafe>(
        ptr: *mut T,
    ) -> AssertUnwindSafe<*mut T> {
        AssertUnwindSafe::from(ptr)
    }
}

// ============================================================================
// 3. core::range::Range 与所有权 — Copy 语义避免消费
// ============================================================================

/// # `core::range::Range` 的 Copy 语义与所有权
///
/// Rust 1.96.0 的 `core::range::Range` 在元素类型 `T: Copy` 时自身也实现 `Copy`。
/// 这意味着范围值可以多次迭代而不被 move/consum——与 `std::ops::Range` 形成对比。
pub struct RangeOwnershipExamples;

impl RangeOwnershipExamples {
    /// 演示 core::range::Range 的 Copy 行为
    pub fn demonstrate_copy_range() {
        use core::range::Range;

        let range: Range<i32> = Range { start: 0, end: 5 };

        // 多次迭代，range 不被消费
        let sum1: i32 = range.into_iter().sum();
        let sum2: i32 = range.into_iter().sum();

        assert_eq!(sum1, 10);
        assert_eq!(sum2, 10);

        // range 仍可在后续使用
        let count = range.into_iter().count();
        assert_eq!(count, 5);
    }

    /// 对比：std::ops::Range 会被消费
    pub fn demonstrate_std_range_move() {
        let range: std::ops::Range<i32> = 0..5;

        let sum1: i32 = range.clone().sum();
        // 如果不 clone()，range 在此处已被消费
        let sum2: i32 = range.sum();

        assert_eq!(sum1, 10);
        assert_eq!(sum2, 10);
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_manually_drop_pattern_classify() {
        assert_eq!(
            ManuallyDropPatternExamples::classify_block_size(ManuallyDrop::new(0x01)),
            "small (<= 1KB)"
        );
        assert_eq!(
            ManuallyDropPatternExamples::classify_block_size(ManuallyDrop::new(0x02)),
            "medium (1KB - 1MB)"
        );
        assert_eq!(
            ManuallyDropPatternExamples::classify_block_size(ManuallyDrop::new(0x03)),
            "large (> 1MB)"
        );
        assert_eq!(
            ManuallyDropPatternExamples::classify_block_size(ManuallyDrop::new(0xFF)),
            "unknown"
        );
    }

    #[test]
    fn test_manually_drop_resource_classify() {
        assert_eq!(
            ManuallyDropPatternExamples::classify_resource(ManuallyDrop::new(0xF1_0E_u64)),
            "file descriptor"
        );
        assert_eq!(
            ManuallyDropPatternExamples::classify_resource(ManuallyDrop::new(0x50_0A_u64)),
            "network socket"
        );
        assert_eq!(
            ManuallyDropPatternExamples::classify_resource(ManuallyDrop::new(0x9999)),
            "other resource"
        );
    }

    #[test]
    fn test_assert_unwind_safe_from() {
        let wrapped: AssertUnwindSafe<i32> = AssertUnwindSafeExamples::wrap_value(42);
        assert_eq!(wrapped.0, 42);
    }

    #[test]
    fn test_assert_unwind_safe_in_catch_unwind() {
        let result = AssertUnwindSafeExamples::safe_operation(vec![1, 2, 3]);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), vec![2, 4, 6]);
    }

    #[test]
    fn test_core_range_copy_semantics() {
        RangeOwnershipExamples::demonstrate_copy_range();
    }

    #[test]
    fn test_std_range_move() {
        RangeOwnershipExamples::demonstrate_std_range_move();
    }
}
