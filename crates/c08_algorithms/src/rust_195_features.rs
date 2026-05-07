//! Rust 1.95 特性 —— 算法场景
//!
//! # 概述
//!
//! Rust 1.95 为算法设计带来的增强：
//! - **`core::range::RangeInclusive`** — 闭区间算法、区间树
//! - **`if let` guards** — 搜索与排序中的条件匹配
//! - **`Atomic*::update`** — 并发算法的无锁计数器
//! - **`cold_path`** — 分支预测不友好的路径标记

use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================================
// 1. core::range::RangeInclusive — 区间算法
// ============================================================================

/// # 区间算法增强
///
/// `core::range::RangeInclusive` 提供了统一闭区间类型，适用于区间覆盖、调度等算法。
pub struct RangeAlgorithmExamples;

impl RangeAlgorithmExamples {
    /// 判断两个闭区间是否重叠
    pub fn ranges_overlap(
        a: core::range::RangeInclusive<i32>,
        b: core::range::RangeInclusive<i32>,
    ) -> bool {
        a.start <= b.last && b.start <= a.last
    }

    /// 合并重叠区间（简化版：假设输入已排序）
    pub fn merge_overlapping(
        ranges: &[core::range::RangeInclusive<i32>],
    ) -> Vec<core::range::RangeInclusive<i32>> {
        let mut merged = Vec::new();
        for range in ranges {
            if let Some(last) = merged.last_mut()
                && Self::ranges_overlap(*last, *range)
            {
                *last = core::range::RangeInclusive {
                    start: last.start.min(range.start),
                    last: last.last.max(range.last),
                };
            } else {
                merged.push(*range);
            }
        }
        merged
    }

    /// 检查点是否在任意区间内（区间覆盖查询）
    pub fn point_in_any(point: i32, ranges: &[core::range::RangeInclusive<i32>]) -> bool {
        ranges.iter().any(|r| r.start <= point && point <= r.last)
    }
}

// ============================================================================
// 2. if let guards — 搜索算法条件
// ============================================================================

/// # 条件搜索模式
///
/// `if let` guards 在搜索和过滤算法中提供更精确的控制流。
pub struct SearchAlgorithmExamples;

impl SearchAlgorithmExamples {
    /// 查找第一个满足复合条件的元素
    pub fn find_first_valid<T>(items: &[&str], min: T) -> Option<T>
    where
        T: std::str::FromStr + PartialOrd,
    {
        items.iter().find_map(|s| match s.parse::<T>() {
            Ok(v) if v >= min => Some(v),
            _ => None,
        })
    }

    /// 二分搜索变体：查找满足谓词的边界
    pub fn partition_point_with_guard<T>(arr: &[T], predicate: impl Fn(&T) -> bool) -> usize {
        arr.iter().position(|x| !predicate(x)).unwrap_or(arr.len())
    }
}

// ============================================================================
// 3. Atomic*::update — 并发算法计数器
// ============================================================================

/// # 并发算法中的原子操作
///
/// 并行算法的统计和协调。
pub struct ConcurrentAlgorithmExamples;

impl ConcurrentAlgorithmExamples {
    /// 比较计数器（用于并行算法的步数统计）
    pub fn increment_step_counter(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::Relaxed, Ordering::Relaxed, |old| old + 1)
    }

    /// 尝试获取工作单元（用于 work-stealing 算法）
    pub fn try_acquire_work_unit(counter: &AtomicUsize) -> Result<usize, usize> {
        counter.try_update(Ordering::Acquire, Ordering::Relaxed, |remaining| {
            if remaining > 0 {
                Some(remaining - 1)
            } else {
                None
            }
        })
    }
}

// ============================================================================
// 4. cold_path — 算法边界情况
// ============================================================================

/// # 算法边界路径优化
///
/// 算法中很少触发的边界情况。
pub struct AlgorithmColdPathExamples;

impl AlgorithmColdPathExamples {
    /// 数组访问：越界为冷路径
    pub fn safe_get<T: Clone>(arr: &[T], index: usize) -> Option<T> {
        if index < arr.len() {
            Some(arr[index].clone())
        } else {
            std::hint::cold_path();
            None
        }
    }

    /// 除法：除零为冷路径
    pub fn safe_divide(a: i32, b: i32) -> Option<i32> {
        if b != 0 {
            Some(a / b)
        } else {
            std::hint::cold_path();
            None
        }
    }
}

// ============================================================================
// 测试
// ============================================================================

// ============================================================================
// cfg_select! 宏 — 编译时平台选择 (Rust 1.95 stable)
// ============================================================================

/// # `cfg_select!` 宏
///
/// `cfg_select!` 是 Rust 1.95.0 稳定的编译时条件选择宏。
/// 在算法优化中，可用于编译期选择平台相关的缓存行大小，
/// 指导伪共享 (false sharing) 避免策略。
pub struct CfgSelectAlgorithmExamples;

impl CfgSelectAlgorithmExamples {
    /// 平台相关的缓存行大小 (bytes)
    ///
    /// 用于对齐并发数据结构以避免伪共享。
    pub const CACHE_LINE_SIZE: usize = cfg_select! {
        any(target_arch = "x86_64", target_arch = "aarch64") => { 64 }
        target_arch = "powerpc64" => { 128 }
        _ => { 64 }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_range_overlap() {
        let a = core::range::RangeInclusive { start: 1, last: 5 };
        let b = core::range::RangeInclusive { start: 3, last: 7 };
        assert!(RangeAlgorithmExamples::ranges_overlap(a, b));

        let c = core::range::RangeInclusive { start: 6, last: 10 };
        assert!(!RangeAlgorithmExamples::ranges_overlap(a, c));
    }

    #[test]
    fn test_merge_overlapping() {
        let ranges = vec![
            core::range::RangeInclusive { start: 1, last: 3 },
            core::range::RangeInclusive { start: 2, last: 6 },
            core::range::RangeInclusive { start: 8, last: 10 },
        ];
        let merged = RangeAlgorithmExamples::merge_overlapping(&ranges);
        assert_eq!(merged.len(), 2);
        assert_eq!(merged[0], core::range::RangeInclusive { start: 1, last: 6 });
    }

    #[test]
    fn test_find_first_valid() {
        let items = vec!["abc", "10", "5", "20"];
        let result: Option<i32> = SearchAlgorithmExamples::find_first_valid(&items, 10);
        assert_eq!(result, Some(10));
    }

    #[test]
    fn test_concurrent_work_stealing() {
        let counter = AtomicUsize::new(3);
        assert!(ConcurrentAlgorithmExamples::try_acquire_work_unit(&counter).is_ok());
        assert_eq!(counter.load(Ordering::Relaxed), 2);

        counter.store(0, Ordering::Relaxed);
        assert!(ConcurrentAlgorithmExamples::try_acquire_work_unit(&counter).is_err());
    }

    #[test]
    fn test_safe_divide() {
        assert_eq!(AlgorithmColdPathExamples::safe_divide(10, 2), Some(5));
        assert_eq!(AlgorithmColdPathExamples::safe_divide(10, 0), None);
    }
}
