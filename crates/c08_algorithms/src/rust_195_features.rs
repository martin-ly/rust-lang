//! Rust 1.95 特性 —— 算法场景
//! Rust 1.95 feature —— algorithm scenario
//!
//! # 概述
//! # Overview
//!
//! Rust 1.95 为算法设计带来的增强：
//! Rust 1.95 as algorithm design ：
//! - **`core::range::RangeInclusive`** — 闭区间算法、区间树
//! - **`core::range::RangeInclusive`** algorithm tree
//! - **`if let` guards** — and ordering in condition
//! - **`Atomic*::update`** — 并发算法的无锁计数器
//! - **`Atomic*::update`** — concurrency algorithm lock-free
//! - **`cold_path`** — 分支预测不友好的路径标记
//! - **`cold_path`** — branch prediction mark

use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================================
// 1. core::range::RangeInclusive — 区间算法
// ============================================================================

/// # 区间算法增强
/// # interval algorithm
///
/// `core::range::RangeInclusive` 提供了统一闭区间类型，适用于区间覆盖、调度等算法。
/// `core::range::RangeInclusive` interval type ，interval 、etc. algorithm 。
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
    /// and interval （：hypothesize ordering ）
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
    /// point in interval inside （interval ）
    pub fn point_in_any(point: i32, ranges: &[core::range::RangeInclusive<i32>]) -> bool {
        ranges.iter().any(|r| r.start <= point && point <= r.last)
    }
}

// ============================================================================
// 2. if let guards — 搜索算法条件
// ============================================================================

/// # 条件搜索模式
/// # search pattern
///
/// `if let` guards 在搜索和过滤算法中提供更精确的控制流。
/// `if let` guards in and algorithm in stream 。
pub struct SearchAlgorithmExamples;

impl SearchAlgorithmExamples {
    /// 查找第一个满足复合条件的元素
    /// first condition element
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
/// # concurrentalgorithmatomic operation
///
/// 并行算法的统计和协调。
/// parallel algorithm and 。
pub struct ConcurrentAlgorithmExamples;

impl ConcurrentAlgorithmExamples {
    /// 比较计数器（用于并行算法的步数统计）
    pub fn increment_step_counter(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::Relaxed, Ordering::Relaxed, |old| old + 1)
    }

    /// 尝试获取工作单元（用于 work-stealing 算法）
    /// unit of work （ work-stealing algorithm ）
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
/// # algorithmedgepath optimization
///
/// 算法中很少触发的边界情况。
/// algorithm in edge situation 。
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
/// `cfg_select!` Rust 1.95.0 compile-time condition 。
/// 在算法优化中，可用于编译期选择平台相关的缓存行大小，
/// in algorithm optimization in ，platform cache line ，
/// 指导伪共享 (false sharing) 避免策略。
/// false sharing (false sharing) strategy 。
pub struct CfgSelectAlgorithmExamples;

impl CfgSelectAlgorithmExamples {
    /// 平台相关的缓存行大小 (bytes)
    /// platform cache line (bytes)
    ///
    /// 用于对齐并发数据结构以避免伪共享。
    /// to concurrency data structure false sharing 。
    pub const CACHE_LINE_SIZE: usize = cfg_select! {
        any(target_arch = "x86_64", target_arch = "aarch64") => { 64 }
        target_arch = "powerpc64" => { 128 }
        _ => { 64 }
    };
}

// ============================================================================
// 5. Vec / VecDeque / LinkedList — push_mut / insert_mut 新 API
// ============================================================================

/// # 集合可变引用插入 API
/// # set reference API
///
/// Rust 1.95.0 为 Vec, VecDeque, LinkedList 稳定了一组新方法，
/// in element after its reference ，。
use std::collections::{LinkedList, VecDeque};

pub struct PushMutExamples;

impl PushMutExamples {
    pub fn vec_push_and_initialize() -> Vec<String> {
        let mut buffers = Vec::new();
        let slot: &mut String = buffers.push_mut(String::new());
        slot.push_str("initialized in-place");
        let slot2 = buffers.push_mut(String::new());
        slot2.push_str("second element");
        buffers
    }

    pub fn vec_insert_at_position() -> Vec<i32> {
        let mut values = vec![10, 30, 40];
        let inserted = values.insert_mut(1, 0);
        *inserted = 20;
        values
    }

    pub fn deque_push_front_lru() -> VecDeque<u64> {
        let mut cache = VecDeque::with_capacity(4);
        cache.push_back(100);
        cache.push_back(200);
        cache.push_back(300);
        let front = cache.push_front_mut(999);
        *front = 0;
        cache
    }

    pub fn deque_push_back_batch() -> VecDeque<String> {
        let mut queue = VecDeque::new();
        for i in 0..3 {
            let item = queue.push_back_mut(format!("task-{i}-placeholder"));
            item.push_str("-completed");
        }
        queue
    }

    pub fn deque_insert_ordered() -> VecDeque<i32> {
        let mut sorted = VecDeque::from([1, 3, 5, 7]);
        let slot = sorted.insert_mut(2, 0);
        *slot = 4;
        sorted
    }

    pub fn list_push_front_build() -> LinkedList<String> {
        let mut list = LinkedList::new();
        let first = list.push_front_mut(String::new());
        first.push_str("head");
        let second = list.push_front_mut(String::new());
        second.push_str("new head");
        list
    }

    pub fn list_push_back_build() -> LinkedList<i32> {
        let mut list = LinkedList::new();
        for i in 0..3 {
            let item = list.push_back_mut(0);
            *item = i * 10;
        }
        list
    }
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

    #[test]
    fn test_vec_push_mut() {
        let v = PushMutExamples::vec_push_and_initialize();
        assert_eq!(v.len(), 2);
        assert_eq!(v[0], "initialized in-place");
        assert_eq!(v[1], "second element");
    }

    #[test]
    fn test_vec_insert_mut() {
        let v = PushMutExamples::vec_insert_at_position();
        assert_eq!(v, vec![10, 20, 30, 40]);
    }

    #[test]
    fn test_deque_push_front_mut() {
        let d = PushMutExamples::deque_push_front_lru();
        assert_eq!(d.front(), Some(&0));
    }

    #[test]
    fn test_deque_push_back_mut() {
        let d = PushMutExamples::deque_push_back_batch();
        assert_eq!(d.len(), 3);
        assert!(d.iter().all(|s| s.ends_with("-completed")));
    }

    #[test]
    fn test_deque_insert_mut() {
        let d = PushMutExamples::deque_insert_ordered();
        let vec: Vec<_> = d.iter().copied().collect();
        assert_eq!(vec, vec![1, 3, 4, 5, 7]);
    }

    #[test]
    fn test_list_push_front_mut() {
        let list = PushMutExamples::list_push_front_build();
        let vec: Vec<_> = list.iter().collect();
        assert_eq!(vec, vec!["new head", "head"]);
    }

    #[test]
    fn test_list_push_back_mut() {
        let list = PushMutExamples::list_push_back_build();
        let vec: Vec<_> = list.iter().copied().collect();
        assert_eq!(vec, vec![0, 10, 20]);
    }
}

// ============================================================================
// Real Rust 1.95 Features — Algorithms, data structures
// ============================================================================

use std::ops::ControlFlow;

/// # Real Rust 1.95 Features
///
/// Demonstrates `gen` blocks, `ControlFlow::map`, and `if let` guards.
pub struct RealRust195Features;

impl RealRust195Features {
    /// Search using `ControlFlow::Break` and `map` for early-exit
    pub fn search_with_control_flow(items: &[i32], target: i32) -> ControlFlow<i32, usize> {
        let flow = items.iter().try_fold((), |_acc, &item| {
            if item == target {
                ControlFlow::Break(item)
            } else {
                ControlFlow::Continue(())
            }
        });
        flow.map_continue(|()| items.len())
    }

    /// Classify data using `if let` guard on `Option<&[u8]>`
    pub fn classify_data_with_guard(data: Option<&[u8]>) -> &'static str {
        match data {
            Some(bytes)
                if let Some(&first) = bytes.first()
                    && first == 0xFF =>
            {
                "header marker"
            }
            Some(bytes) if bytes.len() > 100 => "large payload",
            Some(bytes)
                if let Some(&last) = bytes.last()
                    && last == 0x00 =>
            {
                "null terminated"
            }
            Some(_) => "generic data",
            None => "no data",
        }
    }

}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_search_with_control_flow() {
        let items = vec![10, 20, 30, 40, 50];
        let found = RealRust195Features::search_with_control_flow(&items, 30);
        assert!(found.is_break());
        assert_eq!(found.break_value(), Some(30));

        let missing = RealRust195Features::search_with_control_flow(&items, 99);
        assert!(missing.is_continue());
        if let ControlFlow::Continue(len) = missing {
            assert_eq!(len, 5);
        }
    }

    #[test]
    fn test_classify_data_with_guard() {
        assert_eq!(
            RealRust195Features::classify_data_with_guard(Some(&[0xFF, 0xAB])),
            "header marker"
        );
        assert_eq!(
            RealRust195Features::classify_data_with_guard(Some(&[0xAB, 0x00])),
            "null terminated"
        );
        assert_eq!(
            RealRust195Features::classify_data_with_guard(Some(&[0u8; 200])),
            "large payload"
        );
        assert_eq!(
            RealRust195Features::classify_data_with_guard(Some(&[1, 2, 3])),
            "generic data"
        );
        assert_eq!(
            RealRust195Features::classify_data_with_guard(None),
            "no data"
        );
    }

}
