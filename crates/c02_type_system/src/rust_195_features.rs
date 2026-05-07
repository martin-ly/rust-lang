//! Rust 1.95.0 类型系统新特性实现模块
//!
//! 本模块展示了 Rust 1.95.0 在类型系统方面的关键增强：
//! - `core::range` 模块与 `RangeInclusive` / `RangeInclusiveIter` 类型 ⭐
//! - `bool: TryFrom<{integer}>` (已在 c03 详细覆盖，此处提供类型系统视角)
//!
//! # 版本信息
//! - Rust版本: 1.95.0
//! - 稳定日期: 2026-04-16
//! - Edition: 2024
//!
//! # 参考
//! - [Rust 1.95.0 Release Notes](https://releases.rs/docs/1.95.0/)
//! - [RFC 3550: New Range Types](https://rust-lang.github.io/rfcs/3550-new-range.html)

use std::ops::RangeInclusive;

// ============================================================================
// 1. core::range / RangeInclusive / RangeInclusiveIter
// ============================================================================

/// # `core::range` 模块与新的 `RangeInclusive` 类型
///
/// ## 概念定义
/// Rust 1.95.0 引入了 `core::range` 模块，并新增了 `RangeInclusive` 和
/// `RangeInclusiveIter` 类型。这是 RFC 3550 的阶段性成果，旨在为 Rust
/// 提供更丰富、更一致的区间类型系统。
///
/// ## Wikipedia 概念对齐
/// - **Interval (Mathematics)**: 数学中的区间概念 `[a, b]`，表示包含端点的范围
/// - **Iterator**: 遍历集合元素的抽象，RangeInclusiveIter 是区间的惰性迭代器视图
///
/// ## 关键区分
///
/// | 类型 | 表示法 | 包含端点？ | 用途 |
/// |------|--------|----------|------|
/// | `std::ops::Range` | `a..b` | 半开 `[a, b)` | 通用索引、切片 |
/// | `std::ops::RangeInclusive` | `a..=b` | 闭区间 `[a, b]` | 需要包含结束值的场景 |
/// | **`core::range::RangeInclusive`** (1.95+) | `RangeInclusive::new(a, b)` | 闭区间 `[a, b]` | 新的统一类型，未来将成为标准 |
/// | `core::range::RangeInclusiveIter` | 从 RangeInclusive 迭代 | 闭区间 | 显式的迭代器类型 |
///
/// ## 设计动机（RFC 3550）
/// 1. **一致性**: 将所有 range 类型统一到 `core::range` 模块下
/// 2. **可扩展性**: 为未来的 `RangeFrom`, `RangeTo`, `RangeFull` 等提供统一命名空间
/// 3. **清晰性**: `RangeInclusiveIter` 明确区分"区间值"和"区间迭代器"
///
/// ## 反例 / 迁移注意
/// - `core::range::RangeInclusive` **不是** `std::ops::RangeInclusive` 的替代
/// - 两者目前共存：`std::ops::RangeInclusive` 侧重运算符重载，`core::range::RangeInclusive` 侧重模块组织
/// - 未来 edition 可能进一步统一，目前建议在新代码中使用 `core::range` 以保持一致性
pub struct NewRangeTypesExamples;

impl NewRangeTypesExamples {
    /// 基础示例：创建新的 RangeInclusive
    ///
    /// 使用 `core::range::RangeInclusive::new(start, end)` 创建闭区间。
    pub fn basic_range_inclusive() {
        // 新的 core::range::RangeInclusive
        let range = core::range::RangeInclusive { start: 1, last: 5 };
        println!("RangeInclusive: {:?}", range);

        // 与旧的 std::ops::RangeInclusive 对比
        let old_range: RangeInclusive<i32> = 1..=5;
        println!("std::ops::RangeInclusive: {:?}", old_range);

        // 两者在迭代行为上等价
        let new_vals: Vec<i32> = range.into_iter().collect();
        let old_vals: Vec<i32> = old_range.collect();
        assert_eq!(new_vals, old_vals);
        assert_eq!(new_vals, vec![1, 2, 3, 4, 5]);
    }

    /// RangeInclusiveIter 显式迭代器
    ///
    /// `RangeInclusiveIter` 是 `RangeInclusive` 的迭代器表示，
    /// 允许将区间作为迭代器类型传递，而不暴露具体的范围值。
    pub fn range_inclusive_iter() {
        let range = core::range::RangeInclusive { start: 10, last: 15 };
        let iter: core::range::RangeInclusiveIter<i32> = range.into_iter();

        let values: Vec<i32> = iter.collect();
        assert_eq!(values, vec![10, 11, 12, 13, 14, 15]);
    }

    /// 算法应用：范围交集检测
    ///
    /// 使用新的 RangeInclusive 类型实现区间集合操作。
    pub fn range_intersection(
        a: core::range::RangeInclusive<i32>,
        b: core::range::RangeInclusive<i32>,
    ) -> Option<core::range::RangeInclusive<i32>> {
        let start = std::cmp::max(a.start, b.start);
        let end = std::cmp::min(a.last, b.last);

        if start <= end {
            Some(core::range::RangeInclusive { start, last: end })
        } else {
            None
        }
    }

    /// 算法应用：范围并集（相邻或重叠时合并）
    pub fn range_union(
        a: core::range::RangeInclusive<i32>,
        b: core::range::RangeInclusive<i32>,
    ) -> Vec<core::range::RangeInclusive<i32>> {
        let a_start = a.start;
        let a_end = a.last;
        let b_start = b.start;
        let b_end = b.last;

        // 检查是否重叠或相邻
        if a_end + 1 >= b_start && b_end + 1 >= a_start {
            vec![core::range::RangeInclusive {
                start: std::cmp::min(a_start, b_start),
                last: std::cmp::max(a_end, b_end),
            }]
        } else if a_end < b_start {
            vec![a, b]
        } else {
            vec![b, a]
        }
    }

    /// 类型系统视角：RangeInclusive 作为泛型边界
    ///
    /// 展示了如何在泛型代码中使用新的 range 类型。
    pub fn sum_range<T>(range: core::range::RangeInclusive<T>) -> T
    where
        T: std::ops::Add<Output = T> + Clone + PartialOrd + From<u8>,
    {
        let mut sum = T::from(0);
        let one = T::from(1);
        let mut current = range.start.clone();
        let end = range.last.clone();

        while current <= end {
            sum = sum + current.clone();
            current = current + one.clone();
        }

        sum
    }

    /// 配置解析：从字符串创建范围
    ///
    /// 实际应用中的范围解析示例。
    pub fn parse_range(s: &str) -> Option<core::range::RangeInclusive<u32>> {
        let parts: Vec<&str> = s.split("..=").collect();
        if parts.len() == 2 {
            let start = parts[0].parse().ok()?;
            let end = parts[1].parse().ok()?;
            Some(core::range::RangeInclusive { start, last: end })
        } else {
            None
        }
    }

    /// 分页计算：使用 RangeInclusive 表示页码范围
    pub fn page_range(total_items: u32, items_per_page: u32) -> core::range::RangeInclusive<u32> {
        let total_pages = if total_items == 0 {
            1
        } else {
            total_items.div_ceil(items_per_page)
        };
        core::range::RangeInclusive { start: 1, last: total_pages }
    }
}

// ============================================================================
// 2. RangeInclusive 与算法设计模式
// ============================================================================

/// # 区间树与范围查询（概念性实现）
///
/// 使用新的 `core::range::RangeInclusive` 作为区间树节点的基础类型。
pub struct IntervalTree<T> {
    intervals: Vec<core::range::RangeInclusive<T>>,
}

impl<T: Clone + Ord> IntervalTree<T> {
    pub fn new() -> Self {
        Self {
            intervals: Vec::new(),
        }
    }

    pub fn insert(&mut self, interval: core::range::RangeInclusive<T>) {
        self.intervals.push(interval);
        // 简化版：实际实现应按起点排序并维护平衡树
    }

    pub fn find_overlapping(
        &self,
        query: &core::range::RangeInclusive<T>,
    ) -> Vec<&core::range::RangeInclusive<T>> {
        self.intervals
            .iter()
            .filter(|interval| {
                // 重叠条件：interval.start <= query.end && interval.end >= query.start
                interval.start <= query.last && interval.last >= query.start
            })
            .collect()
    }
}

impl<T: Clone + Ord> Default for IntervalTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 3. 与现有生态的互操作
// ============================================================================

/// # 新旧 RangeInclusive 互转
///
/// 展示了如何在 `std::ops::RangeInclusive` 和 `core::range::RangeInclusive`
/// 之间进行转换，以便与使用旧类型的生态库互操作。
pub struct RangeInterop;

impl RangeInterop {
    /// 从旧类型转换为新类型
    pub fn from_old(old: RangeInclusive<i32>) -> core::range::RangeInclusive<i32> {
        core::range::RangeInclusive { start: *old.start(), last: *old.end() }
    }

    /// 从新类型转换为旧类型
    pub fn to_new(new: core::range::RangeInclusive<i32>) -> RangeInclusive<i32> {
        new.start..=new.last
    }

    /// 切片索引：新 RangeInclusive 暂不支持直接索引，需转换为旧类型
    pub fn slice_with_range(data: &[i32], range: core::range::RangeInclusive<usize>) -> &[i32] {
        let old_range = range.start..=range.last;
        &data[old_range]
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_range_inclusive() {
        NewRangeTypesExamples::basic_range_inclusive();
    }

    #[test]
    fn test_range_inclusive_iter() {
        NewRangeTypesExamples::range_inclusive_iter();
    }

    #[test]
    fn test_range_intersection() {
        let a = core::range::RangeInclusive { start: 1, last: 10 };
        let b = core::range::RangeInclusive { start: 5, last: 15 };
        let inter = NewRangeTypesExamples::range_intersection(a, b);
        assert_eq!(inter, Some(core::range::RangeInclusive { start: 5, last: 10 }));

        let c = core::range::RangeInclusive { start: 20, last: 30 };
        let no_inter = NewRangeTypesExamples::range_intersection(a, c);
        assert_eq!(no_inter, None);
    }

    #[test]
    fn test_range_union() {
        let a = core::range::RangeInclusive { start: 1, last: 5 };
        let b = core::range::RangeInclusive { start: 3, last: 8 };
        let union = NewRangeTypesExamples::range_union(a, b);
        assert_eq!(union.len(), 1);
        assert_eq!(union[0], core::range::RangeInclusive { start: 1, last: 8 });

        let c = core::range::RangeInclusive { start: 10, last: 12 };
        let disjoint = NewRangeTypesExamples::range_union(a, c);
        assert_eq!(disjoint.len(), 2);
    }

    #[test]
    fn test_sum_range() {
        let range = core::range::RangeInclusive { start: 1u32, last: 5 };
        let sum = NewRangeTypesExamples::sum_range(range);
        assert_eq!(sum, 15);
    }

    #[test]
    fn test_parse_range() {
        assert_eq!(
            NewRangeTypesExamples::parse_range("1..=5"),
            Some(core::range::RangeInclusive { start: 1, last: 5 })
        );
        assert_eq!(
            NewRangeTypesExamples::parse_range("10..=20"),
            Some(core::range::RangeInclusive { start: 10, last: 20 })
        );
        assert_eq!(NewRangeTypesExamples::parse_range("invalid"), None);
    }

    #[test]
    fn test_page_range() {
        assert_eq!(
            NewRangeTypesExamples::page_range(0, 10),
            core::range::RangeInclusive { start: 1, last: 1 }
        );
        assert_eq!(
            NewRangeTypesExamples::page_range(50, 10),
            core::range::RangeInclusive { start: 1, last: 5 }
        );
        assert_eq!(
            NewRangeTypesExamples::page_range(51, 10),
            core::range::RangeInclusive { start: 1, last: 6 }
        );
    }

    #[test]
    fn test_interval_tree() {
        let mut tree = IntervalTree::new();
        tree.insert(core::range::RangeInclusive { start: 1, last: 5 });
        tree.insert(core::range::RangeInclusive { start: 3, last: 7 });
        tree.insert(core::range::RangeInclusive { start: 10, last: 15 });

        let query = core::range::RangeInclusive { start: 4, last: 6 };
        let results = tree.find_overlapping(&query);
        assert_eq!(results.len(), 2); // [1,5] 和 [3,7] 与 [4,6] 重叠
    }

    #[test]
    fn test_range_interop() {
        let old = 1..=5;
        let new = RangeInterop::from_old(old);
        assert_eq!(new, core::range::RangeInclusive { start: 1, last: 5 });

        let back_to_old = RangeInterop::to_new(new);
        let collected: Vec<i32> = back_to_old.collect();
        assert_eq!(collected, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_slice_with_range() {
        let data = vec![10, 20, 30, 40, 50];
        let range = core::range::RangeInclusive { start: 1, last: 3 };
        let slice = RangeInterop::slice_with_range(&data, range);
        assert_eq!(slice, &[20, 30, 40]);
    }
}

