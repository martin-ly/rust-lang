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

use std::collections::{LinkedList, VecDeque};
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
/// | **`core::range::RangeInclusive`** (1.96.0+) | `RangeInclusive::new(a, b)` | 闭区间 `[a, b]` | 新的统一类型，未来将成为标准 |
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
        let range = core::range::RangeInclusive {
            start: 10,
            last: 15,
        };
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
        core::range::RangeInclusive {
            start: 1,
            last: total_pages,
        }
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
        core::range::RangeInclusive {
            start: *old.start(),
            last: *old.end(),
        }
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
// 4. 集合可变插入方法 (Collection Mutable Insertion Methods)
// ============================================================================

/// # 集合可变插入方法
///
/// Rust 1.95.0 为 `Vec`、`VecDeque` 和 `LinkedList` 新增了返回 `&mut T` 的
/// 插入/推送方法。这些方法解决了"插入后需要立即修改元素"的常见问题，
/// 避免了不必要的 `unwrap()` 或索引回查。
///
/// ## 新增 API 列表
///
/// | 集合类型 | 新方法 | 返回值 |
/// |---------|--------|--------|
/// | `Vec<T>` | `push_mut` | `&mut T` |
/// | `Vec<T>` | `insert_mut` | `&mut T` |
/// | `VecDeque<T>` | `push_front_mut` | `&mut T` |
/// | `VecDeque<T>` | `push_back_mut` | `&mut T` |
/// | `VecDeque<T>` | `insert_mut` | `&mut T` |
/// | `LinkedList<T>` | `push_front_mut` | `&mut T` |
/// | `LinkedList<T>` | `push_back_mut` | `&mut T` |
///
/// ## 设计动机
/// 在 1.95 之前，如果需要在插入元素后立即修改它，开发者必须：
/// 1. 先调用 `push` / `insert` / `push_front` 等
/// 2. 再调用 `last_mut().unwrap()` 或按索引 `get_mut(index).unwrap()` 获取可变引用
/// 3. 这不仅增加了样板代码，而且在某些情况下编译器难以证明引用的安全性
///
/// 1.95 的新方法将插入和获取可变引用合二为一，提高了代码的 ergonomics。
pub struct CollectionMutMethodsExamples;

impl CollectionMutMethodsExamples {
    /// `Vec::push_mut` —— 推送并立即修改
    ///
    /// ## 1.95 之前
    /// ```ignore
    /// let mut v = Vec::new();
    /// v.push(String::new());
    /// let last = v.last_mut().unwrap();
    /// last.push_str("hello");
    /// ```
    ///
    /// ## 1.95 方式
    /// `push_mut` 直接返回刚插入元素的可变引用。
    pub fn vec_push_mut() {
        let mut names: Vec<String> = Vec::new();

        // 推送一个空字符串，并立即获取其可变引用进行填充
        let last = names.push_mut(String::new());
        last.push_str("Rust");
        last.push_str(" 1.95");

        assert_eq!(names[0], "Rust 1.95");
    }

    /// `Vec::insert_mut` —— 插入并立即修改
    ///
    /// ## 1.95 之前
    /// ```ignore
    /// let mut v = vec![1, 3];
    /// v.insert(1, 0);
    /// let inserted = v.get_mut(1).unwrap();
    /// *inserted = 2;
    /// ```
    ///
    /// ## 1.95 方式
    /// `insert_mut` 在指定位置插入元素并返回其可变引用。
    pub fn vec_insert_mut() {
        let mut scores = vec![85, 92];

        // 在索引 1 处插入一个新分数，并立即加分
        let inserted = scores.insert_mut(1, 88);
        *inserted += 5; //  bonus

        assert_eq!(scores, vec![85, 93, 92]);
    }

    /// `VecDeque::push_front_mut` —— 队首插入并修改
    ///
    /// ## 1.95 之前
    /// ```ignore
    /// let mut dq = VecDeque::from([2, 3]);
    /// dq.push_front(0);
    /// let head = dq.front_mut().unwrap();
    /// *head += 1;
    /// ```
    ///
    /// ## 1.95 方式
    pub fn vecdeque_push_front_mut() {
        let mut queue = VecDeque::from([200, 300]);

        // 在队首插入元素并立即修改
        let head = queue.push_front_mut(100);
        *head += 50; // 调整为 150

        assert_eq!(queue, VecDeque::from([150, 200, 300]));
    }

    /// `VecDeque::push_back_mut` —— 队尾插入并修改
    ///
    /// ## 1.95 之前
    /// ```ignore
    /// let mut dq = VecDeque::from([1, 2]);
    /// dq.push_back(3);
    /// let back = dq.back_mut().unwrap();
    /// *back += 1;
    /// ```
    ///
    /// ## 1.95 方式
    pub fn vecdeque_push_back_mut() {
        let mut queue = VecDeque::from([1, 2]);

        // 在队尾插入元素并立即修改
        let back = queue.push_back_mut(3);
        *back *= 10; // 调整为 30

        assert_eq!(queue, VecDeque::from([1, 2, 30]));
    }

    /// `VecDeque::insert_mut` —— 任意位置插入并修改
    ///
    /// ## 1.95 之前
    /// ```ignore
    /// let mut dq = VecDeque::from([1, 3]);
    /// dq.insert(1, 2);
    /// let mid = dq.get_mut(1).unwrap();
    /// *mid = 20;
    /// ```
    ///
    /// ## 1.95 方式
    pub fn vecdeque_insert_mut() {
        let mut queue = VecDeque::from([10, 30]);

        // 在中间插入并立即加倍
        let mid = queue.insert_mut(1, 20);
        *mid *= 2; // 20 -> 40

        assert_eq!(queue, VecDeque::from([10, 40, 30]));
    }

    /// `LinkedList::push_front_mut` —— 链表头部插入并修改
    ///
    /// ## 1.95 之前
    /// ```ignore
    /// let mut list = LinkedList::from([2, 3]);
    /// list.push_front(1);
    /// let front = list.front_mut().unwrap();
    /// *front += 1;
    /// ```
    ///
    /// ## 1.95 方式
    pub fn linkedlist_push_front_mut() {
        let mut list = LinkedList::from([20, 30]);

        // 在链表头部插入并立即调整
        let front = list.push_front_mut(10);
        *front += 5; // 10 -> 15

        assert_eq!(list, LinkedList::from([15, 20, 30]));
    }

    /// `LinkedList::push_back_mut` —— 链表尾部插入并修改
    ///
    /// ## 1.95 之前
    /// ```ignore
    /// let mut list = LinkedList::from([1, 2]);
    /// list.push_back(3);
    /// let back = list.back_mut().unwrap();
    /// *back += 1;
    /// ```
    ///
    /// ## 1.95 方式
    pub fn linkedlist_push_back_mut() {
        let mut list = LinkedList::from([1, 2]);

        // 在链表尾部插入并立即调整
        let back = list.push_back_mut(3);
        *back += 7; // 3 -> 10

        assert_eq!(list, LinkedList::from([1, 2, 10]));
    }

    /// 综合示例：使用 `push_mut` 构建复杂对象
    ///
    /// 展示了在构建嵌套结构时，新方法如何减少样板代码。
    pub fn comprehensive_build_example() {
        let mut buffers: Vec<Vec<u8>> = Vec::new();

        // 创建一个新的缓冲区并立即写入数据
        let buf = buffers.push_mut(Vec::with_capacity(16));
        buf.extend_from_slice(b"Hello");
        buf.extend_from_slice(b", World!");

        assert_eq!(buffers[0], b"Hello, World!");
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
/// 在类型系统中，它可用于编译期选择平台相关的常量。
pub struct CfgSelectTypeExamples;

impl CfgSelectTypeExamples {
    /// 平台相关的最大数组长度提示
    pub fn platform_array_hint() -> usize {
        cfg_select! {
            target_pointer_width = "64" => { usize::MAX / 16 }
            target_pointer_width = "32" => { usize::MAX / 8 }
            _ => { 1024 * 1024 }
        }
    }
}

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
        assert_eq!(
            inter,
            Some(core::range::RangeInclusive { start: 5, last: 10 })
        );

        let c = core::range::RangeInclusive {
            start: 20,
            last: 30,
        };
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

        let c = core::range::RangeInclusive {
            start: 10,
            last: 12,
        };
        let disjoint = NewRangeTypesExamples::range_union(a, c);
        assert_eq!(disjoint.len(), 2);
    }

    #[test]
    fn test_sum_range() {
        let range = core::range::RangeInclusive {
            start: 1u32,
            last: 5,
        };
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
            Some(core::range::RangeInclusive {
                start: 10,
                last: 20
            })
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
        tree.insert(core::range::RangeInclusive {
            start: 10,
            last: 15,
        });

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

    // ------------------------------------------------------------------------
    // 集合可变插入方法测试
    // ------------------------------------------------------------------------

    #[test]
    fn test_vec_push_mut() {
        CollectionMutMethodsExamples::vec_push_mut();
    }

    #[test]
    fn test_vec_insert_mut() {
        CollectionMutMethodsExamples::vec_insert_mut();
    }

    #[test]
    fn test_vecdeque_push_front_mut() {
        CollectionMutMethodsExamples::vecdeque_push_front_mut();
    }

    #[test]
    fn test_vecdeque_push_back_mut() {
        CollectionMutMethodsExamples::vecdeque_push_back_mut();
    }

    #[test]
    fn test_vecdeque_insert_mut() {
        CollectionMutMethodsExamples::vecdeque_insert_mut();
    }

    #[test]
    fn test_linkedlist_push_front_mut() {
        CollectionMutMethodsExamples::linkedlist_push_front_mut();
    }

    #[test]
    fn test_linkedlist_push_back_mut() {
        CollectionMutMethodsExamples::linkedlist_push_back_mut();
    }

    #[test]
    fn test_comprehensive_build_example() {
        CollectionMutMethodsExamples::comprehensive_build_example();
    }
}

// ============================================================================
// Real Rust 1.95 Features — Type System, Pattern Matching
// ============================================================================

use std::num::Saturating;
use std::ops::ControlFlow;

// ============================================================================
// Saturating 类型 — 饱和算术 (Rust 1.95 stable)
// ============================================================================

/// # `Saturating<T>` 类型
///
/// Rust 1.95.0 稳定了 `std::num::Saturating<T>`，提供**饱和算术**语义：
/// 溢出时不 panic，也不回绕 (wrap)，而是「饱和」到类型的最大值或最小值。
///
/// ## 对比
///
/// | 运算方式 | 溢出行为 | 适用场景 |
/// |:---------|:---------|:---------|
/// | 普通 `+` | Debug panic / Release wrap | 绝大多数场景 |
/// | `saturating_add` | 饱和到边界 | 信号处理、颜色值、音频采样 |
/// | `wrapping_add` | 回绕 | 哈希、密码学、位运算 |
/// | `Saturating<T> + Saturating<T>` | 饱和（运算符重载） | 需要全程饱和的算法 |
///
/// ## 设计动机
/// - **信号处理**: 音频采样值溢出时不应回绕（会产生爆音）
/// - **图形学**: RGB 颜色值溢出时应保持 255，不应回到 0
/// - **控制系统**: PID 控制器积分项不应因溢出而跳变
pub struct SaturatingTypeExamples;

impl SaturatingTypeExamples {
    /// 基础示例：饱和加法 vs 普通加法
    pub fn basic_saturating() {
        let a = Saturating(250_u8);
        let b = Saturating(20_u8);
        let sum = a + b; // 饱和到 255，不溢出
        assert_eq!(sum.0, 255);

        let c = Saturating(10_u8);
        let d = Saturating(20_u8);
        let normal_sum = c + d; // 正常加法
        assert_eq!(normal_sum.0, 30);
    }

    /// 音频采样混合：饱和加法防止爆音
    pub fn audio_sample_mix(a: i16, b: i16) -> i16 {
        let mixed = Saturating(a) + Saturating(b);
        mixed.0
    }

    /// 颜色值混合：RGB 通道饱和
    pub fn color_blend(c1: u8, c2: u8) -> u8 {
        (Saturating(c1) + Saturating(c2)).0
    }

    /// 乘法饱和：增益控制
    pub fn apply_gain(sample: u8, gain: u8) -> u8 {
        let s = Saturating(sample);
        let g = Saturating(gain);
        (s * g).0
    }
}

/// Demonstrates real Rust 1.95 features related to type system and pattern matching.
pub struct RealRust195Features;

impl RealRust195Features {
    /// `if let` guards in match arms (Rust 1.95)
    pub fn classify_with_if_let_guard(input: Option<String>) -> &'static str {
        match input {
            Some(s)
                if let Ok(n) = s.parse::<i32>()
                    && n > 0 =>
            {
                "positive number"
            }
            Some(s)
                if let Ok(n) = s.parse::<i32>()
                    && n < 0 =>
            {
                "negative number"
            }
            Some(s) if s.parse::<i32>().is_ok() => "zero",
            Some(_) => "not a number",
            None => "missing",
        }
    }

    /// `ControlFlow::map_break` (Rust 1.95)
    pub fn control_flow_map_demo() -> ControlFlow<i32, ()> {
        let flow: ControlFlow<i32, ()> = ControlFlow::Break(21);
        flow.map_break(|e| e * 2)
    }
}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_classify_with_if_let_guard() {
        assert_eq!(
            RealRust195Features::classify_with_if_let_guard(Some("42".to_string())),
            "positive number"
        );
        assert_eq!(
            RealRust195Features::classify_with_if_let_guard(Some("-5".to_string())),
            "negative number"
        );
        assert_eq!(
            RealRust195Features::classify_with_if_let_guard(Some("0".to_string())),
            "zero"
        );
        assert_eq!(
            RealRust195Features::classify_with_if_let_guard(Some("abc".to_string())),
            "not a number"
        );
        assert_eq!(
            RealRust195Features::classify_with_if_let_guard(None),
            "missing"
        );
    }

    #[test]
    fn test_control_flow_map_demo() {
        let result = RealRust195Features::control_flow_map_demo();
        assert!(matches!(result, ControlFlow::Break(42)));
    }

    #[test]
    fn test_saturating_basic() {
        SaturatingTypeExamples::basic_saturating();
        assert_eq!(
            SaturatingTypeExamples::audio_sample_mix(30000, 10000),
            32767_i16
        );
        assert_eq!(SaturatingTypeExamples::color_blend(250, 20), 255_u8);
    }
}
