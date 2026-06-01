//! Rust 1.95.0 类型系统新特性实现模块
//! Rust 1.95.0 type system feature module
//! # 版本信息
//! # this
//! - 稳定日期: 2026-04-16
//! - date : 2026-04-16
//! - 稳定date: 2026-04-16
//! - date: 2026-04-16
//! # 参考
//! # reference
//! - [RFC 3550: New Range Types](https://rust-lang.github.io/rfcs/3550-new-range.html)

use std::collections::{LinkedList, VecDeque};
use std::ops::RangeInclusive;

// ============================================================================
// 1. core::range / RangeInclusive / RangeInclusiveIter
// ============================================================================

/// ## 概念定义
/// ## concept definition
/// 提供更丰富、更一致的区间类型系统。
/// 、interval type system 。
/// ## Wikipedia 概念对齐
/// ## 关键区分
/// ## key
/// ## key区分
/// ## key
/// | 类型 | 表示法 | 包含端点？ | 用途 |
/// | type | represent | point ？ | purpose |
/// | `std::ops::Range` | `a..b` | 半开 `[a, b)` | 通用索引、切片 |
/// | `std::ops::Range` | `a..b` | `[a, b)` | 、 |
/// ## 设计动机（RFC 3550）
/// ## design （RFC 3550）
/// ## 反例 / 迁移注意
/// ## /
/// - 未来 edition 可能进一步统一，目前建议在新代码中使用 `core::range` 以保持一致性
/// - future edition may ，before in in `core::range` consistency
pub struct NewRangeTypesExamples;

impl NewRangeTypesExamples {
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

    /// 允许将区间作为迭代器类型传递，而不暴露具体的范围值。
    /// will interval as type ，while expose volume scope 。
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
    /// algorithm application ：scope intersection
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
    /// algorithm application ：scope union （or and ）
    /// algorithmapplication：rangeunion（相邻or重叠时Merge）
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
    /// ：from scope
    /// 实际应用中的范围解析示例。
    /// actual application in scope example 。
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
/// # interval tree and scope （concept ）
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

/// 之间进行转换，以便与使用旧类型的生态库互操作。
/// 's conversion ，and type ecosystem library 。
pub struct RangeInterop;

impl RangeInterop {
    /// 从旧类型转换为新类型
    /// from type conversion as type
    pub fn from_old(old: RangeInclusive<i32>) -> core::range::RangeInclusive<i32> {
        core::range::RangeInclusive {
            start: *old.start(),
            last: *old.end(),
        }
    }

    /// 从新类型转换为旧类型
    /// from type conversion as type
    pub fn to_new(new: core::range::RangeInclusive<i32>) -> RangeInclusive<i32> {
        new.start..=new.last
    }

    pub fn slice_with_range(data: &[i32], range: core::range::RangeInclusive<usize>) -> &[i32] {
        let old_range = range.start..=range.last;
        &data[old_range]
    }
}

// ============================================================================
// 4. 集合可变插入方法 (Collection Mutable Insertion Methods)
// ============================================================================

/// # 集合可变插入方法
/// # set method
/// 插入/推送方法。这些方法解决了"插入后需要立即修改元素"的常见问题，
/// /method 。method "after element "problem ，
/// ## 新增 API 列表
/// ## API
/// | 集合类型 | 新方法 | 返回值 |
/// | set type | method | return value |
/// | settype | 新method | return value |
/// | `Vec<T>` | `insert_mut` | `&mut T` |
/// | `VecDeque<T>` | `push_front_mut` | `&mut T` |
/// | `VecDeque<T>` | `push_back_mut` | `&mut T` |
/// | `VecDeque<T>` | `insert_mut` | `&mut T` |
/// | `LinkedList<T>` | `push_front_mut` | `&mut T` |
/// | `LinkedList<T>` | `push_back_mut` | `&mut T` |
///
/// ## 设计动机
/// ## design
/// 在 1.95 之前，如果需要在插入元素后立即修改它，开发者必须：
/// in 1.95 's before ，if in element after ，must ：
/// 1. 先调用 `push` / `insert` / `push_front` 等
/// 1. 先Call `push` / `insert` / `push_front` etc.
/// 2. 再调用 `last_mut().unwrap()` 或按索引 `get_mut(index).unwrap()` 获取可变引用
/// 2. 再Call `last_mut().unwrap()` or按索引 `get_mut(index).unwrap()` Get可变reference
/// 3. 这不仅增加了样板代码，而且在某些情况下编译器难以证明引用的安全性
/// 3. ，while and in situation under reference
pub struct CollectionMutMethodsExamples;

impl CollectionMutMethodsExamples {
    /// `Vec::push_mut` —— 推送并立即修改
    /// `Vec::push_mut` —— and
    /// ## 1.95 之前
    /// ## 1.95 's before
    /// let mut v = Vec::new();
    /// v.push(String::new());
    /// let last = v.last_mut().unwrap();
    /// last.push_str("hello");
    /// ```
    ///
    /// ## 1.95 方式
    /// ## 1.95 way
    pub fn vec_push_mut() {
        let mut names: Vec<String> = Vec::new();

        // 推送一个空字符串，并立即获取其可变引用进行填充
        let last = names.push_mut(String::new());
        last.push_str("Rust");
        last.push_str(" 1.95");

        assert_eq!(names[0], "Rust 1.95");
    }

    /// `Vec::insert_mut` —— 插入并立即修改
    /// `Vec::insert_mut` —— and
    /// ## 1.95 之前
    /// ## 1.95 's before
    /// let mut v = vec![1, 3];
    /// v.insert(1, 0);
    /// let inserted = v.get_mut(1).unwrap();
    /// *inserted = 2;
    /// ```
    ///
    /// ## 1.95 方式
    /// ## 1.95 way
    /// `insert_mut` 在指定位置插入元素并返回其可变引用。
    /// `insert_mut` in position element and its reference 。
    pub fn vec_insert_mut() {
        let mut scores = vec![85, 92];

        // 在索引 1 处插入一个新分数，并立即加分
        let inserted = scores.insert_mut(1, 88);
        *inserted += 5; //  bonus

        assert_eq!(scores, vec![85, 93, 92]);
    }

    /// ## 1.95 之前
    /// ## 1.95 's before
    /// let mut dq = VecDeque::from([2, 3]);
    /// dq.push_front(0);
    /// let head = dq.front_mut().unwrap();
    /// *head += 1;
    /// ```
    ///
    /// ## 1.95 方式
    /// ## 1.95 way
    pub fn vecdeque_push_front_mut() {
        let mut queue = VecDeque::from([200, 300]);

        // 在队首插入元素并立即修改
        let head = queue.push_front_mut(100);
        *head += 50; // 调整为 150

        assert_eq!(queue, VecDeque::from([150, 200, 300]));
    }

    /// ## 1.95 之前
    /// ## 1.95 's before
    /// let mut dq = VecDeque::from([1, 2]);
    /// dq.push_back(3);
    /// let back = dq.back_mut().unwrap();
    /// *back += 1;
    /// ```
    ///
    /// ## 1.95 方式
    /// ## 1.95 way
    pub fn vecdeque_push_back_mut() {
        let mut queue = VecDeque::from([1, 2]);

        // 在队尾插入元素并立即修改
        let back = queue.push_back_mut(3);
        *back *= 10; // 调整为 30

        assert_eq!(queue, VecDeque::from([1, 2, 30]));
    }

    /// ## 1.95 之前
    /// ## 1.95 's before
    /// let mut dq = VecDeque::from([1, 3]);
    /// dq.insert(1, 2);
    /// let mid = dq.get_mut(1).unwrap();
    /// *mid = 20;
    /// ```
    ///
    /// ## 1.95 方式
    /// ## 1.95 way
    pub fn vecdeque_insert_mut() {
        let mut queue = VecDeque::from([10, 30]);

        // 在中间插入并立即加倍
        let mid = queue.insert_mut(1, 20);
        *mid *= 2; // 20 -> 40

        assert_eq!(queue, VecDeque::from([10, 40, 30]));
    }

    /// ## 1.95 之前
    /// ## 1.95 's before
    /// let mut list = LinkedList::from([2, 3]);
    /// list.push_front(1);
    /// let front = list.front_mut().unwrap();
    /// *front += 1;
    /// ```
    ///
    /// ## 1.95 方式
    /// ## 1.95 way
    pub fn linkedlist_push_front_mut() {
        let mut list = LinkedList::from([20, 30]);

        // 在链表头部插入并立即调整
        let front = list.push_front_mut(10);
        *front += 5; // 10 -> 15

        assert_eq!(list, LinkedList::from([15, 20, 30]));
    }

    /// ## 1.95 之前
    /// ## 1.95 's before
    /// let mut list = LinkedList::from([1, 2]);
    /// list.push_back(3);
    /// let back = list.back_mut().unwrap();
    /// *back += 1;
    /// ```
    ///
    /// ## 1.95 方式
    /// ## 1.95 way
    pub fn linkedlist_push_back_mut() {
        let mut list = LinkedList::from([1, 2]);

        // 在链表尾部插入并立即调整
        let back = list.push_back_mut(3);
        *back += 7; // 3 -> 10

        assert_eq!(list, LinkedList::from([1, 2, 10]));
    }

    /// 综合示例：使用 `push_mut` 构建复杂对象
    /// synthesize example ： `push_mut` complex to
    /// 展示了在构建嵌套结构时，新方法如何减少样板代码。
    /// in structure ，method 。
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
/// 在类型系统中，它可用于编译期选择平台相关的常量。
/// in type system in ，platform constant 。
pub struct CfgSelectTypeExamples;

impl CfgSelectTypeExamples {
    /// 平台相关的最大数组长度提示
    /// platform maximum hint
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
/// ## 对比
/// ## to
/// ## to比
/// ## to
/// | 运算方式 | 溢出行为 | 适用场景 |
/// | way | as | scenario |
/// | 运算way | 溢出行as | 适用scenario |
/// | way | as | scenario |
/// | 普通 `+` | Debug panic / Release wrap | 绝大多数场景 |
/// | 普通 `+` | Debug panic / Release wrap | 绝大多数scenario |
/// | `saturating_add` | 饱和到边界 | 信号处理、颜色值、音频采样 |
/// | `saturating_add` | and to edge | 、、 |
/// | `wrapping_add` | 回绕 | 哈希、密码学、位运算 |
/// | `wrapping_add` | | 、、 |
/// ## 设计动机
/// ## design
/// - **信号处理**: 音频采样值溢出时不应回绕（会产生爆音）
/// - ****: （）
/// - **图形学**: RGB 颜色值溢出时应保持 255，不应回到 0
/// - ****: RGB 255，to 0
/// - **控制系统**: PID 控制器积分项不应因溢出而跳变
/// - **system **: PID because while
pub struct SaturatingTypeExamples;

impl SaturatingTypeExamples {
    /// 基础示例：饱和加法 vs 普通加法
    /// foundation example ：and vs
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
    /// ：and
    pub fn audio_sample_mix(a: i16, b: i16) -> i16 {
        let mixed = Saturating(a) + Saturating(b);
        mixed.0
    }

    /// 颜色值混合：RGB 通道饱和
    /// ：RGB channel and
    pub fn color_blend(c1: u8, c2: u8) -> u8 {
        (Saturating(c1) + Saturating(c2)).0
    }

    /// 乘法饱和：增益控制
    /// and ：
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
