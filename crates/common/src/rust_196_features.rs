//! Rust 1.96 特性跟踪模块 —— 通用工具场景（参考实现）
//!
//! 本模块作为 **Rust 1.96 稳定新特性的参考实现**，集中展示所有 1.96 特性：
//! - `core::range` 完整家族（`Range`、`RangeInclusive`、`RangeFrom`、`RangeToInclusive`）
//! - `assert_matches!` 宏
//! - `From<T>` for `LazyCell` / `LazyLock` / `AssertUnwindSafe`
//! - `ManuallyDrop` 用法
//! - `NonZero` 范围迭代
//! - `never type` 元组 coercion

#![allow(clippy::incompatible_msrv)]

use std::assert_matches;
use std::cell::LazyCell;
use std::mem::ManuallyDrop;
use std::num::NonZero;
use std::panic::AssertUnwindSafe;
use std::sync::LazyLock;

// ============================================================================
// core::range 完整家族
// ============================================================================

/// `core::range` 范围工具集合
pub struct RangeFamilyExamples;

impl RangeFamilyExamples {
    /// 使用 `core::range::Range` 创建左闭右开区间
    pub fn make_range(start: usize, end: usize) -> core::range::Range<usize> {
        core::range::Range { start, end }
    }

    /// 使用 `core::range::RangeInclusive` 创建闭区间
    pub fn make_range_inclusive(start: usize, last: usize) -> core::range::RangeInclusive<usize> {
        core::range::RangeInclusive { start, last }
    }

    /// 使用 `core::range::RangeFrom` 创建从某位置开始到无穷
    pub fn make_range_from(start: usize) -> core::range::RangeFrom<usize> {
        core::range::RangeFrom { start }
    }

    /// 使用 `core::range::RangeToInclusive` 创建从开头到某位置的闭区间
    pub fn make_range_to_inclusive(last: usize) -> core::range::RangeToInclusive<usize> {
        core::range::RangeToInclusive { last }
    }

    /// 计算范围长度
    pub fn range_len(r: &core::range::Range<usize>) -> usize {
        r.end.saturating_sub(r.start)
    }

    /// 计算闭区间包含的元素数量
    pub fn range_inclusive_len(r: &core::range::RangeInclusive<usize>) -> usize {
        r.last.saturating_sub(r.start) + 1
    }
}

// ============================================================================
// assert_matches! 宏
// ============================================================================

/// 匹配测试示例类型
#[derive(Debug, Clone, PartialEq)]
pub enum MatchExample {
    /// 数值变体
    Number(i32),
    /// 字符串变体
    Text(String),
    /// 复合变体
    Pair { first: i32, second: i32 },
    /// 空变体
    Nothing,
}

/// `assert_matches!` 断言工具
pub struct AssertMatchesExamples;

impl AssertMatchesExamples {
    /// 断言值为 Number 变体
    pub fn assert_is_number(val: &MatchExample) {
        assert_matches!(val, MatchExample::Number(_));
    }

    /// 断言值为特定数值
    pub fn assert_is_number_42(val: &MatchExample) {
        assert_matches!(val, MatchExample::Number(42));
    }

    /// 断言值为 Text 且内容非空
    pub fn assert_is_non_empty_text(val: &MatchExample) {
        assert_matches!(val, MatchExample::Text(s) if !s.is_empty());
    }

    /// 断言值为 Pair 且满足条件
    pub fn assert_pair_sum(val: &MatchExample, expected_sum: i32) {
        assert_matches!(
            val,
            MatchExample::Pair { first, second } if first + second == expected_sum
        );
    }

    /// 断言值为 Nothing
    pub fn assert_is_nothing(val: &MatchExample) {
        assert_matches!(val, MatchExample::Nothing);
    }
}

// ============================================================================
// From<T> for LazyCell / LazyLock / AssertUnwindSafe
// ============================================================================

/// 利用 `From<T>` 立即初始化懒加载和 panic 包装类型的示例
pub struct FromInitExamples;

impl FromInitExamples {
    /// 从值直接创建 `LazyLock`（无需闭包）
    pub fn lazy_lock_from_value() -> LazyLock<String> {
        LazyLock::from("initialized".to_string())
    }

    /// 从值直接创建 `LazyCell`（无需闭包）
    pub fn lazy_cell_from_value() -> LazyCell<i32> {
        LazyCell::from(42)
    }

    /// 从值直接创建 `AssertUnwindSafe`
    pub fn assert_unwind_safe_from_value() -> AssertUnwindSafe<Vec<u8>> {
        AssertUnwindSafe::from(vec![1, 2, 3])
    }

    /// 创建包含多种 From<T> 初始化类型的元组
    pub fn mixed_init_tuple() -> (LazyLock<i32>, LazyCell<String>, AssertUnwindSafe<bool>) {
        (
            LazyLock::from(100),
            LazyCell::from("hello".to_string()),
            AssertUnwindSafe::from(true),
        )
    }
}

// ============================================================================
// ManuallyDrop 用法
// ============================================================================

/// 使用 `ManuallyDrop` 控制析构时机的示例
pub struct ManuallyDropExamples;

impl ManuallyDropExamples {
    /// 创建 ManuallyDrop 包装的值
    pub fn wrap_without_drop<T>(value: T) -> ManuallyDrop<T> {
        ManuallyDrop::new(value)
    }

    /// 安全取出内部值（不调用 drop）
    pub fn unwrap_without_drop<T>(md: ManuallyDrop<T>) -> T {
        ManuallyDrop::into_inner(md)
    }

    /// 通过 Deref 访问内部值
    pub fn peek_inner<T: AsRef<str>>(md: &ManuallyDrop<T>) -> &str {
        md.as_ref()
    }

    /// 演示：将 Vec 包装为 ManuallyDrop 后手动管理内存
    pub fn manually_drop_vec() {
        let md = ManuallyDrop::new(vec![1, 2, 3, 4, 5]);
        // 可以安全地读取
        assert_eq!(md.len(), 5);
        // 手动取出，不会调用 Vec 的 drop
        let _inner = ManuallyDrop::into_inner(md);
        // 此处不触发析构
    }
}

// ============================================================================
// NonZero 范围迭代
// ============================================================================

/// `NonZero` 类型范围迭代示例
pub struct NonZeroRangeExamples;

impl NonZeroRangeExamples {
    /// 遍历 NonZero<u8> 闭区间并收集
    pub fn collect_nonzero_range(start: u8, end: u8) -> Vec<NonZero<u8>> {
        let s = NonZero::new(start).expect("start must be non-zero");
        let e = NonZero::new(end).expect("end must be non-zero");
        (s..=e).collect()
    }

    /// 计算 NonZero<u16> 范围内的元素数量
    pub fn count_nonzero_range(start: u16, end: u16) -> usize {
        let s = NonZero::new(start).expect("start must be non-zero");
        let e = NonZero::new(end).expect("end must be non-zero");
        (s..=e).count()
    }

    /// 对 NonZero<u32> 范围求和
    pub fn sum_nonzero_range(start: u32, end: u32) -> u32 {
        let s = NonZero::new(start).expect("start must be non-zero");
        let e = NonZero::new(end).expect("end must be non-zero");
        (s..=e).map(|nz| nz.get()).sum()
    }

    /// 查找 NonZero 范围内第一个满足条件的值
    pub fn find_in_nonzero_range(
        start: u8,
        end: u8,
        predicate: impl Fn(u8) -> bool,
    ) -> Option<NonZero<u8>> {
        let s = NonZero::new(start)?;
        let e = NonZero::new(end)?;
        (s..=e).find(|nz| predicate(nz.get()))
    }
}

// ============================================================================
// never type 元组 coercion
// ============================================================================

/// `!` 类型在元组中的 coercion 示例
pub struct NeverTypeTupleExamples;

impl NeverTypeTupleExamples {
    /// 错误路径返回 `!`，在元组中自动 coercion 为目标类型
    pub fn error_path_tuple() -> (i32, String, bool) {
        if false {
            return (1, "ok".to_string(), true);
        }
        // panic!() 返回 !，在元组上下文中 coercion 为 (i32, String, bool)
        (0, panic!("coercion demo"), false)
    }

    /// 使用 unreachable!() 的 coercion
    pub fn unreachable_path_tuple() -> (u64, &'static str) {
        if false {
            return (42, "reachable");
        }
        // unreachable!() 返回 !，coercion 为 (u64, &'static str)
        (0, unreachable!("never happens"))
    }

    /// 通过返回 ! 的函数进行 coercion
    fn always_panic() -> ! {
        panic!("always panics")
    }

    /// 在元组中使用返回 ! 的函数
    pub fn tuple_with_never_function() -> (usize, u8) {
        if false {
            return (10, 20);
        }
        (0, Self::always_panic())
    }
}

// ============================================================================
// 演示函数
// ============================================================================

/// 集中演示所有 Rust 1.96 特性
pub fn demonstrate_all_rust_196_features() {
    println!("\n=== Rust 1.96 全特性参考演示 ===");

    // core::range
    let r = RangeFamilyExamples::make_range(0, 10);
    println!(
        "Range: {}..{} (len={})",
        r.start,
        r.end,
        RangeFamilyExamples::range_len(&r)
    );

    let ri = RangeFamilyExamples::make_range_inclusive(1, 5);
    println!(
        "RangeInclusive: {}..={} (len={})",
        ri.start,
        ri.last,
        RangeFamilyExamples::range_inclusive_len(&ri)
    );

    // assert_matches!
    let val = MatchExample::Number(42);
    AssertMatchesExamples::assert_is_number_42(&val);

    // From<T>
    let lock = FromInitExamples::lazy_lock_from_value();
    println!("LazyLock: {}", *lock);

    // ManuallyDrop
    ManuallyDropExamples::manually_drop_vec();

    // NonZero range
    let nz_vec = NonZeroRangeExamples::collect_nonzero_range(1, 5);
    println!(
        "NonZero range: {:?}",
        nz_vec.iter().map(|n| n.get()).collect::<Vec<_>>()
    );

    println!("=== 演示完成 ===\n");
}

/// 获取 Rust 1.96 特性信息
pub fn get_rust_196_feature_info() -> String {
    "Rust 1.96 稳定特性参考:\n- core::range family (Range, RangeInclusive, RangeFrom, \
     RangeToInclusive)\n- assert_matches! macro\n- From<T> for LazyCell / LazyLock / \
     AssertUnwindSafe\n- ManuallyDrop patterns\n- NonZero range iteration\n- never type tuple \
     coercion"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    // core::range 测试
    #[test]
    fn test_range_fields() {
        let r = RangeFamilyExamples::make_range(5, 15);
        assert_eq!(r.start, 5);
        assert_eq!(r.end, 15);
        assert_eq!(RangeFamilyExamples::range_len(&r), 10);
    }

    #[test]
    fn test_range_inclusive_fields() {
        let ri = RangeFamilyExamples::make_range_inclusive(1, 3);
        assert_eq!(ri.start, 1);
        assert_eq!(ri.last, 3);
        assert_eq!(RangeFamilyExamples::range_inclusive_len(&ri), 3);
    }

    #[test]
    fn test_range_from() {
        let rf = RangeFamilyExamples::make_range_from(5);
        assert_eq!(rf.start, 5);
    }

    #[test]
    fn test_range_to_inclusive() {
        let rti = RangeFamilyExamples::make_range_to_inclusive(10);
        assert_eq!(rti.last, 10);
    }

    // assert_matches! 测试
    #[test]
    fn test_assert_is_number() {
        let val = MatchExample::Number(7);
        AssertMatchesExamples::assert_is_number(&val);
    }

    #[test]
    fn test_assert_is_number_42() {
        let val = MatchExample::Number(42);
        AssertMatchesExamples::assert_is_number_42(&val);
    }

    #[test]
    #[should_panic]
    fn test_assert_is_number_42_fails() {
        let val = MatchExample::Number(99);
        AssertMatchesExamples::assert_is_number_42(&val);
    }

    #[test]
    fn test_assert_is_non_empty_text() {
        let val = MatchExample::Text("hello".to_string());
        AssertMatchesExamples::assert_is_non_empty_text(&val);
    }

    #[test]
    fn test_assert_pair_sum() {
        let val = MatchExample::Pair {
            first: 10,
            second: 20,
        };
        AssertMatchesExamples::assert_pair_sum(&val, 30);
    }

    #[test]
    fn test_assert_is_nothing() {
        let val = MatchExample::Nothing;
        AssertMatchesExamples::assert_is_nothing(&val);
    }

    // From<T> 测试
    #[test]
    fn test_lazy_lock_from_value() {
        let lock = FromInitExamples::lazy_lock_from_value();
        assert_eq!(*lock, "initialized");
    }

    #[test]
    fn test_lazy_cell_from_value() {
        let cell = FromInitExamples::lazy_cell_from_value();
        assert_eq!(*cell, 42);
    }

    #[test]
    fn test_assert_unwind_safe_from_value() {
        let aws = FromInitExamples::assert_unwind_safe_from_value();
        assert_eq!(aws.0, vec![1, 2, 3]);
    }

    #[test]
    fn test_mixed_init_tuple() {
        let (lock, cell, aws) = FromInitExamples::mixed_init_tuple();
        assert_eq!(*lock, 100);
        assert_eq!(*cell, "hello");
        assert!(aws.0);
    }

    // ManuallyDrop 测试
    #[test]
    fn test_wrap_and_unwrap_without_drop() {
        let md = ManuallyDropExamples::wrap_without_drop(vec![1, 2, 3]);
        let inner = ManuallyDropExamples::unwrap_without_drop(md);
        assert_eq!(inner, vec![1, 2, 3]);
    }

    #[test]
    fn test_peek_inner() {
        let md = ManuallyDrop::new("peek".to_string());
        assert_eq!(ManuallyDropExamples::peek_inner(&md), "peek");
    }

    #[test]
    fn test_manually_drop_vec() {
        ManuallyDropExamples::manually_drop_vec();
        // 如果发生 double-free 或异常，测试会失败
    }

    // NonZero 范围迭代测试
    #[test]
    fn test_collect_nonzero_range() {
        let v = NonZeroRangeExamples::collect_nonzero_range(1, 3);
        assert_eq!(v.len(), 3);
        assert_eq!(v[0].get(), 1);
        assert_eq!(v[1].get(), 2);
        assert_eq!(v[2].get(), 3);
    }

    #[test]
    fn test_count_nonzero_range() {
        assert_eq!(NonZeroRangeExamples::count_nonzero_range(5, 10), 6);
    }

    #[test]
    fn test_sum_nonzero_range() {
        // 1+2+3+4+5 = 15
        assert_eq!(NonZeroRangeExamples::sum_nonzero_range(1, 5), 15);
    }

    #[test]
    fn test_find_in_nonzero_range() {
        let found = NonZeroRangeExamples::find_in_nonzero_range(1, 10, |n| n == 7);
        assert_eq!(found.map(|nz| nz.get()), Some(7));

        let not_found = NonZeroRangeExamples::find_in_nonzero_range(1, 5, |n| n == 10);
        assert_eq!(not_found, None);
    }

    // never type 元组 coercion 测试
    #[test]
    #[should_panic(expected = "coercion demo")]
    fn test_error_path_tuple() {
        NeverTypeTupleExamples::error_path_tuple();
    }

    #[test]
    #[should_panic(expected = "never happens")]
    fn test_unreachable_path_tuple() {
        NeverTypeTupleExamples::unreachable_path_tuple();
    }

    #[test]
    #[should_panic(expected = "always panics")]
    fn test_tuple_with_never_function() {
        NeverTypeTupleExamples::tuple_with_never_function();
    }

    // 信息函数测试
    #[test]
    fn test_get_rust_196_feature_info() {
        let info = get_rust_196_feature_info();
        assert!(info.contains("core::range"));
        assert!(info.contains("assert_matches!"));
        assert!(info.contains("LazyCell"));
        assert!(info.contains("NonZero"));
    }
}
