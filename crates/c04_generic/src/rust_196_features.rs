//! - **`core::range`**: 泛型边界场景下直接构造范围类型
//! - **`core::range`**: generic edge scenario under scope type

use std::{cell::LazyCell, sync::LazyLock};

// ==================== LazyLock / LazyCell::from 在泛型中的应用 ====================

/// 泛型惰性容器构造
/// generic
pub fn create_generic_lazy_lock<T>(value: T) -> LazyLock<T>
where
    T: Send + Sync,
{
    LazyLock::from(value)
}

/// 泛型惰性单元格构造
/// generic
pub fn create_generic_lazy_cell<T>(value: T) -> LazyCell<T> {
    LazyCell::from(value)
}

pub struct GenericLazyCache<T> {
    cache: LazyLock<T>,
}

impl<T: Send + Sync> GenericLazyCache<T> {
    /// 从已计算的值创建缓存
    /// from
    pub fn from_value(value: T) -> Self {
        Self {
            cache: LazyLock::from(value),
        }
    }

    /// 获取缓存值
    /// Gets缓存值
    pub fn get(&self) -> &T {
        &self.cache
    }
}

// ==================== core::range 与泛型边界 ====================

/// 泛型范围过滤
/// generic scope
pub fn generic_filter_by_range<T>(items: &[T], range: core::range::Range<usize>) -> Vec<&T> {
    let core::range::Range { start, end } = range;
    items
        .iter()
        .skip(start)
        .take(end.saturating_sub(start))
        .collect()
}

/// 泛型包含边界范围切片
/// generic edge scope
pub fn generic_slice_inclusive<T>(items: &[T], bounds: core::range::RangeInclusive<usize>) -> &[T] {
    let core::range::RangeInclusive { start, last } = bounds;
    let len = items.len();
    let real_start = start.min(len);
    let real_end = (last + 1).min(len);
    &items[real_start..real_end]
}

/// 泛型起始范围收集
/// generic scope
pub fn generic_collect_from<T: Clone>(items: &[T], from: core::range::RangeFrom<usize>) -> Vec<T> {
    let core::range::RangeFrom { start } = from;
    items.iter().skip(start).cloned().collect()
}

// ==================== assert_matches! 与泛型枚举 ====================

/// 泛型状态枚举
/// generic state enum
#[derive(Debug, Clone, PartialEq)]
pub enum State<T, E> {
    Idle,
    Processing(T),
    Completed(T),
    Failed(E),
}

/// 状态机转换
/// state machine conversion
pub fn state_machine_transition<T, E>(current: State<T, E>, input: T) -> State<T, E>
where
    T: Clone,
{
    match current {
        State::Idle => State::Processing(input),
        State::Processing(_) => State::Completed(input),
        State::Completed(v) => State::Completed(v),
        State::Failed(e) => State::Failed(e),
    }
}

// ==================== 演示函数 ====================

/// 演示 Rust 1.96 泛型特性
/// Demonstrates Rust 1.96 泛型特性
/// demonstration Rust 1.96 generic feature
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 泛型特性演示");
    println!("========================================\n");

    println!("--- LazyLock::from / LazyCell::from ---");
    let lock: LazyLock<i32> = LazyLock::from(100);
    println!("LazyLock value = {}", *lock);

    let cell: LazyCell<String> = LazyCell::from(String::from("hello"));
    println!("LazyCell value = {}", *cell);

    println!("\n--- core::range 泛型边界 ---");
    let items = vec![10, 20, 30, 40, 50];
    let range = core::range::Range { start: 1, end: 4 };
    let filtered = generic_filter_by_range(&items, range);
    println!("filtered [1..4] = {:?}", filtered);

    let inc = core::range::RangeInclusive { start: 0, last: 2 };
    let sliced = generic_slice_inclusive(&items, inc);
    println!("sliced [0..=2] = {:?}", sliced);

    println!("\n--- assert_matches! 泛型枚举 ---");
    let state: State<i32, &str> = State::Processing(42);
    println!("state = {:?}", state);

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
/// Gets特性信息
/// feature
pub fn get_rust_196_generic_info() -> String {
    "Rust 1.96.0 泛型特性:\n\
     - LazyLock::from(value) / LazyCell::from(value) 直接构造\n\
     - core::range 字段公开，泛型函数中直接构造范围\n\
     - assert_matches! 支持泛型枚举模式断言"
        .to_string()
}

#[cfg(test)]
mod tests {
    use std::assert_matches;

    use super::*;

    #[test]
    fn test_create_generic_lazy_lock() {
        let lock: LazyLock<i32> = create_generic_lazy_lock(42);
        assert_eq!(*lock, 42);
    }

    #[test]
    fn test_create_generic_lazy_cell() {
        let cell: LazyCell<String> = create_generic_lazy_cell(String::from("test"));
        assert_eq!(cell.as_str(), "test");
    }

    #[test]
    fn test_generic_lazy_cache() {
        let cache = GenericLazyCache::from_value(vec![1, 2, 3]);
        assert_eq!(cache.get(), &[1, 2, 3]);
    }

    #[test]
    fn test_generic_filter_by_range() {
        let items = vec!['a', 'b', 'c', 'd', 'e'];
        let range = core::range::Range { start: 1, end: 4 };
        let result = generic_filter_by_range(&items, range);
        assert_eq!(result, vec![&'b', &'c', &'d']);
    }

    #[test]
    fn test_generic_slice_inclusive() {
        let items = vec![10, 20, 30, 40];
        let bounds = core::range::RangeInclusive { start: 0, last: 2 };
        assert_eq!(generic_slice_inclusive(&items, bounds), &[10, 20, 30]);
    }

    #[test]
    fn test_generic_collect_from() {
        let items = vec![1, 2, 3, 4, 5];
        let from = core::range::RangeFrom { start: 2 };
        assert_eq!(generic_collect_from(&items, from), vec![3, 4, 5]);
    }

    #[test]
    fn test_state_machine_transition() {
        let idle: State<i32, &str> = State::Idle;
        let processing = state_machine_transition(idle, 10);
        assert_matches!(processing, State::Processing(10));

        let completed = state_machine_transition(processing, 20);
        assert_matches!(completed, State::Completed(20)); // uses new input from Processing

        let failed: State<i32, &str> = State::Failed("error");
        let still_failed = state_machine_transition(failed, 0);
        assert_matches!(still_failed, State::Failed("error"));
    }

    #[test]
    fn test_assert_matches_generic_enum() {
        let state: State<String, i32> = State::Completed(String::from("done"));
        assert_matches!(state, State::Completed(_));
        assert_matches!(state, State::Completed(s) if s == "done");
    }

    #[test]
    fn test_get_rust_196_generic_info() {
        let info = get_rust_196_generic_info();
        assert!(info.contains("LazyLock::from"));
        assert!(info.contains("core::range"));
    }
}
