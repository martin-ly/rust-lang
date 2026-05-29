//! Rust 1.97 特性跟踪模块 —— 泛型与高级类型
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 泛型特性演示
///
/// Rust 1.97 稳定化的核心泛型/集合 API：
/// - `impl Extend` for tuples with arity 1 through 12
/// - `impl FromIterator<(A, ...)>` for tuples with arity 1 through 12
/// - `BufRead` for `VecDeque<u8>`
/// - `BuildHasherDefault::new` const stable
pub struct Rust197GenericFeatures;

impl Rust197GenericFeatures {
    /// 使用元组的 `Extend` trait 并行收集多个迭代器的结果
    ///
    /// Rust 1.97 为元组实现了 `Extend`，允许一次向多个集合追加元素。
    pub fn extend_tuples_example() -> (Vec<i32>, Vec<String>) {
        let mut result: (Vec<i32>, Vec<String>) = (Vec::new(), Vec::new());
        let items = vec![
            (1, "one".to_string()),
            (2, "two".to_string()),
            (3, "three".to_string()),
        ];
        result.extend(items);
        result
    }

    /// 使用 `FromIterator` 为元组从迭代器构造并行集合
    ///
    /// 与 `Extend` 配合使用，实现"一次 collect，多个容器"。
    pub fn from_iterator_tuples_example() -> (Vec<i32>, Vec<String>) {
        let items = vec![(10, "ten".to_string()), (20, "twenty".to_string())];
        items.into_iter().collect()
    }

    /// 三元组版本的 `Extend` 演示
    pub fn extend_three_tuples() -> (Vec<i32>, Vec<i32>, Vec<i32>) {
        let mut result: (Vec<i32>, Vec<i32>, Vec<i32>) = (Vec::new(), Vec::new(), Vec::new());
        let items = vec![(1, 2, 3), (4, 5, 6)];
        result.extend(items);
        result
    }

    /// 使用 `BuildHasherDefault::new` 在 const 上下文中构造哈希构建器
    pub const fn const_build_hasher()
    -> std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher> {
        std::hash::BuildHasherDefault::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extend_tuples() {
        let (nums, strings) = Rust197GenericFeatures::extend_tuples_example();
        assert_eq!(nums, vec![1, 2, 3]);
        assert_eq!(strings, vec!["one", "two", "three"]);
    }

    #[test]
    fn test_from_iterator_tuples() {
        let (nums, strings) = Rust197GenericFeatures::from_iterator_tuples_example();
        assert_eq!(nums, vec![10, 20]);
        assert_eq!(strings, vec!["ten", "twenty"]);
    }

    #[test]
    fn test_extend_three_tuples() {
        let (a, b, c) = Rust197GenericFeatures::extend_three_tuples();
        assert_eq!(a, vec![1, 4]);
        assert_eq!(b, vec![2, 5]);
        assert_eq!(c, vec![3, 6]);
    }

    #[test]
    fn test_const_build_hasher() {
        let _ = Rust197GenericFeatures::const_build_hasher();
    }
}
