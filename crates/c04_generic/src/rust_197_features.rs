//! Rust 197 Features

#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 泛型特性演示
/// # Rust 1.97 generic feature demonstration
/// Rust 1.97 稳定化coregeneric/set API：
/// - `BufRead` for `VecDeque<u8>`
/// - `BuildHasherDefault::new` const stable
pub struct Rust197GenericFeatures;

impl Rust197GenericFeatures {
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

    /// and `Extend` 配合Use，Implementation of"一次 collect，多个容器"。
    pub fn from_iterator_tuples_example() -> (Vec<i32>, Vec<String>) {
        let items = vec![(10, "ten".to_string()), (20, "twenty".to_string())];
        items.into_iter().collect()
    }

    pub fn extend_three_tuples() -> (Vec<i32>, Vec<i32>, Vec<i32>) {
        let mut result: (Vec<i32>, Vec<i32>, Vec<i32>) = (Vec::new(), Vec::new(), Vec::new());
        let items = vec![(1, 2, 3), (4, 5, 6)];
        result.extend(items);
        result
    }

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
