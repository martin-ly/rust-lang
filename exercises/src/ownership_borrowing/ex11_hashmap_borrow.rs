//! # 练习 11: HashMap 的借用冲突 / Exercise 11: HashMap Borrow Conflicts
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: 不能同时持有 `HashMap` 的引用并修改它
//!   Cannot hold a reference to a `HashMap` while modifying it
//!
//! ## 题目描述 / Problem Description
//!
//! 实现 `increment_or_insert`：如果 key 存在，将其对应的值加 1；
//! 如果不存在，插入默认值 `1`。
//!
//! 注意：不能在对 `HashMap` 的引用仍然存在时调用 `insert`。
//! 需要先释放引用，或先完成读取再修改。
//!
//! ## 提示 / Hints
//!
//! - 使用 `if let Some(v) = map.get_mut(key)` 获取可变引用，修改后离开作用域
//! - 否则调用 `map.insert(key, 1)`
//! - 不能让 `get`/`get_mut` 的借用与 `insert` 重叠

use std::collections::HashMap;
use std::hash::Hash;

/// 若 key 存在则值加 1，否则插入 1
/// Increments the value if key exists, otherwise inserts 1
#[allow(clippy::map_entry)] // 本练习刻意展示显式可变借用释放，而非使用 Entry API
pub fn increment_or_insert<K>(map: &mut HashMap<K, i32>, key: K)
where
    K: Eq + Hash,
{
    if map.contains_key(&key) {
        // get_mut 的可变借用在此语句结束后立即释放
        *map.get_mut(&key).unwrap() += 1;
    } else {
        map.insert(key, 1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_increment_existing() {
        let mut map = HashMap::new();
        map.insert("a", 5);
        increment_or_insert(&mut map, "a");
        assert_eq!(map.get("a"), Some(&6));
    }

    #[test]
    fn test_insert_new() {
        let mut map = HashMap::new();
        increment_or_insert(&mut map, "b");
        assert_eq!(map.get("b"), Some(&1));
    }

    #[test]
    fn test_multiple_calls() {
        let mut map = HashMap::new();
        increment_or_insert(&mut map, "k");
        increment_or_insert(&mut map, "k");
        increment_or_insert(&mut map, "k");
        assert_eq!(map.get("k"), Some(&3));
    }
}
