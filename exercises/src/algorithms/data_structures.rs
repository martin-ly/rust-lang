//! # 数据结构练习 / Data Structure Exercises
//!
//! 本模块包含经典数据结构的实现与练习：
//! - LRU 缓存
//! - Trie（前缀树）
//! - 并查集
//! - 最小栈
//! - 用栈实现队列

use indexmap::IndexMap;
use std::collections::HashMap;

/// LRU 缓存，基于 `IndexMap` 实现 O(1) 的 get/put。
pub struct LruCache<K, V> {
    map: IndexMap<K, V>,
    capacity: usize,
}

impl<K, V> LruCache<K, V>
where
    K: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    pub fn new(capacity: usize) -> Self {
        Self {
            map: IndexMap::with_capacity(capacity),
            capacity,
        }
    }

    pub fn get(&mut self, key: &K) -> Option<V> {
        if let Some((idx, _, _)) = self.map.get_full(key) {
            let value = self.map.shift_remove_index(idx).map(|(_, v)| v);
            if let Some(ref v) = value {
                self.map.insert(key.clone(), v.clone());
            }
            return value;
        }
        None
    }

    pub fn put(&mut self, key: K, value: V) {
        if self.capacity == 0 {
            return;
        }
        if self.map.contains_key(&key) {
            self.map.shift_remove(&key);
        } else if self.map.len() >= self.capacity {
            self.map.shift_remove_index(0);
        }
        self.map.insert(key, value);
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

/// Trie 节点。
#[derive(Default)]
pub struct TrieNode {
    children: HashMap<char, TrieNode>,
    is_end: bool,
}

/// 前缀树（Trie）。
#[derive(Default)]
pub struct Trie {
    root: TrieNode,
}

impl Trie {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, word: &str) {
        let mut node = &mut self.root;
        for ch in word.chars() {
            node = node.children.entry(ch).or_default();
        }
        node.is_end = true;
    }

    pub fn search(&self, word: &str) -> bool {
        self.find_node(word).is_some_and(|n| n.is_end)
    }

    pub fn starts_with(&self, prefix: &str) -> bool {
        self.find_node(prefix).is_some()
    }

    fn find_node(&self, word: &str) -> Option<&TrieNode> {
        let mut node = &self.root;
        for ch in word.chars() {
            let next = node.children.get(&ch)?;
            node = next;
        }
        Some(node)
    }
}

/// 并查集：支持路径压缩与按秩合并。
pub struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

impl UnionFind {
    pub fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    pub fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }

    pub fn union(&mut self, x: usize, y: usize) -> bool {
        let root_x = self.find(x);
        let root_y = self.find(y);
        if root_x == root_y {
            return false;
        }
        match self.rank[root_x].cmp(&self.rank[root_y]) {
            std::cmp::Ordering::Less => self.parent[root_x] = root_y,
            std::cmp::Ordering::Greater => self.parent[root_y] = root_x,
            std::cmp::Ordering::Equal => {
                self.parent[root_y] = root_x;
                self.rank[root_x] += 1;
            }
        }
        true
    }

    pub fn connected(&mut self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }
}

/// 最小栈：支持 O(1) 的 push、pop、top、get_min。
pub struct MinStack {
    stack: Vec<(i32, i32)>,
}

impl Default for MinStack {
    fn default() -> Self {
        Self::new()
    }
}

impl MinStack {
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    pub fn push(&mut self, val: i32) {
        let min = if let Some(&(_, current_min)) = self.stack.last() {
            val.min(current_min)
        } else {
            val
        };
        self.stack.push((val, min));
    }

    pub fn pop(&mut self) -> Option<i32> {
        self.stack.pop().map(|(val, _)| val)
    }

    pub fn top(&self) -> Option<i32> {
        self.stack.last().map(|(val, _)| *val)
    }

    pub fn get_min(&self) -> Option<i32> {
        self.stack.last().map(|(_, min)| *min)
    }
}

/// 用两个栈实现队列。
pub struct MyQueue {
    in_stack: Vec<i32>,
    out_stack: Vec<i32>,
}

impl Default for MyQueue {
    fn default() -> Self {
        Self::new()
    }
}

impl MyQueue {
    pub fn new() -> Self {
        Self {
            in_stack: Vec::new(),
            out_stack: Vec::new(),
        }
    }

    pub fn push(&mut self, x: i32) {
        self.in_stack.push(x);
    }

    pub fn pop(&mut self) -> Option<i32> {
        self.peek();
        self.out_stack.pop()
    }

    pub fn peek(&mut self) -> Option<i32> {
        if self.out_stack.is_empty() {
            while let Some(v) = self.in_stack.pop() {
                self.out_stack.push(v);
            }
        }
        self.out_stack.last().copied()
    }

    pub fn is_empty(&self) -> bool {
        self.in_stack.is_empty() && self.out_stack.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lru_cache_basic() {
        let mut cache = LruCache::new(2);
        cache.put(1, 1);
        cache.put(2, 2);
        assert_eq!(cache.get(&1), Some(1));
        cache.put(3, 3);
        assert_eq!(cache.get(&2), None);
        cache.put(4, 4);
        assert_eq!(cache.get(&1), None);
        assert_eq!(cache.get(&3), Some(3));
        assert_eq!(cache.get(&4), Some(4));
    }

    #[test]
    fn test_lru_cache_zero_capacity() {
        let mut cache = LruCache::new(0);
        cache.put(1, 1);
        assert_eq!(cache.get(&1), None);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_trie_basic() {
        let mut trie = Trie::new();
        trie.insert("apple");
        assert!(trie.search("apple"));
        assert!(!trie.search("app"));
        assert!(trie.starts_with("app"));
        trie.insert("app");
        assert!(trie.search("app"));
    }

    #[test]
    fn test_union_find() {
        let mut uf = UnionFind::new(5);
        uf.union(0, 1);
        uf.union(2, 3);
        assert!(uf.connected(0, 1));
        assert!(uf.connected(2, 3));
        assert!(!uf.connected(1, 2));
        uf.union(1, 2);
        assert!(uf.connected(0, 3));
    }

    #[test]
    fn test_min_stack() {
        let mut stack = MinStack::new();
        stack.push(-2);
        stack.push(0);
        stack.push(-3);
        assert_eq!(stack.get_min(), Some(-3));
        assert_eq!(stack.pop(), Some(-3));
        assert_eq!(stack.top(), Some(0));
        assert_eq!(stack.get_min(), Some(-2));
    }

    #[test]
    fn test_my_queue() {
        let mut q = MyQueue::new();
        q.push(1);
        q.push(2);
        assert_eq!(q.peek(), Some(1));
        assert_eq!(q.pop(), Some(1));
        assert_eq!(q.pop(), Some(2));
        assert!(q.is_empty());
    }
}
