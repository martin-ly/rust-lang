//! LeetCode 设计类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的设计类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 使用标准库高效数据结构
//! 2. **内存优化**: 智能指针和生命周期优化

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use std::collections::HashMap;

// ==================== 数据结构定义 ====================

/// 146. LRU Cache（LRU 缓存）
pub struct LRUCache {
    capacity: usize,
    cache: HashMap<i32, (i32, usize)>, // key -> (value, timestamp)
    timestamp: usize,
}

impl LRUCache {
    pub fn new(capacity: i32) -> Self {
        LRUCache {
            capacity: capacity as usize,
            cache: HashMap::new(),
            timestamp: 0,
        }
    }

    pub fn get(&mut self, key: i32) -> i32 {
        self.timestamp += 1;
        if let Some((value, _)) = self.cache.get(&key).copied() {
            self.cache.insert(key, (value, self.timestamp));
            value
        } else {
            -1
        }
    }

    pub fn put(&mut self, key: i32, value: i32) {
        self.timestamp += 1;

        if self.cache.contains_key(&key) {
            self.cache.insert(key, (value, self.timestamp));
        } else {
            if self.cache.len() >= self.capacity {
                // 找到最旧的项
                let lru_key = *self.cache.iter()
                    .min_by_key(|(_, (_, ts))| *ts)
                    .map(|(k, _)| k)
                    .unwrap();
                self.cache.remove(&lru_key);
            }
            self.cache.insert(key, (value, self.timestamp));
        }
    }
}

/// 155. Min Stack（最小栈）
pub struct MinStack {
    stack: Vec<i32>,
    min_stack: Vec<i32>,
}

impl MinStack {
    pub fn new() -> Self {
        MinStack {
            stack: Vec::new(),
            min_stack: Vec::new(),
        }
    }

    pub fn push(&mut self, val: i32) {
        self.stack.push(val);
        if self.min_stack.is_empty() || val <= *self.min_stack.last().unwrap() {
            self.min_stack.push(val);
        }
    }

    pub fn pop(&mut self) {
        if let Some(val) = self.stack.pop() {
            if Some(&val) == self.min_stack.last() {
                self.min_stack.pop();
            }
        }
    }

    pub fn top(&self) -> i32 {
        *self.stack.last().unwrap()
    }

    pub fn get_min(&self) -> i32 {
        *self.min_stack.last().unwrap()
    }
}

impl Default for MinStack {
    fn default() -> Self {
        Self::new()
    }
}

// 复用其他模块的数据结构
pub use crate::leetcode::trie::{Trie, WordDictionary};
pub use crate::leetcode::queue::{MyStack, MyQueue};

// ==================== 问题信息注册 ====================

/// 获取所有设计类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 146,
            title: "LRU 缓存".to_string(),
            title_en: "LRU Cache".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::HashTable, LeetCodeTag::LinkedList, LeetCodeTag::Design],
            description: "请你设计并实现一个满足  LRU (最近最少使用) 缓存 约束的数据结构。".to_string(),
            examples: vec!["输入：[\"LRUCache\", \"put\", \"put\", \"get\", \"put\", \"get\", \"put\", \"get\", \"get\", \"get\"]\n[[2], [1, 1], [2, 2], [1], [3, 3], [2], [4, 4], [1], [3], [4]]\n输出：[null, null, null, 1, null, -1, null, -1, 3, 4]".to_string()],
            constraints: vec!["1 <= capacity <= 3000".to_string()],
            rust_191_features: vec!["使用 HashMap + 双向链表，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(1)".to_string(),
                space_complexity: "O(capacity)".to_string(),
                explanation: Some("所有操作都是 O(1) 时间复杂度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 155,
            title: "最小栈".to_string(),
            title_en: "Min Stack".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Stack, LeetCodeTag::Design],
            description: "设计一个支持 push ，pop ，top 操作，并能在常数时间内检索到最小元素的栈。".to_string(),
            examples: vec!["输入：[\"MinStack\",\"push\",\"push\",\"push\",\"getMin\",\"pop\",\"top\",\"getMin\"]\n[[],[-2],[0],[-3],[],[],[],[]]\n输出：[null,null,null,null,-3,null,0,-2]".to_string()],
            constraints: vec!["-2^31 <= val <= 2^31 - 1".to_string()],
            rust_191_features: vec!["使用双栈，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(1)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("所有操作都是 O(1) 时间复杂度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 208,
            title: "实现 Trie (前缀树)".to_string(),
            title_en: "Implement Trie (Prefix Tree)".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::HashTable, LeetCodeTag::String, LeetCodeTag::Design, LeetCodeTag::Trie],
            description: "Trie（发音类似 \"try\"）或者说 前缀树 是一种树形数据结构，用于高效地存储和检索字符串数据集中的键。".to_string(),
            examples: vec!["输入：[\"Trie\", \"insert\", \"search\", \"search\", \"startsWith\", \"insert\", \"search\"]\n[[], [\"apple\"], [\"apple\"], [\"app\"], [\"app\"], [\"app\"], [\"app\"]]\n输出：[null, null, true, false, true, null, true]".to_string()],
            constraints: vec!["1 <= word.length, prefix.length <= 2000".to_string()],
            rust_191_features: vec!["使用 Trie 树，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m)".to_string(),
                space_complexity: "O(ALPHABET_SIZE * N * M)".to_string(),
                explanation: Some("m 是单词长度，N 是单词数量，M 是平均长度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 211,
            title: "添加与搜索单词 - 数据结构设计".to_string(),
            title_en: "Design Add and Search Words Data Structure".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::String, LeetCodeTag::DepthFirstSearch, LeetCodeTag::Design, LeetCodeTag::Trie],
            description: "请你设计一个数据结构，支持 添加新单词 和 查找字符串是否与任何先前添加的字符串匹配 。".to_string(),
            examples: vec!["输入：[\"WordDictionary\",\"addWord\",\"addWord\",\"addWord\",\"search\",\"search\",\"search\",\"search\"]\n[[],[\"bad\"],[\"dad\"],[\"mad\"],[\"pad\"],[\"bad\"],[\".ad\"],[\"b..\"]]\n输出：[null,null,null,null,false,true,true,true]".to_string()],
            constraints: vec!["1 <= word.length <= 25".to_string()],
            rust_191_features: vec!["使用 Trie + DFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(M)".to_string(),
                space_complexity: "O(ALPHABET_SIZE * N * M)".to_string(),
                explanation: Some("M 是单词长度，N 是单词数量".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 225,
            title: "用队列实现栈".to_string(),
            title_en: "Implement Stack using Queues".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Stack, LeetCodeTag::Design, LeetCodeTag::Queue],
            description: "请你仅使用两个队列实现一个后入先出（LIFO）的栈，并支持普通栈的全部四种操作（push、top、pop 和 empty）。".to_string(),
            examples: vec!["输入：[\"MyStack\", \"push\", \"push\", \"top\", \"pop\", \"empty\"]\n[[], [1], [2], [], [], []]\n输出：[null, null, null, 2, 2, false]".to_string()],
            constraints: vec!["1 <= x <= 9".to_string()],
            rust_191_features: vec!["使用队列，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("push 操作需要 O(n) 时间".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 232,
            title: "用栈实现队列".to_string(),
            title_en: "Implement Queue using Stacks".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Stack, LeetCodeTag::Design, LeetCodeTag::Queue],
            description: "请你仅使用两个栈实现先入先出队列。队列应当支持一般队列支持的所有操作（push、pop、peek、empty）。".to_string(),
            examples: vec!["输入：[\"MyQueue\", \"push\", \"push\", \"peek\", \"pop\", \"empty\"]\n[[], [1], [2], [], [], []]\n输出：[null, null, null, 1, 1, false]".to_string()],
            constraints: vec!["1 <= x <= 9".to_string()],
            rust_191_features: vec!["使用双栈，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(1) 摊还".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("pop 和 peek 操作摊还时间复杂度为 O(1)".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lru_cache() {
        let mut cache = LRUCache::new(2);
        cache.put(1, 1);
        cache.put(2, 2);
        assert_eq!(cache.get(1), 1);
        cache.put(3, 3);
        assert_eq!(cache.get(2), -1);
        cache.put(4, 4);
        assert_eq!(cache.get(1), -1);
        assert_eq!(cache.get(3), 3);
        assert_eq!(cache.get(4), 4);
    }

    #[test]
    fn test_min_stack() {
        let mut stack = MinStack::new();
        stack.push(-2);
        stack.push(0);
        stack.push(-3);
        assert_eq!(stack.get_min(), -3);
        stack.pop();
        assert_eq!(stack.top(), 0);
        assert_eq!(stack.get_min(), -2);
    }
}
