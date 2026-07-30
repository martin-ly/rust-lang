//! Trie（前缀树 / 字典树）
//!
//! Trie 支持 O(|key|) 的插入、查找与前缀匹配，常用于自动补全、拼写检查、
//! IP 路由表、字符串集合去重等场景。
//!
//! # 时间复杂度
//! - 插入: O(m)，m 为键长度
//! - 查找: O(m)
//! - 前缀匹配: O(m)
//! - 空间: O(字母表大小 × 键总数 × 平均键长)
//!
//! # 来源
//! - [Introduction to Algorithms (Cormen et al.)](https://mitpress.mit.edu/books/introduction-algorithms-fourth-edition)
//! - [Algorithm Engineering](https://people.mpi-inf.mpg.de/~mehlhorn/LEDAbook.html)

use std::collections::HashMap;

/// Trie 节点。
#[derive(Clone, Debug, Default)]
pub struct TrieNode {
    children: HashMap<char, TrieNode>,
    is_end: bool,
}

impl TrieNode {
    pub fn new() -> Self {
        Self::default()
    }
}

/// 前缀树。
#[derive(Clone, Debug, Default)]
pub struct Trie {
    root: TrieNode,
}

impl Trie {
    pub fn new() -> Self {
        Self::default()
    }

    /// 插入一个单词。
    pub fn insert(&mut self, word: &str) {
        let mut node = &mut self.root;
        for ch in word.chars() {
            node = node.children.entry(ch).or_default();
        }
        node.is_end = true;
    }

    /// 查找单词是否存在。
    pub fn search(&self, word: &str) -> bool {
        self.find_node(word).is_some_and(|n| n.is_end)
    }

    /// 是否存在以 `prefix` 开头的单词。
    pub fn starts_with(&self, prefix: &str) -> bool {
        self.find_node(prefix).is_some()
    }

    fn find_node(&self, word: &str) -> Option<&TrieNode> {
        let mut node = &self.root;
        for ch in word.chars() {
            node = node.children.get(&ch)?;
        }
        Some(node)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trie_basic() {
        let mut trie = Trie::new();
        trie.insert("rust");
        trie.insert("rest");
        trie.insert("ruby");

        assert!(trie.search("rust"));
        assert!(!trie.search("ru"));
        assert!(trie.starts_with("ru"));
        assert!(trie.starts_with("rest"));
        assert!(!trie.starts_with("java"));
    }
}
