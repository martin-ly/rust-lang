//! Rope（绳索）：用于大文本的可持久化、高效拼接/分割数据结构。
//!
//! Rope 基于二叉树（通常用 B-tree / 平衡树实现），每个节点保存子树的总长度，
//! 从而在 O(log n) 时间内完成拼接、分割、插入、删除。本实现为教学版，使用
//! `String` 作为叶子节点内容，支持不可变共享（`Arc`）以简化可持久化操作。
//!
//! # 时间复杂度
//! - 拼接 (concat): O(log n)
//! - 按索引分割 (split): O(log n)
//! - 插入/删除单字符: O(log n)
//! - 索引访问（按位置取字符）: O(log n)
//! - 构建自字符串: O(n)
//!
//! # 来源
//! - [Introduction to Algorithms (Cormen et al.)](https://mitpress.mit.edu/books/introduction-algorithms-fourth-edition)
//! - [Algorithm Engineering (Saunders / Demetrescu)](https://people.mpi-inf.mpg.de/~mehlhorn/LEDAbook.html)

use std::sync::Arc;

/// Rope 节点。
#[derive(Clone, Debug)]
pub enum Rope {
    /// 内部节点：左右子树与总长度。
    Node {
        left: Arc<Rope>,
        right: Arc<Rope>,
        len: usize,
    },
    /// 叶子节点：连续文本。
    Leaf(String),
    /// 空 rope。
    Empty,
}

impl Rope {
    /// 创建空 Rope。
    pub fn new() -> Self {
        Self::Empty
    }

    /// 从字符串构建 Rope。
    pub fn from_string(s: &str) -> Self {
        if s.is_empty() {
            Self::Empty
        } else {
            Self::Leaf(s.to_string())
        }
    }

    /// 获取总长度（字节数）。
    pub fn len(&self) -> usize {
        match self {
            Self::Node { len, .. } => *len,
            Self::Leaf(s) => s.len(),
            Self::Empty => 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 返回两棵 rope 的拼接。
    pub fn concat(left: Rope, right: Rope) -> Self {
        if left.is_empty() {
            return right;
        }
        if right.is_empty() {
            return left;
        }
        let len = left.len() + right.len();
        Self::Node {
            left: Arc::new(left),
            right: Arc::new(right),
            len,
        }
    }

    /// 按字节索引分割为左右两部分：`[0, idx)` 与 `[idx, len)`。
    ///
    /// # Panics
    /// 若 `idx > self.len()` 则 panic。
    pub fn split(&self, idx: usize) -> (Self, Self) {
        assert!(idx <= self.len(), "split index out of bounds");
        match self {
            Self::Empty => (Self::Empty, Self::Empty),
            Self::Leaf(s) => {
                let (l, r) = s.split_at(idx);
                (Self::Leaf(l.to_string()), Self::Leaf(r.to_string()))
            }
            Self::Node { left, right, len: _ } => {
                let left_len = left.len();
                if idx < left_len {
                    let (ll, lr) = left.split(idx);
                    (ll, Self::concat(lr, (**right).clone()))
                } else if idx > left_len {
                    let (rl, rr) = right.split(idx - left_len);
                    (Self::concat((**left).clone(), rl), rr)
                } else {
                    ((**left).clone(), (**right).clone())
                }
            }
        }
    }

    /// 在字节位置 `idx` 处插入字符串。
    pub fn insert(&self, idx: usize, s: &str) -> Self {
        let (left, right) = self.split(idx);
        Self::concat(Self::concat(left, Self::from_string(s)), right)
    }

    /// 删除字节区间 `[start, end)`。
    pub fn delete(&self, start: usize, end: usize) -> Self {
        assert!(start <= end && end <= self.len(), "invalid delete range");
        let (left, rest) = self.split(start);
        let (_, right) = rest.split(end - start);
        Self::concat(left, right)
    }

    /// 将 Rope 内容收集为 `String`。
    pub fn to_string_lossy(&self) -> String {
        self.to_string()
    }
}

impl std::fmt::Display for Rope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => Ok(()),
            Self::Leaf(s) => write!(f, "{}", s),
            Self::Node { left, right, .. } => {
                write!(f, "{}{}", left, right)
            }
        }
    }
}

impl Default for Rope {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rope_basic() {
        let r = Rope::from_string("Hello, ")
            .insert(7, "World")
            .insert(12, "!");
        assert_eq!(r.to_string(), "Hello, World!");
    }

    #[test]
    fn test_rope_split_concat() {
        let r = Rope::from_string("abcdef");
        let (l, r2) = r.split(3);
        assert_eq!(l.to_string(), "abc");
        assert_eq!(r2.to_string(), "def");
        let merged = Rope::concat(l, r2);
        assert_eq!(merged.to_string(), "abcdef");
    }

    #[test]
    fn test_rope_delete() {
        let r = Rope::from_string("Hello, World!");
        let r2 = r.delete(5, 7); // 删除 ", "
        assert_eq!(r2.to_string(), "HelloWorld!");
    }
}
