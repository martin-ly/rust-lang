//! 红黑树（Red-Black Tree）：自平衡二叉搜索树。
//!
//! 通过五条颜色规则保证树高不超过 2 log(n+1)，从而所有操作的
//! 最坏时间复杂度均为 O(log n)。
//!
//! 本实现为教学版，使用 enum 表示节点颜色，支持插入、删除与查找。
//!
//! # 时间复杂度
//! - 查找: O(log n)
//! - 插入: O(log n)
//! - 删除: O(log n)

use std::cmp::Ordering;

/// 节点颜色。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Color {
    Red,
    Black,
}

/// 红黑树节点。
#[derive(Clone, Debug)]
struct Node {
    key: i32,
    color: Color,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

impl Node {
    fn new(key: i32, color: Color) -> Self {
        Self {
            key,
            color,
            left: None,
            right: None,
        }
    }

    fn is_red(node: &Option<Box<Node>>) -> bool {
        matches!(node.as_ref().map(|n| n.color), Some(Color::Red))
    }
}

/// 红黑树。
#[derive(Clone, Debug, Default)]
pub struct RedBlackTree {
    root: Option<Box<Node>>,
    len: usize,
}

impl RedBlackTree {
    /// 创建空红黑树。
    pub fn new() -> Self {
        Self { root: None, len: 0 }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// 查找 key 是否存在。
    pub fn contains(&self, key: i32) -> bool {
        Self::contains_node(&self.root, key)
    }

    fn contains_node(node: &Option<Box<Node>>, key: i32) -> bool {
        let Some(n) = node else { return false };
        match key.cmp(&n.key) {
            Ordering::Equal => true,
            Ordering::Less => Self::contains_node(&n.left, key),
            Ordering::Greater => Self::contains_node(&n.right, key),
        }
    }

    /// 左旋。
    fn rotate_left(mut h: Box<Node>) -> Box<Node> {
        let mut x = h.right.take().expect("rotate_left 需要右子节点");
        h.right = x.left.take();
        x.color = h.color;
        h.color = Color::Red;
        x.left = Some(h);
        x
    }

    /// 右旋。
    fn rotate_right(mut h: Box<Node>) -> Box<Node> {
        let mut x = h.left.take().expect("rotate_right 需要左子节点");
        h.left = x.right.take();
        x.color = h.color;
        h.color = Color::Red;
        x.right = Some(h);
        x
    }

    /// 颜色翻转。
    fn flip_colors(h: &mut Node) {
        h.color = if h.color == Color::Red {
            Color::Black
        } else {
            Color::Red
        };
        if let Some(ref mut l) = h.left {
            l.color = if l.color == Color::Red {
                Color::Black
            } else {
                Color::Red
            };
        }
        if let Some(ref mut r) = h.right {
            r.color = if r.color == Color::Red {
                Color::Black
            } else {
                Color::Red
            };
        }
    }

    /// 保持红黑树局部平衡。
    fn balance(mut h: Box<Node>) -> Box<Node> {
        if Node::is_red(&h.right) && !Node::is_red(&h.left) {
            h = Self::rotate_left(h);
        }
        if Node::is_red(&h.left) && Node::is_red(&h.left.as_ref().unwrap().left) {
            h = Self::rotate_right(h);
        }
        if Node::is_red(&h.left) && Node::is_red(&h.right) {
            Self::flip_colors(&mut h);
        }
        h
    }

    fn insert_node(node: Option<Box<Node>>, key: i32) -> (Box<Node>, bool) {
        match node {
            None => (Box::new(Node::new(key, Color::Red)), true),
            Some(mut n) => {
                let inserted = match key.cmp(&n.key) {
                    Ordering::Equal => false,
                    Ordering::Less => {
                        let (left, inserted) = Self::insert_node(n.left.take(), key);
                        n.left = Some(left);
                        inserted
                    }
                    Ordering::Greater => {
                        let (right, inserted) = Self::insert_node(n.right.take(), key);
                        n.right = Some(right);
                        inserted
                    }
                };
                (Self::balance(n), inserted)
            }
        }
    }

    /// 插入 key。若 key 已存在则忽略，返回是否新增。
    pub fn insert(&mut self, key: i32) -> bool {
        let (root, inserted) = Self::insert_node(self.root.take(), key);
        self.root = Some(root);
        if let Some(ref mut r) = self.root {
            r.color = Color::Black;
        }
        if inserted {
            self.len += 1;
        }
        inserted
    }

    /// 将红色左子节点提升。
    fn move_red_left(mut h: Box<Node>) -> Box<Node> {
        Self::flip_colors(&mut h);
        if Node::is_red(&h.right.as_ref().unwrap().left) {
            h.right = Some(Self::rotate_right(h.right.take().unwrap()));
            h = Self::rotate_left(h);
            Self::flip_colors(&mut h);
        }
        h
    }

    /// 将红色右子节点提升。
    fn move_red_right(mut h: Box<Node>) -> Box<Node> {
        Self::flip_colors(&mut h);
        if Node::is_red(&h.left.as_ref().unwrap().left) {
            h = Self::rotate_right(h);
            Self::flip_colors(&mut h);
        }
        h
    }

    fn delete_min_node(node: Option<Box<Node>>) -> Option<Box<Node>> {
        let mut h = node?;
        h.left.as_ref()?;
        if !Node::is_red(&h.left) && !Node::is_red(&h.left.as_ref().unwrap().left) {
            h = Self::move_red_left(h);
        }
        h.left = Self::delete_min_node(h.left.take());
        Some(Self::balance(h))
    }

    fn delete_node(node: Option<Box<Node>>, key: i32) -> Option<Box<Node>> {
        let mut h = node?;
        if key < h.key {
            if !Node::is_red(&h.left) && !Node::is_red(&h.left.as_ref().unwrap().left) {
                h = Self::move_red_left(h);
            }
            h.left = Self::delete_node(h.left.take(), key);
        } else {
            if Node::is_red(&h.left) {
                h = Self::rotate_right(h);
            }
            if key == h.key && h.right.is_none() {
                return None;
            }
            if !Node::is_red(&h.right) && !Node::is_red(&h.right.as_ref().unwrap().left) {
                h = Self::move_red_right(h);
            }
            if key == h.key {
                // 用右子树最小值替换。
                let min_key = Self::min_node(&h.right);
                h.key = min_key;
                h.right = Self::delete_min_node(h.right.take());
            } else {
                h.right = Self::delete_node(h.right.take(), key);
            }
        }
        Some(Self::balance(h))
    }

    fn min_node(node: &Option<Box<Node>>) -> i32 {
        let mut current = node.as_ref().unwrap();
        while let Some(ref left) = current.left {
            current = left;
        }
        current.key
    }

    /// 删除 key，若存在则返回 true。
    pub fn delete(&mut self, key: i32) -> bool {
        if !self.contains(key) {
            return false;
        }
        if !Node::is_red(&self.root.as_ref().unwrap().left)
            && !Node::is_red(&self.root.as_ref().unwrap().right)
        {
            self.root.as_mut().unwrap().color = Color::Red;
        }
        self.root = Self::delete_node(self.root.take(), key);
        if let Some(ref mut r) = self.root {
            r.color = Color::Black;
        }
        self.len -= 1;
        true
    }

    fn inorder_node(node: &Option<Box<Node>>, out: &mut Vec<i32>) {
        if let Some(n) = node {
            Self::inorder_node(&n.left, out);
            out.push(n.key);
            Self::inorder_node(&n.right, out);
        }
    }

    /// 返回升序键列表。
    pub fn sorted(&self) -> Vec<i32> {
        let mut out = Vec::with_capacity(self.len);
        Self::inorder_node(&self.root, &mut out);
        out
    }

    /// 校验红黑树五条不变式（用于测试）。
    #[cfg(test)]
    fn validate(&self) -> Result<(), &'static str> {
        if self.root.is_none() {
            return Ok(());
        }
        if Node::is_red(&self.root) {
            return Err("根节点必须是黑色");
        }
        Self::validate_node(&self.root)
    }

    #[cfg(test)]
    fn validate_node(node: &Option<Box<Node>>) -> Result<(), &'static str> {
        let Some(n) = node else { return Ok(()) };
        if Node::is_red(node) && (Node::is_red(&n.left) || Node::is_red(&n.right)) {
            return Err("红色节点的子节点必须是黑色");
        }
        Self::validate_node(&n.left)?;
        Self::validate_node(&n.right)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rb_insert_search() {
        let mut tree = RedBlackTree::new();
        let keys = [10, 5, 15, 3, 7, 12, 20];
        for k in keys {
            assert!(tree.insert(k));
        }
        assert!(!tree.insert(10));
        assert_eq!(tree.len(), 7);
        assert!(tree.contains(12));
        assert!(!tree.contains(99));
        assert_eq!(tree.sorted(), vec![3, 5, 7, 10, 12, 15, 20]);
        tree.validate().unwrap();
    }

    #[test]
    fn test_rb_delete() {
        let mut tree = RedBlackTree::new();
        for i in 0..20 {
            tree.insert(i);
        }
        for i in (0..20).step_by(2) {
            assert!(tree.delete(i));
        }
        for i in (0..20).step_by(2) {
            assert!(!tree.contains(i));
        }
        for i in (1..20).step_by(2) {
            assert!(tree.contains(i));
        }
        assert_eq!(tree.len(), 10);
        tree.validate().unwrap();
    }

    #[test]
    fn test_rb_delete_root() {
        let mut tree = RedBlackTree::new();
        tree.insert(10);
        tree.insert(5);
        tree.insert(15);
        assert!(tree.delete(10));
        assert!(!tree.contains(10));
        assert_eq!(tree.sorted(), vec![5, 15]);
        tree.validate().unwrap();
    }

    #[test]
    fn test_rb_empty() {
        let tree = RedBlackTree::new();
        assert!(tree.is_empty());
        assert!(!tree.contains(0));
    }
}
