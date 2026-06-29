//! Treap（树堆）：结合二叉搜索树与堆的随机化平衡树。
//!
//! 每个节点保存键 key 与随机优先级 priority，按 key 满足 BST 性质，按 priority
//! 满足堆性质（此处用大根堆）。通过优先级隐式实现期望 O(log n) 的平衡。
//!
//! 本实现额外维护子树大小 `size`，从而支持第 k 小/大的顺序统计。
//!
//! # 时间复杂度（期望）
//! - 插入: O(log n)
//! - 删除: O(log n)
//! - 查找: O(log n)
//! - 第 k 小: O(log n)

use std::cmp::Ordering;

/// Treap 节点。
#[derive(Clone, Debug)]
struct Node {
    key: i32,
    priority: u64,
    size: usize,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

impl Node {
    fn new(key: i32, priority: u64) -> Self {
        Self {
            key,
            priority,
            size: 1,
            left: None,
            right: None,
        }
    }

    fn size(node: &Option<Box<Node>>) -> usize {
        node.as_ref().map_or(0, |n| n.size)
    }

    fn update_size(&mut self) {
        self.size = 1 + Self::size(&self.left) + Self::size(&self.right);
    }
}

/// 隐式 Treap（基于键 key 的显式 BST）。
#[derive(Clone, Debug, Default)]
pub struct Treap {
    root: Option<Box<Node>>,
}

impl Treap {
    /// 创建空 Treap。
    pub fn new() -> Self {
        Self { root: None }
    }

    /// 返回节点数量。
    pub fn len(&self) -> usize {
        Node::size(&self.root)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 右旋：将左子节点提升为根。
    fn rotate_right(mut y: Box<Node>) -> Box<Node> {
        let mut x = y.left.take().expect("rotate_right 需要左子节点");
        y.left = x.right.take();
        y.update_size();
        x.right = Some(y);
        x.update_size();
        x
    }

    /// 左旋：将右子节点提升为根。
    fn rotate_left(mut x: Box<Node>) -> Box<Node> {
        let mut y = x.right.take().expect("rotate_left 需要右子节点");
        x.right = y.left.take();
        x.update_size();
        y.left = Some(x);
        y.update_size();
        y
    }

    fn insert_node(node: Option<Box<Node>>, key: i32, priority: u64) -> Box<Node> {
        match node {
            None => Box::new(Node::new(key, priority)),
            Some(mut n) => match key.cmp(&n.key) {
                Ordering::Equal => {
                    // 重复键：直接忽略，保持集合语义。
                    n.update_size();
                    n
                }
                Ordering::Less => {
                    n.left = Some(Self::insert_node(n.left.take(), key, priority));
                    if n.left.as_ref().unwrap().priority > n.priority {
                        n = Self::rotate_right(n);
                    } else {
                        n.update_size();
                    }
                    n
                }
                Ordering::Greater => {
                    n.right = Some(Self::insert_node(n.right.take(), key, priority));
                    if n.right.as_ref().unwrap().priority > n.priority {
                        n = Self::rotate_left(n);
                    } else {
                        n.update_size();
                    }
                    n
                }
            },
        }
    }

    /// 插入键 key。若 key 已存在则忽略。
    pub fn insert(&mut self, key: i32, priority: u64) {
        self.root = Some(Self::insert_node(self.root.take(), key, priority));
    }

    fn delete_node(node: Option<Box<Node>>, key: i32) -> Option<Box<Node>> {
        let mut n = node?;
        match key.cmp(&n.key) {
            Ordering::Equal => {
                // 将当前节点旋转到叶子后删除。
                let left_priority = n.left.as_ref().map(|l| l.priority);
                let right_priority = n.right.as_ref().map(|r| r.priority);
                if let (Some(lp), Some(rp)) = (left_priority, right_priority) {
                    if lp > rp {
                        let mut rotated = Self::rotate_right(n);
                        rotated.right = Self::delete_node(rotated.right.take(), key);
                        rotated.update_size();
                        Some(rotated)
                    } else {
                        let mut rotated = Self::rotate_left(n);
                        rotated.left = Self::delete_node(rotated.left.take(), key);
                        rotated.update_size();
                        Some(rotated)
                    }
                } else {
                    n.left.take().or_else(|| n.right.take())
                }
            }
            Ordering::Less => {
                n.left = Self::delete_node(n.left.take(), key);
                n.update_size();
                Some(n)
            }
            Ordering::Greater => {
                n.right = Self::delete_node(n.right.take(), key);
                n.update_size();
                Some(n)
            }
        }
    }

    /// 删除键 key，若存在则返回 true。
    pub fn delete(&mut self, key: i32) -> bool {
        if !self.contains(key) {
            return false;
        }
        self.root = Self::delete_node(self.root.take(), key);
        true
    }

    fn contains_node(node: &Option<Box<Node>>, key: i32) -> bool {
        let Some(n) = node else { return false };
        match key.cmp(&n.key) {
            Ordering::Equal => true,
            Ordering::Less => Self::contains_node(&n.left, key),
            Ordering::Greater => Self::contains_node(&n.right, key),
        }
    }

    /// 判断 key 是否存在。
    pub fn contains(&self, key: i32) -> bool {
        Self::contains_node(&self.root, key)
    }

    /// 查找 key，存在时返回 Some(key)，否则返回 None。
    ///
    /// 对仅保存键的集合，查找结果等价于 `contains` 的 richer 返回值。
    pub fn find(&self, key: i32) -> Option<i32> {
        if self.contains(key) { Some(key) } else { None }
    }

    fn kth_node(node: &Option<Box<Node>>, mut k: usize) -> Option<i32> {
        // k 为 0-based，升序第 k 个。
        let n = node.as_ref()?;
        let left_size = Node::size(&n.left);
        match k.cmp(&left_size) {
            Ordering::Equal => Some(n.key),
            Ordering::Less => Self::kth_node(&n.left, k),
            Ordering::Greater => {
                k -= left_size + 1;
                Self::kth_node(&n.right, k)
            }
        }
    }

    /// 返回升序第 k（0-based）个键。
    ///
    /// # Panics
    /// 当 k >= len() 时返回 None。
    pub fn kth(&self, k: usize) -> Option<i32> {
        Self::kth_node(&self.root, k)
    }

    /// 返回小于 key 的键的数量（即 key 的排名，0-based）。
    pub fn rank(&self, key: i32) -> usize {
        Self::rank_node(&self.root, key)
    }

    fn rank_node(node: &Option<Box<Node>>, key: i32) -> usize {
        let Some(n) = node else { return 0 };
        match key.cmp(&n.key) {
            Ordering::Less => Self::rank_node(&n.left, key),
            Ordering::Equal => Node::size(&n.left),
            Ordering::Greater => Node::size(&n.left) + 1 + Self::rank_node(&n.right, key),
        }
    }

    fn inorder_node(node: &Option<Box<Node>>, out: &mut Vec<i32>) {
        if let Some(n) = node {
            Self::inorder_node(&n.left, out);
            out.push(n.key);
            Self::inorder_node(&n.right, out);
        }
    }

    /// 中序遍历输出有序键列表。
    pub fn sorted(&self) -> Vec<i32> {
        let mut out = Vec::with_capacity(self.len());
        Self::inorder_node(&self.root, &mut out);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_treap_insert_search() {
        let mut treap = Treap::new();
        for (i, key) in [5, 3, 7, 1, 9, 4].iter().enumerate() {
            treap.insert(*key, i as u64 + 1);
        }
        assert_eq!(treap.len(), 6);
        assert!(treap.contains(5));
        assert!(treap.contains(1));
        assert!(!treap.contains(100));
        assert_eq!(treap.sorted(), vec![1, 3, 4, 5, 7, 9]);
    }

    #[test]
    fn test_treap_delete() {
        let mut treap = Treap::new();
        for i in 0..10 {
            treap.insert(i, i as u64 + 1);
        }
        assert!(treap.delete(5));
        assert!(!treap.delete(5));
        assert!(!treap.contains(5));
        assert_eq!(treap.len(), 9);
        let expected: Vec<i32> = (0..10).filter(|x| *x != 5).collect();
        assert_eq!(treap.sorted(), expected);
    }

    #[test]
    fn test_treap_kth_and_rank() {
        let mut treap = Treap::new();
        let keys = [10, 5, 15, 3, 7, 12, 20];
        for (i, key) in keys.iter().enumerate() {
            treap.insert(*key, (i + 1) as u64);
        }
        assert_eq!(treap.kth(0), Some(3));
        assert_eq!(treap.kth(3), Some(10));
        assert_eq!(treap.kth(6), Some(20));
        assert_eq!(treap.kth(7), None);

        assert_eq!(treap.rank(3), 0);
        assert_eq!(treap.rank(10), 3);
        assert_eq!(treap.rank(100), 7);
    }

    #[test]
    fn test_treap_duplicate_ignored() {
        let mut treap = Treap::new();
        treap.insert(42, 1);
        treap.insert(42, 2);
        assert_eq!(treap.len(), 1);
    }

    #[test]
    fn test_treap_find_and_search() {
        let mut treap = Treap::new();
        for (i, key) in [5, 3, 7, 1, 9].iter().enumerate() {
            treap.insert(*key, (i + 1) as u64);
        }
        assert_eq!(treap.find(5), Some(5));
        assert_eq!(treap.find(100), None);
        assert!(treap.contains(1));
        assert!(!treap.contains(2));
    }

    #[test]
    fn test_treap_delete_root_and_leaf() {
        let mut treap = Treap::new();
        for i in 0..5 {
            treap.insert(i, i as u64 + 1);
        }
        assert!(treap.delete(0)); // 叶子
        assert!(treap.delete(2)); // 可能为根或内部节点
        assert!(treap.delete(4));
        assert_eq!(treap.len(), 2);
        assert!(!treap.contains(0));
        assert!(!treap.contains(2));
        assert!(!treap.contains(4));
    }

    #[test]
    fn test_treap_rank_boundary() {
        let mut treap = Treap::new();
        for key in [2, 4, 6] {
            treap.insert(key, key as u64);
        }
        assert_eq!(treap.rank(0), 0);
        assert_eq!(treap.rank(2), 0);
        assert_eq!(treap.rank(3), 1);
        assert_eq!(treap.rank(7), 3);
    }

    #[test]
    fn test_treap_kth_boundary() {
        let treap = Treap::new();
        assert_eq!(treap.kth(0), None);
    }
}
