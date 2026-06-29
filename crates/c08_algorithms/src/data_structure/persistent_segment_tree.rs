//! 可持久化线段树（Persistent Segment Tree）：支持历史版本回溯的线段树。
//!
//! 每次单点更新都会创建一条从根到叶子的新路径，并复用未修改的子树，
//! 因此可以在 O(log n) 时间和空间内生成一个新版本。
//!
//! 本实现使用下标竞技场（arena）存储节点，支持区间和查询与单点修改。
//!
//! # 时间复杂度
//! - 构建: O(n)
//! - 单点更新: O(log n)
//! - 区间查询: O(log n)
//! - 空间: 每个版本 O(log n)（均摊）

const NIL: usize = 0;

/// 节点。
#[derive(Clone, Debug)]
struct Node {
    left: usize,
    right: usize,
    sum: i64,
}

impl Node {
    fn new() -> Self {
        Self {
            left: NIL,
            right: NIL,
            sum: 0,
        }
    }
}

/// 可持久化线段树。
#[derive(Clone, Debug)]
pub struct PersistentSegmentTree {
    nodes: Vec<Node>,
    n: usize,
}

impl PersistentSegmentTree {
    /// 从数组构建可持久化线段树，返回版本 0 的根节点索引。
    pub fn from_slice(arr: &[i64]) -> (Self, usize) {
        let n = arr.len().max(1);
        let mut tree = Self {
            nodes: vec![Node::new()], // 索引 0 为 NIL 节点。
            n,
        };
        let root = tree.build(0, n - 1, arr);
        (tree, root)
    }

    fn new_node(&mut self, sum: i64, left: usize, right: usize) -> usize {
        let idx = self.nodes.len();
        self.nodes.push(Node { left, right, sum });
        idx
    }

    fn build(&mut self, l: usize, r: usize, arr: &[i64]) -> usize {
        if l == r {
            if l < arr.len() {
                return self.new_node(arr[l], NIL, NIL);
            }
            return self.new_node(0, NIL, NIL);
        }
        let mid = l + (r - l) / 2;
        let left = self.build(l, mid, arr);
        let right = self.build(mid + 1, r, arr);
        let sum = self.nodes[left].sum + self.nodes[right].sum;
        self.new_node(sum, left, right)
    }

    /// 在版本 `root` 的基础上将位置 `idx` 更新为 `value`，返回新版本根索引。
    pub fn update(&mut self, root: usize, idx: usize, value: i64) -> usize {
        self.update_node(root, 0, self.n - 1, idx, value)
    }

    fn update_node(&mut self, root: usize, l: usize, r: usize, idx: usize, value: i64) -> usize {
        if l == r {
            return self.new_node(value, NIL, NIL);
        }
        let mid = l + (r - l) / 2;
        let node = self.nodes[root].clone();
        let (new_left, new_right) = if idx <= mid {
            (self.update_node(node.left, l, mid, idx, value), node.right)
        } else {
            (
                node.left,
                self.update_node(node.right, mid + 1, r, idx, value),
            )
        };
        let sum = self.nodes[new_left].sum + self.nodes[new_right].sum;
        self.new_node(sum, new_left, new_right)
    }

    /// 查询版本 `root` 中区间 [ql, qr] 的和（两端包含）。
    pub fn query(&self, root: usize, ql: usize, qr: usize) -> i64 {
        if ql > qr || root == NIL {
            return 0;
        }
        self.query_node(root, 0, self.n - 1, ql, qr)
    }

    fn query_node(&self, root: usize, l: usize, r: usize, ql: usize, qr: usize) -> i64 {
        if root == NIL || ql > r || qr < l {
            return 0;
        }
        if ql <= l && r <= qr {
            return self.nodes[root].sum;
        }
        let mid = l + (r - l) / 2;
        self.query_node(self.nodes[root].left, l, mid, ql, qr)
            + self.query_node(self.nodes[root].right, mid + 1, r, ql, qr)
    }

    /// 返回节点数量（含 NIL）。
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pst_basic() {
        let arr = vec![1, 2, 3, 4, 5];
        let (mut pst, root0) = PersistentSegmentTree::from_slice(&arr);

        assert_eq!(pst.query(root0, 0, 4), 15);
        assert_eq!(pst.query(root0, 1, 3), 9);

        let root1 = pst.update(root0, 2, 10);
        assert_eq!(pst.query(root0, 1, 3), 9); // 原版本不变
        assert_eq!(pst.query(root1, 1, 3), 16);
        assert_eq!(pst.query(root1, 0, 4), 22);
    }

    #[test]
    fn test_pst_multiple_versions() {
        let arr = vec![0; 5];
        let (mut pst, mut root) = PersistentSegmentTree::from_slice(&arr);
        let mut roots = vec![root];

        for i in 0..5 {
            root = pst.update(root, i, (i as i64 + 1) * 10);
            roots.push(root);
        }

        // 版本 0 全为 0。
        assert_eq!(pst.query(roots[0], 0, 4), 0);
        // 版本 3：前 3 个位置被更新。
        assert_eq!(pst.query(roots[3], 0, 4), 10 + 20 + 30);
        // 版本 5：全部更新。
        assert_eq!(pst.query(roots[5], 0, 4), 10 + 20 + 30 + 40 + 50);
    }

    #[test]
    fn test_pst_empty() {
        let (pst, root) = PersistentSegmentTree::from_slice(&[]);
        assert_eq!(pst.query(root, 0, 0), 0);
    }
}
