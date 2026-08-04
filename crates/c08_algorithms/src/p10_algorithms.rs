//! P10-3 算法实现：segment tree、Trie、union-find、graph algorithms、lock-free stack.
//!
//! 这些实现用于支撑 `concept/05_comparative/05_idioms_patterns_architecture/02_algorithms/`
//! 的权威页代码示例；保持 std-only 或可开启 `crossbeam-epoch` 依赖。

use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::sync::atomic::Ordering as AtomicOrdering;

// ---------------------------------------------------------------------------
// 1. Segment Tree（区间求和，点更新）
// ---------------------------------------------------------------------------

/// 支持单点更新与区间求和的线段树。
///
/// 时间复杂度：
/// - 建树 O(n)
/// - 单点更新 O(log n)
/// - 区间查询 O(log n)
#[derive(Debug, Clone)]
pub struct SegmentTree {
    n: usize,
    tree: Vec<i64>,
}

impl SegmentTree {
    /// 从切片构建线段树。
    pub fn from_slice(data: &[i64]) -> Self {
        let n = data.len();
        let mut tree = vec![0; 4 * n.max(1)];
        if n > 0 {
            Self::build(1, 0, n - 1, data, &mut tree);
        }
        Self { n, tree }
    }

    fn build(node: usize, l: usize, r: usize, data: &[i64], tree: &mut [i64]) {
        if l == r {
            tree[node] = data[l];
            return;
        }
        let mid = (l + r) / 2;
        Self::build(node * 2, l, mid, data, tree);
        Self::build(node * 2 + 1, mid + 1, r, data, tree);
        tree[node] = tree[node * 2] + tree[node * 2 + 1];
    }

    /// 将 `idx` 位置的值更新为 `value`。
    pub fn update(&mut self, idx: usize, value: i64) {
        assert!(idx < self.n, "index out of bounds");
        Self::do_update(1, 0, self.n - 1, idx, value, &mut self.tree);
    }

    fn do_update(node: usize, l: usize, r: usize, idx: usize, value: i64, tree: &mut [i64]) {
        if l == r {
            tree[node] = value;
            return;
        }
        let mid = (l + r) / 2;
        if idx <= mid {
            Self::do_update(node * 2, l, mid, idx, value, tree);
        } else {
            Self::do_update(node * 2 + 1, mid + 1, r, idx, value, tree);
        }
        tree[node] = tree[node * 2] + tree[node * 2 + 1];
    }

    /// 查询闭区间 `[l, r]` 的和。
    pub fn query(&self, l: usize, r: usize) -> i64 {
        assert!(l <= r && r < self.n, "invalid range");
        Self::do_query(1, 0, self.n - 1, l, r, &self.tree)
    }

    fn do_query(node: usize, nl: usize, nr: usize, l: usize, r: usize, tree: &[i64]) -> i64 {
        if l <= nl && nr <= r {
            return tree[node];
        }
        let mid = (nl + nr) / 2;
        let mut ans = 0;
        if l <= mid {
            ans += Self::do_query(node * 2, nl, mid, l, r, tree);
        }
        if r > mid {
            ans += Self::do_query(node * 2 + 1, mid + 1, nr, l, r, tree);
        }
        ans
    }
}

// ---------------------------------------------------------------------------
// 2. Trie（前缀树，小写英文字母）
// ---------------------------------------------------------------------------

/// 仅支持 `a-z` 小写字母的前缀树。
#[derive(Debug, Default)]
pub struct Trie {
    children: [Option<Box<Trie>>; 26],
    is_end: bool,
    count: usize,
}

impl Trie {
    pub fn new() -> Self {
        Self {
            children: Default::default(),
            is_end: false,
            count: 0,
        }
    }

    /// 插入一个单词。
    pub fn insert(&mut self, word: &str) {
        let mut node = self;
        for ch in word.chars() {
            let idx = (ch as u8 - b'a') as usize;
            if node.children[idx].is_none() {
                node.children[idx] = Some(Box::new(Trie::new()));
            }
            node = node.children[idx].as_mut().unwrap();
            node.count += 1;
        }
        node.is_end = true;
    }

    /// 查询单词是否存在。
    pub fn search(&self, word: &str) -> bool {
        self.find(word).map_or(false, |n| n.is_end)
    }

    /// 查询是否有以 `prefix` 开头的单词。
    pub fn starts_with(&self, prefix: &str) -> bool {
        self.find(prefix).is_some()
    }

    fn find(&self, word: &str) -> Option<&Trie> {
        let mut node = self;
        for ch in word.chars() {
            let idx = (ch as u8 - b'a') as usize;
            match &node.children[idx] {
                Some(next) => node = next,
                None => return None,
            }
        }
        Some(node)
    }
}

// ---------------------------------------------------------------------------
// 3. Union-Find（并查集，按秩合并 + 路径压缩）
// ---------------------------------------------------------------------------

/// 并查集，支持合并与查询。
#[derive(Debug, Clone)]
pub struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl UnionFind {
    /// 创建包含 `n` 个独立集合的并查集。
    pub fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    /// 查找 `x` 所在集合的代表元。
    pub fn find(&mut self, x: usize) -> usize {
        assert!(x < self.parent.len(), "index out of bounds");
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }

    /// 合并 `x` 与 `y` 所在集合，返回是否成功合并。
    pub fn union(&mut self, x: usize, y: usize) -> bool {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx == ry {
            return false;
        }
        match self.rank[rx].cmp(&self.rank[ry]) {
            Ordering::Less => self.parent[rx] = ry,
            Ordering::Greater => self.parent[ry] = rx,
            Ordering::Equal => {
                self.parent[ry] = rx;
                self.rank[rx] += 1;
            }
        }
        true
    }

    /// 判断 `x` 与 `y` 是否属于同一集合。
    pub fn connected(&mut self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }
}

// ---------------------------------------------------------------------------
// 4. Graph Algorithms（BFS / DFS / Dijkstra）
// ---------------------------------------------------------------------------

/// 使用邻接表表示的有权图（无向/有向均可）。
#[derive(Debug, Default, Clone)]
pub struct Graph {
    adj: HashMap<usize, Vec<(usize, u64)>>,
}

impl Graph {
    pub fn new() -> Self {
        Self {
            adj: HashMap::new(),
        }
    }

    pub fn add_edge(&mut self, u: usize, v: usize, w: u64) {
        self.adj.entry(u).or_default().push((v, w));
    }

    /// 从 `start` 出发的 BFS，返回访问顺序。
    pub fn bfs(&self, start: usize) -> Vec<usize> {
        let mut visited = HashMap::new();
        let mut queue = VecDeque::new();
        let mut order = Vec::new();
        visited.insert(start, true);
        queue.push_back(start);
        while let Some(u) = queue.pop_front() {
            order.push(u);
            if let Some(neighbors) = self.adj.get(&u) {
                for &(v, _w) in neighbors {
                    if visited.insert(v, true).is_none() {
                        queue.push_back(v);
                    }
                }
            }
        }
        order
    }

    /// 从 `start` 出发的 DFS，返回访问顺序。
    pub fn dfs(&self, start: usize) -> Vec<usize> {
        let mut visited = HashMap::new();
        let mut order = Vec::new();
        Self::do_dfs(self, start, &mut visited, &mut order);
        order
    }

    fn do_dfs(&self, u: usize, visited: &mut HashMap<usize, bool>, order: &mut Vec<usize>) {
        visited.insert(u, true);
        order.push(u);
        if let Some(neighbors) = self.adj.get(&u) {
            for &(v, _w) in neighbors {
                if !visited.contains_key(&v) {
                    Self::do_dfs(self, v, visited, order);
                }
            }
        }
    }

    /// Dijkstra 单源最短路，返回 `start` 到各节点的最短距离。
    pub fn dijkstra(&self, start: usize) -> BTreeMap<usize, u64> {
        let mut dist: BTreeMap<usize, u64> = BTreeMap::new();
        let mut heap = std::collections::BinaryHeap::new();
        dist.insert(start, 0);
        heap.push(std::cmp::Reverse((0u64, start)));
        while let Some(std::cmp::Reverse((d, u))) = heap.pop() {
            if d > *dist.get(&u).unwrap_or(&u64::MAX) {
                continue;
            }
            if let Some(neighbors) = self.adj.get(&u) {
                for &(v, w) in neighbors {
                    let nd = d + w;
                    if nd < *dist.get(&v).unwrap_or(&u64::MAX) {
                        dist.insert(v, nd);
                        heap.push(std::cmp::Reverse((nd, v)));
                    }
                }
            }
        }
        dist
    }
}

// ---------------------------------------------------------------------------
// 5. Lock-free Stack（Treiber Stack，基于 crossbeam-epoch）
// ---------------------------------------------------------------------------

use crossbeam_epoch::{Atomic, Owned};

/// 无锁 Treiber 栈。
///
/// 仅当启用 `crossbeam-epoch` 依赖时可用（本 crate 已声明依赖）。
pub struct LockFreeStack<T> {
    head: Atomic<Node<T>>,
}

struct Node<T> {
    data: T,
    next: Atomic<Node<T>>,
}

impl<T> LockFreeStack<T> {
    pub fn new() -> Self {
        Self {
            head: Atomic::null(),
        }
    }

    /// 压栈。
    pub fn push(&self, value: T) {
        let guard = &crossbeam_epoch::pin();
        let new = Owned::new(Node {
            data: value,
            next: Atomic::null(),
        });
        let new = new.into_shared(guard);
        loop {
            let head = self.head.load(AtomicOrdering::Relaxed, guard);
            unsafe { new.deref().next.store(head, AtomicOrdering::Relaxed) };
            if self
                .head
                .compare_exchange(head, new, AtomicOrdering::Release, AtomicOrdering::Relaxed, guard)
                .is_ok()
            {
                break;
            }
        }
    }

    /// 弹栈。
    pub fn pop(&self) -> Option<T> {
        let guard = &crossbeam_epoch::pin();
        loop {
            let head = self.head.load(AtomicOrdering::Acquire, guard);
            match unsafe { head.as_ref() } {
                Some(h) => {
                    let next = h.next.load(AtomicOrdering::Relaxed, guard);
                    if self
                        .head
                        .compare_exchange(head, next, AtomicOrdering::Relaxed, AtomicOrdering::Relaxed, guard)
                        .is_ok()
                    {
                        unsafe {
                            guard.defer_destroy(head);
                            return Some(std::ptr::read(&h.data));
                        }
                    }
                }
                None => return None,
            }
        }
    }
}

impl<T> Default for LockFreeStack<T> {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl<T: Send> Send for LockFreeStack<T> {}
unsafe impl<T: Send + Sync> Sync for LockFreeStack<T> {}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn segment_tree_basic() {
        let mut st = SegmentTree::from_slice(&[1, 2, 3, 4, 5]);
        assert_eq!(st.query(0, 4), 15);
        st.update(2, 10);
        assert_eq!(st.query(0, 4), 22);
        assert_eq!(st.query(1, 3), 16);
    }

    #[test]
    fn trie_basic() {
        let mut trie = Trie::new();
        trie.insert("rust");
        trie.insert("rule");
        assert!(trie.search("rust"));
        assert!(!trie.search("ru"));
        assert!(trie.starts_with("ru"));
        assert!(!trie.starts_with("java"));
    }

    #[test]
    fn union_find_basic() {
        let mut uf = UnionFind::new(5);
        uf.union(0, 1);
        uf.union(1, 2);
        assert!(uf.connected(0, 2));
        assert!(!uf.connected(0, 3));
    }

    #[test]
    fn graph_algorithms() {
        let mut g = Graph::new();
        g.add_edge(0, 1, 4);
        g.add_edge(0, 2, 1);
        g.add_edge(2, 1, 2);
        g.add_edge(1, 3, 1);
        g.add_edge(2, 3, 5);
        let bfs = g.bfs(0);
        assert_eq!(bfs[0], 0);
        let dist = g.dijkstra(0);
        assert_eq!(dist.get(&3), Some(&3));
    }

    #[test]
    fn lock_free_stack_basic() {
        let stack = LockFreeStack::new();
        stack.push(1);
        stack.push(2);
        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.pop(), None);
    }
}
