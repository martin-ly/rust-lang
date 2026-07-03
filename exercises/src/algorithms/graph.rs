//! # 图论练习 / Graph Exercises
//!
//! 本模块包含经典图论算法的实现与练习：
//! - Dijkstra 单源最短路
//! - 拓扑排序（Kahn 算法）
//! - 并查集（Union-Find）
//! - 无向图环检测
//! - Kruskal 最小生成树
//! - 网络延迟时间（Dijkstra 变种）

use std::cmp::Ordering;
use std::collections::{BinaryHeap, VecDeque};

/// 带权边，用于 Dijkstra 等算法。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Edge {
    pub to: usize,
    pub weight: u32,
}

impl Edge {
    pub fn new(to: usize, weight: u32) -> Self {
        Self { to, weight }
    }
}

impl Ord for Edge {
    fn cmp(&self, other: &Self) -> Ordering {
        // 反转以实现最小堆
        other.weight.cmp(&self.weight)
    }
}

impl PartialOrd for Edge {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Dijkstra：返回从 start 到每个节点的最短距离，不可达为 None。
/// graph 是邻接表，weight 为非负整数。
pub fn dijkstra(graph: &[Vec<Edge>], start: usize) -> Vec<Option<u32>> {
    let n = graph.len();
    let mut dist = vec![None; n];
    let mut heap = BinaryHeap::new();
    dist[start] = Some(0);
    heap.push(Edge::new(start, 0));

    while let Some(Edge { to: u, weight: d }) = heap.pop() {
        if Some(d) > dist[u] {
            continue;
        }
        for edge in &graph[u] {
            let next_dist = d + edge.weight;
            if dist[edge.to].is_none_or(|cur| next_dist < cur) {
                dist[edge.to] = Some(next_dist);
                heap.push(Edge::new(edge.to, next_dist));
            }
        }
    }
    dist
}

/// Kahn 算法拓扑排序。若图存在环，返回 None。
pub fn topological_sort(graph: &[Vec<usize>]) -> Option<Vec<usize>> {
    let n = graph.len();
    let mut in_degree = vec![0usize; n];
    for row in graph {
        for &v in row {
            in_degree[v] += 1;
        }
    }

    let mut queue = VecDeque::new();
    for (v, &deg) in in_degree.iter().enumerate() {
        if deg == 0 {
            queue.push_back(v);
        }
    }

    let mut result = Vec::with_capacity(n);
    while let Some(u) = queue.pop_front() {
        result.push(u);
        for &v in &graph[u] {
            in_degree[v] -= 1;
            if in_degree[v] == 0 {
                queue.push_back(v);
            }
        }
    }

    if result.len() == n {
        Some(result)
    } else {
        None
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
            Ordering::Less => self.parent[root_x] = root_y,
            Ordering::Greater => self.parent[root_y] = root_x,
            Ordering::Equal => {
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

/// 无向图环检测：若存在环返回 true。
pub fn has_cycle_undirected(edges: &[(usize, usize)], n: usize) -> bool {
    let mut uf = UnionFind::new(n);
    for &(u, v) in edges {
        if !uf.union(u, v) {
            return true;
        }
    }
    false
}

/// 带权无向边，用于 Kruskal。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct WeightedEdge {
    pub u: usize,
    pub v: usize,
    pub weight: u32,
}

impl WeightedEdge {
    pub fn new(u: usize, v: usize, weight: u32) -> Self {
        Self { u, v, weight }
    }
}

impl Ord for WeightedEdge {
    fn cmp(&self, other: &Self) -> Ordering {
        self.weight.cmp(&other.weight)
    }
}

impl PartialOrd for WeightedEdge {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Kruskal 最小生成树：返回 MST 的边集合与总权重。
/// 若图不连通，返回已选择的边（不构成生成树）。
pub fn kruskal_mst(edges: &mut [WeightedEdge], n: usize) -> (Vec<WeightedEdge>, u32) {
    edges.sort();
    let mut uf = UnionFind::new(n);
    let mut mst = Vec::new();
    let mut total = 0u32;

    for &edge in edges.iter() {
        if uf.union(edge.u, edge.v) {
            mst.push(edge);
            total += edge.weight;
        }
    }
    (mst, total)
}

/// 网络延迟时间：有向带权图，从节点 k 发出信号，返回所有节点收到信号所需最短时间。
/// 若存在不可达节点，返回 None。
pub fn network_delay_time(times: &[(usize, usize, u32)], n: usize, k: usize) -> Option<u32> {
    let mut graph: Vec<Vec<Edge>> = vec![Vec::new(); n];
    for &(u, v, w) in times {
        graph[u - 1].push(Edge::new(v - 1, w));
    }
    let dist = dijkstra(&graph, k - 1);
    let mut max_dist = 0u32;
    for d in dist {
        match d {
            Some(v) => max_dist = max_dist.max(v),
            None => return None,
        }
    }
    Some(max_dist)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dijkstra_basic() {
        // 图结构：
        // 0 --4--> 1 --1--> 2
        // 0 --1--> 3 --1--> 4 --1--> 2
        let graph = vec![
            vec![Edge::new(1, 4), Edge::new(3, 1)],
            vec![Edge::new(2, 1)],
            vec![],
            vec![Edge::new(4, 1)],
            vec![Edge::new(2, 1)],
        ];
        let dist = dijkstra(&graph, 0);
        assert_eq!(dist, vec![Some(0), Some(4), Some(3), Some(1), Some(2)]);
    }

    #[test]
    fn test_dijkstra_unreachable() {
        let graph = vec![vec![Edge::new(1, 1)], vec![], vec![]];
        let dist = dijkstra(&graph, 0);
        assert_eq!(dist, vec![Some(0), Some(1), None]);
    }

    #[test]
    fn test_topological_sort_basic() {
        let graph = vec![vec![1, 2], vec![3], vec![3], vec![]];
        let order = topological_sort(&graph).unwrap();
        assert_eq!(order[0], 0);
        assert_eq!(order[3], 3);
    }

    #[test]
    fn test_topological_sort_cycle() {
        let graph = vec![vec![1], vec![2], vec![0]];
        assert!(topological_sort(&graph).is_none());
    }

    #[test]
    fn test_union_find() {
        let mut uf = UnionFind::new(5);
        uf.union(0, 1);
        uf.union(1, 2);
        uf.union(3, 4);
        assert!(uf.connected(0, 2));
        assert!(!uf.connected(0, 3));
    }

    #[test]
    fn test_has_cycle_undirected() {
        let edges = vec![(0, 1), (1, 2), (2, 0)];
        assert!(has_cycle_undirected(&edges, 3));

        let tree = vec![(0, 1), (1, 2), (2, 3)];
        assert!(!has_cycle_undirected(&tree, 4));
    }

    #[test]
    fn test_kruskal_mst() {
        let mut edges = vec![
            WeightedEdge::new(0, 1, 10),
            WeightedEdge::new(0, 2, 6),
            WeightedEdge::new(0, 3, 5),
            WeightedEdge::new(1, 3, 15),
            WeightedEdge::new(2, 3, 4),
        ];
        let (mst, total) = kruskal_mst(&mut edges, 4);
        assert_eq!(total, 19);
        assert_eq!(mst.len(), 3);
    }

    #[test]
    fn test_network_delay_time() {
        let times = vec![(2, 1, 1), (2, 3, 1), (3, 4, 1)];
        assert_eq!(network_delay_time(&times, 4, 2), Some(2));

        let disconnected = vec![(1, 2, 1), (2, 3, 1)];
        assert_eq!(network_delay_time(&disconnected, 4, 1), None);
    }
}
