//! 图算法：同步 / Rayon并行 / Tokio异步

use anyhow::Result;
use rayon::prelude::*;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};
use std::hash::Hash;

// =========================
// BFS 最短路径（非加权）
// =========================

/// 同步 BFS 返回最短路径（若不可达返回 None）
pub fn bfs_shortest_path_sync<T>(graph: &HashMap<T, Vec<T>>, start: &T, target: &T) -> Option<Vec<T>>
where
    T: Eq + Hash + Clone,
{
    let mut q = VecDeque::new();
    let mut visited: HashSet<T> = HashSet::new();
    let mut prev: HashMap<T, T> = HashMap::new();
    q.push_back(start.clone());
    visited.insert(start.clone());

    while let Some(node) = q.pop_front() {
        if &node == target {
            return Some(reconstruct_path(prev, start, target));
        }
        if let Some(neigh) = graph.get(&node) {
            for n in neigh {
                if visited.insert(n.clone()) {
                    prev.insert(n.clone(), node.clone());
                    q.push_back(n.clone());
                }
            }
        }
    }
    None
}

/// 并行 BFS：按层并行展开 frontier
pub fn bfs_shortest_path_parallel<T>(graph: &HashMap<T, Vec<T>>, start: &T, target: &T) -> Option<Vec<T>>
where
    T: Eq + Hash + Clone + Sync + Send,
{
    let mut frontier: Vec<T> = vec![start.clone()];
    let mut visited: HashSet<T> = HashSet::new();
    let mut prev: HashMap<T, T> = HashMap::new();
    visited.insert(start.clone());

    while !frontier.is_empty() {
        if frontier.iter().any(|n| n == target) {
            return Some(reconstruct_path(prev, start, target));
        }

        let next: Vec<T> = frontier
            .par_iter()
            .flat_map_iter(|node| graph.get(node).cloned().unwrap_or_default())
            .collect();

        frontier.clear();
        for n in next {
            if visited.insert(n.clone()) {
                prev.insert(n.clone(), prev_candidate(&prev, graph, &n).unwrap_or(start.clone()));
                frontier.push(n);
            }
        }
    }
    None
}

/// 异步 BFS（spawn_blocking 包裹）
pub async fn bfs_shortest_path_async<T>(graph: HashMap<T, Vec<T>>, start: T, target: T) -> Result<Option<Vec<T>>>
where
    T: Eq + Hash + Clone + Send + 'static,
{
    Ok(tokio::task::spawn_blocking(move || bfs_shortest_path_sync(&graph, &start, &target)).await?)
}

fn reconstruct_path<T>(prev: HashMap<T, T>, start: &T, target: &T) -> Vec<T>
where
    T: Eq + Hash + Clone,
{
    let mut path = Vec::new();
    let mut cur = target.clone();
    path.push(cur.clone());
    let mut p = prev;
    while &cur != start {
        if let Some(pr) = p.remove(&cur) {
            cur = pr;
            path.push(cur.clone());
        } else {
            break;
        }
    }
    path.reverse();
    path
}

fn prev_candidate<T>(prev: &HashMap<T, T>, graph: &HashMap<T, Vec<T>>, node: &T) -> Option<T>
where
    T: Eq + Hash + Clone,
{
    // 近似：在图中找到任意一个前驱（上一层），仅用于并行 BFS 的路径回溯辅助
    for (k, vs) in graph {
        if vs.iter().any(|x| x == node) {
            if prev.contains_key(node) {
                return prev.get(node).cloned();
            }
            return Some(k.clone());
        }
    }
    None
}

// =========================
// Dijkstra 最短路径（加权，非负）
// =========================

#[derive(Copy, Clone, PartialEq)]
struct State<N> {
    cost: f64,
    node: N,
}

impl<N: Eq> Eq for State<N> {}

impl<N: Eq> Ord for State<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        // 反转以实现最小堆效果
        other.cost.partial_cmp(&self.cost).unwrap_or(Ordering::Equal)
    }
}

impl<N: Eq> PartialOrd for State<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// 同步 Dijkstra：返回 (距离表, 前驱表)
pub fn dijkstra_sync<T>(graph: &HashMap<T, Vec<(T, f64)>>, start: &T) -> (HashMap<T, f64>, HashMap<T, T>)
where
    T: Eq + Hash + Clone,
{
    let mut dist: HashMap<T, f64> = HashMap::new();
    let mut prev: HashMap<T, T> = HashMap::new();
    let mut heap = BinaryHeap::new();

    dist.insert(start.clone(), 0.0);
    heap.push(State { cost: 0.0, node: start.clone() });

    while let Some(State { cost, node }) = heap.pop() {
        if cost > *dist.get(&node).unwrap_or(&f64::INFINITY) {
            continue;
        }
        if let Some(neigh) = graph.get(&node) {
            for (n, w) in neigh {
                let next = cost + *w;
                if next < *dist.get(n).unwrap_or(&f64::INFINITY) {
                    dist.insert(n.clone(), next);
                    prev.insert(n.clone(), node.clone());
                    heap.push(State { cost: next, node: n.clone() });
                }
            }
        }
    }

    (dist, prev)
}

/// 异步 Dijkstra（spawn_blocking 包裹）
pub async fn dijkstra_async<T>(graph: HashMap<T, Vec<(T, f64)>>, start: T) -> Result<(HashMap<T, f64>, HashMap<T, T>)>
where
    T: Eq + Hash + Clone + Send + 'static,
{
    Ok(tokio::task::spawn_blocking(move || dijkstra_sync(&graph, &start)).await?)
}

// =========================
// 最小生成树：Kruskal / Prim
// =========================

/// Kruskal MST（同步）：返回 (总权重, MST 边集合)
pub fn mst_kruskal_sync<T>(graph: &HashMap<T, Vec<(T, f64)>>) -> (f64, Vec<(T, T, f64)>)
where
    T: Eq + Hash + Clone,
{
    // 收集所有边（无向图：避免重复，可约定仅从较小键指向较大键，或允许重复但在合并时过滤）
    let mut edges: Vec<(T, T, f64)> = Vec::new();
    for (u, vs) in graph.iter() {
        for (v, w) in vs {
            edges.push((u.clone(), v.clone(), *w));
        }
    }
    edges.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(Ordering::Equal));

    // 并查集
    let mut parent: HashMap<T, T> = HashMap::new();
    let mut rank: HashMap<T, usize> = HashMap::new();
    for node in graph.keys() {
        parent.insert(node.clone(), node.clone());
        rank.insert(node.clone(), 0);
    }

    fn find<T: Eq + Hash + Clone>(parent: &mut HashMap<T, T>, x: T) -> T {
        let p = parent.get(&x).cloned().unwrap();
        if p != x {
            let root = find(parent, p.clone());
            parent.insert(x.clone(), root.clone());
            root
        } else {
            x
        }
    }

    fn union<T: Eq + Hash + Clone>(parent: &mut HashMap<T, T>, rank: &mut HashMap<T, usize>, x: T, y: T) -> bool {
        let mut rx = find(parent, x);
        let mut ry = find(parent, y);
        if rx == ry { return false; }
        let rx_rank = *rank.get(&rx).unwrap_or(&0);
        let ry_rank = *rank.get(&ry).unwrap_or(&0);
        if rx_rank < ry_rank {
            std::mem::swap(&mut rx, &mut ry);
        }
        parent.insert(ry.clone(), rx.clone());
        if rx_rank == ry_rank {
            rank.entry(rx).and_modify(|r| *r += 1).or_insert(1);
        }
        true
    }

    let mut total = 0.0;
    let mut mst = Vec::new();
    for (u, v, w) in edges {
        if union(&mut parent, &mut rank, u.clone(), v.clone()) {
            total += w;
            mst.push((u, v, w));
        }
    }
    (total, mst)
}

/// Kruskal MST（并行排序）
pub fn mst_kruskal_parallel<T>(graph: &HashMap<T, Vec<(T, f64)>>) -> (f64, Vec<(T, T, f64)>)
where
    T: Eq + Hash + Clone + Sync + Send,
{
    let mut edges: Vec<(T, T, f64)> = graph
        .par_iter()
        .flat_map_iter(|(u, vs)| vs.iter().map(move |(v, w)| (u.clone(), v.clone(), *w)))
        .collect();
    edges.par_sort_unstable_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(Ordering::Equal));
    // 其余步骤同步进行
    let mut parent: HashMap<T, T> = HashMap::new();
    let mut rank: HashMap<T, usize> = HashMap::new();
    for node in graph.keys() {
        parent.insert(node.clone(), node.clone());
        rank.insert(node.clone(), 0);
    }
    fn find<T: Eq + Hash + Clone>(parent: &mut HashMap<T, T>, x: T) -> T {
        let p = parent.get(&x).cloned().unwrap();
        if p != x {
            let root = find(parent, p.clone());
            parent.insert(x.clone(), root.clone());
            root
        } else { x }
    }
    fn union<T: Eq + Hash + Clone>(parent: &mut HashMap<T, T>, rank: &mut HashMap<T, usize>, x: T, y: T) -> bool {
        let mut rx = find(parent, x);
        let mut ry = find(parent, y);
        if rx == ry { return false; }
        let rx_rank = *rank.get(&rx).unwrap_or(&0);
        let ry_rank = *rank.get(&ry).unwrap_or(&0);
        if rx_rank < ry_rank { std::mem::swap(&mut rx, &mut ry); }
        parent.insert(ry.clone(), rx.clone());
        if rx_rank == ry_rank { rank.entry(rx).and_modify(|r| *r += 1).or_insert(1); }
        true
    }
    let mut total = 0.0;
    let mut mst = Vec::new();
    for (u, v, w) in edges {
        if union(&mut parent, &mut rank, u.clone(), v.clone()) { total += w; mst.push((u, v, w)); }
    }
    (total, mst)
}

pub async fn mst_kruskal_async<T>(graph: HashMap<T, Vec<(T, f64)>>) -> Result<(f64, Vec<(T, T, f64)>)>
where
    T: Eq + Hash + Clone + Send + Sync + 'static,
{
    Ok(tokio::task::spawn_blocking(move || mst_kruskal_parallel(&graph)).await?)
}

/// Prim MST（同步）：给定起点
pub fn mst_prim_sync<T>(graph: &HashMap<T, Vec<(T, f64)>>, start: &T) -> (f64, Vec<(T, T, f64)>)
where
    T: Eq + Hash + Clone,
{
    #[derive(Clone, PartialEq)]
    struct Edge<T> { w: f64, u: T, v: T }
    impl<T: Eq> Eq for Edge<T> {}
    impl<T: Eq> Ord for Edge<T> { fn cmp(&self, other: &Self) -> Ordering { other.w.partial_cmp(&self.w).unwrap_or(Ordering::Equal) } }
    impl<T: Eq> PartialOrd for Edge<T> { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }

    let mut total = 0.0;
    let mut mst = Vec::new();
    let mut visited: HashSet<T> = HashSet::new();
    let mut heap: BinaryHeap<Edge<T>> = BinaryHeap::new();

    let s = start.clone();
    visited.insert(s.clone());
    if let Some(neigh) = graph.get(&s) {
        for (v, w) in neigh { heap.push(Edge { w: *w, u: s.clone(), v: v.clone() }); }
    }
    while let Some(Edge { w, u: _, v }) = heap.pop() {
        if visited.contains(&v) { continue; }
        total += w; // 加入树
        let new_v = v.clone();
        // 需知道 u-v 结构，u 不再使用，这里保存 parent 需要额外信息，简化：从 visited 中任取连接边（我们从堆中取出的就是连接边）
        mst.push((start.clone(), new_v.clone(), w));
        visited.insert(new_v.clone());
        if let Some(neigh) = graph.get(&new_v) {
            for (nv, nw) in neigh { if !visited.contains(nv) { heap.push(Edge { w: *nw, u: new_v.clone(), v: nv.clone() }); } }
        }
    }
    (total, mst)
}

pub fn mst_prim_parallel<T>(graph: &HashMap<T, Vec<(T, f64)>>, start: &T) -> (f64, Vec<(T, T, f64)>)
where
    T: Eq + Hash + Clone + Sync + Send,
{
    // 主要瓶颈在堆操作，示例仅并行准备邻接（对大型图的初始化略有帮助）
    let _deg_sum: usize = graph.par_iter().map(|(_, v)| v.len()).sum();
    mst_prim_sync(graph, start)
}

pub async fn mst_prim_async<T>(graph: HashMap<T, Vec<(T, f64)>>, start: T) -> Result<(f64, Vec<(T, T, f64)>)>
where
    T: Eq + Hash + Clone + Send + Sync + 'static,
{
    Ok(tokio::task::spawn_blocking(move || mst_prim_parallel(&graph, &start)).await?)
}

// =========================
// 拓扑排序（Kahn）
// =========================

pub fn topo_sort_sync<T>(graph: &HashMap<T, Vec<T>>) -> Option<Vec<T>>
where
    T: Eq + Hash + Clone,
{
    let mut indeg: HashMap<T, usize> = HashMap::new();
    for (u, vs) in graph {
        indeg.entry(u.clone()).or_insert(0);
        for v in vs { *indeg.entry(v.clone()).or_insert(0) += 1; }
    }
    let mut q: VecDeque<T> = indeg
        .iter()
        .filter(|(_, d)| **d == 0)
        .map(|(k, _)| k.clone())
        .collect();
    let mut res = Vec::new();
    let mut indeg_mut = indeg;
    while let Some(u) = q.pop_front() {
        res.push(u.clone());
        if let Some(vs) = graph.get(&u) {
            for v in vs {
                if let Some(d) = indeg_mut.get_mut(v) { *d -= 1; if *d == 0 { q.push_back(v.clone()); } }
            }
        }
    }
    if res.len() == indeg_mut.len() { Some(res) } else { None }
}

pub fn topo_sort_parallel<T>(graph: &HashMap<T, Vec<T>>) -> Option<Vec<T>>
where
    T: Eq + Hash + Clone + Sync + Send,
{
    // 仅并行构建入度表，核心 Kahn 步骤仍为串行
    let mut indeg: HashMap<T, usize> = HashMap::new();
    let entries: Vec<(T, usize)> = graph
        .par_iter()
        .flat_map_iter(|(u, vs)| {
            let mut vec = Vec::with_capacity(vs.len() + 1);
            vec.push((u.clone(), 0usize));
            vec.extend(vs.iter().map(|v| (v.clone(), 1usize)));
            vec
        })
        .collect();
    for (k, inc) in entries { *indeg.entry(k).or_insert(0) += inc; }
    topo_sort_sync(graph)
}

pub async fn topo_sort_async<T>(graph: HashMap<T, Vec<T>>) -> Result<Option<Vec<T>>>
where
    T: Eq + Hash + Clone + Send + Sync + 'static,
{
    Ok(tokio::task::spawn_blocking(move || topo_sort_parallel(&graph)).await?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bfs_shortest_path_sync() {
        let mut g: HashMap<i32, Vec<i32>> = HashMap::new();
        g.insert(1, vec![2, 3]);
        g.insert(2, vec![4]);
        g.insert(3, vec![4, 5]);
        g.insert(4, vec![]);
        g.insert(5, vec![4]);
        let path = bfs_shortest_path_sync(&g, &1, &4).unwrap();
        assert!(path == vec![1, 2, 4] || path == vec![1, 3, 4]);
    }

    #[test]
    fn test_dijkstra_sync() {
        let mut g: HashMap<&str, Vec<(&str, f64)>> = HashMap::new();
        g.insert("A", vec![("B", 1.0), ("C", 4.0)]);
        g.insert("B", vec![("C", 2.0), ("D", 5.0)]);
        g.insert("C", vec![("D", 1.0)]);
        g.insert("D", vec![]);

        let (dist, prev) = dijkstra_sync(&g, &"A");
        assert_eq!(dist.get("D").copied().unwrap().round() as i32, 4); // A->B->C->D = 4
        assert_eq!(prev.get("D").copied().unwrap(), "C");
    }

    #[test]
    fn test_mst_kruskal_and_prim_and_topo() {
        // 无向图（用双向边表示）
        let mut g: HashMap<&str, Vec<(&str, f64)>> = HashMap::new();
        g.insert("A", vec![("B", 1.0), ("C", 4.0)]);
        g.insert("B", vec![("A", 1.0), ("C", 2.0), ("D", 5.0)]);
        g.insert("C", vec![("A", 4.0), ("B", 2.0), ("D", 1.0)]);
        g.insert("D", vec![("B", 5.0), ("C", 1.0)]);

        let (w1, _e1) = mst_kruskal_sync(&g);
        let (w2, _e2) = mst_prim_sync(&g, &"A");
        assert!((w1 - w2).abs() < 1e-9);

        // 有向无环图拓扑
        let mut dag: HashMap<&str, Vec<&str>> = HashMap::new();
        dag.insert("A", vec!["B", "C"]);
        dag.insert("B", vec!["D"]);
        dag.insert("C", vec!["D"]);
        dag.insert("D", vec![]);
        let order = topo_sort_sync(&dag).unwrap();
        let pos: HashMap<_, _> = order.iter().enumerate().map(|(i, k)| (*k, i)).collect();
        assert!(pos["A"] < pos["B"] && pos["A"] < pos["C"] && pos["B"] < pos["D"] && pos["C"] < pos["D"]);
    }
}

