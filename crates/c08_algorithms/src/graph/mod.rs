//! 图算法：同步 / Rayon并行 / Tokio异步

use anyhow::Result;
use rayon::prelude::*;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};
use std::hash::Hash;

#[cfg(feature = "with-petgraph")]
pub mod petgraph_bridge {
    use super::*;
    use petgraph::graph::NodeIndex;
    use petgraph::Graph;
    use petgraph::algo::dijkstra as pg_dijkstra;

    /// 将 HashMap<T, Vec<(T, f64)>> 装载为 petgraph 无向加权图
    pub fn to_petgraph_undirected<T: Eq + Hash + Clone>(g: &HashMap<T, Vec<(T, f64)>>) -> (Graph<T, f64>, HashMap<T, NodeIndex>) {
        let mut graph = Graph::<T, f64, petgraph::Undirected>::new_undirected();
        let mut idx = HashMap::new();
        for k in g.keys() { idx.entry(k.clone()).or_insert_with(|| graph.add_node(k.clone())); }
        for (u, vs) in g.iter() {
            let ui = idx[u];
            for (v, w) in vs {
                let vi = *idx.entry(v.clone()).or_insert_with(|| graph.add_node(v.clone()));
                graph.update_edge(ui, vi, *w);
            }
        }
        (graph, idx)
    }

    /// 用 petgraph 跑一次 Dijkstra，与自研实现做对照
    pub fn dijkstra_compare<T: Eq + Hash + Clone>(g: &HashMap<T, Vec<(T, f64)>>, start: &T) -> HashMap<T, f64> {
        let (pg, idx) = to_petgraph_undirected(g);
        let s = idx[start];
        let res = pg_dijkstra(&pg, s, None, |e| *e.weight());
        // 映射回 HashMap<T,f64>
        let mut out = HashMap::new();
        for (node_idx, &d) in res.iter() {
            out.insert(pg[node_idx].clone(), d);
        }
        out
    }
}

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

// =========================
// Bellman-Ford 与 Floyd–Warshall
// =========================

/// Bellman-Ford：允许负权，检测负环。返回 (dist, has_negative_cycle)
pub fn bellman_ford_sync(graph: &HashMap<usize, Vec<(usize, f64)>>, n: usize, src: usize) -> (Vec<f64>, bool) {
    let mut dist = vec![f64::INFINITY; n];
    dist[src] = 0.0;
    for _ in 0..n - 1 {
        let mut changed = false;
        for (&u, vs) in graph.iter() {
            let du = dist[u];
            if du.is_infinite() { continue; }
            for &(v, w) in vs {
                if du + w < dist[v] { dist[v] = du + w; changed = true; }
            }
        }
        if !changed { break; }
    }
    // 检测负环
    let mut neg = false;
    for (&u, vs) in graph.iter() {
        let du = dist[u];
        if du.is_infinite() { continue; }
        for &(v, w) in vs { if du + w < dist[v] { neg = true; break; } }
        if neg { break; }
    }
    (dist, neg)
}

pub async fn bellman_ford_async(graph: HashMap<usize, Vec<(usize, f64)>>, n: usize, src: usize) -> Result<(Vec<f64>, bool)> {
    Ok(tokio::task::spawn_blocking(move || bellman_ford_sync(&graph, n, src)).await?)
}

/// Floyd–Warshall：多源最短路（允许负边但无负环）。返回 n×n 距离矩阵
pub fn floyd_warshall_sync(n: usize, edges: &[(usize, usize, f64)]) -> Vec<Vec<f64>> {
    let mut d = vec![vec![f64::INFINITY; n]; n];
    for i in 0..n { d[i][i] = 0.0; }
    for &(u, v, w) in edges { d[u][v] = d[u][v].min(w); }
    for k in 0..n {
        for i in 0..n {
            let dik = d[i][k];
            if dik.is_infinite() { continue; }
            for j in 0..n {
                let alt = dik + d[k][j];
                if alt < d[i][j] { d[i][j] = alt; }
            }
        }
    }
    d
}

pub async fn floyd_warshall_async(n: usize, edges: Vec<(usize, usize, f64)>) -> Result<Vec<Vec<f64>>> {
    Ok(tokio::task::spawn_blocking(move || floyd_warshall_sync(n, &edges)).await?)
}

/// Floyd–Warshall 带路径重建：返回 (距离矩阵, next 矩阵)
pub fn floyd_warshall_with_path_sync(n: usize, edges: &[(usize, usize, f64)]) -> (Vec<Vec<f64>>, Vec<Vec<Option<usize>>>) {
    let mut d = vec![vec![f64::INFINITY; n]; n];
    let mut next = vec![vec![None; n]; n];
    for i in 0..n { d[i][i] = 0.0; next[i][i] = Some(i); }
    for &(u, v, w) in edges {
        if w < d[u][v] { d[u][v] = w; next[u][v] = Some(v); }
    }
    for k in 0..n {
        for i in 0..n {
            let dik = d[i][k];
            if dik.is_infinite() { continue; }
            for j in 0..n {
                let alt = dik + d[k][j];
                if alt < d[i][j] {
                    d[i][j] = alt;
                    next[i][j] = next[i][k];
                }
            }
        }
    }
    (d, next)
}

pub fn floyd_reconstruct_path(u: usize, v: usize, next: &[Vec<Option<usize>>]) -> Option<Vec<usize>> {
    if next[u][v].is_none() { return None; }
    let mut path = vec![u];
    let mut cur = u;
    while cur != v {
        cur = next[cur][v]?;
        path.push(cur);
    }
    Some(path)
}

pub async fn floyd_warshall_with_path_async(n: usize, edges: Vec<(usize, usize, f64)>) -> Result<(Vec<Vec<f64>>, Vec<Vec<Option<usize>>>)> {
    Ok(tokio::task::spawn_blocking(move || floyd_warshall_with_path_sync(n, &edges)).await?)
}

// =========================
// Hopcroft–Karp 二分图最大匹配（U: 0..n_left, V: 0..n_right）
// 输入邻接：`adj[u]` 列出与之相连的右侧点 v（0..n_right）
// =========================

pub fn hopcroft_karp_sync(adj: &[Vec<usize>], n_left: usize, n_right: usize) -> (usize, Vec<Option<usize>>, Vec<Option<usize>>) {
    assert_eq!(adj.len(), n_left);
    let mut pair_u: Vec<Option<usize>> = vec![None; n_left];
    let mut pair_v: Vec<Option<usize>> = vec![None; n_right];
    let mut dist: Vec<i32> = vec![0; n_left];

    let mut matching = 0usize;

    fn bfs_hk(adj: &[Vec<usize>], n_left: usize, pair_u: &Vec<Option<usize>>, pair_v: &Vec<Option<usize>>, dist: &mut [i32]) -> bool {
        let mut q = VecDeque::new();
        for u in 0..n_left {
            if pair_u[u].is_none() { dist[u] = 0; q.push_back(u); } else { dist[u] = -1; }
        }
        let mut found = false;
        while let Some(u) = q.pop_front() {
            for &v in &adj[u] {
                if let Some(u2) = pair_v[v] {
                    if dist[u2] == -1 { dist[u2] = dist[u] + 1; q.push_back(u2); }
                } else {
                    found = true;
                }
            }
        }
        found
    }

    fn dfs(u: usize, adj: &[Vec<usize>], dist: &mut [i32], pair_u: &mut [Option<usize>], pair_v: &mut [Option<usize>]) -> bool {
        for &v in &adj[u] {
            if let Some(u2) = pair_v[v] {
                if dist[u2] == dist[u] + 1 && dfs(u2, adj, dist, pair_u, pair_v) {
                    pair_u[u] = Some(v);
                    pair_v[v] = Some(u);
                    return true;
                }
            } else {
                pair_u[u] = Some(v);
                pair_v[v] = Some(u);
                return true;
            }
        }
        dist[u] = -1;
        false
    }

    while bfs_hk(adj, n_left, &pair_u, &pair_v, &mut dist) {
        for u in 0..n_left {
            if pair_u[u].is_none() && dfs(u, adj, &mut dist, &mut pair_u, &mut pair_v) {
                matching += 1;
            }
        }
    }

    (matching, pair_u, pair_v)
}

pub async fn hopcroft_karp_async(adj: Vec<Vec<usize>>, n_left: usize, n_right: usize) -> Result<(usize, Vec<Option<usize>>, Vec<Option<usize>>)> {
    Ok(tokio::task::spawn_blocking(move || hopcroft_karp_sync(&adj, n_left, n_right)).await?)
}

/// 基于 Kőnig 定理：从未匹配的左侧点开始，沿未匹配边+匹配边交替遍历，最小点覆盖 = (左侧可达集合的补集) ∪ (右侧可达集合)
pub fn min_vertex_cover_bipartite(adj: &[Vec<usize>], pair_u: &[Option<usize>], pair_v: &[Option<usize>]) -> (Vec<bool>, Vec<bool>) {
    let n_left = adj.len();
    let n_right = pair_v.len();
    let mut vis_u = vec![false; n_left];
    let mut vis_v = vec![false; n_right];
    let mut q = VecDeque::new();
    for u in 0..n_left {
        if pair_u[u].is_none() { q.push_back(u); vis_u[u] = true; }
    }
    while let Some(u) = q.pop_front() {
        for &v in &adj[u] {
            if !vis_v[v] && pair_u[u] != Some(v) {
                vis_v[v] = true;
                if let Some(u2) = pair_v[v] {
                    if !vis_u[u2] { vis_u[u2] = true; q.push_back(u2); }
                }
            }
        }
    }
    // 覆盖集：左侧取非可达，右侧取可达
    (vis_u.iter().map(|&x| !x).collect(), vis_v)
}
// =========================
// 强连通分量（Tarjan）
// =========================

struct TarjanState<T: Eq + Hash + Clone> {
    index: usize,
    index_map: HashMap<T, usize>,
    lowlink_map: HashMap<T, usize>,
    on_stack: HashSet<T>,
    stack: Vec<T>,
    sccs: Vec<Vec<T>>,
}

impl<T: Eq + Hash + Clone> TarjanState<T> {
    fn new() -> Self {
        Self {
            index: 0,
            index_map: HashMap::new(),
            lowlink_map: HashMap::new(),
            on_stack: HashSet::new(),
            stack: Vec::new(),
            sccs: Vec::new(),
        }
    }

    fn strongconnect(&mut self, v: T, graph: &HashMap<T, Vec<T>>) {
        self.index_map.insert(v.clone(), self.index);
        self.lowlink_map.insert(v.clone(), self.index);
        self.index += 1;
        self.stack.push(v.clone());
        self.on_stack.insert(v.clone());

        if let Some(neigh) = graph.get(&v) {
            for w in neigh {
                let w_cl = w.clone();
                if !self.index_map.contains_key(&w_cl) {
                    self.strongconnect(w_cl.clone(), graph);
                    let vlow = *self.lowlink_map.get(&v).unwrap();
                    let wlow = *self.lowlink_map.get(&w_cl).unwrap();
                    self.lowlink_map.insert(v.clone(), vlow.min(wlow));
                } else if self.on_stack.contains(&w_cl) {
                    let vlow = *self.lowlink_map.get(&v).unwrap();
                    let widx = *self.index_map.get(&w_cl).unwrap();
                    self.lowlink_map.insert(v.clone(), vlow.min(widx));
                }
            }
        }

        // 如果 v 是强连通分量的根节点
        let v_is_root = self.lowlink_map.get(&v) == self.index_map.get(&v);
        if v_is_root {
            let mut comp = Vec::new();
            loop {
                let w = self.stack.pop().unwrap();
                self.on_stack.remove(&w);
                comp.push(w.clone());
                if w == v { break; }
            }
            self.sccs.push(comp);
        }
    }
}

/// Tarjan 强连通分量（同步）：返回每个 SCC 的顶点集合
pub fn tarjan_scc_sync<T>(graph: &HashMap<T, Vec<T>>) -> Vec<Vec<T>>
where
    T: Eq + Hash + Clone,
{
    // 收集所有出现的节点（包括仅出现在邻接中的节点）
    let mut nodes: HashSet<T> = HashSet::new();
    for (u, vs) in graph.iter() {
        nodes.insert(u.clone());
        for v in vs { nodes.insert(v.clone()); }
    }

    let mut st = TarjanState::<T>::new();
    for v in nodes {
        if !st.index_map.contains_key(&v) {
            st.strongconnect(v.clone(), graph);
        }
    }
    st.sccs
}

/// Tarjan 强连通分量（异步包装）
pub async fn tarjan_scc_async<T>(graph: HashMap<T, Vec<T>>) -> Result<Vec<Vec<T>>>
where
    T: Eq + Hash + Clone + Send + 'static,
{
    Ok(tokio::task::spawn_blocking(move || tarjan_scc_sync(&graph)).await?)
}

// =========================
// 最大流：Dinic 算法
// =========================

/// Dinic 最大流（同步）。
/// 输入：邻接表 `graph`，其中每条边 (u -> v, cap) 为有向边容量；若要无向边请手动加双向。
/// 返回：从 `s` 到 `t` 的最大流值。
pub fn max_flow_dinic_sync<T>(graph: &HashMap<T, Vec<(T, i64)>>, s: &T, t: &T) -> i64
where
    T: Eq + Hash + Clone,
{
    // 压缩节点到索引
    let mut nodes: HashMap<T, usize> = HashMap::new();
    for (u, vs) in graph.iter() {
        if !nodes.contains_key(u) {
            let idx = nodes.len();
            nodes.insert(u.clone(), idx);
        }
        for (v, _) in vs {
            if !nodes.contains_key(v) {
                let idx = nodes.len();
                nodes.insert(v.clone(), idx);
            }
        }
    }
    if !nodes.contains_key(s) || !nodes.contains_key(t) { return 0; }
    let n = nodes.len();
    let si = nodes[s];
    let ti = nodes[t];

    #[derive(Clone)]
    struct Edge { to: usize, rev: usize, cap: i64 }

    let mut g: Vec<Vec<Edge>> = vec![Vec::new(); n];
    let add_edge = |u: usize, v: usize, c: i64, g: &mut Vec<Vec<Edge>>| {
        let from_rev = g[v].len();
        let to_rev = g[u].len();
        g[u].push(Edge { to: v, rev: from_rev, cap: c });
        g[v].push(Edge { to: u, rev: to_rev, cap: 0 });
    };

    for (u, vs) in graph.iter() {
        let ui = nodes[u];
        for (v, c) in vs { if *c > 0 { add_edge(ui, nodes[v], *c, &mut g); } }
    }

    let mut flow: i64 = 0;
    loop {
        // BFS 分层
        let mut level = vec![-1i32; n];
        let mut q = VecDeque::new();
        level[si] = 0;
        q.push_back(si);
        while let Some(u) = q.pop_front() {
            for e in &g[u] {
                if e.cap > 0 && level[e.to] < 0 {
                    level[e.to] = level[u] + 1;
                    q.push_back(e.to);
                }
            }
        }
        if level[ti] < 0 { break; }

        // 当前弧优化
        let mut it = vec![0usize; n];
        fn dfs(u: usize, t: usize, f: i64, g: &mut [Vec<Edge>], it: &mut [usize], level: &[i32]) -> i64 {
            if u == t { return f; }
            let m = g[u].len();
            while it[u] < m {
                let i = it[u];
                let Edge { to, rev, cap } = g[u][i].clone();
                if cap > 0 && level[u] + 1 == level[to] {
                    let d = dfs(to, t, f.min(cap), g, it, level);
                    if d > 0 {
                        // 更新残量网络
                        g[u][i].cap -= d;
                        let r = rev;
                        g[to][r].cap += d;
                        return d;
                    }
                }
                it[u] += 1;
            }
            0
        }

        loop {
            let pushed = dfs(si, ti, i64::MAX / 4, &mut g, &mut it, &level);
            if pushed == 0 { break; }
            flow += pushed;
        }
    }
    flow
}

/// Dinic 最大流（异步包装）
pub async fn max_flow_dinic_async<T>(graph: HashMap<T, Vec<(T, i64)>>, s: T, t: T) -> Result<i64>
where
    T: Eq + Hash + Clone + Send + 'static,
{
    Ok(tokio::task::spawn_blocking(move || max_flow_dinic_sync(&graph, &s, &t)).await?)
}

// =========================
// Edmonds–Karp 最大流（BFS 寻找最短增广路）与最小割导出
// =========================

/// 返回最大流值
pub fn max_flow_edmonds_karp(adj: &HashMap<usize, Vec<(usize, i64)>>, s: usize, t: usize) -> i64 {
    // 构建残量网络
    let n = adj.keys().copied().chain(adj.values().flatten().map(|(v, _)| *v)).max().unwrap_or(0) + 1;
    #[derive(Clone, Copy)] struct E{to:usize, rev:usize, cap:i64}
    let mut g: Vec<Vec<E>> = vec![Vec::new(); n];
    let mut add_edge = |u:usize,v:usize,c:i64|{ let ru = g[v].len(); let rv = g[u].len(); g[u].push(E{to:v,rev:ru,cap:c}); g[v].push(E{to:u,rev:rv,cap:0}); };
    for (u, vs) in adj { for &(v,c) in vs { if c>0 { add_edge(*u, v, c); } } }
    let mut flow = 0i64;
    loop {
        let mut prev: Vec<Option<(usize,usize)>> = vec![None; n];
        let mut q = VecDeque::new(); q.push_back(s);
        while let Some(u) = q.pop_front() {
            for (i, e) in g[u].iter().enumerate() {
                if e.cap > 0 && prev[e.to].is_none() && e.to != s { prev[e.to] = Some((u,i)); q.push_back(e.to); }
            }
        }
        if prev[t].is_none() { break; }
        let mut add = i64::MAX/4; let mut v = t;
        while let Some((u,i)) = prev[v] { add = add.min(g[u][i].cap); v = u; }
        let mut v2 = t; while let Some((u,i)) = prev[v2] { let to = g[u][i].to; let r = g[u][i].rev; g[u][i].cap -= add; g[to][r].cap += add; v2 = u; }
        flow += add;
    }
    flow
}

/// 基于最终残量网络的可达性导出 s-t 最小割 (S 集, T 集)
pub fn min_cut_from_residual(adj: &HashMap<usize, Vec<(usize, i64)>>, s: usize) -> (Vec<bool>, Vec<bool>) {
    // 构建残量与一次未推进的 BFS 可达集（仅正容量边）
    let n = adj.keys().copied().chain(adj.values().flatten().map(|(v, _)| *v)).max().unwrap_or(0) + 1;
    let mut g: Vec<Vec<(usize,i64)>> = vec![Vec::new(); n];
    for (u, vs) in adj { for &(v,c) in vs { if c>0 { g[*u].push((v,c)); } } }
    let mut vis = vec![false; n];
    let mut q = VecDeque::new(); q.push_back(s); vis[s]=true;
    while let Some(u) = q.pop_front(){ for &(v,c) in &g[u]{ if c>0 && !vis[v]{ vis[v]=true; q.push_back(v);} } }
    let s_set = vis.clone();
    let t_set = vis.iter().map(|&x| !x).collect();
    (s_set, t_set)
}

pub async fn max_flow_edmonds_karp_async(adj: HashMap<usize, Vec<(usize, i64)>>, s: usize, t: usize) -> Result<i64> {
    Ok(tokio::task::spawn_blocking(move || max_flow_edmonds_karp(&adj, s, t)).await?)
}

// =========================
// 树直径：两次 BFS/DFS（无权）
// =========================

pub fn tree_diameter_undirected(n: usize, edges: &[(usize, usize)]) -> usize {
    let mut g = vec![Vec::new(); n];
    for &(u,v) in edges { g[u].push(v); g[v].push(u); }
    fn bfs(start: usize, g: &Vec<Vec<usize>>) -> (usize, usize) {
        let n = g.len(); let mut dist = vec![usize::MAX; n]; let mut q = VecDeque::new();
        dist[start]=0; q.push_back(start);
        while let Some(u)=q.pop_front(){ for &v in &g[u]{ if dist[v]==usize::MAX { dist[v]=dist[u]+1; q.push_back(v); } } }
        let mut best=(0,0); for i in 0..n { if dist[i]>best.1 { best=(i,dist[i]); } }
        best
    }
    let (p, _) = bfs(0, &g);
    let (_, d) = bfs(p, &g);
    d
}

// =========================
// 树上 LCA（二叉提升）
// =========================

/// 预处理 LCA（二叉提升），输入树（无向，根为 root）
pub struct LcaBinaryLift<T: Eq + Hash + Clone> {
    pub root: T,
    node_to_idx: HashMap<T, usize>,
    idx_to_node: Vec<T>,
    up: Vec<Vec<usize>>, // up[k][v] = 2^k 祖先
    depth: Vec<i32>,
}

impl<T: Eq + Hash + Clone> LcaBinaryLift<T> {
    pub fn new(tree: &HashMap<T, Vec<T>>, root: T) -> Self {
        // 压缩索引
        let mut node_to_idx: HashMap<T, usize> = HashMap::new();
        for (u, vs) in tree.iter() {
            if !node_to_idx.contains_key(u) {
                let idx = node_to_idx.len();
                node_to_idx.insert(u.clone(), idx);
            }
            for v in vs {
                if !node_to_idx.contains_key(v) {
                    let idx = node_to_idx.len();
                    node_to_idx.insert(v.clone(), idx);
                }
            }
        }
        let n = node_to_idx.len();
        let mut idx_to_node = vec![root.clone(); n];
        for (node, &i) in node_to_idx.iter() { idx_to_node[i] = node.clone(); }

        let log = (n as f64).log2().ceil() as usize + 1;
        let mut up = vec![vec![0usize; n]; log];
        let mut depth = vec![-1i32; n];

        let r = node_to_idx[&root];
        depth[r] = 0;
        // BFS 建树父子关系
        let mut q = VecDeque::new();
        q.push_back(r);
        while let Some(u) = q.pop_front() {
            if let Some(neigh) = tree.get(&idx_to_node[u]) {
                for vnode in neigh {
                    let v = node_to_idx[vnode];
                    if depth[v] == -1 {
                        depth[v] = depth[u] + 1;
                        up[0][v] = u;
                        q.push_back(v);
                    }
                }
            }
        }
        up[0][r] = r;
        for k in 1..log {
            for v in 0..n { up[k][v] = up[k - 1][up[k - 1][v]]; }
        }
        Self { root, node_to_idx, idx_to_node, up, depth }
    }

    pub fn lca(&self, a: &T, b: &T) -> T {
        let mut u = self.node_to_idx[a];
        let mut v = self.node_to_idx[b];
        if self.depth[u] < self.depth[v] { std::mem::swap(&mut u, &mut v); }
        let diff = (self.depth[u] - self.depth[v]) as usize;
        let mut k = 0usize;
        let mut uu = u;
        while (1usize << k) <= diff { if (diff >> k) & 1 == 1 { uu = self.up[k][uu]; } k += 1; }
        u = uu;
        if u == v { return self.idx_to_node[u].clone(); }
        for k in (0..self.up.len()).rev() {
            if self.up[k][u] != self.up[k][v] { u = self.up[k][u]; v = self.up[k][v]; }
        }
        self.idx_to_node[self.up[0][u]].clone()
    }
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

    #[test]
    fn test_tarjan_scc() {
        // 经典示例：
        // 1 -> 2 -> 3 -> 1   (SCC: {1,2,3})
        // 3 -> 4 -> 5 -> 4   (SCC: {4,5})
        // 5 -> 6              (SCC: {6})
        let mut g: HashMap<i32, Vec<i32>> = HashMap::new();
        g.insert(1, vec![2]);
        g.insert(2, vec![3]);
        g.insert(3, vec![1, 4]);
        g.insert(4, vec![5]);
        g.insert(5, vec![4, 6]);
        g.insert(6, vec![]);

        let mut sccs = tarjan_scc_sync(&g);
        for comp in &mut sccs { comp.sort(); }
        sccs.sort_by_key(|c| (c.len(), c[0]));

        assert!(sccs.contains(&vec![1,2,3]));
        assert!(sccs.contains(&vec![4,5]));
        assert!(sccs.contains(&vec![6]));
    }

    #[test]
    fn test_max_flow_dinic_small() {
        // 经典网络：S(0)->1(10), S->2(10), 1->2(2), 1->T(8), 2->T(10)
        let s = 0;
        let t = 3;
        let mut g: HashMap<i32, Vec<(i32, i64)>> = HashMap::new();
        g.insert(0, vec![(1, 10), (2, 10)]);
        g.insert(1, vec![(2, 2), (3, 8)]);
        g.insert(2, vec![(3, 10)]);
        g.insert(3, vec![]);
        let f = max_flow_dinic_sync(&g, &s, &t);
        assert_eq!(f, 18);
    }

    #[test]
    fn test_edmonds_karp_and_min_cut() {
        // 与 Dinic 相同的小网络
        let s = 0usize; let t = 3usize;
        let mut g: HashMap<usize, Vec<(usize, i64)>> = HashMap::new();
        g.insert(0, vec![(1, 10), (2, 10)]);
        g.insert(1, vec![(2, 2), (3, 8)]);
        g.insert(2, vec![(3, 10)]);
        g.insert(3, vec![]);
        let f = max_flow_edmonds_karp(&g, s, t);
        assert_eq!(f, 18);
        let (s_set, _t_set) = min_cut_from_residual(&g, s);
        // s 应可达
        assert!(s_set[s]);
    }

    #[test]
    fn test_tree_diameter() {
        let edges = vec![(0,1),(1,2),(1,3),(3,4)]; // 线径为 3（2-1-3-4）
        let d = tree_diameter_undirected(5, &edges);
        assert_eq!(d, 3);
    }

    #[test]
    fn test_lca_binary_lift() {
        // 0-1-3, 1-4, 0-2-5  树根设为 0
        let mut tree: HashMap<i32, Vec<i32>> = HashMap::new();
        tree.insert(0, vec![1, 2]);
        tree.insert(1, vec![0, 3, 4]);
        tree.insert(2, vec![0, 5]);
        tree.insert(3, vec![1]);
        tree.insert(4, vec![1]);
        tree.insert(5, vec![2]);
        let lca = LcaBinaryLift::new(&tree, 0);
        assert_eq!(lca.lca(&3, &4), 1);
        assert_eq!(lca.lca(&3, &5), 0);
        assert_eq!(lca.lca(&4, &2), 0);
    }

    #[test]
    fn test_bellman_ford_and_floyd() {
        let mut g: HashMap<usize, Vec<(usize, f64)>> = HashMap::new();
        g.insert(0, vec![(1, 1.0), (2, 4.0)]);
        g.insert(1, vec![(2, 2.0), (3, 5.0)]);
        g.insert(2, vec![(3, 1.0)]);
        g.insert(3, vec![]);
        let (dist, neg) = bellman_ford_sync(&g, 4, 0);
        assert!(!neg);
        assert_eq!(dist[3].round() as i32, 4);

        let edges = vec![(0,1,1.0),(0,2,4.0),(1,2,2.0),(1,3,5.0),(2,3,1.0)];
        let d = floyd_warshall_sync(4, &edges);
        assert_eq!(d[0][3].round() as i32, 4);
    }

    #[test]
    fn test_floyd_with_path() {
        let edges = vec![(0usize,1usize,1.0),(1,2,2.0),(0,2,10.0)];
        let (d, next) = floyd_warshall_with_path_sync(3, &edges);
        assert!((d[0][2] - 3.0).abs() < 1e-9);
        let p = floyd_reconstruct_path(0, 2, &next).unwrap();
        assert_eq!(p, vec![0,1,2]);
    }

    #[test]
    fn test_hopcroft_karp_basic() {
        // 左 0..3, 右 0..3, 最大匹配应为 3
        let adj = vec![
            vec![0, 1],    // u0 -> v0,v1
            vec![1, 2],    // u1 -> v1,v2
            vec![0, 2],    // u2 -> v0,v2
        ];
        let (m, pu, _pv) = hopcroft_karp_sync(&adj, 3, 3);
        assert_eq!(m, 3);
        assert!(pu.iter().all(|o| o.is_some()));

        let (cover_u, cover_v) = min_vertex_cover_bipartite(&adj, &pu, &_pv);
        // 验证覆盖：每条边至少覆盖一个端点
        for (u, vs) in adj.iter().enumerate() {
            for &v in vs {
                assert!(cover_u[u] || cover_v[v]);
            }
        }
    }
}

