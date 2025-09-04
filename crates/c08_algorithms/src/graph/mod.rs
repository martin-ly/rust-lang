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
}

