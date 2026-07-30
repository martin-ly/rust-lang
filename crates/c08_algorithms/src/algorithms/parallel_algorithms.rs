//! # 并行算法（Parallel Algorithms）
//!
//! 本模块实现基于 Rayon 与 fork-join 模型的并行算法，包括并行前缀和、并行图算法
//! （BFS、SSSP、MST）、并行扫描/归约等。所有实现假设输入数据满足 `Send + Sync`。
//!
//! # 来源
//! - [Introduction to Algorithms (Cormen et al.)](https://mitpress.mit.edu/books/introduction-algorithms-fourth-edition)
//! - [Algorithm Engineering (Saunders / Demetrescu)](https://people.mpi-inf.mpg.de/~mehlhorn/LEDAbook.html)
//! - [Rayon docs](https://docs.rs/rayon/latest/rayon/)

use rayon::prelude::*;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashSet};

/// 并行前缀和（Parallel Prefix Sum / Scan）。
///
/// 使用两阶段算法：先分块局部扫描，再块间传播偏移量，最后合并。
/// 时间复杂度 O(n/p + log p)，空间复杂度 O(n)。
pub fn parallel_prefix_sum(input: &[i64]) -> Vec<i64> {
    if input.is_empty() {
        return Vec::new();
    }

    let n = input.len();
    let block_size = (n / rayon::current_num_threads()).max(1);

    // 阶段 1：每个块内局部前缀和
    let blocks: Vec<Vec<i64>> = input
        .par_chunks(block_size)
        .map(|chunk| {
            let mut local = Vec::with_capacity(chunk.len());
            let mut acc = 0i64;
            for &x in chunk {
                acc += x;
                local.push(acc);
            }
            local
        })
        .collect();

    // 阶段 2：块间偏移量
    let mut offsets = vec![0i64; blocks.len()];
    let mut acc = 0i64;
    for (i, block) in blocks.iter().enumerate() {
        offsets[i] = acc;
        acc += block.last().copied().unwrap_or(0);
    }

    // 阶段 3：将偏移量加到每个块
    blocks
        .into_par_iter()
        .enumerate()
        .flat_map_iter(|(i, block)| {
            let offset = offsets[i];
            block.into_iter().map(move |x| x + offset)
        })
        .collect()
}

/// 并行归约（Parallel Reduction）。
pub fn parallel_sum(input: &[i64]) -> i64 {
    input.par_iter().sum()
}

/// 并行 BFS（广度优先搜索）。
///
/// 返回从起点 `start` 到每个节点的最短距离（无权图）。使用 Rayon 并行化 frontier 扩展。
pub fn parallel_bfs(graph: &[Vec<usize>], start: usize) -> Vec<Option<usize>> {
    let n = graph.len();
    let mut dist = vec![None; n];
    let mut frontier = vec![start];
    dist[start] = Some(0);
    let mut d = 0usize;

    while !frontier.is_empty() {
        d += 1;
        // 并行收集所有邻居
        let next_frontier: Vec<usize> = frontier
            .par_iter()
            .flat_map(|&u| graph[u].par_iter().copied())
            .filter(|&v| dist[v].is_none())
            .collect();

        // 去重（简单实现）
        let unique: HashSet<usize> = next_frontier.into_iter().collect();
        frontier = unique
            .into_iter()
            .filter(|&v| {
                if dist[v].is_none() {
                    dist[v] = Some(d);
                    true
                } else {
                    false
                }
            })
            .collect();
    }

    dist
}

/// 单源最短路径（SSSP）—— 并行 Dijkstra 近似。
///
/// 使用优先队列 + 并行松弛。本实现为教学版；稠密图或特殊图应使用更专用算法。
pub fn parallel_dijkstra(graph: &[Vec<(usize, u64)>], start: usize) -> Vec<Option<u64>> {
    let n = graph.len();
    let mut dist: Vec<Option<u64>> = vec![None; n];
    let mut visited = vec![false; n];
    let mut heap = BinaryHeap::new();

    dist[start] = Some(0);
    heap.push(Reverse((0u64, start)));

    while let Some(Reverse((d, u))) = heap.pop() {
        if visited[u] {
            continue;
        }
        visited[u] = true;

        // 并行松弛邻居
        let relaxations: Vec<(usize, u64)> = graph[u]
            .par_iter()
            .filter_map(|&(v, w)| {
                let new_dist = d + w;
                match dist[v] {
                    Some(old) if old <= new_dist => None,
                    _ => Some((v, new_dist)),
                }
            })
            .collect();

        for (v, new_dist) in relaxations {
            dist[v] = Some(new_dist);
            heap.push(Reverse((new_dist, v)));
        }
    }

    dist
}

/// 并行最小生成树（MST）—— Kruskal 算法。
///
/// 边排序使用并行 `par_sort_unstable`，并查集合并串行执行。
pub fn parallel_kruskal(n: usize, mut edges: Vec<(usize, usize, u64)>) -> Vec<(usize, usize, u64)> {
    edges.par_sort_unstable_by_key(|&(_, _, w)| w);

    let mut dsu = crate::data_structure::dsu::DisjointSet::new(n);
    let mut mst = Vec::with_capacity(n.saturating_sub(1));

    for (u, v, w) in edges {
        if dsu.union(u, v) {
            mst.push((u, v, w));
            if mst.len() == n - 1 {
                break;
            }
        }
    }

    mst
}

/// Fork-Join 求和示例。
pub fn fork_join_sum(input: &[i64]) -> i64 {
    if input.len() <= 1024 {
        return input.iter().sum();
    }
    let mid = input.len() / 2;
    let (left, right) = input.split_at(mid);
    let (sum_left, sum_right) = rayon::join(|| fork_join_sum(left), || fork_join_sum(right));
    sum_left + sum_right
}

/// 并行扫描（scan / inclusive scan）。
pub fn parallel_scan(input: &[i64]) -> Vec<i64> {
    parallel_prefix_sum(input)
}

/// 返回当前线程池信息（用于 NUMA 感知示例）。
///
/// 真正的 NUMA 感知需要 `numa` 库或 `hwloc` 绑定；本函数仅作教学占位。
pub fn numa_info() -> String {
    format!(
        "current threads: {}, physical cpus: {}",
        rayon::current_num_threads(),
        num_cpus::get()
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_prefix_sum() {
        let input = vec![1, 2, 3, 4, 5];
        let result = parallel_prefix_sum(&input);
        assert_eq!(result, vec![1, 3, 6, 10, 15]);
    }

    #[test]
    fn test_parallel_bfs() {
        let graph = vec![
            vec![1, 2],
            vec![0, 3],
            vec![0, 3],
            vec![1, 2],
        ];
        let dist = parallel_bfs(&graph, 0);
        assert_eq!(dist, vec![Some(0), Some(1), Some(1), Some(2)]);
    }

    #[test]
    fn test_parallel_dijkstra() {
        let graph = vec![
            vec![(1, 1), (2, 4)],
            vec![(2, 2), (3, 5)],
            vec![(3, 1)],
            vec![],
        ];
        let dist = parallel_dijkstra(&graph, 0);
        assert_eq!(dist, vec![Some(0), Some(1), Some(3), Some(4)]);
    }

    #[test]
    fn test_parallel_kruskal() {
        let edges = vec![
            (0, 1, 1),
            (1, 2, 2),
            (0, 2, 3),
        ];
        let mst = parallel_kruskal(3, edges);
        assert_eq!(mst.len(), 2);
        assert_eq!(mst.iter().map(|e| e.2).sum::<u64>(), 3);
    }

    #[test]
    fn test_fork_join_sum() {
        let input: Vec<i64> = (1..=1000).collect();
        assert_eq!(fork_join_sum(&input), input.iter().sum::<i64>());
    }
}
