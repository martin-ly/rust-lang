//! 搜索算法：同步 / Rayon并行 / Tokio异步

use anyhow::Result;
use rayon::prelude::*;
use std::collections::{HashMap, VecDeque};
use std::hash::Hash;

// =========================
// 序列搜索
// =========================

/// 同步线性搜索，返回首次匹配的索引
pub fn linear_search_sync<T>(data: &[T], target: &T) -> Option<usize>
where
    T: PartialEq,
{
    data.iter().position(|x| x == target)
}

/// 同步二分搜索（要求已排序）
pub fn binary_search_sync<T>(data: &[T], target: &T) -> Result<Option<usize>>
where
    T: Ord,
{
    Ok(data.binary_search(target).ok())
}

/// 并行搜索：在未排序数据中查找目标元素的索引
pub fn parallel_search<T>(data: &[T], target: &T) -> Option<usize>
where
    T: PartialEq + Sync,
{
    data.par_iter()
        .enumerate()
        .find_any(|(_, x)| *x == target)
        .map(|(i, _)| i)
}

/// 异步线性搜索（spawn_blocking 包裹）
pub async fn linear_search_async<T>(data: Vec<T>, target: T) -> Result<Option<usize>>
where
    T: PartialEq + Send + 'static,
{
    Ok(tokio::task::spawn_blocking(move || {
        data.iter().position(|x| x == &target)
    })
    .await?)
}

/// 异步二分搜索（spawn_blocking 包裹，要求已排序）
pub async fn binary_search_async<T>(data: Vec<T>, target: T) -> Result<Option<usize>>
where
    T: Ord + Send + 'static,
{
    Ok(tokio::task::spawn_blocking(move || data.binary_search(&target).ok()).await?)
}

// =========================
// 简易图搜索（DFS / BFS）
// =========================

/// 同步 DFS：判断从 start 是否可达 target
pub fn dfs_sync<T>(graph: &HashMap<T, Vec<T>>, start: &T, target: &T) -> bool
where
    T: Eq + Hash + Clone,
{
    let mut stack = vec![start.clone()];
    let mut visited = std::collections::HashSet::new();
    while let Some(node) = stack.pop() {
        if !visited.insert(node.clone()) {
            continue;
        }
        if &node == target {
            return true;
        }
        if let Some(neigh) = graph.get(&node) {
            for n in neigh.iter().rev() {
                if !visited.contains(n) {
                    stack.push(n.clone());
                }
            }
        }
    }
    false
}

/// 同步 BFS：返回从 start 到 target 的层数（若不可达则 None）
pub fn bfs_sync<T>(graph: &HashMap<T, Vec<T>>, start: &T, target: &T) -> Option<usize>
where
    T: Eq + Hash + Clone,
{
    let mut q = VecDeque::new();
    let mut visited = std::collections::HashSet::new();
    q.push_back((start.clone(), 0usize));
    visited.insert(start.clone());
    while let Some((node, dist)) = q.pop_front() {
        if &node == target {
            return Some(dist);
        }
        if let Some(neigh) = graph.get(&node) {
            for n in neigh {
                if visited.insert(n.clone()) {
                    q.push_back((n.clone(), dist + 1));
                }
            }
        }
    }
    None
}

/// 异步 DFS（spawn_blocking 包裹）
pub async fn dfs_async<T>(graph: HashMap<T, Vec<T>>, start: T, target: T) -> Result<bool>
where
    T: Eq + Hash + Clone + Send + 'static,
{
    Ok(tokio::task::spawn_blocking(move || dfs_sync(&graph, &start, &target)).await?)
}

/// 异步 BFS（spawn_blocking 包裹）
pub async fn bfs_async<T>(graph: HashMap<T, Vec<T>>, start: T, target: T) -> Result<Option<usize>>
where
    T: Eq + Hash + Clone + Send + 'static,
{
    Ok(tokio::task::spawn_blocking(move || bfs_sync(&graph, &start, &target)).await?)
}

// =========================
// 指数搜索（Exponential Search）与三分搜索（Ternary Search）
// =========================

/// 指数搜索：在有序切片中查找 target，先指数扩展边界再二分
pub fn exponential_search_sync<T: Ord>(data: &[T], target: &T) -> Option<usize> {
    if data.is_empty() { return None; }
    if &data[0] == target { return Some(0); }
    let mut bound: usize = 1;
    while bound < data.len() && &data[bound] < target { bound <<= 1; }
    let left = bound >> 1;
    let right = data.len().min(bound + 1);
    data[left..right].binary_search(target).ok().map(|i| i + left)
}

pub async fn exponential_search_async<T: Ord + Send + 'static>(data: Vec<T>, target: T) -> Result<Option<usize>> {
    Ok(tokio::task::spawn_blocking(move || exponential_search_sync(&data, &target)).await?)
}

/// 三分搜索：对单峰实值函数在闭区间 [mut l, mut r] 上找近似极值（最大值）
pub fn ternary_search_max<F>(mut l: f64, mut r: f64, f: F, iters: usize) -> f64
where
    F: Fn(f64) -> f64,
{
    for _ in 0..iters {
        let m1 = l + (r - l) / 3.0;
        let m2 = r - (r - l) / 3.0;
        if f(m1) < f(m2) { l = m1; } else { r = m2; }
    }
    (l + r) / 2.0
}

pub async fn ternary_search_max_async<F>(l: f64, r: f64, f: F, iters: usize) -> Result<f64>
where
    F: Fn(f64) -> f64 + Send + Sync + 'static,
{
    let f_arc = std::sync::Arc::new(f);
    Ok(tokio::task::spawn_blocking(move || ternary_search_max(l, r, |x| (f_arc)(x), iters)).await?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linear_and_binary_sync() {
        let data = vec![1, 3, 5, 7, 9];
        assert_eq!(linear_search_sync(&data, &7), Some(3));
        assert_eq!(binary_search_sync(&data, &7).unwrap(), Some(3));
        assert_eq!(linear_search_sync(&data, &2), None);
    }

    #[test]
    fn test_parallel_search() {
        let data: Vec<_> = (0..10000).collect();
        let idx = parallel_search(&data, &7777).unwrap();
        assert_eq!(data[idx], 7777);
    }

    #[test]
    fn test_graph_search_sync() {
        let mut g: HashMap<i32, Vec<i32>> = HashMap::new();
        g.insert(1, vec![2, 3]);
        g.insert(2, vec![4]);
        g.insert(3, vec![4]);
        g.insert(4, vec![]);

        assert!(dfs_sync(&g, &1, &4));
        assert_eq!(bfs_sync(&g, &1, &4), Some(2));
    }

    #[test]
    fn test_exponential_and_ternary() {
        let data = vec![1,2,3,4,5,6,7,8,9];
        assert_eq!(exponential_search_sync(&data, &7), Some(6));
        let peak_at = ternary_search_max(0.0, 6.28318, |x| (x - 3.14159).cos(), 60);
        // 峰值位置应接近 0 或 2π（cos 最大在 0 处），这里区间包含 0
        assert!(peak_at < 1.0 || peak_at > 5.0);
    }
}

