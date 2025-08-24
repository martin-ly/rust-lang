//! 并行算法实现模块
//! 
//! 本模块提供了Rust中的并行算法实现，包括：
//! - 并行排序算法
//! - 并行搜索算法
//! - 并行图算法

use rayon::prelude::*;
use std::sync::{Arc, Mutex};

/// 并行排序算法实现
pub struct ParallelSort;

impl ParallelSort {
    /// 并行快速排序
    pub fn parallel_quicksort<T: Ord + Send + Sync>(arr: &mut [T]) {
        if arr.len() <= 1 {
            return;
        }
        
        let pivot_index = Self::partition(arr);
        let (left, right) = arr.split_at_mut(pivot_index);
        
        // 并行处理左右两部分
        rayon::join(
            || Self::parallel_quicksort(left),
            || Self::parallel_quicksort(&mut right[1..])
        );
    }
    
    /// 并行归并排序
    pub fn parallel_mergesort<T: Ord + Send + Sync + Clone>(arr: &mut [T]) {
        if arr.len() <= 1 {
            return;
        }
        
        let mid = arr.len() / 2;
        let (left, right) = arr.split_at_mut(mid);
        
        // 并行排序左右两部分
        rayon::join(
            || Self::parallel_mergesort(left),
            || Self::parallel_mergesort(right)
        );
        
        // 合并排序结果
        Self::merge(arr, mid);
    }
    
    /// 并行基数排序
    pub fn parallel_radix_sort(arr: &mut [u32]) {
        const RADIX: usize = 256;
        const BITS: usize = 32;
        
        for shift in (0..BITS).step_by(8) {
            let mut counts = vec![0; RADIX];
            
            // 并行计算计数
            arr.par_iter().for_each(|&num| {
                let digit = ((num >> shift) & 0xFF) as usize;
                counts[digit] += 1;
            });
            
            // 计算前缀和
            for i in 1..RADIX {
                counts[i] += counts[i - 1];
            }
            
            // 并行重排
            let mut output = vec![0; arr.len()];
            arr.par_iter().enumerate().for_each(|(i, &num)| {
                let digit = ((num >> shift) & 0xFF) as usize;
                let pos = counts[digit] - 1;
                output[pos] = num;
                counts[digit] -= 1;
            });
            
            arr.copy_from_slice(&output);
        }
    }
    
    fn partition<T: Ord>(arr: &mut [T]) -> usize {
        let pivot_index = arr.len() - 1;
        let mut i = 0;
        
        for j in 0..pivot_index {
            if arr[j] <= arr[pivot_index] {
                arr.swap(i, j);
                i += 1;
            }
        }
        
        arr.swap(i, pivot_index);
        i
    }
    
    fn merge<T: Ord + Clone>(arr: &mut [T], mid: usize) {
        let left = arr[..mid].to_vec();
        let right = arr[mid..].to_vec();
        
        let mut i = 0;
        let mut j = 0;
        let mut k = 0;
        
        while i < left.len() && j < right.len() {
            if left[i] <= right[j] {
                arr[k] = left[i].clone();
                i += 1;
            } else {
                arr[k] = right[j].clone();
                j += 1;
            }
            k += 1;
        }
        
        while i < left.len() {
            arr[k] = left[i].clone();
            i += 1;
            k += 1;
        }
        
        while j < right.len() {
            arr[k] = right[j].clone();
            j += 1;
            k += 1;
        }
    }
}

/// 并行搜索算法实现
pub struct ParallelSearch;

impl ParallelSearch {
    /// 并行二分搜索
    pub fn parallel_binary_search<T: Ord + Send + Sync>(
        arr: &[T],
        target: &T,
    ) -> Option<usize> {
        if arr.is_empty() {
            return None;
        }
        
        let chunk_size = (arr.len() + rayon::current_num_threads() - 1) / rayon::current_num_threads();
        let chunks: Vec<&[T]> = arr.chunks(chunk_size).collect();
        
        // 并行搜索每个块
        let results: Vec<Option<usize>> = chunks
            .par_iter()
            .enumerate()
            .map(|(chunk_idx, chunk)| {
                if let Some(pos) = chunk.binary_search(target).ok() {
                    Some(chunk_idx * chunk_size + pos)
                } else {
                    None
                }
            })
            .collect();
        
        // 返回第一个找到的结果
        results.into_iter().find(|r| r.is_some()).flatten()
    }
    
    /// 并行线性搜索
    pub fn parallel_linear_search<T: PartialEq + Send + Sync>(
        arr: &[T],
        target: &T,
    ) -> Option<usize> {
        arr.par_iter()
            .position_any(|item| item == target)
    }
    
    /// 并行最大值搜索
    pub fn parallel_max<T: Ord + Send + Sync>(arr: &[T]) -> Option<&T> {
        arr.par_iter().max()
    }
    
    /// 并行最小值搜索
    pub fn parallel_min<T: Ord + Send + Sync>(arr: &[T]) -> Option<&T> {
        arr.par_iter().min()
    }
}

/// 并行图算法实现
pub struct ParallelGraph;

impl ParallelGraph {
    /// 并行广度优先搜索
    pub fn parallel_bfs<F>(
        start: usize,
        neighbors: F,
        num_nodes: usize,
    ) -> Vec<usize>
    where
        F: Fn(usize) -> Vec<usize> + Send + Sync,
    {
        let mut distances = vec![usize::MAX; num_nodes];
        let mut visited = vec![false; num_nodes];
        let mut current_level = vec![start];
        
        distances[start] = 0;
        visited[start] = true;
        
        let mut level = 0;
        
        while !current_level.is_empty() {
            let next_level: Vec<usize> = current_level
                .par_iter()
                .flat_map(|&node| {
                    neighbors(node)
                        .into_iter()
                        .filter(|&neighbor| !visited[neighbor])
                })
                .collect();
            
            // 并行更新距离和访问状态
            next_level.par_iter().for_each(|&node| {
                distances[node] = level + 1;
                visited[node] = true;
            });
            
            current_level = next_level;
            level += 1;
        }
        
        distances
    }
    
    /// 并行深度优先搜索
    pub fn parallel_dfs<F>(
        start: usize,
        neighbors: F,
        num_nodes: usize,
    ) -> Vec<bool>
    where
        F: Fn(usize) -> Vec<usize> + Send + Sync,
    {
        let mut visited = vec![false; num_nodes];
        let visited_mutex = Arc::new(Mutex::new(&mut visited));
        
        Self::parallel_dfs_recursive(start, &neighbors, visited_mutex);
        
        visited
    }
    
    fn parallel_dfs_recursive<F>(
        node: usize,
        neighbors: &F,
        visited: Arc<Mutex<&mut [bool]>>,
    ) where
        F: Fn(usize) -> Vec<usize> + Send + Sync,
    {
        {
            let mut visited_guard = visited.lock().unwrap();
            if visited_guard[node] {
                return;
            }
            visited_guard[node] = true;
        }
        
        let neighbor_list = neighbors(node);
        
        // 并行访问邻居
        neighbor_list.par_iter().for_each(|&neighbor| {
            Self::parallel_dfs_recursive(neighbor, neighbors, Arc::clone(&visited));
        });
    }
    
    /// 并行最短路径算法 (Floyd-Warshall)
    pub fn parallel_floyd_warshall(graph: &mut Vec<Vec<f64>>) {
        let n = graph.len();
        
        for k in 0..n {
            // 并行更新所有距离
            graph.par_iter_mut().enumerate().for_each(|(i, row)| {
                for j in 0..n {
                    let new_distance = graph[i][k] + graph[k][j];
                    if new_distance < row[j] {
                        row[j] = new_distance;
                    }
                }
            });
        }
    }
    
    /// 并行最小生成树算法 (Kruskal)
    pub fn parallel_kruskal(
        edges: &mut Vec<(usize, usize, f64)>,
        num_nodes: usize,
    ) -> Vec<(usize, usize, f64)> {
        // 按权重排序边
        edges.par_sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap());
        
        let mut parent: Vec<usize> = (0..num_nodes).collect();
        let mut rank = vec![0; num_nodes];
        let mut mst = Vec::new();
        
        for &(u, v, weight) in edges.iter() {
            if Self::parallel_union_find(&mut parent, &mut rank, u, v) {
                mst.push((u, v, weight));
            }
        }
        
        mst
    }
    
    fn parallel_union_find(
        parent: &mut [usize],
        rank: &mut [usize],
        mut x: usize,
        mut y: usize,
    ) -> bool {
        x = Self::parallel_find(parent, x);
        y = Self::parallel_find(parent, y);
        
        if x == y {
            return false;
        }
        
        if rank[x] < rank[y] {
            parent[x] = y;
        } else if rank[x] > rank[y] {
            parent[y] = x;
        } else {
            parent[y] = x;
            rank[x] += 1;
        }
        
        true
    }
    
    fn parallel_find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_parallel_quicksort() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5];
        let mut expected = arr.clone();
        expected.sort();
        
        ParallelSort::parallel_quicksort(&mut arr);
        assert_eq!(arr, expected);
    }
    
    #[test]
    fn test_parallel_binary_search() {
        let arr = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        
        assert_eq!(ParallelSearch::parallel_binary_search(&arr, &5), Some(4));
        assert_eq!(ParallelSearch::parallel_binary_search(&arr, &11), None);
    }
    
    #[test]
    fn test_parallel_bfs() {
        let neighbors = |node: usize| -> Vec<usize> {
            match node {
                0 => vec![1, 2],
                1 => vec![0, 3, 4],
                2 => vec![0, 5, 6],
                3 => vec![1],
                4 => vec![1],
                5 => vec![2],
                6 => vec![2],
                _ => vec![],
            }
        };
        
        let distances = ParallelGraph::parallel_bfs(0, neighbors, 7);
        assert_eq!(distances[0], 0);
        assert_eq!(distances[1], 1);
        assert_eq!(distances[2], 1);
        assert_eq!(distances[3], 2);
    }
}
