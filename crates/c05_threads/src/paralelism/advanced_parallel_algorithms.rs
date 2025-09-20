//! 高级并行算法实现
//!
//! 本模块提供了多种高级并行算法：
//! - 并行归并排序
//! - 并行快速排序
//! - 并行基数排序
//! - 并行图算法
//! - 并行数值计算

// use std::sync::{
//     Arc,
//     Mutex
// };

//use std::thread;
//use std::time::Duration;
use rayon::prelude::*;
// use crossbeam_channel::{
//     bounded,
//     unbounded,
// };

/// 并行归并排序
pub struct ParallelMergeSort;

impl ParallelMergeSort {
    /// 并行归并排序实现
    pub fn sort<T>(arr: &mut [T])
    where
        T: Ord + Send + Sync + Clone,
    {
        if arr.len() <= 1 {
            return;
        }

        let mid = arr.len() / 2;
        let (left, right) = arr.split_at_mut(mid);

        // 并行排序左右两部分
        rayon::join(|| Self::sort(left), || Self::sort(right));

        // 合并排序后的两部分
        Self::merge(arr, mid);
    }

    /// 合并两个已排序的数组
    fn merge<T>(arr: &mut [T], mid: usize)
    where
        T: Ord + Clone,
    {
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

    /// 运行归并排序示例
    pub fn run_example() {
        println!("=== 并行归并排序示例 ===");

        let mut arr = vec![64, 34, 25, 12, 22, 11, 90, 5, 77, 30];
        println!("排序前: {:?}", arr);

        let start = std::time::Instant::now();
        Self::sort(&mut arr);
        let duration = start.elapsed();

        println!("排序后: {:?}", arr);
        println!("排序耗时: {:?}", duration);
    }
}

/// 并行快速排序
pub struct ParallelQuickSort;

impl ParallelQuickSort {
    /// 并行快速排序实现
    pub fn sort<T>(arr: &mut [T])
    where
        T: Ord + Send + Sync + Clone,
    {
        if arr.len() <= 1 {
            return;
        }

        let pivot_index = Self::partition(arr);
        let (left, right) = arr.split_at_mut(pivot_index);

        // 并行排序左右两部分
        rayon::join(|| Self::sort(left), || Self::sort(&mut right[1..]));
    }

    /// 分区函数
    fn partition<T>(arr: &mut [T]) -> usize
    where
        T: Ord,
    {
        let len = arr.len();
        let pivot_index = len - 1;
        let mut i = 0;

        for j in 0..len - 1 {
            if arr[j] <= arr[pivot_index] {
                arr.swap(i, j);
                i += 1;
            }
        }

        arr.swap(i, pivot_index);
        i
    }

    /// 运行快速排序示例
    pub fn run_example() {
        println!("=== 并行快速排序示例 ===");

        let mut arr = vec![64, 34, 25, 12, 22, 11, 90, 5, 77, 30];
        println!("排序前: {:?}", arr);

        let start = std::time::Instant::now();
        Self::sort(&mut arr);
        let duration = start.elapsed();

        println!("排序后: {:?}", arr);
        println!("排序耗时: {:?}", duration);
    }
}

/// 并行基数排序
pub struct ParallelRadixSort;

impl ParallelRadixSort {
    /// 并行基数排序实现
    pub fn sort(arr: &mut [i32]) {
        if arr.is_empty() {
            return;
        }

        let max_val = *arr.iter().max().unwrap();
        let mut exp = 1;

        while max_val / exp > 0 {
            Self::counting_sort(arr, exp);
            exp *= 10;
        }
    }

    /// 计数排序
    fn counting_sort(arr: &mut [i32], exp: i32) {
        let n = arr.len();
        let mut output = vec![0; n];
        let mut count = [0; 10];

        // 统计每个数字的出现次数
        for &num in arr.iter() {
            count[((num / exp) % 10) as usize] += 1;
        }

        // 计算累积计数
        for i in 1..10 {
            count[i] += count[i - 1];
        }

        // 构建输出数组
        for &num in arr.iter().rev() {
            let index = ((num / exp) % 10) as usize;
            output[count[index] - 1] = num;
            count[index] -= 1;
        }

        // 复制回原数组
        arr.copy_from_slice(&output);
    }

    /// 运行基数排序示例
    pub fn run_example() {
        println!("=== 并行基数排序示例 ===");

        let mut arr = vec![170, 45, 75, 90, 2, 802, 24, 66];
        println!("排序前: {:?}", arr);

        let start = std::time::Instant::now();
        Self::sort(&mut arr);
        let duration = start.elapsed();

        println!("排序后: {:?}", arr);
        println!("排序耗时: {:?}", duration);
    }
}

/// 并行图算法
pub struct ParallelGraphAlgorithms;

impl ParallelGraphAlgorithms {
    /// 并行广度优先搜索
    pub fn parallel_bfs(graph: &[Vec<usize>], start: usize) -> Vec<usize> {
        let n = graph.len();
        let mut distances = vec![usize::MAX; n];
        let mut visited = vec![false; n];
        let mut queue = std::collections::VecDeque::new();

        distances[start] = 0;
        visited[start] = true;
        queue.push_back(start);

        while let Some(current) = queue.pop_front() {
            let current_distance = distances[current];

            // 并行处理当前节点的所有邻居
            let neighbors = &graph[current];
            let new_distances: Vec<_> = neighbors
                .par_iter()
                .map(|&neighbor| {
                    if !visited[neighbor] {
                        Some((neighbor, current_distance + 1))
                    } else {
                        None
                    }
                })
                .collect();

            // 更新距离和访问状态
            for (neighbor, distance) in new_distances.into_iter().flatten() {
                if !visited[neighbor] {
                    distances[neighbor] = distance;
                    visited[neighbor] = true;
                    queue.push_back(neighbor);
                }
            }
        }

        distances
    }

    /// 并行深度优先搜索
    pub fn parallel_dfs(graph: &[Vec<usize>], start: usize) -> Vec<bool> {
        let n = graph.len();
        let mut visited = vec![false; n];
        let mut stack = vec![start];

        while let Some(current) = stack.pop() {
            if !visited[current] {
                visited[current] = true;

                // 并行处理当前节点的所有邻居
                let neighbors = &graph[current];
                let unvisited_neighbors: Vec<_> = neighbors
                    .par_iter()
                    .filter(|&&neighbor| !visited[neighbor])
                    .copied()
                    .collect();

                stack.extend(unvisited_neighbors);
            }
        }

        visited
    }

    /// 运行图算法示例
    pub fn run_example() {
        println!("=== 并行图算法示例 ===");

        // 创建一个简单的图
        let graph = vec![
            vec![1, 2],    // 节点0连接到节点1和2
            vec![0, 3, 4], // 节点1连接到节点0, 3, 4
            vec![0, 5],    // 节点2连接到节点0, 5
            vec![1, 6],    // 节点3连接到节点1, 6
            vec![1, 7],    // 节点4连接到节点1, 7
            vec![2, 8],    // 节点5连接到节点2, 8
            vec![3, 9],    // 节点6连接到节点3, 9
            vec![4, 9],    // 节点7连接到节点4, 9
            vec![5, 9],    // 节点8连接到节点5, 9
            vec![6, 7, 8], // 节点9连接到节点6, 7, 8
        ];

        println!("图结构: {:?}", graph);

        // 并行BFS
        let start = std::time::Instant::now();
        let distances = Self::parallel_bfs(&graph, 0);
        let bfs_duration = start.elapsed();

        println!("从节点0开始的BFS距离: {:?}", distances);
        println!("BFS耗时: {:?}", bfs_duration);

        // 并行DFS
        let start = std::time::Instant::now();
        let visited = Self::parallel_dfs(&graph, 0);
        let dfs_duration = start.elapsed();

        println!("从节点0开始的DFS访问状态: {:?}", visited);
        println!("DFS耗时: {:?}", dfs_duration);
    }
}

/// 并行数值计算
pub struct ParallelNumericalComputing;

impl ParallelNumericalComputing {
    /// 并行矩阵乘法
    pub fn parallel_matrix_multiply(a: &[Vec<f64>], b: &[Vec<f64>]) -> Vec<Vec<f64>> {
        let rows = a.len();
        let cols = b[0].len();
        let common = a[0].len();

        let result: Vec<Vec<f64>> = (0..rows)
            .into_par_iter()
            .map(|i| {
                (0..cols)
                    .map(|j| (0..common).map(|k| a[i][k] * b[k][j]).sum())
                    .collect()
            })
            .collect();

        result
    }

    /// 并行向量点积
    pub fn parallel_dot_product(a: &[f64], b: &[f64]) -> f64 {
        a.par_iter().zip(b.par_iter()).map(|(x, y)| x * y).sum()
    }

    /// 并行向量范数计算
    pub fn parallel_vector_norm(v: &[f64]) -> f64 {
        v.par_iter().map(|x| x * x).sum::<f64>().sqrt()
    }

    /// 并行积分计算（梯形法则）
    pub fn parallel_integrate<F>(f: F, a: f64, b: f64, n: usize) -> f64
    where
        F: Fn(f64) -> f64 + Send + Sync,
    {
        let h = (b - a) / n as f64;

        let sum: f64 = (1..n)
            .into_par_iter()
            .map(|i| {
                let x = a + i as f64 * h;
                f(x)
            })
            .sum();

        h * (f(a) + f(b)) / 2.0 + h * sum
    }

    /// 运行数值计算示例
    pub fn run_example() {
        println!("=== 并行数值计算示例 ===");

        // 矩阵乘法示例
        let a = vec![vec![1.0, 2.0, 3.0], vec![4.0, 5.0, 6.0]];
        let b = vec![vec![7.0, 8.0], vec![9.0, 10.0], vec![11.0, 12.0]];

        let start = std::time::Instant::now();
        let result = Self::parallel_matrix_multiply(&a, &b);
        let duration = start.elapsed();

        println!("矩阵A: {:?}", a);
        println!("矩阵B: {:?}", b);
        println!("矩阵乘法结果: {:?}", result);
        println!("矩阵乘法耗时: {:?}", duration);

        // 向量点积示例
        let v1 = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let v2 = vec![2.0, 3.0, 4.0, 5.0, 6.0];

        let start = std::time::Instant::now();
        let dot_product = Self::parallel_dot_product(&v1, &v2);
        let duration = start.elapsed();

        println!("向量1: {:?}", v1);
        println!("向量2: {:?}", v2);
        println!("点积: {}", dot_product);
        println!("点积计算耗时: {:?}", duration);

        // 积分计算示例
        let start = std::time::Instant::now();
        let integral = Self::parallel_integrate(|x| x * x, 0.0, 1.0, 1000000);
        let duration = start.elapsed();

        println!("∫₀¹ x² dx = {}", integral);
        println!("积分计算耗时: {:?}", duration);
    }
}

/// 运行所有高级并行算法示例
pub fn demonstrate_advanced_parallel_algorithms() {
    println!("=== 高级并行算法演示 ===");

    ParallelMergeSort::run_example();
    ParallelQuickSort::run_example();
    ParallelRadixSort::run_example();
    ParallelGraphAlgorithms::run_example();
    ParallelNumericalComputing::run_example();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_merge_sort() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90, 5];
        let expected = vec![5, 11, 12, 22, 25, 34, 64, 90];

        ParallelMergeSort::sort(&mut arr);
        assert_eq!(arr, expected);
    }

    #[test]
    fn test_parallel_quick_sort() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90, 5];
        let expected = vec![5, 11, 12, 22, 25, 34, 64, 90];

        ParallelQuickSort::sort(&mut arr);
        assert_eq!(arr, expected);
    }

    #[test]
    fn test_parallel_radix_sort() {
        let mut arr = vec![170, 45, 75, 90, 2, 802, 24, 66];
        let expected = vec![2, 24, 45, 66, 75, 90, 170, 802];

        ParallelRadixSort::sort(&mut arr);
        assert_eq!(arr, expected);
    }

    #[test]
    fn test_parallel_dot_product() {
        let v1 = vec![1.0, 2.0, 3.0];
        let v2 = vec![4.0, 5.0, 6.0];
        let expected = 1.0 * 4.0 + 2.0 * 5.0 + 3.0 * 6.0;

        let result = ParallelNumericalComputing::parallel_dot_product(&v1, &v2);
        assert!((result - expected).abs() < 1e-10);
    }

    #[test]
    fn test_parallel_matrix_multiply() {
        let a = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
        let b = vec![vec![5.0, 6.0], vec![7.0, 8.0]];
        let expected = vec![vec![19.0, 22.0], vec![43.0, 50.0]];

        let result = ParallelNumericalComputing::parallel_matrix_multiply(&a, &b);
        assert_eq!(result, expected);
    }
}
