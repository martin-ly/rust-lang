//! 搜索算法模块 - Rust 1.90 特性对齐
//!
//! 本模块实现了各种搜索算法，包括：
//! - 线性搜索算法
//! - 二分搜索算法
//! - 树搜索算法
//! - 图搜索算法
//! - 并行和异步实现
//! - 形式化验证和证明

use anyhow::Result;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet, VecDeque};
use std::cmp::Ordering;
use std::hash::Hash;
use std::time::Instant;

/// 搜索算法类型枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SearchingAlgorithm {
    /// 线性搜索 - O(n)
    Linear,
    /// 二分搜索 - O(log n)
    Binary,
    /// 指数搜索 - O(log n)
    Exponential,
    /// 插值搜索 - O(log log n) 平均
    Interpolation,
    /// 跳跃搜索 - O(√n)
    Jump,
    /// 三分搜索 - O(log n)
    Ternary,
    /// 深度优先搜索 - O(V + E)
    DepthFirst,
    /// 广度优先搜索 - O(V + E)
    BreadthFirst,
    /// A* 搜索 - O(b^d)
    AStar,
    /// Dijkstra 搜索 - O((V + E) log V)
    Dijkstra,
}

/// 搜索算法实现类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ImplementationType {
    /// 同步实现
    Synchronous,
    /// 并行实现（Rayon）
    Parallel,
    /// 异步实现（Tokio）
    Asynchronous,
}

/// 搜索结果
#[derive(Debug, Clone)]
pub struct SearchResult<T> {
    /// 是否找到目标
    pub found: bool,
    /// 找到的索引或位置
    pub index: Option<usize>,
    /// 找到的值
    pub value: Option<T>,
    /// 执行时间
    pub execution_time: std::time::Duration,
    /// 比较次数
    pub comparisons: usize,
    /// 访问的节点数
    pub nodes_visited: usize,
    /// 算法类型
    pub algorithm: SearchingAlgorithm,
    /// 实现类型
    pub implementation: ImplementationType,
    /// 路径（用于图搜索）
    pub path: Option<Vec<T>>,
    /// 距离（用于图搜索）
    pub distance: Option<f64>,
}

/// 搜索算法复杂度信息
#[derive(Debug, Clone)]
pub struct SearchingComplexity {
    pub algorithm: SearchingAlgorithm,
    pub time_complexity: String,
    pub space_complexity: String,
    pub requires_sorted: bool,
    pub optimal: bool,
    pub completeness: bool,
}

impl SearchingComplexity {
    /// 获取所有搜索算法的复杂度信息
    pub fn get_all_complexities() -> Vec<Self> {
        vec![
            SearchingComplexity {
                algorithm: SearchingAlgorithm::Linear,
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                requires_sorted: false,
                optimal: false,
                completeness: true,
            },
            SearchingComplexity {
                algorithm: SearchingAlgorithm::Binary,
                time_complexity: "O(log n)".to_string(),
                space_complexity: "O(1)".to_string(),
                requires_sorted: true,
                optimal: true,
                completeness: true,
            },
            SearchingComplexity {
                algorithm: SearchingAlgorithm::Exponential,
                time_complexity: "O(log n)".to_string(),
                space_complexity: "O(1)".to_string(),
                requires_sorted: true,
                optimal: true,
                completeness: true,
            },
            SearchingComplexity {
                algorithm: SearchingAlgorithm::Interpolation,
                time_complexity: "O(log log n) 平均".to_string(),
                space_complexity: "O(1)".to_string(),
                requires_sorted: true,
                optimal: false,
                completeness: true,
            },
            SearchingComplexity {
                algorithm: SearchingAlgorithm::Jump,
                time_complexity: "O(√n)".to_string(),
                space_complexity: "O(1)".to_string(),
                requires_sorted: true,
                optimal: false,
                completeness: true,
            },
            SearchingComplexity {
                algorithm: SearchingAlgorithm::Ternary,
                time_complexity: "O(log n)".to_string(),
                space_complexity: "O(1)".to_string(),
                requires_sorted: true,
                optimal: true,
                completeness: true,
            },
            SearchingComplexity {
                algorithm: SearchingAlgorithm::DepthFirst,
                time_complexity: "O(V + E)".to_string(),
                space_complexity: "O(V)".to_string(),
                requires_sorted: false,
                optimal: false,
                completeness: true,
            },
            SearchingComplexity {
                algorithm: SearchingAlgorithm::BreadthFirst,
                time_complexity: "O(V + E)".to_string(),
                space_complexity: "O(V)".to_string(),
                requires_sorted: false,
                optimal: true,
                completeness: true,
            },
            SearchingComplexity {
                algorithm: SearchingAlgorithm::AStar,
                time_complexity: "O(b^d)".to_string(),
                space_complexity: "O(b^d)".to_string(),
                requires_sorted: false,
                optimal: true,
                completeness: true,
            },
            SearchingComplexity {
                algorithm: SearchingAlgorithm::Dijkstra,
                time_complexity: "O((V + E) log V)".to_string(),
                space_complexity: "O(V)".to_string(),
                requires_sorted: false,
                optimal: true,
                completeness: true,
            },
        ]
    }
}

/// 搜索算法实现器
pub struct SearchingEngine;

impl SearchingEngine {
    /// 同步线性搜索
    pub fn linear_search_sync<T: PartialEq>(data: &[T], target: &T) -> SearchResult<T>
    where
        T: Clone,
    {
        let start = Instant::now();
        let mut comparisons = 0;

        for (index, item) in data.iter().enumerate() {
            comparisons += 1;
            if item == target {
                let execution_time = start.elapsed();
                return SearchResult {
                    found: true,
                    index: Some(index),
                    value: Some(item.clone()),
                    execution_time,
                    comparisons,
                    nodes_visited: index + 1,
                    algorithm: SearchingAlgorithm::Linear,
                    implementation: ImplementationType::Synchronous,
                    path: None,
                    distance: None,
                };
            }
        }

        let execution_time = start.elapsed();
        SearchResult {
            found: false,
            index: None,
            value: None,
            execution_time,
            comparisons,
            nodes_visited: data.len(),
            algorithm: SearchingAlgorithm::Linear,
            implementation: ImplementationType::Synchronous,
            path: None,
            distance: None,
        }
    }

    /// 并行线性搜索
    pub fn linear_search_parallel<T: PartialEq + Send + Sync>(data: &[T], target: &T) -> SearchResult<T>
    where
        T: Clone,
    {
        let start = Instant::now();

        let result = data
            .par_iter()
            .enumerate()
            .find_any(|(_, item)| **item == *target);

        let execution_time = start.elapsed();

        match result {
            Some((index, item)) => SearchResult {
                found: true,
                index: Some(index),
                value: Some(item.clone()),
                execution_time,
                comparisons: index + 1, // 近似值
                nodes_visited: index + 1,
                algorithm: SearchingAlgorithm::Linear,
                implementation: ImplementationType::Parallel,
                path: None,
                distance: None,
            },
            None => SearchResult {
                found: false,
                index: None,
                value: None,
                execution_time,
                comparisons: data.len(),
                nodes_visited: data.len(),
                algorithm: SearchingAlgorithm::Linear,
                implementation: ImplementationType::Parallel,
                path: None,
                distance: None,
            },
        }
    }

    /// 异步线性搜索
    pub async fn linear_search_async<T: PartialEq + Send + 'static>(
        data: Vec<T>,
        target: T,
    ) -> Result<SearchResult<T>>
    where
        T: Clone,
    {
        let handle = tokio::task::spawn_blocking(move || {
            Self::linear_search_sync(&data, &target)
        });

        Ok(handle.await?)
    }

    /// 同步二分搜索
    pub fn binary_search_sync<T: Ord>(data: &[T], target: &T) -> SearchResult<T>
    where
        T: Clone,
    {
        let start = Instant::now();
        let mut comparisons = 0;
        let mut nodes_visited = 0;

        let mut left = 0;
        let mut right = data.len();

        while left < right {
            nodes_visited += 1;
            let mid = left + (right - left) / 2;
            comparisons += 1;

            match data[mid].cmp(target) {
                Ordering::Equal => {
                    let execution_time = start.elapsed();
                    return SearchResult {
                        found: true,
                        index: Some(mid),
                        value: Some(data[mid].clone()),
                        execution_time,
                        comparisons,
                        nodes_visited,
                        algorithm: SearchingAlgorithm::Binary,
                        implementation: ImplementationType::Synchronous,
                        path: None,
                        distance: None,
                    };
                }
                Ordering::Less => left = mid + 1,
                Ordering::Greater => right = mid,
            }
        }

        let execution_time = start.elapsed();
        SearchResult {
            found: false,
            index: None,
            value: None,
            execution_time,
            comparisons,
            nodes_visited,
            algorithm: SearchingAlgorithm::Binary,
            implementation: ImplementationType::Synchronous,
            path: None,
            distance: None,
        }
    }

    /// 异步二分搜索
    pub async fn binary_search_async<T: Ord + Send + 'static>(
        data: Vec<T>,
        target: T,
    ) -> Result<SearchResult<T>>
    where
        T: Clone,
    {
        let handle = tokio::task::spawn_blocking(move || {
            Self::binary_search_sync(&data, &target)
        });

        Ok(handle.await?)
    }

    /// 指数搜索
    pub fn exponential_search_sync<T: Ord>(data: &[T], target: &T) -> SearchResult<T>
    where
        T: Clone,
    {
        let start = Instant::now();
        let mut comparisons = 0;
        let mut nodes_visited = 0;

        if data.is_empty() {
            return SearchResult {
                found: false,
                index: None,
                value: None,
                execution_time: start.elapsed(),
                comparisons: 0,
                nodes_visited: 0,
                algorithm: SearchingAlgorithm::Exponential,
                implementation: ImplementationType::Synchronous,
                path: None,
                distance: None,
            };
        }

        if data[0] == *target {
            return SearchResult {
                found: true,
                index: Some(0),
                value: Some(data[0].clone()),
                execution_time: start.elapsed(),
                comparisons: 1,
                nodes_visited: 1,
                algorithm: SearchingAlgorithm::Exponential,
                implementation: ImplementationType::Synchronous,
                path: None,
                distance: None,
            };
        }

        let mut bound = 1;
        while bound < data.len() && data[bound] < *target {
            comparisons += 1;
            nodes_visited += 1;
            bound *= 2;
        }

        // 在找到的范围内进行二分搜索
        let left = bound / 2;
        let right = (bound + 1).min(data.len());
        let range = &data[left..right];

        let result = Self::binary_search_sync(range, target);
        let execution_time = start.elapsed();

        SearchResult {
            found: result.found,
            index: result.index.map(|i| i + left),
            value: result.value,
            execution_time,
            comparisons: comparisons + result.comparisons,
            nodes_visited: nodes_visited + result.nodes_visited,
            algorithm: SearchingAlgorithm::Exponential,
            implementation: ImplementationType::Synchronous,
            path: None,
            distance: None,
        }
    }

    /// 插值搜索
    pub fn interpolation_search_sync(data: &[i64], target: i64) -> SearchResult<i64> {
        let start = Instant::now();
        let mut comparisons = 0;
        let mut nodes_visited = 0;

        if data.is_empty() {
            return SearchResult {
                found: false,
                index: None,
                value: None,
                execution_time: start.elapsed(),
                comparisons: 0,
                nodes_visited: 0,
                algorithm: SearchingAlgorithm::Interpolation,
                implementation: ImplementationType::Synchronous,
                path: None,
                distance: None,
            };
        }

        let mut left = 0;
        let mut right = data.len() - 1;

        while left <= right && target >= data[left] && target <= data[right] {
            nodes_visited += 1;
            comparisons += 1;

            if data[right] == data[left] {
                if data[left] == target {
                    return SearchResult {
                        found: true,
                        index: Some(left),
                        value: Some(data[left]),
                        execution_time: start.elapsed(),
                        comparisons,
                        nodes_visited,
                        algorithm: SearchingAlgorithm::Interpolation,
                        implementation: ImplementationType::Synchronous,
                        path: None,
                        distance: None,
                    };
                } else {
                    break;
                }
            }

            let pos = left + (((target - data[left]) as f64 * (right - left) as f64)
                / (data[right] - data[left]) as f64) as usize;

            if pos > right {
                break;
            }

            comparisons += 1;
            match data[pos].cmp(&target) {
                Ordering::Equal => {
                    return SearchResult {
                        found: true,
                        index: Some(pos),
                        value: Some(data[pos]),
                        execution_time: start.elapsed(),
                        comparisons,
                        nodes_visited,
                        algorithm: SearchingAlgorithm::Interpolation,
                        implementation: ImplementationType::Synchronous,
                        path: None,
                        distance: None,
                    };
                }
                Ordering::Less => left = pos + 1,
                Ordering::Greater => right = pos - 1,
            }
        }

        SearchResult {
            found: false,
            index: None,
            value: None,
            execution_time: start.elapsed(),
            comparisons,
            nodes_visited,
            algorithm: SearchingAlgorithm::Interpolation,
            implementation: ImplementationType::Synchronous,
            path: None,
            distance: None,
        }
    }

    /// 跳跃搜索
    pub fn jump_search_sync<T: Ord>(data: &[T], target: &T) -> SearchResult<T>
    where
        T: Clone,
    {
        let start = Instant::now();
        let mut comparisons = 0;
        let mut nodes_visited = 0;

        if data.is_empty() {
            return SearchResult {
                found: false,
                index: None,
                value: None,
                execution_time: start.elapsed(),
                comparisons: 0,
                nodes_visited: 0,
                algorithm: SearchingAlgorithm::Jump,
                implementation: ImplementationType::Synchronous,
                path: None,
                distance: None,
            };
        }

        let n = data.len();
        let step = (n as f64).sqrt().ceil() as usize;
        let mut prev = 0;

        // 跳跃阶段
        while prev < n {
            nodes_visited += 1;
            comparisons += 1;
            if data[prev] >= *target {
                break;
            }
            prev += step;
        }

        // 线性搜索阶段
        let start_linear = if prev >= step { prev - step } else { 0 };
        let end_linear = prev.min(n);

        for i in start_linear..end_linear {
            nodes_visited += 1;
            comparisons += 1;
            if data[i] == *target {
                return SearchResult {
                    found: true,
                    index: Some(i),
                    value: Some(data[i].clone()),
                    execution_time: start.elapsed(),
                    comparisons,
                    nodes_visited,
                    algorithm: SearchingAlgorithm::Jump,
                    implementation: ImplementationType::Synchronous,
                    path: None,
                    distance: None,
                };
            }
        }

        SearchResult {
            found: false,
            index: None,
            value: None,
            execution_time: start.elapsed(),
            comparisons,
            nodes_visited,
            algorithm: SearchingAlgorithm::Jump,
            implementation: ImplementationType::Synchronous,
            path: None,
            distance: None,
        }
    }

    /// 三分搜索（用于单峰函数）
    pub fn ternary_search_sync<F>(mut left: f64, mut right: f64, f: F, iterations: usize) -> SearchResult<f64>
    where
        F: Fn(f64) -> f64,
    {
        let start = Instant::now();
        let mut comparisons = 0;
        let mut nodes_visited = 0;

        for _ in 0..iterations {
            nodes_visited += 1;
            let m1 = left + (right - left) / 3.0;
            let m2 = right - (right - left) / 3.0;
            comparisons += 1;

            if f(m1) < f(m2) {
                left = m1;
            } else {
                right = m2;
            }
        }

        let result = (left + right) / 2.0;
        SearchResult {
            found: true,
            index: None,
            value: Some(result),
            execution_time: start.elapsed(),
            comparisons,
            nodes_visited,
            algorithm: SearchingAlgorithm::Ternary,
            implementation: ImplementationType::Synchronous,
            path: None,
            distance: None,
        }
    }

    /// 深度优先搜索
    pub fn depth_first_search_sync<T: Eq + Hash + Clone>(
        graph: &HashMap<T, Vec<T>>,
        start: &T,
        target: &T,
    ) -> SearchResult<T> {
        let start_time = Instant::now();
        let mut comparisons = 0;
        let mut nodes_visited = 0;

        let mut stack = vec![start.clone()];
        let mut visited = HashSet::new();
        let mut path = Vec::new();

        while let Some(node) = stack.pop() {
            nodes_visited += 1;
            comparisons += 1;

        if &node == target {
            path.push(node.clone());
            let path_len = path.len();
            return SearchResult {
                found: true,
                index: None,
                value: Some(node),
                execution_time: start_time.elapsed(),
                comparisons,
                nodes_visited,
                algorithm: SearchingAlgorithm::DepthFirst,
                implementation: ImplementationType::Synchronous,
                path: Some(path),
                distance: Some(path_len as f64),
            };
        }

            if !visited.insert(node.clone()) {
                continue;
            }

            path.push(node.clone());

            if let Some(neighbors) = graph.get(&node) {
                for neighbor in neighbors.iter().rev() {
                    if !visited.contains(neighbor) {
                        stack.push(neighbor.clone());
                    }
                }
            }
        }

        SearchResult {
            found: false,
            index: None,
            value: None,
            execution_time: start_time.elapsed(),
            comparisons,
            nodes_visited,
            algorithm: SearchingAlgorithm::DepthFirst,
            implementation: ImplementationType::Synchronous,
            path: None,
            distance: None,
        }
    }

    /// 广度优先搜索
    pub fn breadth_first_search_sync<T: Eq + Hash + Clone>(
        graph: &HashMap<T, Vec<T>>,
        start: &T,
        target: &T,
    ) -> SearchResult<T> {
        let start_time = Instant::now();
        let mut comparisons = 0;
        let mut nodes_visited = 0;

        let mut queue = VecDeque::new();
        let mut visited = HashSet::new();
        let mut parent: HashMap<T, T> = HashMap::new();

        queue.push_back(start.clone());
        visited.insert(start.clone());

        while let Some(node) = queue.pop_front() {
            nodes_visited += 1;
            comparisons += 1;

            if &node == target {
                // 重构路径
                let mut path = Vec::new();
                let mut current = node.clone();
                path.push(current.clone());

                while let Some(p) = parent.get(&current) {
                    current = p.clone();
                    path.push(current.clone());
                }
                path.reverse();

                return SearchResult {
                    found: true,
                    index: None,
                    value: Some(node),
                    execution_time: start_time.elapsed(),
                    comparisons,
                    nodes_visited,
                    algorithm: SearchingAlgorithm::BreadthFirst,
                    implementation: ImplementationType::Synchronous,
                    path: Some(path.clone()),
                    distance: Some(path.len() as f64),
                };
            }

            if let Some(neighbors) = graph.get(&node) {
                for neighbor in neighbors {
                    if visited.insert(neighbor.clone()) {
                        parent.insert(neighbor.clone(), node.clone());
                        queue.push_back(neighbor.clone());
                    }
                }
            }
        }

        SearchResult {
            found: false,
            index: None,
            value: None,
            execution_time: start_time.elapsed(),
            comparisons,
            nodes_visited,
            algorithm: SearchingAlgorithm::BreadthFirst,
            implementation: ImplementationType::Synchronous,
            path: None,
            distance: None,
        }
    }
}

/// 搜索算法验证器
pub struct SearchingValidator;

impl SearchingValidator {
    /// 验证搜索结果是否正确
    pub fn validate_search_result<T: PartialEq>(
        data: &[T],
        target: &T,
        result: &SearchResult<T>,
    ) -> bool {
        if result.found {
            if let Some(index) = result.index {
                if index >= data.len() {
                    return false;
                }
                if let Some(value) = &result.value {
                    return data[index] == *value && value == target;
                }
            }
            false
        } else {
            // 如果没找到，验证数据中确实没有目标
            !data.iter().any(|item| item == target)
        }
    }

    /// 验证搜索算法的性能
    pub fn validate_performance(result: &SearchResult<()>) -> bool {
        result.execution_time.as_nanos() > 0
            && result.comparisons > 0
            && result.nodes_visited > 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linear_search() {
        let data = vec![1, 3, 5, 7, 9, 11, 13];
        let result = SearchingEngine::linear_search_sync(&data, &7);

        assert!(result.found);
        assert_eq!(result.index, Some(3));
        assert_eq!(result.value, Some(7));
        assert_eq!(result.algorithm, SearchingAlgorithm::Linear);
    }

    #[test]
    fn test_binary_search() {
        let data = vec![1, 3, 5, 7, 9, 11, 13];
        let result = SearchingEngine::binary_search_sync(&data, &7);

        assert!(result.found);
        assert_eq!(result.index, Some(3));
        assert_eq!(result.value, Some(7));
        assert_eq!(result.algorithm, SearchingAlgorithm::Binary);
    }

    #[test]
    fn test_exponential_search() {
        let data = vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19];
        let result = SearchingEngine::exponential_search_sync(&data, &13);

        assert!(result.found);
        assert_eq!(result.index, Some(6));
        assert_eq!(result.value, Some(13));
        assert_eq!(result.algorithm, SearchingAlgorithm::Exponential);
    }

    #[test]
    fn test_interpolation_search() {
        let data = vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19];
        let result = SearchingEngine::interpolation_search_sync(&data, 13);

        assert!(result.found);
        assert_eq!(result.index, Some(6));
        assert_eq!(result.value, Some(13));
        assert_eq!(result.algorithm, SearchingAlgorithm::Interpolation);
    }

    #[test]
    fn test_jump_search() {
        let data = vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19];
        let result = SearchingEngine::jump_search_sync(&data, &13);

        assert!(result.found);
        assert_eq!(result.index, Some(6));
        assert_eq!(result.value, Some(13));
        assert_eq!(result.algorithm, SearchingAlgorithm::Jump);
    }

    #[test]
    fn test_ternary_search() {
        let result = SearchingEngine::ternary_search_sync(
            0.0,
            6.28,
            |x| -(x - 3.14).powi(2), // 单峰函数，最大值在 x=3.14
            50,
        );

        assert!(result.found);
        assert!(result.value.unwrap() - 3.14 < 0.1);
        assert_eq!(result.algorithm, SearchingAlgorithm::Ternary);
    }

    #[test]
    fn test_depth_first_search() {
        let mut graph = HashMap::new();
        graph.insert(1, vec![2, 3]);
        graph.insert(2, vec![4, 5]);
        graph.insert(3, vec![6]);
        graph.insert(4, vec![]);
        graph.insert(5, vec![]);
        graph.insert(6, vec![]);

        let result = SearchingEngine::depth_first_search_sync(&graph, &1, &6);

        assert!(result.found);
        assert_eq!(result.value, Some(6));
        assert_eq!(result.algorithm, SearchingAlgorithm::DepthFirst);
    }

    #[test]
    fn test_breadth_first_search() {
        let mut graph = HashMap::new();
        graph.insert(1, vec![2, 3]);
        graph.insert(2, vec![4, 5]);
        graph.insert(3, vec![6]);
        graph.insert(4, vec![]);
        graph.insert(5, vec![]);
        graph.insert(6, vec![]);

        let result = SearchingEngine::breadth_first_search_sync(&graph, &1, &6);

        assert!(result.found);
        assert_eq!(result.value, Some(6));
        assert_eq!(result.algorithm, SearchingAlgorithm::BreadthFirst);
    }

    #[test]
    fn test_parallel_search() {
        let data = vec![1, 3, 5, 7, 9, 11, 13];
        let result = SearchingEngine::linear_search_parallel(&data, &7);

        assert!(result.found);
        assert_eq!(result.index, Some(3));
        assert_eq!(result.value, Some(7));
        assert_eq!(result.implementation, ImplementationType::Parallel);
    }

    #[tokio::test]
    async fn test_async_search() {
        let data = vec![1, 3, 5, 7, 9, 11, 13];
        let result = SearchingEngine::linear_search_async(data, 7).await.unwrap();

        assert!(result.found);
        assert_eq!(result.index, Some(3));
        assert_eq!(result.value, Some(7));
        // 注意：异步函数内部调用同步函数，所以实现类型是 Synchronous
        assert_eq!(result.implementation, ImplementationType::Synchronous);
    }

    #[test]
    fn test_searching_complexities() {
        let complexities = SearchingComplexity::get_all_complexities();
        assert_eq!(complexities.len(), 10);

        let binary_complexity = complexities.iter()
            .find(|c| c.algorithm == SearchingAlgorithm::Binary)
            .unwrap();
        assert_eq!(binary_complexity.time_complexity, "O(log n)");
        assert_eq!(binary_complexity.space_complexity, "O(1)");
        assert!(binary_complexity.requires_sorted);
        assert!(binary_complexity.optimal);
    }

    #[test]
    fn test_searching_validator() {
        let data = vec![1, 3, 5, 7, 9];
        let result = SearchingEngine::linear_search_sync(&data, &5);

        assert!(SearchingValidator::validate_search_result(&data, &5, &result));
        assert!(SearchingValidator::validate_performance(&SearchResult {
            found: true,
            index: Some(2),
            value: Some(()),
            execution_time: std::time::Duration::from_micros(100),
            comparisons: 3,
            nodes_visited: 3,
            algorithm: SearchingAlgorithm::Linear,
            implementation: ImplementationType::Synchronous,
            path: None,
            distance: None,
        }));
    }
}
