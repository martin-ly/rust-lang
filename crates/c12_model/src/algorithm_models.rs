//! 算法模型和各种算法模型的关系分析
//! 
//! 本模块实现了算法的分类、建模和关系分析，包括：
//! - 排序算法模型
//! - 搜索算法模型
//! - 图算法模型
//! - 动态规划模型
//! - 贪心算法模型
//! - 分治算法模型
//! - 算法复杂度分析
//! - 算法等价性分析
//! - 算法优化建议
//! 
//! 充分利用 Rust 1.90 的类型系统和性能特性

use std::collections::{HashMap, HashSet, VecDeque, BinaryHeap};
use std::cmp::{Ordering, Reverse};
use std::hash::Hash;
use std::time::{Duration, Instant};
use serde::{Deserialize, Serialize};
use crate::error::ModelError;

/// 算法模型结果类型
pub type AlgorithmResult<T> = Result<T, ModelError>;

/// 算法分类
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AlgorithmCategory {
    /// 排序算法
    Sorting,
    /// 搜索算法
    Searching,
    /// 图算法
    Graph,
    /// 动态规划
    DynamicProgramming,
    /// 贪心算法
    Greedy,
    /// 分治算法
    DivideAndConquer,
    /// 字符串算法
    String,
    /// 数学算法
    Mathematical,
    /// 几何算法
    Geometric,
    /// 网络流算法
    NetworkFlow,
    /// 机器学习算法
    MachineLearning,
}

/// 算法复杂度
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AlgorithmComplexity {
    /// 时间复杂度
    pub time_complexity: ComplexityClass,
    /// 空间复杂度
    pub space_complexity: ComplexityClass,
    /// 最好情况时间复杂度
    pub best_case_time: ComplexityClass,
    /// 最坏情况时间复杂度
    pub worst_case_time: ComplexityClass,
    /// 平均情况时间复杂度
    pub average_case_time: ComplexityClass,
}

/// 复杂度类别
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ComplexityClass {
    /// O(1) - 常数时间
    Constant,
    /// O(log n) - 对数时间
    Logarithmic,
    /// O(n) - 线性时间
    Linear,
    /// O(n log n) - 线性对数时间
    Linearithmic,
    /// O(n²) - 平方时间
    Quadratic,
    /// O(n³) - 立方时间
    Cubic,
    /// O(2^n) - 指数时间
    Exponential,
    /// O(n!) - 阶乘时间
    Factorial,
    /// 自定义复杂度
    Custom(String),
}

/// 算法特征
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlgorithmCharacteristics {
    /// 算法名称
    pub name: String,
    /// 算法分类
    pub category: AlgorithmCategory,
    /// 复杂度分析
    pub complexity: AlgorithmComplexity,
    /// 是否稳定
    pub is_stable: bool,
    /// 是否原地算法
    pub is_in_place: bool,
    /// 是否适应性算法
    pub is_adaptive: bool,
    /// 是否在线算法
    pub is_online: bool,
    /// 并行化潜力
    pub parallelization_potential: ParallelizationLevel,
    /// 内存访问模式
    pub memory_access_pattern: MemoryAccessPattern,
}

/// 并行化级别
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ParallelizationLevel {
    /// 不可并行化
    NotParallelizable,
    /// 部分并行化
    PartiallyParallelizable,
    /// 高度并行化
    HighlyParallelizable,
    /// 完全并行化
    FullyParallelizable,
}

/// 内存访问模式
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum MemoryAccessPattern {
    /// 顺序访问
    Sequential,
    /// 随机访问
    Random,
    /// 局部性访问
    Locality,
    /// 分块访问
    Blocked,
    /// 流式访问
    Streaming,
}

/// 算法性能指标
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AlgorithmMetrics {
    /// 执行时间
    pub execution_time: Duration,
    /// 内存使用峰值
    pub peak_memory_usage: usize,
    /// 比较次数
    pub comparison_count: u64,
    /// 交换次数
    pub swap_count: u64,
    /// 递归深度
    pub recursion_depth: usize,
    /// 缓存命中率
    pub cache_hit_rate: f64,
    /// 分支预测准确率
    pub branch_prediction_accuracy: f64,
}

impl AlgorithmMetrics {
    pub fn new() -> Self {
        Self::default()
    }
    
    pub fn record_comparison(&mut self) {
        self.comparison_count += 1;
    }
    
    pub fn record_swap(&mut self) {
        self.swap_count += 1;
    }
    
    pub fn set_execution_time(&mut self, duration: Duration) {
        self.execution_time = duration;
    }
    
    pub fn update_peak_memory(&mut self, memory_usage: usize) {
        self.peak_memory_usage = self.peak_memory_usage.max(memory_usage);
    }
}

/// 排序算法实现
#[derive(Debug)]
pub struct SortingAlgorithms;

impl SortingAlgorithms {
    /// 快速排序
    pub fn quicksort<T>(arr: &mut [T], metrics: &mut AlgorithmMetrics) -> AlgorithmResult<()>
    where
        T: PartialOrd + Clone,
    {
        let start_time = Instant::now();
        Self::quicksort_recursive(arr, 0, arr.len(), metrics, 0)?;
        metrics.set_execution_time(start_time.elapsed());
        Ok(())
    }
    
    fn quicksort_recursive<T>(
        arr: &mut [T],
        low: usize,
        high: usize,
        metrics: &mut AlgorithmMetrics,
        depth: usize,
    ) -> AlgorithmResult<()>
    where
        T: PartialOrd + Clone,
    {
        metrics.recursion_depth = metrics.recursion_depth.max(depth);
        
        if low < high && high > 0 {
            let pivot = Self::partition(arr, low, high - 1, metrics)?;
            
            if pivot > 0 {
                Self::quicksort_recursive(arr, low, pivot, metrics, depth + 1)?;
            }
            Self::quicksort_recursive(arr, pivot + 1, high, metrics, depth + 1)?;
        }
        Ok(())
    }
    
    fn partition<T>(arr: &mut [T], low: usize, high: usize, metrics: &mut AlgorithmMetrics) -> AlgorithmResult<usize>
    where
        T: PartialOrd + Clone,
    {
        let pivot_index = high;
        let mut i = low;
        
        for j in low..high {
            metrics.record_comparison();
            if arr[j] <= arr[pivot_index] {
                if i != j {
                    arr.swap(i, j);
                    metrics.record_swap();
                }
                i += 1;
            }
        }
        
        if i != pivot_index {
            arr.swap(i, pivot_index);
            metrics.record_swap();
        }
        
        Ok(i)
    }
    
    /// 归并排序
    pub fn mergesort<T>(arr: &mut [T], metrics: &mut AlgorithmMetrics) -> AlgorithmResult<()>
    where
        T: PartialOrd + Clone,
    {
        let start_time = Instant::now();
        let mut temp = vec![arr[0].clone(); arr.len()];
        Self::mergesort_recursive(arr, &mut temp, 0, arr.len(), metrics, 0)?;
        metrics.set_execution_time(start_time.elapsed());
        Ok(())
    }
    
    fn mergesort_recursive<T>(
        arr: &mut [T],
        temp: &mut [T],
        low: usize,
        high: usize,
        metrics: &mut AlgorithmMetrics,
        depth: usize,
    ) -> AlgorithmResult<()>
    where
        T: PartialOrd + Clone,
    {
        metrics.recursion_depth = metrics.recursion_depth.max(depth);
        
        if high - low > 1 {
            let mid = (low + high) / 2;
            Self::mergesort_recursive(arr, temp, low, mid, metrics, depth + 1)?;
            Self::mergesort_recursive(arr, temp, mid, high, metrics, depth + 1)?;
            Self::merge(arr, temp, low, mid, high, metrics)?;
        }
        Ok(())
    }
    
    fn merge<T>(
        arr: &mut [T],
        temp: &mut [T],
        low: usize,
        mid: usize,
        high: usize,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<()>
    where
        T: PartialOrd + Clone,
    {
        // 复制到临时数组
        for i in low..high {
            temp[i] = arr[i].clone();
        }
        
        let mut i = low;
        let mut j = mid;
        let mut k = low;
        
        // 合并
        while i < mid && j < high {
            metrics.record_comparison();
            if temp[i] <= temp[j] {
                arr[k] = temp[i].clone();
                i += 1;
            } else {
                arr[k] = temp[j].clone();
                j += 1;
            }
            k += 1;
        }
        
        // 复制剩余元素
        while i < mid {
            arr[k] = temp[i].clone();
            i += 1;
            k += 1;
        }
        
        while j < high {
            arr[k] = temp[j].clone();
            j += 1;
            k += 1;
        }
        
        Ok(())
    }
    
    /// 堆排序
    pub fn heapsort<T>(arr: &mut [T], metrics: &mut AlgorithmMetrics) -> AlgorithmResult<()>
    where
        T: PartialOrd + Clone,
    {
        let start_time = Instant::now();
        let n = arr.len();
        
        // 构建最大堆
        for i in (0..n / 2).rev() {
            Self::heapify(arr, n, i, metrics)?;
        }
        
        // 逐个提取元素
        for i in (1..n).rev() {
            arr.swap(0, i);
            metrics.record_swap();
            Self::heapify(arr, i, 0, metrics)?;
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(())
    }
    
    fn heapify<T>(arr: &mut [T], n: usize, i: usize, metrics: &mut AlgorithmMetrics) -> AlgorithmResult<()>
    where
        T: PartialOrd + Clone,
    {
        let mut largest = i;
        let left = 2 * i + 1;
        let right = 2 * i + 2;
        
        if left < n {
            metrics.record_comparison();
            if arr[left] > arr[largest] {
                largest = left;
            }
        }
        
        if right < n {
            metrics.record_comparison();
            if arr[right] > arr[largest] {
                largest = right;
            }
        }
        
        if largest != i {
            arr.swap(i, largest);
            metrics.record_swap();
            Self::heapify(arr, n, largest, metrics)?;
        }
        
        Ok(())
    }
    
    /// 获取快速排序特征
    pub fn quicksort_characteristics() -> AlgorithmCharacteristics {
        AlgorithmCharacteristics {
            name: "Quick Sort".to_string(),
            category: AlgorithmCategory::Sorting,
            complexity: AlgorithmComplexity {
                time_complexity: ComplexityClass::Linearithmic,
                space_complexity: ComplexityClass::Logarithmic,
                best_case_time: ComplexityClass::Linearithmic,
                worst_case_time: ComplexityClass::Quadratic,
                average_case_time: ComplexityClass::Linearithmic,
            },
            is_stable: false,
            is_in_place: true,
            is_adaptive: false,
            is_online: false,
            parallelization_potential: ParallelizationLevel::HighlyParallelizable,
            memory_access_pattern: MemoryAccessPattern::Random,
        }
    }
    
    /// 获取归并排序特征
    pub fn mergesort_characteristics() -> AlgorithmCharacteristics {
        AlgorithmCharacteristics {
            name: "Merge Sort".to_string(),
            category: AlgorithmCategory::Sorting,
            complexity: AlgorithmComplexity {
                time_complexity: ComplexityClass::Linearithmic,
                space_complexity: ComplexityClass::Linear,
                best_case_time: ComplexityClass::Linearithmic,
                worst_case_time: ComplexityClass::Linearithmic,
                average_case_time: ComplexityClass::Linearithmic,
            },
            is_stable: true,
            is_in_place: false,
            is_adaptive: false,
            is_online: false,
            parallelization_potential: ParallelizationLevel::HighlyParallelizable,
            memory_access_pattern: MemoryAccessPattern::Sequential,
        }
    }
}

/// 搜索算法实现
#[derive(Debug)]
pub struct SearchingAlgorithms;

impl SearchingAlgorithms {
    /// 二分搜索
    pub fn binary_search<T>(arr: &[T], target: &T, metrics: &mut AlgorithmMetrics) -> AlgorithmResult<Option<usize>>
    where
        T: PartialOrd,
    {
        let start_time = Instant::now();
        let mut left = 0;
        let mut right = arr.len();
        
        while left < right {
            let mid = left + (right - left) / 2;
            metrics.record_comparison();
            
            match arr[mid].partial_cmp(target) {
                Some(Ordering::Equal) => {
                    metrics.set_execution_time(start_time.elapsed());
                    return Ok(Some(mid));
                }
                Some(Ordering::Less) => left = mid + 1,
                Some(Ordering::Greater) => right = mid,
                None => return Err(ModelError::ComparisonError("Cannot compare values".to_string())),
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(None)
    }
    
    /// 线性搜索
    pub fn linear_search<T>(arr: &[T], target: &T, metrics: &mut AlgorithmMetrics) -> AlgorithmResult<Option<usize>>
    where
        T: PartialEq,
    {
        let start_time = Instant::now();
        
        for (i, item) in arr.iter().enumerate() {
            metrics.record_comparison();
            if item == target {
                metrics.set_execution_time(start_time.elapsed());
                return Ok(Some(i));
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(None)
    }
    
    /// 深度优先搜索
    pub fn depth_first_search<T>(
        graph: &HashMap<T, Vec<T>>,
        start: &T,
        target: &T,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<Option<Vec<T>>>
    where
        T: Clone + Eq + Hash,
    {
        let start_time = Instant::now();
        let mut visited = HashSet::new();
        let mut path = Vec::new();
        
        let result = Self::dfs_recursive(graph, start, target, &mut visited, &mut path, metrics, 0)?;
        metrics.set_execution_time(start_time.elapsed());
        
        if result {
            Ok(Some(path))
        } else {
            Ok(None)
        }
    }
    
    fn dfs_recursive<T>(
        graph: &HashMap<T, Vec<T>>,
        current: &T,
        target: &T,
        visited: &mut HashSet<T>,
        path: &mut Vec<T>,
        metrics: &mut AlgorithmMetrics,
        depth: usize,
    ) -> AlgorithmResult<bool>
    where
        T: Clone + Eq + Hash,
    {
        metrics.recursion_depth = metrics.recursion_depth.max(depth);
        visited.insert(current.clone());
        path.push(current.clone());
        
        metrics.record_comparison();
        if current == target {
            return Ok(true);
        }
        
        if let Some(neighbors) = graph.get(current) {
            for neighbor in neighbors {
                if !visited.contains(neighbor) {
                    if Self::dfs_recursive(graph, neighbor, target, visited, path, metrics, depth + 1)? {
                        return Ok(true);
                    }
                }
            }
        }
        
        path.pop();
        Ok(false)
    }
    
    /// 广度优先搜索
    pub fn breadth_first_search<T>(
        graph: &HashMap<T, Vec<T>>,
        start: &T,
        target: &T,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<Option<Vec<T>>>
    where
        T: Clone + Eq + Hash,
    {
        let start_time = Instant::now();
        let mut visited: HashSet<T> = HashSet::new();
        let mut queue: VecDeque<T> = VecDeque::new();
        let mut parent: HashMap<T, T> = HashMap::new();
        
        queue.push_back(start.clone());
        visited.insert(start.clone());
        
        while let Some(current) = queue.pop_front() {
            metrics.record_comparison();
            if current == *target {
                // 重构路径
                let mut path = Vec::new();
                let mut node = target.clone();
                
                while let Some(p) = parent.get(&node) {
                    path.push(node.clone());
                    node = p.clone();
                }
                path.push(start.clone());
                path.reverse();
                
                metrics.set_execution_time(start_time.elapsed());
                return Ok(Some(path));
            }
            
            if let Some(neighbors) = graph.get(&current) {
                for neighbor in neighbors {
                    if !visited.contains(neighbor) {
                        visited.insert(neighbor.clone());
                        parent.insert(neighbor.clone(), current.clone());
                        queue.push_back(neighbor.clone());
                    }
                }
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(None)
    }
}

/// 动态规划算法实现
#[derive(Debug)]
pub struct DynamicProgrammingAlgorithms;

impl DynamicProgrammingAlgorithms {
    /// 斐波那契数列（动态规划）
    pub fn fibonacci_dp(n: usize, metrics: &mut AlgorithmMetrics) -> AlgorithmResult<u64> {
        let start_time = Instant::now();
        
        if n <= 1 {
            metrics.set_execution_time(start_time.elapsed());
            return Ok(n as u64);
        }
        
        let mut dp = vec![0u64; n + 1];
        dp[0] = 0;
        dp[1] = 1;
        
        for i in 2..=n {
            dp[i] = dp[i - 1] + dp[i - 2];
            metrics.record_comparison();
        }
        
        metrics.set_execution_time(start_time.elapsed());
        metrics.update_peak_memory(dp.len() * std::mem::size_of::<u64>());
        Ok(dp[n])
    }
    
    /// 最长公共子序列
    pub fn longest_common_subsequence(
        text1: &str,
        text2: &str,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<usize> {
        let start_time = Instant::now();
        let chars1: Vec<char> = text1.chars().collect();
        let chars2: Vec<char> = text2.chars().collect();
        let m = chars1.len();
        let n = chars2.len();
        
        let mut dp = vec![vec![0; n + 1]; m + 1];
        
        for i in 1..=m {
            for j in 1..=n {
                metrics.record_comparison();
                if chars1[i - 1] == chars2[j - 1] {
                    dp[i][j] = dp[i - 1][j - 1] + 1;
                } else {
                    dp[i][j] = dp[i - 1][j].max(dp[i][j - 1]);
                }
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        metrics.update_peak_memory((m + 1) * (n + 1) * std::mem::size_of::<usize>());
        Ok(dp[m][n])
    }
    
    /// 0-1背包问题
    pub fn knapsack_01(
        weights: &[usize],
        values: &[usize],
        capacity: usize,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<usize> {
        let start_time = Instant::now();
        let n = weights.len();
        let mut dp = vec![vec![0; capacity + 1]; n + 1];
        
        for i in 1..=n {
            for w in 1..=capacity {
                metrics.record_comparison();
                if weights[i - 1] <= w {
                    dp[i][w] = dp[i - 1][w].max(
                        dp[i - 1][w - weights[i - 1]] + values[i - 1]
                    );
                } else {
                    dp[i][w] = dp[i - 1][w];
                }
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        metrics.update_peak_memory((n + 1) * (capacity + 1) * std::mem::size_of::<usize>());
        Ok(dp[n][capacity])
    }
    
    /// 编辑距离
    pub fn edit_distance(
        str1: &str,
        str2: &str,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<usize> {
        let start_time = Instant::now();
        let chars1: Vec<char> = str1.chars().collect();
        let chars2: Vec<char> = str2.chars().collect();
        let m = chars1.len();
        let n = chars2.len();
        
        let mut dp = vec![vec![0; n + 1]; m + 1];
        
        // 初始化边界条件
        for i in 0..=m {
            dp[i][0] = i;
        }
        for j in 0..=n {
            dp[0][j] = j;
        }
        
        for i in 1..=m {
            for j in 1..=n {
                metrics.record_comparison();
                if chars1[i - 1] == chars2[j - 1] {
                    dp[i][j] = dp[i - 1][j - 1];
                } else {
                    dp[i][j] = 1 + dp[i - 1][j].min(dp[i][j - 1]).min(dp[i - 1][j - 1]);
                }
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        metrics.update_peak_memory((m + 1) * (n + 1) * std::mem::size_of::<usize>());
        Ok(dp[m][n])
    }
}

/// 排序的距离（用于Dijkstra算法的优先队列）
#[derive(Debug, Clone, Copy, PartialEq)]
struct OrdF64(f64);

impl Eq for OrdF64 {}

impl PartialOrd for OrdF64 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for OrdF64 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.partial_cmp(&other.0).unwrap_or(std::cmp::Ordering::Equal)
    }
}

/// 贪心算法实现
#[derive(Debug)]
pub struct GreedyAlgorithms;

impl GreedyAlgorithms {
    /// 活动选择问题
    pub fn activity_selection(
        activities: &[(usize, usize)], // (start_time, end_time)
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<Vec<usize>> {
        let start_time = Instant::now();
        let mut sorted_activities: Vec<(usize, usize, usize)> = activities
            .iter()
            .enumerate()
            .map(|(i, &(start, end))| (start, end, i))
            .collect();
        
        // 按结束时间排序
        sorted_activities.sort_by_key(|&(_, end, _)| end);
        
        let mut selected = Vec::new();
        let mut last_end_time = 0;
        
        for &(start, end, index) in &sorted_activities {
            metrics.record_comparison();
            if start >= last_end_time {
                selected.push(index);
                last_end_time = end;
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(selected)
    }
    
    /// 分数背包问题
    pub fn fractional_knapsack(
        items: &[(f64, f64)], // (weight, value)
        capacity: f64,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<f64> {
        let start_time = Instant::now();
        let mut sorted_items: Vec<(f64, f64, f64)> = items
            .iter()
            .map(|&(weight, value)| (weight, value, value / weight))
            .collect();
        
        // 按价值密度排序
        sorted_items.sort_by(|a, b| b.2.partial_cmp(&a.2).unwrap_or(Ordering::Equal));
        
        let mut total_value = 0.0;
        let mut remaining_capacity = capacity;
        
        for &(weight, value, _) in &sorted_items {
            metrics.record_comparison();
            if remaining_capacity >= weight {
                total_value += value;
                remaining_capacity -= weight;
            } else if remaining_capacity > 0.0 {
                total_value += value * (remaining_capacity / weight);
                break;
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(total_value)
    }
    
    /// Dijkstra最短路径算法
    pub fn dijkstra_shortest_path<T>(
        graph: &HashMap<T, Vec<(T, f64)>>, // 邻接表，(neighbor, weight)
        start: &T,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<HashMap<T, f64>>
    where
        T: Clone + Eq + Hash + Ord,
    {
        let start_time = Instant::now();
        let mut distances: HashMap<T, f64> = HashMap::new();
        let mut heap: BinaryHeap<Reverse<(OrdF64, T)>> = BinaryHeap::new();
        let mut visited = HashSet::new();
        
        distances.insert(start.clone(), 0.0);
        heap.push(Reverse((OrdF64(0.0), start.clone())));
        
        while let Some(Reverse((OrdF64(current_dist), current_node))) = heap.pop() {
            if visited.contains(&current_node) {
                continue;
            }
            
            visited.insert(current_node.clone());
            
            if let Some(neighbors) = graph.get(&current_node) {
                for (neighbor, weight) in neighbors {
                    metrics.record_comparison();
                    let new_dist = current_dist + weight;
                    
                    if !distances.contains_key(neighbor) || new_dist < distances[neighbor] {
                        distances.insert(neighbor.clone(), new_dist);
                        heap.push(Reverse((OrdF64(new_dist), neighbor.clone())));
                    }
                }
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(distances)
    }
    
    /// Floyd-Warshall全源最短路径算法
    /// 
    /// 计算所有顶点对之间的最短路径
    /// 时间复杂度: O(V³)
    /// 空间复杂度: O(V²)
    pub fn floyd_warshall<T>(
        vertices: &[T],
        edges: &[(T, T, f64)], // (from, to, weight)
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<HashMap<(T, T), f64>>
    where
        T: Clone + Eq + Hash,
    {
        let start_time = Instant::now();
        let mut dist: HashMap<(T, T), f64> = HashMap::new();
        
        // 初始化距离矩阵
        for v1 in vertices {
            for v2 in vertices {
                if v1 == v2 {
                    dist.insert((v1.clone(), v2.clone()), 0.0);
                } else {
                    dist.insert((v1.clone(), v2.clone()), f64::INFINITY);
                }
            }
        }
        
        // 设置边的权重
        for (from, to, weight) in edges {
            dist.insert((from.clone(), to.clone()), *weight);
        }
        
        // Floyd-Warshall核心算法
        for k in vertices {
            for i in vertices {
                for j in vertices {
                    metrics.record_comparison();
                    let ik = dist.get(&(i.clone(), k.clone())).copied().unwrap_or(f64::INFINITY);
                    let kj = dist.get(&(k.clone(), j.clone())).copied().unwrap_or(f64::INFINITY);
                    let ij = dist.get(&(i.clone(), j.clone())).copied().unwrap_or(f64::INFINITY);
                    
                    if ik + kj < ij {
                        dist.insert((i.clone(), j.clone()), ik + kj);
                    }
                }
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(dist)
    }
    
    /// Bellman-Ford最短路径算法（支持负权边）
    /// 
    /// 时间复杂度: O(VE)
    /// 空间复杂度: O(V)
    pub fn bellman_ford<T>(
        vertices: &[T],
        edges: &[(T, T, f64)],
        start: &T,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<HashMap<T, f64>>
    where
        T: Clone + Eq + Hash,
    {
        let start_time = Instant::now();
        let mut distances: HashMap<T, f64> = HashMap::new();
        
        // 初始化距离
        for v in vertices {
            distances.insert(v.clone(), f64::INFINITY);
        }
        distances.insert(start.clone(), 0.0);
        
        // 松弛边 |V| - 1 次
        for _ in 0..vertices.len() - 1 {
            for (from, to, weight) in edges {
                metrics.record_comparison();
                let dist_from = distances.get(from).copied().unwrap_or(f64::INFINITY);
                let dist_to = distances.get(to).copied().unwrap_or(f64::INFINITY);
                
                if dist_from + weight < dist_to {
                    distances.insert(to.clone(), dist_from + weight);
                }
            }
        }
        
        // 检测负权环
        for (from, to, weight) in edges {
            let dist_from = distances.get(from).copied().unwrap_or(f64::INFINITY);
            let dist_to = distances.get(to).copied().unwrap_or(f64::INFINITY);
            
            if dist_from + weight < dist_to {
                return Err(ModelError::ComputationError(
                    "图中存在负权环".to_string()
                ));
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(distances)
    }
    
    /// Kruskal最小生成树算法
    /// 
    /// 时间复杂度: O(E log E)
    /// 空间复杂度: O(V + E)
    pub fn kruskal<T>(
        vertices: &[T],
        edges: &[(T, T, f64)],
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<Vec<(T, T, f64)>>
    where
        T: Clone + Eq + Hash,
    {
        let start_time = Instant::now();
        let mut result = Vec::new();
        let mut parent: HashMap<T, T> = HashMap::new();
        let mut rank: HashMap<T, usize> = HashMap::new();
        
        // 初始化并查集
        for v in vertices {
            parent.insert(v.clone(), v.clone());
            rank.insert(v.clone(), 0);
        }
        
        // 按权重排序边
        let mut sorted_edges = edges.to_vec();
        sorted_edges.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(Ordering::Equal));
        
        // 查找根节点
        fn find<T: Clone + Eq + Hash>(parent: &mut HashMap<T, T>, x: &T) -> T {
            let parent_x = parent.get(x).cloned().unwrap();
            if parent_x != *x {
                let root = find(parent, &parent_x);
                parent.insert(x.clone(), root.clone());
                root
            } else {
                x.clone()
            }
        }
        
        // 合并集合
        fn union<T: Clone + Eq + Hash>(
            parent: &mut HashMap<T, T>,
            rank: &mut HashMap<T, usize>,
            x: &T,
            y: &T,
        ) {
            let root_x = find(parent, x);
            let root_y = find(parent, y);
            
            if root_x != root_y {
                let rank_x = rank.get(&root_x).copied().unwrap_or(0);
                let rank_y = rank.get(&root_y).copied().unwrap_or(0);
                
                if rank_x < rank_y {
                    parent.insert(root_x, root_y);
                } else if rank_x > rank_y {
                    parent.insert(root_y, root_x);
                } else {
                    parent.insert(root_y, root_x.clone());
                    rank.insert(root_x, rank_x + 1);
                }
            }
        }
        
        // 贪心选择边
        for (from, to, weight) in sorted_edges {
            metrics.record_comparison();
            let root_from = find(&mut parent, &from);
            let root_to = find(&mut parent, &to);
            
            if root_from != root_to {
                result.push((from.clone(), to.clone(), weight));
                union(&mut parent, &mut rank, &from, &to);
                
                if result.len() == vertices.len() - 1 {
                    break;
                }
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(result)
    }
    
    /// Prim最小生成树算法
    /// 
    /// 时间复杂度: O(E log V)
    /// 空间复杂度: O(V + E)
    pub fn prim<T>(
        graph: &HashMap<T, Vec<(T, f64)>>,
        start: &T,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<Vec<(T, T, f64)>>
    where
        T: Clone + Eq + Hash + Ord,
    {
        let start_time = Instant::now();
        let mut result = Vec::new();
        let mut visited = HashSet::new();
        let mut heap: BinaryHeap<Reverse<(OrdF64, T, T)>> = BinaryHeap::new(); // (weight, from, to)
        
        visited.insert(start.clone());
        
        // 将起始顶点的所有边加入堆
        if let Some(neighbors) = graph.get(start) {
            for (neighbor, weight) in neighbors {
                heap.push(Reverse((OrdF64(*weight), start.clone(), neighbor.clone())));
            }
        }
        
        while let Some(Reverse((OrdF64(weight), from, to))) = heap.pop() {
            if visited.contains(&to) {
                continue;
            }
            
            metrics.record_comparison();
            visited.insert(to.clone());
            result.push((from.clone(), to.clone(), weight));
            
            // 将新顶点的边加入堆
            if let Some(neighbors) = graph.get(&to) {
                for (neighbor, w) in neighbors {
                    if !visited.contains(neighbor) {
                        heap.push(Reverse((OrdF64(*w), to.clone(), neighbor.clone())));
                    }
                }
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(result)
    }
    
    /// 拓扑排序（Kahn算法）
    /// 
    /// 时间复杂度: O(V + E)
    /// 空间复杂度: O(V)
    pub fn topological_sort<T>(
        graph: &HashMap<T, Vec<T>>,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<Vec<T>>
    where
        T: Clone + Eq + Hash,
    {
        let start_time = Instant::now();
        let mut in_degree: HashMap<T, usize> = HashMap::new();
        let mut result = Vec::new();
        let mut queue = VecDeque::new();
        
        // 计算所有顶点的入度
        for (vertex, neighbors) in graph {
            in_degree.entry(vertex.clone()).or_insert(0);
            for neighbor in neighbors {
                *in_degree.entry(neighbor.clone()).or_insert(0) += 1;
            }
        }
        
        // 将所有入度为0的顶点加入队列
        for (vertex, &degree) in &in_degree {
            if degree == 0 {
                queue.push_back(vertex.clone());
            }
        }
        
        // Kahn算法
        while let Some(vertex) = queue.pop_front() {
            metrics.record_comparison();
            result.push(vertex.clone());
            
            if let Some(neighbors) = graph.get(&vertex) {
                for neighbor in neighbors {
                    if let Some(degree) = in_degree.get_mut(neighbor) {
                        *degree -= 1;
                        if *degree == 0 {
                            queue.push_back(neighbor.clone());
                        }
                    }
                }
            }
        }
        
        // 检测环
        if result.len() != in_degree.len() {
            return Err(ModelError::ComputationError(
                "图中存在环，无法进行拓扑排序".to_string()
            ));
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(result)
    }
}

/// 字符串算法实现
#[derive(Debug)]
pub struct StringAlgorithms;

impl StringAlgorithms {
    /// KMP模式匹配算法
    /// 
    /// 时间复杂度: O(m + n) 其中m是模式串长度，n是文本串长度
    /// 空间复杂度: O(m)
    pub fn kmp_search(
        text: &str,
        pattern: &str,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<Vec<usize>> {
        let start_time = Instant::now();
        let mut result = Vec::new();
        
        if pattern.is_empty() {
            return Ok(result);
        }
        
        let text_chars: Vec<char> = text.chars().collect();
        let pattern_chars: Vec<char> = pattern.chars().collect();
        let m = pattern_chars.len();
        let n = text_chars.len();
        
        // 构建部分匹配表（前缀函数）
        let mut lps = vec![0; m];
        let mut len = 0;
        let mut i = 1;
        
        while i < m {
            metrics.record_comparison();
            if pattern_chars[i] == pattern_chars[len] {
                len += 1;
                lps[i] = len;
                i += 1;
            } else {
                if len != 0 {
                    len = lps[len - 1];
                } else {
                    lps[i] = 0;
                    i += 1;
                }
            }
        }
        
        // KMP搜索
        let mut j = 0; // pattern的索引
        i = 0; // text的索引
        
        while i < n {
            metrics.record_comparison();
            if pattern_chars[j] == text_chars[i] {
                i += 1;
                j += 1;
            }
            
            if j == m {
                result.push(i - j);
                j = lps[j - 1];
            } else if i < n && pattern_chars[j] != text_chars[i] {
                if j != 0 {
                    j = lps[j - 1];
                } else {
                    i += 1;
                }
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(result)
    }
    
    /// Boyer-Moore算法
    /// 
    /// 时间复杂度: O(n/m) 最好情况，O(mn) 最坏情况
    /// 空间复杂度: O(k) k是字符集大小
    pub fn boyer_moore_search(
        text: &str,
        pattern: &str,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<Vec<usize>> {
        let start_time = Instant::now();
        let mut result = Vec::new();
        
        if pattern.is_empty() {
            return Ok(result);
        }
        
        let text_chars: Vec<char> = text.chars().collect();
        let pattern_chars: Vec<char> = pattern.chars().collect();
        let m = pattern_chars.len();
        let n = text_chars.len();
        
        if m > n {
            return Ok(result);
        }
        
        // 构建坏字符表
        let mut bad_char: HashMap<char, isize> = HashMap::new();
        for (i, &ch) in pattern_chars.iter().enumerate() {
            bad_char.insert(ch, i as isize);
        }
        
        let mut s = 0; // 文本中的偏移量
        
        while s <= n - m {
            let mut j = (m - 1) as isize;
            
            while j >= 0 && pattern_chars[j as usize] == text_chars[s + j as usize] {
                metrics.record_comparison();
                j -= 1;
            }
            
            if j < 0 {
                result.push(s);
                s += if s + m < n {
                    m - bad_char.get(&text_chars[s + m]).copied().unwrap_or(-1) as usize - 1
                } else {
                    1
                };
            } else {
                metrics.record_comparison();
                let bad_char_shift = j - bad_char.get(&text_chars[s + j as usize]).copied().unwrap_or(-1);
                s += bad_char_shift.max(1) as usize;
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(result)
    }
    
    /// Rabin-Karp算法（滚动哈希）
    /// 
    /// 时间复杂度: O(m + n) 平均情况
    /// 空间复杂度: O(1)
    pub fn rabin_karp_search(
        text: &str,
        pattern: &str,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<Vec<usize>> {
        let start_time = Instant::now();
        let mut result = Vec::new();
        
        if pattern.is_empty() || pattern.len() > text.len() {
            return Ok(result);
        }
        
        const BASE: u64 = 256;
        const MOD: u64 = 101;
        
        let text_bytes = text.as_bytes();
        let pattern_bytes = pattern.as_bytes();
        let m = pattern.len();
        let n = text.len();
        
        // 计算 BASE^(m-1) % MOD
        let mut h: u64 = 1;
        for _ in 0..m - 1 {
            h = (h * BASE) % MOD;
        }
        
        // 计算模式串和第一个窗口的哈希值
        let mut pattern_hash: u64 = 0;
        let mut text_hash: u64 = 0;
        
        for i in 0..m {
            pattern_hash = (BASE * pattern_hash + pattern_bytes[i] as u64) % MOD;
            text_hash = (BASE * text_hash + text_bytes[i] as u64) % MOD;
        }
        
        // 滑动窗口
        for i in 0..=n - m {
            metrics.record_comparison();
            
            // 哈希值匹配时，验证实际字符串
            if pattern_hash == text_hash {
                let mut match_found = true;
                for j in 0..m {
                    metrics.record_comparison();
                    if text_bytes[i + j] != pattern_bytes[j] {
                        match_found = false;
                        break;
                    }
                }
                if match_found {
                    result.push(i);
                }
            }
            
            // 计算下一个窗口的哈希值
            if i < n - m {
                text_hash = (BASE * (text_hash + MOD - (text_bytes[i] as u64 * h) % MOD) 
                    + text_bytes[i + m] as u64) % MOD;
            }
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(result)
    }
    
    /// 最长回文子串（Manacher算法）
    /// 
    /// 时间复杂度: O(n)
    /// 空间复杂度: O(n)
    pub fn longest_palindrome(
        s: &str,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<String> {
        let start_time = Instant::now();
        
        if s.is_empty() {
            return Ok(String::new());
        }
        
        // 预处理字符串，在字符间插入'#'
        let mut t = String::from("^");
        for ch in s.chars() {
            t.push('#');
            t.push(ch);
        }
        t.push_str("#$");
        
        let t_chars: Vec<char> = t.chars().collect();
        let n = t_chars.len();
        let mut p = vec![0; n];
        let mut center = 0;
        let mut right = 0;
        
        for i in 1..n - 1 {
            metrics.record_comparison();
            let mirror = 2 * center - i;
            
            if right > i {
                p[i] = p[mirror].min(right - i);
            }
            
            // 尝试扩展回文
            while t_chars[i + p[i] + 1] == t_chars[i - p[i] - 1] {
                metrics.record_comparison();
                p[i] += 1;
            }
            
            // 更新中心和右边界
            if i + p[i] > right {
                center = i;
                right = i + p[i];
            }
        }
        
        // 找到最长回文
        let (max_len, center_idx) = p.iter().enumerate()
            .max_by_key(|(_, len)| *len)
            .map(|(idx, len)| (*len, idx))
            .unwrap_or((0, 0));
        
        let start = (center_idx - max_len) / 2;
        let result = s.chars().skip(start).take(max_len).collect();
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(result)
    }
}

/// 数学算法实现
#[derive(Debug)]
pub struct MathematicalAlgorithms;

impl MathematicalAlgorithms {
    /// 欧几里得算法（最大公约数）
    /// 
    /// 时间复杂度: O(log min(a, b))
    /// 空间复杂度: O(1)
    pub fn gcd(mut a: i64, mut b: i64, metrics: &mut AlgorithmMetrics) -> AlgorithmResult<i64> {
        let start_time = Instant::now();
        
        while b != 0 {
            metrics.record_comparison();
            let temp = b;
            b = a % b;
            a = temp;
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(a.abs())
    }
    
    /// 扩展欧几里得算法
    /// 
    /// 求解 ax + by = gcd(a, b)
    /// 返回 (gcd, x, y)
    pub fn extended_gcd(a: i64, b: i64, metrics: &mut AlgorithmMetrics) -> AlgorithmResult<(i64, i64, i64)> {
        let start_time = Instant::now();
        
        if b == 0 {
            metrics.set_execution_time(start_time.elapsed());
            return Ok((a, 1, 0));
        }
        
        let (gcd, x1, y1) = Self::extended_gcd(b, a % b, metrics)?;
        let x = y1;
        let y = x1 - (a / b) * y1;
        
        metrics.set_execution_time(start_time.elapsed());
        Ok((gcd, x, y))
    }
    
    /// 快速幂算法
    /// 
    /// 计算 base^exp % mod
    /// 时间复杂度: O(log exp)
    pub fn fast_power(base: i64, exp: u64, modulo: i64, metrics: &mut AlgorithmMetrics) -> AlgorithmResult<i64> {
        let start_time = Instant::now();
        let mut result = 1i64;
        let mut base = base % modulo;
        let mut exp = exp;
        
        while exp > 0 {
            metrics.record_comparison();
            if exp % 2 == 1 {
                result = (result * base) % modulo;
            }
            exp >>= 1;
            base = (base * base) % modulo;
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(result)
    }
    
    /// 埃拉托斯特尼筛法（素数筛）
    /// 
    /// 时间复杂度: O(n log log n)
    /// 空间复杂度: O(n)
    pub fn sieve_of_eratosthenes(n: usize, metrics: &mut AlgorithmMetrics) -> AlgorithmResult<Vec<usize>> {
        let start_time = Instant::now();
        
        if n < 2 {
            return Ok(Vec::new());
        }
        
        let mut is_prime = vec![true; n + 1];
        is_prime[0] = false;
        is_prime[1] = false;
        
        for i in 2..=((n as f64).sqrt() as usize) {
            if is_prime[i] {
                metrics.record_comparison();
                let mut j = i * i;
                while j <= n {
                    is_prime[j] = false;
                    j += i;
                }
            }
        }
        
        let primes: Vec<usize> = (2..=n)
            .filter(|&i| is_prime[i])
            .collect();
        
        metrics.set_execution_time(start_time.elapsed());
        metrics.update_peak_memory((n + 1) * std::mem::size_of::<bool>());
        Ok(primes)
    }
    
    /// 欧拉函数（φ函数）
    /// 
    /// 计算小于n且与n互质的正整数个数
    /// 时间复杂度: O(sqrt(n))
    pub fn euler_phi(mut n: i64, metrics: &mut AlgorithmMetrics) -> AlgorithmResult<i64> {
        let start_time = Instant::now();
        let mut result = n;
        let mut i = 2i64;
        
        while i * i <= n {
            metrics.record_comparison();
            if n % i == 0 {
                while n % i == 0 {
                    n /= i;
                }
                result -= result / i;
            }
            i += 1;
        }
        
        if n > 1 {
            result -= result / n;
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(result)
    }
    
    /// 矩阵快速幂
    /// 
    /// 时间复杂度: O(n³ log exp)
    pub fn matrix_power(
        matrix: &[Vec<i64>],
        exp: u64,
        modulo: i64,
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<Vec<Vec<i64>>> {
        let start_time = Instant::now();
        let n = matrix.len();
        
        // 单位矩阵
        let mut result = vec![vec![0; n]; n];
        for i in 0..n {
            result[i][i] = 1;
        }
        
        let mut base = matrix.to_vec();
        let mut exp = exp;
        
        // 矩阵乘法
        fn matrix_multiply(a: &[Vec<i64>], b: &[Vec<i64>], modulo: i64) -> Vec<Vec<i64>> {
            let n = a.len();
            let mut c = vec![vec![0; n]; n];
            for i in 0..n {
                for j in 0..n {
                    for k in 0..n {
                        c[i][j] = (c[i][j] + a[i][k] * b[k][j]) % modulo;
                    }
                }
            }
            c
        }
        
        while exp > 0 {
            metrics.record_comparison();
            if exp % 2 == 1 {
                result = matrix_multiply(&result, &base, modulo);
            }
            base = matrix_multiply(&base, &base, modulo);
            exp >>= 1;
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok(result)
    }
    
    /// 中国剩余定理
    /// 
    /// 求解同余方程组
    pub fn chinese_remainder_theorem(
        remainders: &[i64],
        moduli: &[i64],
        metrics: &mut AlgorithmMetrics,
    ) -> AlgorithmResult<i64> {
        let start_time = Instant::now();
        
        if remainders.len() != moduli.len() {
            return Err(ModelError::ValidationError(
                "余数和模数数量不匹配".to_string()
            ));
        }
        
        let prod: i64 = moduli.iter().product();
        let mut result = 0i64;
        
        for i in 0..remainders.len() {
            metrics.record_comparison();
            let p = prod / moduli[i];
            let (_, inv, _) = Self::extended_gcd(p, moduli[i], metrics)?;
            result = (result + remainders[i] * inv * p) % prod;
        }
        
        metrics.set_execution_time(start_time.elapsed());
        Ok((result % prod + prod) % prod)
    }
}

/// 算法关系分析器
#[derive(Debug)]
pub struct AlgorithmRelationshipAnalyzer {
    algorithms: HashMap<String, AlgorithmCharacteristics>,
    relationships: HashMap<(String, String), RelationshipType>,
    performance_data: HashMap<String, Vec<AlgorithmMetrics>>,
}

impl AlgorithmRelationshipAnalyzer {
    pub fn new() -> Self {
        Self {
            algorithms: HashMap::new(),
            relationships: HashMap::new(),
            performance_data: HashMap::new(),
        }
    }
    
    /// 注册算法
    pub fn register_algorithm(&mut self, characteristics: AlgorithmCharacteristics) {
        self.algorithms.insert(characteristics.name.clone(), characteristics);
    }
    
    /// 添加算法关系
    pub fn add_relationship(&mut self, algo1: String, algo2: String, relationship: RelationshipType) {
        self.relationships.insert((algo1, algo2), relationship);
    }
    
    /// 记录性能数据
    pub fn record_performance(&mut self, algorithm_name: String, metrics: AlgorithmMetrics) {
        self.performance_data
            .entry(algorithm_name)
            .or_insert_with(Vec::new)
            .push(metrics);
    }
    
    /// 分析算法复杂度关系
    pub fn analyze_complexity_relationships(&self) -> Vec<ComplexityComparison> {
        let mut comparisons = Vec::new();
        
        for (name1, algo1) in &self.algorithms {
            for (name2, algo2) in &self.algorithms {
                if name1 != name2 {
                    let comparison = ComplexityComparison {
                        algorithm_a: name1.clone(),
                        algorithm_b: name2.clone(),
                        time_complexity_comparison: Self::compare_complexity(
                            &algo1.complexity.time_complexity,
                            &algo2.complexity.time_complexity,
                        ),
                        space_complexity_comparison: Self::compare_complexity(
                            &algo1.complexity.space_complexity,
                            &algo2.complexity.space_complexity,
                        ),
                        overall_recommendation: Self::determine_recommendation(algo1, algo2),
                    };
                    comparisons.push(comparison);
                }
            }
        }
        
        comparisons
    }
    
    fn compare_complexity(complexity1: &ComplexityClass, complexity2: &ComplexityClass) -> ComplexityRelation {
        match complexity1.cmp(complexity2) {
            Ordering::Less => ComplexityRelation::Better,
            Ordering::Equal => ComplexityRelation::Equal,
            Ordering::Greater => ComplexityRelation::Worse,
        }
    }
    
    fn determine_recommendation(algo1: &AlgorithmCharacteristics, algo2: &AlgorithmCharacteristics) -> AlgorithmRecommendation {
        let mut score1 = 0;
        let mut score2 = 0;
        
        // 时间复杂度权重最高
        match algo1.complexity.time_complexity.cmp(&algo2.complexity.time_complexity) {
            Ordering::Less => score1 += 3,
            Ordering::Greater => score2 += 3,
            Ordering::Equal => {}
        }
        
        // 空间复杂度
        match algo1.complexity.space_complexity.cmp(&algo2.complexity.space_complexity) {
            Ordering::Less => score1 += 2,
            Ordering::Greater => score2 += 2,
            Ordering::Equal => {}
        }
        
        // 稳定性
        if algo1.is_stable && !algo2.is_stable {
            score1 += 1;
        } else if !algo1.is_stable && algo2.is_stable {
            score2 += 1;
        }
        
        // 原地算法
        if algo1.is_in_place && !algo2.is_in_place {
            score1 += 1;
        } else if !algo1.is_in_place && algo2.is_in_place {
            score2 += 1;
        }
        
        if score1 > score2 {
            AlgorithmRecommendation::PreferFirst
        } else if score2 > score1 {
            AlgorithmRecommendation::PreferSecond
        } else {
            AlgorithmRecommendation::NoPreference
        }
    }
    
    /// 生成优化建议
    pub fn generate_optimization_suggestions(&self) -> Vec<AlgorithmOptimizationSuggestion> {
        let mut suggestions = Vec::new();
        
        for (name, characteristics) in &self.algorithms {
            let mut algorithm_suggestions = Vec::new();
            
            // 基于复杂度的建议
            if matches!(characteristics.complexity.time_complexity, ComplexityClass::Quadratic | ComplexityClass::Cubic) {
                algorithm_suggestions.push("Consider using a more efficient algorithm with better time complexity".to_string());
            }
            
            if matches!(characteristics.complexity.space_complexity, ComplexityClass::Linear | ComplexityClass::Quadratic) {
                algorithm_suggestions.push("Consider space optimization techniques".to_string());
            }
            
            // 基于特征的建议
            if characteristics.parallelization_potential == ParallelizationLevel::HighlyParallelizable {
                algorithm_suggestions.push("Consider parallel implementation for better performance".to_string());
            }
            
            if !characteristics.is_in_place && characteristics.category == AlgorithmCategory::Sorting {
                algorithm_suggestions.push("Consider in-place variant to reduce memory usage".to_string());
            }
            
            if !algorithm_suggestions.is_empty() {
                suggestions.push(AlgorithmOptimizationSuggestion {
                    algorithm_name: name.clone(),
                    suggestions: algorithm_suggestions,
                    priority: OptimizationPriority::Medium,
                });
            }
        }
        
        suggestions
    }
    
    /// 获取性能统计
    pub fn get_performance_statistics(&self, algorithm_name: &str) -> Option<PerformanceStatistics> {
        if let Some(metrics_list) = self.performance_data.get(algorithm_name) {
            if metrics_list.is_empty() {
                return None;
            }
            
            let total_runs = metrics_list.len();
            let total_nanos = metrics_list.iter().map(|m| m.execution_time.as_nanos()).sum::<u128>();
            let avg_nanos = (total_nanos / total_runs as u128) as u64;
            let avg_execution_time = Duration::from_nanos(avg_nanos);
            let avg_comparisons = metrics_list.iter().map(|m| m.comparison_count).sum::<u64>() / total_runs as u64;
            let avg_swaps = metrics_list.iter().map(|m| m.swap_count).sum::<u64>() / total_runs as u64;
            let max_memory = metrics_list.iter().map(|m| m.peak_memory_usage).max().unwrap_or(0);
            
            Some(PerformanceStatistics {
                algorithm_name: algorithm_name.to_string(),
                total_runs,
                average_execution_time: avg_execution_time,
                average_comparisons: avg_comparisons,
                average_swaps: avg_swaps,
                peak_memory_usage: max_memory,
            })
        } else {
            None
        }
    }
}

/// 关系类型
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RelationshipType {
    /// 等价算法
    Equivalent,
    /// 优化版本
    Optimization,
    /// 特殊情况
    SpecialCase,
    /// 组合算法
    Combination,
    /// 竞争算法
    Alternative,
    /// 预处理关系
    Preprocessing,
}

/// 复杂度比较
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplexityComparison {
    pub algorithm_a: String,
    pub algorithm_b: String,
    pub time_complexity_comparison: ComplexityRelation,
    pub space_complexity_comparison: ComplexityRelation,
    pub overall_recommendation: AlgorithmRecommendation,
}

/// 复杂度关系
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ComplexityRelation {
    Better,
    Equal,
    Worse,
}

/// 算法推荐
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AlgorithmRecommendation {
    PreferFirst,
    PreferSecond,
    NoPreference,
}

/// 算法优化建议
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlgorithmOptimizationSuggestion {
    pub algorithm_name: String,
    pub suggestions: Vec<String>,
    pub priority: OptimizationPriority,
}

/// 优化优先级
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum OptimizationPriority {
    Low,
    Medium,
    High,
    Critical,
}

/// 性能统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceStatistics {
    pub algorithm_name: String,
    pub total_runs: usize,
    pub average_execution_time: Duration,
    pub average_comparisons: u64,
    pub average_swaps: u64,
    pub peak_memory_usage: usize,
}

impl Default for AlgorithmRelationshipAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_quicksort() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5];
        let mut metrics = AlgorithmMetrics::new();
        
        SortingAlgorithms::quicksort(&mut arr, &mut metrics).unwrap();
        
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 5, 6, 9]);
        assert!(metrics.comparison_count > 0);
        assert!(metrics.swap_count > 0);
    }
    
    #[test]
    fn test_mergesort() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5];
        let mut metrics = AlgorithmMetrics::new();
        
        SortingAlgorithms::mergesort(&mut arr, &mut metrics).unwrap();
        
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 5, 6, 9]);
        assert!(metrics.comparison_count > 0);
    }
    
    #[test]
    fn test_binary_search() {
        let arr = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
        let mut metrics = AlgorithmMetrics::new();
        
        let result = SearchingAlgorithms::binary_search(&arr, &5, &mut metrics).unwrap();
        assert_eq!(result, Some(4));
        
        let result = SearchingAlgorithms::binary_search(&arr, &10, &mut metrics).unwrap();
        assert_eq!(result, None);
    }
    
    #[test]
    fn test_fibonacci_dp() {
        let mut metrics = AlgorithmMetrics::new();
        
        let result = DynamicProgrammingAlgorithms::fibonacci_dp(10, &mut metrics).unwrap();
        assert_eq!(result, 55);
        
        let result = DynamicProgrammingAlgorithms::fibonacci_dp(0, &mut metrics).unwrap();
        assert_eq!(result, 0);
        
        let result = DynamicProgrammingAlgorithms::fibonacci_dp(1, &mut metrics).unwrap();
        assert_eq!(result, 1);
    }
    
    #[test]
    fn test_lcs() {
        let mut metrics = AlgorithmMetrics::new();
        
        let result = DynamicProgrammingAlgorithms::longest_common_subsequence(
            "ABCDGH",
            "AEDFHR",
            &mut metrics,
        ).unwrap();
        assert_eq!(result, 3); // "ADH"
    }
    
    #[test]
    fn test_knapsack() {
        let mut metrics = AlgorithmMetrics::new();
        let weights = vec![10, 20, 30];
        let values = vec![60, 100, 120];
        
        let result = DynamicProgrammingAlgorithms::knapsack_01(&weights, &values, 50, &mut metrics).unwrap();
        assert_eq!(result, 220); // items 1 and 2
    }
    
    #[test]
    fn test_activity_selection() {
        let mut metrics = AlgorithmMetrics::new();
        let activities = vec![(1, 4), (3, 5), (0, 6), (5, 7), (3, 9), (5, 9), (6, 10), (8, 11), (8, 12), (2, 14), (12, 16)];
        
        let result = GreedyAlgorithms::activity_selection(&activities, &mut metrics).unwrap();
        assert!(!result.is_empty());
    }
    
    #[test]
    fn test_fractional_knapsack() {
        let mut metrics = AlgorithmMetrics::new();
        let items = vec![(10.0, 60.0), (20.0, 100.0), (30.0, 120.0)];
        
        let result = GreedyAlgorithms::fractional_knapsack(&items, 50.0, &mut metrics).unwrap();
        assert!((result - 240.0).abs() < 1e-6);
    }
    
    #[test]
    fn test_algorithm_analyzer() {
        let mut analyzer = AlgorithmRelationshipAnalyzer::new();
        
        analyzer.register_algorithm(SortingAlgorithms::quicksort_characteristics());
        analyzer.register_algorithm(SortingAlgorithms::mergesort_characteristics());
        
        let comparisons = analyzer.analyze_complexity_relationships();
        assert!(!comparisons.is_empty());
        
        let suggestions = analyzer.generate_optimization_suggestions();
        assert!(!suggestions.is_empty());
    }
    
    #[test]
    fn test_complexity_ordering() {
        assert!(ComplexityClass::Constant < ComplexityClass::Logarithmic);
        assert!(ComplexityClass::Logarithmic < ComplexityClass::Linear);
        assert!(ComplexityClass::Linear < ComplexityClass::Linearithmic);
        assert!(ComplexityClass::Linearithmic < ComplexityClass::Quadratic);
        assert!(ComplexityClass::Quadratic < ComplexityClass::Cubic);
        assert!(ComplexityClass::Cubic < ComplexityClass::Exponential);
        assert!(ComplexityClass::Exponential < ComplexityClass::Factorial);
    }
}
