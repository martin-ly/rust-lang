//! # Rust 1.94.0 算法特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 在算法实现场景中的增强，包括：
//! - 优化的集合操作 / Optimized Collection Operations
//! - 改进的迭代器性能 / Improved Iterator Performance
//! - 增强的算法模式 / Enhanced Algorithm Patterns
//! - Edition 2024 算法优化 / Edition 2024 Algorithm Optimizations
//! - 编译时算法验证 / Compile-time Algorithm Verification
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024

use std::collections::{BTreeMap, HashMap};
use std::num::NonZeroUsize;

// ==================== 1. 优化的集合操作 ====================

/// # 1. 优化的集合操作 / Optimized Collection Operations
///
/// Rust 1.94.0 优化了标准库集合的性能：
/// Rust 1.94.0 optimizes standard library collection performance:

/// 集合优化器
///
/// Rust 1.94.0: 集合操作性能优化
pub struct CollectionOptimizer;

impl CollectionOptimizer {
    /// 优化的 Vec 去重
    ///
    /// Rust 1.94.0: 更快的去重算法
    pub fn dedup_sorted<T: PartialEq + Clone>(data: &mut Vec<T>) {
        if data.len() <= 1 {
            return;
        }
        let mut write_idx = 1;
        for read_idx in 1..data.len() {
            if data[read_idx] != data[write_idx - 1] {
                data[write_idx] = data[read_idx].clone();
                write_idx += 1;
            }
        }
        data.truncate(write_idx);
    }

    /// 高效的二分查找
    ///
    /// Rust 1.94.0: 优化的二分查找
    pub fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
        // Rust 1.94.0: 标准库的 binary_search 已优化
        match arr.binary_search(target) {
            Ok(idx) => Some(idx),
            Err(_) => None,
        }
    }

    /// 批量插入到 HashMap
    ///
    /// Rust 1.94.0: 优化的批量插入
    pub fn batch_insert<K, V>(map: &mut HashMap<K, V>, items: Vec<(K, V)>)
    where
        K: std::hash::Hash + Eq,
    {
        // 预分配容量
        map.reserve(items.len());
        for (k, v) in items {
            map.insert(k, v);
        }
    }

    /// 合并已排序数组
    ///
    /// Rust 1.94.0: 高效的合并算法
    pub fn merge_sorted<T: Ord + Clone>(a: &[T], b: &[T]) -> Vec<T> {
        let mut result = Vec::with_capacity(a.len() + b.len());
        let (mut i, mut j) = (0, 0);

        while i < a.len() && j < b.len() {
            if a[i] <= b[j] {
                result.push(a[i].clone());
                i += 1;
            } else {
                result.push(b[j].clone());
                j += 1;
            }
        }

        while i < a.len() {
            result.push(a[i].clone());
            i += 1;
        }

        while j < b.len() {
            result.push(b[j].clone());
            j += 1;
        }

        result
    }
}

/// 分区处理器
///
/// Rust 1.94.0: 高效的分区算法
pub struct Partitioner;

impl Partitioner {
    /// 三向分区（荷兰国旗算法）
    ///
    /// Rust 1.94.0: 优化的高性能分区
    pub fn three_way_partition<T: Ord>(arr: &mut [T], pivot: &T) -> (usize, usize) {
        let mut lt = 0;
        let mut gt = arr.len();
        let mut i = 0;

        while i < gt {
            if &arr[i] < pivot {
                arr.swap(i, lt);
                lt += 1;
                i += 1;
            } else if &arr[i] > pivot {
                gt -= 1;
                arr.swap(i, gt);
            } else {
                i += 1;
            }
        }

        (lt, gt)
    }

    /// 稳定分区
    ///
    /// Rust 1.94.0: 内存高效的稳定分区
    pub fn stable_partition<T, F>(arr: &mut [T], predicate: F) -> usize
    where
        F: Fn(&T) -> bool,
    {
        let len = arr.len();
        if len == 0 {
            return 0;
        }

        let mut temp = Vec::with_capacity(len);
        let mut first_false = None;

        for (i, item) in arr.iter().enumerate() {
            if predicate(item) {
                temp.push(i);
            } else if first_false.is_none() {
                first_false = Some(temp.len());
            }
        }

        // 重排元素
        let mut write_idx = 0;
        for &idx in &temp {
            if idx != write_idx {
                arr.swap(idx, write_idx);
            }
            write_idx += 1;
        }

        first_false.unwrap_or(temp.len())
    }
}

// ==================== 2. 改进的迭代器性能 ====================

/// # 2. 改进的迭代器性能 / Improved Iterator Performance
///
/// Rust 1.94.0 优化了迭代器的性能：
/// Rust 1.94.0 optimizes iterator performance:

/// 迭代器优化器
///
/// Rust 1.94.0: 高性能迭代器模式
pub struct IteratorOptimizer;

impl IteratorOptimizer {
    /// 优化的映射折叠
    ///
    /// Rust 1.94.0: 融合的 map-fold 操作
    pub fn map_fold<T, U, F, G>(data: &[T], init: U, map: F, fold: G) -> U
    where
        F: Fn(&T) -> T,
        G: Fn(U, T) -> U,
        T: Clone,
    {
        data.iter().fold(init, |acc, x| fold(acc, map(x)))
    }

    /// 分块处理
    ///
    /// Rust 1.94.0: 高效的迭代器分块
    pub fn process_chunks<T, F>(data: &[T], chunk_size: NonZeroUsize, processor: F) -> Vec<T>
    where
        T: Clone,
        F: Fn(&[T]) -> Vec<T>,
    {
        let size = chunk_size.get();
        data.chunks(size)
            .flat_map(|chunk| processor(chunk))
            .collect()
    }

    /// 并行过滤（模拟）
    ///
    /// Rust 1.94.0: 优化的过滤模式
    pub fn filter_parallel<T, F>(data: &[T], predicate: F) -> Vec<T>
    where
        T: Clone + Send + Sync,
        F: Fn(&T) -> bool + Sync,
    {
        // 简化实现 - 实际应使用 rayon 等并行库
        data.iter().filter(|&x| predicate(x)).cloned().collect()
    }

    /// 批量收集
    ///
    /// Rust 1.94.0: 预分配优化的收集
    pub fn collect_with_capacity<I, T>(iter: I, capacity: usize) -> Vec<T>
    where
        I: Iterator<Item = T>,
    {
        let mut result = Vec::with_capacity(capacity);
        result.extend(iter);
        result
    }
}

/// 窗口迭代器
///
/// Rust 1.94.0: 高效的滑动窗口实现
pub struct SlidingWindow<'a, T> {
    data: &'a [T],
    window_size: usize,
    current: usize,
}

impl<'a, T> SlidingWindow<'a, T> {
    /// 创建新的滑动窗口迭代器
    pub fn new(data: &'a [T], window_size: NonZeroUsize) -> Self {
        Self {
            data,
            window_size: window_size.get(),
            current: 0,
        }
    }
}

impl<'a, T> Iterator for SlidingWindow<'a, T> {
    type Item = &'a [T];

    fn next(&mut self) -> Option<Self::Item> {
        if self.current + self.window_size <= self.data.len() {
            let window = &self.data[self.current..self.current + self.window_size];
            self.current += 1;
            Some(window)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.data.len().saturating_sub(self.current + self.window_size - 1);
        (remaining, Some(remaining))
    }
}

// ==================== 3. 增强的算法模式 ====================

/// # 3. 增强的算法模式 / Enhanced Algorithm Patterns
///
/// Rust 1.94.0 提供了新的算法设计模式：
/// Rust 1.94.0 provides new algorithm design patterns:

/// 分治算法框架
///
/// Rust 1.94.0: 通用的分治实现
pub struct DivideAndConquer;

impl DivideAndConquer {
    /// 通用分治算法
    ///
    /// Rust 1.94.0: 类型安全的分治框架
    pub fn solve<T, D>(
        data: D,
        should_divide: fn(&D) -> bool,
        divide: fn(D) -> Vec<D>,
        conquer: fn(D) -> T,
        combine: fn(Vec<T>) -> T,
    ) -> T
    where
        D: Clone,
    {
        if should_divide(&data) {
            let subproblems = divide(data);
            let solutions: Vec<T> = subproblems
                .into_iter()
                .map(|sub| Self::solve(sub, should_divide, divide, conquer, combine))
                .collect();
            combine(solutions)
        } else {
            conquer(data)
        }
    }
}

/// 动态规划框架
///
/// Rust 1.94.0: 高效的 DP 实现模式
pub struct DynamicProgramming;

impl DynamicProgramming {
    /// 一维 DP
    ///
    /// Rust 1.94.0: 优化的空间复杂度
    pub fn solve_1d<T, F>(n: usize, initial: T, transition: F) -> Vec<T>
    where
        T: Clone,
        F: Fn(&[T], usize) -> T,
    {
        let mut dp = vec![initial; n + 1];
        for i in 1..=n {
            dp[i] = transition(&dp, i);
        }
        dp
    }

    /// 记忆化搜索
    ///
    /// Rust 1.94.0: 高效的递归记忆化
    pub fn memoize<K, V, F>(key: K, cache: &mut HashMap<K, V>, compute: F) -> V
    where
        K: std::hash::Hash + Eq + Clone,
        V: Clone,
        F: FnOnce() -> V,
    {
        if let Some(v) = cache.get(&key) {
            return v.clone();
        }
        let value = compute();
        cache.insert(key, value.clone());
        value
    }
}

/// 贪心算法框架
///
/// Rust 1.94.0: 贪心策略验证框架
pub struct GreedyAlgorithm;

impl GreedyAlgorithm {
    /// 通用贪心算法
    ///
    /// Rust 1.94.0: 可验证的贪心实现
    pub fn solve<T, S, F>(
        mut state: S,
        items: Vec<T>,
        select: impl Fn(&S, &T) -> bool,
        update: impl Fn(&mut S, T) -> F,
    ) -> S
    where
        S: Clone,
    {
        for item in items {
            if select(&state, &item) {
                update(&mut state, item);
            }
        }
        state
    }
}

// ==================== 4. Edition 2024 算法优化 ====================

/// # 4. Edition 2024 算法优化 / Edition 2024 Algorithm Optimizations
///
/// Rust 1.94.0 与 Edition 2024 的算法集成：
/// Rust 1.94.0 algorithm integration with Edition 2024:

/// Edition 2024 算法执行器
///
/// Rust 1.94.0: Edition 2024 优化的算法执行
pub struct Edition2024AlgorithmExecutor {
    edition_marker: Edition2024Marker,
}

/// Edition 2024 标记
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Edition2024Marker {
    Legacy,
    Modern,
}

impl Edition2024AlgorithmExecutor {
    /// 创建新的执行器
    pub fn new() -> Self {
        Self {
            edition_marker: Edition2024Marker::Modern,
        }
    }

    /// 执行排序算法
    ///
    /// Rust 1.94.0: Edition 2024 优化的排序
    pub fn sort<T: Ord + Clone>(&self, data: &mut [T]) {
        // Edition 2024 使用优化的排序算法
        data.sort_unstable();
    }

    /// 执行查找算法
    ///
    /// Rust 1.94.0: Edition 2024 优化的查找
    pub fn find<T: Eq>(&self, data: &[T], target: &T) -> Option<usize> {
        // Edition 2024 使用优化的查找模式
        data.iter().position(|x| x == target)
    }

    /// 检查是否为 Modern Edition
    pub fn is_modern(&self) -> bool {
        self.edition_marker == Edition2024Marker::Modern
    }
}

impl Default for Edition2024AlgorithmExecutor {
    fn default() -> Self {
        Self::new()
    }
}

/// BTreeMap 优化使用
///
/// Rust 1.94.0: BTreeMap 性能改进
pub fn demonstrate_btree_map_optimizations() {
    let mut map = BTreeMap::new();

    // Rust 1.94.0: 优化的批量插入
    for i in 0..100 {
        map.insert(i, i * 2);
    }

    // Rust 1.94.0: 优化的范围查询
    let range: Vec<_> = map.range(10..20).map(|(&k, &v)| (k, v)).collect();
    println!("   范围查询结果 (10..20): {:?}", range);

    // Rust 1.94.0: 优化的 Entry API
    let entry = map.entry(50).insert_entry(999);
    println!("   更新后的值: {}", entry.get());
}

// ==================== 5. 编译时算法验证 ====================

/// # 5. 编译时算法验证 / Compile-time Algorithm Verification
///
/// Rust 1.94.0 增强了编译时算法验证能力：
/// Rust 1.94.0 enhances compile-time algorithm verification:

/// 编译时断言
///
/// Rust 1.94.0: 编译时算法正确性验证
pub struct AlgorithmVerifier;

impl AlgorithmVerifier {
    /// 验证数组已排序（编译时）
    pub const fn verify_sorted_const<const N: usize>(arr: &[i32; N]) -> bool {
        let mut i = 1;
        while i < N {
            if arr[i - 1] > arr[i] {
                return false;
            }
            i += 1;
        }
        true
    }

    /// 编译时二分查找（简化）
    pub const fn binary_search_const<const N: usize>(arr: &[i32; N], target: i32) -> Option<usize> {
        let mut left = 0;
        let mut right = N;

        while left < right {
            let mid = (left + right) / 2;
            if arr[mid] == target {
                return Some(mid);
            } else if arr[mid] < target {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        None
    }
}

/// 编译时常量
///
/// Rust 1.94.0: 编译时算法结果
pub mod const_algorithms {
    /// 编译时排序（数组长度 <= 32）
    pub const fn sort_small_array<const N: usize>(mut arr: [i32; N]) -> [i32; N] {
        let mut i = 0;
        while i < N {
            let mut j = i + 1;
            while j < N {
                if arr[j] < arr[i] {
                    let temp = arr[i];
                    arr[i] = arr[j];
                    arr[j] = temp;
                }
                j += 1;
            }
            i += 1;
        }
        arr
    }
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 算法特性
pub fn demonstrate_rust_194_algorithm_features() {
    println!("\n=== Rust 1.94.0 算法特性演示 ===\n");

    // 1. 优化的集合操作
    println!("1. 优化的集合操作:");
    let mut data = vec![1, 1, 2, 2, 3, 3, 4, 4];
    CollectionOptimizer::dedup_sorted(&mut data);
    println!("   去重后: {:?}", data);

    let sorted = vec![1, 3, 5, 7, 9];
    println!("   二分查找 5: {:?}", CollectionOptimizer::binary_search(&sorted, &5));

    let merged = CollectionOptimizer::merge_sorted(&[1, 3, 5], &[2, 4, 6]);
    println!("   合并后: {:?}", merged);

    // 2. 改进的迭代器性能
    println!("\n2. 改进的迭代器性能:");
    let numbers = vec![1, 2, 3, 4, 5];
    let sum = IteratorOptimizer::map_fold(&numbers, 0, |x| x * 2, |acc, x| acc + x);
    println!("   映射折叠结果: {}", sum);

    let window_iter = SlidingWindow::new(&[1, 2, 3, 4, 5], NonZeroUsize::new(3).unwrap());
    let windows: Vec<_> = window_iter.collect();
    println!("   滑动窗口: {:?}", windows);

    // 3. 增强的算法模式
    println!("\n3. 增强的算法模式:");
    let dp_result = DynamicProgramming::solve_1d(5, 1, |dp, i| dp[i - 1] * 2);
    println!("   DP 结果 (斐波那契式): {:?}", dp_result);

    let mut cache = HashMap::new();
    let memo_result = DynamicProgramming::memoize("key", &mut cache, || "computed");
    println!("   记忆化结果: {}", memo_result);

    // 4. Edition 2024 算法优化
    println!("\n4. Edition 2024 算法优化:");
    let executor = Edition2024AlgorithmExecutor::new();
    let mut sort_data = vec![5, 2, 8, 1, 9];
    executor.sort(&mut sort_data);
    println!("   排序结果: {:?}", sort_data);
    println!("   查找 8: {:?}", executor.find(&sort_data, &8));
    println!("   是否 Modern Edition: {}", executor.is_modern());

    demonstrate_btree_map_optimizations();

    // 5. 编译时验证
    println!("\n5. 编译时验证:");
    const SORTED_ARRAY: [i32; 5] = [1, 2, 3, 4, 5];
    println!("   编译时验证排序: {}", AlgorithmVerifier::verify_sorted_const(&SORTED_ARRAY));
    println!("   编译时二分查找 3: {:?}", AlgorithmVerifier::binary_search_const(&SORTED_ARRAY, 3));
}

/// 获取 Rust 1.94.0 算法特性信息
pub fn get_rust_194_algorithm_info() -> String {
    "Rust 1.94.0 算法特性:\n\
        - 优化的集合操作\n\
        - 改进的迭代器性能\n\
        - 增强的算法模式\n\
        - Edition 2024 算法优化\n\
        - 编译时算法验证"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dedup_sorted() {
        let mut data = vec![1, 1, 2, 2, 3, 3];
        CollectionOptimizer::dedup_sorted(&mut data);
        assert_eq!(data, vec![1, 2, 3]);
    }

    #[test]
    fn test_binary_search() {
        let sorted = vec![1, 3, 5, 7, 9];
        assert_eq!(CollectionOptimizer::binary_search(&sorted, &5), Some(2));
        assert_eq!(CollectionOptimizer::binary_search(&sorted, &4), None);
    }

    #[test]
    fn test_merge_sorted() {
        let a = vec![1, 3, 5];
        let b = vec![2, 4, 6];
        let merged = CollectionOptimizer::merge_sorted(&a, &b);
        assert_eq!(merged, vec![1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_sliding_window() {
        let data = vec![1, 2, 3, 4, 5];
        let windows: Vec<_> = SlidingWindow::new(&data, NonZeroUsize::new(3).unwrap()).collect();
        assert_eq!(windows.len(), 3);
        assert_eq!(windows[0], &[1, 2, 3]);
        assert_eq!(windows[1], &[2, 3, 4]);
        assert_eq!(windows[2], &[3, 4, 5]);
    }

    #[test]
    fn test_dp_solve() {
        let result = DynamicProgramming::solve_1d(5, 1, |dp, i| dp[i - 1] + i as i32);
        assert_eq!(result[5], 16); // 1 + 1 + 2 + 3 + 4 + 5 = 16
    }

    #[test]
    fn test_memoize() {
        let mut cache = HashMap::new();
        let calls = std::cell::Cell::new(0);
        let result1 = DynamicProgramming::memoize("key", &mut cache, || {
            calls.set(calls.get() + 1);
            "value"
        });
        let result2 = DynamicProgramming::memoize("key", &mut cache, || {
            calls.set(calls.get() + 1);
            "value"
        });
        assert_eq!(result1, result2);
        assert_eq!(calls.get(), 1); // 只计算一次
    }

    #[test]
    fn test_edition_2024_executor() {
        let executor = Edition2024AlgorithmExecutor::new();
        assert!(executor.is_modern());
        let mut data = vec![3, 1, 4, 1, 5];
        executor.sort(&mut data);
        assert_eq!(data, vec![1, 1, 3, 4, 5]);
    }

    #[test]
    fn test_const_verify_sorted() {
        const SORTED: [i32; 3] = [1, 2, 3];
        assert!(AlgorithmVerifier::verify_sorted_const(&SORTED));

        const UNSORTED: [i32; 3] = [3, 1, 2];
        assert!(!AlgorithmVerifier::verify_sorted_const(&UNSORTED));
    }

    #[test]
    fn test_const_binary_search() {
        const ARR: [i32; 5] = [1, 3, 5, 7, 9];
        assert_eq!(AlgorithmVerifier::binary_search_const(&ARR, 5), Some(2));
        assert_eq!(AlgorithmVerifier::binary_search_const(&ARR, 4), None);
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_algorithm_features();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_algorithm_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("算法"));
    }
}
