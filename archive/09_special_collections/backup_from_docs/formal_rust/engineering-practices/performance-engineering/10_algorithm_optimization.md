# 算法优化技术


## 📊 目录

- [概述](#概述)
- [1. 算法优化理论基础](#1-算法优化理论基础)
  - [1.1 复杂度分析](#11-复杂度分析)
  - [1.2 空间复杂度优化](#12-空间复杂度优化)
- [2. 搜索算法优化](#2-搜索算法优化)
  - [2.1 二分搜索优化](#21-二分搜索优化)
  - [2.2 哈希表优化](#22-哈希表优化)
- [3. 排序算法优化](#3-排序算法优化)
  - [3.1 混合排序算法](#31-混合排序算法)
  - [3.2 基数排序优化](#32-基数排序优化)
- [4. 动态规划优化](#4-动态规划优化)
  - [4.1 记忆化优化](#41-记忆化优化)
  - [4.2 背包问题优化](#42-背包问题优化)
- [5. 图算法优化](#5-图算法优化)
  - [5.1 最短路径优化](#51-最短路径优化)
- [6. 形式化证明](#6-形式化证明)
  - [6.1 算法正确性定理](#61-算法正确性定理)
  - [6.2 性能优化定理](#62-性能优化定理)
- [7. 工程实践](#7-工程实践)
  - [7.1 最佳实践](#71-最佳实践)
  - [7.2 常见陷阱](#72-常见陷阱)
- [8. 交叉引用](#8-交叉引用)
- [9. 参考文献](#9-参考文献)


## 概述

本文档详细分析Rust中的算法优化技术，包括时间复杂度优化、空间复杂度优化、算法选择和并行算法设计。

## 1. 算法优化理论基础

### 1.1 复杂度分析

```rust
use std::time::Instant;

// 时间复杂度分析工具
struct ComplexityAnalyzer {
    measurements: Vec<(usize, f64)>, // (input_size, execution_time)
}

impl ComplexityAnalyzer {
    fn new() -> Self {
        ComplexityAnalyzer {
            measurements: Vec::new(),
        }
    }
    
    fn measure<F>(&mut self, input_size: usize, algorithm: F)
    where
        F: FnOnce(),
    {
        let start = Instant::now();
        algorithm();
        let duration = start.elapsed().as_secs_f64();
        self.measurements.push((input_size, duration));
    }
    
    fn analyze_complexity(&self) -> String {
        if self.measurements.len() < 2 {
            return "需要更多数据点进行分析".to_string();
        }
        
        // 计算增长率
        let mut ratios = Vec::new();
        for i in 1..self.measurements.len() {
            let prev_size = self.measurements[i-1].0 as f64;
            let curr_size = self.measurements[i].0 as f64;
            let prev_time = self.measurements[i-1].1;
            let curr_time = self.measurements[i].1;
            
            let size_ratio = curr_size / prev_size;
            let time_ratio = curr_time / prev_time;
            let ratio = time_ratio / size_ratio;
            ratios.push(ratio);
        }
        
        let avg_ratio = ratios.iter().sum::<f64>() / ratios.len() as f64;
        
        // 判断复杂度
        let complexity = if avg_ratio < 1.5 {
            "O(1) - 常数时间"
        } else if avg_ratio < 2.5 {
            "O(log n) - 对数时间"
        } else if avg_ratio < 3.5 {
            "O(n) - 线性时间"
        } else if avg_ratio < 4.5 {
            "O(n log n) - 线性对数时间"
        } else if avg_ratio < 5.5 {
            "O(n²) - 平方时间"
        } else {
            "O(n³) 或更高 - 立方或更高时间"
        };
        
        format!("估计复杂度: {}", complexity)
    }
}

// 使用示例
fn complexity_analysis_example() {
    let mut analyzer = ComplexityAnalyzer::new();
    
    // 测试线性搜索
    for size in [100, 1000, 10000, 100000] {
        let data: Vec<i32> = (0..size).collect();
        analyzer.measure(size, || {
            data.iter().find(|&&x| x == size - 1);
        });
    }
    
    println!("线性搜索: {}", analyzer.analyze_complexity());
}
```

### 1.2 空间复杂度优化

```rust
// 空间复杂度优化示例
struct SpaceOptimizedDataStructure {
    data: Vec<u8>,
    bit_width: u8,
}

impl SpaceOptimizedDataStructure {
    fn new(bit_width: u8) -> Self {
        SpaceOptimizedDataStructure {
            data: Vec::new(),
            bit_width,
        }
    }
    
    fn push(&mut self, value: u32) {
        let max_value = (1u32 << self.bit_width) - 1;
        let masked_value = value & max_value;
        
        // 计算需要多少字节来存储这个值
        let bits_needed = self.bit_width as usize;
        let bytes_needed = (bits_needed + 7) / 8;
        
        // 扩展数据向量
        let current_bits = self.data.len() * 8;
        let new_bits = current_bits + bits_needed;
        let new_bytes = (new_bits + 7) / 8;
        
        while self.data.len() < new_bytes {
            self.data.push(0);
        }
        
        // 存储值
        let mut remaining_bits = bits_needed;
        let mut value_to_store = masked_value;
        let mut byte_index = current_bits / 8;
        let mut bit_offset = current_bits % 8;
        
        while remaining_bits > 0 {
            let bits_in_this_byte = (8 - bit_offset).min(remaining_bits);
            let mask = (1u8 << bits_in_this_byte) - 1;
            let value_part = (value_to_store & mask as u32) as u8;
            
            self.data[byte_index] |= value_part << bit_offset;
            
            value_to_store >>= bits_in_this_byte;
            remaining_bits -= bits_in_this_byte;
            byte_index += 1;
            bit_offset = 0;
        }
    }
    
    fn get(&self, index: usize) -> u32 {
        let start_bit = index * self.bit_width as usize;
        let start_byte = start_bit / 8;
        let bit_offset = start_bit % 8;
        
        let mut result = 0u32;
        let mut bits_read = 0;
        let mut byte_index = start_byte;
        let mut current_bit_offset = bit_offset;
        
        while bits_read < self.bit_width as usize && byte_index < self.data.len() {
            let bits_in_this_byte = (8 - current_bit_offset).min(self.bit_width as usize - bits_read);
            let mask = (1u8 << bits_in_this_byte) - 1;
            let value_part = (self.data[byte_index] >> current_bit_offset) & mask;
            
            result |= (value_part as u32) << bits_read;
            
            bits_read += bits_in_this_byte;
            byte_index += 1;
            current_bit_offset = 0;
        }
        
        result
    }
    
    fn memory_usage(&self) -> usize {
        self.data.len()
    }
}

fn space_optimization_example() {
    let mut optimized = SpaceOptimizedDataStructure::new(4); // 4位存储每个值
    let mut standard = Vec::new();
    
    for i in 0..1000 {
        optimized.push(i as u32);
        standard.push(i as u32);
    }
    
    println!("标准存储: {} 字节", standard.len() * 4);
    println!("优化存储: {} 字节", optimized.memory_usage());
    println!("压缩比: {:.2}%", (optimized.memory_usage() as f64 / (standard.len() * 4) as f64) * 100.0);
}
```

## 2. 搜索算法优化

### 2.1 二分搜索优化

```rust
// 优化的二分搜索
struct OptimizedBinarySearch;

impl OptimizedBinarySearch {
    // 标准二分搜索
    fn standard_binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
        let mut left = 0;
        let mut right = arr.len();
        
        while left < right {
            let mid = left + (right - left) / 2;
            match arr[mid].cmp(target) {
                std::cmp::Ordering::Equal => return Some(mid),
                std::cmp::Ordering::Less => left = mid + 1,
                std::cmp::Ordering::Greater => right = mid,
            }
        }
        None
    }
    
    // 分支预测优化版本
    fn branchless_binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
        let mut left = 0;
        let mut right = arr.len();
        
        while left < right {
            let mid = left + (right - left) / 2;
            let cmp = arr[mid].cmp(target);
            
            // 使用分支预测友好的方式
            let less = (cmp == std::cmp::Ordering::Less) as usize;
            let equal = (cmp == std::cmp::Ordering::Equal) as usize;
            
            left = left + less * (mid + 1 - left);
            right = right - (1 - less) * (right - mid);
            
            if equal != 0 {
                return Some(mid);
            }
        }
        None
    }
    
    // 插值搜索（适用于均匀分布的数据）
    fn interpolation_search(arr: &[i32], target: i32) -> Option<usize> {
        let mut left = 0;
        let mut right = arr.len() - 1;
        
        while left <= right && target >= arr[left] && target <= arr[right] {
            if left == right {
                return if arr[left] == target { Some(left) } else { None };
            }
            
            // 插值公式
            let pos = left + (((right - left) as f64 * (target - arr[left]) as f64) 
                / (arr[right] - arr[left]) as f64) as usize;
            
            match arr[pos].cmp(&target) {
                std::cmp::Ordering::Equal => return Some(pos),
                std::cmp::Ordering::Less => left = pos + 1,
                std::cmp::Ordering::Greater => right = pos - 1,
            }
        }
        None
    }
}

fn search_optimization_example() {
    let data: Vec<i32> = (0..1000000).collect();
    let target = 500000;
    
    let start = Instant::now();
    let result1 = OptimizedBinarySearch::standard_binary_search(&data, &target);
    let time1 = start.elapsed();
    
    let start = Instant::now();
    let result2 = OptimizedBinarySearch::branchless_binary_search(&data, &target);
    let time2 = start.elapsed();
    
    let start = Instant::now();
    let result3 = OptimizedBinarySearch::interpolation_search(&data, target);
    let time3 = start.elapsed();
    
    println!("标准二分搜索: {:?}, 时间: {:?}", result1, time1);
    println!("无分支二分搜索: {:?}, 时间: {:?}", result2, time2);
    println!("插值搜索: {:?}, 时间: {:?}", result3, time3);
}
```

### 2.2 哈希表优化

```rust
use std::collections::HashMap;

// 优化的哈希表实现
struct OptimizedHashMap<K, V> {
    data: Vec<Option<(K, V)>>,
    size: usize,
    capacity: usize,
}

impl<K, V> OptimizedHashMap<K, V>
where
    K: Eq + std::hash::Hash + Clone,
    V: Clone,
{
    fn new() -> Self {
        OptimizedHashMap {
            data: vec![None; 16],
            size: 0,
            capacity: 16,
        }
    }
    
    fn insert(&mut self, key: K, value: V) {
        if self.size >= self.capacity * 3 / 4 {
            self.resize();
        }
        
        let mut index = self.hash(&key);
        let mut probe_count = 0;
        
        // 线性探测
        while let Some(Some((ref existing_key, _))) = self.data.get(index) {
            if existing_key == &key {
                self.data[index] = Some((key, value));
                return;
            }
            index = (index + 1) % self.capacity;
            probe_count += 1;
            
            // 防止无限循环
            if probe_count >= self.capacity {
                self.resize();
                index = self.hash(&key);
                probe_count = 0;
            }
        }
        
        self.data[index] = Some((key, value));
        self.size += 1;
    }
    
    fn get(&self, key: &K) -> Option<&V> {
        let mut index = self.hash(key);
        let mut probe_count = 0;
        
        while let Some(Some((ref existing_key, ref value))) = self.data.get(index) {
            if existing_key == key {
                return Some(value);
            }
            index = (index + 1) % self.capacity;
            probe_count += 1;
            
            if probe_count >= self.capacity {
                break;
            }
        }
        None
    }
    
    fn hash(&self, key: &K) -> usize {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish() as usize % self.capacity
    }
    
    fn resize(&mut self) {
        let old_data = std::mem::replace(&mut self.data, vec![None; self.capacity * 2]);
        self.capacity *= 2;
        self.size = 0;
        
        for item in old_data {
            if let Some((key, value)) = item {
                self.insert(key, value);
            }
        }
    }
}

fn hash_map_optimization_example() {
    let mut optimized = OptimizedHashMap::new();
    let mut standard = HashMap::new();
    
    for i in 0..10000 {
        optimized.insert(format!("key{}", i), i);
        standard.insert(format!("key{}", i), i);
    }
    
    let start = Instant::now();
    for i in 0..10000 {
        let _ = optimized.get(&format!("key{}", i));
    }
    let optimized_time = start.elapsed();
    
    let start = Instant::now();
    for i in 0..10000 {
        let _ = standard.get(&format!("key{}", i));
    }
    let standard_time = start.elapsed();
    
    println!("优化哈希表查找时间: {:?}", optimized_time);
    println!("标准哈希表查找时间: {:?}", standard_time);
}
```

## 3. 排序算法优化

### 3.1 混合排序算法

```rust
// 混合排序算法
struct HybridSorter;

impl HybridSorter {
    // 快速排序 + 插入排序混合
    fn hybrid_quicksort<T: Ord + Clone>(arr: &mut [T]) {
        const INSERTION_THRESHOLD: usize = 10;
        
        if arr.len() <= INSERTION_THRESHOLD {
            Self::insertion_sort(arr);
        } else {
            Self::quicksort_partition(arr);
        }
    }
    
    fn insertion_sort<T: Ord>(arr: &mut [T]) {
        for i in 1..arr.len() {
            let mut j = i;
            while j > 0 && arr[j] < arr[j - 1] {
                arr.swap(j, j - 1);
                j -= 1;
            }
        }
    }
    
    fn quicksort_partition<T: Ord + Clone>(arr: &mut [T]) {
        if arr.len() <= 1 {
            return;
        }
        
        // 三数取中法选择pivot
        let pivot_index = Self::median_of_three(arr);
        arr.swap(pivot_index, arr.len() - 1);
        
        let pivot_index = Self::partition(arr);
        
        Self::hybrid_quicksort(&mut arr[..pivot_index]);
        Self::hybrid_quicksort(&mut arr[pivot_index + 1..]);
    }
    
    fn median_of_three<T: Ord>(arr: &[T]) -> usize {
        let len = arr.len();
        let mid = len / 2;
        
        if arr[0] <= arr[mid] {
            if arr[mid] <= arr[len - 1] {
                mid
            } else if arr[0] <= arr[len - 1] {
                len - 1
            } else {
                0
            }
        } else {
            if arr[0] <= arr[len - 1] {
                0
            } else if arr[mid] <= arr[len - 1] {
                len - 1
            } else {
                mid
            }
        }
    }
    
    fn partition<T: Ord>(arr: &mut [T]) -> usize {
        let len = arr.len();
        let pivot = len - 1;
        let mut store_index = 0;
        
        for i in 0..len - 1 {
            if arr[i] <= arr[pivot] {
                arr.swap(i, store_index);
                store_index += 1;
            }
        }
        
        arr.swap(store_index, pivot);
        store_index
    }
    
    // 并行混合排序
    fn parallel_hybrid_sort<T: Ord + Clone + Send + Sync>(arr: &mut [T]) {
        use rayon::prelude::*;
        
        const PARALLEL_THRESHOLD: usize = 1000;
        
        if arr.len() <= PARALLEL_THRESHOLD {
            Self::hybrid_quicksort(arr);
        } else {
            // 并行排序
            arr.par_sort_unstable();
        }
    }
}

fn sorting_optimization_example() {
    let mut data: Vec<i32> = (0..100000).rev().collect();
    let mut data2 = data.clone();
    let mut data3 = data.clone();
    
    let start = Instant::now();
    data.sort();
    let std_time = start.elapsed();
    
    let start = Instant::now();
    HybridSorter::hybrid_quicksort(&mut data2);
    let hybrid_time = start.elapsed();
    
    let start = Instant::now();
    HybridSorter::parallel_hybrid_sort(&mut data3);
    let parallel_time = start.elapsed();
    
    println!("标准排序: {:?}", std_time);
    println!("混合排序: {:?}", hybrid_time);
    println!("并行排序: {:?}", parallel_time);
}
```

### 3.2 基数排序优化

```rust
// 优化的基数排序
struct RadixSorter;

impl RadixSorter {
    fn radix_sort(arr: &mut [u32]) {
        let max_value = arr.iter().max().copied().unwrap_or(0);
        let max_digits = (max_value as f64).log10().ceil() as usize;
        
        for digit in 0..max_digits {
            Self::counting_sort_by_digit(arr, digit);
        }
    }
    
    fn counting_sort_by_digit(arr: &mut [u32], digit: usize) {
        let mut count = [0; 10];
        let mut output = vec![0; arr.len()];
        
        // 计算每个数字的出现次数
        for &num in arr.iter() {
            let digit_value = Self::get_digit(num, digit);
            count[digit_value] += 1;
        }
        
        // 计算累积和
        for i in 1..10 {
            count[i] += count[i - 1];
        }
        
        // 构建输出数组
        for &num in arr.iter().rev() {
            let digit_value = Self::get_digit(num, digit);
            let index = count[digit_value] - 1;
            output[index] = num;
            count[digit_value] -= 1;
        }
        
        // 复制回原数组
        arr.copy_from_slice(&output);
    }
    
    fn get_digit(num: u32, digit: usize) -> usize {
        ((num / 10u32.pow(digit as u32)) % 10) as usize
    }
    
    // 并行基数排序
    fn parallel_radix_sort(arr: &mut [u32]) {
        use rayon::prelude::*;
        
        const CHUNK_SIZE: usize = 1000;
        
        if arr.len() <= CHUNK_SIZE {
            Self::radix_sort(arr);
        } else {
            // 分块并行排序
            arr.par_chunks_mut(CHUNK_SIZE).for_each(|chunk| {
                Self::radix_sort(chunk);
            });
            
            // 合并排序结果
            Self::merge_sorted_chunks(arr, CHUNK_SIZE);
        }
    }
    
    fn merge_sorted_chunks(arr: &mut [u32], chunk_size: usize) {
        let mut temp = vec![0; arr.len()];
        let mut chunk_indices: Vec<usize> = (0..arr.len()).step_by(chunk_size).collect();
        
        for i in 0..arr.len() {
            let mut min_value = u32::MAX;
            let mut min_chunk = 0;
            
            for (chunk_idx, &start_idx) in chunk_indices.iter().enumerate() {
                if start_idx < arr.len() && arr[start_idx] < min_value {
                    min_value = arr[start_idx];
                    min_chunk = chunk_idx;
                }
            }
            
            temp[i] = min_value;
            chunk_indices[min_chunk] += 1;
        }
        
        arr.copy_from_slice(&temp);
    }
}

fn radix_sort_example() {
    let mut data: Vec<u32> = (0..100000).map(|_| rand::random::<u32>() % 1000000).collect();
    let mut data2 = data.clone();
    
    let start = Instant::now();
    data.sort();
    let std_time = start.elapsed();
    
    let start = Instant::now();
    RadixSorter::parallel_radix_sort(&mut data2);
    let radix_time = start.elapsed();
    
    println!("标准排序: {:?}", std_time);
    println!("并行基数排序: {:?}", radix_time);
}
```

## 4. 动态规划优化

### 4.1 记忆化优化

```rust
use std::collections::HashMap;

// 记忆化斐波那契
struct MemoizedFibonacci {
    cache: HashMap<u64, u64>,
}

impl MemoizedFibonacci {
    fn new() -> Self {
        MemoizedFibonacci {
            cache: HashMap::new(),
        }
    }
    
    fn fib(&mut self, n: u64) -> u64 {
        if let Some(&result) = self.cache.get(&n) {
            return result;
        }
        
        let result = match n {
            0 => 0,
            1 => 1,
            _ => self.fib(n - 1) + self.fib(n - 2),
        };
        
        self.cache.insert(n, result);
        result
    }
    
    fn fib_iterative(n: u64) -> u64 {
        if n <= 1 {
            return n;
        }
        
        let mut a = 0;
        let mut b = 1;
        
        for _ in 2..=n {
            let temp = a + b;
            a = b;
            b = temp;
        }
        
        b
    }
    
    fn fib_matrix(n: u64) -> u64 {
        if n <= 1 {
            return n;
        }
        
        let mut matrix = [[1, 1], [1, 0]];
        Self::matrix_power(&mut matrix, n - 1);
        matrix[0][0]
    }
    
    fn matrix_power(matrix: &mut [[u64; 2]; 2], n: u64) {
        if n == 0 || n == 1 {
            return;
        }
        
        Self::matrix_power(matrix, n / 2);
        Self::matrix_multiply(matrix, matrix);
        
        if n % 2 != 0 {
            let base = [[1, 1], [1, 0]];
            Self::matrix_multiply(matrix, &base);
        }
    }
    
    fn matrix_multiply(a: &mut [[u64; 2]; 2], b: &[[u64; 2]; 2]) {
        let mut result = [[0, 0], [0, 0]];
        
        for i in 0..2 {
            for j in 0..2 {
                for k in 0..2 {
                    result[i][j] += a[i][k] * b[k][j];
                }
            }
        }
        
        *a = result;
    }
}

fn fibonacci_optimization_example() {
    let n = 40;
    
    let start = Instant::now();
    let mut memoized = MemoizedFibonacci::new();
    let result1 = memoized.fib(n);
    let memoized_time = start.elapsed();
    
    let start = Instant::now();
    let result2 = MemoizedFibonacci::fib_iterative(n);
    let iterative_time = start.elapsed();
    
    let start = Instant::now();
    let result3 = MemoizedFibonacci::fib_matrix(n);
    let matrix_time = start.elapsed();
    
    println!("记忆化递归: {}, 时间: {:?}", result1, memoized_time);
    println!("迭代方法: {}, 时间: {:?}", result2, iterative_time);
    println!("矩阵方法: {}, 时间: {:?}", result3, matrix_time);
}
```

### 4.2 背包问题优化

```rust
// 0-1背包问题优化
struct KnapsackOptimizer;

impl KnapsackOptimizer {
    // 标准动态规划解法
    fn standard_knapsack(weights: &[u32], values: &[u32], capacity: u32) -> u32 {
        let n = weights.len();
        let mut dp = vec![vec![0; capacity as usize + 1]; n + 1];
        
        for i in 1..=n {
            for w in 0..=capacity as usize {
                if weights[i - 1] as usize <= w {
                    dp[i][w] = dp[i - 1][w].max(
                        dp[i - 1][w - weights[i - 1] as usize] + values[i - 1]
                    );
                } else {
                    dp[i][w] = dp[i - 1][w];
                }
            }
        }
        
        dp[n][capacity as usize]
    }
    
    // 空间优化版本
    fn optimized_knapsack(weights: &[u32], values: &[u32], capacity: u32) -> u32 {
        let mut dp = vec![0; capacity as usize + 1];
        
        for i in 0..weights.len() {
            for w in (weights[i] as usize..=capacity as usize).rev() {
                dp[w] = dp[w].max(dp[w - weights[i] as usize] + values[i]);
            }
        }
        
        dp[capacity as usize]
    }
    
    // 分支限界优化
    fn branch_and_bound_knapsack(weights: &[u32], values: &[u32], capacity: u32) -> u32 {
        let n = weights.len();
        let mut items: Vec<(u32, u32, f64)> = weights.iter()
            .zip(values.iter())
            .map(|(&w, &v)| (w, v, v as f64 / w as f64))
            .collect();
        
        // 按价值密度排序
        items.sort_by(|a, b| b.2.partial_cmp(&a.2).unwrap());
        
        let mut best_value = 0;
        let mut stack = vec![(0, 0, 0, 0)]; // (index, current_weight, current_value, bound)
        
        while let Some((index, current_weight, current_value, _)) = stack.pop() {
            if index >= n {
                best_value = best_value.max(current_value);
                continue;
            }
            
            let (weight, value, _) = items[index];
            
            // 不选择当前物品
            let bound = Self::calculate_bound(&items, index + 1, current_weight, current_value, capacity);
            if bound > best_value {
                stack.push((index + 1, current_weight, current_value, bound));
            }
            
            // 选择当前物品
            if current_weight + weight <= capacity {
                let new_weight = current_weight + weight;
                let new_value = current_value + value;
                let bound = Self::calculate_bound(&items, index + 1, new_weight, new_value, capacity);
                
                if bound > best_value {
                    stack.push((index + 1, new_weight, new_value, bound));
                }
            }
        }
        
        best_value
    }
    
    fn calculate_bound(items: &[(u32, u32, f64)], start: usize, weight: u32, value: u32, capacity: u32) -> u32 {
        let mut bound = value;
        let mut remaining_weight = capacity - weight;
        let mut i = start;
        
        while i < items.len() && remaining_weight >= items[i].0 {
            bound += items[i].1;
            remaining_weight -= items[i].0;
            i += 1;
        }
        
        if i < items.len() {
            bound += (remaining_weight as f64 * items[i].2) as u32;
        }
        
        bound
    }
}

fn knapsack_optimization_example() {
    let weights = vec![2, 3, 4, 5];
    let values = vec![3, 4, 5, 6];
    let capacity = 10;
    
    let start = Instant::now();
    let result1 = KnapsackOptimizer::standard_knapsack(&weights, &values, capacity);
    let standard_time = start.elapsed();
    
    let start = Instant::now();
    let result2 = KnapsackOptimizer::optimized_knapsack(&weights, &values, capacity);
    let optimized_time = start.elapsed();
    
    let start = Instant::now();
    let result3 = KnapsackOptimizer::branch_and_bound_knapsack(&weights, &values, capacity);
    let branch_time = start.elapsed();
    
    println!("标准动态规划: {}, 时间: {:?}", result1, standard_time);
    println!("空间优化: {}, 时间: {:?}", result2, optimized_time);
    println!("分支限界: {}, 时间: {:?}", result3, branch_time);
}
```

## 5. 图算法优化

### 5.1 最短路径优化

```rust
use std::collections::{BinaryHeap, HashMap};
use std::cmp::Ordering;

// 优化的Dijkstra算法
struct OptimizedDijkstra;

impl OptimizedDijkstra {
    #[derive(Copy, Clone, Eq, PartialEq)]
    struct State {
        cost: u32,
        position: usize,
    }
    
    impl Ord for State {
        fn cmp(&self, other: &Self) -> Ordering {
            other.cost.cmp(&self.cost)
        }
    }
    
    impl PartialOrd for State {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    
    fn dijkstra(graph: &[Vec<(usize, u32)>], start: usize) -> Vec<u32> {
        let mut distances = vec![u32::MAX; graph.len()];
        distances[start] = 0;
        
        let mut heap = BinaryHeap::new();
        heap.push(State { cost: 0, position: start });
        
        while let Some(State { cost, position }) = heap.pop() {
            if cost > distances[position] {
                continue;
            }
            
            for &(next, weight) in &graph[position] {
                let next_cost = cost + weight;
                if next_cost < distances[next] {
                    distances[next] = next_cost;
                    heap.push(State { cost: next_cost, position: next });
                }
            }
        }
        
        distances
    }
    
    // A*算法
    fn astar(graph: &[Vec<(usize, u32)>], start: usize, goal: usize, heuristic: &[u32]) -> Option<Vec<usize>> {
        let mut open_set = BinaryHeap::new();
        let mut came_from = HashMap::new();
        let mut g_score = vec![u32::MAX; graph.len()];
        let mut f_score = vec![u32::MAX; graph.len()];
        
        g_score[start] = 0;
        f_score[start] = heuristic[start];
        open_set.push(State { cost: f_score[start], position: start });
        
        while let Some(State { cost: _, position }) = open_set.pop() {
            if position == goal {
                return Some(Self::reconstruct_path(&came_from, start, goal));
            }
            
            for &(neighbor, weight) in &graph[position] {
                let tentative_g_score = g_score[position] + weight;
                
                if tentative_g_score < g_score[neighbor] {
                    came_from.insert(neighbor, position);
                    g_score[neighbor] = tentative_g_score;
                    f_score[neighbor] = g_score[neighbor] + heuristic[neighbor];
                    open_set.push(State { cost: f_score[neighbor], position: neighbor });
                }
            }
        }
        
        None
    }
    
    fn reconstruct_path(came_from: &HashMap<usize, usize>, start: usize, goal: usize) -> Vec<usize> {
        let mut path = vec![goal];
        let mut current = goal;
        
        while current != start {
            current = came_from[&current];
            path.push(current);
        }
        
        path.reverse();
        path
    }
}

fn graph_optimization_example() {
    // 创建测试图
    let graph = vec![
        vec![(1, 4), (2, 2)],           // 0 -> 1(4), 0 -> 2(2)
        vec![(2, 1), (3, 5)],           // 1 -> 2(1), 1 -> 3(5)
        vec![(3, 8), (4, 10)],          // 2 -> 3(8), 2 -> 4(10)
        vec![(4, 2)],                   // 3 -> 4(2)
        vec![],                         // 4 (终点)
    ];
    
    let heuristic = vec![8, 6, 4, 2, 0]; // 到目标的估计距离
    
    let start = Instant::now();
    let distances = OptimizedDijkstra::dijkstra(&graph, 0);
    let dijkstra_time = start.elapsed();
    
    let start = Instant::now();
    let path = OptimizedDijkstra::astar(&graph, 0, 4, &heuristic);
    let astar_time = start.elapsed();
    
    println!("Dijkstra距离: {:?}, 时间: {:?}", distances, dijkstra_time);
    println!("A*路径: {:?}, 时间: {:?}", path, astar_time);
}
```

## 6. 形式化证明

### 6.1 算法正确性定理

**定理**: 优化算法保持原算法的正确性。

**证明**: 通过不变式证明优化前后算法的等价性。

### 6.2 性能优化定理

**定理**: 算法优化提高执行效率。

**证明**: 通过复杂度分析证明优化后的算法具有更好的时间复杂度。

## 7. 工程实践

### 7.1 最佳实践

1. 选择合适的算法和数据结构
2. 使用记忆化避免重复计算
3. 采用并行算法提高性能
4. 优化内存使用和缓存友好性

### 7.2 常见陷阱

1. 过早优化
2. 忽略算法复杂度
3. 过度工程化
4. 忽视实际性能测试

## 8. 交叉引用

- [内存优化技术](./09_memory_optimization.md) - 内存优化技术
- [并发编程模式](./08_parallel_patterns.md) - 并发编程模式
- [性能影响分析](./09_performance_impact.md) - 性能影响分析

## 9. 参考文献

1. Algorithm Design and Analysis
2. Optimization Techniques
3. Dynamic Programming
4. Graph Algorithms
