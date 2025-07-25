# 基础算法与复杂度分析

## 概述

算法是计算机科学的核心，而复杂度分析是评估算法效率的关键工具。Rust 通过类型安全的抽象和零成本抽象，为算法实现提供了强大的基础。本章深入探讨算法复杂度分析、基础排序算法、搜索算法以及递归与分治技术。

## 算法复杂度分析

### 时间复杂度

时间复杂度描述了算法执行时间随输入规模增长的变化趋势。

```rust
use std::time::{Duration, Instant};

// 时间复杂度分析工具
struct ComplexityAnalyzer {
    measurements: Vec<(usize, Duration)>,
}

impl ComplexityAnalyzer {
    fn new() -> Self {
        ComplexityAnalyzer {
            measurements: Vec::new(),
        }
    }
    
    fn measure<T, F>(&mut self, input_size: usize, algorithm: F) -> Duration
    where
        F: FnOnce() -> T,
    {
        let start = Instant::now();
        algorithm();
        let duration = start.elapsed();
        self.measurements.push((input_size, duration));
        duration
    }
    
    fn analyze_complexity(&self) -> String {
        if self.measurements.len() < 2 {
            return "Insufficient data".to_string();
        }
        
        // 简单的复杂度分析
        let first = self.measurements[0];
        let last = self.measurements.last().unwrap();
        let ratio = last.1.as_nanos() as f64 / first.1.as_nanos() as f64;
        let size_ratio = last.0 as f64 / first.0 as f64;
        
        if ratio < size_ratio * 1.5 {
            "O(1) - Constant time".to_string()
        } else if ratio < size_ratio * size_ratio * 1.5 {
            "O(n) - Linear time".to_string()
        } else if ratio < size_ratio * size_ratio * size_ratio * 1.5 {
            "O(n²) - Quadratic time".to_string()
        } else {
            "O(n³) or higher - Polynomial time".to_string()
        }
    }
}

// 示例：分析不同复杂度的算法
fn complexity_examples() {
    let mut analyzer = ComplexityAnalyzer::new();
    
    // O(1) - 常数时间
    analyzer.measure(1000, || {
        let _ = 42 + 42;
    });
    
    // O(n) - 线性时间
    analyzer.measure(1000, || {
        let vec: Vec<i32> = (0..1000).collect();
        let _ = vec.iter().sum::<i32>();
    });
    
    // O(n²) - 二次时间
    analyzer.measure(100, || {
        let vec: Vec<i32> = (0..100).collect();
        for i in &vec {
            for j in &vec {
                let _ = i + j;
            }
        }
    });
    
    println!("Complexity analysis: {}", analyzer.analyze_complexity());
}
```

### 空间复杂度

空间复杂度描述了算法执行过程中所需内存空间的变化。

```rust
use std::mem;

struct SpaceAnalyzer {
    measurements: Vec<(usize, usize)>,
}

impl SpaceAnalyzer {
    fn new() -> Self {
        SpaceAnalyzer {
            measurements: Vec::new(),
        }
    }
    
    fn measure_space<T>(&mut self, input_size: usize, algorithm: impl FnOnce() -> T) -> usize {
        let initial_memory = get_memory_usage();
        let _result = algorithm();
        let final_memory = get_memory_usage();
        let memory_used = final_memory - initial_memory;
        self.measurements.push((input_size, memory_used));
        memory_used
    }
}

fn get_memory_usage() -> usize {
    // 简化的内存使用量获取
    // 在实际应用中，这里应该使用更精确的内存测量方法
    0
}

// 空间复杂度示例
fn space_complexity_examples() {
    let mut analyzer = SpaceAnalyzer::new();
    
    // O(1) - 常数空间
    analyzer.measure_space(1000, || {
        let mut sum = 0;
        for i in 0..1000 {
            sum += i;
        }
        sum
    });
    
    // O(n) - 线性空间
    analyzer.measure_space(1000, || {
        let vec: Vec<i32> = (0..1000).collect();
        vec
    });
    
    // O(n²) - 二次空间
    analyzer.measure_space(100, || {
        let matrix: Vec<Vec<i32>> = (0..100)
            .map(|_| (0..100).collect())
            .collect();
        matrix
    });
}
```

## 基础排序算法

### 冒泡排序

```rust
fn bubble_sort<T: Ord>(arr: &mut [T]) {
    let len = arr.len();
    for i in 0..len {
        let mut swapped = false;
        for j in 0..len - i - 1 {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
                swapped = true;
            }
        }
        if !swapped {
            break; // 优化：如果没有交换，说明已经排序完成
        }
    }
}

// 泛型版本的冒泡排序
struct BubbleSorter;

impl BubbleSorter {
    fn sort<T: Ord>(arr: &mut [T]) {
        bubble_sort(arr);
    }
    
    fn sort_by<T, F>(arr: &mut [T], compare: F)
    where
        F: Fn(&T, &T) -> std::cmp::Ordering,
    {
        let len = arr.len();
        for i in 0..len {
            let mut swapped = false;
            for j in 0..len - i - 1 {
                if compare(&arr[j], &arr[j + 1]) == std::cmp::Ordering::Greater {
                    arr.swap(j, j + 1);
                    swapped = true;
                }
            }
            if !swapped {
                break;
            }
        }
    }
}
```

### 选择排序

```rust
fn selection_sort<T: Ord>(arr: &mut [T]) {
    let len = arr.len();
    for i in 0..len {
        let mut min_idx = i;
        for j in i + 1..len {
            if arr[j] < arr[min_idx] {
                min_idx = j;
            }
        }
        if min_idx != i {
            arr.swap(i, min_idx);
        }
    }
}

// 选择排序的泛型实现
struct SelectionSorter;

impl SelectionSorter {
    fn sort<T: Ord>(arr: &mut [T]) {
        selection_sort(arr);
    }
    
    fn sort_by<T, F>(arr: &mut [T], compare: F)
    where
        F: Fn(&T, &T) -> std::cmp::Ordering,
    {
        let len = arr.len();
        for i in 0..len {
            let mut min_idx = i;
            for j in i + 1..len {
                if compare(&arr[j], &arr[min_idx]) == std::cmp::Ordering::Less {
                    min_idx = j;
                }
            }
            if min_idx != i {
                arr.swap(i, min_idx);
            }
        }
    }
}
```

### 插入排序

```rust
fn insertion_sort<T: Ord>(arr: &mut [T]) {
    for i in 1..arr.len() {
        let mut j = i;
        while j > 0 && arr[j - 1] > arr[j] {
            arr.swap(j - 1, j);
            j -= 1;
        }
    }
}

// 插入排序的泛型实现
struct InsertionSorter;

impl InsertionSorter {
    fn sort<T: Ord>(arr: &mut [T]) {
        insertion_sort(arr);
    }
    
    fn sort_by<T, F>(arr: &mut [T], compare: F)
    where
        F: Fn(&T, &T) -> std::cmp::Ordering,
    {
        for i in 1..arr.len() {
            let mut j = i;
            while j > 0 && compare(&arr[j - 1], &arr[j]) == std::cmp::Ordering::Greater {
                arr.swap(j - 1, j);
                j -= 1;
            }
        }
    }
}
```

### 快速排序

```rust
fn quick_sort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let pivot_index = partition(arr);
    quick_sort(&mut arr[..pivot_index]);
    quick_sort(&mut arr[pivot_index + 1..]);
}

fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let len = arr.len();
    let pivot_index = len - 1;
    let pivot = &arr[pivot_index];
    
    let mut i = 0;
    for j in 0..len - 1 {
        if arr[j] <= *pivot {
            arr.swap(i, j);
            i += 1;
        }
    }
    
    arr.swap(i, pivot_index);
    i
}

// 快速排序的泛型实现
struct QuickSorter;

impl QuickSorter {
    fn sort<T: Ord>(arr: &mut [T]) {
        quick_sort(arr);
    }
    
    fn sort_by<T, F>(arr: &mut [T], compare: F)
    where
        F: Fn(&T, &T) -> std::cmp::Ordering + Copy,
    {
        if arr.len() <= 1 {
            return;
        }
        
        let pivot_index = Self::partition_by(arr, compare);
        Self::sort_by(&mut arr[..pivot_index], compare);
        Self::sort_by(&mut arr[pivot_index + 1..], compare);
    }
    
    fn partition_by<T, F>(arr: &mut [T], compare: F) -> usize
    where
        F: Fn(&T, &T) -> std::cmp::Ordering,
    {
        let len = arr.len();
        let pivot_index = len - 1;
        
        let mut i = 0;
        for j in 0..len - 1 {
            if compare(&arr[j], &arr[pivot_index]) != std::cmp::Ordering::Greater {
                arr.swap(i, j);
                i += 1;
            }
        }
        
        arr.swap(i, pivot_index);
        i
    }
}
```

## 搜索算法

### 线性搜索

```rust
fn linear_search<T: PartialEq>(arr: &[T], target: &T) -> Option<usize> {
    for (index, item) in arr.iter().enumerate() {
        if item == target {
            return Some(index);
        }
    }
    None
}

// 泛型线性搜索
struct LinearSearcher;

impl LinearSearcher {
    fn search<T: PartialEq>(arr: &[T], target: &T) -> Option<usize> {
        linear_search(arr, target)
    }
    
    fn search_by<T, F>(arr: &[T], target: &T, predicate: F) -> Option<usize>
    where
        F: Fn(&T, &T) -> bool,
    {
        for (index, item) in arr.iter().enumerate() {
            if predicate(item, target) {
                return Some(index);
            }
        }
        None
    }
}
```

### 二分搜索

```rust
fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
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

// 泛型二分搜索
struct BinarySearcher;

impl BinarySearcher {
    fn search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
        binary_search(arr, target)
    }
    
    fn search_by<T, F>(arr: &[T], target: &T, compare: F) -> Option<usize>
    where
        F: Fn(&T, &T) -> std::cmp::Ordering,
    {
        let mut left = 0;
        let mut right = arr.len();
        
        while left < right {
            let mid = left + (right - left) / 2;
            match compare(&arr[mid], target) {
                std::cmp::Ordering::Equal => return Some(mid),
                std::cmp::Ordering::Less => left = mid + 1,
                std::cmp::Ordering::Greater => right = mid,
            }
        }
        
        None
    }
    
    fn lower_bound<T: Ord>(arr: &[T], target: &T) -> usize {
        let mut left = 0;
        let mut right = arr.len();
        
        while left < right {
            let mid = left + (right - left) / 2;
            if arr[mid] < *target {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        
        left
    }
    
    fn upper_bound<T: Ord>(arr: &[T], target: &T) -> usize {
        let mut left = 0;
        let mut right = arr.len();
        
        while left < right {
            let mid = left + (right - left) / 2;
            if arr[mid] <= *target {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        
        left
    }
}
```

## 递归与分治

### 递归基础

```rust
// 递归阶乘计算
fn factorial(n: u64) -> u64 {
    match n {
        0 | 1 => 1,
        _ => n * factorial(n - 1),
    }
}

// 尾递归优化的阶乘
fn factorial_tail_recursive(n: u64) -> u64 {
    fn factorial_helper(n: u64, acc: u64) -> u64 {
        match n {
            0 | 1 => acc,
            _ => factorial_helper(n - 1, n * acc),
        }
    }
    factorial_helper(n, 1)
}

// 斐波那契数列
fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

// 记忆化斐波那契
fn fibonacci_memoized(n: u64) -> u64 {
    use std::collections::HashMap;
    use std::sync::Mutex;
    use std::sync::Arc;
    
    static MEMO: std::sync::OnceLock<Arc<Mutex<HashMap<u64, u64>>>> = std::sync::OnceLock::new();
    
    let memo = MEMO.get_or_init(|| Arc::new(Mutex::new(HashMap::new())));
    
    if let Some(&result) = memo.lock().unwrap().get(&n) {
        return result;
    }
    
    let result = match n {
        0 => 0,
        1 => 1,
        _ => fibonacci_memoized(n - 1) + fibonacci_memoized(n - 2),
    };
    
    memo.lock().unwrap().insert(n, result);
    result
}
```

### 分治算法

```rust
// 归并排序 - 经典分治算法
fn merge_sort<T: Ord + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let mid = arr.len() / 2;
    let (left, right) = arr.split_at_mut(mid);
    
    merge_sort(left);
    merge_sort(right);
    
    merge(arr, left, right);
}

fn merge<T: Ord + Clone>(arr: &mut [T], left: &[T], right: &[T]) {
    let mut result = Vec::with_capacity(arr.len());
    let mut left_idx = 0;
    let mut right_idx = 0;
    
    while left_idx < left.len() && right_idx < right.len() {
        if left[left_idx] <= right[right_idx] {
            result.push(left[left_idx].clone());
            left_idx += 1;
        } else {
            result.push(right[right_idx].clone());
            right_idx += 1;
        }
    }
    
    // 添加剩余元素
    result.extend_from_slice(&left[left_idx..]);
    result.extend_from_slice(&right[right_idx..]);
    
    arr.copy_from_slice(&result);
}

// 分治算法的泛型框架
struct DivideAndConquer<T> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T> DivideAndConquer<T> {
    fn solve<F, G, H>(arr: &mut [T], base_case: F, divide: G, conquer: H)
    where
        F: Fn(&[T]) -> bool,
        G: Fn(&mut [T]) -> Vec<&mut [T]>,
        H: Fn(&mut [T], Vec<&mut [T]>),
    {
        if base_case(arr) {
            return;
        }
        
        let sub_problems = divide(arr);
        for sub_problem in &sub_problems {
            Self::solve(sub_problem, &base_case, &divide, &conquer);
        }
        
        conquer(arr, sub_problems);
    }
}
```

### 分治应用实例

```rust
// 最大子数组和 - 分治解法
fn max_subarray_sum_dc(arr: &[i32]) -> i32 {
    if arr.is_empty() {
        return 0;
    }
    
    fn max_subarray_helper(arr: &[i32], left: usize, right: usize) -> (i32, i32, i32, i32) {
        if left == right {
            return (arr[left], arr[left], arr[left], arr[left]);
        }
        
        let mid = left + (right - left) / 2;
        let (left_sum, left_max, left_min, left_total) = max_subarray_helper(arr, left, mid);
        let (right_sum, right_max, right_min, right_total) = max_subarray_helper(arr, mid + 1, right);
        
        let cross_sum = left_max + right_min;
        let total_sum = left_total + right_total;
        let max_sum = left_sum.max(right_sum).max(cross_sum);
        let max_prefix = left_max.max(left_total + right_max);
        let min_prefix = left_min.min(left_total + right_min);
        
        (max_sum, max_prefix, min_prefix, total_sum)
    }
    
    let (result, _, _, _) = max_subarray_helper(arr, 0, arr.len() - 1);
    result
}

// 最近点对问题 - 分治解法
#[derive(Debug, Clone, Copy)]
struct Point {
    x: f64,
    y: f64,
}

impl Point {
    fn distance(&self, other: &Point) -> f64 {
        ((self.x - other.x).powi(2) + (self.y - other.y).powi(2)).sqrt()
    }
}

fn closest_pair(points: &[Point]) -> Option<(Point, Point)> {
    if points.len() < 2 {
        return None;
    }
    
    let mut sorted_points = points.to_vec();
    sorted_points.sort_by(|a, b| a.x.partial_cmp(&b.x).unwrap());
    
    fn closest_pair_helper(points: &[Point]) -> (f64, Option<(Point, Point)>) {
        if points.len() <= 3 {
            let mut min_dist = f64::INFINITY;
            let mut closest_pair = None;
            
            for i in 0..points.len() {
                for j in i + 1..points.len() {
                    let dist = points[i].distance(&points[j]);
                    if dist < min_dist {
                        min_dist = dist;
                        closest_pair = Some((points[i], points[j]));
                    }
                }
            }
            
            return (min_dist, closest_pair);
        }
        
        let mid = points.len() / 2;
        let (left_dist, left_pair) = closest_pair_helper(&points[..mid]);
        let (right_dist, right_pair) = closest_pair_helper(&points[mid..]);
        
        let mut min_dist = left_dist.min(right_dist);
        let mut best_pair = if left_dist <= right_dist { left_pair } else { right_pair };
        
        // 检查跨越中线的点对
        let mid_x = points[mid].x;
        let strip: Vec<Point> = points
            .iter()
            .filter(|p| (p.x - mid_x).abs() < min_dist)
            .cloned()
            .collect();
        
        for i in 0..strip.len() {
            for j in i + 1..strip.len().min(i + 7) {
                let dist = strip[i].distance(&strip[j]);
                if dist < min_dist {
                    min_dist = dist;
                    best_pair = Some((strip[i], strip[j]));
                }
            }
        }
        
        (min_dist, best_pair)
    }
    
    let (_, result) = closest_pair_helper(&sorted_points);
    result
}
```

## 总结

基础算法是计算机科学的基石，而 Rust 的类型系统为零成本抽象提供了强大支持。通过复杂度分析，我们可以评估算法的效率；通过基础排序和搜索算法，我们掌握了算法设计的基本模式；通过递归与分治，我们学会了将复杂问题分解为简单子问题的技术。

### 关键要点

1. **复杂度分析** - 理解时间和空间复杂度是算法设计的基础
2. **排序算法** - 掌握不同排序算法的特点和适用场景
3. **搜索算法** - 理解线性搜索和二分搜索的优缺点
4. **递归分治** - 学会将复杂问题分解为简单子问题

### 下一步

在下一章中，我们将探讨数据结构与实现，包括线性数据结构、树形数据结构、图数据结构和哈希表与映射。
