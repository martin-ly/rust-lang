//! # 同步排序算法实现
//!
//! 本模块实现了各种同步排序算法，提供传统的单线程排序实现。
//! 适用于小到中等规模的数据排序。

use super::*;
use crate::algorithms::execution_modes::SyncAlgorithm;
//use std::cmp::Ordering;

/// 快速排序算法
pub struct QuickSort;

impl SyncAlgorithm<Vec<i32>, Vec<i32>> for QuickSort {
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        let len = input.len();
        if len > 0 {
            quick_sort_recursive(&mut input, 0, len - 1);
        }
        Ok(input)
    }
}

impl SyncSortingAlgorithm for QuickSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::QuickSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n²)", "O(log n)", false, true)
    }
}

/// 快速排序递归实现
fn quick_sort_recursive(arr: &mut [i32], low: usize, high: usize) {
    if low < high {
        let pi = partition(arr, low, high);
        if pi > 0 {
            quick_sort_recursive(arr, low, pi - 1);
        }
        if pi < high {
            quick_sort_recursive(arr, pi + 1, high);
        }
    }
}

/// 分区函数
fn partition(arr: &mut [i32], low: usize, high: usize) -> usize {
    let pivot = arr[high];
    let mut i = low;

    for j in low..high {
        if arr[j] <= pivot {
            arr.swap(i, j);
            i += 1;
        }
    }

    arr.swap(i, high);
    i
}

/// 归并排序算法
pub struct MergeSort;

impl SyncAlgorithm<Vec<i32>, Vec<i32>> for MergeSort {
    fn execute(&self, input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        let mut arr = input;
        merge_sort_recursive(&mut arr);
        Ok(arr)
    }
}

impl SyncSortingAlgorithm for MergeSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::MergeSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n log n)", "O(n)", true, false)
    }
}

/// 归并排序递归实现
fn merge_sort_recursive(arr: &mut [i32]) {
    if arr.len() <= 1 {
        return;
    }

    let mid = arr.len() / 2;
    let (left, right) = arr.split_at_mut(mid);

    merge_sort_recursive(left);
    merge_sort_recursive(right);

    merge(arr, mid);
}

/// 归并函数
fn merge(arr: &mut [i32], mid: usize) {
    let left = arr[..mid].to_vec();
    let right = arr[mid..].to_vec();

    let mut i = 0;
    let mut j = 0;
    let mut k = 0;

    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            arr[k] = left[i];
            i += 1;
        } else {
            arr[k] = right[j];
            j += 1;
        }
        k += 1;
    }

    while i < left.len() {
        arr[k] = left[i];
        i += 1;
        k += 1;
    }

    while j < right.len() {
        arr[k] = right[j];
        j += 1;
        k += 1;
    }
}

/// 堆排序算法
pub struct HeapSort;

impl SyncAlgorithm<Vec<i32>, Vec<i32>> for HeapSort {
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        heap_sort(&mut input);
        Ok(input)
    }
}

impl SyncSortingAlgorithm for HeapSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::HeapSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n log n)", "O(1)", false, true)
    }
}

/// 堆排序实现
fn heap_sort(arr: &mut [i32]) {
    let n = arr.len();

    // 构建最大堆
    for i in (0..n / 2).rev() {
        heapify(arr, n, i);
    }

    // 逐个提取元素
    for i in (1..n).rev() {
        arr.swap(0, i);
        heapify(arr, i, 0);
    }
}

/// 堆化函数
fn heapify(arr: &mut [i32], n: usize, i: usize) {
    let mut largest = i;
    let left = 2 * i + 1;
    let right = 2 * i + 2;

    if left < n && arr[left] > arr[largest] {
        largest = left;
    }

    if right < n && arr[right] > arr[largest] {
        largest = right;
    }

    if largest != i {
        arr.swap(i, largest);
        heapify(arr, n, largest);
    }
}

/// 插入排序算法
pub struct InsertionSort;

impl SyncAlgorithm<Vec<i32>, Vec<i32>> for InsertionSort {
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        insertion_sort(&mut input);
        Ok(input)
    }
}

impl SyncSortingAlgorithm for InsertionSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::InsertionSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n)", "O(n²)", "O(n²)", "O(1)", true, true)
    }
}

/// 插入排序实现
fn insertion_sort(arr: &mut [i32]) {
    for i in 1..arr.len() {
        let key = arr[i];
        let mut j = i;

        while j > 0 && arr[j - 1] > key {
            arr[j] = arr[j - 1];
            j -= 1;
        }

        arr[j] = key;
    }
}

/// 选择排序算法
pub struct SelectionSort;

impl SyncAlgorithm<Vec<i32>, Vec<i32>> for SelectionSort {
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        selection_sort(&mut input);
        Ok(input)
    }
}

impl SyncSortingAlgorithm for SelectionSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::SelectionSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n²)", "O(n²)", "O(n²)", "O(1)", false, true)
    }
}

/// 选择排序实现
fn selection_sort(arr: &mut [i32]) {
    for i in 0..arr.len() - 1 {
        let mut min_idx = i;

        for j in i + 1..arr.len() {
            if arr[j] < arr[min_idx] {
                min_idx = j;
            }
        }

        if min_idx != i {
            arr.swap(i, min_idx);
        }
    }
}

/// 冒泡排序算法
pub struct BubbleSort;

impl SyncAlgorithm<Vec<i32>, Vec<i32>> for BubbleSort {
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        bubble_sort(&mut input);
        Ok(input)
    }
}

impl SyncSortingAlgorithm for BubbleSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::BubbleSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n)", "O(n²)", "O(n²)", "O(1)", true, true)
    }
}

/// 冒泡排序实现
fn bubble_sort(arr: &mut [i32]) {
    let n = arr.len();

    for i in 0..n {
        let mut swapped = false;

        for j in 0..n - i - 1 {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
                swapped = true;
            }
        }

        if !swapped {
            break;
        }
    }
}

/// 基数排序算法
pub struct RadixSort;

impl SyncAlgorithm<Vec<i32>, Vec<i32>> for RadixSort {
    fn execute(&self, input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        let mut arr = input;
        radix_sort(&mut arr);
        Ok(arr)
    }
}

impl SyncSortingAlgorithm for RadixSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::RadixSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(d(n+k))", "O(d(n+k))", "O(d(n+k))", "O(n+k)", true, false)
    }
}

/// 基数排序实现
fn radix_sort(arr: &mut [i32]) {
    let max = *arr.iter().max().unwrap_or(&0);
    let mut exp = 1;

    while max / exp > 0 {
        counting_sort_by_digit(arr, exp);
        exp *= 10;
    }
}

/// 按位计数排序
fn counting_sort_by_digit(arr: &mut [i32], exp: i32) {
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
    for i in (0..n).rev() {
        let digit = ((arr[i] / exp) % 10) as usize;
        output[count[digit] - 1] = arr[i];
        count[digit] -= 1;
    }

    // 复制回原数组
    arr[..n].copy_from_slice(&output[..n]);
}

/// 计数排序算法
pub struct CountingSort;

impl SyncAlgorithm<Vec<i32>, Vec<i32>> for CountingSort {
    fn execute(&self, input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        let mut arr = input;
        counting_sort(&mut arr);
        Ok(arr)
    }
}

impl SyncSortingAlgorithm for CountingSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::CountingSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n+k)", "O(n+k)", "O(n+k)", "O(k)", true, false)
    }
}

/// 计数排序实现
fn counting_sort(arr: &mut [i32]) {
    let max = *arr.iter().max().unwrap_or(&0);
    let min = *arr.iter().min().unwrap_or(&0);
    let range = (max - min + 1) as usize;

    let mut count = vec![0; range];
    let mut output = vec![0; arr.len()];

    // 统计每个数字的出现次数
    for &num in arr.iter() {
        count[(num - min) as usize] += 1;
    }

    // 计算累积计数
    for i in 1..range {
        count[i] += count[i - 1];
    }

    // 构建输出数组
    for i in (0..arr.len()).rev() {
        let index = (arr[i] - min) as usize;
        output[count[index] - 1] = arr[i];
        count[index] -= 1;
    }

    // 复制回原数组
    arr.copy_from_slice(&output[..arr.len()]);
}

/// 桶排序算法
pub struct BucketSort;

impl SyncAlgorithm<Vec<i32>, Vec<i32>> for BucketSort {
    fn execute(&self, input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        let mut arr = input;
        bucket_sort(&mut arr);
        Ok(arr)
    }
}

impl SyncSortingAlgorithm for BucketSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::BucketSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n+k)", "O(n+k)", "O(n²)", "O(n)", true, false)
    }
}

/// 桶排序实现
fn bucket_sort(arr: &mut [i32]) {
    let n = arr.len();
    if n == 0 {
        return;
    }

    let max = *arr.iter().max().unwrap_or(&0);
    let min = *arr.iter().min().unwrap_or(&0);
    let range = max - min + 1;

    let bucket_count = n;
    let bucket_size = (range as f64 / bucket_count as f64).ceil() as i32;

    let mut buckets: Vec<Vec<i32>> = vec![Vec::new(); bucket_count];

    // 将元素分配到桶中
    for &num in arr.iter() {
        let bucket_index = ((num - min) / bucket_size).min(bucket_count as i32 - 1) as usize;
        buckets[bucket_index].push(num);
    }

    // 对每个桶进行排序
    for bucket in buckets.iter_mut() {
        bucket.sort();
    }

    // 合并桶中的元素
    let mut index = 0;
    for bucket in buckets {
        for num in bucket {
            arr[index] = num;
            index += 1;
        }
    }
}

/// TimSort 算法
pub struct TimSort;

impl SyncAlgorithm<Vec<i32>, Vec<i32>> for TimSort {
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        tim_sort(&mut input);
        Ok(input)
    }
}

impl SyncSortingAlgorithm for TimSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::TimSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n)", "O(n log n)", "O(n log n)", "O(n)", true, false)
    }
}

/// TimSort 实现
fn tim_sort(arr: &mut [i32]) {
    const MIN_MERGE: usize = 32;

    let n = arr.len();
    if n < MIN_MERGE {
        insertion_sort(arr);
        return;
    }

    // 计算最小运行长度
    let mut _min_run = MIN_MERGE;
    let mut n = n;
    while n >= 64 {
        n |= n & 1;
        n >>= 1;
    }
    _min_run = n + 1;

    // 找到运行并合并
    let mut runs = Vec::new();
    let mut i = 0;

    while i < arr.len() {
        let run_start = i;
        let mut run_end = i + 1;

        // 扩展运行
        while run_end < arr.len() && arr[run_end - 1] <= arr[run_end] {
            run_end += 1;
        }

        // 如果运行是递减的，反转它
        if run_end - run_start > 1 && arr[run_start] > arr[run_end - 1] {
            // Rust 1.92.0: 可以使用 rotate_right 进行更高效的操作
            // 对于 reverse，保持使用 reverse 方法
            arr[run_start..run_end].reverse();
        }

        // 如果运行太短，扩展它
        if run_end - run_start < _min_run {
            let extend_to = (run_start + _min_run).min(arr.len());
            insertion_sort(&mut arr[run_start..extend_to]);
            run_end = extend_to;
        }

        runs.push((run_start, run_end));
        i = run_end;
    }

    // 合并运行
    while runs.len() > 1 {
        let mut new_runs = Vec::new();
        let mut i = 0;

        while i < runs.len() {
            if i + 1 < runs.len() {
                let (start1, end1) = runs[i];
                let (start2, end2) = runs[i + 1];

                merge_runs(arr, start1, end1, start2, end2);
                new_runs.push((start1, end2));
                i += 2;
            } else {
                new_runs.push(runs[i]);
                i += 1;
            }
        }

        runs = new_runs;
    }
}

/// 合并两个运行
fn merge_runs(arr: &mut [i32], start1: usize, end1: usize, start2: usize, end2: usize) {
    let left = arr[start1..end1].to_vec();
    let right = arr[start2..end2].to_vec();

    let mut i = 0;
    let mut j = 0;
    let mut k = start1;

    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            arr[k] = left[i];
            i += 1;
        } else {
            arr[k] = right[j];
            j += 1;
        }
        k += 1;
    }

    while i < left.len() {
        arr[k] = left[i];
        i += 1;
        k += 1;
    }

    while j < right.len() {
        arr[k] = right[j];
        j += 1;
        k += 1;
    }
}
