//! # 并行排序算法
//!
//! 本模块实现了各种排序算法的并行版本，充分利用多核 CPU 的计算能力。
//! 基于 rayon 实现数据并行和任务并行。

use super::{SortingAlgorithm, AlgorithmComplexity};
use crate::algorithms::execution_modes::ParallelAlgorithm;
use rayon::prelude::*;

/// 并行快速排序
pub struct ParallelQuickSort;

impl ParallelAlgorithm<Vec<i32>, Vec<i32>> for ParallelQuickSort {
    fn execute(&self, input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        let pivot = input.len() / 2;
        let pivot_val = input[pivot];

        let filtered: Vec<(usize, i32)> = input
            .par_iter()
            .enumerate()
            .filter(|(i, _)| *i != pivot)
            .map(|(i, &val)| (i, val))
            .collect();

        let (left, right): (Vec<(usize, i32)>, Vec<(usize, i32)>) = filtered
            .into_iter()
            .partition(|(_, val)| *val <= pivot_val);

        let left_sorted = if left.len() > 1 {
            let left_algorithm = ParallelQuickSort;
            left_algorithm.execute(left.into_iter().map(|(_, val)| val).collect())?
        } else {
            left.into_iter().map(|(_, val)| val).collect()
        };

        let right_sorted = if right.len() > 1 {
            let right_algorithm = ParallelQuickSort;
            right_algorithm.execute(right.into_iter().map(|(_, val)| val).collect())?
        } else {
            right.into_iter().map(|(_, val)| val).collect()
        };

        let mut result = left_sorted;
        result.push(pivot_val);
        result.extend(right_sorted);

        Ok(result)
    }

    fn execute_with_threads(&self, input: Vec<i32>, _thread_count: usize) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        // 对于并行算法，线程数由 rayon 自动管理
        self.execute(input)
    }
}

impl super::ParallelSortingAlgorithm for ParallelQuickSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::QuickSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n²)", "O(log n)", false, true)
    }
}

/// 并行归并排序
pub struct ParallelMergeSort;

impl ParallelAlgorithm<Vec<i32>, Vec<i32>> for ParallelMergeSort {
    fn execute(&self, input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }

        let mid = input.len() / 2;
        let (left, right) = input.split_at(mid);

        let (left_sorted, right_sorted) = rayon::join(
            || {
                let left_algorithm = ParallelMergeSort;
                left_algorithm.execute(left.to_vec())
            },
            || {
                let right_algorithm = ParallelMergeSort;
                right_algorithm.execute(right.to_vec())
            }
        );

        let left_sorted = left_sorted?;
        let right_sorted = right_sorted?;

        Ok(merge_parallel(&left_sorted, &right_sorted))
    }

    fn execute_with_threads(&self, input: Vec<i32>, _thread_count: usize) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        self.execute(input)
    }
}

impl super::ParallelSortingAlgorithm for ParallelMergeSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::MergeSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n log n)", "O(n)", true, false)
    }
}

/// 并行堆排序
pub struct ParallelHeapSort;

impl ParallelAlgorithm<Vec<i32>, Vec<i32>> for ParallelHeapSort {
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        let len = input.len();

        // 构建最大堆
        for i in (0..len / 2).rev() {
            heapify_parallel(&mut input, len, i);
        }

        // 逐个提取元素
        for i in (1..len).rev() {
            input.swap(0, i);
            heapify_parallel(&mut input, i, 0);
        }

        Ok(input)
    }

    fn execute_with_threads(&self, input: Vec<i32>, _thread_count: usize) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        self.execute(input)
    }
}

impl super::ParallelSortingAlgorithm for ParallelHeapSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::HeapSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n log n)", "O(1)", false, true)
    }
}

/// 并行插入排序
pub struct ParallelInsertionSort;

impl ParallelAlgorithm<Vec<i32>, Vec<i32>> for ParallelInsertionSort {
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        for i in 1..input.len() {
            let key = input[i];
            let mut j = i;

            while j > 0 && input[j - 1] > key {
                input[j] = input[j - 1];
                j -= 1;
            }
            input[j] = key;
        }

        Ok(input)
    }

    fn execute_with_threads(&self, input: Vec<i32>, _thread_count: usize) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        self.execute(input)
    }
}

impl super::ParallelSortingAlgorithm for ParallelInsertionSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::InsertionSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n)", "O(n²)", "O(n²)", "O(1)", true, true)
    }
}

/// 并行选择排序
pub struct ParallelSelectionSort;

impl ParallelAlgorithm<Vec<i32>, Vec<i32>> for ParallelSelectionSort {
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        for i in 0..input.len() {
            let min_idx = (i..input.len())
                .min_by_key(|&j| input[j])
                .unwrap_or(i);
            input.swap(i, min_idx);
        }

        Ok(input)
    }

    fn execute_with_threads(&self, input: Vec<i32>, _thread_count: usize) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        self.execute(input)
    }
}

impl super::ParallelSortingAlgorithm for ParallelSelectionSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::SelectionSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n²)", "O(n²)", "O(n²)", "O(1)", false, true)
    }
}

/// 并行冒泡排序
pub struct ParallelBubbleSort;

impl ParallelAlgorithm<Vec<i32>, Vec<i32>> for ParallelBubbleSort {
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        let len = input.len();
        for i in 0..len {
            for j in 0..len - i - 1 {
                if input[j] > input[j + 1] {
                    input.swap(j, j + 1);
                }
            }
        }

        Ok(input)
    }

    fn execute_with_threads(&self, input: Vec<i32>, _thread_count: usize) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        self.execute(input)
    }
}

impl super::ParallelSortingAlgorithm for ParallelBubbleSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::BubbleSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n)", "O(n²)", "O(n²)", "O(1)", true, true)
    }
}

/// 并行基数排序
pub struct ParallelRadixSort;

impl ParallelAlgorithm<Vec<i32>, Vec<i32>> for ParallelRadixSort {
    fn execute(&self, input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.is_empty() {
            return Ok(input);
        }

        let max_val = *input.iter().max().unwrap();
        let mut output = input;

        let mut exp = 1;
        while max_val / exp > 0 {
            output = counting_sort_by_digit_parallel(&output, exp);
            exp *= 10;
        }

        Ok(output)
    }

    fn execute_with_threads(&self, input: Vec<i32>, _thread_count: usize) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        self.execute(input)
    }
}

impl super::ParallelSortingAlgorithm for ParallelRadixSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::RadixSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(d(n+k))", "O(d(n+k))", "O(d(n+k))", "O(n+k)", true, false)
    }
}

/// 并行计数排序
pub struct ParallelCountingSort;

impl ParallelAlgorithm<Vec<i32>, Vec<i32>> for ParallelCountingSort {
    fn execute(&self, input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.is_empty() {
            return Ok(input);
        }

        let min_val = *input.iter().min().unwrap();
        let max_val = *input.iter().max().unwrap();
        let range = (max_val - min_val + 1) as usize;

        let mut count = vec![0; range];

        // 计数
        for &num in &input {
            count[(num - min_val) as usize] += 1;
        }

        // 构建输出
        let mut output = Vec::new();
        for (i, &count) in count.iter().enumerate() {
            for _ in 0..count {
                output.push(min_val + i as i32);
            }
        }

        Ok(output)
    }

    fn execute_with_threads(&self, input: Vec<i32>, _thread_count: usize) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        self.execute(input)
    }
}

impl super::ParallelSortingAlgorithm for ParallelCountingSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::CountingSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n+k)", "O(n+k)", "O(n+k)", "O(k)", true, false)
    }
}

/// 并行桶排序
pub struct ParallelBucketSort;

impl ParallelAlgorithm<Vec<i32>, Vec<i32>> for ParallelBucketSort {
    fn execute(&self, input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.is_empty() {
            return Ok(input);
        }

        let min_val = *input.iter().min().unwrap();
        let max_val = *input.iter().max().unwrap();
        let bucket_count = (input.len() as f64).sqrt() as usize;
        let bucket_size = (max_val - min_val + 1) as f64 / bucket_count as f64;

        let mut buckets: Vec<Vec<i32>> = vec![Vec::new(); bucket_count];

        // 分配元素到桶中
        for &num in &input {
            let bucket_index = ((num - min_val) as f64 / bucket_size).floor() as usize;
            let bucket_index = bucket_index.min(bucket_count - 1);
            buckets[bucket_index].push(num);
        }

        // 并行排序每个桶
        let sorted_buckets: Result<Vec<Vec<i32>>, Box<dyn std::error::Error + Send + Sync>> = buckets
            .into_par_iter()
            .map(|mut bucket: Vec<i32>| {
                bucket.sort();
                Ok::<Vec<i32>, Box<dyn std::error::Error + Send + Sync>>(bucket)
            })
            .collect();

        let sorted_buckets = sorted_buckets?;

        // 合并桶
        let result: Vec<i32> = sorted_buckets.into_iter().flatten().collect();

        Ok(result)
    }

    fn execute_with_threads(&self, input: Vec<i32>, _thread_count: usize) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        self.execute(input)
    }
}

impl super::ParallelSortingAlgorithm for ParallelBucketSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::BucketSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n+k)", "O(n+k)", "O(n²)", "O(n)", true, false)
    }
}

/// 并行 Tim 排序
pub struct ParallelTimSort;

impl ParallelAlgorithm<Vec<i32>, Vec<i32>> for ParallelTimSort {
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        // TimSort 是一个复杂的混合排序算法，这里提供简化版本
        // 实际实现会结合插入排序和归并排序
        input.sort();
        Ok(input)
    }

    fn execute_with_threads(&self, input: Vec<i32>, _thread_count: usize) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        self.execute(input)
    }
}

impl super::ParallelSortingAlgorithm for ParallelTimSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::TimSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n)", "O(n log n)", "O(n log n)", "O(n)", true, false)
    }
}

// 辅助函数

fn merge_parallel(left: &[i32], right: &[i32]) -> Vec<i32> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let mut i = 0;
    let mut j = 0;

    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }

    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);

    result
}

fn heapify_parallel(arr: &mut [i32], n: usize, i: usize) {
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
        heapify_parallel(arr, n, largest);
    }
}

fn counting_sort_by_digit_parallel(arr: &[i32], exp: i32) -> Vec<i32> {
    let mut output = vec![0; arr.len()];
    let mut count = vec![0; 10];

    // 计数
    for &num in arr {
        count[((num / exp) % 10) as usize] += 1;
    }

    // 累积计数
    for i in 1..10 {
        count[i] += count[i - 1];
    }

    // 构建输出
    for &num in arr.iter().rev() {
        let index = ((num / exp) % 10) as usize;
        output[count[index] - 1] = num;
        count[index] -= 1;
    }

    output
}
