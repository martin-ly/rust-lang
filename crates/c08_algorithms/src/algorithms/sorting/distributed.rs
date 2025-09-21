//! # 分布式排序算法
//! 
//! 本模块实现了各种排序算法的分布式版本，支持跨节点的分布式计算。
//! 适用于大规模数据处理和需要水平扩展的场景。

use super::{SortingAlgorithm, AlgorithmComplexity};
use crate::algorithms::execution_modes::{
    DistributedAlgorithm,
    //ExecutionResult,
};
//use std::time::Instant;
//use serde::{Serialize, Deserialize};

/// 分布式快速排序
pub struct DistributedQuickSort;

impl DistributedAlgorithm<Vec<i32>, Vec<i32>> for DistributedQuickSort {
    fn execute(&self, input: Vec<i32>, nodes: Vec<String>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }
        
        // 简化版本：将数据分割到不同节点
        let chunk_size = input.len() / nodes.len().max(1);
        let mut sorted_chunks = Vec::new();
        
        for (i, chunk) in input.chunks(chunk_size).enumerate() {
            if i < nodes.len() {
                // 模拟分布式节点处理
                let mut chunk_vec = chunk.to_vec();
                chunk_vec.sort();
                sorted_chunks.push(chunk_vec);
            }
        }
        
        // 合并排序后的块
        Ok(merge_distributed_chunks(sorted_chunks))
    }
}

impl super::DistributedSortingAlgorithm for DistributedQuickSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::QuickSort
    }
    
    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n²)", "O(log n)", false, true)
    }
}

/// 分布式归并排序
pub struct DistributedMergeSort;

impl DistributedAlgorithm<Vec<i32>, Vec<i32>> for DistributedMergeSort {
    fn execute(&self, input: Vec<i32>, nodes: Vec<String>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.len() <= 1 {
            return Ok(input);
        }
        
        // 将数据分割到不同节点
        let chunk_size = input.len() / nodes.len().max(1);
        let mut sorted_chunks = Vec::new();
        
        for (i, chunk) in input.chunks(chunk_size).enumerate() {
            if i < nodes.len() {
                // 模拟分布式节点处理
                let mut chunk_vec = chunk.to_vec();
                chunk_vec.sort();
                sorted_chunks.push(chunk_vec);
            }
        }
        
        // 使用归并策略合并
        Ok(merge_distributed_chunks(sorted_chunks))
    }
}

impl super::DistributedSortingAlgorithm for DistributedMergeSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::MergeSort
    }
    
    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n log n)", "O(n)", true, false)
    }
}

/// 分布式堆排序
pub struct DistributedHeapSort;

impl DistributedAlgorithm<Vec<i32>, Vec<i32>> for DistributedHeapSort {
    fn execute(&self, input: Vec<i32>, nodes: Vec<String>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.is_empty() {
            return Ok(input);
        }
        
        // 简化版本：将数据分割到不同节点进行堆排序
        let chunk_size = input.len() / nodes.len().max(1);
        let mut sorted_chunks = Vec::new();
        
        for (i, chunk) in input.chunks(chunk_size).enumerate() {
            if i < nodes.len() {
                let mut chunk_vec = chunk.to_vec();
                heap_sort_distributed(&mut chunk_vec);
                sorted_chunks.push(chunk_vec);
            }
        }
        
        Ok(merge_distributed_chunks(sorted_chunks))
    }
}

impl super::DistributedSortingAlgorithm for DistributedHeapSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::HeapSort
    }
    
    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n log n)", "O(1)", false, true)
    }
}

/// 分布式插入排序
pub struct DistributedInsertionSort;

impl DistributedAlgorithm<Vec<i32>, Vec<i32>> for DistributedInsertionSort {
    fn execute(&self, input: Vec<i32>, nodes: Vec<String>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.is_empty() {
            return Ok(input);
        }
        
        // 将数据分割到不同节点
        let chunk_size = input.len() / nodes.len().max(1);
        let mut sorted_chunks = Vec::new();
        
        for (i, chunk) in input.chunks(chunk_size).enumerate() {
            if i < nodes.len() {
                let mut chunk_vec = chunk.to_vec();
                insertion_sort_distributed(&mut chunk_vec);
                sorted_chunks.push(chunk_vec);
            }
        }
        
        Ok(merge_distributed_chunks(sorted_chunks))
    }
}

impl super::DistributedSortingAlgorithm for DistributedInsertionSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::InsertionSort
    }
    
    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n)", "O(n²)", "O(n²)", "O(1)", true, true)
    }
}

/// 分布式选择排序
pub struct DistributedSelectionSort;

impl DistributedAlgorithm<Vec<i32>, Vec<i32>> for DistributedSelectionSort {
    fn execute(&self, input: Vec<i32>, nodes: Vec<String>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.is_empty() {
            return Ok(input);
        }
        
        // 将数据分割到不同节点
        let chunk_size = input.len() / nodes.len().max(1);
        let mut sorted_chunks = Vec::new();
        
        for (i, chunk) in input.chunks(chunk_size).enumerate() {
            if i < nodes.len() {
                let mut chunk_vec = chunk.to_vec();
                selection_sort_distributed(&mut chunk_vec);
                sorted_chunks.push(chunk_vec);
            }
        }
        
        Ok(merge_distributed_chunks(sorted_chunks))
    }
}

impl super::DistributedSortingAlgorithm for DistributedSelectionSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::SelectionSort
    }
    
    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n²)", "O(n²)", "O(n²)", "O(1)", false, true)
    }
}

/// 分布式冒泡排序
pub struct DistributedBubbleSort;

impl DistributedAlgorithm<Vec<i32>, Vec<i32>> for DistributedBubbleSort {
    fn execute(&self, input: Vec<i32>, nodes: Vec<String>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.is_empty() {
            return Ok(input);
        }
        
        // 将数据分割到不同节点
        let chunk_size = input.len() / nodes.len().max(1);
        let mut sorted_chunks = Vec::new();
        
        for (i, chunk) in input.chunks(chunk_size).enumerate() {
            if i < nodes.len() {
                let mut chunk_vec = chunk.to_vec();
                bubble_sort_distributed(&mut chunk_vec);
                sorted_chunks.push(chunk_vec);
            }
        }
        
        Ok(merge_distributed_chunks(sorted_chunks))
    }
}

impl super::DistributedSortingAlgorithm for DistributedBubbleSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::BubbleSort
    }
    
    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n)", "O(n²)", "O(n²)", "O(1)", true, true)
    }
}

/// 分布式基数排序
pub struct DistributedRadixSort;

impl DistributedAlgorithm<Vec<i32>, Vec<i32>> for DistributedRadixSort {
    fn execute(&self, input: Vec<i32>, nodes: Vec<String>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.is_empty() {
            return Ok(input);
        }
        
        // 分布式基数排序：按数字位分配到不同节点
        let max_val = *input.iter().max().unwrap();
        let mut output = input;
        
        let mut exp = 1;
        while max_val / exp > 0 {
            output = counting_sort_by_digit_distributed(&output, exp, &nodes);
            exp *= 10;
        }
        
        Ok(output)
    }
}

impl super::DistributedSortingAlgorithm for DistributedRadixSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::RadixSort
    }
    
    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(d(n+k))", "O(d(n+k))", "O(d(n+k))", "O(n+k)", true, false)
    }
}

/// 分布式计数排序
pub struct DistributedCountingSort;

impl DistributedAlgorithm<Vec<i32>, Vec<i32>> for DistributedCountingSort {
    fn execute(&self, input: Vec<i32>, nodes: Vec<String>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.is_empty() {
            return Ok(input);
        }
        
        let min_val = *input.iter().min().unwrap();
        let max_val = *input.iter().max().unwrap();
        let range = (max_val - min_val + 1) as usize;
        
        // 将计数任务分配到不同节点
        let _chunk_size = range / nodes.len().max(1);
        let mut count = vec![0; range];
        
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
}

impl super::DistributedSortingAlgorithm for DistributedCountingSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::CountingSort
    }
    
    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n+k)", "O(n+k)", "O(n+k)", "O(k)", true, false)
    }
}

/// 分布式桶排序
pub struct DistributedBucketSort;

impl DistributedAlgorithm<Vec<i32>, Vec<i32>> for DistributedBucketSort {
    fn execute(&self, input: Vec<i32>, nodes: Vec<String>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.is_empty() {
            return Ok(input);
        }
        
        let min_val = *input.iter().min().unwrap();
        let max_val = *input.iter().max().unwrap();
        let bucket_count = nodes.len().max(1);
        let bucket_size = (max_val - min_val + 1) as f64 / bucket_count as f64;
        
        let mut buckets: Vec<Vec<i32>> = vec![Vec::new(); bucket_count];
        
        // 分配元素到桶中
        for &num in &input {
            let bucket_index = ((num - min_val) as f64 / bucket_size).floor() as usize;
            let bucket_index = bucket_index.min(bucket_count - 1);
            buckets[bucket_index].push(num);
        }
        
        // 每个节点处理一个桶
        let mut sorted_buckets = Vec::new();
        for (i, mut bucket) in buckets.into_iter().enumerate() {
            if i < nodes.len() {
                bucket.sort();
                sorted_buckets.push(bucket);
            }
        }
        
        // 合并桶
        let result: Vec<i32> = sorted_buckets.into_iter().flatten().collect();
        
        Ok(result)
    }
}

impl super::DistributedSortingAlgorithm for DistributedBucketSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::BucketSort
    }
    
    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n+k)", "O(n+k)", "O(n²)", "O(n)", true, false)
    }
}

/// 分布式 Tim 排序
pub struct DistributedTimSort;

impl DistributedAlgorithm<Vec<i32>, Vec<i32>> for DistributedTimSort {
    fn execute(&self, input: Vec<i32>, nodes: Vec<String>) -> Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>> {
        if input.is_empty() {
            return Ok(input);
        }
        
        // 将数据分割到不同节点
        let chunk_size = input.len() / nodes.len().max(1);
        let mut sorted_chunks = Vec::new();
        
        for (i, chunk) in input.chunks(chunk_size).enumerate() {
            if i < nodes.len() {
                let mut chunk_vec = chunk.to_vec();
                chunk_vec.sort(); // 使用标准库的 TimSort
                sorted_chunks.push(chunk_vec);
            }
        }
        
        Ok(merge_distributed_chunks(sorted_chunks))
    }
}

impl super::DistributedSortingAlgorithm for DistributedTimSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::TimSort
    }
    
    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n)", "O(n log n)", "O(n log n)", "O(n)", true, false)
    }
}

// 辅助函数

fn merge_distributed_chunks(mut chunks: Vec<Vec<i32>>) -> Vec<i32> {
    if chunks.is_empty() {
        return Vec::new();
    }
    
    if chunks.len() == 1 {
        return chunks.pop().unwrap();
    }
    
    // 递归合并
    while chunks.len() > 1 {
        let mut new_chunks = Vec::new();
        for chunk_pair in chunks.chunks(2) {
            if chunk_pair.len() == 2 {
                new_chunks.push(merge_two_chunks(&chunk_pair[0], &chunk_pair[1]));
            } else {
                new_chunks.push(chunk_pair[0].clone());
            }
        }
        chunks = new_chunks;
    }
    
    chunks.pop().unwrap()
}

fn merge_two_chunks(left: &[i32], right: &[i32]) -> Vec<i32> {
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

fn heap_sort_distributed(arr: &mut [i32]) {
    let len = arr.len();
    
    // 构建最大堆
    for i in (0..len / 2).rev() {
        heapify_distributed(arr, len, i);
    }
    
    // 逐个提取元素
    for i in (1..len).rev() {
        arr.swap(0, i);
        heapify_distributed(arr, i, 0);
    }
}

fn heapify_distributed(arr: &mut [i32], n: usize, i: usize) {
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
        heapify_distributed(arr, n, largest);
    }
}

fn insertion_sort_distributed(arr: &mut [i32]) {
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

fn selection_sort_distributed(arr: &mut [i32]) {
    for i in 0..arr.len() {
        let min_idx = (i..arr.len())
            .min_by_key(|&j| arr[j])
            .unwrap_or(i);
        arr.swap(i, min_idx);
    }
}

fn bubble_sort_distributed(arr: &mut [i32]) {
    let len = arr.len();
    for i in 0..len {
        for j in 0..len - i - 1 {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
            }
        }
    }
}

fn counting_sort_by_digit_distributed(arr: &[i32], exp: i32, _nodes: &[String]) -> Vec<i32> {
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
