//! # 异步排序算法实现
//!
//! 本模块实现了各种异步排序算法。

use super::*;
use crate::algorithms::execution_modes::AsyncAlgorithm;
use std::pin::Pin;
use std::future::Future;

/// 异步快速排序算法
pub struct AsyncQuickSort;

impl AsyncAlgorithm<Vec<i32>, Vec<i32>> for AsyncQuickSort {
    fn execute<'a>(
        &'a self,
        input: Vec<i32>,
    ) -> Pin<Box<dyn Future<Output = Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>>> + Send + 'a>> {
        Box::pin(async move {
            tokio::task::spawn_blocking(move || {
                if input.len() <= 1 {
                    return input;
                }

                let mut data = input;
                let len = data.len();
                if len > 0 {
                    quick_sort_recursive(&mut data, 0, len - 1);
                }
                data
            }).await.map_err(|e| Box::new(e) as Box<dyn std::error::Error + Send + Sync>)
        })
    }
}

impl AsyncSortingAlgorithm for AsyncQuickSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::QuickSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n²)", "O(log n)", false, true)
    }
}

/// 异步归并排序算法
pub struct AsyncMergeSort;

impl AsyncAlgorithm<Vec<i32>, Vec<i32>> for AsyncMergeSort {
    fn execute<'a>(
        &'a self,
        input: Vec<i32>,
    ) -> Pin<Box<dyn Future<Output = Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>>> + Send + 'a>> {
        Box::pin(async move {
            tokio::task::spawn_blocking(move || {
                if input.len() <= 1 {
                    return input;
                }

                let mut data = input;
                merge_sort_recursive(&mut data);
                data
            }).await.map_err(|e| Box::new(e) as Box<dyn std::error::Error + Send + Sync>)
        })
    }
}

impl AsyncSortingAlgorithm for AsyncMergeSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm {
        SortingAlgorithm::MergeSort
    }

    fn get_complexity(&self) -> AlgorithmComplexity {
        AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n log n)", "O(n)", true, false)
    }
}

// 占位实现：其他异步排序算法
pub struct AsyncHeapSort;
impl AsyncAlgorithm<Vec<i32>, Vec<i32>> for AsyncHeapSort {
    fn execute<'a>(&'a self, input: Vec<i32>) -> Pin<Box<dyn Future<Output = Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>>> + Send + 'a>> {
        Box::pin(async move { Ok(input) })
    }
}
impl AsyncSortingAlgorithm for AsyncHeapSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm { SortingAlgorithm::HeapSort }
    fn get_complexity(&self) -> AlgorithmComplexity { AlgorithmComplexity::new("O(n log n)", "O(n log n)", "O(n log n)", "O(1)", false, true) }
}

pub struct AsyncInsertionSort;
impl AsyncAlgorithm<Vec<i32>, Vec<i32>> for AsyncInsertionSort {
    fn execute<'a>(&'a self, input: Vec<i32>) -> Pin<Box<dyn Future<Output = Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>>> + Send + 'a>> {
        Box::pin(async move { Ok(input) })
    }
}
impl AsyncSortingAlgorithm for AsyncInsertionSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm { SortingAlgorithm::InsertionSort }
    fn get_complexity(&self) -> AlgorithmComplexity { AlgorithmComplexity::new("O(n)", "O(n²)", "O(n²)", "O(1)", true, true) }
}

pub struct AsyncSelectionSort;
impl AsyncAlgorithm<Vec<i32>, Vec<i32>> for AsyncSelectionSort {
    fn execute<'a>(&'a self, input: Vec<i32>) -> Pin<Box<dyn Future<Output = Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>>> + Send + 'a>> {
        Box::pin(async move { Ok(input) })
    }
}
impl AsyncSortingAlgorithm for AsyncSelectionSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm { SortingAlgorithm::SelectionSort }
    fn get_complexity(&self) -> AlgorithmComplexity { AlgorithmComplexity::new("O(n²)", "O(n²)", "O(n²)", "O(1)", false, true) }
}

pub struct AsyncBubbleSort;
impl AsyncAlgorithm<Vec<i32>, Vec<i32>> for AsyncBubbleSort {
    fn execute<'a>(&'a self, input: Vec<i32>) -> Pin<Box<dyn Future<Output = Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>>> + Send + 'a>> {
        Box::pin(async move { Ok(input) })
    }
}
impl AsyncSortingAlgorithm for AsyncBubbleSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm { SortingAlgorithm::BubbleSort }
    fn get_complexity(&self) -> AlgorithmComplexity { AlgorithmComplexity::new("O(n)", "O(n²)", "O(n²)", "O(1)", true, true) }
}

pub struct AsyncRadixSort;
impl AsyncAlgorithm<Vec<i32>, Vec<i32>> for AsyncRadixSort {
    fn execute<'a>(&'a self, input: Vec<i32>) -> Pin<Box<dyn Future<Output = Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>>> + Send + 'a>> {
        Box::pin(async move { Ok(input) })
    }
}
impl AsyncSortingAlgorithm for AsyncRadixSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm { SortingAlgorithm::RadixSort }
    fn get_complexity(&self) -> AlgorithmComplexity { AlgorithmComplexity::new("O(d(n+k))", "O(d(n+k))", "O(d(n+k))", "O(n+k)", true, false) }
}

pub struct AsyncCountingSort;
impl AsyncAlgorithm<Vec<i32>, Vec<i32>> for AsyncCountingSort {
    fn execute<'a>(&'a self, input: Vec<i32>) -> Pin<Box<dyn Future<Output = Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>>> + Send + 'a>> {
        Box::pin(async move { Ok(input) })
    }
}
impl AsyncSortingAlgorithm for AsyncCountingSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm { SortingAlgorithm::CountingSort }
    fn get_complexity(&self) -> AlgorithmComplexity { AlgorithmComplexity::new("O(n+k)", "O(n+k)", "O(n+k)", "O(k)", true, false) }
}

pub struct AsyncBucketSort;
impl AsyncAlgorithm<Vec<i32>, Vec<i32>> for AsyncBucketSort {
    fn execute<'a>(&'a self, input: Vec<i32>) -> Pin<Box<dyn Future<Output = Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>>> + Send + 'a>> {
        Box::pin(async move { Ok(input) })
    }
}
impl AsyncSortingAlgorithm for AsyncBucketSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm { SortingAlgorithm::BucketSort }
    fn get_complexity(&self) -> AlgorithmComplexity { AlgorithmComplexity::new("O(n+k)", "O(n+k)", "O(n²)", "O(n)", true, false) }
}

pub struct AsyncTimSort;
impl AsyncAlgorithm<Vec<i32>, Vec<i32>> for AsyncTimSort {
    fn execute<'a>(&'a self, input: Vec<i32>) -> Pin<Box<dyn Future<Output = Result<Vec<i32>, Box<dyn std::error::Error + Send + Sync>>> + Send + 'a>> {
        Box::pin(async move { Ok(input) })
    }
}
impl AsyncSortingAlgorithm for AsyncTimSort {
    fn get_algorithm_type(&self) -> SortingAlgorithm { SortingAlgorithm::TimSort }
    fn get_complexity(&self) -> AlgorithmComplexity { AlgorithmComplexity::new("O(n)", "O(n log n)", "O(n log n)", "O(n)", true, false) }
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
