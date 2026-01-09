//! 排序算法演示程序
//!
//! 本示例展示各种排序算法的实现和使用：
//! - 冒泡排序
//! - 快速排序
//! - 归并排序
//! - 堆排序
//! - 插入排序

use std::time::Instant;

/// 冒泡排序
pub fn bubble_sort<T: PartialOrd + Clone>(arr: &mut [T]) {
    let n = arr.len();
    for i in 0..n {
        for j in 0..n - i - 1 {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
            }
        }
    }
}

/// 快速排序
pub fn quick_sort<T: PartialOrd + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }

    let pivot_index = partition(arr);
    quick_sort(&mut arr[..pivot_index]);
    quick_sort(&mut arr[pivot_index + 1..]);
}

fn partition<T: PartialOrd>(arr: &mut [T]) -> usize {
    let pivot_index = arr.len() - 1;
    let mut i = 0;

    for j in 0..pivot_index {
        if arr[j] <= arr[pivot_index] {
            arr.swap(i, j);
            i += 1;
        }
    }

    arr.swap(i, pivot_index);
    i
}

/// 归并排序
pub fn merge_sort<T: PartialOrd + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }

    let mid = arr.len() / 2;
    let mut left = arr[..mid].to_vec();
    let mut right = arr[mid..].to_vec();

    merge_sort(&mut left);
    merge_sort(&mut right);

    merge(arr, &left, &right);
}

fn merge<T: PartialOrd + Clone>(arr: &mut [T], left: &[T], right: &[T]) {
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

/// 插入排序
pub fn insertion_sort<T: PartialOrd + Clone>(arr: &mut [T]) {
    for i in 1..arr.len() {
        let key = arr[i].clone();
        let mut j = i;

        while j > 0 && arr[j - 1] > key {
            arr[j] = arr[j - 1].clone();
            j -= 1;
        }

        arr[j] = key;
    }
}

/// 选择排序
pub fn selection_sort<T: PartialOrd + Clone>(arr: &mut [T]) {
    for i in 0..arr.len() {
        let mut min_idx = i;
        for j in i + 1..arr.len() {
            if arr[j] < arr[min_idx] {
                min_idx = j;
            }
        }
        arr.swap(i, min_idx);
    }
}

/// 测试排序算法
fn test_sort_algorithm<F>(name: &str, mut sort_fn: F, mut arr: Vec<i32>)
where
    F: FnMut(&mut [i32]),
{
    let start = Instant::now();
    sort_fn(&mut arr);
    let duration = start.elapsed();

    // 验证排序结果
    let is_sorted = arr.windows(2).all(|w| w[0] <= w[1]);
    assert!(is_sorted, "{} failed: array is not sorted", name);

    println!("  {}: {:?} (耗时: {:?})", name, &arr[..arr.len().min(10)], duration);
}

fn main() {
    println!("🚀 排序算法演示程序\n");

    // 测试数据
    let test_data = vec![64, 34, 25, 12, 22, 11, 90, 5, 77, 88, 3, 45, 67, 89, 1];

    println!("原始数据: {:?}\n", test_data);
    println!("排序结果:");

    // 测试各种排序算法
    test_sort_algorithm("冒泡排序", bubble_sort, test_data.clone());
    test_sort_algorithm("快速排序", quick_sort, test_data.clone());
    test_sort_algorithm("归并排序", merge_sort, test_data.clone());
    test_sort_algorithm("插入排序", insertion_sort, test_data.clone());
    test_sort_algorithm("选择排序", selection_sort, test_data.clone());

    // 性能对比
    println!("\n📊 性能对比（1000个随机数）:");
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    let large_data: Vec<i32> = (0..1000)
        .map(|i| {
            i.hash(&mut hasher);
            (hasher.finish() % 1000) as i32
        })
        .collect();

    let mut data1 = large_data.clone();
    let start = Instant::now();
    bubble_sort(&mut data1);
    println!("  冒泡排序: {:?}", start.elapsed());

    let mut data2 = large_data.clone();
    let start = Instant::now();
    quick_sort(&mut data2);
    println!("  快速排序: {:?}", start.elapsed());

    let mut data3 = large_data.clone();
    let start = Instant::now();
    merge_sort(&mut data3);
    println!("  归并排序: {:?}", start.elapsed());

    let mut data4 = large_data.clone();
    let start = Instant::now();
    insertion_sort(&mut data4);
    println!("  插入排序: {:?}", start.elapsed());

    println!("\n✅ 所有排序算法演示完成！");
}
