//! 算法对比示例
//!
//! 本示例展示相同问题的不同算法实现和性能对比：
//! - 排序算法对比
//! - 搜索算法对比
//! - 算法选择指南
//!
//! 运行方式:
//! ```bash
//! cargo run --example algorithm_comparison_demo
//! ```
use std::time::Instant;

fn main() {
    println!("🚀 算法对比示例\n");
    println!("{}", "=".repeat(60));

    let data = (0..1000).rev().collect::<Vec<i32>>();

    // 1. 排序算法对比
    println!("\n📊 排序算法性能对比:");
    println!("{}", "-".repeat(60));
    let mut data1 = data.clone();
    let start = Instant::now();
    data1.sort(); // 使用标准库的优化排序（通常是Timsort）
    let duration1 = start.elapsed();
    println!("标准库排序: {:?}", duration1);

    let mut data2 = data.clone();
    let start = Instant::now();
    bubble_sort(&mut data2);
    let duration2 = start.elapsed();
    println!("冒泡排序: {:?}", duration2);

    println!(
        "性能差异: {:.2}x",
        duration2.as_nanos() as f64 / duration1.as_nanos() as f64
    );

    // 2. 搜索算法对比
    println!("\n📊 搜索算法对比:");
    println!("{}", "-".repeat(60));
    let sorted_data: Vec<i32> = (0..10000).collect();
    let target = 5000;

    let start = Instant::now();
    let _result1 = linear_search(&sorted_data, target);
    let duration1 = start.elapsed();
    println!("线性搜索: {:?}", duration1);

    let start = Instant::now();
    let _result2 = binary_search_simple(&sorted_data, target);
    let duration2 = start.elapsed();
    println!("二分搜索: {:?}", duration2);

    println!(
        "性能差异: {:.2}x",
        duration1.as_nanos() as f64 / duration2.as_nanos() as f64
    );

    // 3. 算法选择指南
    println!("\n💡 算法选择指南:");
    println!("{}", "-".repeat(60));
    println!("  小数据集: 简单算法可能更快（常数因子小）");
    println!("  大数据集: 选择时间复杂度低的算法");
    println!("  已排序数据: 使用二分搜索");
    println!("  未排序数据: 先排序再搜索，或使用线性搜索");

    println!("\n✅ 算法对比演示完成！");
}

/// 冒泡排序（O(n²)）
fn bubble_sort(arr: &mut [i32]) {
    let n = arr.len();
    for i in 0..n {
        for j in 0..n - i - 1 {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
            }
        }
    }
}

/// 线性搜索（O(n)）
fn linear_search(arr: &[i32], target: i32) -> Option<usize> {
    for (i, &value) in arr.iter().enumerate() {
        if value == target {
            return Some(i);
        }
    }
    None
}

/// 二分搜索（O(log n)）
fn binary_search_simple(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
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
