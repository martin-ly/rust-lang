//! 搜索算法演示程序
//!
//! 本示例展示各种搜索算法的实现和使用：
//! - 线性搜索
//! - 二分搜索
//! - 插值搜索
//! - 哈希搜索

use std::time::Instant;
use std::collections::HashMap;

/// 线性搜索
pub fn linear_search<T: PartialEq>(arr: &[T], target: &T) -> Option<usize> {
    for (i, item) in arr.iter().enumerate() {
        if item == target {
            return Some(i);
        }
    }
    None
}

/// 二分搜索（要求数组已排序）
pub fn binary_search<T: PartialOrd>(arr: &[T], target: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        if arr[mid] < *target {
            left = mid + 1;
        } else if arr[mid] > *target {
            right = mid;
        } else {
            return Some(mid);
        }
    }
    None
}

/// 插值搜索（要求数组已排序且均匀分布）
pub fn interpolation_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len() - 1;

    while left <= right && target >= arr[left] && target <= arr[right] {
        if left == right {
            if arr[left] == target {
                return Some(left);
            }
            return None;
        }

        // 插值公式
        let pos = left + (((right - left) as f64 / (arr[right] - arr[left]) as f64)
            * (target - arr[left]) as f64) as usize;

        if arr[pos] == target {
            return Some(pos);
        } else if arr[pos] < target {
            left = pos + 1;
        } else {
            right = pos - 1;
        }
    }
    None
}

/// 哈希搜索（使用 HashMap）
pub struct HashSearch {
    map: HashMap<i32, usize>,
}

impl HashSearch {
    /// 创建新的哈希搜索结构
    pub fn new(arr: &[i32]) -> Self {
        let mut map = HashMap::new();
        for (i, &value) in arr.iter().enumerate() {
            map.insert(value, i);
        }
        Self { map }
    }

    /// 搜索目标值
    pub fn search(&self, target: i32) -> Option<usize> {
        self.map.get(&target).copied()
    }
}

/// 测试搜索算法性能
fn benchmark_search<F>(name: &str, search_fn: F, arr: &[i32], target: i32)
where
    F: Fn(&[i32], &i32) -> Option<usize>,
{
    let start = Instant::now();
    let result = search_fn(arr, &target);
    let duration = start.elapsed();

    match result {
        Some(idx) => println!(
            "  {}: 找到目标 {} 在索引 {} (耗时: {:?})",
            name, target, idx, duration
        ),
        None => println!("  {}: 未找到目标 {} (耗时: {:?})", name, target, duration),
    }
}

fn main() {
    println!("🚀 搜索算法演示程序\n");

    // 测试数据 - 未排序数组
    let unsorted_data = vec![64, 34, 25, 12, 22, 11, 90, 5, 77, 88];
    println!("未排序数据: {:?}", unsorted_data);

    // 测试数据 - 排序数组
    let mut sorted_data = unsorted_data.clone();
    sorted_data.sort();
    println!("排序数据: {:?}\n", sorted_data);

    let target = 77;

    println!("搜索目标: {}\n", target);
    println!("=== 搜索结果 ===");

    // 1. 线性搜索
    if let Some(idx) = linear_search(&unsorted_data, &target) {
        println!("线性搜索: 找到目标 {} 在索引 {}", target, idx);
    } else {
        println!("线性搜索: 未找到目标 {}", target);
    }

    // 2. 二分搜索
    if let Some(idx) = binary_search(&sorted_data, &target) {
        println!("二分搜索: 找到目标 {} 在索引 {}", target, idx);
    } else {
        println!("二分搜索: 未找到目标 {}", target);
    }

    // 3. 插值搜索
    let uniform_data: Vec<i32> = (0..100).map(|i| i * 2).collect();
    if let Some(idx) = interpolation_search(&uniform_data, 50) {
        println!("插值搜索: 找到目标 50 在索引 {}", idx);
    } else {
        println!("插值搜索: 未找到目标 50");
    }

    // 4. 哈希搜索
    let hash_search = HashSearch::new(&sorted_data);
    if let Some(idx) = hash_search.search(target) {
        println!("哈希搜索: 找到目标 {} 在索引 {}", target, idx);
    } else {
        println!("哈希搜索: 未找到目标 {}", target);
    }

    // 性能对比
    println!("\n📊 性能对比（10000个元素）:");
    let large_data: Vec<i32> = (0..10000).collect();
    let search_target = 5000;

    benchmark_search("线性搜索", linear_search, &large_data, search_target);
    benchmark_search("二分搜索", binary_search, &large_data, search_target);

    let hash_search = HashSearch::new(&large_data);
    let start = Instant::now();
    let result = hash_search.search(search_target);
    let duration = start.elapsed();
    println!(
        "  哈希搜索: {:?} (耗时: {:?})",
        result,
        duration
    );

    println!("\n✅ 所有搜索算法演示完成！");
    println!("\n💡 提示:");
    println!("  - 线性搜索: O(n)，适用于未排序数组");
    println!("  - 二分搜索: O(log n)，要求数组已排序");
    println!("  - 插值搜索: O(log log n)，要求数组已排序且均匀分布");
    println!("  - 哈希搜索: O(1) 平均，O(n) 最坏，需要额外空间");
}
