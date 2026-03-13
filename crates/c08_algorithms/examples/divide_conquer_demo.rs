//! 分治算法示例
//!
//! 本示例展示C08算法模块的分治算法：
//! - 归并排序
//! - 快速排序
//! - 最大子数组和
//!
//! 运行方式:
//! ```bash
//! cargo run --example divide_conquer_demo
//! ```
fn main() {
    println!("🚀 分治算法示例\n");
    println!("{}", "=".repeat(60));

    // 1. 归并排序
    println!("\n📊 归并排序（分治）:");
    println!("{}", "-".repeat(60));
    let mut data = vec![64, 34, 25, 12, 22, 11, 90, 5];
    println!("原始数据: {:?}", data);
    merge_sort(&mut data);
    println!("排序后: {:?}", data);

    // 2. 最大子数组和
    println!("\n📊 最大子数组和（分治）:");
    println!("{}", "-".repeat(60));
    let data = vec![-2, 1, -3, 4, -1, 2, 1, -5, 4];
    println!("数组: {:?}", data);
    let max_sum = max_subarray_sum(&data);
    println!("最大子数组和: {}", max_sum);

    // 3. 算法说明
    println!("\n💡 分治算法说明:");
    println!("{}", "-".repeat(60));
    println!("  核心思想: 将问题分解为子问题，分别解决后合并");
    println!("  时间复杂度: 通常为O(n log n)");
    println!("  适用场景: 排序、搜索、优化问题");

    println!("\n✅ 分治算法演示完成！");
}

/// 归并排序
fn merge_sort(arr: &mut [i32]) {
    if arr.len() <= 1 {
        return;
    }

    let mid = arr.len() / 2;
    merge_sort(&mut arr[..mid]);
    merge_sort(&mut arr[mid..]);
    merge(arr, mid);
}

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

/// 最大子数组和（分治）
fn max_subarray_sum(arr: &[i32]) -> i32 {
    if arr.is_empty() {
        return 0;
    }
    if arr.len() == 1 {
        return arr[0].max(0);
    }

    let mid = arr.len() / 2;
    let left_max = max_subarray_sum(&arr[..mid]);
    let right_max = max_subarray_sum(&arr[mid..]);

    let mut left_sum = i32::MIN;
    let mut sum = 0;
    for i in (0..mid).rev() {
        sum += arr[i];
        left_sum = left_sum.max(sum);
    }

    let mut right_sum = i32::MIN;
    sum = 0;
    for i in mid..arr.len() {
        sum += arr[i];
        right_sum = right_sum.max(sum);
    }

    left_max.max(right_max).max(left_sum + right_sum)
}
