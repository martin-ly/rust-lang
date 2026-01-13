//! 算法优化示例
//!
//! 本示例展示算法优化的技巧和方法：
//! - 空间换时间
//! - 时间换空间
//! - 算法改进
//!
//! 运行方式:
//! ```bash
//! cargo run --example algorithm_optimization_demo
//! ```

use std::collections::HashMap;
use std::time::Instant;

fn main() {
    println!("🚀 算法优化示例\n");
    println!("{}", "=".repeat(60));

    let n = 40;

    // 1. 斐波那契：递归 vs 动态规划
    println!("\n📊 斐波那契：递归 vs 动态规划:");
    println!("{}", "-".repeat(60));
    let start = Instant::now();
    let result1 = fibonacci_recursive(n);
    let duration1 = start.elapsed();
    println!("递归版本 (n={}): {} 耗时: {:?}", n, result1, duration1);

    let start = Instant::now();
    let result2 = fibonacci_dp_optimized(n);
    let duration2 = start.elapsed();
    println!("动态规划版本 (n={}): {} 耗时: {:?}", n, result2, duration2);

    println!(
        "性能提升: {:.2}x",
        duration1.as_nanos() as f64 / duration2.as_nanos() as f64
    );

    // 2. 查找：线性搜索 vs 哈希表
    println!("\n📊 查找：线性搜索 vs 哈希表:");
    println!("{}", "-".repeat(60));
    let data: Vec<i32> = (0..10000).collect();
    let target = 5000;

    let start = Instant::now();
    let _result1 = linear_search_opt(&data, target);
    let duration1 = start.elapsed();
    println!("线性搜索: {:?}", duration1);

    let map: HashMap<i32, usize> = data.iter().enumerate().map(|(i, &v)| (v, i)).collect();
    let start = Instant::now();
    let _result2 = map.get(&target);
    let duration2 = start.elapsed();
    println!("哈希表查找: {:?}", duration2);

    println!(
        "性能差异: {:.2}x",
        duration1.as_nanos() as f64 / duration2.as_nanos() as f64
    );

    // 3. 优化技巧说明
    println!("\n💡 算法优化技巧:");
    println!("{}", "-".repeat(60));
    println!("  1. 空间换时间: 使用哈希表、缓存等");
    println!("  2. 时间换空间: 使用流式处理、延迟计算");
    println!("  3. 算法改进: 选择更高效的算法");
    println!("  4. 数据结构优化: 选择合适的数据结构");

    println!("\n✅ 算法优化演示完成！");
}

/// 递归版本的斐波那契（O(2^n)）
fn fibonacci_recursive(n: usize) -> u64 {
    if n <= 1 {
        n as u64
    } else {
        fibonacci_recursive(n - 1) + fibonacci_recursive(n - 2)
    }
}

/// 优化的动态规划版本（O(n)）
fn fibonacci_dp_optimized(n: usize) -> u64 {
    if n <= 1 {
        return n as u64;
    }
    let mut a = 0u64;
    let mut b = 1u64;
    for _ in 2..=n {
        let temp = a + b;
        a = b;
        b = temp;
    }
    b
}

/// 线性搜索
fn linear_search_opt(arr: &[i32], target: i32) -> Option<usize> {
    arr.iter().position(|&x| x == target)
}
