//! 算法复杂度示例
//! algorithm complex example
//! 本示例展示不同复杂度算法的性能对比：
//! this example complex algorithm performance to ：
//! - O(1) - 常数时间
//! - O(1) - time
//! - O(1) - 常数time
//! - O(log n) - 对数时间
//! - O(log n) - to time
//! - O(log n) - to数time
//! - O(n) - 线性时间
//! - O(n) - line time
//! - O(n log n) - 线性对数时间
//! - O(n log n) - line to time
//! - O(n²) - 平方时间
//! - O(n²) - time
//! - O(n²) - 平方time
//! 运行方式:
//!
//! Run way :
//!
//! cargo run --example algorithm_complexity_demo
//! ```
use std::time::Instant;

fn main() {
    println!("🚀 算法复杂度示例\n");
    println!("{}", "=".repeat(60));

    let n = 10000;

    // 1. O(1) - 常数时间
    println!("\n📊 O(1) - 常数时间:");
    println!("{}", "-".repeat(60));
    let start = Instant::now();
    let _result = constant_time(n);
    let duration = start.elapsed();
    println!("输入大小: {}", n);
    println!("执行时间: {:?}", duration);

    // 2. O(log n) - 对数时间
    println!("\n📊 O(log n) - 对数时间:");
    println!("{}", "-".repeat(60));
    let start = Instant::now();
    let _result = log_time(n);
    let duration = start.elapsed();
    println!("输入大小: {}", n);
    println!("执行时间: {:?}", duration);

    // 3. O(n) - 线性时间
    println!("\n📊 O(n) - 线性时间:");
    println!("{}", "-".repeat(60));
    let start = Instant::now();
    let _result = linear_time(n);
    let duration = start.elapsed();
    println!("输入大小: {}", n);
    println!("执行时间: {:?}", duration);

    // 4. O(n log n) - 线性对数时间
    println!("\n📊 O(n log n) - 线性对数时间:");
    println!("{}", "-".repeat(60));
    let start = Instant::now();
    let _result = n_log_n_time(n);
    let duration = start.elapsed();
    println!("输入大小: {}", n);
    println!("执行时间: {:?}", duration);

    // 5. 复杂度对比
    println!("\n💡 算法复杂度对比:");
    println!("{}", "-".repeat(60));
    println!("  O(1):      常数时间 - 最佳");
    println!("  O(log n):  对数时间 - 很好");
    println!("  O(n):      线性时间 - 良好");
    println!("  O(n log n):线性对数时间 - 可接受");
    println!("  O(n²):     平方时间 - 较差");

    println!("\n✅ 算法复杂度演示完成！");
}

/// O(1) - 常数时间
/// O(1) - time
/// O(1) - 常数time
fn constant_time(_n: usize) -> usize {
    42 // 无论输入大小，执行时间相同
}

/// O(log n) - 对数时间
/// O(log n) - to time
/// O(log n) - to数time
fn log_time(n: usize) -> usize {
    let mut result = 0;
    let mut value = n;
    while value > 0 {
        result += 1;
        value /= 2;
    }
    result
}

/// O(n) - 线性时间
/// O(n) - line time
fn linear_time(n: usize) -> usize {
    let mut sum = 0;
    for i in 0..n {
        sum += i;
    }
    sum
}

/// O(n log n) - 线性对数时间
/// O(n log n) - line to time
fn n_log_n_time(n: usize) -> usize {
    let mut result = 0;
    for _i in 0..n {
        let mut j = n;
        while j > 0 {
            result += 1;
            j /= 2;
        }
    }
    result
}
