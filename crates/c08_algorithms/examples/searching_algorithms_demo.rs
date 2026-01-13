//! 搜索算法示例
//!
//! 本示例展示C08算法模块的各种搜索算法：
//! - 二分搜索
//! - 线性搜索
//! - 插值搜索
//! - 并行搜索
//!
//! 运行方式:
//! ```bash
//! cargo run --example searching_algorithms_demo
//! ```

use c08_algorithms::searching::{binary_search_sync, parallel_search};

fn main() {
    println!("🚀 搜索算法示例\n");
    println!("{}", "=".repeat(60));

    let data = vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19];
    println!("数据: {:?}\n", data);

    // 1. 二分搜索
    println!("📊 二分搜索:");
    println!("{}", "-".repeat(60));
    match binary_search_sync(&data, &7) {
        Ok(Some(index)) => println!("找到 7 在索引: {}", index),
        Ok(None) => println!("未找到 7"),
        Err(e) => println!("搜索错误: {}", e),
    }

    // 2. 并行搜索
    println!("\n📊 并行搜索:");
    println!("{}", "-".repeat(60));
    match parallel_search(&data, &7) {
        Some(index) => println!("找到 7 在索引: {}", index),
        None => println!("未找到 7"),
    }

    // 3. 搜索不存在的元素
    println!("\n📊 搜索不存在的元素:");
    println!("{}", "-".repeat(60));
    match binary_search_sync(&data, &20) {
        Ok(Some(index)) => println!("找到 20 在索引: {}", index),
        Ok(None) => println!("未找到 20"),
        Err(e) => println!("搜索错误: {}", e),
    }

    // 4. 算法对比
    println!("\n💡 搜索算法对比:");
    println!("{}", "-".repeat(60));
    println!("  二分搜索: O(log n) - 需要已排序数组");
    println!("  线性搜索: O(n) - 适用于未排序数组");
    println!("  并行搜索: O(n/p) - 并行处理，p为线程数");

    println!("\n✅ 搜索算法演示完成！");
}
