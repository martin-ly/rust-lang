//! 排序算法示例
//!
//! 本示例展示C08算法模块的各种排序算法：
//! - 快速排序
//! - 归并排序
//! - 堆排序
//! - 冒泡排序
//! - 插入排序
//!
//! 运行方式:
//! ```bash
//! cargo run --example sorting_algorithms_demo
//! ```

use c08_algorithms::sorting::{sort_sync, SortingAlgo};

fn main() {
    println!("🚀 排序算法示例\n");
    println!("{}", "=".repeat(60));

    let data = vec![64, 34, 25, 12, 22, 11, 90, 5];
    println!("原始数据: {:?}\n", data);

    // 1. 快速排序
    println!("📊 快速排序:");
    println!("{}", "-".repeat(60));
    let mut data1 = data.clone();
    sort_sync(&mut data1, SortingAlgo::Quick);
    println!("排序后: {:?}", data1);

    // 2. 归并排序
    println!("\n📊 归并排序:");
    println!("{}", "-".repeat(60));
    let mut data2 = data.clone();
    sort_sync(&mut data2, SortingAlgo::Merge);
    println!("排序后: {:?}", data2);

    // 3. 堆排序
    println!("\n📊 堆排序:");
    println!("{}", "-".repeat(60));
    let mut data3 = data.clone();
    sort_sync(&mut data3, SortingAlgo::Heap);
    println!("排序后: {:?}", data3);

    // 4. 算法对比
    println!("\n💡 排序算法对比:");
    println!("{}", "-".repeat(60));
    println!("  快速排序: O(n log n) 平均，O(n²) 最坏");
    println!("  归并排序: O(n log n) 稳定");
    println!("  堆排序:   O(n log n) 原地排序");

    println!("\n✅ 排序算法演示完成！");
}
