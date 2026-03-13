//! 数据结构示例
//!
//! 本示例展示C08算法模块中使用的各种数据结构：
//! - 栈
//! - 队列
//! - 堆
//! - 哈希表
//!
//! 运行方式:
//! ```bash
//! cargo run --example data_structures_demo
//! ```
use std::collections::{BinaryHeap, HashMap, VecDeque};

fn main() {
    println!("🚀 数据结构示例\n");
    println!("{}", "=".repeat(60));

    // 1. 栈
    println!("\n📊 栈（Stack）:");
    println!("{}", "-".repeat(60));
    let mut stack = Vec::new();
    stack.push(1);
    stack.push(2);
    stack.push(3);
    println!("入栈: 1, 2, 3");
    while let Some(value) = stack.pop() {
        println!("出栈: {}", value);
    }

    // 2. 队列
    println!("\n📊 队列（Queue）:");
    println!("{}", "-".repeat(60));
    let mut queue = VecDeque::new();
    queue.push_back(1);
    queue.push_back(2);
    queue.push_back(3);
    println!("入队: 1, 2, 3");
    while let Some(value) = queue.pop_front() {
        println!("出队: {}", value);
    }

    // 3. 堆（优先队列）
    println!("\n📊 堆（Priority Queue）:");
    println!("{}", "-".repeat(60));
    let mut heap = BinaryHeap::new();
    heap.push(3);
    heap.push(1);
    heap.push(4);
    heap.push(2);
    println!("插入: 3, 1, 4, 2");
    while let Some(value) = heap.pop() {
        println!("最大堆弹出: {}", value);
    }

    // 4. 哈希表
    println!("\n📊 哈希表（Hash Map）:");
    println!("{}", "-".repeat(60));
    let mut map = HashMap::new();
    map.insert("apple", 5);
    map.insert("banana", 3);
    map.insert("orange", 7);
    println!("插入: apple=5, banana=3, orange=7");
    for (key, value) in &map {
        println!("  {}: {}", key, value);
    }

    // 5. 数据结构说明
    println!("\n💡 数据结构说明:");
    println!("{}", "-".repeat(60));
    println!("  栈: LIFO（后进先出），用于DFS、表达式求值");
    println!("  队列: FIFO（先进先出），用于BFS、任务调度");
    println!("  堆: 用于优先队列、堆排序");
    println!("  哈希表: O(1)查找，用于快速查找和计数");

    println!("\n✅ 数据结构演示完成！");
}
