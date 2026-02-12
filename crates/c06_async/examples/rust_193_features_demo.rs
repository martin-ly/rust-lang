//! Rust 1.93.0 异步编程相关 API 演示
//!
//! 本示例展示 Rust 1.93.0 在异步编程场景中的新 API：
//! - Duration::from_nanos_u128 - 高精度纳秒级异步延迟
//! - VecDeque::pop_front_if - 异步任务队列的条件性消费
//! - slice::as_array - 异步流中固定大小块的处理
//!
//! 运行: cargo run -p c06_async --example rust_193_features_demo

use std::collections::VecDeque;
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() {
    println!("🚀 Rust 1.93.0 异步编程相关 API 演示\n");

    demonstrate_duration_async().await;
    demonstrate_vecdeque_async_task_queue().await;
    demonstrate_slice_as_array_async().await;

    println!("\n✅ 演示完成");
}

/// Duration::from_nanos_u128 (Rust 1.93) - 高精度纳秒延迟
async fn demonstrate_duration_async() {
    println!("--- Duration::from_nanos_u128 异步延迟 ---");
    let nanos: u128 = 100_000_000; // 100ms
    let d = Duration::from_nanos_u128(nanos);
    println!("  等待 {:?}...", d);
    sleep(d).await;
    println!("  完成");
}

/// VecDeque::pop_front_if (Rust 1.93) - 异步任务队列条件消费
async fn demonstrate_vecdeque_async_task_queue() {
    println!("\n--- VecDeque::pop_front_if 异步任务队列 ---");
    let mut queue = VecDeque::from([
        ("ready", 1),
        ("ready", 3),
        ("ready", 5),
        ("pending", 2),
        ("pending", 4),
    ]);

    let mut processed = 0;
    while let Some((_status, id)) = queue.pop_front_if(|(s, _)| *s == "ready") {
        println!("  处理就绪任务 ID={}", id);
        processed += 1;
    }
    println!("  已处理 {} 个就绪任务，剩余 {} 个待处理", processed, queue.len());
}

/// slice::as_array (Rust 1.93) - 异步流中固定大小块
async fn demonstrate_slice_as_array_async() {
    println!("\n--- slice::as_array 异步数据块处理 ---");
    let data = vec![1u8, 2, 3, 4, 5, 6, 7, 8];
    let mut chunks_processed = 0;

    for chunk in data.chunks(4) {
        if let Some(arr) = chunk.as_array::<4>() {
            tokio::task::yield_now().await;
            chunks_processed += 1;
            println!("  处理块 {}: {:?}", chunks_processed, arr);
        }
    }
    println!("  共处理 {} 个 4 元素块", chunks_processed);
}
