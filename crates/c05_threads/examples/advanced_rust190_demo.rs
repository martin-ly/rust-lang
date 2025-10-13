//! Rust 1.90 Edition 2024 高级特性演示
//!
//! 本示例展示了 c05_threads 项目中实现的 Rust 1.90 最新特性：
//! - 高性能原子计数器
//! - 高级线程池
//! - 无锁环形缓冲区
//! - 内存预取优化
//! - SIMD 向量化操作
//! - 工作窃取模式

use c05_threads::rust_190_features::{
    demonstrate_advanced_rust_190_features,
    HighPerformanceCounter,
    AdvancedThreadPool,
    LockFreeRingBuffer,
    MemoryPrefetchOptimizer,
    SimdOptimizer,
    AdvancedConcurrencyPatterns,
};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

fn main() {
    println!("=== Rust 1.90 Edition 2024 高级特性演示 ===\n");

    // 1. 高性能原子计数器演示
    println!("1. 高性能原子计数器演示:");
    let counter = HighPerformanceCounter::new();
    
    // 多线程递增测试
    let counter = Arc::new(counter);
    let mut handles = vec![];
    
    for i in 0..4 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..25000 {
                counter.increment_relaxed();
            }
            println!("线程 {} 完成", i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("最终计数值: {}", counter.get());
    println!("预期值: 100000\n");

    // 2. 高级线程池演示
    println!("2. 高级线程池演示:");
    let pool = AdvancedThreadPool::new(4);
    
    // 提交多个任务
    for i in 0..20 {
        pool.execute(move || {
            println!("执行任务 {}", i);
            thread::sleep(Duration::from_millis(10));
        });
    }
    
    // 等待任务完成
    thread::sleep(Duration::from_millis(200));
    println!("完成任务数: {}", pool.get_completed_tasks());
    pool.shutdown();
    println!();

    // 3. 无锁环形缓冲区演示
    println!("3. 无锁环形缓冲区演示:");
    let buffer = Arc::new(LockFreeRingBuffer::<1024>::new());
    
    // 生产者线程
    let producer_buffer = Arc::clone(&buffer);
    let producer = thread::spawn(move || {
        for i in 0..1000 {
            while producer_buffer.try_push(i).is_err() {
                thread::yield_now();
            }
            if i % 100 == 0 {
                println!("生产者: 已推送 {} 个元素", i);
            }
        }
        println!("生产者完成");
    });

    // 消费者线程
    let consumer_buffer = Arc::clone(&buffer);
    let consumer = thread::spawn(move || {
        let mut count = 0;
        while count < 1000 {
            if consumer_buffer.try_pop().is_some() {
                count += 1;
                if count % 100 == 0 {
                    println!("消费者: 已消费 {} 个元素", count);
                }
            } else {
                thread::yield_now();
            }
        }
        println!("消费者完成");
    });

    producer.join().unwrap();
    consumer.join().unwrap();
    println!();

    // 4. 内存预取优化演示
    println!("4. 内存预取优化演示:");
    let optimizer = MemoryPrefetchOptimizer::new(64);
    let data: Vec<f64> = (1..=1000000).map(|i| i as f64).collect();
    
    let start = std::time::Instant::now();
    let sum = optimizer.optimized_vector_sum(&data);
    let duration = start.elapsed();
    
    println!("内存优化求和结果: {}", sum);
    println!("耗时: {:?}", duration);
    println!();

    // 5. SIMD 优化演示
    println!("5. SIMD 优化演示:");
    let a: Vec<f32> = (1..=1000000).map(|i| i as f32).collect();
    let b: Vec<f32> = (1..=1000000).map(|i| (i * 2) as f32).collect();
    
    let start = std::time::Instant::now();
    let result = SimdOptimizer::simd_vector_add(&a, &b);
    let duration = start.elapsed();
    
    println!("SIMD 向量加法完成");
    println!("结果长度: {}", result.len());
    println!("前5个结果: {:?}", &result[..5]);
    println!("耗时: {:?}", duration);
    println!();

    // 6. 工作窃取模式演示
    println!("6. 工作窃取模式演示:");
    AdvancedConcurrencyPatterns::work_stealing_demo();
    println!();

    // 7. 综合演示
    println!("7. 综合演示:");
    demonstrate_advanced_rust_190_features();
    
    println!("\n=== Rust 1.90 Edition 2024 高级特性演示完成 ===");
}
