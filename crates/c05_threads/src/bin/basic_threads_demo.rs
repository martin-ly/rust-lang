//! 基础线程功能演示程序
//!
//! 本程序展示Rust中基础线程功能的使用，包括：
//! - 线程创建和管理
//! - 线程池使用
//! - 线程间通信
//! - 线程同步

use c05_threads::threads::{creation::*, thread_pool::*};
use std::thread;

fn main() {
    println!("🔧 Rust 基础线程功能演示");
    println!("============================\n");

    // 1. 基本线程创建演示
    println!("📋 1. 基本线程创建演示");
    println!("------------------------");
    basic_thread_creation();
    println!();

    // 2. 带参数的线程创建
    println!("📋 2. 带参数的线程创建");
    println!("------------------------");
    thread_with_parameters();
    println!();

    // 3. 线程命名演示
    println!("📋 3. 线程命名演示");
    println!("------------------------");
    named_threads();
    println!();

    // 4. 自定义栈大小线程
    println!("📋 4. 自定义栈大小线程");
    println!("------------------------");
    custom_stack_size_thread();
    println!();

    // 5. 多线程并行执行
    println!("📋 5. 多线程并行执行");
    println!("------------------------");
    parallel_execution();
    println!();

    // 6. 线程创建最佳实践
    println!("📋 6. 线程创建最佳实践");
    println!("------------------------");
    thread_best_practices();
    println!();

    // 7. 线程池演示
    println!("📋 7. 线程池演示");
    println!("------------------------");
    thread_pool_demo();
    println!();

    // 8. 线程池性能测试
    println!("📋 8. 线程池性能测试");
    println!("------------------------");
    benchmark_thread_pools();
    println!();

    println!("✅ 基础线程功能演示完成！");
}

/// 线程池演示
fn thread_pool_demo() {
    println!("🔧 线程池演示");

    // 简单线程池
    println!("  简单线程池示例:");
    let pool = SimpleThreadPool::new(3);

    let (tx, rx) = std::sync::mpsc::channel();

    for i in 0..5 {
        let tx = tx.clone();
        pool.execute(move || {
            println!("    任务 {} 在工作线程中执行", i);
            thread::sleep(std::time::Duration::from_millis(100));
            tx.send(i * i).unwrap();
        });
    }

    drop(tx); // 关闭发送端，让接收端知道没有更多数据

    let results: Vec<i32> = rx.iter().collect();
    println!("    任务结果: {:?}", results);

    // 可配置线程池
    println!("  可配置线程池示例:");
    let config = ThreadPoolConfig {
        min_threads: 2,
        max_threads: 4,
        keep_alive_time: std::time::Duration::from_secs(10),
        queue_size: 50,
    };

    let pool = ConfigurableThreadPool::new(config);
    println!("    线程池配置: {:?}", pool.config());
    println!("    当前线程数: {}", pool.thread_count());

    let (tx, rx) = std::sync::mpsc::channel();

    for i in 0..3 {
        let tx = tx.clone();
        pool.execute(move || {
            println!("    配置任务 {} 在工作线程中执行", i);
            thread::sleep(std::time::Duration::from_millis(50));
            tx.send(i * 10).unwrap();
        });
    }

    drop(tx);
    let results: Vec<i32> = rx.iter().collect();
    println!("    配置任务结果: {:?}", results);
}
