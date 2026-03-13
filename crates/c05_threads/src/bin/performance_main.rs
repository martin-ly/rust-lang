//! 多线程性能优化主程序
//!
//! 本程序展示Rust 2025版本的高级多线程优化技术，包括：
//! - 高性能线程池
//! - 工作窃取调度
//! - 无锁数据结构
//! - 并发算法优化
use c05_threads::{
    advanced_concurrency::{
        HighPerformanceThreadPool, LockFreeRingBuffer, LockFreeStack, parallel_map, parallel_reduce,
    },
    performance_benchmarks::{
        BenchmarkConfig, benchmark_concurrent_algorithms, benchmark_lock_free_structures,
        benchmark_thread_pools, generate_performance_report,
    },
};
use std::time::Instant;

fn main() {
    println!("🚀 Rust 2025 多线程性能优化演示");
    println!("=====================================\n");

    // 配置性能测试
    let config = BenchmarkConfig {
        data_size: 100_000, // 减少数据量以加快演示
        thread_counts: vec![1, 2, 4, 8],
        iterations: 5,
        warmup_iterations: 2,
    };

    // 1. 线程池性能对比测试
    println!("📊 执行线程池性能对比测试...");
    let thread_pool_results = benchmark_thread_pools(&config);

    // 2. 无锁数据结构性能测试
    println!("🔓 执行无锁数据结构性能测试...");
    let lock_free_results = benchmark_lock_free_structures(&config);

    // 3. 并发算法性能测试
    println!("⚡ 执行并发算法性能测试...");
    let algorithm_results = benchmark_concurrent_algorithms(&config);

    // 4. 合并所有结果
    let mut all_results = Vec::new();
    all_results.extend(thread_pool_results);
    all_results.extend(lock_free_results);
    all_results.extend(algorithm_results);

    // 5. 生成性能报告
    println!("📈 生成性能测试报告...");
    let report = generate_performance_report(&all_results);

    // 6. 输出报告
    println!("\n{}", report);

    // 7. 交互式性能演示
    println!("🎯 交互式性能演示");
    println!("==================\n");

    interactive_performance_demo();
}

/// 交互式性能演示
fn interactive_performance_demo() {
    let data_size = 1_000_000;
    let data: Vec<i32> = (0..data_size).collect();

    println!("数据集大小: {} 个元素", data_size);

    // 演示1: 高性能线程池
    println!("\n🔧 演示1: 高性能线程池");
    demo_high_performance_thread_pool(&data);

    // 演示2: 无锁数据结构
    println!("\n🔓 演示2: 无锁数据结构");
    demo_lock_free_structures();

    // 演示3: 并发算法
    println!("\n⚡ 演示3: 并发算法");
    demo_concurrent_algorithms(&data);

    // 演示4: 性能对比
    println!("\n📊 演示4: 性能对比");
    demo_performance_comparison(&data);
}

/// 演示高性能线程池
fn demo_high_performance_thread_pool(data: &[i32]) {
    let data = data.to_vec();
    let thread_counts = [1, 2, 4, 8];

    for &thread_count in &thread_counts {
        let pool = HighPerformanceThreadPool::new(thread_count);

        let start = Instant::now();
        let data_clone1 = data.clone();
        let data_clone2 = data.clone();
        let data_clone3 = data.clone();
        let data_clone4 = data.clone();

        let results = pool.execute_batch(vec![
            Box::new(move || data_clone1.iter().map(|&x| x * 2).sum::<i32>()),
            Box::new(move || data_clone2.iter().map(|&x| x * 3).sum::<i32>()),
            Box::new(move || data_clone3.iter().map(|&x| x * 4).sum::<i32>()),
            Box::new(move || data_clone4.iter().map(|&x| x * 5).sum::<i32>()),
        ]);
        let duration = start.elapsed();

        println!(
            "  {} 线程: {:?} (结果: {:?})",
            thread_count, duration, results
        );

        let stats = pool.stats();
        println!(
            "    统计: 总任务={}, 当前任务={}, 窃取任务={}",
            stats.total_tasks, stats.current_tasks, stats.stolen_tasks
        );
    }
}

/// 演示无锁数据结构
fn demo_lock_free_structures() {
    // 无锁环形缓冲区
    let buffer = LockFreeRingBuffer::new(1000);
    let start = Instant::now();

    for i in 0..1000 {
        buffer.try_push(i).unwrap();
    }

    let mut sum = 0;
    for _ in 0..1000 {
        if let Some(value) = buffer.try_pop() {
            sum += value;
        }
    }

    let duration = start.elapsed();
    println!("  无锁环形缓冲区: {:?} (总和: {})", duration, sum);

    // 无锁栈
    let stack = LockFreeStack::new(1000);
    let start = Instant::now();

    for i in 0..1000 {
        stack.push(i).unwrap();
    }

    let mut sum = 0;
    for _ in 0..1000 {
        if let Some(value) = stack.pop() {
            sum += value;
        }
    }

    let duration = start.elapsed();
    println!("  无锁栈: {:?} (总和: {})", duration, sum);
}

/// 演示并发算法
fn demo_concurrent_algorithms(data: &[i32]) {
    let thread_counts = [1, 2, 4, 8];

    for &thread_count in &thread_counts {
        // 并发归约
        let start = Instant::now();
        let sum = parallel_reduce(data, thread_count, 0, |acc, x| acc + x);
        let duration = start.elapsed();
        println!(
            "  并发归约 ({} 线程): {:?} (总和: {})",
            thread_count, duration, sum
        );

        // 并发映射
        let start = Instant::now();
        let mapped = parallel_map(data, thread_count, |&x| x * 2 + 1);
        let duration = start.elapsed();
        println!(
            "  并发映射 ({} 线程): {:?} (样本: {:?})",
            thread_count,
            duration,
            &mapped[..5]
        );
    }
}

/// 演示性能对比
fn demo_performance_comparison(data: &[i32]) {
    println!("  串行处理 vs 并行处理对比:");

    // 串行处理
    let start = Instant::now();
    let serial_result: Vec<i32> = data.iter().map(|&x| x * 2 + 1).collect();
    let serial_duration = start.elapsed();
    println!(
        "    串行: {:?} (样本: {:?})",
        serial_duration,
        &serial_result[..5]
    );

    // 并行处理
    let start = Instant::now();
    let parallel_result = parallel_map(data, 8, |&x| x * 2 + 1);
    let parallel_duration = start.elapsed();
    println!(
        "    并行: {:?} (样本: {:?})",
        parallel_duration,
        &parallel_result[..5]
    );

    // 计算加速比
    let speedup = serial_duration.as_micros() as f64 / parallel_duration.as_micros() as f64;
    println!("    加速比: {:.2}x", speedup);

    // 验证结果一致性
    let is_consistent = serial_result == parallel_result;
    println!(
        "    结果一致性: {}",
        if is_consistent { "✅" } else { "❌" }
    );
}

/// 内存使用监控
#[allow(dead_code)]
fn monitor_memory_usage() {
    // 这里可以添加内存使用监控代码
    // 在实际应用中，可以使用jemalloc或其他内存分配器
    println!("💾 内存使用监控功能已启用");
}

/// 性能优化建议
#[allow(dead_code)]
fn provide_optimization_suggestions() {
    println!("\n💡 性能优化建议:");
    println!("  1. 使用适当数量的线程 (通常等于CPU核心数)");
    println!("  2. 避免频繁的内存分配和释放");
    println!("  3. 使用无锁数据结构减少锁竞争");
    println!("  4. 合理设置任务粒度，避免任务过小");
    println!("  5. 使用工作窃取调度算法平衡负载");
    println!("  6. 考虑使用SIMD指令进行向量化");
    println!("  7. 监控CPU缓存命中率");
    println!("  8. 使用性能分析工具识别瓶颈");
}
