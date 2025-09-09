//! 综合演示模块
//! 
//! 本模块展示了所有线程相关功能的综合使用

use std::thread;
use std::time::Duration;
use std::sync::Arc;

// 导入所有模块
pub mod concurrency {
    pub use super::super::concurrency::*;
}

pub mod lockfree {
    pub use super::super::lockfree::*;
}

pub mod synchronization {
    pub use super::super::synchronization::*;
}

pub mod parallelism {
    pub use super::super::paralelism::*;
}

pub mod threads {
    pub use super::super::threads::*;
}

pub mod message_passing {
    pub use super::super::message_passing::*;
}

/// 综合演示
pub fn run_comprehensive_demo() {
    println!("=== Rust 线程编程综合演示 ===");
    println!("本演示展示了Rust 1.89中线程编程的各种高级特性\n");
    
    // 1. 作用域线程演示
    println!("1. 作用域线程演示");
    println!("==================");
    concurrency::scoped_threads::demonstrate_scoped_threads();
    println!();
    
    // 2. 工作窃取演示
    println!("2. 工作窃取演示");
    println!("===============");
    concurrency::work_stealing::demonstrate_work_stealing();
    println!();
    
    // 3. 无锁数据结构演示
    println!("3. 无锁数据结构演示");
    println!("===================");
    lockfree::lockfree_ring_buffer::demonstrate_lockfree_ring_buffers();
    println!();
    
    // 4. 优先级通道演示
    println!("4. 优先级通道演示");
    println!("=================");
    message_passing::priority_channels::demonstrate_priority_channels();
    println!();
    
    // 5. 背压处理演示
    println!("5. 背压处理演示");
    println!("===============");
    message_passing::backpressure_handling::demonstrate_backpressure_handling();
    println!();
    
    // 6. 自适应锁演示
    println!("6. 自适应锁演示");
    println!("===============");
    synchronization::adaptive_locks::demonstrate_adaptive_locks();
    println!();
    
    // 7. 无锁屏障演示
    println!("7. 无锁屏障演示");
    println!("===============");
    synchronization::lockfree_barrier::demonstrate_lockfree_barriers();
    println!();
    
    // 8. NUMA感知演示
    println!("8. NUMA感知演示");
    println!("===============");
    parallelism::numa_aware::demonstrate_numa_aware();
    println!();
    
    // 9. SIMD操作演示
    println!("9. SIMD操作演示");
    println!("===============");
    parallelism::simd_operations::demonstrate_simd_operations();
    println!();
    
    // 10. 高级并行算法演示
    println!("10. 高级并行算法演示");
    println!("====================");
    parallelism::advanced_parallel_algorithms::demonstrate_advanced_parallel_algorithms();
    println!();
    
    // 11. 线程亲和性演示
    println!("11. 线程亲和性演示");
    println!("==================");
    threads::thread_affinity::demonstrate_thread_affinity();
    println!();
    
    // 12. 优先级调度演示
    println!("12. 优先级调度演示");
    println!("==================");
    threads::priority_scheduling::demonstrate_priority_scheduling();
    println!();
    
    // 13. 性能监控演示
    println!("13. 性能监控演示");
    println!("==================");
    synchronization::performance_monitoring::demonstrate_performance_monitoring();
    println!();
    
    println!("=== 综合演示完成 ===");
    println!("所有线程编程功能演示完毕！");
}

/// 性能基准测试
pub fn run_performance_benchmarks() {
    println!("=== 性能基准测试 ===");
    
    // 测试不同排序算法的性能
    println!("1. 排序算法性能测试");
    println!("===================");
    
    let test_data = (1..=10000).rev().collect::<Vec<i32>>();
    
    // 测试并行归并排序
    let mut data1 = test_data.clone();
    let start = std::time::Instant::now();
    parallelism::advanced_parallel_algorithms::ParallelMergeSort::sort(&mut data1);
    let merge_sort_time = start.elapsed();
    println!("并行归并排序耗时: {:?}", merge_sort_time);
    
    // 测试并行快速排序
    let mut data2 = test_data.clone();
    let start = std::time::Instant::now();
    parallelism::advanced_parallel_algorithms::ParallelQuickSort::sort(&mut data2);
    let quick_sort_time = start.elapsed();
    println!("并行快速排序耗时: {:?}", quick_sort_time);
    
    // 测试并行基数排序
    let mut data3 = test_data.clone();
    let start = std::time::Instant::now();
    parallelism::advanced_parallel_algorithms::ParallelRadixSort::sort(&mut data3);
    let radix_sort_time = start.elapsed();
    println!("并行基数排序耗时: {:?}", radix_sort_time);
    
    println!();
    
    // 测试不同同步原语的性能
    println!("2. 同步原语性能测试");
    println!("===================");
    
    let iterations = 100000;
    let thread_count = 4;
    
    // 测试自适应锁
    let adaptive_lock = Arc::new(synchronization::adaptive_locks::AdaptiveMutex::new(0));
    let start = std::time::Instant::now();
    let handles: Vec<_> = (0..thread_count)
        .map(|_| {
            let lock = adaptive_lock.clone();
            thread::spawn(move || {
                for _ in 0..iterations / thread_count {
                    lock.lock(|data| {
                        *data += 1;
                    });
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    let adaptive_lock_time = start.elapsed();
    println!("自适应锁耗时: {:?}", adaptive_lock_time);
    
    // 测试无锁屏障
    let barrier = Arc::new(synchronization::lockfree_barrier::LockFreeBarrier::new(thread_count));
    let start = std::time::Instant::now();
    let handles: Vec<_> = (0..thread_count)
        .map(|_| {
            let barrier = barrier.clone();
            thread::spawn(move || {
                for _ in 0..iterations / thread_count {
                    barrier.wait();
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    let barrier_time = start.elapsed();
    println!("无锁屏障耗时: {:?}", barrier_time);
    
    println!();
    
    // 测试不同工作窃取策略的性能
    println!("3. 工作窃取策略性能测试");
    println!("=======================");
    
    let _task_count = 1000;
    
    // 测试基础工作窃取
    let start = std::time::Instant::now();
    #[cfg(feature = "work_stealing_examples")]
    concurrency::work_stealing::WorkStealingScheduler::<i32>::run_example();
    let basic_work_stealing_time = start.elapsed();
    println!("基础工作窃取耗时: {:?}", basic_work_stealing_time);
    
    // 测试优先级工作窃取
    let start = std::time::Instant::now();
    #[cfg(feature = "work_stealing_examples")]
    concurrency::work_stealing::PriorityWorkStealingScheduler::<i32>::run_example();
    let priority_work_stealing_time = start.elapsed();
    println!("优先级工作窃取耗时: {:?}", priority_work_stealing_time);
    
    // 测试自适应工作窃取
    let start = std::time::Instant::now();
    #[cfg(feature = "work_stealing_examples")]
    concurrency::work_stealing::AdaptiveWorkStealingScheduler::<i32>::run_example();
    let adaptive_work_stealing_time = start.elapsed();
    println!("自适应工作窃取耗时: {:?}", adaptive_work_stealing_time);
    
    println!();
    println!("=== 性能基准测试完成 ===");
}

/// 内存使用分析
pub fn run_memory_analysis() {
    println!("=== 内存使用分析 ===");
    
    // 分析不同数据结构的内存使用
    println!("1. 数据结构内存使用分析");
    println!("=======================");
    
    let element_count = 10000;
    
    // 分析无锁环形缓冲区（使用稳定提供的 Crossbeam 实现）
    let buffer = lockfree::lockfree_ring_buffer::CrossbeamRingBuffer::<i32>::new(element_count);
    let buffer_size = std::mem::size_of_val(&buffer);
    println!("Crossbeam环形缓冲区内存使用: {} 字节", buffer_size);
    
    // 分析无锁哈希表
    let hashmap = lockfree::lockfree_hashmap::LockFreeHashMap::<i32, i32>::new(element_count);
    let hashmap_size = std::mem::size_of_val(&hashmap);
    println!("无锁哈希表内存使用: {} 字节", hashmap_size);
    
    // 分析工作窃取调度器
    let scheduler = concurrency::work_stealing::WorkStealingScheduler::<i32>::new(4);
    let scheduler_size = std::mem::size_of_val(&scheduler);
    println!("工作窃取调度器内存使用: {} 字节", scheduler_size);
    
    println!();
    
    // 分析线程开销
    println!("2. 线程开销分析");
    println!("===============");
    
    let thread_count = 100;
    let mut handles = Vec::new();
    
    let start = std::time::Instant::now();
    for i in 0..thread_count {
        let handle = thread::spawn(move || {
            thread::sleep(Duration::from_millis(1));
            i
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    let thread_creation_time = start.elapsed();
    
    println!("创建 {} 个线程耗时: {:?}", thread_count, thread_creation_time);
    println!("平均每个线程创建耗时: {:?}", 
             thread_creation_time / thread_count as u32);
    
    println!();
    println!("=== 内存使用分析完成 ===");
}

/// 错误处理演示
pub fn run_error_handling_demo() {
    println!("=== 错误处理演示 ===");
    
    // 演示作用域线程中的错误处理
    println!("1. 作用域线程错误处理");
    println!("=====================");
    
    let mut demo = concurrency::scoped_threads::ScopedThreadsDemo::new(vec![0, 1, 2, 0, 3]);
    demo.error_handling_example();
    
    println!();
    
    // 演示背压处理中的错误处理
    println!("2. 背压处理错误处理");
    println!("===================");
    
    let config = message_passing::backpressure_handling::BackpressureConfig::default();
    let channel = message_passing::backpressure_handling::AdaptiveBackpressureChannel::new(config);
    
    // 尝试发送超出容量的消息
    for i in 0..10 {
        match channel.send(i) {
            Ok(()) => println!("成功发送消息: {}", i),
            Err(msg) => println!("发送失败，消息被丢弃: {}", msg),
        }
    }
    
    println!();
    println!("=== 错误处理演示完成 ===");
}

/// 运行所有演示
pub fn run_all_demos() {
    println!("开始运行所有演示...\n");
    
    run_comprehensive_demo();
    println!("\n{}\n", "=".repeat(50));
    
    run_performance_benchmarks();
    println!("\n{}\n", "=".repeat(50));
    
    run_memory_analysis();
    println!("\n{}\n", "=".repeat(50));
    
    run_error_handling_demo();
    
    println!("\n所有演示运行完成！");
}
