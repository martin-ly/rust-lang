//! Rust 1.92.0 线程特性性能基准测试套件
//!
//! 本模块提供 Rust 1.92.0 新特性的性能基准测试，包括：
//! - rotate_right 在线程池管理中的性能
//! - NonZero::div_ceil 的计算性能
//! - MaybeUninit 在并发编程中的性能
//! - 线程池管理器的性能
//!
//! 运行方式:
//! ```bash
//! cargo bench --bench rust_192_benchmarks
//! ```

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use std::hint::black_box;
use std::num::NonZeroUsize;
use std::sync::Arc;
use std::thread;

use c05_threads::rust_192_features::{
    ThreadPoolTaskQueue, ThreadPoolManager, ThreadResourceAllocator,
    ThreadTask, calculate_thread_pool_size, ThreadSchedulingConfig,
    ThreadSafeUninitBuffer,
};

/// 基准测试 rotate_right 在线程池任务队列中的性能
fn bench_rotate_right_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("rotate_right_performance");
    group.throughput(Throughput::Elements(1));

    // 测试不同队列大小的轮转性能
    for size in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("rotate_queue", size),
            size,
            |b, &size| {
                b.iter(|| {
                    let mut queue = ThreadPoolTaskQueue::new();

                    // 填充队列
                    for i in 0..size {
                        queue.push(ThreadTask {
                            id: i as u64,
                            priority: (i % 256) as u8,
                        });
                    }

                    // 执行轮转
                    queue.rotate(size / 2);

                    black_box(&queue);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试 NonZero::div_ceil 的计算性能
fn bench_div_ceil_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("div_ceil_performance");
    group.throughput(Throughput::Elements(1));

    // 测试不同大小的池计算
    let sizes: &[(usize, usize)] = &[
        (100, 10),
        (1000, 50),
        (10000, 100),
        (100000, 500),
        (1000000, 1000),
    ];

    for (total, per_thread) in sizes {
        let per_thread_nonzero = NonZeroUsize::new(*per_thread).unwrap();
        group.bench_with_input(
            BenchmarkId::new("calculate_pool_size", format!("{}/{}", total, per_thread)),
            &(*total, per_thread_nonzero),
            |b, (total, per_thread)| {
                b.iter(|| {
                    let result = calculate_thread_pool_size(*total, *per_thread);
                    black_box(result);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试线程资源分配器的性能
fn bench_resource_allocator_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("resource_allocator_performance");

    // 测试不同配置的资源分配器
    let configs: &[(usize, usize)] = &[
        (16, 2),
        (32, 4),
        (64, 8),
        (128, 16),
    ];

    for (total, per_thread) in configs {
        let per_thread_nonzero = NonZeroUsize::new(*per_thread).unwrap();
        group.bench_with_input(
            BenchmarkId::new("max_threads", format!("{}/{}", total, per_thread)),
            &(*total, per_thread_nonzero),
            |b, (total, per_thread)| {
                let allocator = ThreadResourceAllocator::new(*total, *per_thread);
                b.iter(|| {
                    let result = allocator.max_threads();
                    black_box(result);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试线程调度配置的性能
fn bench_scheduling_config_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("scheduling_config_performance");

    let config = ThreadSchedulingConfig::new(NonZeroUsize::new(2).unwrap(), 10);

    // 测试不同任务数量的计算
    for task_count in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("calculate_threads", task_count),
            task_count,
            |b, &count| {
                b.iter(|| {
                    let result = config.calculate_threads_for_tasks(count);
                    black_box(result);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试线程池管理器的性能
fn bench_thread_pool_manager_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("thread_pool_manager_performance");
    group.throughput(Throughput::Elements(1));

    // 测试不同任务数量的管理性能
    for task_count in [10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("manage_tasks", task_count),
            task_count,
            |b, &count| {
                b.iter(|| {
                    let manager = ThreadPoolManager::new();

                    // 添加任务
                    for i in 0..count {
                        manager.add_task(ThreadTask {
                            id: i as u64,
                            priority: (i % 256) as u8,
                        });
                    }

                    // 执行轮转
                    manager.rotate();

                    // 处理所有任务
                    let mut processed = 0;
                    while manager.next_task().is_some() {
                        processed += 1;
                    }

                    black_box(processed);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试线程池管理器的并发性能
fn bench_concurrent_manager_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_manager_operations");
    group.throughput(Throughput::Elements(1));

    // 测试并发添加和轮转
    for concurrent_tasks in [10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("concurrent_operations", concurrent_tasks),
            concurrent_tasks,
            |b, &count| {
                b.iter(|| {
                    let manager = Arc::new(ThreadPoolManager::new());
                    let mut handles = vec![];

                    // 并发添加任务
                    for i in 0..count {
                        let manager_clone = manager.clone();
                        let handle = thread::spawn(move || {
                            manager_clone.add_task(ThreadTask {
                                id: i as u64,
                                priority: (i % 256) as u8,
                            });
                        });
                        handles.push(handle);
                    }

                    // 等待所有任务添加完成
                    for handle in handles {
                        handle.join().unwrap();
                    }

                    // 执行轮转
                    manager.rotate();

                    // 处理所有任务
                    let mut processed = 0;
                    while manager.next_task().is_some() {
                        processed += 1;
                    }

                    black_box(processed);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试 MaybeUninit 缓冲区的性能
fn bench_maybe_uninit_buffer_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("maybe_uninit_buffer_performance");

    // 测试不同大小的缓冲区
    for size in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("buffer_operations", size),
            size,
            |b, &size| {
                b.iter(|| {
                    let mut buffer = ThreadSafeUninitBuffer::<i32>::new(size);

                    // 初始化数据
                    unsafe {
                        for i in 0..size {
                            buffer.init_at(i, i as i32);
                        }
                    }

                    // 读取数据
                    let mut sum = 0;
                    unsafe {
                        for i in 0..size {
                            sum += *buffer.get(i);
                        }
                    }

                    black_box(sum);
                });
            },
        );
    }

    group.finish();
}

/// 综合性能基准测试：完整的线程池处理流程
fn bench_complete_workflow_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("complete_workflow_performance");
    group.throughput(Throughput::Elements(1));

    // 测试完整工作流程
    for workflow_size in [100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("complete_workflow", workflow_size),
            workflow_size,
            |b, &size| {
                b.iter(|| {
                    // 1. 创建资源分配器
                    let allocator = ThreadResourceAllocator::new(16, NonZeroUsize::new(2).unwrap());
                    let max_threads = allocator.max_threads();
                    black_box(max_threads);

                    // 2. 创建任务队列
                    let mut queue = ThreadPoolTaskQueue::new();
                    for i in 0..size {
                        queue.push(ThreadTask {
                            id: i as u64,
                            priority: (i % 256) as u8,
                        });
                    }

                    // 3. 轮转队列
                    queue.rotate(size / 2);

                    // 4. 创建管理器并添加任务
                    let manager = ThreadPoolManager::new();
                    while let Some(task) = queue.pop() {
                        manager.add_task(task);
                    }

                    // 5. 执行轮转
                    manager.rotate();

                    // 6. 处理所有任务
                    let mut processed = 0;
                    while manager.next_task().is_some() {
                        processed += 1;
                    }

                    black_box(processed);
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_rotate_right_performance,
    bench_div_ceil_performance,
    bench_resource_allocator_performance,
    bench_scheduling_config_performance,
    bench_thread_pool_manager_performance,
    bench_concurrent_manager_operations,
    bench_maybe_uninit_buffer_performance,
    bench_complete_workflow_performance
);

criterion_main!(benches);
