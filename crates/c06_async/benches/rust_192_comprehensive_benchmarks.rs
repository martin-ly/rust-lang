//! Rust 1.92.0 综合性能基准测试套件
//!
//! 本模块提供 Rust 1.92.0 新特性的性能基准测试，包括：
//! - rotate_right 在异步任务队列中的性能
//! - NonZero::div_ceil 的计算性能
//! - 迭代器方法特化的性能提升
//! - 异步任务调度器的性能
//!
//! 运行方式:
//! ```bash
//! cargo bench --bench rust_192_comprehensive_benchmarks
//! ```

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use std::sync::Arc;
use std::num::NonZeroUsize;
use tokio::runtime::Runtime;

use c06_async::rust_192_features::{
    AsyncTaskQueue, AsyncTaskScheduler, AsyncResourceAllocator,
    TaskItem, calculate_async_pool_size, compare_async_task_lists,
};

/// 基准测试 rotate_right 在异步任务队列中的性能
fn bench_rotate_right_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();

    let mut group = c.benchmark_group("rotate_right_performance");
    group.throughput(Throughput::Elements(1));

    // 测试不同队列大小的轮转性能
    for size in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("rotate_queue", size),
            size,
            |b, &size| {
                b.to_async(&rt).iter(|| async {
                    let mut queue: AsyncTaskQueue<u64> = AsyncTaskQueue::new();

                    // 填充队列
                    for i in 0..size {
                        queue.push(TaskItem {
                            id: i,
                            priority: (i % 256) as u8,
                            data: i,
                        });
                    }

                    // 执行轮转
                    queue.rotate((size / 2) as usize);

                    std::hint::black_box(&queue);
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
    let sizes = vec![
        (100, 10),
        (1000, 50),
        (10000, 100),
        (100000, 500),
        (1000000, 1000),
    ];

    for (total, per_worker) in sizes {
        let per_worker_nonzero = NonZeroUsize::new(per_worker).unwrap();
        group.bench_with_input(
            BenchmarkId::new("calculate_pool_size", format!("{}/{}", total, per_worker)),
            &(total, per_worker_nonzero),
            |b, &(total, per_worker)| {
                b.iter(|| {
                    let result = calculate_async_pool_size(total, per_worker);
                    std::hint::black_box(result);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试异步资源分配器的性能
fn bench_resource_allocator_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("resource_allocator_performance");

    // 测试不同配置的资源分配器
    let configs = vec![
        (1024, 64),
        (4096, 256),
        (16384, 1024),
        (65536, 4096),
    ];

    for (total, per_task) in configs {
        let per_task_nonzero = NonZeroUsize::new(per_task).unwrap();
        group.bench_with_input(
            BenchmarkId::new("max_concurrent_tasks", format!("{}/{}", total, per_task)),
            &(total, per_task_nonzero),
            |b, &(total, per_task)| {
                let allocator = AsyncResourceAllocator::new(total, per_task);
                b.iter(|| {
                    let result = allocator.max_concurrent_tasks();
                    std::hint::black_box(result);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试迭代器方法特化的性能
fn bench_iterator_specialization_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("iterator_specialization_performance");
    group.throughput(Throughput::Elements(1));

    // 创建测试数据
    for size in [10, 100, 1000, 10000].iter() {
        let list1: Vec<TaskItem<u64>> = (0..*size)
            .map(|i| TaskItem {
                id: i,
                priority: (i % 256) as u8,
                data: i,
            })
            .collect();
        let list2 = list1.clone();
        let list3: Vec<TaskItem<u64>> = (0..*size)
            .map(|i| TaskItem {
                id: i + 1, // 不同的 ID
                priority: (i % 256) as u8,
                data: i,
            })
            .collect();

        // 测试相等列表比较
        group.bench_with_input(
            BenchmarkId::new("compare_equal_lists", size),
            &(&list1, &list2),
            |b, (l1, l2)| {
                b.iter(|| {
                    let result = compare_async_task_lists(l1, l2);
                    std::hint::black_box(result);
                });
            },
        );

        // 测试不相等列表比较
        group.bench_with_input(
            BenchmarkId::new("compare_different_lists", size),
            &(&list1, &list3),
            |b, (l1, l3)| {
                b.iter(|| {
                    let result = compare_async_task_lists(l1, l3);
                    std::hint::black_box(result);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试异步任务调度器的性能
fn bench_task_scheduler_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();

    let mut group = c.benchmark_group("task_scheduler_performance");
    group.throughput(Throughput::Elements(1));

    // 测试不同任务数量的调度性能
    for task_count in [10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("schedule_tasks", task_count),
            task_count,
            |b, &count| {
                b.to_async(&rt).iter(|| async {
                    let scheduler = AsyncTaskScheduler::new(1);

                    // 添加任务
                    for i in 0..count {
                        scheduler.add_task(TaskItem {
                            id: i,
                            priority: (i % 256) as u8,
                            data: i,
                        }).await;
                    }

                    // 执行调度
                    scheduler.schedule().await;

                    // 处理所有任务
                    let mut processed = 0;
                    while scheduler.next_task().await.is_some() {
                        processed += 1;
                    }

                    std::hint::black_box(processed);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试异步任务队列的并发性能
fn bench_concurrent_queue_operations(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();

    let mut group = c.benchmark_group("concurrent_queue_operations");
    group.throughput(Throughput::Elements(1));

    // 测试并发添加和轮转
    for concurrent_tasks in [10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("concurrent_operations", concurrent_tasks),
            concurrent_tasks,
            |b, &count| {
                b.to_async(&rt).iter(|| async {
                    let scheduler = Arc::new(AsyncTaskScheduler::new(1));
                    let mut handles = vec![];

                    // 并发添加任务
                    for i in 0..count {
                        let scheduler_clone = scheduler.clone();
                        let handle = tokio::spawn(async move {
                            scheduler_clone.add_task(TaskItem {
                                id: i,
                                priority: (i % 256) as u8,
                                data: i,
                            }).await;
                        });
                        handles.push(handle);
                    }

                    // 等待所有任务添加完成
                    for handle in handles {
                        handle.await.unwrap();
                    }

                    // 执行调度
                    scheduler.schedule().await;

                    // 处理所有任务
                    let mut processed = 0;
                    while scheduler.next_task().await.is_some() {
                        processed += 1;
                    }

                    std::hint::black_box(processed);
                });
            },
        );
    }

    group.finish();
}

/// 综合性能基准测试：完整的异步任务处理流程
fn bench_complete_workflow_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();

    let mut group = c.benchmark_group("complete_workflow_performance");
    group.throughput(Throughput::Elements(1));

    // 测试完整工作流程
    for workflow_size in [100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("complete_workflow", workflow_size),
            workflow_size,
            |b, &size| {
                b.to_async(&rt).iter(|| async {
                    // 1. 创建资源分配器
                    let allocator = AsyncResourceAllocator::new(1024, NonZeroUsize::new(64).unwrap());
                    let max_tasks = allocator.max_concurrent_tasks();
                    std::hint::black_box(max_tasks);

                    // 2. 创建任务队列
                    let mut queue: AsyncTaskQueue<u64> = AsyncTaskQueue::new();
                    for i in 0..size {
                        queue.push(TaskItem {
                            id: i,
                            priority: (i % 256) as u8,
                            data: i,
                        });
                    }

                    // 3. 轮转队列
                    queue.rotate((size / 2) as usize);

                    // 4. 创建调度器并添加任务
                    let scheduler = AsyncTaskScheduler::new(1);
                    while let Some(task) = queue.pop() {
                        scheduler.add_task(task).await;
                    }

                    // 5. 执行调度
                    scheduler.schedule().await;

                    // 6. 处理所有任务
                    let mut processed = 0;
                    while scheduler.next_task().await.is_some() {
                        processed += 1;
                    }

                    std::hint::black_box(processed);
                });
            },
        );
    }

    group.finish();
}

/// 对比测试：rotate_right vs 手动实现
fn bench_rotate_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("rotate_comparison");

    for size in [100, 1000, 10000].iter() {
        // 测试 rotate_right
        group.bench_with_input(
            BenchmarkId::new("rotate_right", size),
            size,
            |b, &size| {
                let mut queue: AsyncTaskQueue<u64> = AsyncTaskQueue::new();
                for i in 0..size {
                    queue.push(TaskItem {
                        id: i as u64,
                        priority: (i % 256) as u8,
                        data: i as u64,
                    });
                }

                b.iter(|| {
                    queue.rotate(size / 2);
                });
            },
        );

        // 测试手动实现（用于对比）
        group.bench_with_input(
            BenchmarkId::new("manual_rotate", size),
            size,
            |b, &size| {
                let size_usize = size as usize;
                let mut vec: Vec<u64> = (0..size as u64).collect();

                b.iter(|| {
                    let rotate_by = size_usize / 2;
                    let mut rotated = vec![0u64; size_usize];
                    for i in 0..size_usize {
                        rotated[(i + rotate_by) % size_usize] = vec[i];
                    }
                    vec = rotated;
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
    bench_iterator_specialization_performance,
    bench_task_scheduler_performance,
    bench_concurrent_queue_operations,
    bench_complete_workflow_performance,
    bench_rotate_comparison
);

criterion_main!(benches);
