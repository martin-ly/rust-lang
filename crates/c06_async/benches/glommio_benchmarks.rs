//! # Glommio 性能基准测试
//!
//! 对 Glommio 运行时与其他运行时进行全面的性能对比测试。
//!
//! ## 运行基准测试
//!
//! ```bash
//! # 运行所有基准测试
//! cargo bench --bench glommio_benchmarks
//!
//! # 仅在 Linux 上运行
//! cargo bench --bench glommio_benchmarks --target x86_64-unknown-linux-gnu
//! ```

#![cfg(target_os = "linux")]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::time::Duration;

// ============================================================================
// 1. 任务创建与切换性能测试
// ============================================================================

#[cfg(target_os = "linux")]
fn bench_task_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("task_creation");
    group.throughput(Throughput::Elements(1000));

    // Glommio 任务创建
    group.bench_function("glommio", |b| {
        b.iter(|| {
            use glommio::{LocalExecutor, Task};

            LocalExecutor::default().run(async {
                let mut tasks = Vec::with_capacity(1000);
                for i in 0..1000 {
                    let task = Task::local(async move { black_box(i * 2) });
                    tasks.push(task);
                }

                for task in tasks {
                    black_box(task.await);
                }
            });
        });
    });

    // Tokio 任务创建
    group.bench_function("tokio", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let mut set = tokio::task::JoinSet::new();
                for i in 0..1000 {
                    set.spawn(async move { black_box(i * 2) });
                }

                while let Some(result) = set.join_next().await {
                    black_box(result.unwrap());
                }
            });
        });
    });

    // Smol 任务创建
    group.bench_function("smol", |b| {
        b.iter(|| {
            smol::block_on(async {
                let mut tasks = Vec::with_capacity(1000);
                for i in 0..1000 {
                    let task = smol::spawn(async move { black_box(i * 2) });
                    tasks.push(task);
                }

                for task in tasks {
                    black_box(task.await);
                }
            });
        });
    });

    group.finish();
}

// ============================================================================
// 2. I/O 性能测试
// ============================================================================

#[cfg(target_os = "linux")]
fn bench_file_io(c: &mut Criterion) {
    let mut group = c.benchmark_group("file_io");
    group.throughput(Throughput::Bytes(4096));

    let test_data = vec![0u8; 4096];

    // Glommio DMA 文件 I/O
    group.bench_function("glommio_dma", |b| {
        b.iter(|| {
            use glommio::{io::DmaFile, LocalExecutor};

            LocalExecutor::default().run(async {
                let path = "/tmp/glommio_bench.dat";

                // 写入
                let file = DmaFile::create(path).await.unwrap();
                file.write_at(test_data.clone(), 0).await.unwrap();
                file.close().await.unwrap();

                // 读取
                let file = DmaFile::open(path).await.unwrap();
                let buf = file.read_at(0, 4096).await.unwrap();
                file.close().await.unwrap();

                // 清理
                std::fs::remove_file(path).unwrap();

                black_box(buf);
            });
        });
    });

    // Tokio 异步文件 I/O
    group.bench_function("tokio_async", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                use tokio::io::{AsyncReadExt, AsyncWriteExt};

                let path = "/tmp/tokio_bench.dat";

                // 写入
                let mut file = tokio::fs::File::create(path).await.unwrap();
                file.write_all(&test_data).await.unwrap();

                // 读取
                let mut file = tokio::fs::File::open(path).await.unwrap();
                let mut buf = vec![0u8; 4096];
                file.read_exact(&mut buf).await.unwrap();

                // 清理
                tokio::fs::remove_file(path).await.unwrap();

                black_box(buf);
            });
        });
    });

    group.finish();
}

// ============================================================================
// 3. 并发任务性能测试
// ============================================================================

#[cfg(target_os = "linux")]
fn bench_concurrent_tasks(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_tasks");

    for size in [100, 1000, 10000].iter() {
        group.throughput(Throughput::Elements(*size));

        // Glommio
        group.bench_with_input(BenchmarkId::new("glommio", size), size, |b, &size| {
            b.iter(|| {
                use glommio::{LocalExecutor, Task};

                LocalExecutor::default().run(async {
                    let tasks: Vec<_> = (0..size)
                        .map(|i| {
                            Task::local(async move {
                                glommio::timer::sleep(Duration::from_micros(1)).await;
                                black_box(i * 2)
                            })
                        })
                        .collect();

                    let results = futures::future::join_all(tasks).await;
                    black_box(results);
                });
            });
        });

        // Tokio
        group.bench_with_input(BenchmarkId::new("tokio", size), size, |b, &size| {
            b.iter(|| {
                let rt = tokio::runtime::Runtime::new().unwrap();
                rt.block_on(async {
                    let mut set = tokio::task::JoinSet::new();

                    for i in 0..size {
                        set.spawn(async move {
                            tokio::time::sleep(Duration::from_micros(1)).await;
                            black_box(i * 2)
                        });
                    }

                    let mut results = Vec::new();
                    while let Some(result) = set.join_next().await {
                        results.push(result.unwrap());
                    }
                    black_box(results);
                });
            });
        });

        // Smol
        group.bench_with_input(BenchmarkId::new("smol", size), size, |b, &size| {
            b.iter(|| {
                smol::block_on(async {
                    let tasks: Vec<_> = (0..size)
                        .map(|i| {
                            smol::spawn(async move {
                                smol::Timer::after(Duration::from_micros(1)).await;
                                black_box(i * 2)
                            })
                        })
                        .collect();

                    let mut results = Vec::new();
                    for task in tasks {
                        results.push(task.await);
                    }
                    black_box(results);
                });
            });
        });
    }

    group.finish();
}

// ============================================================================
// 4. CPU 密集型任务性能测试
// ============================================================================

#[cfg(target_os = "linux")]
fn bench_cpu_intensive(c: &mut Criterion) {
    let mut group = c.benchmark_group("cpu_intensive");

    // Glommio
    group.bench_function("glommio", |b| {
        b.iter(|| {
            use glommio::{LocalExecutor, Task};

            LocalExecutor::default().run(async {
                let tasks: Vec<_> = (0..4)
                    .map(|_| {
                        Task::local(async move {
                            let mut sum = 0u64;
                            for i in 0..1_000_000 {
                                sum = sum.wrapping_add(i);
                            }
                            black_box(sum)
                        })
                    })
                    .collect();

                let results = futures::future::join_all(tasks).await;
                black_box(results);
            });
        });
    });

    // Tokio
    group.bench_function("tokio", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let mut set = tokio::task::JoinSet::new();

                for _ in 0..4 {
                    set.spawn(async move {
                        let mut sum = 0u64;
                        for i in 0..1_000_000 {
                            sum = sum.wrapping_add(i);
                        }
                        black_box(sum)
                    });
                }

                let mut results = Vec::new();
                while let Some(result) = set.join_next().await {
                    results.push(result.unwrap());
                }
                black_box(results);
            });
        });
    });

    group.finish();
}

// ============================================================================
// 5. 延迟测试
// ============================================================================

#[cfg(target_os = "linux")]
fn bench_latency(c: &mut Criterion) {
    let mut group = c.benchmark_group("latency");
    group.measurement_time(Duration::from_secs(10));

    // Glommio 延迟
    group.bench_function("glommio", |b| {
        b.iter(|| {
            use glommio::{LocalExecutor, Task};

            LocalExecutor::default().run(async {
                let start = std::time::Instant::now();
                let task = Task::local(async { 42 });
                let result = task.await;
                let elapsed = start.elapsed();
                black_box((result, elapsed));
            });
        });
    });

    // Tokio 延迟
    group.bench_function("tokio", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let start = std::time::Instant::now();
                let task = tokio::spawn(async { 42 });
                let result = task.await.unwrap();
                let elapsed = start.elapsed();
                black_box((result, elapsed));
            });
        });
    });

    group.finish();
}

// ============================================================================
// 6. 内存使用测试
// ============================================================================

#[cfg(target_os = "linux")]
fn bench_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");
    group.throughput(Throughput::Elements(10000));

    // Glommio 内存使用
    group.bench_function("glommio", |b| {
        b.iter(|| {
            use glommio::{LocalExecutor, Task};

            LocalExecutor::default().run(async {
                let tasks: Vec<_> = (0..10000)
                    .map(|i| Task::local(async move { black_box(i) }))
                    .collect();

                for task in tasks {
                    black_box(task.await);
                }
            });
        });
    });

    // Tokio 内存使用
    group.bench_function("tokio", |b| {
        b.iter(|| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let mut set = tokio::task::JoinSet::new();
                for i in 0..10000 {
                    set.spawn(async move { black_box(i) });
                }

                while let Some(result) = set.join_next().await {
                    black_box(result.unwrap());
                }
            });
        });
    });

    group.finish();
}

// ============================================================================
// Criterion 配置
// ============================================================================

#[cfg(target_os = "linux")]
criterion_group! {
    name = benches;
    config = Criterion::default()
        .measurement_time(Duration::from_secs(10))
        .sample_size(100)
        .warm_up_time(Duration::from_secs(3));
    targets =
        bench_task_creation,
        bench_file_io,
        bench_concurrent_tasks,
        bench_cpu_intensive,
        bench_latency,
        bench_memory_usage
}

#[cfg(target_os = "linux")]
criterion_main!(benches);

#[cfg(not(target_os = "linux"))]
fn main() {
    println!("❌ 错误: Glommio 基准测试仅支持 Linux 系统");
    println!("   需要 Linux 5.1+ 版本 (io_uring 支持)");
}
