//! Rust 1.90.0 综合性能基准测试套件
//! 
//! 本模块提供全面的性能基准测试，包括：
//! - 基础异步操作性能
//! - 高级特性性能对比
//! - 内存使用效率
//! - 并发处理能力
//! - 不同运行时性能对比

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use std::time::Duration;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use tokio::runtime::Runtime;
use tokio::sync::Semaphore;
use tokio::time::sleep;

use c06_async::rust_190_real_stable_features::Rust190AsyncFeatures;
use c06_async::rust_190_advanced_features::AdvancedAsyncFeatures190;

/// 基础异步操作基准测试
fn bench_basic_async_operations(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("basic_async_operations");
    group.throughput(Throughput::Elements(1));
    
    // 异步睡眠基准测试
    group.bench_function("async_sleep_1ms", |b| {
        b.to_async(&rt).iter(|| async {
            sleep(Duration::from_millis(1)).await;
        });
    });
    
    // 异步计算基准测试
    group.bench_function("async_computation", |b| {
        b.to_async(&rt).iter(|| async {
            let mut sum = 0;
            for i in 0..1000 {
                sum += i;
            }
            std::hint::black_box(sum);
        });
    });
    
    // 异步任务创建基准测试
    group.bench_function("async_task_creation", |b| {
        b.to_async(&rt).iter(|| async {
            let handle = tokio::spawn(async {
                sleep(Duration::from_micros(100)).await;
                42
            });
            let result = handle.await.unwrap();
            std::hint::black_box(result);
        });
    });
    
    group.finish();
}

/// 并发处理基准测试
fn bench_concurrent_processing(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("concurrent_processing");
    
    for &task_count in &[10, 50, 100, 500, 1000] {
        group.throughput(Throughput::Elements(task_count));
        group.bench_with_input(
            BenchmarkId::new("concurrent_tasks", task_count),
            &task_count,
            |b, &task_count| {
                b.to_async(&rt).iter(|| async {
                    let handles: Vec<_> = (0..task_count)
                        .map(|i| {
                            tokio::spawn(async move {
                                sleep(Duration::from_micros(100)).await;
                                i * 2
                            })
                        })
                        .collect();
                    
                    let results = futures::future::join_all(handles).await;
                    std::hint::black_box(results);
                });
            },
        );
    }
    
    group.finish();
}

/// 资源池性能基准测试
fn bench_resource_pool_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("resource_pool_performance");
    
    for &pool_size in &[10, 50, 100, 500] {
        group.throughput(Throughput::Elements(pool_size));
        group.bench_with_input(
            BenchmarkId::new("resource_pool_operations", pool_size),
            &pool_size,
            |b, &pool_size| {
                b.to_async(&rt).iter(|| async {
                    let pool = Arc::new(AdvancedAsyncFeatures190::new());
                    
                    let handles: Vec<_> = (0..pool_size)
                        .map(|_| {
                            let pool = Arc::clone(&pool);
                            tokio::spawn(async move {
                                pool.demo_advanced_resource_pool().await
                            })
                        })
                        .collect();
                    
                    let results = futures::future::join_all(handles).await;
                    std::hint::black_box(results);
                });
            },
        );
    }
    
    group.finish();
}

/// 缓存性能基准测试
fn bench_cache_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("cache_performance");
    
    for &cache_size in &[100, 1000, 10000] {
        group.throughput(Throughput::Elements(cache_size));
        group.bench_with_input(
            BenchmarkId::new("cache_operations", cache_size),
            &cache_size,
            |b, &cache_size| {
                b.to_async(&rt).iter(|| async {
                    let features = AdvancedAsyncFeatures190::new();
                    
                    // 模拟缓存操作
                    for i in 0..cache_size {
                        features.demo_smart_async_cache().await.unwrap();
                        if i % 100 == 0 {
                            // 模拟缓存刷新
                            sleep(Duration::from_micros(10)).await;
                        }
                    }
                });
            },
        );
    }
    
    group.finish();
}

/// 流处理性能基准测试
fn bench_stream_processing(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("stream_processing");
    
    for &item_count in &[100, 500, 1000, 5000] {
        group.throughput(Throughput::Elements(item_count));
        group.bench_with_input(
            BenchmarkId::new("stream_items", item_count),
            &item_count,
            |b, &item_count| {
                b.to_async(&rt).iter(|| async {
                    let features = AdvancedAsyncFeatures190::new();
                    
                    // 模拟流处理
                    for i in 0..item_count {
                        features.demo_advanced_async_streams().await.unwrap();
                        if i % 100 == 0 {
                            sleep(Duration::from_micros(50)).await;
                        }
                    }
                });
            },
        );
    }
    
    group.finish();
}

/// 批处理性能基准测试
fn bench_batch_processing(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("batch_processing");
    
    for &batch_size in &[10, 50, 100, 500] {
        group.throughput(Throughput::Elements(batch_size));
        group.bench_with_input(
            BenchmarkId::new("batch_size", batch_size),
            &batch_size,
            |b, &batch_size| {
                b.to_async(&rt).iter(|| async {
                    let features = AdvancedAsyncFeatures190::new();
                    
                    // 模拟批处理
                    for _ in 0..batch_size {
                        features.demo_async_batch_processing().await.unwrap();
                    }
                });
            },
        );
    }
    
    group.finish();
}

/// Rust 1.90.0 特性性能对比基准测试
fn bench_rust_190_features_comparison(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("rust_190_features_comparison");
    group.throughput(Throughput::Elements(1));
    
    // 基础特性 vs 高级特性对比
    group.bench_function("basic_features", |b| {
        b.to_async(&rt).iter(|| async {
            let features = Rust190AsyncFeatures::new();
            features.demo_enhanced_async_resource_management().await.unwrap();
        });
    });
    
    group.bench_function("advanced_features", |b| {
        b.to_async(&rt).iter(|| async {
            let features = AdvancedAsyncFeatures190::new();
            features.demo_advanced_resource_pool().await.unwrap();
        });
    });
    
    group.finish();
}

/// 内存使用效率基准测试
fn bench_memory_efficiency(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("memory_efficiency");
    
    for &allocation_count in &[100, 1000, 10000] {
        group.throughput(Throughput::Elements(allocation_count));
        group.bench_with_input(
            BenchmarkId::new("memory_allocation", allocation_count),
            &allocation_count,
            |b, &allocation_count| {
                b.to_async(&rt).iter(|| async {
                    let mut data = Vec::with_capacity(allocation_count as usize);
                    
                    for i in 0..allocation_count as usize {
                        data.push(vec![i as u8; 1024]);
                        
                        if i % 100 == 0 {
                            // 模拟内存清理
                            data.truncate(data.len() / 2);
                        }
                    }
                    
                    std::hint::black_box(data);
                });
            },
        );
    }
    
    group.finish();
}

/// 错误处理性能基准测试
fn bench_error_handling_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("error_handling_performance");
    
    for &error_rate in &[0.1, 0.2, 0.5] {
        group.throughput(Throughput::Elements(1000));
        group.bench_with_input(
            BenchmarkId::new("error_rate", (error_rate * 100.0) as u32),
            &error_rate,
            |b, &error_rate| {
                b.to_async(&rt).iter(|| async {
                    let features = Rust190AsyncFeatures::new();
                    
                    // 模拟不同错误率的处理
                    for i in 0..1000 {
                        if (i as f64 / 1000.0) < error_rate {
                            // 模拟错误情况
                            let _ = features.demo_enhanced_async_error_handling().await;
                        } else {
                            // 正常处理
                            let _ = features.demo_performance_optimized_async().await;
                        }
                    }
                });
            },
        );
    }
    
    group.finish();
}

/// 综合性能基准测试
fn bench_comprehensive_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("comprehensive_performance");
    group.throughput(Throughput::Elements(1));
    
    // 完整特性演示基准测试
    group.bench_function("complete_basic_demo", |b| {
        b.to_async(&rt).iter(|| async {
            let features = Rust190AsyncFeatures::new();
            features.run_all_demos().await.unwrap();
        });
    });
    
    group.bench_function("complete_advanced_demo", |b| {
        b.to_async(&rt).iter(|| async {
            let features = AdvancedAsyncFeatures190::new();
            features.demo_advanced_features().await.unwrap();
        });
    });
    
    group.finish();
}

/// 压力测试基准测试
fn bench_stress_test(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("stress_test");
    
    for &concurrent_level in &[100, 500, 1000, 2000] {
        group.throughput(Throughput::Elements(concurrent_level));
        group.bench_with_input(
            BenchmarkId::new("concurrent_level", concurrent_level),
            &concurrent_level,
            |b, &concurrent_level| {
                b.to_async(&rt).iter(|| async {
                    let semaphore = Arc::new(Semaphore::new(concurrent_level as usize));
                    let counter = Arc::new(AtomicUsize::new(0));
                    
                    let handles: Vec<_> = (0..concurrent_level as usize)
                        .map(|_| {
                            let semaphore = Arc::clone(&semaphore);
                            let counter = Arc::clone(&counter);
                            
                            tokio::spawn(async move {
                                let _permit = semaphore.acquire().await.unwrap();
                                
                                // 模拟一些工作
                                sleep(Duration::from_micros(100)).await;
                                
                                counter.fetch_add(1, Ordering::Relaxed);
                            })
                        })
                        .collect();
                    
                    futures::future::join_all(handles).await;
                    
                    let final_count = counter.load(Ordering::Relaxed);
                    std::hint::black_box(final_count);
                });
            },
        );
    }
    
    group.finish();
}

criterion_group!(
    benches,
    bench_basic_async_operations,
    bench_concurrent_processing,
    bench_resource_pool_performance,
    bench_cache_performance,
    bench_stream_processing,
    bench_batch_processing,
    bench_rust_190_features_comparison,
    bench_memory_efficiency,
    bench_error_handling_performance,
    bench_comprehensive_performance,
    bench_stress_test
);

criterion_main!(benches);
