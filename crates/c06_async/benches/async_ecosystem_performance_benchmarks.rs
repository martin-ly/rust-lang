//! 异步生态系统性能基准测试套件
//!
//! 本基准测试套件用于测试和比较不同异步运行时的性能，
//! 包括std、tokio、async-std、smol等库的性能对比

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use std::time::Duration;
use std::sync::Arc;
use tokio::time::sleep;
use tokio::sync::{Mutex, Semaphore};
use c06_async::async_runtime_integration_framework_simple::*;

/// 基准测试：单个任务执行性能
fn benchmark_single_task_execution(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    c.bench_function("single_task_execution", |b| {
        b.to_async(&rt).iter(|| async {
            let config = RuntimeConfig::default();
            let framework = SimpleAsyncRuntimeFramework::new(config);

            let task = Box::new(ExampleTask::new("benchmark_task", TaskPriority::Normal, 1));
            let result = framework.execute_task(task).await;
            black_box(result)
        })
    });
}

/// 基准测试：批量任务执行性能
fn benchmark_batch_task_execution(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    let mut group = c.benchmark_group("batch_task_execution");

    for size in [10, 50, 100, 200].iter() {
        group.bench_with_input(BenchmarkId::new("batch_size", size), size, |b, &size| {
            b.to_async(&rt).iter(|| async {
                let config = RuntimeConfig {
                    max_concurrent_tasks: size,
                    ..Default::default()
                };
                let framework = SimpleAsyncRuntimeFramework::new(config);

                let mut tasks: Vec<Box<dyn AsyncTask>> = Vec::new();
                for i in 0..size {
                    let task = Box::new(ExampleTask::new(
                        &format!("batch_task_{}", i),
                        TaskPriority::Normal,
                        1
                    ));
                    tasks.push(task);
                }

                let results = framework.execute_batch(tasks).await;
                black_box(results)
            })
        });
    }

    group.finish();
}

/// 基准测试：不同优先级的任务执行性能
fn benchmark_task_priority_performance(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    let mut group = c.benchmark_group("task_priority_performance");

    let priorities = [
        ("low", TaskPriority::Low),
        ("normal", TaskPriority::Normal),
        ("high", TaskPriority::High),
        ("critical", TaskPriority::Critical),
    ];

    for (name, priority) in priorities.iter() {
        group.bench_with_input(BenchmarkId::new("priority", name), priority, |b, &priority| {
            b.to_async(&rt).iter(|| async {
                let config = RuntimeConfig::default();
                let framework = SimpleAsyncRuntimeFramework::new(config);

                let task = Box::new(ExampleTask::new("priority_task", priority, 1));
                let result = framework.execute_task(task).await;
                black_box(result)
            })
        });
    }

    group.finish();
}

/// 基准测试：异步同步转换性能
fn benchmark_async_sync_conversion(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    let mut group = c.benchmark_group("async_sync_conversion");

    // 异步到同步转换
    group.bench_function("async_to_sync", |b| {
        b.to_async(&rt).iter(|| async {
            let service = AsyncSyncConversionService::new(10);
            let result = service.async_to_sync(async {
                sleep(Duration::from_millis(1)).await;
                Ok("async_result".to_string())
            }).await;
            black_box(result)
        })
    });

    // 同步到异步转换
    group.bench_function("sync_to_async", |b| {
        b.to_async(&rt).iter(|| async {
            let service = AsyncSyncConversionService::new(10);
            let result = service.sync_to_async(|| {
                std::thread::sleep(Duration::from_millis(1));
                Ok("sync_result".to_string())
            }).await;
            black_box(result)
        })
    });

    // 混合转换
    group.bench_function("hybrid_conversion", |b| {
        b.to_async(&rt).iter(|| async {
            let service = AsyncSyncConversionService::new(10);
            let result = service.hybrid_conversion().await;
            black_box(result)
        })
    });

    group.finish();
}

/// 基准测试：聚合组合模式性能
fn benchmark_aggregation_composition(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    let mut group = c.benchmark_group("aggregation_composition");

    // 顺序聚合
    group.bench_function("sequential_aggregation", |b| {
        b.to_async(&rt).iter(|| async {
            let service = AggregationCompositionService::new();

            // 注册组件
            let component1 = Box::new(DataProcessingComponent::new("processor1", 1));
            let component2 = Box::new(DataProcessingComponent::new("processor2", 1));
            let component3 = Box::new(DataProcessingComponent::new("processor3", 1));

            service.register_component(component1).await.unwrap();
            service.register_component(component2).await.unwrap();
            service.register_component(component3).await.unwrap();

            let result = service.sequential_aggregation(
                vec!["processor1".to_string(), "processor2".to_string(), "processor3".to_string()],
                "input_data"
            ).await;
            black_box(result)
        })
    });

    // 并行聚合
    group.bench_function("parallel_aggregation", |b| {
        b.to_async(&rt).iter(|| async {
            let service = AggregationCompositionService::new();

            // 注册组件
            let component1 = Box::new(DataProcessingComponent::new("processor1", 1));
            let component2 = Box::new(DataProcessingComponent::new("processor2", 1));
            let component3 = Box::new(DataProcessingComponent::new("processor3", 1));

            service.register_component(component1).await.unwrap();
            service.register_component(component2).await.unwrap();
            service.register_component(component3).await.unwrap();

            let result = service.parallel_aggregation(
                vec!["processor1".to_string(), "processor2".to_string(), "processor3".to_string()],
                "input_data"
            ).await;
            black_box(result)
        })
    });

    group.finish();
}

/// 基准测试：并发安全性性能
fn benchmark_concurrency_safety(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    let mut group = c.benchmark_group("concurrency_safety");

    for concurrent_tasks in [10, 50, 100, 200].iter() {
        group.bench_with_input(BenchmarkId::new("concurrent_tasks", concurrent_tasks), concurrent_tasks, |b, &concurrent_tasks| {
            b.to_async(&rt).iter(|| async {
                let semaphore = Arc::new(Semaphore::new(concurrent_tasks));
                let counter = Arc::new(Mutex::new(0));

                let mut handles = Vec::new();

                for _i in 0..concurrent_tasks {
                    let semaphore = Arc::clone(&semaphore);
                    let counter = Arc::clone(&counter);

                    let handle = tokio::spawn(async move {
                        let _permit = semaphore.acquire().await.unwrap();
                        sleep(Duration::from_millis(1)).await;

                        let mut count = counter.lock().await;
                        *count += 1;
                    });

                    handles.push(handle);
                }

                // 等待所有任务完成
                for handle in handles {
                    handle.await.unwrap();
                }

                let final_count = *counter.lock().await;
                black_box(final_count)
            })
        });
    }

    group.finish();
}

/// 基准测试：内存使用性能
fn benchmark_memory_usage(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    c.bench_function("memory_usage", |b| {
        b.to_async(&rt).iter(|| async {
            let config = RuntimeConfig::default();
            let framework = SimpleAsyncRuntimeFramework::new(config);

            // 执行大量任务以测试内存使用
            for i in 0..1000 {
                let task = Box::new(ExampleTask::new(
                    &format!("memory_task_{}", i),
                    TaskPriority::Low,
                    0
                ));
                let _ = framework.execute_task(task).await;
            }

            let metrics = framework.get_metrics().await;
            black_box(metrics)
        })
    });
}

/// 基准测试：错误处理性能
fn benchmark_error_handling(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    c.bench_function("error_handling", |b| {
        b.to_async(&rt).iter(|| async {
            let config = RuntimeConfig::default();
            let framework = SimpleAsyncRuntimeFramework::new(config);

            // 创建会失败的任务
            let failing_task = Box::new(FailingTask::new("failing_task", TaskPriority::Normal, 1));
            let result = framework.execute_task(failing_task).await;

            // 验证错误处理
            assert!(result.is_err());

            let metrics = framework.get_metrics().await;
            black_box(metrics)
        })
    });
}

/// 失败任务实现（用于错误处理基准测试）
struct FailingTask {
    name: String,
    priority: TaskPriority,
    execution_delay: Duration,
}

impl FailingTask {
    fn new(name: &str, priority: TaskPriority, delay_ms: u64) -> Self {
        Self {
            name: name.to_string(),
            priority,
            execution_delay: Duration::from_millis(delay_ms),
        }
    }
}

#[async_trait::async_trait]
impl AsyncTask for FailingTask {
    async fn execute(&self) -> Result<String, anyhow::Error> {
        sleep(self.execution_delay).await;
        Err(anyhow::anyhow!("任务执行失败: {}", self.name))
    }

    fn get_name(&self) -> &str {
        &self.name
    }

    fn get_priority(&self) -> TaskPriority {
        self.priority
    }

    fn get_timeout(&self) -> Duration {
        Duration::from_secs(30)
    }
}

/// 基准测试：不同运行时类型的性能对比
fn benchmark_runtime_type_comparison(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    let mut group = c.benchmark_group("runtime_type_comparison");

    let runtime_types = [
        ("std", AsyncRuntimeType::Std),
        ("tokio", AsyncRuntimeType::Tokio),
        ("async-std", AsyncRuntimeType::AsyncStd),
        ("smol", AsyncRuntimeType::Smol),
    ];

    for (name, runtime_type) in runtime_types.iter() {
        group.bench_with_input(BenchmarkId::new("runtime_type", name), runtime_type, |b, &runtime_type| {
            b.to_async(&rt).iter(|| async {
                let config = RuntimeConfig {
                    runtime_type,
                    ..Default::default()
                };
                let framework = SimpleAsyncRuntimeFramework::new(config);

                let task = Box::new(ExampleTask::new("runtime_test_task", TaskPriority::Normal, 1));
                let result = framework.execute_task(task).await;
                black_box(result)
            })
        });
    }

    group.finish();
}

/// 基准测试：超时处理性能
fn benchmark_timeout_handling(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    let mut group = c.benchmark_group("timeout_handling");

    for timeout_ms in [10, 50, 100, 500].iter() {
        group.bench_with_input(BenchmarkId::new("timeout_ms", timeout_ms), timeout_ms, |b, &timeout_ms| {
            b.to_async(&rt).iter(|| async {
                let config = RuntimeConfig {
                    timeout_duration: Duration::from_millis(timeout_ms),
                    ..Default::default()
                };
                let framework = SimpleAsyncRuntimeFramework::new(config);

                // 创建一个执行时间超过超时时间的任务
                let task = Box::new(ExampleTask::new("timeout_task", TaskPriority::Normal, timeout_ms + 100));
                let result = framework.execute_task(task).await;
                black_box(result)
            })
        });
    }

    group.finish();
}

/// 基准测试：监控性能
fn benchmark_monitoring_performance(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    c.bench_function("monitoring_performance", |b| {
        b.to_async(&rt).iter(|| async {
            let config = RuntimeConfig {
                enable_monitoring: true,
                ..Default::default()
            };
            let framework = SimpleAsyncRuntimeFramework::new(config);

            // 执行一些任务
            for i in 0..100 {
                let task = Box::new(ExampleTask::new(
                    &format!("monitoring_task_{}", i),
                    TaskPriority::Normal,
                    1
                ));
                let _ = framework.execute_task(task).await;
            }

            // 获取监控指标
            let metrics = framework.get_metrics().await;
            black_box(metrics)
        })
    });
}

/// 基准测试：健康检查性能
fn benchmark_health_check_performance(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    let mut group = c.benchmark_group("health_check_performance");

    let runtime_types = [
        ("std", AsyncRuntimeType::Std),
        ("tokio", AsyncRuntimeType::Tokio),
        ("async-std", AsyncRuntimeType::AsyncStd),
        ("smol", AsyncRuntimeType::Smol),
    ];

    for (name, runtime_type) in runtime_types.iter() {
        group.bench_with_input(BenchmarkId::new("runtime_type", name), runtime_type, |b, &runtime_type| {
            b.to_async(&rt).iter(|| async {
                let config = RuntimeConfig {
                    runtime_type,
                    ..Default::default()
                };
                let framework = SimpleAsyncRuntimeFramework::new(config);

                let health_status = framework.health_check().await;
                black_box(health_status)
            })
        });
    }

    group.finish();
}

/// 基准测试：压力测试
fn benchmark_stress_test(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    let mut group = c.benchmark_group("stress_test");

    for task_count in [1000, 5000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("task_count", task_count), task_count, |b, &task_count| {
            b.to_async(&rt).iter(|| async {
                let config = RuntimeConfig {
                    max_concurrent_tasks: 100,
                    ..Default::default()
                };
                let framework = SimpleAsyncRuntimeFramework::new(config);

                let mut tasks: Vec<Box<dyn AsyncTask>> = Vec::new();
                for i in 0..task_count {
                    let task = Box::new(ExampleTask::new(
                        &format!("stress_task_{}", i),
                        TaskPriority::Normal,
                        0
                    ));
                    tasks.push(task);
                }

                let results = framework.execute_batch(tasks).await;
                black_box(results)
            })
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    benchmark_single_task_execution,
    benchmark_batch_task_execution,
    benchmark_task_priority_performance,
    benchmark_async_sync_conversion,
    benchmark_aggregation_composition,
    benchmark_concurrency_safety,
    benchmark_memory_usage,
    benchmark_error_handling,
    benchmark_runtime_type_comparison,
    benchmark_timeout_handling,
    benchmark_monitoring_performance,
    benchmark_health_check_performance,
    benchmark_stress_test
);

criterion_main!(benches);
