//! 异步生态系统性能基准测试
//!
//! 本模块提供了对各个异步运行时的性能基准测试，
//! 包括内存使用、启动时间、并发性能等指标。

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use c06_async::{
    async_runtime_examples::{
        StdAsyncExamples, TokioExamples, AsyncStdExamples, SmolExamples,
        RuntimeCompositionExamples
    },
    async_integration_framework::{
        AsyncSyncConversionFramework, AggregationCompositionFramework, DataProcessingComponent
    }
};
use std::time::Duration;
use tokio::runtime::Runtime;

/// 基准测试：异步任务执行性能
fn bench_async_task_execution(c: &mut Criterion) {
    let mut group = c.benchmark_group("async_task_execution");

    // 测试不同运行时的任务执行性能
    group.bench_function("tokio_concurrent_processing", |b| {
        let rt = Runtime::new().unwrap();
        b.to_async(rt).iter(|| async {
            let tokio_examples = TokioExamples::new(10);
            let tasks = (0..100).map(|i| format!("task_{}", i)).collect();
            tokio_examples.high_performance_concurrent_processing(tasks).await
        });
    });

    group.bench_function("async_std_task_management", |b| {
        let rt = Runtime::new().unwrap();
        b.to_async(rt).iter(|| async {
            let async_std_examples = AsyncStdExamples::new();
            async_std_examples.task_management_example().await
        });
    });

    group.bench_function("smol_lightweight_scheduling", |b| {
        let rt = Runtime::new().unwrap();
        b.to_async(rt).iter(|| async {
            let smol_examples = SmolExamples::new();
            smol_examples.lightweight_task_scheduling().await
        });
    });

    group.finish();
}

/// 基准测试：流处理性能
fn bench_stream_processing(c: &mut Criterion) {
    let mut group = c.benchmark_group("stream_processing");

    group.bench_function("tokio_stream_processing", |b| {
        let rt = Runtime::new().unwrap();
        b.to_async(rt).iter(|| async {
            let tokio_examples = TokioExamples::new(5);
            tokio_examples.stream_processing_example().await
        });
    });

    group.finish();
}

/// 基准测试：异步同步转换性能
fn bench_async_sync_conversion(c: &mut Criterion) {
    let mut group = c.benchmark_group("async_sync_conversion");

    group.bench_function("sync_to_async_conversion", |b| {
        let rt = Runtime::new().unwrap();
        b.to_async(rt).iter(|| async {
            let conversion_framework = AsyncSyncConversionFramework::new(4);
            conversion_framework.sync_to_async_conversion(|| {
                std::thread::sleep(Duration::from_micros(1));
                Ok("sync_result".to_string())
            }).await
        });
    });

    group.finish();
}

/// 基准测试：聚合组合模式性能
fn bench_aggregation_composition(c: &mut Criterion) {
    let mut group = c.benchmark_group("aggregation_composition");

    group.bench_function("sequential_aggregation", |b| {
        let rt = Runtime::new().unwrap();
        b.to_async(rt).iter(|| async {
            let composition_framework = AggregationCompositionFramework::new();

            // 注册组件
            let component1 = Box::new(DataProcessingComponent::new("processor1", 1));
            let component2 = Box::new(DataProcessingComponent::new("processor2", 1));

            composition_framework.register_component(component1).await.unwrap();
            composition_framework.register_component(component2).await.unwrap();

            composition_framework.sequential_aggregation(
                vec!["processor1".to_string(), "processor2".to_string()],
                "test_input"
            ).await
        });
    });

    group.bench_function("parallel_aggregation", |b| {
        let rt = Runtime::new().unwrap();
        b.to_async(rt).iter(|| async {
            let composition_framework = AggregationCompositionFramework::new();

            // 注册组件
            let component1 = Box::new(DataProcessingComponent::new("processor1", 1));
            let component2 = Box::new(DataProcessingComponent::new("processor2", 1));

            composition_framework.register_component(component1).await.unwrap();
            composition_framework.register_component(component2).await.unwrap();

            composition_framework.parallel_aggregation(
                vec!["processor1".to_string(), "processor2".to_string()],
                "test_input"
            ).await
        });
    });

    group.finish();
}

/// 基准测试：运行时组合模式性能
fn bench_runtime_composition(c: &mut Criterion) {
    let mut group = c.benchmark_group("runtime_composition");

    group.bench_function("runtime_selector_pattern", |b| {
        let rt = Runtime::new().unwrap();
        b.to_async(rt).iter(|| async {
            let composition_examples = RuntimeCompositionExamples::new();
            composition_examples.runtime_selector_pattern("high_performance").await
        });
    });

    group.bench_function("runtime_adapter_pattern", |b| {
        let rt = Runtime::new().unwrap();
        b.to_async(rt).iter(|| async {
            let composition_examples = RuntimeCompositionExamples::new();
            composition_examples.runtime_adapter_pattern().await
        });
    });

    group.bench_function("runtime_bridge_pattern", |b| {
        let rt = Runtime::new().unwrap();
        b.to_async(rt).iter(|| async {
            let composition_examples = RuntimeCompositionExamples::new();
            composition_examples.runtime_bridge_pattern().await
        });
    });

    group.finish();
}

/// 基准测试：内存使用效率
fn bench_memory_efficiency(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_efficiency");

    // 测试不同运行时的内存使用
    group.bench_function("tokio_memory_usage", |b| {
        b.iter(|| {
            let _tokio_examples = TokioExamples::new(100);
            black_box(())
        });
    });

    group.bench_function("async_std_memory_usage", |b| {
        b.iter(|| {
            let _async_std_examples = AsyncStdExamples::new();
            black_box(())
        });
    });

    group.bench_function("smol_memory_usage", |b| {
        b.iter(|| {
            let _smol_examples = SmolExamples::new();
            black_box(())
        });
    });

    group.finish();
}

/// 基准测试：启动时间
fn bench_startup_time(c: &mut Criterion) {
    let mut group = c.benchmark_group("startup_time");

    group.bench_function("tokio_runtime_startup", |b| {
        b.iter(|| {
            let _rt = Runtime::new().unwrap();
            black_box(())
        });
    });

    group.bench_function("async_std_startup", |b| {
        b.iter(|| {
            let _async_std_examples = AsyncStdExamples::new();
            black_box(())
        });
    });

    group.bench_function("smol_startup", |b| {
        b.iter(|| {
            let _smol_examples = SmolExamples::new();
            black_box(())
        });
    });

    group.finish();
}

/// 基准测试：并发性能
fn bench_concurrency_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrency_performance");

    // 测试不同并发级别的性能
    for concurrency in [1, 10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("tokio_concurrent_tasks", concurrency),
            concurrency,
            |b, &concurrency| {
                let rt = Runtime::new().unwrap();
                b.to_async(rt).iter(|| async {
                    let tokio_examples = TokioExamples::new(concurrency);
                    let tasks = (0..concurrency).map(|i| format!("task_{}", i)).collect();
                    tokio_examples.high_performance_concurrent_processing(tasks).await
                });
            },
        );
    }

    group.finish();
}

/// 基准测试：错误处理性能
fn bench_error_handling_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_handling_performance");

    group.bench_function("std_async_error_handling", |b| {
        let rt = Runtime::new().unwrap();
        b.to_async(rt).iter(|| async {
            let std_examples = StdAsyncExamples::new();
            std_examples.async_error_handling(false).await
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_async_task_execution,
    bench_stream_processing,
    bench_async_sync_conversion,
    bench_aggregation_composition,
    bench_runtime_composition,
    bench_memory_efficiency,
    bench_startup_time,
    bench_concurrency_performance,
    bench_error_handling_performance
);

criterion_main!(benches);
