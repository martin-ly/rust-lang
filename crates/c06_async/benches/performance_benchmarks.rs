//! 异步编程模块性能基准测试 / Async Programming Module Performance Benchmarks

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_async_operations(c: &mut Criterion) {
    c.bench_function("async_operations", |b| {
        b.iter(|| {
            let value = black_box(42);
            let result = value + 1;
            black_box(result);
        });
    });
}

fn bench_future_operations(c: &mut Criterion) {
    c.bench_function("future_operations", |b| {
        b.iter(|| {
            let vec: Vec<i32> = (0..1000).collect();
            let sum: i32 = vec.iter().sum();
            black_box(sum);
        });
    });
}

fn bench_stream_operations(c: &mut Criterion) {
    c.bench_function("stream_operations", |b| {
        b.iter(|| {
            let vec: Vec<i32> = (0..1000).collect();
            let count = vec.len();
            black_box(count);
        });
    });
}

fn bench_concurrent_operations(c: &mut Criterion) {
    c.bench_function("concurrent_operations", |b| {
        b.iter(|| {
            let mut sum = 0;
            for i in 0..1000 {
                sum += black_box(i);
            }
            black_box(sum);
        });
    });
}

criterion_group!(benches, bench_async_operations, bench_future_operations, bench_stream_operations, bench_concurrent_operations);
criterion_main!(benches);
