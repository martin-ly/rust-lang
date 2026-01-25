//! 算法模块性能基准测试 / Algorithms Module Performance Benchmarks

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_vector_operations(c: &mut Criterion) {
    c.bench_function("vector_operations", |b| {
        b.iter(|| {
            let vec: Vec<i32> = (0..1000).collect();
            let sum: i32 = vec.iter().sum();
            black_box(sum);
        });
    });
}

fn bench_sorting_operations(c: &mut Criterion) {
    c.bench_function("sorting_operations", |b| {
        b.iter(|| {
            let mut vec: Vec<i32> = (0..1000).rev().collect();
            vec.sort();
            black_box(vec);
        });
    });
}

fn bench_search_operations(c: &mut Criterion) {
    c.bench_function("search_operations", |b| {
        let vec: Vec<i32> = (0..1000).collect();
        b.iter(|| {
            let result = vec.binary_search(&black_box(500));
            black_box(result);
        });
    });
}

criterion_group!(benches, bench_vector_operations, bench_sorting_operations, bench_search_operations);
criterion_main!(benches);
