//! WebAssembly模块性能基准测试 / WebAssembly Module Performance Benchmarks

use criterion::{criterion_group, criterion_main, Criterion};

fn bench_wasm_operations(c: &mut Criterion) {
    c.bench_function("wasm_operations", |b| {
        b.iter(|| {
            let value = std::hint::black_box(42);
            let result = value + 1;
            std::hint::black_box(result);
        });
    });
}

fn bench_wasm_module_operations(c: &mut Criterion) {
    c.bench_function("wasm_module_operations", |b| {
        b.iter(|| {
            let vec: Vec<i32> = (0..1000).collect();
            let sum: i32 = vec.iter().sum();
            std::hint::black_box(sum);
        });
    });
}

fn bench_wasm_function_operations(c: &mut Criterion) {
    c.bench_function("wasm_function_operations", |b| {
        b.iter(|| {
            let mut sum = 0;
            for i in 0..1000 {
                sum += std::hint::black_box(i);
            }
            std::hint::black_box(sum);
        });
    });
}

fn bench_wasm_memory_operations(c: &mut Criterion) {
    c.bench_function("wasm_memory_operations", |b| {
        b.iter(|| {
            let vec: Vec<u8> = vec![0; 1024];
            let len = vec.len();
            std::hint::black_box(len);
        });
    });
}

criterion_group!(benches, bench_wasm_operations, bench_wasm_module_operations, bench_wasm_function_operations, bench_wasm_memory_operations);
criterion_main!(benches);
