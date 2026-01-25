//! 宏系统模块性能基准测试 / Macro System Module Performance Benchmarks

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_macro_expansion(c: &mut Criterion) {
    c.bench_function("macro_expansion", |b| {
        b.iter(|| {
            macro_rules! simple_macro {
                ($x:expr) => {
                    $x + 1
                };
            }
            let result = simple_macro!(black_box(42));
            black_box(result);
        });
    });
}

fn bench_macro_operations(c: &mut Criterion) {
    c.bench_function("macro_operations", |b| {
        b.iter(|| {
            let vec: Vec<i32> = (0..1000).collect();
            let sum: i32 = vec.iter().sum();
            black_box(sum);
        });
    });
}

fn bench_procedural_macro(c: &mut Criterion) {
    c.bench_function("procedural_macro", |b| {
        b.iter(|| {
            let value = black_box(42);
            let result = value * 2;
            black_box(result);
        });
    });
}

fn bench_macro_nesting(c: &mut Criterion) {
    c.bench_function("macro_nesting", |b| {
        b.iter(|| {
            macro_rules! nested_macro {
                ($x:expr) => {
                    $x * 2
                };
            }
            let result = nested_macro!(black_box(21));
            black_box(result);
        });
    });
}

criterion_group!(benches, bench_macro_expansion, bench_macro_operations, bench_procedural_macro, bench_macro_nesting);
criterion_main!(benches);
