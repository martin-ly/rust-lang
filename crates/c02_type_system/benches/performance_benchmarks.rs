//! 类型系统模块性能基准测试 / Type System Module Performance Benchmarks

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_type_conversion(c: &mut Criterion) {
    c.bench_function("type_conversion", |b| {
        b.iter(|| {
            let value: i32 = 42;
            let converted: u32 = black_box(value) as u32;
            black_box(converted);
        });
    });
}

fn bench_type_inference(c: &mut Criterion) {
    c.bench_function("type_inference", |b| {
        b.iter(|| {
            let vec: Vec<i32> = (0..1000).collect();
            let sum: i32 = vec.iter().sum();
            black_box(sum);
        });
    });
}

fn bench_generic_operations(c: &mut Criterion) {
    c.bench_function("generic_operations", |b| {
        b.iter(|| {
            fn identity<T: Clone>(x: T) -> T {
                x.clone()
            }
            let result = identity(black_box(42));
            black_box(result);
        });
    });
}

fn bench_trait_operations(c: &mut Criterion) {
    c.bench_function("trait_operations", |b| {
        b.iter(|| {
            trait Display {
                fn display(&self) -> String;
            }
            
            impl Display for i32 {
                fn display(&self) -> String {
                    format!("{}", self)
                }
            }
            
            let value: i32 = 42;
            let result = value.display();
            black_box(result);
        });
    });
}

criterion_group!(benches, bench_type_conversion, bench_type_inference, bench_generic_operations, bench_trait_operations);
criterion_main!(benches);
