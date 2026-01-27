//! 泛型模块性能基准测试 / Generics Module Performance Benchmarks

use criterion::{criterion_group, criterion_main, Criterion};

fn bench_generic_operations(c: &mut Criterion) {
    c.bench_function("generic_operations", |b| {
        b.iter(|| {
            fn identity<T: Clone>(x: T) -> T {
                x.clone()
            }
            let result = identity(std::hint::black_box(42));
            std::hint::black_box(result);
        });
    });
}

fn bench_type_inference(c: &mut Criterion) {
    c.bench_function("type_inference", |b| {
        b.iter(|| {
            let vec: Vec<i32> = (0..1000).collect();
            let sum: i32 = vec.iter().sum();
            std::hint::black_box(sum);
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
            std::hint::black_box(result);
        });
    });
}

criterion_group!(benches, bench_generic_operations, bench_type_inference, bench_trait_operations);
criterion_main!(benches);
