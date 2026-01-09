//! Rust 1.90 简化性能基准测试 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新基准测试请参考 `rust_192_benchmarks.rs`
//!
//! 本文件提供了 Rust 1.90 新特性的简化性能基准测试

use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

// 导入我们定义的类型
use c02_type_system::rust_189_simple_demo::simple_demo::*;

// ==================== 常量泛型性能测试 ====================

fn benchmark_const_generics_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("const_generics_creation");

    group.bench_function("array_5", |b| {
        b.iter(|| {
            black_box(ConstGenericArray::new([1, 2, 3, 4, 5]))
        });
    });

    group.bench_function("array_10", |b| {
        b.iter(|| {
            black_box(ConstGenericArray::new([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]))
        });
    });

    group.finish();
}

fn benchmark_const_generics_access(c: &mut Criterion) {
    let mut group = c.benchmark_group("const_generics_access");

    group.bench_function("array_access_5", |b| {
        let array = ConstGenericArray::new([1, 2, 3, 4, 5]);
        b.iter(|| {
            for i in 0..5 {
                black_box(array.get(i));
            }
        });
    });

    group.finish();
}

// ==================== 矩阵性能测试 ====================

fn benchmark_matrix_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("matrix_operations");

    group.bench_function("matrix_creation_3x3", |b| {
        b.iter(|| {
            black_box(Matrix::<i32, 3, 3>::new())
        });
    });

    group.bench_function("matrix_access_3x3", |b| {
        let matrix = Matrix::<i32, 3, 3>::new();
        b.iter(|| {
            for i in 0..3 {
                for j in 0..3 {
                    black_box(matrix.get(i, j));
                }
            }
        });
    });

    group.finish();
}

// ==================== 向量性能测试 ====================

fn benchmark_vector_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_operations");

    group.bench_function("vector_creation_3d", |b| {
        b.iter(|| {
            black_box(Vector::<i32, 3>::new())
        });
    });

    group.bench_function("vector_access_3d", |b| {
        let vector = Vector::<i32, 3>::new();
        b.iter(|| {
            for i in 0..3 {
                black_box(vector.get(i));
            }
        });
    });

    group.finish();
}

// ==================== 智能指针组合性能测试 ====================

fn benchmark_smart_pointer_composition(c: &mut Criterion) {
    let mut group = c.benchmark_group("smart_pointer_composition");

    group.bench_function("creation", |b| {
        b.iter(|| {
            black_box(SmartPointerComposition::new(42))
        });
    });

    group.bench_function("access", |b| {
        let composition = SmartPointerComposition::new(42);
        b.iter(|| {
            black_box(composition.get())
        });
    });

    group.finish();
}

// ==================== 类型别名性能测试 ====================

fn benchmark_type_aliases(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_aliases");

    group.bench_function("number_processor_creation", |b| {
        b.iter(|| {
            black_box(create_number_processor())
        });
    });

    group.bench_function("complex_type_creation", |b| {
        b.iter(|| {
            black_box(create_complex_type())
        });
    });

    group.finish();
}

// ==================== 内存使用性能测试 ====================

fn benchmark_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");

    group.bench_function("const_generic_array_memory", |b| {
        b.iter(|| {
            let array = ConstGenericArray::new([1, 2, 3, 4, 5]);
            black_box(std::mem::size_of_val(&array))
        });
    });

    group.bench_function("matrix_memory", |b| {
        b.iter(|| {
            let matrix = Matrix::<i32, 3, 3>::new();
            black_box(std::mem::size_of_val(&matrix))
        });
    });

    group.finish();
}

// ==================== 基准测试配置 ====================

criterion_group!(
    benches,
    benchmark_const_generics_creation,
    benchmark_const_generics_access,
    benchmark_matrix_operations,
    benchmark_vector_operations,
    benchmark_smart_pointer_composition,
    benchmark_type_aliases,
    benchmark_memory_usage
);

criterion_main!(benches);
