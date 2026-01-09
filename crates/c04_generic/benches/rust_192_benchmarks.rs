//! Rust 1.92.0 泛型特性性能基准测试套件
//!
//! 本模块提供 Rust 1.92.0 新特性的性能基准测试，包括：
//! - 关联项的多个边界性能
//! - 高阶生命周期处理性能
//! - 泛型内存计算性能
//! - 迭代器方法特化性能
//!
//! 运行方式:
//! ```bash
//! cargo bench --bench rust_192_benchmarks
//! ```

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use std::hint::black_box;
use std::num::NonZeroUsize;

use c04_generic::rust_192_features::{
    GenericVector, GenericContainer, GenericTransformer, GenericLifetimeProcessor,
    StringToNumberTransformer, IdentityProcessor, compose_generic_processors,
    calculate_generic_aligned_size, GenericMemoryAllocator,
    compare_generic_collections, GenericCollectionValidator,
};

/// 基准测试关联项的多个边界性能
fn bench_multiple_bounds_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("multiple_bounds_performance");
    group.throughput(Throughput::Elements(1));

    // 测试不同大小的容器操作
    for size in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("container_operations", size),
            size,
            |b, &size| {
                b.iter(|| {
                    let mut container: GenericVector<String> = GenericVector::new();
                    for i in 0..size {
                        container.set(i, format!("item_{}", i));
                    }

                    // 读取操作
                    for i in 0..size {
                        black_box(container.get(i));
                    }

                    black_box(&container);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试泛型转换器性能
fn bench_generic_transformer_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("generic_transformer_performance");
    group.throughput(Throughput::Elements(1));

    let transformer = StringToNumberTransformer;

    // 测试成功转换
    group.bench_function("transform_success", |b| {
        b.iter(|| {
            let result = transformer.transform(String::from("42"));
            let _ = black_box(result);
        });
    });

    // 测试失败转换
    group.bench_function("transform_error", |b| {
        b.iter(|| {
            let result = transformer.transform(String::from("invalid"));
            let _ = black_box(result);
        });
    });

    group.finish();
}

/// 基准测试高阶生命周期处理性能
fn bench_higher_ranked_lifetime_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("higher_ranked_lifetime_performance");
    group.throughput(Throughput::Elements(1));

    let processor = IdentityProcessor::<String>::new();

    // 测试单个处理器
    group.bench_function("single_processor", |b| {
        let input = String::from("test");
        b.iter(|| {
            let result = GenericLifetimeProcessor::<String>::process(&processor, &input);
            black_box(result);
        });
    });

    // 测试组合处理器
    group.bench_function("compose_processors", |b| {
        let processor1 = IdentityProcessor::<String>::new();
        let processor2 = IdentityProcessor::<String>::new();
        let input = String::from("test");
        b.iter(|| {
            let result = compose_generic_processors(
                &input, &processor1, &processor2
            );
            black_box(result);
        });
    });

    group.finish();
}

/// 基准测试泛型内存计算性能
fn bench_generic_memory_calculation_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("generic_memory_calculation_performance");

    let alignment = NonZeroUsize::new(8).unwrap();
    let allocator = GenericMemoryAllocator::new(NonZeroUsize::new(16).unwrap());

    // 测试不同大小的对齐计算
    let sizes: &[(usize, &str)] = &[
        (10, "small"),
        (100, "medium"),
        (1000, "large"),
        (10000, "xlarge"),
    ];

    for (count, label) in sizes {
        let count_val = *count;
        group.bench_with_input(
            BenchmarkId::new("calculate_aligned_size_u64", *label),
            &count_val,
            |b, count| {
                b.iter(|| {
                    let result = calculate_generic_aligned_size::<u64>(*count, alignment);
                    black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("calculate_blocks_u32", *label),
            &count_val,
            |b, count| {
                b.iter(|| {
                    let result = allocator.calculate_blocks::<u32>(*count);
                    black_box(result);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试迭代器方法特化性能
fn bench_iterator_specialization_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("iterator_specialization_performance");
    group.throughput(Throughput::Elements(1));

    // 测试不同大小的集合比较
    for size in [10, 100, 1000, 10000].iter() {
        let col1: Vec<i32> = (0..*size).collect();
        let col2: Vec<i32> = (0..*size).collect();
        let col3: Vec<i32> = (0..*size).map(|x| if x == *size - 1 { x + 1 } else { x }).collect();

        group.bench_with_input(
            BenchmarkId::new("compare_equal", size),
            size,
            |b, _| {
                b.iter(|| {
                    let result = compare_generic_collections(&col1, &col2);
                    black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("compare_different", size),
            size,
            |b, _| {
                b.iter(|| {
                    let result = compare_generic_collections(&col1, &col3);
                    black_box(result);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试泛型集合验证器性能
fn bench_collection_validator_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("collection_validator_performance");
    group.throughput(Throughput::Elements(1));

    // 测试不同大小的验证
    for size in [10, 100, 1000, 10000].iter() {
        let expected: Vec<i32> = (0..*size).collect();
        let validator = GenericCollectionValidator::new(expected.clone());
        let actual_match = expected.clone();
        let actual_mismatch: Vec<i32> = (0..*size).map(|x| if x == *size - 1 { x + 1 } else { x }).collect();

        group.bench_with_input(
            BenchmarkId::new("validate_match", size),
            size,
            |b, _| {
                b.iter(|| {
                    let result = validator.validate(&actual_match);
                    black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("validate_mismatch", size),
            size,
            |b, _| {
                b.iter(|| {
                    let result = validator.validate(&actual_mismatch);
                    black_box(result);
                });
            },
        );
    }

    group.finish();
}

/// 综合性能基准测试：完整的泛型处理流程
fn bench_complete_workflow_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("complete_workflow_performance");
    group.throughput(Throughput::Elements(1));

    // 测试完整工作流程
    for workflow_size in [100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("complete_workflow", workflow_size),
            workflow_size,
            |b, &size| {
                b.iter(|| {
                    // 1. 创建容器
                    let mut container: GenericVector<String> = GenericVector::new();
                    for i in 0..size {
                        container.set(i, format!("item_{}", i));
                    }

                    // 2. 转换数据
                    let transformer = StringToNumberTransformer;
                    let _number = transformer.transform(String::from("42"));

                    // 3. 处理生命周期
                    let processor = IdentityProcessor::<String>::new();
                    if let Some(item) = container.get(0) {
                        let _processed = GenericLifetimeProcessor::<String>::process(&processor, item);
                    }

                    // 4. 计算内存
                    let alignment = NonZeroUsize::new(8).unwrap();
                    let _size = calculate_generic_aligned_size::<String>(container.size(), alignment);

                    // 5. 验证集合
                    let expected: Vec<i32> = (0..10).collect();
                    let validator = GenericCollectionValidator::new(expected.clone());
                    let _is_valid = validator.validate(&expected);

                    black_box(&container);
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_multiple_bounds_performance,
    bench_generic_transformer_performance,
    bench_higher_ranked_lifetime_performance,
    bench_generic_memory_calculation_performance,
    bench_iterator_specialization_performance,
    bench_collection_validator_performance,
    bench_complete_workflow_performance
);

criterion_main!(benches);
