//! Rust 1.92.0 性能基准测试
//!
//! 本文件提供了 Rust 1.92.0 新特性的性能基准测试

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use std::num::NonZeroUsize;

// 导入 Rust 1.92.0 特性
use c02_type_system::rust_192_features::*;

// ==================== 关联项多边界性能测试 ====================

fn benchmark_type_converter(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_converter");

    let converter = StringConverter;
    let input = String::from("benchmark test string");

    group.bench_function("string_converter", |b| {
        b.iter(|| {
            black_box(converter.convert(black_box(input.clone())))
        });
    });

    let generic_converter = GenericTypeConverter::<String, String>::new();

    group.bench_function("generic_converter", |b| {
        b.iter(|| {
            black_box(generic_converter.convert(black_box(input.clone())))
        });
    });

    group.finish();
}

// ==================== 高阶生命周期性能测试 ====================

fn benchmark_higher_ranked_lifetimes(c: &mut Criterion) {
    let mut group = c.benchmark_group("higher_ranked_lifetimes");

    let input = "benchmark string for lifetime processing";

    group.bench_function("convert_with_lifetime", |b| {
        b.iter(|| {
            black_box(convert_with_lifetime(black_box(input), |s| s))
        });
    });

    group.bench_function("process_strings", |b| {
        b.iter(|| {
            black_box(process_strings(black_box(input), |s| s))
        });
    });

    let processor = StringReverser;
    group.bench_function("processor_process", |b| {
        b.iter(|| {
            black_box(processor.process(black_box(input)))
        });
    });

    group.finish();
}

// ==================== MaybeUninit 性能测试 ====================

fn benchmark_maybe_uninit(c: &mut Criterion) {
    let mut group = c.benchmark_group("maybe_uninit");

    group.bench_function("create_manager", |b| {
        b.iter(|| {
            black_box(TypeSafeUninitManager::<i32>::new())
        });
    });

    group.bench_function("initialize_and_get", |b| {
        b.iter(|| {
            let mut manager = TypeSafeUninitManager::<i32>::new();
            manager.initialize(black_box(42));
            let result = manager.get().copied();
            black_box(result)
        });
    });

    group.bench_function("initialize_string", |b| {
        b.iter(|| {
            let mut manager = TypeSafeUninitManager::<String>::new();
            manager.initialize(black_box(String::from("test")));
            let result = manager.get().map(|s| s.clone());
            black_box(result)
        });
    });

    group.finish();
}

// ==================== NonZero::div_ceil 性能测试 ====================

fn benchmark_nonzero_div_ceil(c: &mut Criterion) {
    let mut group = c.benchmark_group("nonzero_div_ceil");

    let alignment = NonZeroUsize::new(8).unwrap();
    let calculator = TypeSizeCalculator::new(alignment);

    for count in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("calculate_aligned_u64", count),
            count,
            |b, &count| {
                b.iter(|| {
                    black_box(calculator.calculate_aligned::<u64>(black_box(count)))
                });
            },
        );
    }

    for size in [100, 1000, 10000, 100000].iter() {
        group.bench_with_input(
            BenchmarkId::new("calculate_blocks", size),
            size,
            |b, &size| {
                b.iter(|| {
                    black_box(calculator.calculate_blocks(
                        black_box(size),
                        NonZeroUsize::new(16).unwrap()
                    ))
                });
            },
        );
    }

    group.finish();
}

// ==================== 迭代器特化性能测试 ====================

fn benchmark_iterator_specialization(c: &mut Criterion) {
    let mut group = c.benchmark_group("iterator_specialization");

    // 小列表
    let small_list1: Vec<i32> = (1..=100).collect();
    let small_list2: Vec<i32> = (1..=100).collect();
    let small_list3: Vec<i32> = (1..=99).chain(std::iter::once(0)).collect();

    group.bench_function("compare_small_equal", |b| {
        b.iter(|| {
            black_box(compare_type_lists(black_box(&small_list1), black_box(&small_list2)))
        });
    });

    group.bench_function("compare_small_different", |b| {
        b.iter(|| {
            black_box(compare_type_lists(black_box(&small_list1), black_box(&small_list3)))
        });
    });

    // 中等列表
    let medium_list1: Vec<i32> = (1..=1000).collect();
    let medium_list2: Vec<i32> = (1..=1000).collect();
    let medium_list3: Vec<i32> = (1..=999).chain(std::iter::once(0)).collect();

    group.bench_function("compare_medium_equal", |b| {
        b.iter(|| {
            black_box(compare_type_lists(black_box(&medium_list1), black_box(&medium_list2)))
        });
    });

    group.bench_function("compare_medium_different", |b| {
        b.iter(|| {
            black_box(compare_type_lists(black_box(&medium_list1), black_box(&medium_list3)))
        });
    });

    // 大列表
    let large_list1: Vec<i32> = (1..=10000).collect();
    let large_list2: Vec<i32> = (1..=10000).collect();
    let large_list3: Vec<i32> = (1..=9999).chain(std::iter::once(0)).collect();

    group.bench_function("compare_large_equal", |b| {
        b.iter(|| {
            black_box(compare_type_lists(black_box(&large_list1), black_box(&large_list2)))
        });
    });

    group.bench_function("compare_large_different", |b| {
        b.iter(|| {
            black_box(compare_type_lists(black_box(&large_list1), black_box(&large_list3)))
        });
    });

    group.finish();
}

// ==================== 类型列表验证器性能测试 ====================

fn benchmark_type_list_validator(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_list_validator");

    let expected: Vec<i32> = (1..=100).collect();
    let validator = TypeListValidator::new(expected.clone());
    let actual_match = expected.clone();
    let actual_mismatch: Vec<i32> = (1..=99).chain(std::iter::once(0)).collect();

    group.bench_function("validate_match", |b| {
        b.iter(|| {
            black_box(validator.validate(black_box(&actual_match)))
        });
    });

    group.bench_function("validate_mismatch", |b| {
        b.iter(|| {
            black_box(validator.validate(black_box(&actual_mismatch)))
        });
    });

    // 更大的列表
    let large_expected: Vec<i32> = (1..=1000).collect();
    let large_validator = TypeListValidator::new(large_expected.clone());
    let large_actual_match = large_expected.clone();
    let large_actual_mismatch: Vec<i32> = (1..=999).chain(std::iter::once(0)).collect();

    group.bench_function("validate_large_match", |b| {
        b.iter(|| {
            black_box(large_validator.validate(black_box(&large_actual_match)))
        });
    });

    group.bench_function("validate_large_mismatch", |b| {
        b.iter(|| {
            black_box(large_validator.validate(black_box(&large_actual_mismatch)))
        });
    });

    group.finish();
}

// ==================== 自动特征性能测试 ====================

fn benchmark_auto_traits(c: &mut Criterion) {
    let mut group = c.benchmark_group("auto_traits");

    group.bench_function("create_auto_trait_example", |b| {
        b.iter(|| {
            black_box(AutoTraitExample::new(black_box(42)))
        });
    });

    let example = AutoTraitExample::new(42);
    group.bench_function("get_from_auto_trait_example", |b| {
        b.iter(|| {
            black_box(example.get())
        });
    });

    let string_example = AutoTraitExample::new(String::from("test"));
    group.bench_function("get_string_from_auto_trait_example", |b| {
        b.iter(|| {
            black_box(string_example.get())
        });
    });

    group.finish();
}

// ==================== 综合性能测试 ====================

fn benchmark_integration(c: &mut Criterion) {
    let mut group = c.benchmark_group("integration");

    // 组合多个特性
    group.bench_function("type_conversion_and_storage", |b| {
        b.iter(|| {
            let mut manager = TypeSafeUninitManager::<String>::new();
            let converter = StringConverter;
            let input = String::from("integration test");
            let converted = converter.convert(black_box(input));
            manager.initialize(converted);
            let result = manager.get().map(|s| s.clone());
            black_box(result)
        });
    });

    // 类型大小计算和验证
    group.bench_function("size_calculation_and_validation", |b| {
        b.iter(|| {
            let calculator = TypeSizeCalculator::new(NonZeroUsize::new(8).unwrap());
            let size = calculator.calculate_aligned::<u64>(black_box(100));
            let validator = TypeListValidator::new(vec![1, 2, 3]);
            let result = validator.validate(black_box(&[1, 2, 3]));
            black_box((size, result))
        });
    });

    group.finish();
}

// ==================== 主函数 ====================

criterion_group!(
    benches,
    benchmark_type_converter,
    benchmark_higher_ranked_lifetimes,
    benchmark_maybe_uninit,
    benchmark_nonzero_div_ceil,
    benchmark_iterator_specialization,
    benchmark_type_list_validator,
    benchmark_auto_traits,
    benchmark_integration
);

criterion_main!(benches);
