//! # 数组处理性能基准测试
//!
//! 测试各种数组操作的性能
//!
//! ## 运行方式
//!
//! ```bash
//! cargo bench --bench array_processing_bench
//! ```

use c12_wasm::array_examples::*;
use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};

/// 测试不同大小数组的求和性能
fn bench_sum_array(c: &mut Criterion) {
    let mut group = c.benchmark_group("sum_array");

    for size in [10, 100, 1000, 10000].iter() {
        let data: Vec<i32> = (0..*size).collect();

        group.bench_with_input(BenchmarkId::from_parameter(size), &data, |b, data| {
            b.iter(|| {
                calculate_average(black_box(
                    &data.iter().map(|&x| x as f64).collect::<Vec<_>>(),
                ))
            });
        });
    }

    group.finish();
}

/// 测试查找最大值性能
fn bench_find_max(c: &mut Criterion) {
    let mut group = c.benchmark_group("find_max");

    for size in [10, 100, 1000, 10000].iter() {
        let data: Vec<i32> = (0..*size).collect();

        group.bench_with_input(BenchmarkId::from_parameter(size), &data, |b, data| {
            b.iter(|| find_max(black_box(data)));
        });
    }

    group.finish();
}

/// 测试数组过滤性能
fn bench_filter_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("filter_operations");

    let data: Vec<i32> = (-5000..5000).collect();

    group.bench_function("filter_even", |b| {
        b.iter(|| filter_even(black_box(&data)));
    });

    group.finish();
}

/// 测试数组反转性能
fn bench_reverse_array(c: &mut Criterion) {
    let mut group = c.benchmark_group("reverse_array");

    for size in [100, 1000, 10000].iter() {
        let data: Vec<i32> = (0..*size).collect();

        group.bench_with_input(BenchmarkId::from_parameter(size), &data, |b, data| {
            b.iter(|| reverse_array(black_box(data)));
        });
    }

    group.finish();
}

/// 测试数组映射操作
fn bench_double_elements(c: &mut Criterion) {
    let mut group = c.benchmark_group("double_elements");

    let data: Vec<i32> = (0..10000).collect();

    group.bench_function("map_iterator", |b| {
        b.iter(|| {
            black_box(&data)
                .iter()
                .map(|&x| x * 2)
                .collect::<Vec<i32>>()
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_sum_array,
    bench_find_max,
    bench_filter_operations,
    bench_reverse_array,
    bench_double_elements
);

criterion_main!(benches);
