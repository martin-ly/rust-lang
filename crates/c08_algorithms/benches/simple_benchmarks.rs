//! 简化的算法性能基准测试
//! 
//! 本文件包含简化的算法性能基准测试，使用实际存在的函数

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use c08_algorithms::algorithms::sorting::sync::{QuickSort, MergeSort};
use c08_algorithms::algorithms::SyncAlgorithm;

/// 排序算法基准测试
fn bench_sorting_algorithms(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorting_algorithms");
    
    // 测试不同大小的数组
    for size in [100, 1000, 10000].iter() {
        let data: Vec<i32> = (0..*size).rev().collect();
        
        group.bench_with_input(BenchmarkId::new("quick_sort", size), size, |b, _| {
            b.iter(|| {
                let test_data = data.clone();
                let sorter = QuickSort;
                sorter.execute(black_box(test_data)).unwrap()
            })
        });
        
        group.bench_with_input(BenchmarkId::new("merge_sort", size), size, |b, _| {
            b.iter(|| {
                let test_data = data.clone();
                let sorter = MergeSort;
                sorter.execute(black_box(test_data)).unwrap()
            })
        });
    }
    
    group.finish();
}

/// 内存分配基准测试
fn bench_memory_allocation(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_allocation");
    
    // 测试不同大小的数据结构
    for size in [1000, 10000, 100000].iter() {
        group.bench_with_input(BenchmarkId::new("vector_allocation", size), size, |b, size| {
            b.iter(|| {
                let mut vec = Vec::with_capacity(*size);
                for i in 0..*size {
                    vec.push(i);
                }
                vec
            })
        });
        
        group.bench_with_input(BenchmarkId::new("vector_with_capacity", size), size, |b, size| {
            b.iter(|| {
                let mut vec = Vec::with_capacity(*size);
                for i in 0..*size {
                    vec.push(i);
                }
                vec
            })
        });
    }
    
    group.finish();
}

/// 数学运算基准测试
fn bench_math_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("math_operations");
    
    let sizes = [1000, 10000, 100000];
    
    for size in sizes.iter() {
        let data: Vec<f64> = (0..*size).map(|i| i as f64).collect();
        
        group.bench_with_input(BenchmarkId::new("sum", size), size, |b, _| {
            b.iter(|| {
                data.iter().sum::<f64>()
            })
        });
        
        group.bench_with_input(BenchmarkId::new("product", size), size, |b, _| {
            b.iter(|| {
                data.iter().product::<f64>()
            })
        });
        
        group.bench_with_input(BenchmarkId::new("mean", size), size, |b, _| {
            b.iter(|| {
                data.iter().sum::<f64>() / *size as f64
            })
        });
    }
    
    group.finish();
}

/// 字符串操作基准测试
fn bench_string_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("string_operations");
    
    let sizes = [100, 1000, 10000];
    
    for size in sizes.iter() {
        let text = "a".repeat(*size);
        
        group.bench_with_input(BenchmarkId::new("string_concat", size), size, |b, _| {
            b.iter(|| {
                let mut result = String::new();
                for i in 0..*size {
                    result.push_str(&format!("{}", i));
                }
                result
            })
        });
        
        group.bench_with_input(BenchmarkId::new("string_find", size), size, |b, _| {
            b.iter(|| {
                text.find("a")
            })
        });
        
        group.bench_with_input(BenchmarkId::new("string_replace", size), size, |b, _| {
            b.iter(|| {
                text.replace("a", "b")
            })
        });
    }
    
    group.finish();
}

/// 并发性能基准测试
fn bench_concurrent_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_operations");
    
    let sizes = [1000, 10000, 100000];
    
    for size in sizes.iter() {
        let data: Vec<i32> = (0..*size).collect();
        
        group.bench_with_input(BenchmarkId::new("parallel_sum", size), size, |b, _| {
            b.iter(|| {
                use rayon::prelude::*;
                data.par_iter().sum::<i32>()
            })
        });
        
        group.bench_with_input(BenchmarkId::new("sequential_sum", size), size, |b, _| {
            b.iter(|| {
                data.iter().sum::<i32>()
            })
        });
        
        group.bench_with_input(BenchmarkId::new("parallel_map", size), size, |b, _| {
            b.iter(|| {
                use rayon::prelude::*;
                data.par_iter().map(|x| x * 2).collect::<Vec<_>>()
            })
        });
        
        group.bench_with_input(BenchmarkId::new("sequential_map", size), size, |b, _| {
            b.iter(|| {
                data.iter().map(|x| x * 2).collect::<Vec<_>>()
            })
        });
    }
    
    group.finish();
}

// 基准测试配置
criterion_group!(
    benches,
    bench_sorting_algorithms,
    bench_memory_allocation,
    bench_math_operations,
    bench_string_operations,
    bench_concurrent_operations
);

criterion_main!(benches);
