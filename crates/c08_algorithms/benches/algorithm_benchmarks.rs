//! 算法性能基准测试
//! 
//! 本文件包含各种算法的性能基准测试，用于评估2025年最新优化后的性能

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use c08_algorithms::algorithms::{
    sorting::QuickSort,
    searching::SearchingAlgorithms,
    string_algorithms::StringAlgorithms,
    graph::GraphAlgorithms,
    dynamic_programming::DynamicProgrammingAlgorithms,
    number_theory::NumberTheoryAlgorithms,
    execution_modes::SyncAlgorithm,
};

/// 排序算法基准测试
fn bench_sorting_algorithms(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorting_algorithms");
    
    // 测试不同大小的数组
    for size in [100, 1000, 10000].iter() {
        let data: Vec<i32> = (0..*size).rev().collect();
        
        group.bench_with_input(BenchmarkId::new("quick_sort", size), size, |b, _| {
            b.iter(|| {
                let test_data = data.clone();
                let quick_sort = QuickSort;
                quick_sort.execute(black_box(test_data)).unwrap()
            })
        });
    }
    
    group.finish();
}

/// 搜索算法基准测试
fn bench_searching_algorithms(c: &mut Criterion) {
    let mut group = c.benchmark_group("searching_algorithms");
    
    // 准备有序数组
    let data: Vec<i32> = (0..10000).collect();
    let targets = [100, 1000, 5000, 9999];
    
    for target in targets.iter() {
        group.bench_with_input(BenchmarkId::new("binary_search", target), target, |b, target| {
            b.iter(|| {
                SearchingAlgorithms::binary_search(black_box(&data), black_box(target))
            })
        });
    }
    
    group.finish();
}

/// 字符串算法基准测试
fn bench_string_algorithms(c: &mut Criterion) {
    let mut group = c.benchmark_group("string_algorithms");
    
    // 准备测试数据
    let text = "a".repeat(10000) + "b" + &"a".repeat(1000);
    let pattern = "ba";
    
    group.bench_function("kmp_search", |b| {
        b.iter(|| {
            StringAlgorithms::kmp_search(black_box(&text), black_box(pattern))
        })
    });
    
    group.bench_function("rabin_karp_search", |b| {
        b.iter(|| {
            StringAlgorithms::rabin_karp_search(black_box(&text), black_box(pattern))
        })
    });
    
    group.finish();
}

/// 图算法基准测试
fn bench_graph_algorithms(c: &mut Criterion) {
    let mut group = c.benchmark_group("graph_algorithms");
    
    // 创建测试图
    let graph = create_test_graph(1000);
    let start = 0;
    
    group.bench_function("bfs", |b| {
        b.iter(|| {
            GraphAlgorithms::bfs(black_box(&graph), black_box(start))
        })
    });
    
    group.bench_function("dfs", |b| {
        b.iter(|| {
            GraphAlgorithms::dfs(black_box(&graph), black_box(start))
        })
    });
    
    group.finish();
}

/// 动态规划算法基准测试
fn bench_dynamic_programming(c: &mut Criterion) {
    let mut group = c.benchmark_group("dynamic_programming");
    
    let text1 = "abcdefghijklmnopqrstuvwxyz";
    let text2 = "acegikmoqsuwy";
    
    group.bench_function("longest_common_subsequence", |b| {
        b.iter(|| {
            DynamicProgrammingAlgorithms::longest_common_subsequence(
                black_box(text1), 
                black_box(text2)
            )
        })
    });
    
    let weights = vec![10, 20, 30, 40, 50];
    let values = vec![60, 100, 120, 160, 200];
    let capacity = 100;
    
    group.bench_function("knapsack_01", |b| {
        b.iter(|| {
            DynamicProgrammingAlgorithms::knapsack_01(
                black_box(&weights), 
                black_box(&values), 
                black_box(capacity)
            )
        })
    });
    
    group.finish();
}

/// 数学算法基准测试
fn bench_math_algorithms(c: &mut Criterion) {
    let mut group = c.benchmark_group("math_algorithms");
    
    let test_cases = [(100u64, 25u64), (1000u64, 250u64), (10000u64, 2500u64), (100000u64, 25000u64)];
    
    for (a, b) in test_cases.iter() {
        group.bench_with_input(BenchmarkId::new("gcd", format!("{}_{}", a, b)), &(a, b), |bench, (a, b)| {
            bench.iter(|| {
                NumberTheoryAlgorithms::gcd(black_box(**a), black_box(**b))
            })
        });
    }
    
    group.finish();
}

/// 内存使用基准测试
fn bench_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");
    
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
    }
    
    group.finish();
}

/// 并发性能基准测试
fn bench_concurrent_algorithms(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_algorithms");
    
    let data: Vec<i32> = (0..10000).collect();
    
    group.bench_function("parallel_sum", |b| {
        b.iter(|| {
            use rayon::prelude::*;
            data.par_iter().sum::<i32>()
        })
    });
    
    group.bench_function("sequential_sum", |b| {
        b.iter(|| {
            data.iter().sum::<i32>()
        })
    });
    
    group.finish();
}

/// 创建测试图
fn create_test_graph(n: usize) -> c08_algorithms::algorithms::graph::Graph {
    let mut edges = Vec::new();
    
    for i in 0..n {
        if i > 0 {
            edges.push((i, i - 1, 1.0));
        }
        if i < n - 1 {
            edges.push((i, i + 1, 1.0));
        }
        if i + 10 < n {
            edges.push((i, i + 10, 2.0));
        }
    }
    
    c08_algorithms::algorithms::graph::Graph {
        vertices: n,
        edges,
    }
}

// 基准测试配置
criterion_group!(
    benches,
    bench_sorting_algorithms,
    bench_searching_algorithms,
    bench_string_algorithms,
    bench_graph_algorithms,
    bench_dynamic_programming,
    bench_math_algorithms,
    bench_memory_usage,
    bench_concurrent_algorithms
);

criterion_main!(benches);