use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use c08_algorithms::backtracking::*;
use c08_algorithms::divide_and_conquer::*;
use c08_algorithms::dynamic_programming::*;
use c08_algorithms::graph::*;
use c08_algorithms::greedy::*;
use c08_algorithms::searching::*;
use c08_algorithms::sorting::*;
use c08_algorithms::string_algorithms::*;

fn bench_sorting(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorting_sync_vs_parallel");
    for &n in &[10_000usize, 50_000] {
        group.bench_with_input(BenchmarkId::new("sync_quick", n), &n, |b, &n| {
            b.iter(|| {
                let mut v: Vec<i32> = (0..n as i32).rev().collect();
                sort_sync(&mut v, SortingAlgo::Quick);
                black_box(v)
            })
        });
        group.bench_with_input(BenchmarkId::new("parallel", n), &n, |b, &n| {
            b.iter(|| {
                let mut v: Vec<i32> = (0..n as i32).rev().collect();
                sort_parallel(&mut v, SortingAlgo::Quick);
                black_box(v)
            })
        });
        group.bench_with_input(BenchmarkId::new("async_merge", n), &n, |b, &n| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            b.iter(|| {
                let v: Vec<i32> = (0..n as i32).rev().collect();
                rt.block_on(async { black_box(sort_async(v, SortingAlgo::Merge).await.unwrap()) })
            })
        });
    }
    group.finish();
}

fn bench_searching(c: &mut Criterion) {
    let mut group = c.benchmark_group("searching_sync_vs_parallel");
    for &n in &[100_000usize, 500_000] {
        let data: Vec<i32> = (0..n as i32).collect();
        group.bench_with_input(BenchmarkId::new("binary_sync", n), &n, |b, &n| {
            b.iter(|| black_box(binary_search_sync(&data, &(n as i32 - 1)).unwrap()))
        });
        group.bench_with_input(BenchmarkId::new("parallel_linear", n), &n, |b, _| {
            b.iter(|| black_box(parallel_search(&data, &42_i32)))
        });
        group.bench_with_input(BenchmarkId::new("binary_async", n), &n, |b, &n| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            b.iter(|| {
                rt.block_on(async {
                    black_box(
                        binary_search_async(data.clone(), n as i32 - 1)
                            .await
                            .unwrap(),
                    )
                })
            })
        });
    }
    group.finish();
}

fn bench_graph(c: &mut Criterion) {
    let mut group = c.benchmark_group("graph_bfs_dijkstra");

    // small DAG for BFS
    let mut g: std::collections::HashMap<i32, Vec<i32>> = std::collections::HashMap::new();
    for i in 0..5000 {
        g.insert(i, vec![i + 1]);
    }
    g.insert(5000, vec![]);

    group.bench_function("bfs_sync", |b| {
        b.iter(|| black_box(bfs_shortest_path_sync(&g, &0, &5000)))
    });
    group.bench_function("bfs_parallel", |b| {
        b.iter(|| black_box(bfs_shortest_path_parallel(&g, &0, &5000)))
    });
    group.bench_function("bfs_async", |b| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        b.iter(|| {
            rt.block_on(async {
                black_box(bfs_shortest_path_async(g.clone(), 0, 5000).await.unwrap())
            })
        })
    });

    // weighted for Dijkstra
    let mut wg: std::collections::HashMap<i32, Vec<(i32, f64)>> = std::collections::HashMap::new();
    for i in 0..5000 {
        wg.insert(i, vec![(i + 1, 1.0)]);
    }
    wg.insert(5000, vec![]);
    group.bench_function("dijkstra_async", |b| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        b.iter(|| rt.block_on(async { black_box(dijkstra_async(wg.clone(), 0).await.unwrap()) }))
    });

    group.finish();
}

fn bench_dp_and_dac(c: &mut Criterion) {
    let mut group = c.benchmark_group("dp_dac");

    // DP LCS
    let a = vec![b'A'; 2000];
    let b = vec![b'A'; 2000];
    group.bench_function("lcs_sync", |bch| bch.iter(|| black_box(lcs_sync(&a, &b))));
    group.bench_function("lcs_async", |bch| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        bch.iter(|| {
            rt.block_on(async { black_box(lcs_async(a.clone(), b.clone()).await.unwrap()) })
        })
    });

    // DAC Max subarray
    let nums: Vec<i64> = (0..200_000)
        .map(|i| if i % 10 == 0 { -5 } else { 3 })
        .collect();
    group.bench_function("max_subarray_sync", |bch| {
        bch.iter(|| black_box(max_subarray_sum_sync(&nums)))
    });
    group.bench_function("max_subarray_parallel", |bch| {
        bch.iter(|| black_box(max_subarray_sum_parallel(&nums)))
    });

    // DAC Closest pair
    let pts: Vec<Point> = (0..50_000)
        .map(|i| Point {
            x: (i as f64) * 0.001,
            y: ((i * 97 % 1111) as f64) * 0.002,
        })
        .collect();
    group.bench_function("closest_pair_sync", |bch| {
        bch.iter(|| black_box(closest_pair_sync(pts.clone())))
    });
    group.bench_function("closest_pair_parallel", |bch| {
        bch.iter(|| black_box(closest_pair_parallel(pts.clone())))
    });
    group.bench_function("closest_pair_async", |bch| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        bch.iter(|| {
            rt.block_on(async { black_box(closest_pair_async(pts.clone()).await.unwrap()) })
        })
    });

    // DP 0-1 Knapsack
    let weights: Vec<usize> = (0..2000).map(|i| 1 + (i as usize % 10)).collect();
    let values: Vec<i64> = (0..2000).map(|i| i as i64 * 37_i64 % 101_i64).collect();
    let cap: usize = 1000;
    group.bench_function("knapsack_sync", |bch| {
        bch.iter(|| black_box(knapsack_01_sync(&weights, &values, cap)))
    });
    group.bench_function("knapsack_parallel", |bch| {
        bch.iter(|| black_box(knapsack_01_parallel(&weights, &values, cap)))
    });
    group.bench_function("knapsack_async", |bch| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        bch.iter(|| {
            rt.block_on(async {
                black_box(
                    knapsack_01_async(weights.clone(), values.clone(), cap)
                        .await
                        .unwrap(),
                )
            })
        })
    });

    group.finish();
}

fn bench_greedy(c: &mut Criterion) {
    let mut group = c.benchmark_group("greedy");
    // interval scheduling
    let ivs: Vec<Interval> = (0..50_000)
        .map(|i| Interval {
            start: i as i64,
            end: i as i64 + 10,
        })
        .collect();
    group.bench_function("interval_sync", |b| {
        b.iter(|| black_box(interval_scheduling_sync(ivs.clone())))
    });
    group.bench_function("interval_parallel", |b| {
        b.iter(|| black_box(interval_scheduling_parallel(ivs.clone())))
    });

    // coin change
    let coins = vec![1, 2, 5, 10, 20, 50];
    group.bench_function("coin_parallel", |b| {
        b.iter(|| black_box(coin_change_greedy_parallel(coins.clone(), 999)))
    });
    group.finish();
}

fn bench_string_algorithms(c: &mut Criterion) {
    let mut group = c.benchmark_group("strings");
    for &n in &[10_000usize, 100_000] {
        let text: String = (0..n)
            .map(|i| char::from(((i * 131) % 26) as u8 + b'a'))
            .collect();
        let pattern = "abcab".to_string();
        group.bench_with_input(BenchmarkId::new("kmp", n), &n, |b, _| {
            b.iter(|| black_box(kmp_search(&text, &pattern)))
        });
        group.bench_with_input(BenchmarkId::new("rk", n), &n, |b, _| {
            b.iter(|| black_box(rabin_karp_search(&text, &pattern)))
        });
        group.bench_with_input(BenchmarkId::new("kmp_async", n), &n, |b, _| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            b.iter(|| {
                rt.block_on(async {
                    black_box(
                        kmp_search_async(text.clone(), pattern.clone())
                            .await
                            .unwrap(),
                    )
                })
            })
        });
        group.bench_with_input(BenchmarkId::new("rk_async", n), &n, |b, _| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            b.iter(|| {
                rt.block_on(async {
                    black_box(
                        rabin_karp_search_async(text.clone(), pattern.clone())
                            .await
                            .unwrap(),
                    )
                })
            })
        });
    }
    // AC 多模式匹配
    for &n in &[10_000usize, 100_000] {
        let text: String = (0..n)
            .map(|i| char::from(((i * 97) % 26) as u8 + b'a'))
            .collect();
        let patterns: Vec<String> = vec!["he".into(), "she".into(), "hers".into(), "his".into()];
        group.bench_with_input(BenchmarkId::new("ac_async", n), &n, |b, _| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            b.iter(|| {
                rt.block_on(async {
                    black_box(
                        ac_search_async(text.clone(), patterns.clone())
                            .await
                            .unwrap(),
                    )
                })
            })
        });
    }
    group.finish();
}

fn bench_backtracking(c: &mut Criterion) {
    let mut group = c.benchmark_group("backtracking");

    // n-queens count
    for &n in &[10usize, 11] {
        group.bench_with_input(BenchmarkId::new("nqueens_parallel", n), &n, |b, &n| {
            b.iter(|| black_box(nqueens_count_parallel(n)))
        });
        group.bench_with_input(BenchmarkId::new("nqueens_async", n), &n, |b, &n| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            b.iter(|| {
                rt.block_on(async { black_box(nqueens_solutions_async(n).await.unwrap().len()) })
            })
        });
    }

    // permutations
    for &n in &[8usize, 9] {
        let data: Vec<usize> = (0..n).collect();
        group.bench_with_input(BenchmarkId::new("perm_parallel", n), &n, |b, _| {
            b.iter(|| black_box(permutations_parallel(data.clone())))
        });
    }

    // subsets
    for &n in &[16usize, 18] {
        let data: Vec<usize> = (0..n).collect();
        group.bench_with_input(BenchmarkId::new("subsets_parallel", n), &n, |b, _| {
            b.iter(|| black_box(subsets_parallel(&data)))
        });
    }

    group.finish();
}

criterion_group!(
    name = benches;
    config = Criterion::default();
    targets = bench_sorting, bench_searching, bench_graph, bench_dp_and_dac, bench_greedy, bench_string_algorithms, bench_backtracking
);
criterion_main!(benches);
