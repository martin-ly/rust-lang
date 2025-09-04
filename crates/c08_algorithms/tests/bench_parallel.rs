use c08_algorithms::sorting::*;
use c08_algorithms::searching::*;
use c08_algorithms::graph::*;
use c08_algorithms::string_algorithms::*;

#[test]
fn test_sorting_parallel_and_async() {
    // parallel
    let mut a = (0..50_000).rev().collect::<Vec<_>>();
    sort_parallel(&mut a, SortingAlgo::Quick);
    assert!(a.windows(2).all(|w| w[0] <= w[1]));

    // async
    let rt = tokio::runtime::Runtime::new().unwrap();
    let v = rt.block_on(async {
        sort_async((0..10_000).rev().collect::<Vec<_>>(), SortingAlgo::Merge)
            .await
            .unwrap()
    });
    assert!(v.windows(2).all(|w| w[0] <= w[1]));
}

#[test]
fn test_searching_parallel_and_async() {
    let data: Vec<_> = (0..100_000).collect();
    // parallel search
    let idx = parallel_search(&data, &42_424).unwrap();
    assert_eq!(idx, 42_424);

    // async binary search
    let rt = tokio::runtime::Runtime::new().unwrap();
    let found = rt
        .block_on(async { binary_search_async(data.clone(), 99_999).await.unwrap() })
        .unwrap();
    assert_eq!(found, 99_999);
}

#[test]
fn test_graph_async_bfs_and_dijkstra() {
    // Unweighted graph for BFS
    let mut g: std::collections::HashMap<i32, Vec<i32>> = std::collections::HashMap::new();
    g.insert(1, vec![2, 3]);
    g.insert(2, vec![4]);
    g.insert(3, vec![4]);
    g.insert(4, vec![]);

    let rt = tokio::runtime::Runtime::new().unwrap();
    let path = rt
        .block_on(async { bfs_shortest_path_async(g.clone(), 1, 4).await.unwrap() })
        .unwrap();
    assert!(path == vec![1, 2, 4] || path == vec![1, 3, 4]);

    // Weighted graph for Dijkstra
    let mut wg: std::collections::HashMap<&str, Vec<(&str, f64)>> = std::collections::HashMap::new();
    wg.insert("A", vec![("B", 1.0), ("C", 4.0)]);
    wg.insert("B", vec![("C", 2.0), ("D", 5.0)]);
    wg.insert("C", vec![("D", 1.0)]);
    wg.insert("D", vec![]);

    let (dist, _prev) = rt
        .block_on(async { dijkstra_async(wg, "A").await.unwrap() });
    assert_eq!(dist.get("D").copied().unwrap().round() as i32, 4);
}
// c08 算法并行与内存集成基准（轻量）

use std::time::Instant;

use c08_algorithms::advanced_algorithms::ParallelSort;

#[test]
fn bench_parallel_quicksort_vs_std_sort() {
    let mut data1: Vec<i32> = (0..50_000).rev().collect();
    let mut data2 = data1.clone();

    let t0 = Instant::now();
    data2.sort();
    let std_dur = t0.elapsed();

    let t1 = Instant::now();
    ParallelSort::parallel_quicksort(&mut data1);
    let par_dur = t1.elapsed();

    // 校验正确性
    assert_eq!(data1, data2);

    eprintln!("std::sort: {:?} | parallel_quicksort: {:?}", std_dur, par_dur);
}

#[test]
fn bench_memory_pool_allocate_deallocate() {
    use c08_algorithms::performance_optimization::MemoryPool;

    let mut pool = MemoryPool::new(1024, 10_000);

    let t0 = Instant::now();
    let mut ptrs = Vec::with_capacity(5_000);
    for _ in 0..5_000 {
        ptrs.push(pool.allocate().expect("allocation should succeed"));
    }
    let alloc_dur = t0.elapsed();

    let t1 = Instant::now();
    for p in ptrs {
        pool.deallocate(p);
    }
    let dealloc_dur = t1.elapsed();

    eprintln!("MemoryPool allocate: {:?} | deallocate: {:?}", alloc_dur, dealloc_dur);
}

#[test]
fn test_counting_and_radix_sorts() {
    let v: Vec<u32> = (0..10_000u32).rev().collect();
    let c = counting_sort_sync_u32(&v);
    assert!(c.windows(2).all(|w| w[0] <= w[1]));
    let cp = counting_sort_parallel_u32(&v);
    assert_eq!(c, cp);
    let rt = tokio::runtime::Runtime::new().unwrap();
    let ca = rt.block_on(async { counting_sort_async_u32(v.clone()).await.unwrap() });
    assert_eq!(cp, ca);

    let r = radix_sort_lsd_sync_u32(v.clone());
    assert!(r.windows(2).all(|w| w[0] <= w[1]));
    let ra = rt.block_on(async { radix_sort_lsd_async_u32(v).await.unwrap() });
    assert_eq!(r, ra);
}

#[test]
fn test_manacher_and_floyd() {
    let (s, l) = manacher_longest_palindrome("forgeeksskeegfor");
    assert_eq!(&"forgeeksskeegfor"[s..s + l], "geeksskeeg");

    let rt = tokio::runtime::Runtime::new().unwrap();
    let edges = vec![(0usize,1usize,1.0),(1,2,2.0),(0,2,10.0)];
    let d = rt.block_on(async { floyd_warshall_async(3, edges).await.unwrap() });
    assert!((d[0][2] - 3.0).abs() < 1e-9);
}


