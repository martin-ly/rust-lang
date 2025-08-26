//! c08 算法并行与内存集成基准（轻量）

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


