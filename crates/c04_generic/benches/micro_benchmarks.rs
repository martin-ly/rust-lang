//! 微基准测试：迭代器管道与锁策略对比
//! 
//! 本文件提供可运行的基准测试，对比不同实现的性能特征。

use criterion::{black_box, criterion_group, criterion_main, Criterion};

// 导入我们的示例代码
use c04_generic::rust_190_features::*;

fn bench_iterator_pipelines(c: &mut Criterion) {
    let data = (1..=1000).collect::<Vec<i32>>();
    
    c.bench_function("unboxed_pipeline", |b| {
        b.iter(|| {
            let d = Data::new(black_box(data.clone()));
            let result: Vec<i32> = d.pipeline().collect();
            black_box(result)
        })
    });
    
    c.bench_function("boxed_pipeline", |b| {
        b.iter(|| {
            let result: Vec<i32> = boxed_pipeline(black_box(&data)).collect();
            black_box(result)
        })
    });
}

fn bench_shared_state_mutex(c: &mut Criterion) {
    c.bench_function("mutex_counter_8_threads", |b| {
        b.iter(|| {
            let result = shared_state_demo::mutex_counter(8, 1000);
            black_box(result)
        })
    });
}

fn bench_shared_state_rwlock(c: &mut Criterion) {
    c.bench_function("rwlock_read_heavy", |b| {
        b.iter(|| {
            let result = shared_state_demo::rwlock_accumulate(16, 2, 1000);
            black_box(result)
        })
    });
}

fn bench_async_generic(c: &mut Criterion) {
    c.bench_function("async_add_generic", |b| {
        b.iter(|| {
            let fut = async_add_generic(black_box(2u8), black_box(3u8));
            let result = block_on(fut);
            black_box(result)
        })
    });
}

criterion_group!(
    benches,
    bench_iterator_pipelines,
    bench_shared_state_mutex,
    bench_shared_state_rwlock,
    bench_async_generic
);
criterion_main!(benches);
