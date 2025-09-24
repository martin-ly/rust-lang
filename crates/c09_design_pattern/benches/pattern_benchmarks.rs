use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

pub fn rayon_parallel_sum_benchmark(c: &mut Criterion) {
    let data: Vec<u64> = (0..1_000_000).collect();
    c.bench_function("rayon_parallel_sum", |b| {
        b.iter(|| {
            #[cfg(feature = "rayon")] // 允许未来做特性门控
            {
                use rayon::prelude::*;
                let sum: u64 = data.par_iter().cloned().sum();
                black_box(sum);
            }
            #[cfg(not(feature = "rayon"))]
            {
                let sum: u64 = data.iter().cloned().sum();
                black_box(sum);
            }
        })
    });
}

#[cfg(feature = "tokio-bench")] // 可选异步路径，避免默认引入运行时
pub fn tokio_spawn_benchmark(c: &mut Criterion) {
    use std::time::Duration;
    c.bench_function("tokio_spawn_small_tasks", |b| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        b.iter(|| {
            rt.block_on(async {
                let mut handles = Vec::with_capacity(100);
                for _ in 0..100 {
                    handles.push(tokio::spawn(async {
                        tokio::time::sleep(Duration::from_millis(1)).await;
                        1u32
                    }));
                }
                let mut acc = 0u32;
                for h in handles {
                    acc += h.await.unwrap();
                }
                black_box(acc);
            });
        })
    });
}

pub fn criterion_benchmark(c: &mut Criterion) {
    rayon_parallel_sum_benchmark(c);
    #[cfg(feature = "tokio-bench")]
    tokio_spawn_benchmark(c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

