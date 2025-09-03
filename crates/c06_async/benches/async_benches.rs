use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use std::time::Duration;

fn bench_mpsc(c: &mut Criterion) {
    let mut g = c.benchmark_group("mpsc_bounded_vs_unbounded");
    g.sample_size(20);
    g.bench_function("bounded32_10k", |b| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        b.iter(|| {
            rt.block_on(async {
                let (tx, mut rx) = tokio::sync::mpsc::channel::<u32>(32);
                let prod = tokio::spawn(async move {
                    for i in 0..10_000u32 { tx.send(i).await.unwrap(); }
                });
                let cons = tokio::spawn(async move {
                    let mut sum = 0u64;
                    while let Some(v) = rx.recv().await { sum += v as u64; }
                    black_box(sum);
                });
                let _ = tokio::join!(prod, cons);
            })
        })
    });
    g.bench_function("unbounded_10k", |b| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        b.iter(|| {
            rt.block_on(async {
                let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<u32>();
                let prod = tokio::spawn(async move {
                    for i in 0..10_000u32 { tx.send(i).unwrap(); }
                });
                let cons = tokio::spawn(async move {
                    let mut sum = 0u64;
                    while let Some(v) = rx.recv().await { sum += v as u64; }
                    black_box(sum);
                });
                let _ = tokio::join!(prod, cons);
            })
        })
    });
    g.finish();
}

fn bench_semaphore_pipeline(c: &mut Criterion) {
    let mut g = c.benchmark_group("semaphore_pipeline_throughput");
    g.measurement_time(Duration::from_secs(10));
    g.bench_function("semaphore_concurrency4_5k", |b| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        b.iter(|| {
            rt.block_on(async {
                use std::sync::Arc;
                let (tx, mut rx) = tokio::sync::mpsc::channel::<u32>(128);
                let sem = Arc::new(tokio::sync::Semaphore::new(4));
                let prod = tokio::spawn(async move {
                    for i in 0..5_000u32 { tx.send(i).await.unwrap(); }
                });
                let cons = {
                    let sem = Arc::clone(&sem);
                    tokio::spawn(async move {
                        let mut sum = 0u64;
                        while let Some(v) = rx.recv().await {
                            let permit = sem.clone().acquire_owned().await.unwrap();
                            let h = tokio::spawn(async move {
                                let _p = permit;
                                black_box(v as u64)
                            });
                            sum += h.await.unwrap();
                        }
                        black_box(sum);
                    })
                };
                let _ = tokio::join!(prod, cons);
            })
        })
    });
    g.finish();
}

criterion_group!(benches, bench_mpsc, bench_semaphore_pipeline);
criterion_main!(benches);


