use criterion::{Criterion, criterion_group, criterion_main};
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
                    for i in 0..10_000u32 {
                        tx.send(i).await.unwrap();
                    }
                });
                let cons = tokio::spawn(async move {
                    let mut sum = 0u64;
                    while let Some(v) = rx.recv().await {
                        sum += v as u64;
                    }
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
                    for i in 0..10_000u32 {
                        tx.send(i).unwrap();
                    }
                });
                let cons = tokio::spawn(async move {
                    let mut sum = 0u64;
                    while let Some(v) = rx.recv().await {
                        sum += v as u64;
                    }
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
                    for i in 0..5_000u32 {
                        tx.send(i).await.unwrap();
                    }
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

fn bench_select_and_joinset(c: &mut Criterion) {
    let mut g = c.benchmark_group("select_joinset");
    g.bench_function("select_two_timers", |b| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        b.iter(|| {
            rt.block_on(async {
                let mut a = tokio::time::interval(Duration::from_millis(1));
                let mut b = tokio::time::interval(Duration::from_millis(2));
                let mut n = 0u32;
                while n < 100u32 {
                    tokio::select! {
                        _ = a.tick() => n += 1,
                        _ = b.tick() => n += 1,
                    }
                }
                black_box(n);
            })
        })
    });
    g.bench_function("joinset_spawn_100", |b| {
        let rt = tokio::runtime::Runtime::new().unwrap();
        b.iter(|| {
            rt.block_on(async {
                let mut set = tokio::task::JoinSet::new();
                for i in 0..100u32 {
                    set.spawn(async move { i });
                }
                let mut sum = 0u64;
                while let Some(r) = set.join_next().await {
                    sum += r.unwrap() as u64;
                }
                black_box(sum);
            })
        })
    });
    g.finish();
}

fn bench_backpressure_limit(c: &mut Criterion) {
    let mut g = c.benchmark_group("backpressure_limit");
    for cap in [8usize, 32, 128] {
        g.bench_function(format!("bounded_cap_{}", cap), |b| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            b.iter(|| {
                rt.block_on(async {
                    let (tx, mut rx) = tokio::sync::mpsc::channel::<u32>(cap);
                    let prod = tokio::spawn(async move {
                        for i in 0..2000u32 {
                            tx.send(i).await.unwrap();
                        }
                    });
                    let cons = tokio::spawn(async move {
                        let mut sum = 0u64;
                        while let Some(v) = rx.recv().await {
                            sum += v as u64;
                        }
                        black_box(sum);
                    });
                    let _ = tokio::join!(prod, cons);
                })
            })
        });
    }

    for conc in [2usize, 4, 8] {
        g.bench_function(format!("semaphore_conc_{}", conc), |b| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            b.iter(|| {
                rt.block_on(async {
                    use std::sync::Arc;
                    let sem = Arc::new(tokio::sync::Semaphore::new(conc));
                    let mut handles = Vec::new();
                    for _ in 0..500usize {
                        let sem = Arc::clone(&sem);
                        handles.push(tokio::spawn(async move {
                            let permit = sem.acquire_owned().await.unwrap();
                            let _p = permit;
                            black_box(1u64)
                        }));
                    }
                    for h in handles {
                        let _ = h.await;
                    }
                })
            })
        });
    }
    g.finish();
}

criterion_group!(extended, bench_select_and_joinset, bench_backpressure_limit);
