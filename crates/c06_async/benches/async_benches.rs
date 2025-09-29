use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use once_cell::sync::Lazy;
use prometheus::{Registry, IntCounter, Histogram, HistogramOpts, Opts};
use std::hint::black_box;
use std::time::Duration;

// 基准目标：对比不同并发度下 JoinSet 与 join_all 的吞吐（简化原型，避免 async feature）

fn bench_joinset_concurrency(c: &mut Criterion) {
    // 基准×指标：最小联动（可选）
    static BENCH_EXEC_TOTAL: Lazy<IntCounter> = Lazy::new(|| IntCounter::with_opts(Opts::new("bench_exec_total", "基准执行次数")).unwrap());
    static BENCH_EXEC_SECONDS: Lazy<Histogram> = Lazy::new(|| Histogram::with_opts(HistogramOpts::new("bench_exec_seconds", "基准耗时(秒)")).unwrap());
    let registry = Registry::new();
    let _ = registry.register(Box::new(BENCH_EXEC_TOTAL.clone()));
    let _ = registry.register(Box::new(BENCH_EXEC_SECONDS.clone()));
    let mut group = c.benchmark_group("joinset_concurrency");
    for conc in [1usize, 2, 4, 8, 16] {
        group.throughput(Throughput::Elements(conc as u64));
        group.measurement_time(Duration::from_secs(5));
        group.bench_with_input(BenchmarkId::from_parameter(conc), &conc, |b, &concurrency| {
            b.iter(|| {
                let rt = tokio::runtime::Runtime::new().unwrap();
                let t = std::time::Instant::now();
                rt.block_on(async move {
                    use tokio::task::JoinSet;
                    let mut set = JoinSet::new();
                    for _ in 0..concurrency {
                        set.spawn(async {
                            tokio::time::sleep(Duration::from_millis(1)).await;
                            1u64
                        });
                    }
                    let mut sum = 0u64;
                    while let Some(r) = set.join_next().await {
                        sum += r.unwrap();
                    }
                    sum
                })
                ;
                BENCH_EXEC_TOTAL.inc();
                BENCH_EXEC_SECONDS.observe(t.elapsed().as_secs_f64());
            });
        });
    }
    group.finish();
}

fn bench_join_all_concurrency(c: &mut Criterion) {
    let mut group = c.benchmark_group("join_all_concurrency");
    for conc in [1usize, 2, 4, 8, 16] {
        group.throughput(Throughput::Elements(conc as u64));
        group.measurement_time(Duration::from_secs(5));
        group.bench_with_input(BenchmarkId::from_parameter(conc), &conc, |b, &concurrency| {
            b.iter(|| {
                let rt = tokio::runtime::Runtime::new().unwrap();
                rt.block_on(async move {
                    let tasks: Vec<_> = (0..concurrency)
                        .map(|_| async {
                            tokio::time::sleep(Duration::from_millis(1)).await;
                            1u64
                        })
                        .collect();
                    let vals = futures::future::join_all(tasks).await;
                    vals.into_iter().sum::<u64>()
                })
            });
        });
    }
    group.finish();
}

// 下面继续定义更多基准项，并在文件末尾统一注册多个 group 与 main

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

// 统一在末尾注册

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

// 统一在末尾注册

// 统一注册所有基准组
criterion_group!(benches, bench_joinset_concurrency, bench_join_all_concurrency, bench_mpsc, bench_semaphore_pipeline, bench_select_and_joinset, bench_backpressure_limit);
criterion_main!(benches);
