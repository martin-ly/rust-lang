use criterion::{criterion_group, criterion_main, Criterion};
use once_cell::sync::Lazy;
use prometheus::{Registry, IntCounter, Histogram, HistogramOpts, Opts};

static BENCH_EXEC_TOTAL: Lazy<IntCounter> = Lazy::new(|| IntCounter::with_opts(Opts::new("bench_exec_total", "基准执行次数")).unwrap());
static BENCH_EXEC_SECONDS: Lazy<Histogram> = Lazy::new(|| Histogram::with_opts(HistogramOpts::new("bench_exec_seconds", "基准耗时(秒)")).unwrap());

fn start_metrics_server() -> Registry {
    let registry = Registry::new();
    let _ = registry.register(Box::new(BENCH_EXEC_TOTAL.clone()));
    let _ = registry.register(Box::new(BENCH_EXEC_SECONDS.clone()));
    let registry_for_server = registry.clone();
    std::thread::spawn(move || {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async move {
            let _ = c06_async::utils::metrics::serve_metrics(registry_for_server, "127.0.0.1:9900").await;
        });
    });
    registry
}

fn bench_dummy(c: &mut Criterion) {
    // 启动一次（多基准共享）；如需要，可通过 Once 控制
    static START: std::sync::Once = std::sync::Once::new();
    START.call_once(|| { let _ = start_metrics_server(); });

    c.bench_function("dummy_work", |b| {
        b.iter(|| {
            let t = std::time::Instant::now();
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                tokio::time::sleep(std::time::Duration::from_millis(5)).await;
            });
            BENCH_EXEC_TOTAL.inc();
            BENCH_EXEC_SECONDS.observe(t.elapsed().as_secs_f64());
        })
    });
}

criterion_group!(benches, bench_dummy);
criterion_main!(benches);


