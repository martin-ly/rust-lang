use criterion::{criterion_group, criterion_main, Criterion};

#[cfg(feature = "tower-examples")]
#[tokio::main]
async fn async_entry(c: &mut Criterion) {
    use std::time::Duration;
    use tower::{limit::RateLimitLayer, Service, ServiceBuilder};

    struct Nop;
    impl Service<()> for Nop {
        type Response = ();
        type Error = std::convert::Infallible;
        type Future = std::future::Ready<Result<(), Self::Error>>;
        fn poll_ready(&mut self, _cx: &mut std::task::Context<'_>) -> std::task::Poll<Result<(), Self::Error>> {
            std::task::Poll::Ready(Ok(()))
        }
        fn call(&mut self, _req: ()) -> Self::Future { std::future::ready(Ok(())) }
    }

    let mut group = c.benchmark_group("rate_limit_latency");
    for &(num, per) in &[(50, 1u64), (200, 1), (1000, 1)] {
        group.bench_with_input(format!("{}-per-{}s", num, per), &(num, per), |b, &(num, per)| {
            let rt = tokio::runtime::Runtime::new().unwrap();
            b.to_async(&rt).iter(|| async move {
                let mut svc = ServiceBuilder::new()
                    .layer(RateLimitLayer::new(num, Duration::from_secs(per)))
                    .service(Nop);
                for _ in 0..num {
                    let _ = svc.ready().await.unwrap().call(()).await.unwrap();
                }
            });
        });
    }
    group.finish();
}

#[cfg(not(feature = "tower-examples"))]
fn async_entry(_c: &mut Criterion) { }

pub fn bench_rate_limit(c: &mut Criterion) { async_entry(c); }

criterion_group!(benches, bench_rate_limit);
criterion_main!(benches);


