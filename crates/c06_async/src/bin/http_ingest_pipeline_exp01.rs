// 端到端流水线：HTTP 入站 -> 有界队列 -> 工作池(ExecStrategyBuilder) -> 回传

use c06_async::utils::{ExecStrategyBuilder, SimpleTokenBucket};
use c06_async::utils::circuit_breaker::CircuitBreaker;
use std::time::Duration;
use prometheus::{Registry, CounterVec, Histogram, HistogramOpts, Opts, Encoder, TextEncoder};

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    let _ = tracing_subscriber::fmt::try_init();
    // Prometheus 指标
    let registry = Registry::new();
    let ingested = CounterVec::new(Opts::new("ingest_total", "Items ingested"), &["stage"]) ?;
    let errors = CounterVec::new(Opts::new("ingest_errors_total", "Errors"), &["stage"]) ?;
    let proc_latency = Histogram::with_opts(HistogramOpts::new("ingest_latency_seconds", "Per-item latency").buckets(vec![0.005,0.01,0.05,0.1,0.2,0.5,1.0,2.0])) ?;
    registry.register(Box::new(ingested.clone()))?;
    registry.register(Box::new(errors.clone()))?;
    registry.register(Box::new(proc_latency.clone()))?;
    tokio::spawn({
        let registry = registry.clone();
        async move {
            use tokio::net::TcpListener; use tokio::io::{AsyncReadExt, AsyncWriteExt};
            let listener = TcpListener::bind(("127.0.0.1", 9899)).await.expect("bind metrics");
            loop {
                if let Ok((mut s, _)) = listener.accept().await {
                    let mut buf = [0u8;1024]; let _=s.read(&mut buf).await;
                    let mf = registry.gather(); let enc = TextEncoder::new(); let mut out=Vec::new(); let _=enc.encode(&mf, &mut out);
                    let header = format!("HTTP/1.1 200 OK\r\nContent-Type: text/plain; version=0.0.4\r\nContent-Length: {}\r\n\r\n", out.len());
                    let _=s.write_all(header.as_bytes()).await; let _=s.write_all(&out).await; let _=s.shutdown().await;
                }
            }
        }
    });
    let (tx, mut rx) = tokio::sync::mpsc::channel::<String>(128); // 背压

    // 模拟 HTTP 入站生产者
    let prod = tokio::spawn({
        let tx = tx.clone();
        let ingested_p = ingested.clone();
        async move {
            for i in 0..200 {
                let _ = tx.send(format!("job-{i}")).await;
                ingested_p.with_label_values(&["enqueue"]).inc();
            }
        }
    });

    // 构建策略：并发 8，重试 5，超时 2s，熔断 + 限速
    let breaker = CircuitBreaker::new(5, Duration::from_secs(30));
    let bucket = SimpleTokenBucket::new(50, 50);
    let runner = ExecStrategyBuilder::new()
        .concurrency(8)
        .attempts(5)
        .start_delay(Duration::from_millis(50))
        .timeout(Duration::from_secs(2))
        .breaker(breaker)
        .token_bucket(bucket)
        .build();

    let worker = tokio::spawn(async move {
        let client = reqwest::Client::new();
        let mut handled = 0u32;
        while let Some(job) = rx.recv().await {
            let client = client.clone();
            let url = format!("https://httpbin.org/anything/{}", job);
            let start = std::time::Instant::now();
            let ingested = ingested.clone();
            let errors = errors.clone();
            let proc_latency = proc_latency.clone();
            let res = runner
                .run(
                    move |_| {
                        let client = client.clone();
                        let url = url.clone();
                        async move {
                            let r = client.get(&url).send().await?;
                            let s = r.status();
                            if s.is_success() { Ok(s) } else { Err(anyhow::anyhow!("status {s}")) }
                        }
                    },
                    Some(|e: &anyhow::Error| format!("{e}").contains("status 5")),
                )
                .await;
            handled += 1;
            if handled.is_multiple_of(50) { tracing::info!(handled, "progress"); }
            let el = start.elapsed().as_secs_f64(); proc_latency.observe(el);
            if res.is_err() { errors.with_label_values(&["worker"]).inc(); } else { ingested.with_label_values(&["done"]).inc(); }
            tracing::info!(job = job.as_str(), ?res, "ingest handled");
        }
    });

    let _ = tokio::join!(prod, worker);
    Ok(())
}


