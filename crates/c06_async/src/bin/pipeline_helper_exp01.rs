// 流水线 helper 演示：背压 + 并发 + 限速 + 重试 + 超时 + 熔断

use c06_async::utils::{ExecHelper, SimpleTokenBucket};
use c06_async::utils::circuit_breaker::CircuitBreaker;
use std::time::Duration;
use prometheus::{Registry, CounterVec, Histogram, HistogramOpts, Opts, Encoder, TextEncoder};

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    // tracing 初始化（RUST_LOG 控制级别）
    let _ = tracing_subscriber::fmt::try_init();
    // Prometheus 指标注册
    let registry = Registry::new();
    let req_counter = CounterVec::new(Opts::new("pipeline_requests_total", "Pipeline requests"), &["phase"]) ?;
    let err_counter = CounterVec::new(Opts::new("pipeline_errors_total", "Pipeline errors"), &["phase"]) ?;
    let latency = Histogram::with_opts(HistogramOpts::new("pipeline_latency_seconds", "End-to-end latency").buckets(vec![0.01,0.05,0.1,0.2,0.5,1.0,2.0,5.0])) ?;
    registry.register(Box::new(req_counter.clone()))?;
    registry.register(Box::new(err_counter.clone()))?;
    registry.register(Box::new(latency.clone()))?;
    // 导出 /metrics 端点（本地 127.0.0.1:9898），简化为最小实现
    tokio::spawn({
        let registry = registry.clone();
        async move {
            use tokio::net::TcpListener; use tokio::io::AsyncWriteExt; use tokio::io::AsyncReadExt;
            let listener = TcpListener::bind(("127.0.0.1", 9898)).await.expect("bind metrics");
            loop {
                if let Ok((mut socket, _)) = listener.accept().await {
                    let mut buf = [0u8; 1024]; let _ = socket.read(&mut buf).await; // 读丢弃
                    let mf = registry.gather(); let encoder = TextEncoder::new(); let mut out = Vec::new(); let _ = encoder.encode(&mf, &mut out);
                    let body = out;
                    let header = format!("HTTP/1.1 200 OK\r\nContent-Type: text/plain; version=0.0.4\r\nContent-Length: {}\r\n\r\n", body.len());
                    let _ = socket.write_all(header.as_bytes()).await; let _ = socket.write_all(&body).await; let _ = socket.shutdown().await;
                }
            }
        }
    });
    // 限流：每秒 10 个令牌，桶容量 10
    let bucket = SimpleTokenBucket::new(10, 10);

    // 熔断器：连续 5 次失败打开，30s 后半开
    let breaker = CircuitBreaker::new(5, Duration::from_secs(30));

    // 执行助手：并发 4
    let exec = ExecHelper::new(4).with_breaker(breaker);

    let client = reqwest::Client::new();
    let urls: Vec<String> = (0..20).map(|i| format!("https://httpbin.org/status/20{}", i % 5)).collect();

    let mut handles = Vec::new();
    for (idx, url) in urls.into_iter().enumerate() {
        let exec = exec.clone();
        let bucket = bucket.clone();
        let client = client.clone();
        let req_counter = req_counter.clone();
        let err_counter = err_counter.clone();
        let latency = latency.clone();
        handles.push(tokio::spawn(async move {
            bucket.acquire(1).await; // 速率限制
            let start = std::time::Instant::now();
            req_counter.with_label_values(&["start"]).inc();
            let res = exec
                .run_with_policies(
                    move |_| {
                        let client = client.clone();
                        let url = url.clone();
                        async move {
                            let r = client.get(&url).send().await?;
                            let s = r.status();
                            if !s.is_success() {
                                Err(anyhow::anyhow!("status: {}", s))
                            } else {
                                Ok(s)
                            }
                        }
                    },
                    3,
                    Duration::from_millis(100),
                    Duration::from_secs(2),
                )
                .await;
            let elapsed = start.elapsed().as_secs_f64();
            latency.observe(elapsed);
            if res.is_err() { err_counter.with_label_values(&["worker"]).inc(); }
            tracing::info!(job = idx, ?res, elapsed, "pipeline handled one job");
        }));
    }

    for h in handles { let _ = h.await; }
    Ok(())
}


