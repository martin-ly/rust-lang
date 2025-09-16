use c06_async::utils::circuit_breaker::CircuitBreaker;
use c06_async::utils::{retry_with_backoff, with_timeout};
use futures::stream::{self, StreamExt};
use std::time::Instant;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let client = reqwest::Client::new();
    let breaker = CircuitBreaker::new(3, std::time::Duration::from_secs(2));
    let urls = vec![
        "https://example.com/".to_string(),
        "https://example.com/404".to_string(),
        "https://example.com/".to_string(),
    ];

    let results = stream::iter(urls.into_iter().map(|u| {
        let c = client.clone();
        let b = breaker.clone();
        async move {
            let start = Instant::now();
            let op = || {
                let c = c.clone();
                let b = b.clone();
                let u = u.clone();
                async move {
                    let fut = b.run(async move {
                        let r = c.get(&u).send().await.map_err(|e| anyhow::anyhow!(e))?;
                        let status = r.status();
                        let len = r.bytes().await.map_err(|e| anyhow::anyhow!(e))?.len();
                        if !status.is_success() {
                            return Err(anyhow::anyhow!("status {:?}", status));
                        }
                        Ok::<_, anyhow::Error>((status, len))
                    });
                    match with_timeout(std::time::Duration::from_millis(500), fut).await {
                        Some(res) => res,
                        None => Err(anyhow::anyhow!("timeout")),
                    }
                }
            };
            let out = retry_with_backoff(|_| op(), 3, std::time::Duration::from_millis(50)).await;
            let dur_ms = start.elapsed().as_millis() as u64;
            out.map(|ok| (ok.0, ok.1, dur_ms))
        }
    }))
    .buffer_unordered(4)
    .collect::<Vec<_>>()
    .await;

    let mut latencies = Vec::new();
    for r in results {
        match r {
            Ok((status, len, ms)) => {
                println!("ok {status} len={len} {ms}ms");
                latencies.push(ms);
            }
            Err(e) => println!("err {e}"),
        }
    }

    if !latencies.is_empty() {
        latencies.sort_unstable();
        let p50 = latencies[latencies.len() * 50 / 100];
        let p95 = latencies[latencies.len() * 95 / 100];
        println!("p50={}ms p95={}ms (n={})", p50, p95, latencies.len());
    }
}
