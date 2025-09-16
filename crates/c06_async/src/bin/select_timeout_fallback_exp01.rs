use c06_async::utils::with_timeout;
use std::time::Duration;

async fn primary() -> Option<&'static str> {
    tokio::time::sleep(Duration::from_millis(200)).await;
    Some("primary")
}

async fn fallback() -> &'static str {
    tokio::time::sleep(Duration::from_millis(50)).await;
    "fallback"
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    // 使用 with_timeout 简化超时降级
    let result = match with_timeout(Duration::from_millis(100), primary()).await {
        Some(v) => v.unwrap_or("none"),
        None => fallback().await,
    };
    println!("result: {}", result);
}
