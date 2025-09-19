// ExecHelper 增强版示例：可重试判定 + 截止时间（deadline）

use c06_async::utils::ExecHelper;
use std::time::{Duration, Instant};

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    let exec = ExecHelper::new(4);
    let client = reqwest::Client::new();
    let url = "https://httpbin.org/status/503".to_string();

    let deadline = Instant::now() + Duration::from_secs(3);

    let out = exec
        .run_with_decider_and_deadline(
            move |_| {
                let client = client.clone();
                let url = url.clone();
                async move {
                    let resp = client.get(&url).send().await?;
                    let s = resp.status();
                    if s.is_server_error() { // 5xx 可重试
                        Err(anyhow::anyhow!("server error: {}", s))
                    } else if s.is_success() {
                        Ok(s)
                    } else {
                        Err(anyhow::anyhow!("non-retryable status: {}", s))
                    }
                }
            },
            |e: &anyhow::Error| format!("{e}").contains("server error"),
            5,
            Duration::from_millis(100),
            deadline,
        )
        .await;

    println!("result = {:?}", out);
    Ok(())
}


