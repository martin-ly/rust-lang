// 并发流处理示例：buffer_unordered（Rust 1.90）
// 说明：对一组 URL 并发抓取，限制同时在途请求数量，结果乱序到达

use futures::{stream, StreamExt};
use std::time::Duration;

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    let urls = vec![
        "https://httpbin.org/delay/1",
        "https://httpbin.org/get",
        "https://httpbin.org/uuid",
        "https://httpbin.org/headers",
        "https://httpbin.org/anything",
    ];
    let client = reqwest::Client::builder()
        .timeout(Duration::from_secs(3))
        .build()?;

    let concurrency = 3usize;

    let responses = stream::iter(urls.into_iter().map(|u| {
        let c = client.clone();
        async move {
            let r = c.get(u).send().await;
            r.map(|resp| resp.status())
        }
    }))
    .buffer_unordered(concurrency)
    .collect::<Vec<_>>()
    .await;

    for (i, r) in responses.into_iter().enumerate() {
        match r {
            Ok(s) => println!("item#{i} => status={}", s),
            Err(e) => println!("item#{i} => error={:#}", e),
        }
    }
    Ok(())
}


