// 并发抓取示例（Rust 1.90）
// 说明：使用 reqwest + tokio 并发抓取多个 URL，展示 try_join/select 超时与错误处理

use std::time::Duration;

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    let urls = vec![
        "https://httpbin.org/delay/1",
        "https://httpbin.org/get",
        "https://httpbin.org/status/503",
    ];

    let client = reqwest::Client::builder()
        .timeout(Duration::from_secs(5))
        .build()?;

    // 并发抓取：每个任务有自身的 2s 超时
    let tasks = urls.into_iter().map(|u| {
        let c = client.clone();
        async move {
            let fut = c.get(u).send();
            let resp = tokio::time::timeout(Duration::from_secs(2), fut).await??;
            let status = resp.status();
            Ok::<_, anyhow::Error>(status)
        }
    });

    // 将若干请求并发执行，并收集结果
    let results = futures::future::join_all(tasks).await;
    for (idx, r) in results.into_iter().enumerate() {
        match r {
            Ok(s) => println!("req#{idx} => status={}" , s),
            Err(e) => println!("req#{idx} => error={:#}", e),
        }
    }
    Ok(())
}


