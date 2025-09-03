use std::sync::Arc;
use std::time::Duration;
use c06_async::utils::SemaphoreLimiter;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<u32>(8);
    let limiter = SemaphoreLimiter::new(3); // 限制并发处理数

    // 生产者
    let prod = tokio::spawn(async move {
        for i in 0..20u32 { tx.send(i).await.unwrap(); }
    });

    // 单接收者循环：为每个消息在受限并发下派发处理任务
    let limiter_consume = limiter.clone();
    let cons = tokio::spawn(async move {
        while let Some(v) = rx.recv().await {
            let l = limiter_consume.clone();
            tokio::spawn(async move {
                l.run(async move {
                    tokio::time::sleep(Duration::from_millis(60)).await;
                    println!("processed {}", v);
                }).await;
            });
        }
    });

    let _ = tokio::join!(prod, cons);
}


