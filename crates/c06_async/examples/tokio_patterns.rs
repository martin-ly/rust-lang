use anyhow::Result;
use futures::FutureExt;
use std::sync::Arc;
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::TcpListener,
    sync::{mpsc, Semaphore},
    task::JoinSet,
    time::{timeout, Duration},
};

/// 入口：多线程 Tokio 运行时。生产环境建议结合 CPU 配额调整线程数。
#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<()> {
    // 结构化日志（开发环境使用人类可读格式；生产可输出 JSON）
    tracing_subscriber::fmt::init();
    // 1) 超时边界演示：小超时包裹慢操作
    basic_timeout().await;
    // 2) 有界通道背压：避免内存无界增长
    mpsc_backpressure().await;
    // 3) 并发限额：Semaphore + JoinSet
    limited_concurrency(200).await?;
    // 4) 最小 echo TCP 服务器：演示 Tokio I/O 基本模式
    echo_server("127.0.0.1:0").await?;
    Ok(())
}

/// 超时与取消：timeout 只说明未在时限内完成，不保证任务“已停止”。
async fn basic_timeout() {
    let slow = async { tokio::time::sleep(Duration::from_millis(500)).await };
    let res = timeout(Duration::from_millis(50), slow).await;
    tracing::info!("basic_timeout = {:?}", res.is_ok());
}

/// 背压：使用有界队列并匹配消费速率，避免生产过快导致 OOM。
async fn mpsc_backpressure() {
    let (tx, mut rx) = mpsc::channel::<u64>(256);
    let prod = tokio::spawn(async move {
        for i in 0..10_000u64 {
            if tx.send(i).await.is_err() { break; }
        }
    });
    let cons = tokio::spawn(async move {
        while let Some(v) = rx.recv().await { let _ = v; /* 业务处理 */ }
    });
    let _ = tokio::join!(prod, cons);
}

/// 并发限流：信号量与 JoinSet 控制并发上限与结果收割。
async fn limited_concurrency(n: usize) -> Result<()> {
    async fn work(i: usize) -> Result<usize> { Ok(i * 2) }
    let limiter = Arc::new(Semaphore::new(64));
    let mut set = JoinSet::new();
    for i in 0..n {
        let sem = limiter.clone();
        set.spawn(async move { let _p = sem.acquire_owned().await.unwrap(); work(i).await });
    }
    let mut sum = 0usize;
    while let Some(r) = set.join_next().await { sum += r??; }
    tracing::info!(%sum, "limited_concurrency done");
    Ok(())
}

/// 最小 echo 服务器：注意错误处理与连接的生命周期。
async fn echo_server(addr: &str) -> Result<()> {
    let listener = TcpListener::bind(addr).await?;
    let local = listener.local_addr()?;
    tracing::info!(%local, "echo listening");
    let server = async move {
        loop {
            let (mut s, _) = listener.accept().await?;
            tokio::spawn(async move {
                let mut buf = vec![0u8; 1024];
                loop {
                    match s.read(&mut buf).await { Ok(0) => break, Ok(n) => {
                        if s.write_all(&buf[..n]).await.is_err() { break; }
                    }, Err(_) => break }
                }
            });
            if false { break; }
        }
        #[allow(unreachable_code)]
        Ok::<_, std::io::Error>(())
    };
    let _ = server.map(|r| { let _=r; }).await;
    Ok(())
}


