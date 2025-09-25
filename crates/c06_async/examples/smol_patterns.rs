use anyhow::Result;
use futures::{stream::FuturesUnordered, StreamExt};
use smol::io::{AsyncReadExt, AsyncWriteExt};
use smol::net::TcpListener;

/// 入口：Smol 轻量运行时，适合 CLI/嵌入式/库内嵌。
fn main() -> Result<()> {
    env_logger::init();
    smol::block_on(async move {
        // 1) FuturesUnordered 演示：批量并发与结果收割
        basic_concurrency().await?;
        // 2) 最小 echo TCP 服务器：Smol I/O 基本模式
        tcp_echo("127.0.0.1:0").await?;
        Ok(())
    })
}

/// 并发集合：FuturesUnordered 适合大量动态并发任务。
async fn basic_concurrency() -> Result<()> {
    async fn compute(i: usize) -> Result<usize> { Ok(i * 2) }
    let mut futs = FuturesUnordered::new();
    for i in 0..100 { futs.push(async move { compute(i).await }); }
    let mut acc = 0usize;
    while let Some(v) = futs.next().await { acc += v?; }
    println!("acc={}", acc);
    Ok(())
}

/// 最小 echo 服务器：detach 后注意错误丢失问题。
async fn tcp_echo(addr: &str) -> Result<()> {
    let listener = TcpListener::bind(addr).await?;
    let local = listener.local_addr()?;
    println!("listening {}", local);
    smol::spawn(async move {
        loop {
            let (mut s, _) = listener.accept().await.unwrap();
            smol::spawn(async move {
                let mut buf = vec![0u8; 1024];
                loop {
                    match s.read(&mut buf).await { Ok(0) => break, Ok(n) => {
                        if s.write_all(&buf[..n]).await.is_err() { break; }
                    }, Err(_) => break }
                }
            }).detach();
        }
    }).detach();
    Ok(())
}


