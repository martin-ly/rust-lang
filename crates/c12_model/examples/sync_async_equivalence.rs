//! 同步 vs 异步：最小可观察等价示例
//! 用同步 mpsc 与异步 async-channel 实现同样的“生产-消费”语义。
//! 运行：
//! cargo run -p c12_model --example sync_async_equivalence --features tokio-adapter

#[cfg(feature = "tokio-adapter")]
#[tokio::main]
async fn main() {
    use async_channel::{bounded, Receiver};
    use std::sync::mpsc;
    use std::thread;

    // 同步版本（阻塞队列）
    let (tx_sync, rx_sync) = mpsc::sync_channel::<u32>(2);
    let h = thread::spawn(move || {
        for i in 0..5 {
            tx_sync.send(i).unwrap();
        }
    });
    drop(h);
    for v in rx_sync.try_iter() {
        let _ = v;
    }

    // 异步版本（有界通道 + await）
    let (tx_async, rx_async): (async_channel::Sender<u32>, Receiver<u32>) = bounded(2);
    let prod = tokio::spawn(async move {
        for i in 0..5u32 {
            let _ = tx_async.send(i).await;
        }
    });
    while let Ok(_v) = rx_async.recv().await {}
    let _ = prod.await;
}

#[cfg(not(feature = "tokio-adapter"))]
fn main() {
    eprintln!("Enable feature: --features tokio-adapter");
}


