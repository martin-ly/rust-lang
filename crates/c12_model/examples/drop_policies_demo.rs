//! 丢弃策略对比：丢最新/丢最旧/拒绝（示意）
//! 运行：cargo run -p c12_model --example drop_policies_demo --features tokio-adapter

#[cfg(feature = "tokio-adapter")]
#[tokio::main]
async fn main() {
    use async_channel::{bounded, Receiver, Sender, TrySendError};

    async fn produce_with_drop_newest(tx: &Sender<u64>, n: u64) {
        for i in 0..n {
            match tx.try_send(i) {
                Ok(_) => {}
                Err(TrySendError::Full(_)) => { /* 丢最新：忽略 */ }
                Err(e) => panic!("{:?}", e),
            }
        }
    }

    async fn produce_block_or_reject(tx: &Sender<u64>, n: u64) {
        for i in 0..n {
            // 拒绝：如果满则返回错误（此处仅打印）
            if let Err(TrySendError::Full(v)) = tx.try_send(i) {
                eprintln!("reject value: {}", v);
            }
        }
    }

    async fn consume(rx: Receiver<u64>) {
        while let Ok(_v) = rx.recv().await {}
    }

    let (tx, rx) = bounded::<u64>(64);
    let c = tokio::spawn(consume(rx));
    produce_with_drop_newest(&tx, 10_000).await;
    produce_block_or_reject(&tx, 10_000).await;
    drop(tx);
    let _ = c.await;
}

#[cfg(not(feature = "tokio-adapter"))]
fn main() {
    eprintln!("Enable feature: --features tokio-adapter");
}


