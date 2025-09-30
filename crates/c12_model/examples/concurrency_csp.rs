//! 最小 CSP 风格示例：有界通道 + 生产者/消费者 + 超时/取消
//! 运行：
//!   cargo run -p c12_model --example concurrency_csp --features tokio-adapter

#[cfg(feature = "tokio-adapter")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use tokio::sync::mpsc;
    use tokio_util::sync::CancellationToken;
    use std::time::Duration;

    let cancel = CancellationToken::new();
    let (tx, mut rx) = mpsc::channel::<u32>(8);

    // 生产者
    let prod = tokio::spawn({
        let tx = tx.clone();
        let cancel = cancel.clone();
        async move {
            for i in 0..100u32 {
                if cancel.is_cancelled() {
                    break;
                }
                if tx.send(i).await.is_err() {
                    break;
                }
            }
        }
    });

    // 消费者（带超时）
    let cons = tokio::spawn({
        let cancel = cancel.clone();
        async move {
            let mut sum = 0u64;
            loop {
                tokio::select! {
                    _ = cancel.cancelled() => break sum,
                    _ = tokio::time::sleep(Duration::from_millis(50)) => {
                        // 周期性检查，模拟处理
                    }
                    Some(v) = rx.recv() => {
                        sum += v as u64;
                        if sum > 1000 { break sum; }
                    }
                    else => break sum,
                }
            }
        }
    });

    // 等待并取消
    let _ = prod.await;
    let total = cons.await.unwrap();
    cancel.cancel();
    println!("csp total={}", total);
}

#[cfg(not(feature = "tokio-adapter"))]
fn main() {
    eprintln!("启用 --features tokio-adapter 运行该示例");
}
