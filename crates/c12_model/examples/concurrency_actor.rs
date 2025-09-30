//! 最小 Actor 模型示例：邮箱容量 + 背压 + 取消
//! 运行：
//!   cargo run -p c12_model --example concurrency_actor --features tokio-adapter

#[cfg(feature = "tokio-adapter")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use tokio::sync::mpsc;
    use tokio_util::sync::CancellationToken;

    let cancel = CancellationToken::new();
    let (tx, mut rx) = mpsc::channel::<&'static str>(4);

    let actor = tokio::spawn({
        let cancel = cancel.clone();
        async move {
            let mut handled = 0usize;
            loop {
                tokio::select! {
                    _ = cancel.cancelled() => break handled,
                    Some(msg) = rx.recv() => {
                        handled += 1;
                        if msg == "stop" { break handled; }
                    }
                    else => break handled,
                }
            }
        }
    });

    for _ in 0..10 {
        if tx.try_send("ping").is_err() {
            // 背压触发：邮箱满，丢弃或记录
        }
    }
    let _ = tx.send("stop").await;

    let handled = actor.await.unwrap();
    cancel.cancel();
    println!("actor handled={}", handled);
}

#[cfg(not(feature = "tokio-adapter"))]
fn main() {
    eprintln!("启用 --features tokio-adapter 运行该示例");
}
