//! 最小 Actor 模型示例：邮箱容量 + 背压 + 取消
//! 运行：
//!   cargo run -p c18_model --example concurrency_actor --features tokio-adapter

#[cfg(feature = "tokio-adapter")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use c18_model::runtime_abi::Channel as _;
    use c18_model::runtime_tokio::{TokioCancellationToken, TokioChannel, TokioSpawner};

    let spawner = TokioSpawner;
    let cancel = TokioCancellationToken::new();
    let (tx, mut rx) = <TokioChannel as c18_model::runtime_abi::Channel<&'static str>>::bounded(4);

    let actor = spawner.spawn(async move {
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
    });

    for _ in 0..10 {
        if tx.try_send("ping").is_err() {
            // 背压触发：邮箱满，丢弃或记录
        }
    }
    let _ = tx.send("stop").await;

    let handled = actor.await;
    cancel.cancel();
    println!("actor handled={}", handled);
}

#[cfg(not(feature = "tokio-adapter"))]
fn main() {
    eprintln!("启用 --features tokio-adapter 运行该示例");
}
