//! 与 c20_distributed 对接占位：统一取消/超时/背压策略演示
//! 运行：
//!   cargo run -p c18_model --example c20_integration_demo --features c20-integration,tokio-adapter

#[cfg(feature = "c20-integration")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use core::time::Duration;
    use c18_model::runtime_tokio::{TokioCancellationToken, TokioTimer, TokioSpawner};
    let spawner = TokioSpawner;
    let timer = TokioTimer;
    let cancel = TokioCancellationToken::new();

    // 占位：在真实实现中，这里会调用 c20_distributed 的节点/消息机制
    let task = spawner.spawn({
        let cancel = cancel.clone();
        async move {
            tokio::select! {
                _ = cancel.cancelled() => "cancelled",
                _ = timer.sleep(Duration::from_millis(100)) => "ok",
            }
        }
    });

    let res = task.await;
    println!("c20 integration demo result={}", res);
}

#[cfg(not(feature = "c20-integration"))]
fn main() {
    eprintln!(
        "示例需要启用特性：`c20-integration,tokio-adapter`\n运行：cargo run -p c18_model --example c20_integration_demo --features c20-integration,tokio-adapter"
    );
}


