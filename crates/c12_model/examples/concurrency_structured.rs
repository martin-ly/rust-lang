//! 结构化并发最小示例：作用域内 spawn + 取消传播
//! 运行：
//!   cargo run -p c12_model --example concurrency_structured --features tokio-adapter

#[cfg(feature = "tokio-adapter")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    use tokio_util::sync::CancellationToken;
    use std::time::Duration;

    let cancel = CancellationToken::new();

    let parent = tokio::spawn({
        let cancel = cancel.clone();
        async move {
            let t1 = tokio::spawn({
                let cancel = cancel.clone();
                async move {
                    tokio::select! {
                        _ = cancel.cancelled() => 1,
                        _ = tokio::time::sleep(Duration::from_millis(200)) => 2,
                    }
                }
            });

            let t2 = tokio::spawn({
                let cancel = cancel.clone();
                async move {
                    tokio::select! {
                        _ = cancel.cancelled() => 3,
                        _ = tokio::time::sleep(Duration::from_millis(50)) => 4,
                    }
                }
            });

            let r1 = t1.await.unwrap();
            let r2 = t2.await.unwrap();
            (r1, r2)
        }
    });

    // 父作用域内取消
    cancel.cancel();
    let (r1, r2) = parent.await.unwrap();
    println!("structured r1={}, r2={}", r1, r2);
}

#[cfg(not(feature = "tokio-adapter"))]
fn main() {
    eprintln!("启用 --features tokio-adapter 运行该示例");
}
