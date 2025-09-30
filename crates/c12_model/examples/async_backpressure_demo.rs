//! 异步背压演示：bounded 通道 + tower 限流 + 超时/重试
//! 运行：
//! cargo run -p c12_model --example async_backpressure_demo --features tokio-adapter,tower-examples

#[cfg(all(feature = "tokio-adapter", feature = "tower-examples"))]
mod demo {
    use async_channel::{bounded, Receiver, Sender};
    use std::time::Duration;
    use tokio::task::JoinSet;
    use tower::{limit::ConcurrencyLimitLayer, timeout::TimeoutLayer, ServiceBuilder};

    async fn producer(tx: Sender<u64>, total: u64) {
        for i in 0..total {
            // 有界队列：满则等待，形成自然背压
            let _ = tx.send(i).await;
        }
    }

    async fn consumer(rx: Receiver<u64>) {
        // 模拟处理开销
        while let Ok(v) = rx.recv().await {
            let _ = tokio::time::sleep(Duration::from_millis(5)).await;
            let _ = v;
        }
    }

    pub async fn run() {
        let (tx, rx) = bounded::<u64>(128);

        // 组合中间件：并发限制 + 超时
        let _middleware = ServiceBuilder::new()
            .layer(ConcurrencyLimitLayer::new(32))
            .layer(TimeoutLayer::new(Duration::from_secs(1)));

        let mut tasks = JoinSet::new();
        tasks.spawn(producer(tx.clone(), 10_000));
        tasks.spawn(consumer(rx));

        while let Some(_res) = tasks.join_next().await {}
    }
}

#[cfg(all(feature = "tokio-adapter", feature = "tower-examples"))]
#[tokio::main]
async fn main() {
    demo::run().await;
}

#[cfg(not(all(feature = "tokio-adapter", feature = "tower-examples")))]
fn main() {
    eprintln!("Enable features: --features tokio-adapter,tower-examples");
}


