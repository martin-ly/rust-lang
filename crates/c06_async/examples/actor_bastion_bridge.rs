#[cfg(not(feature = "bastion"))]
fn main() {
    eprintln!("enable with: cargo run --features bastion --example actor_bastion_bridge");
}

#[cfg(feature = "bastion")]
#[tokio::main]
async fn main() {
    use bastion::prelude::*;
    use tracing::{info, instrument};
    use once_cell::sync::Lazy;
    use prometheus::{Registry, IntCounter, Opts};
    use c06_async::utils::metrics;

    let _ = tracing_subscriber::fmt().with_env_filter("info").try_init();

    // 指标
    static BRIDGE_IN_TOTAL: Lazy<IntCounter> = Lazy::new(|| IntCounter::with_opts(Opts::new("bridge_in_total", "桥接入口收到的消息总数")).unwrap());
    static PIPELINE_IN_TOTAL: Lazy<IntCounter> = Lazy::new(|| IntCounter::with_opts(Opts::new("pipeline_in_total", "流水线入口收到的消息总数")).unwrap());
    let registry = Registry::new();
    let _ = registry.register(Box::new(BRIDGE_IN_TOTAL.clone()));
    let _ = registry.register(Box::new(PIPELINE_IN_TOTAL.clone()));
    let _ = tokio::spawn(metrics::serve_metrics(registry.clone(), "127.0.0.1:9896"));

    Bastion::init();

    let (tx_high, mut rx_high) = tokio::sync::mpsc::channel::<String>(16);
    let (tx_norm, mut rx_norm) = tokio::sync::mpsc::channel::<String>(64);
    let (tx_pipeline, mut rx_pipeline) = tokio::sync::mpsc::channel::<String>(64);

    // 合并器：优先级到流水线
    tokio::spawn(async move {
        loop {
            tokio::select! {
                biased;
                Some(m) = rx_high.recv() => { let _ = tx_pipeline.send(m).await; PIPELINE_IN_TOTAL.inc(); }
                Some(m) = rx_norm.recv() => { let _ = tx_pipeline.send(m).await; PIPELINE_IN_TOTAL.inc(); }
                else => break,
            }
        }
    });

    // 流水线阶段
    tokio::spawn(async move {
        while let Some(m) = rx_pipeline.recv().await {
            info!(msg=%m, "pipeline stage");
        }
    });

    // bastion 子进程：作为 Actor 边界
    Bastion::children(|children| {
        children.with_exec(|ctx| async move {
            loop {
                msg! { ctx,
                    msg: String => {
                        BRIDGE_IN_TOTAL.inc();
                        // 简单规则：包含 urgent 走高优先级
                        let is_high = msg.contains("urgent");
                        if is_high { let _ = tx_high.send(msg).await; } else { let _ = tx_norm.send(msg).await; }
                    };
                    _msg => ();
                }
            }
        })
    }).ok();

    // 发送测试消息
    let _ = Bastion::broadcast("hello".to_string());
    let _ = Bastion::broadcast("urgent: please handle".to_string());

    Bastion::start();
    std::thread::sleep(std::time::Duration::from_millis(300));
    Bastion::stop();
}


