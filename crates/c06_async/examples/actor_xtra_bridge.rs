#[cfg(not(feature = "xtra"))]
fn main() {
    eprintln!("enable with: cargo run --features xtra --example actor_xtra_bridge");
}

#[cfg(feature = "xtra")]
#[tokio::main]
async fn main() {
    use tracing::info;
    let _ = tracing_subscriber::fmt().with_env_filter("info").try_init();
    use once_cell::sync::Lazy;
    use prometheus::{Registry, IntCounter, Opts};
    use c06_async::utils::metrics;

    use xtra::{prelude::*, Address};

    // 指标
    static BRIDGE_IN_TOTAL: Lazy<IntCounter> = Lazy::new(|| IntCounter::with_opts(Opts::new("xtra_bridge_in_total", "xtra 桥接入口消息计数")).unwrap());
    static PIPELINE_IN_TOTAL: Lazy<IntCounter> = Lazy::new(|| IntCounter::with_opts(Opts::new("xtra_pipeline_in_total", "xtra 流水线入口消息计数")).unwrap());
    let registry = Registry::new();
    let _ = registry.register(Box::new(BRIDGE_IN_TOTAL.clone()));
    let _ = registry.register(Box::new(PIPELINE_IN_TOTAL.clone()));
    let _ = tokio::spawn(metrics::serve_metrics(registry.clone(), "127.0.0.1:9895"));

    // CSP 管线入口
    let (tx_pipeline, mut rx_pipeline) = tokio::sync::mpsc::channel::<String>(64);

    // 流水线阶段
    tokio::spawn(async move {
        while let Some(m) = rx_pipeline.recv().await {
            info!(msg=%m, "pipeline stage");
        }
    });

    struct Router { tx: tokio::sync::mpsc::Sender<String> }
    struct Inbound(pub String);

    #[async_trait::async_trait]
    impl Actor for Router { type Stop = (); }

    #[async_trait::async_trait]
    impl Handler<Inbound> for Router {
        type Return = ();
        async fn handle(&mut self, msg: Inbound, _ctx: &mut xtra::Context<Self>) {
            // 简单分类规则（可扩展为优先级映射）
            BRIDGE_IN_TOTAL.inc();
            let _ = self.tx.send(msg.0).await;
            PIPELINE_IN_TOTAL.inc();
        }
    }

    let router_addr: Address<Router> = Router { tx: tx_pipeline }.create(None).spawn_global().await;

    let _ = router_addr.send(Inbound("hello".into())).await;
    let _ = router_addr.send(Inbound("from xtra".into())).await;

    tokio::time::sleep(std::time::Duration::from_millis(200)).await;
}


