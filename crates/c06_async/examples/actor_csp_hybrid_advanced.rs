use std::sync::Arc;
use std::time::Duration;

use tokio::select;
use tokio::sync::{broadcast, mpsc, Mutex};
use tokio::time::{interval, sleep, Instant};
use tracing::{info, warn, instrument};
use c06_async::utils::{metrics, supervisor};

// 指标导出（Prometheus）
use prometheus::{Histogram, HistogramOpts, IntCounter, IntGauge, Opts, Registry};

#[derive(Clone, Debug)]
enum Priority { High, Normal }

#[derive(Clone, Debug)]
struct Message { priority: Priority, payload: String }

#[derive(Clone)]
struct IngressActor { tx_high: mpsc::Sender<Message>, tx_norm: mpsc::Sender<Message> }

impl IngressActor {
    fn new(tx_high: mpsc::Sender<Message>, tx_norm: mpsc::Sender<Message>) -> Self { Self { tx_high, tx_norm } }
    async fn send(&self, msg: Message) {
        let res = match msg.priority { Priority::High => self.tx_high.send(msg).await, Priority::Normal => self.tx_norm.send(msg).await };
        if let Err(e) = res { warn!(error = %e, "ingress mailbox full or closed"); }
    }
}

/// 简易限速器：令牌桶
struct TokenBucket { capacity: u64, tokens: u64, refill_per_ms: f64, last: Instant }

impl TokenBucket {
    fn new(capacity: u64, refill_per_sec: u64) -> Self {
        Self { capacity, tokens: capacity, refill_per_ms: refill_per_sec as f64 / 1000.0, last: Instant::now() }
    }
    fn allow(&mut self, cost: u64) -> bool {
        let now = Instant::now();
        let elapsed_ms = now.duration_since(self.last).as_millis() as f64;
        let add = (elapsed_ms * self.refill_per_ms) as u64;
        if add > 0 { self.tokens = (self.tokens + add).min(self.capacity); self.last = now; }
        if self.tokens >= cost { self.tokens -= cost; true } else { false }
    }
}

// 监督器已抽取到 utils::supervisor

#[instrument(skip(rx_high, rx_norm, tx_pipeline, shutdown_rx), level = "info", name = "mailbox_mux")]
async fn run_mailbox_mux(mut rx_high: mpsc::Receiver<Message>, mut rx_norm: mpsc::Receiver<Message>, tx_pipeline: mpsc::Sender<Message>, mut shutdown_rx: broadcast::Receiver<()>) -> anyhow::Result<()> {
    loop {
        select! {
            biased;
            _ = shutdown_rx.recv() => break,
            Some(msg) = rx_high.recv() => { tx_pipeline.send(msg).await.map_err(|e| anyhow::anyhow!(e))?; }
            Some(msg) = rx_norm.recv() => { tx_pipeline.send(msg).await.map_err(|e| anyhow::anyhow!(e))?; }
            else => break,
        }
    }
    Ok(())
}

#[instrument(skip(rx, limiter, shutdown_rx, processed_total, dropped_total, process_hist), level = "info", name = "stage_limited")]
async fn run_stage_limited(
    mut rx: mpsc::Receiver<Message>,
    limiter: Arc<Mutex<TokenBucket>>,
    mut shutdown_rx: broadcast::Receiver<()>,
    processed_total: IntCounter,
    dropped_total: IntCounter,
    process_hist: Histogram,
) -> anyhow::Result<()> {
    loop {
        select! {
            _ = shutdown_rx.recv() => break,
            maybe = rx.recv() => {
                match maybe { Some(msg) => {
                    // 限速，不允许则丢弃并告警（也可改为排队）
                    let mut tb = limiter.lock().await;
                    if !tb.allow(1) {
                        warn!(payload=%msg.payload, "stage limited: drop");
                        dropped_total.inc();
                        continue;
                    }
                    drop(tb);
                    let start = Instant::now();
                    match msg.priority {
                        Priority::High => info!(payload=%msg.payload, "stage: HIGH"),
                        Priority::Normal => info!(payload=%msg.payload, "stage: NORM"),
                    }
                    sleep(Duration::from_millis(25)).await;
                    processed_total.inc();
                    process_hist.observe(start.elapsed().as_secs_f64());
                }, None => break }
            }
        }
    }
    Ok(())
}

/// 指标心跳（示意）：每秒打印一次近似处理速率
async fn run_metrics_heartbeat(mut shutdown_rx: broadcast::Receiver<()>) -> anyhow::Result<()> {
    let mut tick = interval(Duration::from_secs(1));
    let mut n = 0u64;
    loop {
        select! {
            _ = shutdown_rx.recv() => break,
            _ = tick.tick() => { info!(processed=n, "metrics: heartbeat"); n = 0; }
            else => {}
        }
    }
    Ok(())
}

// 指标服务已抽取到 utils::metrics

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let _ = tracing_subscriber::fmt().with_env_filter("info").with_target(false).try_init();

    // 广播关闭（任务组取消）
    let (shutdown_tx, _shutdown_rx) = broadcast::channel::<()>(8);

    // 优先级邮箱
    let (tx_high, rx_high) = mpsc::channel::<Message>(32);
    let (tx_norm, rx_norm) = mpsc::channel::<Message>(128);
    let ingress = IngressActor::new(tx_high.clone(), tx_norm.clone());

    // CSP 入口与阶段
    let (tx_pipeline, rx_pipeline) = mpsc::channel::<Message>(128);
    let limiter = Arc::new(Mutex::new(TokenBucket::new(50, 100))); // 容量 50、每秒补充 100

    // Prometheus 指标注册
    let registry = Registry::new();
    let processed_total = IntCounter::with_opts(Opts::new("stage_processed_total", "总处理条数")).unwrap();
    let dropped_total = IntCounter::with_opts(Opts::new("stage_dropped_total", "限速丢弃条数")).unwrap();
    let inflight_gauge = IntGauge::with_opts(Opts::new("mailbox_inflight", "入口在途(估算)"));
    let process_hist = Histogram::with_opts(HistogramOpts::new("stage_process_seconds", "处理耗时(秒)")).unwrap();
    registry.register(Box::new(processed_total.clone())).unwrap();
    registry.register(Box::new(dropped_total.clone())).unwrap();
    registry.register(Box::new(process_hist.clone())).unwrap();
    if let Ok(g) = inflight_gauge { let _ = registry.register(Box::new(g)); }

    // 监督：合并器
    let mux_shutdown = shutdown_tx.subscribe();
    let rxh_cell = std::sync::Arc::new(std::sync::Mutex::new(Some(rx_high)));
    let rxn_cell = std::sync::Arc::new(std::sync::Mutex::new(Some(rx_norm)));
    let mux_handle = tokio::spawn(supervisor::supervise("mux", move || {
        let txp = tx_pipeline.clone();
        let sdr = mux_shutdown.resubscribe();
        let rxh_cell_cloned = rxh_cell.clone();
        let rxn_cell_cloned = rxn_cell.clone();
        async move {
            let rxh = rxh_cell_cloned.lock().unwrap().take();
            let rxn = rxn_cell_cloned.lock().unwrap().take();
            if let (Some(rxh), Some(rxn)) = (rxh, rxn) {
                run_mailbox_mux(rxh, rxn, txp, sdr).await
            } else {
                // 已经消费过接收端，后续重启时直接退出
                Ok(())
            }
        }
    }, shutdown_tx.subscribe()));

    // 监督：限速阶段
    let stage_shutdown = shutdown_tx.subscribe();
    let limiter_cloned = limiter.clone();
    let rxp_cell = std::sync::Arc::new(std::sync::Mutex::new(Some(rx_pipeline)));
    let stage_handle = tokio::spawn(supervisor::supervise("stage", move || {
        let sdr = stage_shutdown.resubscribe();
        let lim = limiter_cloned.clone();
        let processed = processed_total.clone();
        let dropped = dropped_total.clone();
        let hist = process_hist.clone();
        let rxp_cell_cloned = rxp_cell.clone();
        async move {
            let rxp = rxp_cell_cloned.lock().unwrap().take();
            if let Some(rxp) = rxp {
                run_stage_limited(rxp, lim, sdr, processed, dropped, hist).await
            } else {
                Ok(())
            }
        }
    }, shutdown_tx.subscribe()));

    // 指标心跳（示例）
    let hb_handle = tokio::spawn(run_metrics_heartbeat(shutdown_tx.subscribe()));

    // 启动 /metrics 服务
    let metrics_handle = tokio::spawn(metrics::serve_metrics(registry.clone(), "127.0.0.1:9898"));

    // 注入一些请求（混合优先级）
    for i in 0..120 {
        ingress.send(Message { priority: if i % 5 == 0 { Priority::High } else { Priority::Normal }, payload: format!("job-{i}") }).await;
    }

    // 运行一段时间，然后广播关闭
    sleep(Duration::from_secs(3)).await;
    let _ = shutdown_tx.send(());

    let _ = mux_handle.await;
    let _ = stage_handle.await;
    let _ = hb_handle.await;
    let _ = metrics_handle.await;

    Ok(())
}


