use futures::future::{AbortHandle, Abortable};
use std::future::Future;
use std::sync::Arc;
use std::time::Duration;

pub async fn retry_with_backoff<F, Fut, T, E>(
    mut make_fut: F,
    max_attempts: u32,
    start_delay: Duration,
) -> Result<T, E>
where
    F: FnMut(u32) -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    let mut delay = start_delay;
    let mut attempt = 0u32;
    loop {
        attempt += 1;
        match make_fut(attempt).await {
            Ok(v) => return Ok(v),
            Err(e) if attempt >= max_attempts => return Err(e),
            Err(_) => {
                tokio::time::sleep(delay).await;
                delay = delay.saturating_mul(2);
            }
        }
    }
}

pub struct CancelScope {
    handle: AbortHandle,
}

impl CancelScope {
    pub fn new() -> (Self, futures::future::AbortRegistration) {
        let (h, reg) = AbortHandle::new_pair();
        (Self { handle: h }, reg)
    }
    pub fn cancel(&self) {
        self.handle.abort();
    }
}

pub async fn with_timeout<T, F>(dur: Duration, fut: F) -> Option<T>
where
    F: Future<Output = T>,
{
    tokio::time::timeout(dur, fut).await.ok()
}

#[derive(Clone)]
pub struct SemaphoreLimiter {
    inner: Arc<tokio::sync::Semaphore>,
}

impl SemaphoreLimiter {
    pub fn new(concurrency: usize) -> Self {
        Self {
            inner: Arc::new(tokio::sync::Semaphore::new(concurrency)),
        }
    }
    pub async fn run<F, T>(&self, fut: F) -> T
    where
        F: Future<Output = T>,
    {
        let permit = self
            .inner
            .clone()
            .acquire_owned()
            .await
            .expect("acquire permit");
        let res = fut.await;
        drop(permit);
        res
    }
}

pub async fn abortable<F, T>(
    reg: futures::future::AbortRegistration,
    fut: F,
) -> Result<T, futures::future::Aborted>
where
    F: Future<Output = T>,
{
    Abortable::new(fut, reg).await
}

pub mod circuit_breaker;

pub mod supervisor {
    use tokio::sync::broadcast;
    use tokio::time::{sleep, Duration};
    use tracing::{info, warn};

    pub async fn supervise<F, Fut>(name: &'static str, mut factory: F, mut shutdown_rx: broadcast::Receiver<()>)
    where
        F: FnMut() -> Fut + Send + 'static,
        Fut: std::future::Future<Output = anyhow::Result<()>> + Send,
    {
        let mut backoff_ms = 200u64;
        let max_backoff_ms = 10_000u64;
        loop {
            tokio::select! {
                _ = shutdown_rx.recv() => { info!(component=name, "supervisor: shutdown received"); break; }
                res = factory() => {
                    match res {
                        Ok(()) => { info!(component=name, "component exited gracefully"); break; }
                        Err(e) => { warn!(component=name, error=%e, "component failed; will restart"); sleep(Duration::from_millis(backoff_ms)).await; backoff_ms = (backoff_ms.saturating_mul(2)).min(max_backoff_ms); }
                    }
                }
            }
        }
    }
}

pub mod metrics {
    use axum::{routing::get, Router};
    use prometheus::{Encoder, Registry, TextEncoder};

    pub async fn serve_metrics(registry: Registry, bind: &str) -> anyhow::Result<()> {
        async fn handle_metrics(registry: Registry) -> axum::http::Response<String> {
            let encoder = TextEncoder::new();
            let metric_families = registry.gather();
            let mut buffer = Vec::new();
            let _ = encoder.encode(&metric_families, &mut buffer);
            let body = String::from_utf8_lossy(&buffer).to_string();
            axum::http::Response::builder().status(200).header(axum::http::header::CONTENT_TYPE, encoder.format_type()).body(body).unwrap()
        }
        let app = Router::new().route("/metrics", get({ let reg = registry.clone(); move || handle_metrics(reg.clone()) }));
        let listener = tokio::net::TcpListener::bind(bind).await.map_err(|e| anyhow::anyhow!(e))?;
        axum::serve(listener, app.into_make_service()).await.map_err(|e| anyhow::anyhow!(e))
    }
}

/// 统一执行助手：并发控制 + 超时 + 重试
#[derive(Clone)]
pub struct ExecHelper {
    limiter: SemaphoreLimiter,
    breaker: Option<circuit_breaker::CircuitBreaker>,
}

impl ExecHelper {
    pub fn new(concurrency: usize) -> Self {
        Self { limiter: SemaphoreLimiter::new(concurrency), breaker: None }
    }

    pub fn with_breaker(mut self, breaker: circuit_breaker::CircuitBreaker) -> Self {
        self.breaker = Some(breaker);
        self
    }

    pub async fn run_with_policies<F, Fut, T, E>(
        &self,
        mut make_fut: F,
        max_attempts: u32,
        start_delay: Duration,
        timeout: Duration,
    ) -> Result<Option<T>, E>
    where
        F: FnMut(u32) -> Fut + Send + 'static,
        Fut: Future<Output = Result<T, E>> + Send + 'static,
        T: Send + 'static,
        E: Send + 'static,
    {
        let fut = async move {
            // 重试链路（带自定义可重试判定支持：通过闭包内部自行决定错误）
            retry_with_backoff(&mut make_fut, max_attempts, start_delay).await
        };

        // 统一为一个 Boxed Future，避免 async block 类型不一致
        use std::pin::Pin;
        use std::future::Future as StdFuture;
        let fut: Pin<Box<dyn StdFuture<Output = Result<T, E>> + Send>> = if let Some(breaker) = &self.breaker {
            let b = breaker.clone();
            Box::pin(async move { b.run(fut).await })
        } else {
            Box::pin(fut)
        };

        let run = self.limiter.run(async move { with_timeout(timeout, fut).await });
        match run.await {
            Some(Ok(v)) => Ok(Some(v)),
            Some(Err(e)) => Err(e),
            None => Ok(None),
        }
    }

    /// 增强版：支持可重试判定与整体截止时间（deadline）
    pub async fn run_with_decider_and_deadline<F, Fut, T, E, D>(
        &self,
        mut make_fut: F,
        mut is_retryable: D,
        max_attempts: u32,
        start_delay: Duration,
        deadline: std::time::Instant,
    ) -> Result<Option<T>, E>
    where
        F: FnMut(u32) -> Fut + Send + 'static,
        Fut: Future<Output = Result<T, E>> + Send + 'static,
        D: FnMut(&E) -> bool + Send + 'static,
        T: Send + 'static,
        E: Send + 'static,
    {
        // 自定义重试：基于判定函数决定是否继续重试
        let fut = async move {
            let mut attempt = 0u32;
            let mut delay = start_delay;
            loop {
                attempt += 1;
                match make_fut(attempt).await {
                    Ok(v) => break Ok(v),
                    Err(e) => {
                        if attempt >= max_attempts || !is_retryable(&e) {
                            break Err(e);
                        }
                        tokio::time::sleep(delay).await;
                        delay = delay.saturating_mul(2);
                    }
                }
            }
        };

        use std::pin::Pin;
        use std::future::Future as StdFuture;
        let fut: Pin<Box<dyn StdFuture<Output = Result<T, E>> + Send>> = if let Some(breaker) = &self.breaker {
            let b = breaker.clone();
            Box::pin(async move { b.run(fut).await })
        } else {
            Box::pin(fut)
        };

        // 将截止时间转为剩余超时，循环检查
        loop {
            let now = std::time::Instant::now();
            if now >= deadline {
                return Ok(None);
            }
            let remain = deadline - now;
            let res = self.limiter.run(async { tokio::time::timeout(remain, fut).await }).await;
            match res {
                Ok(Ok(v)) => return Ok(Some(v)),
                Ok(Err(e)) => return Err(e),
                Err(_) => return Ok(None), // reach deadline in this slice
            }
        }
    }
}

/// 可配置策略构建器：并发/重试/退避/超时或截止/熔断/限速
#[derive(Clone)]
pub struct ExecStrategyBuilder {
    concurrency: usize,
    max_attempts: u32,
    start_delay: Duration,
    timeout: Option<Duration>,
    deadline: Option<std::time::Instant>,
    breaker: Option<circuit_breaker::CircuitBreaker>,
    token_bucket: Option<SimpleTokenBucket>,
}

impl Default for ExecStrategyBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ExecStrategyBuilder {
    pub fn new() -> Self {
        Self {
            concurrency: 4,
            max_attempts: 3,
            start_delay: Duration::from_millis(100),
            timeout: Some(Duration::from_secs(2)),
            deadline: None,
            breaker: None,
            token_bucket: None,
        }
    }
    pub fn concurrency(mut self, c: usize) -> Self { self.concurrency = c; self }
    pub fn attempts(mut self, n: u32) -> Self { self.max_attempts = n; self }
    pub fn start_delay(mut self, d: Duration) -> Self { self.start_delay = d; self }
    pub fn timeout(mut self, d: Duration) -> Self { self.timeout = Some(d); self.deadline = None; self }
    pub fn deadline(mut self, t: std::time::Instant) -> Self { self.deadline = Some(t); self.timeout = None; self }
    pub fn breaker(mut self, b: circuit_breaker::CircuitBreaker) -> Self { self.breaker = Some(b); self }
    pub fn token_bucket(mut self, b: SimpleTokenBucket) -> Self { self.token_bucket = Some(b); self }

    pub fn build(self) -> ExecStrategyRunner {
        ExecStrategyRunner {
            helper: ExecHelper::new(self.concurrency).with_breaker_opt(self.breaker.clone()),
            max_attempts: self.max_attempts,
            start_delay: self.start_delay,
            timeout: self.timeout,
            deadline: self.deadline,
            token_bucket: self.token_bucket,
        }
    }

    /// 从 JSON 配置构建（支持高级选项）
    pub fn from_config(cfg: &StrategyConfig) -> Self {
        let mut b = ExecStrategyBuilder::new()
            .concurrency(cfg.concurrency as usize)
            .attempts(cfg.max_attempts)
            .start_delay(Duration::from_millis(cfg.start_delay_ms));
        
        if let Some(to_ms) = cfg.timeout_ms { 
            b = b.timeout(Duration::from_millis(to_ms)); 
        }
        if let Some(dl_ms) = cfg.deadline_ms {
            b = b.deadline(std::time::Instant::now() + Duration::from_millis(dl_ms));
        }
        if let Some(tb) = cfg.token_bucket.as_ref() {
            b = b.token_bucket(SimpleTokenBucket::new(tb.capacity, tb.refill_per_sec));
        }
        
        // 高级熔断器配置
        if cfg.enable_breaker.unwrap_or(false) {
            let threshold = cfg.breaker_threshold.unwrap_or(5) as u64;
            let window = Duration::from_millis(cfg.breaker_window_ms.unwrap_or(30000));
            let half_open_max = cfg.breaker_half_open_max_calls.unwrap_or(3);
            b = b.breaker(circuit_breaker::CircuitBreaker::new_with_half_open_max(threshold, window, half_open_max));
        }
        
        b
    }
}

#[derive(Clone)]
pub struct ExecStrategyRunner {
    helper: ExecHelper,
    max_attempts: u32,
    start_delay: Duration,
    timeout: Option<Duration>,
    deadline: Option<std::time::Instant>,
    token_bucket: Option<SimpleTokenBucket>,
}

impl ExecHelper {
    fn with_breaker_opt(mut self, breaker: Option<circuit_breaker::CircuitBreaker>) -> Self {
        self.breaker = breaker;
        self
    }
}

impl ExecStrategyRunner {
    /// 运行操作：可选择传入可重试判定
    pub async fn run<F, Fut, T, E, D>(
        &self,
        make_fut: F,
        is_retryable: Option<D>,
    ) -> Result<Option<T>, E>
    where
        F: FnMut(u32) -> Fut + Send + 'static,
        Fut: Future<Output = Result<T, E>> + Send + 'static,
        D: FnMut(&E) -> bool + Send + 'static,
        T: Send + 'static,
        E: Send + 'static,
    {
        if let Some(tb) = &self.token_bucket {
            tb.acquire(1).await;
        }
        match (self.timeout, self.deadline, is_retryable) {
            (Some(to), _, None) => self.helper.run_with_policies(make_fut, self.max_attempts, self.start_delay, to).await,
            (None, Some(dl), None) => self.helper.run_with_decider_and_deadline(make_fut, |_e: &E| true, self.max_attempts, self.start_delay, dl).await,
            (Some(to), _, Some(decider)) => {
                // 使用 deadline 近似：多次切片在 to 内
                let dl = std::time::Instant::now() + to;
                // 将 decider 包装在 Mutex 中以便可变借用
                let d = std::sync::Mutex::new(decider);
                self.helper.run_with_decider_and_deadline(make_fut, move |e| (d.lock().unwrap())(e), self.max_attempts, self.start_delay, dl).await
            }
            (None, Some(dl), Some(decider)) => self.helper.run_with_decider_and_deadline(make_fut, decider, self.max_attempts, self.start_delay, dl).await,
            _ => unreachable!("必须设置 timeout 或 deadline 其一"),
        }
    }
}
/// 简单令牌桶限速器（线程安全）
#[derive(Clone)]
pub struct SimpleTokenBucket {
    inner: Arc<parking_lot::Mutex<BucketInner>>,
}

struct BucketInner {
    capacity: f64,
    tokens: f64,
    refill_per_sec: f64,
    last: std::time::Instant,
}

impl SimpleTokenBucket {
    pub fn new(capacity: u32, refill_per_sec: u32) -> Self {
        let cap = capacity as f64;
        let rate = refill_per_sec as f64;
        Self {
            inner: Arc::new(parking_lot::Mutex::new(BucketInner {
                capacity: cap,
                tokens: cap,
                refill_per_sec: rate,
                last: std::time::Instant::now(),
            })),
        }
    }

    pub async fn acquire(&self, permits: u32) {
        let need = permits as f64;
        loop {
            // 计算是否需要等待；将锁的生命周期限制在此块内，避免跨 await
            let maybe_sleep: Option<Duration> = {
                let mut g = self.inner.lock();
                let now = std::time::Instant::now();
                let elapsed = now.duration_since(g.last).as_secs_f64();
                if elapsed > 0.0 {
                    g.tokens = (g.tokens + g.refill_per_sec * elapsed).min(g.capacity);
                    g.last = now;
                }
                if g.tokens >= need {
                    g.tokens -= need;
                    None
                } else {
                    let deficit = need - g.tokens;
                    let secs = deficit / g.refill_per_sec;
                    Some(Duration::from_secs_f64(secs.max(0.001)))
                }
            };
            if let Some(d) = maybe_sleep {
                tokio::time::sleep(d).await;
            } else {
                break;
            }
        }
    }
}

// 配置结构（用于从 JSON/TOML 读取）
#[derive(Debug, serde::Deserialize)]
pub struct StrategyConfig {
    pub concurrency: u32,
    pub max_attempts: u32,
    pub start_delay_ms: u64,
    pub timeout_ms: Option<u64>,
    pub deadline_ms: Option<u64>,
    pub enable_breaker: Option<bool>,
    pub token_bucket: Option<TokenBucketConfig>,
    // 新增高级选项
    pub backoff_multiplier: Option<f64>,
    pub max_backoff_ms: Option<u64>,
    pub jitter: Option<bool>,
    pub breaker_threshold: Option<u32>,
    pub breaker_window_ms: Option<u64>,
    pub breaker_half_open_max_calls: Option<u32>,
}

#[derive(Debug, serde::Deserialize)]
pub struct TokenBucketConfig {
    pub capacity: u32,
    pub refill_per_sec: u32,
}
