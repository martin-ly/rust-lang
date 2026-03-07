# 超时模式语义 (Timeout Pattern Semantics)

## 目录

- [超时模式语义 (Timeout Pattern Semantics)](#超时模式语义-timeout-pattern-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 超时分类与语义](#2-超时分类与语义)
    - [2.1 超时类型谱系](#21-超时类型谱系)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 自适应超时算法](#3-自适应超时算法)
    - [3.1 基于 EWMA 的自适应超时](#31-基于-ewma-的自适应超时)
    - [3.2 百分位自适应超时](#32-百分位自适应超时)
    - [3.3 协同自适应超时](#33-协同自适应超时)
  - [4. Rust 实现](#4-rust-实现)
    - [4.1 基础超时框架](#41-基础超时框架)
    - [4.2 自适应超时实现](#42-自适应超时实现)
    - [4.3 取消传播与协作式取消](#43-取消传播与协作式取消)
    - [4.4 多级超时策略](#44-多级超时策略)
    - [4.5 超时预算与传播](#45-超时预算与传播)
  - [5. 形式化验证](#5-形式化验证)
    - [5.1 超时正确性](#51-超时正确性)
    - [5.2 自适应收敛性](#52-自适应收敛性)
  - [6. 性能考量](#6-性能考量)
  - [7. 总结](#7-总结)

## 1. 引言

超时机制是分布式系统中保障服务质量、防止资源无限等待的基础组件。
本文档深入分析各种超时策略的形式化定义、实现原理及其在 Rust 异步运行时中的应用。

---

## 2. 超时分类与语义

### 2.1 超时类型谱系

```
超时类型层次:

┌──────────────────────────────────────────────────────────────────┐
│                      超时分类                                     │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │ 连接超时     │  │ 请求超时    │  │ 空闲超时    │              │
│  │ Connect     │  │ Request     │  │ Idle        │              │
│  │ Timeout     │  │ Timeout     │  │ Timeout     │              │
│  │             │  │             │  │             │              │
│  │ TCP握手完成 │  │ 完整响应    │  │ 无活动检测  │              │
│  │ TLS协商完成 │  │ 数据下载    │  │ 连接保活    │              │
│  └─────────────┘  └─────────────┘  └─────────────┘              │
│                                                                  │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │ 会话超时    │  │ 事务超时    │  │ 队列超时    │              │
│  │ Session     │  │ Transaction │  │ Queue       │              │
│  │ Timeout     │  │ Timeout     │  │ Timeout     │              │
│  │             │  │             │  │             │              │
│  │ 认证有效期  │  │ ACID保证    │  │ 排队期限    │              │
│  │ 会话生命周期│  │ 资源锁定    │  │ 背压控制    │              │
│  └─────────────┘  └─────────────┘  └─────────────┘              │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

### 2.2 形式化定义

```
超时形式化语义:

基本超时:
  Timeout(operation, deadline) =
    if time(operation) ≤ deadline then
      result(operation)
    else
      ⊥ (timeout error)

超时组合:
  Sequential(t₁, t₂): 顺序超时
    TotalTimeout = t₁ + t₂

  Parallel(t₁, t₂): 并行超时
    TotalTimeout = max(t₁, t₂)

  Nested(t_outer, t_inner): 嵌套超时
    EffectiveTimeout = min(t_outer, t_inner)

超时类型形式化:

连接超时 (Connect Timeout):
  □ (ConnectStarted → ◇ (Connected ∨ ConnectTimeout))
  Duration(ConnectStarted, Connected) ≤ T_connect

请求超时 (Request Timeout):
  □ (RequestSent → ◇ (ResponseReceived ∨ RequestTimeout))
  Duration(RequestSent, ResponseReceived) ≤ T_request

空闲超时 (Idle Timeout):
  □ (LastActivity > T_idle → Disconnect)
  ◇ (NoActivityFor(T_idle) → SessionExpired)
```

---

## 3. 自适应超时算法

### 3.1 基于 EWMA 的自适应超时

```
自适应超时公式:

响应时间估计:
  μ_t = α × observed_t + (1 - α) × μ_{t-1}

标准差估计:
  σ_t = √[β × (observed_t - μ_t)² + (1 - β) × σ²_{t-1}]

动态超时计算:
  timeout_t = μ_t + k × σ_t

其中:
  α, β: 平滑因子 (通常 0.1 - 0.3)
  k:    置信系数 (通常 2-4，对应 95-99% 置信区间)

边界限制:
  timeout_t ∈ [timeout_min, timeout_max]
```

### 3.2 百分位自适应超时

```
基于百分位的超时:

维护滑动窗口 W = {r₁, r₂, ..., rₙ} 的历史响应时间

计算 p-百分位:
  timeout_p = Percentile(W, p)

常用百分位选择:
  p50 (中位数):  适合低延迟要求
  p90:           平衡延迟与成功率
  p99:           高可靠性要求
  p99.9:         关键路径

指数加权百分位:
  对窗口内的样本应用时间衰减权重
  weight(rᵢ) = e^{-λ × (now - timestampᵢ)}

加权百分位计算:
  timeout = WeightedPercentile(W, weights, p)
```

### 3.3 协同自适应超时

```
系统级协同超时:

上游超时约束下游:
  T_downstream ≤ T_upstream - T_overhead

传播公式:
  T_effective(serviceᵢ) = min(
    T_configured(serviceᵢ),
    T_remaining - Σ_{j=i+1}^{n} T_min(serviceⱼ)
  )

其中:
  T_remaining = T_deadline - elapsed
  T_overhead = 网络延迟 + 序列化开销
```

---

## 4. Rust 实现

### 4.1 基础超时框架

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;
use tokio::time::{sleep, timeout as tokio_timeout, Instant, Sleep};
use pin_project::pin_project;

/// 超时错误类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimeoutError<E> {
    /// 操作超时
    Elapsed,
    /// 操作错误
    Inner(E),
}

impl<E: std::fmt::Display> std::fmt::Display for TimeoutError<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Elapsed => write!(f, "operation timed out"),
            Self::Inner(e) => write!(f, "{}", e),
        }
    }
}

impl<E: std::fmt::Debug + std::fmt::Display> std::error::Error for TimeoutError<E> {}

/// 超时包装器
#[pin_project]
pub struct Timeout<F> {
    #[pin]
    future: F,
    #[pin]
    deadline: Sleep,
}

impl<F: Future> Future for Timeout<F> {
    type Output = Result<F::Output, TimeoutError<()>>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();

        // 首先检查 futures 是否完成
        match this.future.poll(cx) {
            Poll::Ready(result) => Poll::Ready(Ok(result)),
            Poll::Pending => {
                // 检查是否超时
                match this.deadline.poll(cx) {
                    Poll::Ready(_) => Poll::Ready(Err(TimeoutError::Elapsed)),
                    Poll::Pending => Poll::Pending,
                }
            }
        }
    }
}

/// 为 Future 添加超时扩展 trait
pub trait TimeoutExt: Future + Sized {
    /// 设置超时时间
    fn timeout(self, duration: Duration) -> Timeout<Self> {
        Timeout {
            future: self,
            deadline: sleep(duration),
        }
    }

    /// 设置截止时间点
    fn timeout_at(self, deadline: Instant) -> Timeout<Self> {
        Timeout {
            future: self,
            deadline: sleep_until(deadline),
        }
    }
}

impl<F: Future> TimeoutExt for F {}

/// 使用 tokio::time::timeout 的简化版本
pub async fn with_timeout<F, T>(
    duration: Duration,
    future: F,
) -> Result<T, TimeoutError<()>>
where
    F: Future<Output = T>,
{
    match tokio_timeout(duration, future).await {
        Ok(result) => Ok(result),
        Err(_) => Err(TimeoutError::Elapsed),
    }
}
```

### 4.2 自适应超时实现

```rust
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};
use tokio::sync::RwLock;

/// 自适应超时计算器
pub struct AdaptiveTimeout {
    /// 历史响应时间窗口
    history: RwLock<VecDeque<Duration>>,
    /// 窗口大小
    window_size: usize,
    /// 平滑因子 α
    alpha: f64,
    /// 标准差系数 k
    std_dev_factor: f64,
    /// 当前 EWMA 估计
    ewma: AtomicU64, // 存储为微秒
    /// 当前方差估计
    variance: AtomicU64,
    /// 最小/最大超时边界
    min_timeout: Duration,
    max_timeout: Duration,
}

impl AdaptiveTimeout {
    pub fn new(
        window_size: usize,
        alpha: f64,
        std_dev_factor: f64,
        min_timeout: Duration,
        max_timeout: Duration,
    ) -> Self {
        Self {
            history: RwLock::new(VecDeque::with_capacity(window_size)),
            window_size,
            alpha,
            std_dev_factor,
            ewma: AtomicU64::new(min_timeout.as_micros() as u64),
            variance: AtomicU64::new(0),
            min_timeout,
            max_timeout,
        }
    }

    /// 记录观测到的响应时间
    pub async fn record(&self, duration: Duration) {
        // 更新历史窗口
        {
            let mut history = self.history.write().await;
            history.push_back(duration);
            if history.len() > self.window_size {
                history.pop_front();
            }
        }

        // 更新 EWMA
        let observed = duration.as_micros() as f64;
        let old_ewma = self.ewma.load(Ordering::Relaxed) as f64;
        let new_ewma = self.alpha * observed + (1.0 - self.alpha) * old_ewma;
        self.ewma.store(new_ewma as u64, Ordering::Relaxed);

        // 更新方差 (使用 Welford 算法)
        let diff = observed - new_ewma;
        let old_variance = self.variance.load(Ordering::Relaxed) as f64;
        let new_variance = (1.0 - self.alpha) * old_variance + self.alpha * diff * diff;
        self.variance.store(new_variance as u64, Ordering::Relaxed);
    }

    /// 计算当前推荐的超时时间
    pub fn current_timeout(&self) -> Duration {
        let ewma = self.ewma.load(Ordering::Relaxed) as f64;
        let variance = self.variance.load(Ordering::Relaxed) as f64;
        let std_dev = variance.sqrt();

        // timeout = EWMA + k * σ
        let timeout_micros = ewma + self.std_dev_factor * std_dev;
        let timeout = Duration::from_micros(timeout_micros as u64);

        // 应用边界限制
        timeout.clamp(self.min_timeout, self.max_timeout)
    }

    /// 计算百分位超时
    pub async fn percentile_timeout(&self, percentile: f64) -> Option<Duration> {
        let history = self.history.read().await;
        if history.is_empty() {
            return None;
        }

        let mut sorted: Vec<_> = history.iter().cloned().collect();
        sorted.sort();

        let idx = ((sorted.len() as f64) * percentile / 100.0) as usize;
        sorted.get(idx.min(sorted.len() - 1)).cloned()
    }

    /// 执行带自适应超时的操作
    pub async fn execute<F, Fut, T>(&self, operation: F) -> Result<T, TimeoutError<()>>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = T>,
    {
        let timeout = self.current_timeout();
        let start = Instant::now();

        let result = match tokio_timeout(timeout, operation()).await {
            Ok(r) => Ok(r),
            Err(_) => Err(TimeoutError::Elapsed),
        };

        // 记录实际耗时
        let elapsed = start.elapsed();
        self.record(elapsed).await;

        result
    }
}

/// 分层自适应超时
pub struct TieredAdaptiveTimeout {
    /// 连接超时（通常较短）
    connect_timeout: AdaptiveTimeout,
    /// 请求超时（通常较长）
    request_timeout: AdaptiveTimeout,
    /// 空闲超时
    idle_timeout: Duration,
    /// 最后活动时间
    last_activity: RwLock<Instant>,
}

impl TieredAdaptiveTimeout {
    pub fn new(
        connect_config: (Duration, Duration),
        request_config: (Duration, Duration),
        idle_timeout: Duration,
    ) -> Self {
        Self {
            connect_timeout: AdaptiveTimeout::new(
                100, 0.2, 3.0, connect_config.0, connect_config.1,
            ),
            request_timeout: AdaptiveTimeout::new(
                1000, 0.1, 4.0, request_config.0, request_config.1,
            ),
            idle_timeout,
            last_activity: RwLock::new(Instant::now()),
        }
    }

    /// 检查空闲超时
    pub async fn check_idle(&self) -> bool {
        let last = *self.last_activity.read().await;
        Instant::now().duration_since(last) < self.idle_timeout
    }

    /// 更新活动时间
    pub async fn touch(&self) {
        *self.last_activity.write().await = Instant::now();
    }
}
```

### 4.3 取消传播与协作式取消

```rust
use tokio::select;
use tokio::sync::oneshot;
use std::sync::Arc;
use tokio_util::sync::CancellationToken;

/// 可取消的操作包装器
#[pin_project]
pub struct Cancellable<F> {
    #[pin]
    future: F,
    token: CancellationToken,
}

impl<F: Future> Future for Cancellable<F> {
    type Output = Option<F::Output>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();

        // 检查取消令牌
        if this.token.is_cancelled() {
            return Poll::Ready(None);
        }

        this.future.poll(cx).map(Some)
    }
}

/// 超时与取消传播管理器
pub struct TimeoutManager {
    cancellation_token: CancellationToken,
    timeout_handles: Arc<RwLock<Vec<tokio::task::JoinHandle<()>>>>,
}

impl TimeoutManager {
    pub fn new() -> Self {
        Self {
            cancellation_token: CancellationToken::new(),
            timeout_handles: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 创建子令牌
    pub fn child_token(&self) -> CancellationToken {
        self.cancellation_token.child_token()
    }

    /// 执行带超时和取消的操作
    pub async fn execute_with_cancellation<F, Fut, T>(
        &self,
        operation: F,
        timeout: Duration,
    ) -> Result<T, TimeoutError<()>>
    where
        F: FnOnce(CancellationToken) -> Fut,
        Fut: Future<Output = T>,
    {
        let token = self.child_token();
        let token_clone = token.clone();

        select! {
            result = operation(token_clone) => Ok(result),
            _ = tokio_timeout(timeout, token.cancelled()) => {
                token.cancel();
                Err(TimeoutError::Elapsed)
            }
        }
    }

    /// 级联取消所有子操作
    pub fn cancel_all(&self) {
        self.cancellation_token.cancel();
    }
}

/// 协作式取消的 HTTP 客户端示例
use reqwest::Client;

pub struct CancellableHttpClient {
    client: Client,
    timeout_manager: TimeoutManager,
}

impl CancellableHttpClient {
    pub async fn request_with_timeout(
        &self,
        method: reqwest::Method,
        url: &str,
        timeout: Duration,
    ) -> Result<reqwest::Response, TimeoutError<reqwest::Error>> {
        let token = self.timeout_manager.child_token();

        let request = self.client
            .request(method, url)
            .timeout(timeout) // 设置请求级超时
            .build()
            .map_err(TimeoutError::Inner)?;

        let client = self.client.clone();

        match tokio_timeout(timeout, async {
            let resp = client.execute(request).await?;

            // 检查取消令牌
            if token.is_cancelled() {
                return Err(reqwest::Error::from(
                    std::io::Error::new(
                        std::io::ErrorKind::Interrupted,
                        "Operation cancelled"
                    )
                ));
            }

            Ok(resp)
        }).await {
            Ok(Ok(response)) => Ok(response),
            Ok(Err(e)) => Err(TimeoutError::Inner(e)),
            Err(_) => {
                token.cancel();
                Err(TimeoutError::Elapsed)
            }
        }
    }
}
```

### 4.4 多级超时策略

```rust
/// 分层超时配置
#[derive(Debug, Clone)]
pub struct TimeoutHierarchy {
    /// 总超时（硬限制）
    pub total_timeout: Duration,
    /// 连接超时
    pub connect_timeout: Duration,
    /// 请求超时
    pub request_timeout: Duration,
    /// 读取超时（每个数据包）
    pub read_timeout: Duration,
    /// 写入超时
    pub write_timeout: Duration,
}

/// 分层超时执行器
pub struct HierarchicalTimeoutExecutor;

impl HierarchicalTimeoutExecutor {
    /// 执行带分层超时的操作
    pub async fn execute<F, Fut, T>(
        hierarchy: &TimeoutHierarchy,
        operation: F,
    ) -> Result<T, TimeoutError<()>>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = T>,
    {
        let start = Instant::now();
        let deadline = start + hierarchy.total_timeout;

        // 第一层：连接超时
        let connect_result = tokio_timeout(
            hierarchy.connect_timeout,
            Self::phase_connect()
        ).await;

        if connect_result.is_err() {
            return Err(TimeoutError::Elapsed);
        }

        let remaining = deadline.saturating_duration_since(Instant::now());
        let request_deadline = remaining.min(hierarchy.request_timeout);

        // 第二层：请求超时
        let request_result = tokio_timeout(
            request_deadline,
            operation()
        ).await;

        match request_result {
            Ok(result) => Ok(result),
            Err(_) => Err(TimeoutError::Elapsed),
        }
    }

    async fn phase_connect() {
        // 连接阶段逻辑
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
}

/// 流式超时（适用于大文件下载）
#[pin_project]
pub struct StreamWithTimeout<S> {
    #[pin]
    stream: S,
    item_timeout: Duration,
    last_item_time: RwLock<Instant>,
}

impl<S: Stream> Stream for StreamWithTimeout<S> {
    type Item = Result<S::Item, TimeoutError<()>>;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.project();

        // 检查单项超时
        let last = *this.last_item_time.try_read().unwrap_or_else(|_| return Poll::Pending);
        if Instant::now().duration_since(last) > *this.item_timeout {
            return Poll::Ready(Some(Err(TimeoutError::Elapsed)));
        }

        match this.stream.poll_next(cx) {
            Poll::Ready(Some(item)) => {
                // 更新最后接收时间
                if let Ok(mut guard) = this.last_item_time.try_write() {
                    *guard = Instant::now();
                }
                Poll::Ready(Some(Ok(item)))
            }
            Poll::Ready(None) => Poll::Ready(None),
            Poll::Pending => Poll::Pending,
        }
    }
}
```

### 4.5 超时预算与传播

```rust
/// 超时预算上下文
#[derive(Debug, Clone, Copy)]
pub struct TimeoutBudget {
    /// 截止时间
    deadline: Instant,
    /// 剩余预算
    remaining: Duration,
    /// 已用预算
    used: Duration,
}

impl TimeoutBudget {
    /// 创建新的预算
    pub fn new(total: Duration) -> Self {
        let now = Instant::now();
        Self {
            deadline: now + total,
            remaining: total,
            used: Duration::ZERO,
        }
    }

    /// 分配子预算
    pub fn allocate(&mut self, amount: Duration) -> Option<Duration> {
        if amount > self.remaining {
            return None;
        }
        self.remaining -= amount;
        self.used += amount;
        Some(amount)
    }

    /// 计算可分配的最大预算
    pub fn max_allocation(&self, safety_margin: f64) -> Duration {
        let safety = Duration::from_millis(
            (self.remaining.as_millis() as f64 * (1.0 - safety_margin)) as u64
        );
        safety
    }

    /// 检查是否还有预算
    pub fn has_budget(&self) -> bool {
        self.remaining > Duration::ZERO && Instant::now() < self.deadline
    }

    /// 获取实际剩余时间
    pub fn actual_remaining(&self) -> Duration {
        self.deadline.saturating_duration_since(Instant::now())
    }
}

/// 带预算的传播执行器
pub struct BudgetedExecutor {
    budget: TimeoutBudget,
}

impl BudgetedExecutor {
    pub fn new(budget: TimeoutBudget) -> Self {
        Self { budget }
    }

    /// 执行子操作，自动分配预算
    pub async fn execute_child<F, Fut, T>(
        &mut self,
        estimated_cost: Duration,
        child_operation: F,
    ) -> Result<T, TimeoutError<()>>
    where
        F: FnOnce(Duration) -> Fut,
        Fut: Future<Output = T>,
    {
        // 分配预算（预留安全边际）
        let allocated = self.budget.max_allocation(0.9)
            .min(estimated_cost * 2); // 允许一定超支

        if allocated.is_zero() {
            return Err(TimeoutError::Elapsed);
        }

        let actual_remaining = self.budget.actual_remaining();
        let effective_timeout = allocated.min(actual_remaining);

        let start = Instant::now();
        let result = tokio_timeout(effective_timeout, child_operation(effective_timeout)).await;
        let elapsed = start.elapsed();

        // 更新预算
        if elapsed < allocated {
            // 返还未使用的预算
            self.budget.remaining += allocated - elapsed;
        }

        match result {
            Ok(r) => Ok(r),
            Err(_) => Err(TimeoutError::Elapsed),
        }
    }
}

/// 传播性超时（跨服务调用）
#[derive(Debug, Clone)]
pub struct PropagatedTimeout {
    budget: TimeoutBudget,
    trace_id: String,
}

impl PropagatedTimeout {
    /// 序列化为 HTTP 头
    pub fn to_headers(&self) -> Vec<(String, String)> {
        vec![
            ("X-Timeout-Deadline".to_string(),
             self.budget.deadline.elapsed().as_millis().to_string()),
            ("X-Timeout-Remaining".to_string(),
             self.budget.remaining.as_millis().to_string()),
            ("X-Trace-ID".to_string(), self.trace_id.clone()),
        ]
    }

    /// 从 HTTP 头解析
    pub fn from_headers(headers: &reqwest::header::HeaderMap) -> Option<Self> {
        let remaining = headers.get("X-Timeout-Remaining")?
            .to_str().ok()?
            .parse::<u64>().ok()?;

        Some(Self {
            budget: TimeoutBudget::new(Duration::from_millis(remaining)),
            trace_id: headers.get("X-Trace-ID")?
                .to_str().ok()?.to_string(),
        })
    }
}
```

---

## 5. 形式化验证

### 5.1 超时正确性

```
超时正确性属性:

1. 及时性 (Timeliness):
   □ (TimeoutSet(deadline) → ◇ (Complete ∨ Timeout) ∧ Time ≤ deadline + ε)

2. 完整性 (Completeness):
   □ (OperationCompletes → ◇ ResultDelivered)

3. 一致性 (Consistency):
   □ (TimeoutOccurs → ¬ResultDelivered) ∧
   □ (ResultDelivered → ¬TimeoutOccurs)

4. 单调性 (Monotonicity):
   deadline₁ < deadline₂ → P(Timeout₁) ≥ P(Timeout₂)
```

### 5.2 自适应收敛性

```
自适应超时收敛性:

设真实响应时间分布为 R ~ N(μ, σ²)

EWMA 收敛:
  lim_{t→∞} E[μ̂_t] = μ
  lim_{t→∞} Var[μ̂_t] = α/(2-α) × σ²

超时覆盖概率:
  P(observed ≤ timeout_t) = Φ(k)

  其中 Φ 是标准正态 CDF，k 为标准差系数

  k=2: 约 97.7% 覆盖率
  k=3: 约 99.9% 覆盖率
  k=4: 约 99.997% 覆盖率

收敛速度:
  收敛到稳态的迭代次数 ≈ 4/α
  α=0.1: 约 40 次迭代
  α=0.2: 约 20 次迭代
  α=0.3: 约 13 次迭代
```

---

## 6. 性能考量

```
超时机制性能分析:

1. 定时器精度:
   - tokio::time 精度: 约 1ms
   - 操作系统定时器: 通常 1-10ms
   - 高精度需求: 使用 async-io 或 polling

2. 内存开销:
   - 每个 pending 超时任务: ~100-200 bytes
   - 大量并发超时: 使用时间轮优化

3. CPU 开销:
   - 超时检查: O(1) 每 tick
   - 自适应计算: 每请求 O(1)

优化策略:

1. 批量超时管理:
   struct TimeoutWheel {
       buckets: Vec<Vec<TimeoutHandle>>,
       tick_duration: Duration,
   }

2. 惰性超时检查:
   - 仅在 poll 时检查超时
   - 避免主动扫描

3. 零拷贝传播:
   - 使用 Arc<TimeoutBudget> 共享
   - 减少克隆开销
```

---

## 7. 总结

| 超时类型 | 适用场景 | 推荐值 |
|----------|----------|--------|
| Connect | 建立连接 | 1-5s |
| Request | 完整请求 | 5-30s |
| Read | 数据流传输 | 1-5s per chunk |
| Idle | 连接保活 | 30-300s |

核心公式:

$$
\text{timeout}_{adaptive} = \mu_{ewma} + k \cdot \sigma_{ewma}
$$

$$
\mu_t = \alpha \cdot x_t + (1-\alpha) \cdot \mu_{t-1}
$$

$$
T_{effective} = \min(T_{configured}, T_{deadline} - T_{elapsed} - T_{overhead})
$$
