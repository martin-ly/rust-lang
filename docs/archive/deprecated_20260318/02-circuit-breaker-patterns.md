# 断路器模式语义 (Circuit Breaker Pattern Semantics)

## 目录

- [断路器模式语义 (Circuit Breaker Pattern Semantics)](#断路器模式语义-circuit-breaker-pattern-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 断路器状态机](#2-断路器状态机)
    - [2.1 三态模型](#21-三态模型)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 数学模型](#3-数学模型)
    - [3.1 失败率计算](#31-失败率计算)
    - [3.2 恢复时间计算](#32-恢复时间计算)
    - [3.3 令牌桶限流（半开状态）](#33-令牌桶限流半开状态)
  - [4. Rust 实现](#4-rust-实现)
    - [4.1 核心状态机实现](#41-核心状态机实现)
    - [4.2 异步适配器与集成](#42-异步适配器与集成)
    - [4.3 事件通知与可观测性](#43-事件通知与可观测性)
  - [5. 形式化验证](#5-形式化验证)
    - [5.1 安全性与活性](#51-安全性与活性)
    - [5.2 时序逻辑规格](#52-时序逻辑规格)
  - [6. 高级模式](#6-高级模式)
    - [6.1 多级断路器](#61-多级断路器)
    - [6.2 预测性断路器](#62-预测性断路器)
  - [7. 性能考量](#7-性能考量)
  - [8. 总结](#8-总结)

## 1. 引言

断路器模式是分布式系统中实现故障隔离的核心机制。
本文档深入分析断路器的形式化语义、状态转换机制及其在 Rust 中的异步实现。

---

## 2. 断路器状态机

### 2.1 三态模型

```
断路器状态转换图:

                    ┌─────────────┐
                    │   CLOSED    │ ← 正常状态，请求通过
                    │  (关闭)     │
                    └──────┬──────┘
                           │ 失败计数超过阈值
                           ▼
              ┌────────────────────────┐
              │   ┌───────────────┐    │
              │   │  FAILURE      │    │
              │   │  COUNT++      │    │
              │   └───────┬───────┘    │
              │           │ ≥ threshold│
              └───────────┼────────────┘
                          ▼
                    ┌─────────────┐
         ┌───────→ │    OPEN     │ ← 熔断状态，快速失败
         │         │   (打开)    │
         │         └──────┬──────┘
         │                │
         │                │ 超时时间到
         │                ▼
         │         ┌─────────────┐
         │         │  HALF-OPEN  │ ← 探测状态，限量放行
         │         │  (半开)     │
         │         └──────┬──────┘
         │                │
         │                │ 探测成功
         └────────────────┘
                探测失败
```

### 2.2 形式化定义

```
断路器形式化语义:

状态集合: S = {Closed, Open, HalfOpen}
输入符号: Σ = {Request, Success, Failure, Timeout}
输出符号: Γ = {Pass, Reject, Probe}

状态转换函数 δ: S × Σ → S × Γ

δ(Closed, Request)  = (Closed, Pass)
δ(Closed, Success)  = (Closed, ε)
δ(Closed, Failure)  = (s', ε)  其中:
                        s' = Open   if count_failures ≥ threshold
                        s' = Closed otherwise

δ(Open, Request)    = (Open, Reject)
δ(Open, Timeout)    = (HalfOpen, ε)

δ(HalfOpen, Request) = (HalfOpen, Probe)  限量放行
δ(HalfOpen, Success) = (Closed, ε)        全部成功则关闭
δ(HalfOpen, Failure) = (Open, ε)          任一失败则重新打开

状态不变式:
  □ (Open → ◇ Timeout → HalfOpen)         打开状态最终会超时
  □ (HalfOpen ∧ Success* → Closed)        半开状态成功则关闭
  □ (HalfOpen ∧ Failure → Open)           半开状态失败则重新打开
```

---

## 3. 数学模型

### 3.1 失败率计算

```
指数加权移动平均 (EWMA):

failure_rate_t = α × I{request_failed} + (1 - α) × failure_rate_{t-1}

其中:
  α ∈ (0, 1)  为平滑因子 (通常 0.1 - 0.3)
  I{·} 为指示函数

断路器打开条件:
  OpenCircuit ⇔ failure_rate_t > threshold_failure
            ∨  consecutive_failures ≥ max_consecutive
```

### 3.2 恢复时间计算

```
指数退避恢复:

timeout_open = base_timeout × β^n

其中:
  base_timeout: 基础超时时间
  β > 1:       退避乘数 (通常 2.0)
  n:           连续打开次数

最大超时限制:
  timeout_open ≤ max_timeout
```

### 3.3 令牌桶限流（半开状态）

```
半开状态令牌桶:

tokens_{t+1} = min(tokens_t + rate × Δt, capacity)

请求准入:
  Admit(request) ⇔ tokens_t ≥ 1

令牌消耗:
  tokens_{after} = tokens_{before} - 1  (如果准入)

恢复判定:
  RecoveryComplete ⇔ success_count ≥ probe_success_threshold
```

---

## 4. Rust 实现

### 4.1 核心状态机实现

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::time::{interval, sleep};

/// 断路器状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitState {
    /// 关闭状态 - 正常服务
    Closed,
    /// 打开状态 - 拒绝请求
    Open { opened_at: Instant, attempt: usize },
    /// 半开状态 - 试探性放行
    HalfOpen { probe_count: usize, success_count: usize },
}

/// 断路器配置
#[derive(Debug, Clone)]
pub struct CircuitBreakerConfig {
    /// 失败阈值（触发熔断）
    pub failure_threshold: u32,
    /// 连续成功阈值（恢复关闭）
    pub success_threshold: u32,
    /// 打开状态超时时间
    pub timeout: Duration,
    /// 最大超时时间（指数退避）
    pub max_timeout: Duration,
    /// 退避乘数
    pub backoff_multiplier: f64,
    /// 半开状态请求限制
    pub half_open_max_requests: usize,
    /// 监控窗口大小
    pub observation_window: Duration,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            success_threshold: 3,
            timeout: Duration::from_secs(30),
            max_timeout: Duration::from_secs(300),
            backoff_multiplier: 2.0,
            half_open_max_requests: 3,
            observation_window: Duration::from_secs(60),
        }
    }
}

/// 断路器统计信息
#[derive(Debug, Default)]
struct CircuitMetrics {
    consecutive_successes: AtomicUsize,
    consecutive_failures: AtomicUsize,
    total_requests: AtomicUsize,
    total_successes: AtomicUsize,
    total_failures: AtomicUsize,
    // EWMA 失败率
    failure_rate: RwLock<f64>,
}

/// 断路器
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: RwLock<CircuitState>,
    metrics: CircuitMetrics,
    open_count: AtomicUsize,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            state: RwLock::new(CircuitState::Closed),
            metrics: CircuitMetrics::default(),
            open_count: AtomicUsize::new(0),
        }
    }

    /// 执行受保护的异步操作
    pub async fn execute<F, Fut, T, E>(
        &self,
        operation: F,
    ) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
    {
        // 检查状态并获取执行许可
        self.check_state().await?;

        // 执行操作
        match operation().await {
            Ok(result) => {
                self.on_success().await;
                Ok(result)
            }
            Err(err) => {
                self.on_failure().await;
                Err(CircuitBreakerError::OperationError(err))
            }
        }
    }

    /// 检查当前状态
    async fn check_state(&self) -> Result<(), CircuitBreakerError<()>> {
        let mut state = self.state.write().await;
        let now = Instant::now();

        match *state {
            CircuitState::Closed => {
                // 关闭状态允许通过
                self.metrics.total_requests.fetch_add(1, Ordering::Relaxed);
                Ok(())
            }
            CircuitState::Open { opened_at, attempt } => {
                // 检查是否超时
                let timeout = self.calculate_timeout(attempt);

                if now.duration_since(opened_at) >= timeout {
                    // 超时，转换为半开状态
                    tracing::info!("Circuit breaker transitioning to Half-Open");
                    *state = CircuitState::HalfOpen {
                        probe_count: 0,
                        success_count: 0,
                    };
                    Ok(())
                } else {
                    // 仍在打开状态，计算剩余时间
                    let remaining = timeout - now.duration_since(opened_at);
                    Err(CircuitBreakerError::CircuitOpen {
                        retry_after: remaining
                    })
                }
            }
            CircuitState::HalfOpen { probe_count, .. } => {
                // 半开状态限制并发请求数
                if probe_count >= self.config.half_open_max_requests {
                    Err(CircuitBreakerError::CircuitOpen {
                        retry_after: self.config.timeout,
                    })
                } else {
                    // 增加探测计数
                    if let CircuitState::HalfOpen { ref mut probe_count, .. } = *state {
                        *probe_count += 1;
                    }
                    self.metrics.total_requests.fetch_add(1, Ordering::Relaxed);
                    Ok(())
                }
            }
        }
    }

    /// 计算当前超时时间（指数退避）
    fn calculate_timeout(&self, attempt: usize) -> Duration {
        let multiplier = self.config.backoff_multiplier.powi(attempt as i32);
        let timeout_ms = self.config.timeout.as_millis() as f64 * multiplier;
        let timeout = Duration::from_millis(timeout_ms as u64);
        timeout.min(self.config.max_timeout)
    }

    /// 成功处理
    async fn on_success(&self) {
        let mut state = self.state.write().await;

        self.metrics.consecutive_successes.fetch_add(1, Ordering::Relaxed);
        self.metrics.consecutive_failures.store(0, Ordering::Relaxed);
        self.metrics.total_successes.fetch_add(1, Ordering::Relaxed);

        match *state {
            CircuitState::Closed => {
                // 更新失败率（EWMA）
                self.update_failure_rate(false).await;
            }
            CircuitState::HalfOpen { probe_count, success_count } => {
                let new_success = success_count + 1;

                if new_success >= self.config.success_threshold {
                    // 达到成功阈值，关闭断路器
                    tracing::info!("Circuit breaker closing after successful probes");
                    *state = CircuitState::Closed;
                    self.metrics.consecutive_successes.store(0, Ordering::Relaxed);
                    self.open_count.store(0, Ordering::Relaxed);
                } else {
                    *state = CircuitState::HalfOpen {
                        probe_count,
                        success_count: new_success,
                    };
                }
            }
            _ => {}
        }
    }

    /// 失败处理
    async fn on_failure(&self) {
        let mut state = self.state.write().await;

        let failures = self.metrics.consecutive_failures.fetch_add(1, Ordering::Relaxed) + 1;
        self.metrics.consecutive_successes.store(0, Ordering::Relaxed);
        self.metrics.total_failures.fetch_add(1, Ordering::Relaxed);

        // 更新失败率
        self.update_failure_rate(true).await;

        match *state {
            CircuitState::Closed => {
                // 检查是否达到失败阈值
                let failure_rate = *self.metrics.failure_rate.read().await;

                if failures >= self.config.failure_threshold as usize
                    || failure_rate > 0.5
                {
                    let open_count = self.open_count.fetch_add(1, Ordering::Relaxed);
                    tracing::warn!(
                        "Circuit breaker opening after {} consecutive failures",
                        failures
                    );
                    *state = CircuitState::Open {
                        opened_at: Instant::now(),
                        attempt: open_count,
                    };
                }
            }
            CircuitState::HalfOpen { .. } => {
                // 半开状态失败，立即重新打开
                let open_count = self.open_count.load(Ordering::Relaxed);
                tracing::warn!("Circuit breaker re-opening after probe failure");
                *state = CircuitState::Open {
                    opened_at: Instant::now(),
                    attempt: open_count,
                };
            }
            _ => {}
        }
    }

    /// 更新 EWMA 失败率
    async fn update_failure_rate(&self, is_failure: bool) {
        const ALPHA: f64 = 0.2; // 平滑因子

        let mut rate = self.metrics.failure_rate.write().await;
        let indicator = if is_failure { 1.0 } else { 0.0 };
        *rate = ALPHA * indicator + (1.0 - ALPHA) * *rate;
    }

    /// 获取当前状态（用于监控）
    pub async fn current_state(&self) -> CircuitState {
        *self.state.read().await
    }

    /// 获取统计信息
    pub fn metrics(&self) -> &CircuitMetrics {
        &self.metrics
    }
}

/// 断路器错误类型
#[derive(Debug)]
pub enum CircuitBreakerError<E> {
    /// 断路器打开
    CircuitOpen { retry_after: Duration },
    /// 操作执行错误
    OperationError(E),
}

impl<E: std::fmt::Display> std::fmt::Display for CircuitBreakerError<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CircuitOpen { retry_after } => {
                write!(f, "Circuit breaker is OPEN, retry after {:?}", retry_after)
            }
            Self::OperationError(e) => write!(f, "Operation failed: {}", e),
        }
    }
}

impl<E: std::fmt::Debug + std::fmt::Display> std::error::Error for CircuitBreakerError<E> {}
```

### 4.2 异步适配器与集成

```rust
/// 断路器 HTTP 中间件
use tower::{Layer, Service};
use std::task::{Context, Poll};
use std::pin::Pin;

#[derive(Clone)]
pub struct CircuitBreakerLayer {
    breaker: Arc<CircuitBreaker>,
}

impl CircuitBreakerLayer {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            breaker: Arc::new(CircuitBreaker::new(config)),
        }
    }
}

impl<S> Layer<S> for CircuitBreakerLayer {
    type Service = CircuitBreakerService<S>;

    fn layer(&self, inner: S) -> Self::Service {
        CircuitBreakerService {
            inner,
            breaker: self.breaker.clone(),
        }
    }
}

#[derive(Clone)]
pub struct CircuitBreakerService<S> {
    inner: S,
    breaker: Arc<CircuitBreaker>,
}

impl<S, Request> Service<Request> for CircuitBreakerService<S>
where
    S: Service<Request> + Clone + Send + 'static,
    S::Future: Send,
    S::Error: std::fmt::Debug + std::fmt::Display,
{
    type Response = S::Response;
    type Error = CircuitBreakerError<S::Error>;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        // 检查断路器状态
        match self.breaker.current_state().try_into_ready() {
            Ok(()) => self.inner.poll_ready(cx).map_err(CircuitBreakerError::OperationError),
            Err(e) => Poll::Ready(Err(e)),
        }
    }

    fn call(&mut self, req: Request) -> Self::Future {
        let mut inner = self.inner.clone();
        let breaker = self.breaker.clone();

        Box::pin(async move {
            breaker.execute(|| async { inner.call(req).await }).await
        })
    }
}

/// 批量请求断路器
pub struct BulkheadCircuitBreaker {
    breaker: CircuitBreaker,
    semaphore: Arc<Semaphore>,
}

impl BulkheadCircuitBreaker {
    pub fn new(breaker_config: CircuitBreakerConfig, max_concurrent: usize) -> Self {
        Self {
            breaker: CircuitBreaker::new(breaker_config),
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
        }
    }

    pub async fn execute<F, Fut, T, E>(
        &self,
        operation: F,
    ) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<T, E>>,
    {
        // 先获取执行许可
        let _permit = self.semaphore.acquire().await
            .map_err(|_| CircuitBreakerError::CircuitOpen {
                retry_after: Duration::from_secs(1),
            })?;

        // 再经过断路器
        self.breaker.execute(operation).await
    }
}

/// 自适应断路器（基于延迟）
pub struct AdaptiveCircuitBreaker {
    inner: CircuitBreaker,
    latency_threshold: Duration,
    latency_window: RwLock<VecDeque<Duration>>,
}

impl AdaptiveCircuitBreaker {
    pub fn new(config: CircuitBreakerConfig, latency_threshold: Duration) -> Self {
        Self {
            inner: CircuitBreaker::new(config),
            latency_threshold,
            latency_window: RwLock::new(VecDeque::with_capacity(100)),
        }
    }

    pub async fn execute<F, Fut, T, E>(
        &self,
        operation: F,
    ) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<T, E>>,
    {
        let start = Instant::now();

        let result = self.inner.execute(operation).await;

        // 记录延迟
        let latency = start.elapsed();
        self.record_latency(latency).await;

        // 如果延迟过高，触发失败计数
        if latency > self.latency_threshold {
            self.inner.on_failure().await;
        }

        result
    }

    async fn record_latency(&self, latency: Duration) {
        let mut window = self.latency_window.write().await;
        window.push_back(latency);
        if window.len() > 100 {
            window.pop_front();
        }
    }

    /// 计算百分位延迟
    pub async fn percentile_latency(&self, p: f64) -> Option<Duration> {
        let window = self.latency_window.read().await;
        if window.is_empty() {
            return None;
        }

        let mut sorted: Vec<_> = window.iter().cloned().collect();
        sorted.sort();

        let idx = ((sorted.len() as f64) * p / 100.0) as usize;
        sorted.get(idx).cloned()
    }
}
```

### 4.3 事件通知与可观测性

```rust
/// 断路器事件
#[derive(Debug, Clone)]
pub enum CircuitBreakerEvent {
    StateChanged {
        from: CircuitState,
        to: CircuitState,
        timestamp: Instant,
    },
    RequestRejected {
        state: CircuitState,
        timestamp: Instant,
    },
    FailureRecorded {
        consecutive_failures: usize,
        failure_rate: f64,
    },
    RecoveryStarted {
        probe_count: usize,
    },
    RecoveryCompleted,
}

/// 事件处理器 trait
#[async_trait]
pub trait CircuitBreakerEventHandler: Send + Sync {
    async fn handle(&self, event: CircuitBreakerEvent);
}

/// 带事件通知的断路器
pub struct ObservableCircuitBreaker {
    inner: CircuitBreaker,
    handlers: RwLock<Vec<Box<dyn CircuitBreakerEventHandler>>>,
}

impl ObservableCircuitBreaker {
    pub async fn add_handler<H: CircuitBreakerEventHandler + 'static>(&self, handler: H) {
        self.handlers.write().await.push(Box::new(handler));
    }

    async fn notify(&self, event: CircuitBreakerEvent) {
        for handler in self.handlers.read().await.iter() {
            handler.handle(event.clone()).await;
        }
    }

    /// Prometheus 指标导出
    pub fn register_metrics(&self, registry: &Registry) {
        let state_gauge = GaugeVec::new(
            Opts::new("circuit_breaker_state", "Current circuit breaker state"),
            &["name"],
        ).unwrap();

        let request_counter = CounterVec::new(
            Opts::new("circuit_breaker_requests_total", "Total requests"),
            &["name", "result"],
        ).unwrap();

        registry.register(Box::new(state_gauge.clone())).unwrap();
        registry.register(Box::new(request_counter.clone())).unwrap();

        // 启动指标更新任务
        let breaker = Arc::clone(&self.inner);
        tokio::spawn(async move {
            let mut ticker = interval(Duration::from_secs(10));
            loop {
                ticker.tick().await;

                let state = breaker.current_state().await;
                let state_value = match state {
                    CircuitState::Closed => 0.0,
                    CircuitState::Open { .. } => 1.0,
                    CircuitState::HalfOpen { .. } => 2.0,
                };
                state_gauge.with_label_values(&["default"]).set(state_value);
            }
        });
    }
}
```

---

## 5. 形式化验证

### 5.1 安全性与活性

```
断路器安全性 (Safety):

1. 当断路器处于 Open 状态时，不会执行目标操作:
   □ (state = Open → ¬Execute(operation))

2. 半开状态的并发请求数受限制:
   □ (state = HalfOpen ∧ active_requests ≤ half_open_max)

3. 失败率计算正确性:
   failure_rate ∈ [0, 1] ∧ monotonic_in_failure

断路器活性 (Liveness):

1. 打开状态最终会超时:
   ◇ (state = Open → ◇ (state = HalfOpen))

2. 半开状态最终会收敛:
   state = HalfOpen → ◇ (state = Closed ∨ state = Open)

3. 成功恢复后关闭:
   (success_count ≥ threshold) → ◇ (state = Closed)
```

### 5.2 时序逻辑规格

```
TLA+ 风格的时序规格:

VARIABLES state, failure_count, success_count, last_open_time

Init ==
  ∧ state = "Closed"
  ∧ failure_count = 0
  ∧ success_count = 0

OpenCircuit ==
  ∧ state = "Closed"
  ∧ failure_count ≥ FailureThreshold
  ∧ state' = "Open"
  ∧ failure_count' = 0
  ∧ last_open_time' = now
  ∧ UNCHANGED success_count

AttemptRecovery ==
  ∧ state = "Open"
  ∧ now - last_open_time ≥ Timeout
  ∧ state' = "HalfOpen"
  ∧ success_count' = 0
  ∧ UNCHANGED <<failure_count, last_open_time>>

CloseCircuit ==
  ∧ state = "HalfOpen"
  ∧ success_count ≥ SuccessThreshold
  ∧ state' = "Closed"
  ∧ success_count' = 0
  ∧ UNCHANGED <<failure_count, last_open_time>>

ReOpenCircuit ==
  ∧ state = "HalfOpen"
  ∧ failure_count > 0
  ∧ state' = "Open"
  ∧ failure_count' = 0
  ∧ last_open_time' = now
  ∧ UNCHANGED success_count

Next ==
  ∨ OpenCircuit
  ∨ AttemptRecovery
  ∨ CloseCircuit
  ∨ ReOpenCircuit
  ∨ ProcessRequest

Spec == Init ∧ □[Next]_vars ∧ WF_vars(AttemptRecovery)
```

---

## 6. 高级模式

### 6.1 多级断路器

```rust
/// 分层断路器
pub struct HierarchicalCircuitBreaker {
    /// 全局断路器
    global: Arc<CircuitBreaker>,
    /// 按服务分类的断路器
    services: DashMap<String, Arc<CircuitBreaker>>,
    /// 按端点分类的断路器
    endpoints: DashMap<(String, String), Arc<CircuitBreaker>>,
}

impl HierarchicalCircuitBreaker {
    pub async fn execute_service<F, Fut, T, E>(
        &self,
        service: &str,
        operation: F,
    ) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<T, E>>,
    {
        // 先检查全局断路器
        self.global.check_state().await?;

        // 再检查服务断路器
        let service_breaker = self.services.entry(service.to_string())
            .or_insert_with(|| Arc::new(CircuitBreaker::new(self.service_config(service))));

        service_breaker.execute(operation).await
    }
}
```

### 6.2 预测性断路器

```rust
/// 基于机器学习的预测性断路器
pub struct PredictiveCircuitBreaker {
    inner: CircuitBreaker,
    predictor: Arc<dyn FailurePredictor>,
    features: RwLock<Vec<FeatureVector>>,
}

#[async_trait]
pub trait FailurePredictor: Send + Sync {
    async fn predict_failure_probability(&self, features: &FeatureVector) -> f64;
}

impl PredictiveCircuitBreaker {
    /// 提前打开断路器（预测性）
    pub async fn preemptive_open(&self) {
        let features = self.collect_features().await;
        let probability = self.predictor.predict_failure_probability(&features).await;

        if probability > 0.7 {
            // 预测到高失败概率，提前熔断
            self.inner.force_open().await;
        }
    }
}
```

---

## 7. 性能考量

```
断路器性能开销分析:

1. 状态检查开销:
   - 内存读取: ~10-50ns
   - RwLock 读取: ~100-500ns
   - 无锁原子操作: ~50-100ns

2. 失败计数更新:
   - 原子自增: ~20-50ns
   - 建议使用 Relaxed 序

3. 状态转换:
   - 写锁获取: ~500ns-2μs
   - 仅在阈值触发时发生，频率低

4. 监控指标:
   - 建议异步批量更新
   - 避免每次请求同步记录

优化策略:
- 使用 ThreadLocal 缓存状态副本
- 批量处理指标上报
- 无锁数据结构用于高频计数
```

---

## 8. 总结

| 特性 | 实现要点 |
|------|----------|
| 状态机 | Closed → Open → HalfOpen 三态 |
| 触发条件 | 连续失败数 / 失败率 / 延迟阈值 |
| 恢复机制 | 超时 + 探测成功计数 |
| 并发控制 | 半开状态令牌桶限流 |
| 可观测性 | 事件通知 + 指标导出 |

关键公式:

$$
\text{OpenDecision} = \begin{cases}
\text{Open} & \text{if } f_{consecutive} \geq \theta_{failure} \lor \rho_{ewma} > \theta_{rate} \\
\text{Closed} & \text{otherwise}
\end{cases}
$$

$$
\rho_{ewma}^{(t)} = \alpha \cdot \mathbb{1}_{failure} + (1-\alpha) \cdot \rho_{ewma}^{(t-1)}
$$

$$
\tau_{open}^{(n)} = \min(\tau_{base} \cdot \beta^n, \tau_{max})
$$
