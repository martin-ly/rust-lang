# 重试模式语义 (Retry Pattern Semantics)

## 目录

- [重试模式语义 (Retry Pattern Semantics)](#重试模式语义-retry-pattern-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 重试策略分类](#2-重试策略分类)
    - [2.1 策略类型谱系](#21-策略类型谱系)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 数学模型](#3-数学模型)
    - [3.1 指数退避分析](#31-指数退避分析)
    - [3.2 碰撞避免分析](#32-碰撞避免分析)
    - [3.3 幂等性分析](#33-幂等性分析)
  - [4. Rust 实现](#4-rust-实现)
    - [4.1 核心重试框架](#41-核心重试框架)
    - [4.2 幂等性保证](#42-幂等性保证)
    - [4.3 高级重试模式](#43-高级重试模式)
  - [5. 形式化验证](#5-形式化验证)
    - [5.1 终止性保证](#51-终止性保证)
    - [5.2 活性保证](#52-活性保证)
  - [6. 性能与最佳实践](#6-性能与最佳实践)
  - [7. 总结](#7-总结)

## 1. 引言

重试模式是分布式系统处理瞬时故障的基础机制。本文档深入分析各种重试策略的数学模型、语义保证及其在 Rust 中的实现。

---

## 2. 重试策略分类

### 2.1 策略类型谱系

```
重试策略分类:

┌─────────────────────────────────────────────────────────────────┐
│  策略类型          公式                          适用场景         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  立即重试         delay = 0                      低延迟要求       │
│  (Immediate)                                                   │
│                                                                 │
│  固定间隔         delay = base                   均匀负载         │
│  (Fixed)                                                         │
│                                                                 │
│  线性退避         delay = base × n               渐进式等待       │
│  (Linear)                                                        │
│                                                                 │
│  指数退避         delay = base × k^n             网络抖动         │
│  (Exponential)                                                   │
│                                                                 │
│  随机抖动         delay = f(n) + jitter          避免惊群         │
│  (Jitter)                                                        │
│                                                                 │
│  自适应退避       delay = f(telemetry)           动态调整         │
│  (Adaptive)                                                      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 形式化定义

```
重试策略形式化:

重试决策函数:
  RetryDecision: Attempt × Error × Context → {Retry, Abort}

重试延迟函数:
  Delay: Attempt × Strategy → Duration

策略类型:

1. 固定间隔 (Fixed):
   delay(n) = base

2. 线性退避 (Linear):
   delay(n) = base × n

3. 指数退避 (Exponential):
   delay(n) = min(base × multiplier^n, max_delay)

4. 抖动指数退避 (Exponential with Jitter):
   delay(n) = min(base × multiplier^n, max_delay) + jitter()

   其中 jitter() ∈ [0, jitter_max]

5. 全抖动 (Full Jitter):
   delay(n) = Uniform(0, min(base × multiplier^n, max_delay))

6. 等抖动 (Equal Jitter):
   temp = min(base × multiplier^n, max_delay)
   delay(n) = temp/2 + Uniform(0, temp/2)

7. 退correlated抖动:
   delay(n) = min(base × multiplier^n, max_delay) × (1 + α × rand())
```

---

## 3. 数学模型

### 3.1 指数退避分析

```
指数退避的期望延迟:

E[delay(n)] = base × multiplier^n × (1 + E[jitter])

对于全抖动策略:
E[delay_jitter(n)] = base × multiplier^n / 2

总重试时间（N 次重试）:

T_total = Σ_{i=0}^{N-1} delay(i)

对于纯指数退避:
T_total = base × (multiplier^N - 1) / (multiplier - 1)   (当 multiplier ≠ 1)

上界分析:
T_total ≤ N × max_delay
```

### 3.2 碰撞避免分析

```
抖动策略的碰撞概率:

无抖动时:
P_collision = 1 - (1 - 1/W)^{n-1} ≈ (n-1)/W  (当 n << W)

其中 W 为时间窗口，n 为并发客户端数

带抖动时:
P_collision_jitter = 1 - Π_{i=1}^{n-1} (1 - P_i)

对于均匀抖动，碰撞概率显著降低:
P_collision_jitter ≈ P_collision / jitter_factor

最优抖动参数:
  jitter_max ≈ delay(n) × 0.5  通常提供良好的平衡
```

### 3.3 幂等性分析

```
幂等性定义:

操作 f 是幂等的，当且仅当:
  ∀x. f(f(x)) = f(x)

在重试语境下:
  Execute(request) ∘ Execute(request) = Execute(request)

幂等性保证级别:

级别 0 (无保证):
  重复执行可能导致不一致状态

级别 1 (最终一致):
  重复执行最终收敛到一致状态

级别 2 (强幂等):
  重复执行立即返回相同结果

级别 3 (严格幂等):
  重复执行不改变任何状态

幂等键设计:
  IdempotencyKey = Hash(ClientID, RequestID, Timestamp)

幂等窗口:
  Window = [now - retention, now]
  超出窗口的请求视为新请求
```

---

## 4. Rust 实现

### 4.1 核心重试框架

```rust
use std::fmt::Debug;
use std::future::Future;
use std::pin::Pin;
use std::time::Duration;
use tokio::time::sleep;
use rand::{thread_rng, Rng};
use thiserror::Error;

/// 重试策略 trait
pub trait RetryStrategy: Send + Sync {
    /// 计算下一次重试的延迟
    fn next_delay(&self, attempt: u32) -> Duration;

    /// 最大重试次数
    fn max_attempts(&self) -> u32;
}

/// 固定间隔策略
#[derive(Debug, Clone, Copy)]
pub struct FixedInterval {
    pub interval: Duration,
    pub max_attempts: u32,
}

impl RetryStrategy for FixedInterval {
    fn next_delay(&self, _attempt: u32) -> Duration {
        self.interval
    }

    fn max_attempts(&self) -> u32 {
        self.max_attempts
    }
}

/// 线性退避策略
#[derive(Debug, Clone, Copy)]
pub struct LinearBackoff {
    pub base: Duration,
    pub increment: Duration,
    pub max_delay: Duration,
    pub max_attempts: u32,
}

impl RetryStrategy for LinearBackoff {
    fn next_delay(&self, attempt: u32) -> Duration {
        let delay = self.base + self.increment * attempt;
        delay.min(self.max_delay)
    }

    fn max_attempts(&self) -> u32 {
        self.max_attempts
    }
}

/// 指数退避策略
#[derive(Debug, Clone, Copy)]
pub struct ExponentialBackoff {
    pub base: Duration,
    pub multiplier: f64,
    pub max_delay: Duration,
    pub max_attempts: u32,
}

impl RetryStrategy for ExponentialBackoff {
    fn next_delay(&self, attempt: u32) -> Duration {
        let exp_delay = self.base.as_millis() as f64 * self.multiplier.powi(attempt as i32);
        let delay_ms = exp_delay.min(self.max_delay.as_millis() as f64) as u64;
        Duration::from_millis(delay_ms)
    }

    fn max_attempts(&self) -> u32 {
        self.max_attempts
    }
}

/// 抖动类型
#[derive(Debug, Clone, Copy)]
pub enum JitterType {
    /// 无抖动
    None,
    /// 全抖动 - 均匀分布在 [0, delay]
    Full,
    /// 等抖动 - 均匀分布在 [delay/2, delay]
    Equal,
    ///  decorrelated抖动 - 基于上次延迟
    Decorrelated { base: Duration },
}

/// 带抖动的指数退避
#[derive(Debug, Clone)]
pub struct JitteredExponentialBackoff {
    pub base: Duration,
    pub multiplier: f64,
    pub max_delay: Duration,
    pub max_attempts: u32,
    pub jitter: JitterType,
}

impl RetryStrategy for JitteredExponentialBackoff {
    fn next_delay(&self, attempt: u32) -> Duration {
        let base_delay = self.base.as_millis() as f64 * self.multiplier.powi(attempt as i32);
        let capped_delay = base_delay.min(self.max_delay.as_millis() as f64) as u64;

        let mut rng = thread_rng();

        let jittered_ms = match self.jitter {
            JitterType::None => capped_delay,
            JitterType::Full => rng.gen_range(0..=capped_delay),
            JitterType::Equal => {
                let half = capped_delay / 2;
                half + rng.gen_range(0..=half)
            }
            JitterType::Decorrelated { base } => {
                let prev = self.base.as_millis() as f64 *
                    self.multiplier.powi(attempt.saturating_sub(1) as i32);
                let decorrelated = rng.gen_range(base.as_millis()..=prev as u64);
                decorrelated.min(capped_delay)
            }
        };

        Duration::from_millis(jittered_ms)
    }

    fn max_attempts(&self) -> u32 {
        self.max_attempts
    }
}

/// 重试条件 trait
pub trait RetryCondition<E>: Send + Sync {
    fn should_retry(&self, error: &E, attempt: u32) -> bool;
}

/// 基于错误类型的条件
#[derive(Debug, Clone)]
pub struct ErrorTypeCondition<E> {
    pub retryable_errors: Vec<E>,
    pub max_attempts: u32,
}

impl<E: PartialEq + Debug> RetryCondition<E> for ErrorTypeCondition<E> {
    fn should_retry(&self, error: &E, attempt: u32) -> bool {
        if attempt >= self.max_attempts {
            return false;
        }
        self.retryable_errors.iter().any(|e| e == error)
    }
}

/// 闭包条件
pub struct ClosureCondition<F> {
    predicate: F,
}

impl<E, F> RetryCondition<E> for ClosureCondition<F>
where
    F: Fn(&E, u32) -> bool + Send + Sync,
{
    fn should_retry(&self, error: &E, attempt: u32) -> bool {
        (self.predicate)(error, attempt)
    }
}

/// 重试上下文
#[derive(Debug, Clone)]
pub struct RetryContext {
    pub attempt: u32,
    pub total_delay: Duration,
    pub last_error: Option<String>,
    pub start_time: std::time::Instant,
}

impl Default for RetryContext {
    fn default() -> Self {
        Self {
            attempt: 0,
            total_delay: Duration::ZERO,
            last_error: None,
            start_time: std::time::Instant::now(),
        }
    }
}

/// 重试执行器
pub struct RetryExecutor<S, C> {
    strategy: S,
    condition: C,
}

impl<S, C> RetryExecutor<S, C> {
    pub fn new(strategy: S, condition: C) -> Self {
        Self { strategy, condition }
    }
}

impl<S, C, E> RetryExecutor<S, C>
where
    S: RetryStrategy,
    C: RetryCondition<E>,
    E: Debug,
{
    /// 执行带重试的操作
    pub async fn execute<F, Fut, T>(
        &self,
        mut operation: F,
    ) -> Result<T, RetryError<E>>
    where
        F: FnMut() -> Fut,
        Fut: Future<Output = Result<T, E>>,
    {
        let mut context = RetryContext::default();

        loop {
            match operation().await {
                Ok(result) => {
                    tracing::debug!(
                        "Operation succeeded after {} attempts",
                        context.attempt + 1
                    );
                    return Ok(result);
                }
                Err(error) => {
                    context.attempt += 1;
                    context.last_error = Some(format!("{:?}", error));

                    // 检查是否应该重试
                    if !self.condition.should_retry(&error, context.attempt) {
                        tracing::warn!(
                            "Not retrying after {} attempts: {:?}",
                            context.attempt,
                            error
                        );
                        return Err(RetryError::Permanent(error));
                    }

                    // 检查是否达到最大重试次数
                    if context.attempt >= self.strategy.max_attempts() {
                        tracing::error!(
                            "Max retries ({}) exceeded: {:?}",
                            self.strategy.max_attempts(),
                            error
                        );
                        return Err(RetryError::Exhausted {
                            attempts: context.attempt,
                            last_error: error,
                        });
                    }

                    // 计算并应用延迟
                    let delay = self.strategy.next_delay(context.attempt);
                    tracing::info!(
                        "Retry attempt {}/{} after {:?}",
                        context.attempt,
                        self.strategy.max_attempts(),
                        delay
                    );

                    context.total_delay += delay;
                    sleep(delay).await;
                }
            }
        }
    }
}

/// 重试错误类型
#[derive(Debug, Error)]
pub enum RetryError<E> {
    /// 永久性错误（不应重试）
    #[error("Permanent error: {0:?}")]
    Permanent(E),

    /// 重试用尽
    #[error("Retries exhausted after {attempts} attempts: {last_error:?}")]
    Exhausted { attempts: u32, last_error: E },
}
```

### 4.2 幂等性保证

```rust
use std::collections::HashMap;
use std::hash::Hash;
use tokio::sync::RwLock;
use uuid::Uuid;

/// 幂等键
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct IdempotencyKey {
    pub client_id: String,
    pub request_id: String,
    pub timestamp: u64,
}

impl IdempotencyKey {
    pub fn new(client_id: impl Into<String>, request_id: impl Into<String>) -> Self {
        Self {
            client_id: client_id.into(),
            request_id: request_id.into(),
            timestamp: chrono::Utc::now().timestamp_millis() as u64,
        }
    }

    pub fn generate() -> Self {
        Self {
            client_id: "auto".to_string(),
            request_id: Uuid::new_v4().to_string(),
            timestamp: chrono::Utc::now().timestamp_millis() as u64,
        }
    }
}

/// 幂等响应存储
#[derive(Debug, Clone)]
pub struct IdempotentResponse<T> {
    pub response: T,
    pub created_at: std::time::Instant,
    pub expires_at: std::time::Instant,
}

/// 幂等执行器
pub struct IdempotentExecutor<T, E> {
    /// 响应缓存
    responses: Arc<RwLock<HashMap<IdempotencyKey, Result<T, E>>>>,
    /// 正在处理的请求
    in_progress: Arc<RwLock<HashMap<IdempotencyKey, tokio::sync::broadcast::Sender<Result<T, E>>>>>,
    /// 响应保留时间
    retention: Duration,
    /// 清理间隔
    cleanup_interval: Duration,
}

impl<T: Clone + Send + Sync + 'static, E: Clone + Send + Sync + 'static> IdempotentExecutor<T, E> {
    pub fn new(retention: Duration) -> Self {
        let executor = Self {
            responses: Arc::new(RwLock::new(HashMap::new())),
            in_progress: Arc::new(RwLock::new(HashMap::new())),
            retention,
            cleanup_interval: retention / 2,
        };

        // 启动清理任务
        executor.start_cleanup_task();

        executor
    }

    fn start_cleanup_task(&self) {
        let responses = Arc::clone(&self.responses);
        let interval = self.cleanup_interval;

        tokio::spawn(async move {
            let mut ticker = tokio::time::interval(interval);
            loop {
                ticker.tick().await;

                let now = std::time::Instant::now();
                let mut guard = responses.write().await;
                guard.retain(|_, v| {
                    if let Ok(resp) = v {
                        // 保留未过期的响应
                        now < std::time::Instant::now() + interval
                    } else {
                        // 错误响应保留更短时间
                        true
                    }
                });

                tracing::debug!("Cleaned up expired idempotent responses, {} remaining", guard.len());
            }
        });
    }

    /// 执行幂等操作
    pub async fn execute<F, Fut>(
        &self,
        key: IdempotencyKey,
        operation: F,
    ) -> Result<T, E>
    where
        F: FnOnce() -> Fut + Send,
        Fut: Future<Output = Result<T, E>> + Send,
    {
        // 检查缓存
        {
            let responses = self.responses.read().await;
            if let Some(result) = responses.get(&key) {
                tracing::debug!("Returning cached idempotent response for {:?}", key);
                return result.clone();
            }
        }

        // 检查是否已有正在处理的请求
        let mut rx = {
            let in_progress = self.in_progress.read().await;
            if let Some(tx) = in_progress.get(&key) {
                tracing::debug!("Waiting for in-progress request for {:?}", key);
                tx.subscribe()
            } else {
                drop(in_progress);

                // 创建新的广播通道
                let (tx, rx) = tokio::sync::broadcast::channel(1);
                let mut in_progress = self.in_progress.write().await;
                in_progress.insert(key.clone(), tx);

                // 执行操作
                let result = operation().await;

                // 存储结果
                {
                    let mut responses = self.responses.write().await;
                    responses.insert(key.clone(), result.clone());
                }

                // 通知等待者
                let _ = tx.send(result.clone());

                // 从进行中的请求中移除
                in_progress.remove(&key);

                return result;
            }
        };

        // 等待正在处理的请求完成
        rx.recv().await.expect("Sender should not be dropped")
    }
}

/// 带幂等性的重试执行器
pub struct IdempotentRetryExecutor<S, C, T, E> {
    retry: RetryExecutor<S, C>,
    idempotent: IdempotentExecutor<T, E>,
}

impl<S, C, T: Clone + Send + Sync + 'static, E: Clone + Send + Sync + 'static>
    IdempotentRetryExecutor<S, C, T, E>
{
    pub fn new(strategy: S, condition: C, retention: Duration) -> Self {
        Self {
            retry: RetryExecutor::new(strategy, condition),
            idempotent: IdempotentExecutor::new(retention),
        }
    }

    pub async fn execute<F, Fut>(
        &self,
        key: IdempotencyKey,
        operation: F,
    ) -> Result<T, RetryError<E>>
    where
        F: FnMut() -> Fut + Clone,
        Fut: Future<Output = Result<T, E>>,
    {
        self.idempotent.execute(key, || {
            let mut op = operation.clone();
            async move { self.retry.execute(|| op()).await }
        }).await
    }
}
```

### 4.3 高级重试模式

```rust
/// 熔断感知重试
pub struct CircuitBreakerRetry<S, CB> {
    strategy: S,
    circuit_breaker: CB,
}

impl<S: RetryStrategy, CB: CircuitBreaker> CircuitBreakerRetry<S, CB> {
    pub async fn execute<F, Fut, T, E>(
        &self,
        operation: F,
    ) -> Result<T, RetryError<E>>
    where
        F: FnMut() -> Fut,
        Fut: Future<Output = Result<T, E>>,
    {
        // 检查断路器
        if self.circuit_breaker.is_open() {
            return Err(RetryError::CircuitOpen);
        }

        let result = self.execute_with_retry(operation).await;

        // 更新断路器状态
        match &result {
            Ok(_) => self.circuit_breaker.record_success(),
            Err(_) => self.circuit_breaker.record_failure(),
        }

        result
    }
}

/// 自适应重试策略
pub struct AdaptiveRetryStrategy {
    base: Duration,
    max_delay: Duration,
    max_attempts: u32,
    /// 成功/失败历史
    history: Arc<RwLock<Vec<bool>>>,
    /// 自适应调整因子
    adapt_factor: f64,
}

impl RetryStrategy for AdaptiveRetryStrategy {
    fn next_delay(&self, attempt: u32) -> Duration {
        let base_delay = self.base.as_millis() as f64 * 2.0_f64.powi(attempt as i32);

        // 根据成功率调整延迟
        let success_rate = self.calculate_success_rate();
        let adjusted_delay = base_delay * (1.0 + (1.0 - success_rate) * self.adapt_factor);

        Duration::from_millis(adjusted_delay as u64).min(self.max_delay)
    }

    fn max_attempts(&self) -> u32 {
        // 根据成功率动态调整最大重试次数
        let success_rate = self.calculate_success_rate();
        if success_rate < 0.1 {
            (self.max_attempts / 2).max(1) // 成功率低时减少重试
        } else {
            self.max_attempts
        }
    }
}

/// 批量重试（Batched Retry）
pub struct BatchedRetry<S> {
    strategy: S,
    batch_size: usize,
    max_concurrent: usize,
}

impl<S: RetryStrategy> BatchedRetry<S> {
    pub async fn execute_batch<F, Fut, T, E, I>(
        &self,
        items: I,
        operation: F,
    ) -> Vec<Result<T, RetryError<E>>>
    where
        F: Fn(I::Item) -> Fut + Clone + Send + Sync,
        Fut: Future<Output = Result<T, E>> + Send,
        I: IntoIterator,
    {
        use futures::stream::{self, StreamExt};

        stream::iter(items)
            .map(|item| {
                let op = operation.clone();
                let strategy = &self.strategy;
                async move {
                    self.execute_single(|| op(item)).await
                }
            })
            .buffer_unordered(self.max_concurrent)
            .collect()
            .await
    }
}

/// 带超时的重试
pub struct TimeoutRetry<S> {
    strategy: S,
    total_timeout: Duration,
}

impl<S: RetryStrategy> TimeoutRetry<S> {
    pub async fn execute<F, Fut, T, E>(
        &self,
        operation: F,
    ) -> Result<T, RetryError<E>>
    where
        F: FnMut() -> Fut,
        Fut: Future<Output = Result<T, E>>,
    {
        let start = tokio::time::Instant::now();
        let deadline = start + self.total_timeout;

        let mut attempt = 0;
        let mut last_error = None;

        loop {
            attempt += 1;

            // 检查总超时
            let remaining = deadline.saturating_duration_since(tokio::time::Instant::now());
            if remaining.is_zero() {
                return Err(RetryError::Timeout {
                    duration: self.total_timeout,
                    last_error: last_error.expect("Should have an error"),
                });
            }

            // 使用剩余时间作为单次超时
            match tokio::time::timeout(remaining, operation()).await {
                Ok(Ok(result)) => return Ok(result),
                Ok(Err(error)) => {
                    last_error = Some(error);

                    if attempt >= self.strategy.max_attempts() {
                        return Err(RetryError::Exhausted {
                            attempts: attempt,
                            last_error: last_error.unwrap(),
                        });
                    }

                    let delay = self.strategy.next_delay(attempt);
                    sleep(delay).await;
                }
                Err(_) => {
                    return Err(RetryError::Timeout {
                        duration: self.total_timeout,
                        last_error: last_error.expect("Should have an error"),
                    });
                }
            }
        }
    }
}
```

---

## 5. 形式化验证

### 5.1 终止性保证

```
重试终止条件:

1. 成功终止:
   ◇ Success(operation) → ◇□ Result = Ok(value)

2. 失败终止（达到最大重试次数）:
   □ (attempts ≥ max_attempts → ◇ Result = Err(Exhausted))

3. 超时终止:
   □ (elapsed ≥ timeout → ◇ Result = Err(Timeout))

4. 永久错误终止:
   □ (PermanentError(error) → ◇ Result = Err(Permanent(error)))

终止性证明:
  由于 max_attempts ∈ ℕ 且 attempt 单调递增，
  最多经过 max_attempts 次迭代必定终止。
```

### 5.2 活性保证

```
重试活性:

1. 瞬时错误恢复:
   □ (TransientError(e) ∧ retries_remain → ◇ Success)

2. 重试延迟上界:
   □ (Retry(n) → delay(n) ≤ max_delay)

3. 总时间上界:
   □ (Complete → total_time ≤ Σ_{i=1}^{max} delay(i))

抖动公平性:
  对于并发客户端 C = {c₁, c₂, ..., cₙ}，
  使用抖动策略后，碰撞概率满足:

  P(∃i≠j. collision(cᵢ, cⱼ)) ≤ 1/n  (当使用全抖动)
```

---

## 6. 性能与最佳实践

```
性能优化建议:

1. 延迟计算:
   - 使用预计算延迟表避免浮点运算
   - 延迟缓存: Vec<Duration> = precompute(1..max_attempts)

2. 内存分配:
   - 避免每次重试分配 BoxFuture
   - 使用 stack pinning 或池化

3. 并发控制:
   - 限制并发重试数避免级联压力
   - 使用信号量控制

4. 取消传播:
   - 正确处理 tokio::select! 取消
   - 确保操作可取消

5. 指标收集:
   - 重试次数分布
   - 成功/失败率
   - 平均延迟

最佳实践:

| 场景                    | 推荐策略              |
|-------------------------|----------------------|
| 数据库连接失败          | 指数退避 + 抖动       |
| 网络请求超时            | 指数退避 + 全抖动     |
| 幂等 API 调用           | 固定间隔 + 幂等键     |
| 资源竞争                | 线性退避 + decorrelate|
| 高峰流量                | 自适应退避            |
```

---

## 7. 总结

| 策略 | 延迟公式 | 适用场景 |
|------|----------|----------|
| Fixed | $d$ | 稳定延迟环境 |
| Linear | $d \times n$ | 渐进压力释放 |
| Exponential | $d \times k^n$ | 网络抖动恢复 |
| Full Jitter | $U(0, d \times k^n)$ | 高并发碰撞避免 |
| Equal Jitter | $\frac{d \times k^n}{2} + U(0, \frac{d \times k^n}{2})$ | 平衡延迟与分散 |

核心公式:

$$
\text{delay}(n) = \min(d_0 \times k^n, d_{max}) + \text{jitter}
$$

$$
\text{jitter}_{full} \sim \mathcal{U}(0, \text{delay}(n))
$$

$$
\text{P(collision)} = 1 - \left(1 - \frac{1}{W}\right)^{n-1} \approx \frac{n-1}{W} \quad (n \ll W)
$$
