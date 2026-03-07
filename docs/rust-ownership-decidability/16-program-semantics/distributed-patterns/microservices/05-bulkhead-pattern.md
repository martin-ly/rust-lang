# 舱壁隔离模式语义 (Bulkhead Pattern Semantics)

## 目录

- [舱壁隔离模式语义 (Bulkhead Pattern Semantics)](#舱壁隔离模式语义-bulkhead-pattern-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 隔离模型](#2-隔离模型)
    - [2.1 舱壁类型](#21-舱壁类型)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 数学模型](#3-数学模型)
    - [3.1 资源分配模型](#31-资源分配模型)
    - [3.2 容量规划模型](#32-容量规划模型)
  - [4. Rust 实现](#4-rust-实现)
    - [4.1 核心舱壁实现](#41-核心舱壁实现)
    - [4.2 多舱壁管理器](#42-多舱壁管理器)
    - [4.3 舱壁与断路器集成](#43-舱壁与断路器集成)
    - [4.4 自适应舱壁](#44-自适应舱壁)
  - [5. 形式化验证](#5-形式化验证)
    - [5.1 隔离属性](#51-隔离属性)
    - [5.2 性能保证](#52-性能保证)
  - [6. 最佳实践](#6-最佳实践)
  - [7. 总结](#7-总结)

## 1. 引言

舱壁隔离模式（Bulkhead Pattern）是将系统资源划分为独立隔离的池，以防止故障在不同组件之间传播的关键容错机制。
其名称来源于船舶设计中的防水舱壁概念。

---

## 2. 隔离模型

### 2.1 舱壁类型

```
舱壁隔离类型:

┌──────────────────────────────────────────────────────────────────┐
│                      舱壁隔离模式                                 │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │                   线程池隔离                               │  │
│  ├───────────────────────────────────────────────────────────┤  │
│  │  Service A          Service B          Service C          │  │
│  │  ┌─────────┐        ┌─────────┐        ┌─────────┐       │  │
│  │  │ Thread  │        │ Thread  │        │ Thread  │       │  │
│  │  │ Pool A  │        │ Pool B  │        │ Pool C  │       │  │
│  │  │ [▓▓░░]  │        │ [▓▓▓░]  │        │ [░░░░]  │       │  │
│  │  └────┬────┘        └────┬────┘        └────┬────┘       │  │
│  │       │                  │                  │            │  │
│  │       ▼                  ▼                  ▼            │  │
│  │  [Isolated]          [Isolated]          [Isolated]      │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │                   连接池隔离                               │  │
│  ├───────────────────────────────────────────────────────────┤  │
│  │  DB Primary        DB Replica        External API         │  │
│  │  ┌─────────┐       ┌─────────┐       ┌─────────┐         │  │
│  │  │ Conn×10 │       │ Conn×5  │       │ Conn×3  │         │  │
│  │  │ [▓▓▓▓]  │       │ [▓▓░░]  │       │ [▓▓▓]   │         │  │
│  │  └────┬────┘       └────┬────┘       └────┬────┘         │  │
│  │       │                  │                 │              │  │
│  │       ▼                  ▼                 ▼              │  │
│  │  [Separate]           [Separate]         [Separate]       │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │                   信号量隔离                               │  │
│  ├───────────────────────────────────────────────────────────┤  │
│  │  Critical Path      Normal Path        Background         │  │
│  │  ┌─────────┐       ┌─────────┐       ┌─────────┐         │  │
│  │  │ Sem: 5  │       │ Sem: 20 │       │ Sem: 50 │         │  │
│  │  │ [▓▓░░░] │       │ [▓▓▓▓░░]│       │ [▓▓▓▓▓▓]│         │  │
│  │  └─────────┘       └─────────┘       └─────────┘         │  │
│  │  Priority: HIGH    Priority: NORMAL  Priority: LOW       │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

### 2.2 形式化定义

```
舱壁模式形式化语义:

舱壁定义:
  Bulkhead = (Name, Capacity, QueueSize, Allocated, Available)

资源分配:
  Allocate: Bulkhead × Request → {Success, Queue, Reject}

  Allocate(bulkhead, req) =
    if bulkhead.available > 0 then
      bulkhead.available -= 1
      Success
    else if bulkhead.queue.size < bulkhead.queue.capacity then
      bulkhead.queue.enqueue(req)
      Queue
    else
      Reject

资源释放:
  Release: Bulkhead → Unit

  Release(bulkhead) =
    if bulkhead.queue.not_empty then
      req = bulkhead.queue.dequeue()
      process(req)
    else
      bulkhead.available += 1

隔离不变式:
  1. 资源独立性:
     □ (Bulkheadᵢ.resources ∩ Bulkheadⱼ.resources = ∅) for i ≠ j

  2. 故障隔离:
     □ (FailureIn(Bulkheadᵢ) → ¬FailurePropagatesTo(Bulkheadⱼ))

  3. 容量限制:
     □ (Bulkheadᵢ.allocated ≤ Bulkheadᵢ.capacity)
```

---

## 3. 数学模型

### 3.1 资源分配模型

```
资源池数学模型:

状态表示:
  S = (A, Q) where
    A: 可用资源数 (Available)
    Q: 队列中的请求数 (Queued)

状态转换:
  Request: (A, Q) → (A-1, Q)   if A > 0
                    (A, Q+1)   if A = 0 ∧ Q < Q_max
                    (A, Q)     if A = 0 ∧ Q = Q_max (reject)

  Complete: (A, Q) → (A, Q-1)  if Q > 0 (process queued)
                     (A+1, Q)  if Q = 0

利用率计算:
  Utilization = (Capacity - Avg(A)) / Capacity

等待时间估计:
  E[Wait] = λ × E[Service]² / (2 × (1 - ρ))

  其中:
    λ: 到达率
    E[Service]: 平均服务时间
    ρ: 系统负载 (λ × E[Service] / Capacity)

拒绝概率 (Erlang B 公式):
  P(reject) = (λ^C / C!) / (Σ_{k=0}^{C} λ^k / k!)

  其中 C 是容量
```

### 3.2 容量规划模型

```
最优容量计算:

目标:
  Minimize: Cost(Capacity)
  Subject to:
    P(reject) < threshold_reject
    E[latency] < threshold_latency
    Utilization > threshold_util

响应式扩容:
  Capacity(t+1) = Capacity(t) × (1 + α × (Load(t) - TargetLoad))

其中 α 是调整系数

预测式扩容:
  Capacity(t+Δt) = Predict(Load(t), Load(t-1), ..., Load(t-n))
```

---

## 4. Rust 实现

### 4.1 核心舱壁实现

```rust
use std::collections::VecDeque;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, Semaphore, oneshot};
use thiserror::Error;

/// 舱壁配置
#[derive(Debug, Clone)]
pub struct BulkheadConfig {
    /// 舱壁名称
    pub name: String,
    /// 最大并发数
    pub max_concurrent: usize,
    /// 最大队列大小
    pub max_queue_size: usize,
    /// 队列等待超时
    pub queue_wait_timeout: Duration,
    /// 执行超时
    pub execution_timeout: Duration,
}

impl Default for BulkheadConfig {
    fn default() -> Self {
        Self {
            name: "default".to_string(),
            max_concurrent: 10,
            max_queue_size: 100,
            queue_wait_timeout: Duration::from_secs(5),
            execution_timeout: Duration::from_secs(30),
        }
    }
}

/// 舱壁统计
#[derive(Debug, Default)]
pub struct BulkheadMetrics {
    pub total_executed: std::sync::atomic::AtomicU64,
    pub total_rejected: std::sync::atomic::AtomicU64,
    pub total_queued: std::sync::atomic::AtomicU64,
    pub total_queue_timeouts: std::sync::atomic::AtomicU64,
    pub total_execution_timeouts: std::sync::atomic::AtomicU64,
    pub current_in_use: std::sync::atomic::AtomicUsize,
    pub current_queued: std::sync::atomic::AtomicUsize,
}

/// 舱壁结构
pub struct Bulkhead {
    config: BulkheadConfig,
    /// 并发控制信号量
    semaphore: Arc<Semaphore>,
    /// 等待队列
    queue: Arc<Mutex<VecDeque<QueuedRequest>>>,
    /// 统计信息
    metrics: Arc<BulkheadMetrics>,
}

/// 队列中的请求
struct QueuedRequest {
    permit_tx: oneshot::Sender<tokio::sync::OwnedSemaphorePermit>,
    queued_at: Instant,
}

impl Bulkhead {
    /// 创建新的舱壁
    pub fn new(config: BulkheadConfig) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(config.max_concurrent)),
            queue: Arc::new(Mutex::new(VecDeque::with_capacity(config.max_queue_size))),
            metrics: Arc::new(BulkheadMetrics::default()),
            config,
        }
    }

    /// 执行操作（带舱壁隔离）
    pub async fn execute<F, Fut, T>(&self, operation: F) -> Result<T, BulkheadError>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        let start = Instant::now();

        // 尝试立即获取许可
        match self.semaphore.clone().try_acquire_owned() {
            Ok(permit) => {
                // 直接执行
                self.metrics.total_executed.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                self.metrics.current_in_use.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

                let result = self.execute_with_timeout(operation, permit).await;

                self.metrics.current_in_use.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
                self.process_queue().await;

                return result;
            }
            Err(_) => {
                // 需要排队
                self.metrics.total_queued.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
        }

        // 尝试加入队列
        let permit = self.enqueue_and_wait().await?;

        // 记录排队时间
        let queue_time = start.elapsed();
        if queue_time > self.config.queue_wait_timeout {
            self.metrics.total_queue_timeouts.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            drop(permit); // 释放许可
            self.process_queue().await;
            return Err(BulkheadError::QueueTimeout);
        }

        // 执行操作
        self.metrics.current_in_use.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

        let result = self.execute_with_timeout(operation, permit).await;

        self.metrics.current_in_use.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
        self.process_queue().await;

        result
    }

    /// 将请求加入队列并等待
    async fn enqueue_and_wait(&self) -> Result<tokio::sync::OwnedSemaphorePermit, BulkheadError> {
        let (permit_tx, permit_rx) = oneshot::channel();

        {
            let mut queue = self.queue.lock().await;

            if queue.len() >= self.config.max_queue_size {
                self.metrics.total_rejected.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                return Err(BulkheadError::BulkheadFull);
            }

            queue.push_back(QueuedRequest {
                permit_tx,
                queued_at: Instant::now(),
            });

            self.metrics.current_queued.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }

        // 等待许可
        match tokio::time::timeout(self.config.queue_wait_timeout, permit_rx).await {
            Ok(Ok(permit)) => {
                self.metrics.current_queued.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
                Ok(permit)
            }
            Ok(Err(_)) => {
                self.metrics.current_queued.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
                Err(BulkheadError::ChannelClosed)
            }
            Err(_) => {
                self.metrics.current_queued.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
                self.metrics.total_queue_timeouts.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                Err(BulkheadError::QueueTimeout)
            }
        }
    }

    /// 处理队列中的下一个请求
    async fn process_queue(&self) {
        let next_request = {
            let mut queue = self.queue.lock().await;
            queue.pop_front()
        };

        if let Some(request) = next_request {
            // 尝试获取许可并传递给队列中的请求
            if let Ok(permit) = self.semaphore.clone().try_acquire_owned() {
                let _ = request.permit_tx.send(permit);
            } else {
                // 如果无法获取许可，重新放回队列
                let mut queue = self.queue.lock().await;
                queue.push_front(request);
            }
        }
    }

    /// 带超时的执行
    async fn execute_with_timeout<F, Fut, T>(
        &self,
        operation: F,
        _permit: tokio::sync::OwnedSemaphorePermit,
    ) -> Result<T, BulkheadError>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        match tokio::time::timeout(self.config.execution_timeout, operation()).await {
            Ok(result) => Ok(result),
            Err(_) => {
                self.metrics.total_execution_timeouts.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                Err(BulkheadError::ExecutionTimeout)
            }
        }
    }

    /// 获取统计信息
    pub fn metrics(&self) -> &BulkheadMetrics {
        &self.metrics
    }

    /// 获取当前状态
    pub async fn status(&self) -> BulkheadStatus {
        BulkheadStatus {
            name: self.config.name.clone(),
            available_permits: self.semaphore.available_permits(),
            queued_requests: self.queue.lock().await.len(),
            max_concurrent: self.config.max_concurrent,
            max_queue_size: self.config.max_queue_size,
        }
    }
}

/// 舱壁状态
#[derive(Debug, Clone)]
pub struct BulkheadStatus {
    pub name: String,
    pub available_permits: usize,
    pub queued_requests: usize,
    pub max_concurrent: usize,
    pub max_queue_size: usize,
}

/// 舱壁错误类型
#[derive(Debug, Error)]
pub enum BulkheadError {
    #[error("Bulkhead is full, cannot accept more requests")]
    BulkheadFull,
    #[error("Queue wait timeout")]
    QueueTimeout,
    #[error("Execution timeout")]
    ExecutionTimeout,
    #[error("Channel closed")]
    ChannelClosed,
}

impl Clone for Bulkhead {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            semaphore: Arc::clone(&self.semaphore),
            queue: Arc::clone(&self.queue),
            metrics: Arc::clone(&self.metrics),
        }
    }
}
```

### 4.2 多舱壁管理器

```rust
use std::collections::HashMap;

/// 舱壁管理器
pub struct BulkheadManager {
    bulkheads: RwLock<HashMap<String, Arc<Bulkhead>>>,
    default_config: BulkheadConfig,
}

impl BulkheadManager {
    pub fn new(default_config: BulkheadConfig) -> Self {
        Self {
            bulkheads: RwLock::new(HashMap::new()),
            default_config,
        }
    }

    /// 注册舱壁
    pub async fn register(&self, config: BulkheadConfig) -> Arc<Bulkhead> {
        let bulkhead = Arc::new(Bulkhead::new(config.clone()));
        let mut bulkheads = self.bulkheads.write().await;
        bulkheads.insert(config.name.clone(), Arc::clone(&bulkhead));
        bulkhead
    }

    /// 获取舱壁
    pub async fn get(&self, name: &str) -> Option<Arc<Bulkhead>> {
        let bulkheads = self.bulkheads.read().await;
        bulkheads.get(name).cloned()
    }

    /// 执行操作（自动路由到对应舱壁）
    pub async fn execute<F, Fut, T>(
        &self,
        bulkhead_name: &str,
        operation: F,
    ) -> Result<T, BulkheadManagerError>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        let bulkhead = self.get(bulkhead_name).await
            .ok_or(BulkheadManagerError::BulkheadNotFound)?;

        bulkhead.execute(operation).await
            .map_err(BulkheadManagerError::BulkheadError)
    }

    /// 获取所有舱壁状态
    pub async fn all_statuses(&self) -> Vec<BulkheadStatus> {
        let bulkheads = self.bulkheads.read().await;
        let mut statuses = Vec::new();

        for bulkhead in bulkheads.values() {
            statuses.push(bulkhead.status().await);
        }

        statuses
    }
}

#[derive(Debug, Error)]
pub enum BulkheadManagerError {
    #[error("Bulkhead not found")]
    BulkheadNotFound,
    #[error("Bulkhead error: {0}")]
    BulkheadError(#[from] BulkheadError),
}
```

### 4.3 舱壁与断路器集成

```rust
/// 带断路器的舱壁
pub struct CircuitBreakerBulkhead {
    bulkhead: Arc<Bulkhead>,
    circuit_breaker: Arc<CircuitBreaker>,
}

impl CircuitBreakerBulkhead {
    pub fn new(bulkhead: Arc<Bulkhead>, circuit_breaker: Arc<CircuitBreaker>) -> Self {
        Self {
            bulkhead,
            circuit_breaker,
        }
    }

    pub async fn execute<F, Fut, T, E>(
        &self,
        operation: F,
    ) -> Result<T, CircuitBreakerBulkheadError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Debug + std::fmt::Display,
    {
        // 首先检查断路器
        self.circuit_breaker.check_state().await
            .map_err(|_| CircuitBreakerBulkheadError::CircuitOpen)?;

        // 通过舱壁执行
        let result = self.bulkhead.execute(|| async {
            operation().await
        }).await.map_err(CircuitBreakerBulkheadError::BulkheadError)?;

        // 记录结果
        match &result {
            Ok(_) => self.circuit_breaker.record_success().await,
            Err(_) => self.circuit_breaker.record_failure().await,
        }

        result.map_err(CircuitBreakerBulkheadError::OperationError)
    }
}

#[derive(Debug, Error)]
pub enum CircuitBreakerBulkheadError<E> {
    #[error("Circuit breaker is open")]
    CircuitOpen,
    #[error("Bulkhead error: {0}")]
    BulkheadError(#[from] BulkheadError),
    #[error("Operation error: {0}")]
    OperationError(E),
}
```

### 4.4 自适应舱壁

```rust
/// 自适应舱壁（根据负载动态调整容量）
pub struct AdaptiveBulkhead {
    inner: Arc<Bulkhead>,
    config: AdaptiveBulkheadConfig,
    current_capacity: AtomicUsize,
    load_history: Arc<RwLock<VecDeque<f64>>>,
}

#[derive(Debug, Clone)]
pub struct AdaptiveBulkheadConfig {
    pub min_capacity: usize,
    pub max_capacity: usize,
    pub target_latency: Duration,
    pub scale_up_threshold: f64,
    pub scale_down_threshold: f64,
}

impl AdaptiveBulkhead {
    pub fn new(base_config: BulkheadConfig, adaptive_config: AdaptiveBulkheadConfig) -> Self {
        let current_capacity = AtomicUsize::new(base_config.max_concurrent);

        Self {
            inner: Arc::new(Bulkhead::new(base_config)),
            config: adaptive_config,
            current_capacity,
            load_history: Arc::new(RwLock::new(VecDeque::with_capacity(100))),
        }
    }

    /// 更新容量（基于当前负载）
    pub async fn adjust_capacity(&self) {
        let history = self.load_history.read().await;
        if history.len() < 10 {
            return;
        }

        let avg_load: f64 = history.iter().sum::<f64>() / history.len() as f64;
        let current = self.current_capacity.load(std::sync::atomic::Ordering::Relaxed);

        let new_capacity = if avg_load > self.config.scale_up_threshold && current < self.config.max_capacity {
            // 负载高，扩容
            (current + 1).min(self.config.max_capacity)
        } else if avg_load < self.config.scale_down_threshold && current > self.config.min_capacity {
            // 负载低，缩容
            (current - 1).max(self.config.min_capacity)
        } else {
            current
        };

        if new_capacity != current {
            self.current_capacity.store(new_capacity, std::sync::atomic::Ordering::Relaxed);
            tracing::info!("Adaptive bulkhead capacity adjusted: {} -> {}", current, new_capacity);
        }
    }

    /// 记录当前负载
    pub async fn record_load(&self, load: f64) {
        let mut history = self.load_history.write().await;
        history.push_back(load);
        if history.len() > 100 {
            history.pop_front();
        }
    }
}
```

---

## 5. 形式化验证

### 5.1 隔离属性

```
舱壁隔离定理:

定理 1 (资源独立性):
  ∀bᵢ, bⱼ ∈ Bulkheads, i ≠ j.
    Resources(bᵢ) ∩ Resources(bⱼ) = ∅

定理 2 (故障隔离):
  □ (FailureIn(bᵢ) → □ Healthy(bⱼ)) for i ≠ j

定理 3 (容量界限):
  □ (0 ≤ Allocated(b) ≤ Capacity(b))

定理 4 (队列界限):
  □ (0 ≤ QueueSize(b) ≤ MaxQueueSize(b))
```

### 5.2 性能保证

```
性能定理:

等待时间界限:
  WaitTime ≤ QueueTimeout + ExecutionTimeout

吞吐量:
  Throughput ≤ Capacity / AverageServiceTime

拒绝率:
  P(Reject) = f(ArrivalRate, Capacity, ServiceTime)
            ≈ (λ^C / C!) / (Σ_{k=0}^{C} λ^k / k!)  (Erlang B)
```

---

## 6. 最佳实践

```
舱壁设计原则:

1. 按服务边界划分:
   - 关键服务独立舱壁
   - 非关键服务可共享

2. 按故障域划分:
   - 不同数据源独立
   - 第三方服务独立

3. 容量规划:
   - 基于历史峰值
   - 预留 20% 余量

4. 监控指标:
   - 利用率
   - 队列长度
   - 拒绝率
   - 等待时间

推荐配置:

| 场景          | 并发数 | 队列大小 | 超时  |
|---------------|--------|----------|-------|
| 核心服务      | 50-100 | 500-1000 | 30s   |
| 普通服务      | 20-50  | 200-500  | 10s   |
| 慢服务        | 5-10   | 50-100   | 60s   |
| 第三方 API    | 10-20  | 100-200  | 30s   |
```

---

## 7. 总结

| 特性 | 舱壁模式 | 优势 | 注意事项 |
|------|----------|------|----------|
| 资源隔离 | 独立线程池/连接池 | 故障不扩散 | 资源利用率可能降低 |
| 有限并发 | 信号量控制 | 防止过载 | 需合理设置容量 |
| 优雅降级 | 队列缓冲 | 吸收突发流量 | 设置队列上限 |
| 优先级 | 多舱壁调度 | 关键服务优先 | 避免饥饿 |

核心公式:

$$
\text{RejectProbability} = \frac{\lambda^C}{C!} \bigg/ \sum_{k=0}^{C} \frac{\lambda^k}{k!}
$$

$$
\text{Utilization} = \frac{\lambda \cdot E[S]}{C}
$$

$$
\text{AvgQueueLength} = \frac{\rho^{C+1}}{(C-1)!(C-\rho)^2} \cdot P_0
$$

其中 $\lambda$ 是到达率，$C$ 是容量，$E[S]$ 是平均服务时间，$\rho = \lambda E[S] / C$
