# 故障模型语义 (Failure Models Semantics)

## 目录

- [故障模型语义 (Failure Models Semantics)](#故障模型语义-failure-models-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 故障分类](#2-故障分类)
    - [2.1 故障类型谱系](#21-故障类型谱系)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 故障检测器](#3-故障检测器)
    - [3.1 故障检测器分类](#31-故障检测器分类)
    - [3.2 Rust 实现](#32-rust-实现)
  - [4. 超时机制](#4-超时机制)
    - [4.1 超时设计原则](#41-超时设计原则)
  - [5. 故障恢复策略](#5-故障恢复策略)
    - [5.1 重启策略](#51-重启策略)
    - [5.2 检查点与恢复](#52-检查点与恢复)
  - [6. 容错设计模式](#6-容错设计模式)
    - [6.1 断路器模式](#61-断路器模式)
    - [6.2 舱壁隔离](#62-舱壁隔离)
  - [7. 形式化保证](#7-形式化保证)
    - [7.1 容错系统属性](#71-容错系统属性)
  - [8. 总结](#8-总结)

## 1. 引言

理解分布式系统中的故障模型是设计容错系统的基础。
本文档深入分析各种故障模型的形式化定义、检测机制和 Rust 实践。

---

## 2. 故障分类

### 2.1 故障类型谱系

```
故障类型（从良性到恶性）:

┌──────────────────────────────────────────────────────────────┐
│  故障类型              描述                      可检测性     │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│  Crash-Stop        进程停止响应                容易          │
│  (崩溃停止)        不再执行任何操作                          │
│                                                              │
│  Crash-Recovery    进程崩溃后可能恢复          中等          │
│  (崩溃恢复)        恢复后可以继续执行                        │
│                                                              │
│  Omission          进程遗漏某些消息            中等          │
│  (遗漏)            发送或接收遗漏                            │
│                                                              │
│  Timing            进程响应但超时              困难          │
│  (时序)            快慢不确定                                │
│                                                              │
│  Byzantine         进程可能任意行为            非常困难      │
│  (拜占庭)          包括恶意行为                              │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

### 2.2 形式化定义

```
故障模型形式化:

崩溃停止 (Crash-Stop):
  □ (Failed(p) → ◇□ ¬Responds(p))

  一旦失败，永远停止响应

崩溃恢复 (Crash-Recovery):
  □ (Failed(p) → ◇ (Recovered(p) ∨ ◇□ Failed(p)))

  可能恢复，也可能永久失败

遗漏故障 (Omission):
  ◇ (Send(m) ∧ ¬Deliver(m))

  发送的消息未被送达

时序故障 (Timing):
  ResponseTime(p) > Expected(p) + Δ

  响应时间超出预期

拜占庭故障 (Byzantine):
  □ (Byzantine(p) → ArbitraryBehavior(p))

  任意行为，包括恶意
```

---

## 3. 故障检测器

### 3.1 故障检测器分类

```
故障检测器属性:

完备性 (Completeness):
  强完备性: ◇ Failed(p) → ◇ Suspect(p)
            最终每个崩溃进程被所有正确进程怀疑

  弱完备性: ◇ Failed(p) → ◇ ∃q. Suspect(q, p)
            最终每个崩溃进程被某个正确进程怀疑

准确性 (Accuracy):
  强准确性: □ ¬Failed(p) → □ ¬Suspect(p)
            没有崩溃的进程永不被怀疑

  弱准确性: □ ¬Failed(p) → ◇□ ¬Suspect(p)
            没有崩溃的进程最终不被怀疑

失效检测器类型:
  完美 (Perfect):   强完备 + 强准确
  最终完美:          强完备 + 最终强准确
  强 (Strong):      强完备 + 弱准确
  弱 (Weak):        弱完备 + 弱准确
```

### 3.2 Rust 实现

```rust
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use std::time::{Duration, Instant};
use tokio::time::{interval, timeout};

// 故障检测器 trait
trait FailureDetector {
    fn monitor(&self, node_id: NodeId);
    fn unmonitor(&self, node_id: NodeId);
    fn is_suspected(&self, node_id: NodeId) -> bool;
    fn suspect_stream(&self) -> impl Stream<Item = (NodeId, Suspicion)>;
}

// 基于心跳的故障检测器
struct HeartbeatFailureDetector {
    heartbeats: Arc<DashMap<NodeId, Instant>>,
    suspects: Arc<DashMap<NodeId, SuspicionLevel>>,
    timeout: Duration,
    phi_threshold: f64,  // φ-accrual 检测器阈值
}

enum SuspicionLevel {
    Healthy,
    Suspected(Instant),
    Failed,
}

impl HeartbeatFailureDetector {
    fn new(timeout: Duration) -> Self {
        Self {
            heartbeats: Arc::new(DashMap::new()),
            suspects: Arc::new(DashMap::new()),
            timeout,
            phi_threshold: 8.0,
        }
    }

    // 接收心跳
    fn heartbeat(&self, from: NodeId) {
        self.heartbeats.insert(from, Instant::now());
        self.suspects.insert(from, SuspicionLevel::Healthy);
    }

    // 检查故障
    async fn check_failures(&self) {
        let now = Instant::now();

        for entry in self.heartbeats.iter() {
            let node_id = *entry.key();
            let last_heartbeat = *entry.value();
            let elapsed = now.duration_since(last_heartbeat);

            if elapsed > self.timeout {
                // 超过超时时间，标记为怀疑
                let current = self.suspects
                    .get(&node_id)
                    .map(|s| matches!(s, SuspicionLevel::Healthy))
                    .unwrap_or(true);

                if current {
                    self.suspects.insert(node_id, SuspicionLevel::Suspected(now));
                    tracing::warn!("Node {} suspected failed", node_id);
                }
            }

            // 检查是否确认故障
            if let Some(suspicion) = self.suspects.get(&node_id) {
                if let SuspicionLevel::Suspected(since) = *suspicion {
                    if now.duration_since(since) > self.timeout * 2 {
                        self.suspects.insert(node_id, SuspicionLevel::Failed);
                        tracing::error!("Node {} confirmed failed", node_id);
                    }
                }
            }
        }
    }

    // 启动检测循环
    async fn run(self: Arc<Self>) {
        let mut ticker = interval(Duration::from_secs(1));

        loop {
            ticker.tick().await;
            self.check_failures().await;
        }
    }
}

// φ-accrual 故障检测器（自适应）
struct PhiAccrualFailureDetector {
    // 心跳间隔采样窗口
    samples: Arc<DashMap<NodeId, VecDeque<Duration>>>,
    window_size: usize,
    phi_threshold: f64,
}

impl PhiAccrualFailureDetector {
    fn compute_phi(&self, node_id: NodeId) -> f64 {
        let samples = self.samples.get(&node_id)?;
        if samples.len() < 2 {
            return 0.0;
        }

        // 计算均值和标准差
        let mean: f64 = samples.iter()
            .map(|d| d.as_secs_f64())
            .sum::<f64>() / samples.len() as f64;

        let variance: f64 = samples.iter()
            .map(|d| (d.as_secs_f64() - mean).powi(2))
            .sum::<f64>() / samples.len() as f64;

        let std_dev = variance.sqrt();

        // 计算 φ 值
        let last = self.last_heartbeat(node_id)?;
        let elapsed = Instant::now().duration_since(last).as_secs_f64();

        // φ = -log10(1 - F(elapsed))
        // 其中 F 是正态分布的累积分布函数
        let phi = -((1.0 - Self::cdf(elapsed, mean, std_dev)).log10());

        Some(phi)
    }

    fn cdf(x: f64, mean: f64, std_dev: f64) -> f64 {
        use statrs::distribution::{Normal, ContinuousCDF};
        let normal = Normal::new(mean, std_dev).unwrap();
        normal.cdf(x)
    }

    fn is_suspected(&self, node_id: NodeId) -> bool {
        self.compute_phi(node_id)
            .map(|phi| phi >= self.phi_threshold)
            .unwrap_or(true)
    }
}
```

---

## 4. 超时机制

### 4.1 超时设计原则

```rust
// 自适应超时
struct AdaptiveTimeout {
    base_timeout: Duration,
    min_timeout: Duration,
    max_timeout: Duration,
    ewma_factor: f64,

    // 历史响应时间
    response_times: VecDeque<Duration>,
    current_estimate: Duration,
}

impl AdaptiveTimeout {
    fn new(base: Duration) -> Self {
        Self {
            base_timeout: base,
            min_timeout: base / 10,
            max_timeout: base * 10,
            ewma_factor: 0.2,
            response_times: VecDeque::with_capacity(100),
            current_estimate: base,
        }
    }

    fn update(&mut self, actual: Duration) {
        // EWMA 更新
        let actual_secs = actual.as_secs_f64();
        let current_secs = self.current_estimate.as_secs_f64();

        let new_estimate = self.ewma_factor * actual_secs
            + (1.0 - self.ewma_factor) * current_secs;

        self.current_estimate = Duration::from_secs_f64(new_estimate);

        // 保存样本
        self.response_times.push_back(actual);
        if self.response_times.len() > 100 {
            self.response_times.pop_front();
        }
    }

    fn current_timeout(&self) -> Duration {
        // 超时 = 估计值 + 3 * 标准差
        let mean = self.current_estimate.as_secs_f64();
        let variance = self.response_times.iter()
            .map(|d| (d.as_secs_f64() - mean).powi(2))
            .sum::<f64>() / self.response_times.len().max(1) as f64;
        let std_dev = variance.sqrt();

        let timeout_secs = mean + 3.0 * std_dev;
        let timeout = Duration::from_secs_f64(timeout_secs);

        timeout.clamp(self.min_timeout, self.max_timeout)
    }
}

// 分层超时
struct TieredTimeout {
    tiers: Vec<(usize, Duration)>, // (重试次数, 超时时间)
}

impl TieredTimeout {
    fn exponential_backoff(
        base: Duration,
        max: Duration,
        multiplier: f64,
    ) -> Self {
        let mut tiers = vec![];
        let mut current = base;

        for i in 0..10 {
            tiers.push((i, current));
            current = min(
                Duration::from_secs_f64(current.as_secs_f64() * multiplier),
                max,
            );
        }

        Self { tiers }
    }

    fn timeout_for_attempt(&self, attempt: usize) -> Duration {
        self.tiers.iter()
            .find(|(a, _)| *a == attempt)
            .map(|(_, t)| *t)
            .unwrap_or(self.tiers.last().unwrap().1)
    }
}
```

---

## 5. 故障恢复策略

### 5.1 重启策略

```rust
// 监督者模式 (Supervisor Pattern)
enum RestartStrategy {
    OneForOne,    // 一个子进程失败，只重启它
    OneForAll,    // 一个子进程失败，重启所有
    RestForOne,   // 一个子进程失败，重启它和它之后启动的
}

enum RestartIntensity {
    Permanent,    // 总是重启
    Transient,    // 非正常退出时重启
    Temporary,    // 永不重启
}

struct Supervisor {
    children: Vec<ChildSpec>,
    strategy: RestartStrategy,
    max_restarts: usize,
    restart_window: Duration,
    restart_history: VecDeque<Instant>,
}

struct ChildSpec {
    id: String,
    start_fn: Box<dyn Fn() -> Box<dyn Process>>,
    restart: RestartIntensity,
}

impl Supervisor {
    async fn handle_child_failure(&mut self, child_id: &str, exit_reason: ExitReason) {
        // 检查重启频率
        if self.too_many_restarts() {
            tracing::error!("Supervisor {} exceeded max restarts", self.id);
            self.terminate_all().await;
            return;
        }

        match self.strategy {
            RestartStrategy::OneForOne => {
                self.restart_child(child_id).await;
            }
            RestartStrategy::OneForAll => {
                self.restart_all().await;
            }
            RestartStrategy::RestForOne => {
                self.restart_from(child_id).await;
            }
        }
    }

    fn too_many_restarts(&self) -> bool {
        let now = Instant::now();
        let recent: Vec<_> = self.restart_history.iter()
            .filter(|t| now.duration_since(**t) < self.restart_window)
            .collect();

        recent.len() >= self.max_restarts
    }
}
```

### 5.2 检查点与恢复

```rust
// 检查点机制
trait Checkpointable {
    type State: Serialize + DeserializeOwned;

    fn checkpoint(&self) -> Self::State;
    fn restore(&mut self, state: Self::State);
}

struct CheckpointManager<P: Checkpointable> {
    process: P,
    storage: Arc<dyn CheckpointStorage>,
    interval: Duration,
    last_checkpoint: Option<CheckpointId>,
}

impl<P: Checkpointable> CheckpointManager<P> {
    async fn take_checkpoint(&mut self) -> Result<CheckpointId, Error> {
        let state = self.process.checkpoint();
        let data = serialize(&state)?;

        let id = generate_checkpoint_id();
        self.storage.store(id, data).await?;
        self.last_checkpoint = Some(id);

        tracing::info!("Checkpoint {} taken", id);
        Ok(id)
    }

    async fn recover(&mut self) -> Result<(), Error> {
        let id = self.last_checkpoint
            .or_else(|| self.storage.find_latest())
            .ok_or(Error::NoCheckpoint)?;

        let data = self.storage.load(id).await?;
        let state = deserialize(&data)?;

        self.process.restore(state);

        tracing::info!("Recovered from checkpoint {}", id);
        Ok(())
    }
}
```

---

## 6. 容错设计模式

### 6.1 断路器模式

```rust
// 已在前文覆盖，此处略
```

### 6.2 舱壁隔离

```rust
// Bulkhead 模式 - 资源隔离
struct Bulkhead {
    name: String,
    max_concurrent: usize,
    max_queue: usize,
    semaphore: Arc<Semaphore>,
    queue: Arc<Mutex<VecDeque<oneshot::Sender<()>>>>,
}

impl Bulkhead {
    async fn execute<F, Fut, T>(&self, f: F) -> Result<T, BulkheadError>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = T>,
    {
        // 尝试获取许可
        match self.semaphore.try_acquire() {
            Ok(permit) => {
                // 立即执行
                let result = f().await;
                drop(permit);
                Ok(result)
            }
            Err(_) => {
                // 加入队列
                let (tx, rx) = oneshot::channel();
                {
                    let mut queue = self.queue.lock().await;
                    if queue.len() >= self.max_queue {
                        return Err(BulkheadError::QueueFull);
                    }
                    queue.push_back(tx);
                }

                // 等待队列
                rx.await.map_err(|_| BulkheadError::Rejected)?;

                // 获取许可并执行
                let permit = self.semaphore.acquire().await.unwrap();
                let result = f().await;
                drop(permit);

                // 通知队列中的下一个
                self.process_queue().await;

                Ok(result)
            }
        }
    }
}
```

---

## 7. 形式化保证

### 7.1 容错系统属性

```
容错属性:

可用性 (Availability):
  ◇□ Available(system)

  系统最终总是可用

可靠性 (Reliability):
  □ (Failure → ◇ Recovery)

  故障最终导致恢复

安全性 (Safety):
  □ (¬BadState)

  永远不入坏状态

活性 (Liveness):
  ◇ GoodState

  最终达到好状态
```

---

## 8. 总结

| 故障类型 | 检测难度 | 处理策略 |
|----------|----------|----------|
| Crash-Stop | 低 | 心跳检测 + 重启 |
| Crash-Recovery | 中 | 检查点 + 重连 |
| Omission | 中 | 重传 + 超时 |
| Timing | 高 | 自适应超时 |
| Byzantine | 很高 | 多数派投票 |

关键公式:

$$
\text{FaultTolerance} = \text{Detection} \times \text{Recovery} \times \text{Redundancy}
$$
