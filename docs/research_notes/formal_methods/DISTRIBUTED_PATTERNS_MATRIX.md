# 分布式模式矩阵

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **状态**: ✅ 已扩展
> **版本**: Rust 1.93.0+ (Edition 2024)

---

## 概述

分布式模式矩阵系统梳理微服务架构中的核心分布式模式，包括一致性、容错、通信和集成模式，为Rust分布式系统设计提供参考。

---

## 核心模式对比矩阵

### 一致性模式

| 模式 | 一致性 | 可用性 | 分区容错 | 复杂度 | 延迟 | Rust实现 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Saga** | 最终 | 高 | 高 | 中 | 低 | 事务协调器+补偿 |
| **2PC** | 强 | 低 | 低 | 高 | 高 | 分布式锁 |
| **TCC** | 最终 | 高 | 高 | 高 | 低 | Try-Confirm-Cancel |
| **Event Sourcing** | 最终 | 高 | 高 | 高 | 低 | Event Store |
| **CQRS** | 最终 | 高 | 高 | 高 | 低 | 读写分离 |
| **Outbox** | 最终 | 高 | 高 | 中 | 低 | 事务+消息表 |

### 容错模式

| 模式 | 故障检测 | 恢复策略 | 状态管理 | 性能影响 | Rust生态 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Circuit Breaker** | 连续失败计数 | 快速失败 | 三种状态 | 低 | `backoff` crate |
| **Retry** | 异常捕获 | 指数退避 | 重试计数 | 中 | `backoff` crate |
| **Timeout** | 时间限制 | 中断执行 | 超时设置 | 低 | `tokio::time` |
| **Bulkhead** | 资源限制 | 隔离失败 | 配额管理 | 中 | 信号量 |
| **Rate Limiter** | 流量监控 | 限流/排队 | 令牌桶 | 低 | `governor` crate |
| **Fallback** | 主路径失败 | 降级服务 | 备用策略 | 低 | 模式实现 |

### 通信模式

| 模式 | 同步性 | 耦合度 | 可靠性 | 扩展性 | Rust实现 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **REST API** | 同步 | 松 | HTTP依赖 | 高 | `axum`, `actix-web` |
| **gRPC** | 同步/流 | 松 | HTTP/2 | 高 | `tonic` |
| **Message Queue** | 异步 | 松 | 持久化 | 高 | `lapin`, `rdkafka` |
| **Event Bus** | 异步 | 极松 | 至少一次 | 高 | NATS, Redis |
| **Pub/Sub** | 异步 | 极松 | 可配置 | 高 | `redis`, `nats` |
| **RPC** | 同步 | 紧 | 网络依赖 | 中 | `tarpc`, `jsonrpc` |

---

## 模式组合矩阵

### 场景-模式映射

| 场景 | 推荐模式组合 | 理由 |
| :--- | :--- | :--- |
| 订单处理 | Saga + Outbox + Retry | 最终一致，可靠投递 |
| 读多写少 | CQRS + Cache + Rate Limiter | 读优化，流量控制 |
| 实时通信 | Pub/Sub + Circuit Breaker | 低延迟，容错 |
| 数据同步 | Event Sourcing + Message Queue | 审计，可靠传输 |
| 微服务网关 | Rate Limiter + Timeout + Fallback | 保护后端，降级 |
| 批处理 | Bulkhead + Retry + Timeout | 资源隔离，可靠性 |

### CAP权衡矩阵

```
         ┌─────────────┐
         │  Consistency │
         │    (一致性)   │
         └──────┬──────┘
                │
    ┌───────────┼───────────┐
    │           │           │
    ▼           │           ▼
┌───────┐       │       ┌───────┐
│  CP   │       │       │  AP   │
│  2PC  │       │       │ Saga  │
│ Paxos │       │       │ CQRS  │
└───────┘       │       └───────┘
                │
         ┌──────┴──────┐
         │ Partition   │
         │ Tolerance   │
         └─────────────┘
```

---

## Rust实现指南

### Saga模式

```rust
// Saga协调器
pub struct Saga {
    steps: Vec<SagaStep>,
    compensations: Vec<Compensation>,
}

pub struct SagaStep {
    name: String,
    action: Box<dyn Fn() -> Result<(), Error> + Send>,
    compensation: Box<dyn Fn() -> Result<(), Error> + Send>,
}

impl Saga {
    pub async fn execute(&mut self) -> Result<(), SagaError> {
        let executed = Vec::new();

        for step in &self.steps {
            match (step.action)().await {
                Ok(_) => executed.push(&step.compensation),
                Err(e) => {
                    // 执行补偿
                    for compensation in executed.iter().rev() {
                        compensation().await.ok(); // 补偿不应失败
                    }
                    return Err(SagaError::StepFailed(step.name.clone(), e));
                }
            }
        }

        Ok(())
    }
}

// 使用
let mut saga = Saga::new();
saga.add_step(
    "deduct_inventory",
    || inventory_service.deduct().await,
    || inventory_service.restore().await,
);
saga.add_step(
    "process_payment",
    || payment_service.charge().await,
    || payment_service.refund().await,
);
saga.execute().await?;
```

### Circuit Breaker

```rust
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::{Duration, Instant};

pub enum CircuitState {
    Closed,      // 正常
    Open,        // 熔断
    HalfOpen,    // 试探
}

pub struct CircuitBreaker {
    state: CircuitState,
    failure_count: AtomicU32,
    last_failure_time: Option<Instant>,
    threshold: u32,
    timeout: Duration,
}

impl CircuitBreaker {
    pub async fn call<F, Fut, T>(&mut self, f: F) -> Result<T, CircuitError>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<T, Error>>,
    {
        match self.state {
            CircuitState::Open => {
                if self.should_attempt_reset() {
                    self.state = CircuitState::HalfOpen;
                } else {
                    return Err(CircuitError::Open);
                }
            }
            _ => {}
        }

        match f().await {
            Ok(result) => {
                self.on_success();
                Ok(result)
            }
            Err(e) => {
                self.on_failure();
                Err(CircuitError::Underlying(e))
            }
        }
    }

    fn on_failure(&mut self) {
        let count = self.failure_count.fetch_add(1, Ordering::SeqCst);
        if count + 1 >= self.threshold {
            self.state = CircuitState::Open;
            self.last_failure_time = Some(Instant::now());
        }
    }

    fn on_success(&mut self) {
        self.failure_count.store(0, Ordering::SeqCst);
        self.state = CircuitState::Closed;
    }
}
```

### Retry模式

```rust
use backoff::{ExponentialBackoff, future::retry};

pub async fn with_retry<F, Fut, T>(operation: F) -> Result<T, Error>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, Error>>,
{
    let backoff = ExponentialBackoff {
        initial_interval: Duration::from_millis(100),
        max_interval: Duration::from_secs(10),
        max_elapsed_time: Some(Duration::from_secs(60)),
        ..Default::default()
    };

    retry(backoff, || async {
        operation().await.map_err(|e| backoff::Error::transient(e))
    }).await
}

// 使用
let result = with_retry(|| async {
    reqwest::get("https://api.example.com/data").await
}).await?;
```

---

## 反模式警示

| 反模式 | 问题 | 解决方案 |
| :--- | :--- | :--- |
| 分布式事务滥用 | 性能差，死锁 | Saga模式 |
| 超时设置不当 | 级联故障 | 自适应超时 |
| 重试风暴 | 雪崩效应 | 指数退避+抖动 |
| 同步调用链 | 延迟累积 | 异步+事件驱动 |
| 单点故障 | 可用性低 | 冗余+故障转移 |

---

## 形式化验证视角

| 模式 | 可验证属性 | 验证方法 |
| :--- | :--- | :--- |
| Saga | 补偿完整性 | 模型检测 |
| Circuit Breaker | 状态转换正确性 | 状态机验证 |
| Rate Limiter | 流量约束 | 不变式检查 |
| 2PC | 原子性 | TLA+ |

---

## 推荐技术栈

```rust
// 完整分布式Rust栈
[dependencies]
# Web框架
axum = "0.7"           # HTTP服务
tonic = "0.12"         # gRPC

# 消息队列
lapin = "2.3"          # AMQP/RabbitMQ
rdkafka = "0.36"       # Kafka
nats = "0.25"          # NATS

# 容错
backoff = { version = "0.4", features = ["tokio"] }
/governor = "0.4"       # 限流

# 分布式追踪
opentelemetry = "0.24"
tracing = "0.1"

# 序列化
serde = { version = "1.0", features = ["derive"] }
prost = "0.13"         # Protocol Buffers
```

---

## 分布式模式对比

| 模式 | 一致性 | 可用性 | 分区容错 | 复杂度 | 延迟 | Rust实现 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Saga** | 最终 | 高 | 高 | 中 | 低 | Result链+补偿 |
| **CQRS** | 最终 | 高 | 高 | 高 | 低 | Event Store |
| **Event Sourcing** | 最终 | 高 | 高 | 高 | 低 | eventstore crate |
| **Circuit Breaker** | - | 高 | 高 | 低 | 低 | 状态机实现 |
| **Bulkhead** | - | 高 | 高 | 低 | 低 | Semaphore |
| **Retry** | - | 高 | 高 | 低 | 中 | backoff crate |
| **Timeout** | - | 中 | 高 | 低 | 低 | tokio::time |
| **Outbox** | 最终 | 高 | 高 | 中 | 低 | 事务+消息表 |
| **2PC** | 强 | 低 | 低 | 高 | 高 | 协调器实现 |

---

## 模式适用场景

| 场景 | 推荐模式 | 理由 |
| :--- | :--- | :--- |
| 长事务 | Saga | 分解+补偿 |
| 读写分离 | CQRS | 优化查询 |
| 容错 | Circuit Breaker | 防止级联故障 |
| 资源隔离 | Bulkhead | 限制影响范围 |
| 瞬时故障 | Retry | 自动恢复 |
| 消息可靠投递 | Outbox | 保证送达 |

---

## CAP权衡

```
Saga/CQRS/Event Sourcing → AP (可用+分区容忍)
2PC → CP (一致+分区容忍)
```

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 分布式模式矩阵完整版
