# 分布式架构选型决策树

> **创建日期**: 2026-02-23
> **最后更新**: 2026-02-23
> **状态**: ✅ 新建 (Phase 1 Week 8)
> **任务ID**: P1-W8-T1

---

## 决策树概览

```
构建分布式系统？
│
├── 需要事务一致性？
│   ├── 是 → 强一致性？
│   │   ├── 是 → 2PC/3PC + 外部协调器
│   │   └── 否 → 最终一致性
│   │       ├── 长事务？
│   │       │   ├── 是 → Saga模式
│   │       │   │   ├── 编排 → 协调器驱动 (Temporal/Cadence)
│   │       │   │   └── 编制 → 事件驱动 (Kafka + 消费者)
│   │       │   └── 补偿策略
│   │       │       ├── 向后补偿 → 标准Saga
│   │       │       └── 向前补偿 → 可交换更新
│   │       └── 短事务？
│   │           └── Outbox模式 + 消息代理
│   └── 否 → 无需事务
│
├── 读写负载分离？
│   ├── 是 → CQRS模式
│   │   ├── 同步更新 → 2PC
│   │   └── 异步更新 → 事件溯源
│   └── 否 → 统一模型
│
├── 容错要求高？
│   ├── 是 → 熔断器 (Circuit Breaker)
│   │   ├── 失败率阈值？
│   │   │   ├── >50% → 激进熔断
│   │   │   └── <50% → 保守熔断
│   │   └── 恢复策略
│   │       ├── 自动恢复 → 半开状态探测
│   │       └── 手动恢复 → 管理API
│   ├── 资源隔离 → Bulkhead模式
│   └── 重试策略
│       ├── 立即重试 → 简单循环
│       ├── 固定间隔 → tokio::time::interval
│       └── 指数退避 → backoff crate
│
└── 服务发现？
    ├── 集中式 → Consul/etcd
    │   ├── 健康检查
    │   │   ├── HTTP检查
    │   │   ├── TCP检查
    │   │   └── 自定义脚本
    │   └── 一致性要求
    │       ├── CP → Consul RAFT
    │       └── AP → etcd
    └── 去中心化 → gossip协议
        ├── 种子节点配置
        └── 传播策略
            ├── 反熵 → 周期性全同步
            └── 谣言传播 → 事件驱动
```

---

## 详细决策路径

### 路径1: Saga事务模式

```rust
// 决策条件: 长事务 + 最终一致性
// Rust实现示例

use std::future::Future;
use std::pin::Pin;

// Saga定义
trait Saga<T, E> {
    fn execute(&self) -> Pin<Box<dyn Future<Output = Result<T, E>> + '_>>;
    fn compensate(&self) -> Pin<Box<dyn Future<Output = Result<(), E>> + '_>>;
}

// 编排式Saga (Orchestration)
struct OrchestratedSaga {
    steps: Vec<Box<dyn Saga<(), SagaError>>>,
    compensations: Vec<Box<dyn Saga<(), SagaError>>>,
}

impl OrchestratedSaga {
    async fn run(&self) -> Result<(), SagaError> {
        let mut completed = 0;
        for (i, step) in self.steps.iter().enumerate() {
            match step.execute().await {
                Ok(_) => completed += 1,
                Err(e) => {
                    // 补偿已完成的步骤
                    for j in (0..completed).rev() {
                        self.compensations[j].compensate().await?;
                    }
                    return Err(e);
                }
            }
        }
        Ok(())
    }
}

// 编制式Saga (Choreography) - 事件驱动
struct ChoreographedSaga {
    event_bus: EventBus,
}

impl ChoreographedSaga {
    async fn handle_event(&self, event: DomainEvent) {
        match event {
            DomainEvent::OrderCreated(order) => {
                // 发布ReserveInventory事件
                self.event_bus.publish(Event::ReserveInventory(order)).await;
            }
            DomainEvent::InventoryReserved(order) => {
                // 发布ProcessPayment事件
                self.event_bus.publish(Event::ProcessPayment(order)).await;
            }
            DomainEvent::PaymentFailed(order) => {
                // 发布ReleaseInventory事件 (补偿)
                self.event_bus.publish(Event::ReleaseInventory(order)).await;
            }
            // ...
        }
    }
}
```

**适用场景**:
- 电商订单处理
- 金融转账
- 库存扣减+支付

**Rust crates**:
- `saga` - Saga模式实现
- `temporal-sdk` - Temporal工作流
- `kafka` - 事件驱动编制

---

### 路径2: CQRS模式

```rust
// 决策条件: 读写负载分离 + 复杂查询

// 命令端 (写模型)
struct OrderCommandHandler {
    event_store: EventStore,
}

impl OrderCommandHandler {
    async fn create_order(&self, cmd: CreateOrder) -> Result<OrderId, Error> {
        let order = Order::new(cmd)?;
        let events = order.into_events();
        self.event_store.append(events).await?;
        Ok(order.id())
    }
}

// 查询端 (读模型)
struct OrderQueryHandler {
    read_db: ReadDatabase,
}

impl OrderQueryHandler {
    async fn get_order_summary(&self, id: OrderId) -> Result<OrderSummary, Error> {
        // 优化的读模型，直接查询物化视图
        self.read_db.query("SELECT * FROM order_summary WHERE id = ?", id).await
    }
}

// 投影器 - 同步读写模型
struct OrderProjector;

impl Projector for OrderProjector {
    fn project(&self, event: &Event) -> Vec<SqlQuery> {
        match event {
            Event::OrderCreated(e) => vec![
                sql!("INSERT INTO order_summary (id, status, total) VALUES (?, ?, ?)",
                     e.id, "pending", e.total)
            ],
            Event::OrderPaid(e) => vec![
                sql!("UPDATE order_summary SET status = ? WHERE id = ?",
                     "paid", e.id)
            ],
            // ...
        }
    }
}
```

**适用场景**:
- 高并发读场景
- 复杂报表查询
- 事件溯源系统

**Rust crates**:
- `cqrs` - CQRS框架
- `eventstore` - EventStoreDB客户端
- `sqlx` - 异步SQL

---

### 路径3: 熔断器模式

```rust
// 决策条件: 容错要求高 + 防止级联故障

use std::sync::atomic::{AtomicU8, Ordering};
use std::time::{Duration, Instant};

enum CircuitState {
    Closed,      // 正常，请求通过
    Open,        // 熔断，快速失败
    HalfOpen,    // 半开，试探性请求
}

struct CircuitBreaker {
    state: AtomicU8,
    failure_count: AtomicUsize,
    success_count: AtomicUsize,
    last_failure_time: Mutex<Option<Instant>>,
    config: CircuitConfig,
}

struct CircuitConfig {
    failure_threshold: usize,      // 熔断阈值
    success_threshold: usize,      // 恢复阈值
    timeout_duration: Duration,    // 熔断持续时间
}

impl CircuitBreaker {
    async fn call<F, T, E>(&self, f: F) -> Result<T, CircuitError<E>>
    where
        F: Future<Output = Result<T, E>>,
    {
        match self.state() {
            CircuitState::Open => {
                // 检查是否应该进入半开状态
                if self.should_attempt_reset() {
                    self.set_state(CircuitState::HalfOpen);
                } else {
                    return Err(CircuitError::Open);
                }
            }
            CircuitState::HalfOpen => {
                // 限制并发试探请求
                if !self.acquire_half_open_slot() {
                    return Err(CircuitError::Open);
                }
            }
            CircuitState::Closed => {}
        }

        // 执行实际请求
        match f.await {
            Ok(result) => {
                self.on_success();
                Ok(result)
            }
            Err(e) => {
                self.on_failure();
                Err(CircuitError::Inner(e))
            }
        }
    }

    fn on_success(&self) {
        match self.state() {
            CircuitState::HalfOpen => {
                let success = self.success_count.fetch_add(1, Ordering::SeqCst);
                if success + 1 >= self.config.success_threshold {
                    self.set_state(CircuitState::Closed);
                    self.failure_count.store(0, Ordering::SeqCst);
                }
            }
            CircuitState::Closed => {
                self.failure_count.store(0, Ordering::SeqCst);
            }
            _ => {}
        }
    }

    fn on_failure(&self) {
        let failures = self.failure_count.fetch_add(1, Ordering::SeqCst);
        *self.last_failure_time.lock().unwrap() = Some(Instant::now());
        
        if failures + 1 >= self.config.failure_threshold {
            self.set_state(CircuitState::Open);
        }
    }
}
```

**适用场景**:
- 微服务调用
- 外部API调用
- 数据库访问

**Rust crates**:
- `resilience4j` - 熔断器实现
- `tokio-circuit-breaker` - Tokio集成
- `backoff` - 重试策略

---

## 决策矩阵

| 需求特征 | 推荐模式 | 一致性 | 复杂度 | 延迟 |
| :--- | :--- | :--- | :--- | :--- |
| 强一致性 + 短事务 | 2PC | 强 | 高 | 高 |
| 最终一致 + 长事务 | Saga | 最终 | 中 | 低 |
| 读写分离 + 复杂查询 | CQRS | 最终 | 高 | 低(读) |
| 高可用 + 容错 | 熔断器 | - | 低 | 低 |
| 资源隔离 | Bulkhead | - | 中 | 低 |
| 服务发现(CP) | Consul | - | 中 | 中 |
| 服务发现(AP) | Gossip | - | 中 | 低 |

---

## 组合模式

```
复杂分布式系统通常组合多个模式:

示例: 电商订单系统
├── 订单服务
│   ├── Saga (订单流程)
│   ├── 熔断器 (调用支付服务)
│   └── 重试 (网络超时)
├── 商品服务
│   ├── CQRS (商品搜索)
│   └── 缓存 (Redis)
├── 支付服务
│   ├── 2PC (银行接口)
│   └── 幂等性 (防重)
└── 基础设施
    ├── Consul (服务发现)
    └── Bulkhead (资源隔离)
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-23
**状态**: ✅ 已完成 - 分布式架构选型决策树
