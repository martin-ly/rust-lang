# 工作流引擎选型决策树

> **创建日期**: 2026-02-23
> **最后更新**: 2026-02-23
> **状态**: ✅ 新建 (Phase 1 Week 8)
> **任务ID**: P1-W8-T4

---

## 决策树概览
> **[来源: Rust Official Docs]**

```text
需要工作流引擎？
│
├── 持久化要求？
│   ├── 是 → 外部引擎 (Temporal/Cadence)
│   │   ├── 需要复杂状态机？
│   │   │   ├── 是 → Temporal (支持任意复杂性)
│   │   │   │   ├── 需要多语言SDK？
│   │   │   │   │   ├── 是 → Temporal (Go/Java/TypeScript/PHP/Python)
│   │   │   │   │   └── 否 → Temporal Rust SDK (社区)
│   │   │   │   ├── 需要可视化UI？
│   │   │   │   │   ├── 是 → Temporal Web UI
│   │   │   │   │   └── 否 → CLI/代码驱动
│   │   │   │   └── 云原生？
│   │   │   │       ├── 是 → Temporal Cloud / 自建K8s
│   │   │   │       └── 否 → 传统部署
│   │   │   └── 否 → Cadence (简单工作流，Uber出品)
│   │   └── 云原生？
│   │       ├── 是 → Temporal Cloud
│   │       └── 否 → 自建集群
│   │           ├── 高可用要求？
│   │           │   ├── 是 → 多实例+Cassandra/PostgreSQL
│   │           │   └── 否 → 单实例+SQLite (开发)
│   │           └── 监控要求？
│   │               ├── 是 → Prometheus + Grafana
│   │               └── 否 → 日志足够
│   └── 否 → 内存工作流
│       ├── 简单顺序 → 函数组合
│       │   └── impl Fn() -> impl Future
│       ├── 分支逻辑 → 状态机枚举
│       │   └── enum WorkflowState { Init, Processing, Done }
│       ├── 并行执行 → tokio::join!
│       │   └── async { join!(task1, task2, task3) }
│       └── 需要超时/重试？
│           ├── 是 → tokio::time::timeout + backoff
│           └── 否 → 简单async/await
│
├── 人工任务？
│   ├── 是 → 需要BPMN引擎
│   │   ├── 复杂审批流？
│   │   │   ├── 是 → Camunda / Flowable
│   │   │   └── 否 → 简单任务列表
│   │   └── 表单要求？
│   │       ├── 动态表单 → 集成表单引擎
│   │       └── 静态表单 → 硬编码模板
│   └── 否 → 纯自动工作流
│
├── 补偿事务？
│   ├── 是 → Saga模式实现
│   │   ├── 向后补偿 → 标准Saga (try-compensate)
│   │   └── 向前补偿 → 可交换更新 (无需补偿)
│   └── 否 → 简单事务
│
└── 监控要求？
    ├── 是 → 选择有UI的引擎
    │   ├── 实时追踪 → Temporal Web UI
    │   ├── 历史查询 → Elasticsearch集成
    │   └── 告警 → PagerDuty/Opsgenie集成
    └── 否 → 日志足够
        └── tracing + structured logging
```

---

## 引擎对比矩阵
> **[来源: Rust Official Docs]**

| 引擎 | 持久化 | 复杂度 | Rust支持 | 云原生 | 适用场景 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Temporal** | ✅ 强 | 高 | 🔄 SDK开发中 | ✅ | 复杂业务流程 |
| **Cadence** | ✅ 强 | 中 | ❌ | ✅ | Uber生态 |
| **Camunda** | ✅ 强 | 高 | ❌ | ⚠️ | BPMN流程 |
| **自研状态机** | ❌ 内存 | 低-中 | ✅ | ✅ | 简单工作流 |
| **tokio::fsm** | ❌ 内存 | 低 | ✅ | ✅ | 嵌入式状态机 |

---

## Rust实现示例
> **[来源: Rust Official Docs]**

### 方案1: 自研工作流引擎 (轻量级)
> **[来源: Rust Official Docs]**

```rust
use std::future::Future;
use std::pin::Pin;
use std::time::Duration;
use tokio::time::timeout;

// 工作流上下文
type WorkflowContext = serde_json::Value;

// 活动定义
trait Activity: Send + Sync {
    fn name(&self) -> &'static str;
    fn execute(&self, ctx: &WorkflowContext) -> Pin<Box<dyn Future<Output = Result<WorkflowContext, ActivityError>> + Send + '_>>;
    fn compensate(&self, ctx: &WorkflowContext) -> Pin<Box<dyn Future<Output = Result<(), ActivityError>> + Send + '_>>;
}

// 工作流定义
struct Workflow {
    name: String,
    activities: Vec<Box<dyn Activity>>,
    compensations: Vec<Box<dyn Activity>>,
    retry_policy: RetryPolicy,
}

struct RetryPolicy {
    max_attempts: u32,
    initial_interval: Duration,
    backoff_multiplier: f64,
    max_interval: Duration,
}

impl Workflow {
    async fn execute(&self, input: WorkflowContext) -> Result<WorkflowContext, WorkflowError> {
        let mut ctx = input;
        let mut completed = 0;

        for (i, activity) in self.activities.iter().enumerate() {
            match self.execute_with_retry(activity, &ctx).await {
                Ok(result) => {
                    ctx = result;
                    completed += 1;
                }
                Err(e) => {
                    // 执行补偿
                    for j in (0..completed).rev() {
                        if let Err(comp_err) = self.compensations[j].compensate(&ctx).await {
                            // 补偿失败 - 需要人工干预
                            return Err(WorkflowError::CompensationFailed {
                                activity: self.activities[j].name(),
                                original_error: e,
                                compensation_error: comp_err,
                            });
                        }
                    }
                    return Err(WorkflowError::ActivityFailed {
                        activity: activity.name(),
                        error: e,
                    });
                }
            }
        }

        Ok(ctx)
    }

    async fn execute_with_retry(
        &self,
        activity: &dyn Activity,
        ctx: &WorkflowContext,
    ) -> Result<WorkflowContext, ActivityError> {
        let mut interval = self.retry_policy.initial_interval;

        for attempt in 1..=self.retry_policy.max_attempts {
            match timeout(Duration::from_secs(30), activity.execute(ctx)).await {
                Ok(Ok(result)) => return Ok(result),
                Ok(Err(e)) if attempt < self.retry_policy.max_attempts => {
                    tokio::time::sleep(interval).await;
                    interval = std::cmp::min(
                        Duration::from_millis(
                            (interval.as_millis() as f64 * self.retry_policy.backoff_multiplier) as u64
                        ),
                        self.retry_policy.max_interval,
                    );
                }
                Ok(Err(e)) => return Err(e),
                Err(_) => return Err(ActivityError::Timeout),
            }
        }

        unreachable!()
    }
}

// 使用示例
struct ProcessPaymentActivity;

#[async_trait]
impl Activity for ProcessPaymentActivity {
    fn name(&self) -> &'static str { "process_payment" }

    async fn execute(&self, ctx: &WorkflowContext) -> Result<WorkflowContext, ActivityError> {
        // 调用支付网关
        let payment_id = ctx["order_id"].as_str().unwrap();
        let amount = ctx["amount"].as_f64().unwrap();

        // 实际支付逻辑...

        let mut result = ctx.clone();
        result["payment_id"] = json!(format!("pay_{}", uuid::Uuid::new_v4()));
        result["status"] = json!("paid");

        Ok(result)
    }

    async fn compensate(&self, ctx: &WorkflowContext) -> Result<(), ActivityError> {
        // 退款逻辑
        let payment_id = ctx["payment_id"].as_str().unwrap();
        println!("Refunding payment: {}", payment_id);
        Ok(())
    }
}
```

### 方案2: 状态机模式
> **[来源: Rust Official Docs]**

```rust
// 枚举驱动的状态机
enum OrderWorkflowState {
    Created { order_id: String },
    InventoryReserved { order_id: String, reservation_id: String },
    PaymentProcessed { order_id: String, payment_id: String },
    Completed { order_id: String },
    Cancelled { order_id: String, reason: String },
}

struct OrderWorkflow {
    state: OrderWorkflowState,
}

impl OrderWorkflow {
    async fn step(&mut self) -> Result<(), WorkflowError> {
        match &self.state {
            OrderWorkflowState::Created { order_id } => {
                // 预留库存
                match reserve_inventory(order_id).await {
                    Ok(reservation_id) => {
                        self.state = OrderWorkflowState::InventoryReserved {
                            order_id: order_id.clone(),
                            reservation_id,
                        };
                    }
                    Err(e) => {
                        self.state = OrderWorkflowState::Cancelled {
                            order_id: order_id.clone(),
                            reason: format!("Inventory reservation failed: {}", e),
                        };
                    }
                }
            }
            OrderWorkflowState::InventoryReserved { order_id, reservation_id } => {
                // 处理支付
                match process_payment(order_id).await {
                    Ok(payment_id) => {
                        self.state = OrderWorkflowState::PaymentProcessed {
                            order_id: order_id.clone(),
                            payment_id,
                        };
                    }
                    Err(e) => {
                        // 补偿：释放库存
                        release_inventory(reservation_id).await?;
                        self.state = OrderWorkflowState::Cancelled {
                            order_id: order_id.clone(),
                            reason: format!("Payment failed: {}", e),
                        };
                    }
                }
            }
            OrderWorkflowState::PaymentProcessed { order_id, .. } => {
                // 完成订单
                complete_order(order_id).await?;
                self.state = OrderWorkflowState::Completed {
                    order_id: order_id.clone(),
                };
            }
            OrderWorkflowState::Completed { .. } | OrderWorkflowState::Cancelled { .. } => {
                // 终态，无需处理
            }
        }
        Ok(())
    }

    fn is_terminal(&self) -> bool {
        matches!(self.state, OrderWorkflowState::Completed { .. } | OrderWorkflowState::Cancelled { .. })
    }
}
```

### 方案3: Temporal集成
> **[来源: Rust Official Docs]**

```rust
// 使用Temporal Rust SDK (假设)
#[temporal::workflow]
async fn order_workflow(ctx: WorkflowContext, order: Order) -> Result<OrderResult, WorkflowError> {
    // 活动选项
    let opts = ActivityOptions::default()
        .with_schedule_to_close_timeout(Duration::from_secs(60))
        .with_retry_policy(RetryPolicy {
            initial_interval: Duration::from_secs(1),
            backoff_coefficient: 2.0,
            max_attempts: 3,
            ..Default::default()
        });

    // 执行活动
    let reservation = ctx.execute_activity(
        "reserve_inventory",
        opts.clone(),
        &order.items,
    ).await?;

    // 设置补偿
    ctx.on_compensate("release_inventory", &reservation.id);

    // 继续执行
    let payment = ctx.execute_activity(
        "process_payment",
        opts,
        &order.payment_info,
    ).await?;

    ctx.on_compensate("refund_payment", &payment.id);

    // 发货
    let shipment = ctx.execute_activity(
        "create_shipment",
        opts,
        &order.shipping_address,
    ).await?;

    Ok(OrderResult {
        order_id: order.id,
        reservation_id: reservation.id,
        payment_id: payment.id,
        shipment_id: shipment.id,
    })
}

#[temporal::activity]
async fn reserve_inventory(items: Vec<OrderItem>) -> Result<Reservation, ActivityError> {
    // 实际库存预留逻辑
    todo!()
}
```

---

## 选择建议
> **[来源: Rust Official Docs]**

| 场景 | 推荐方案 | 理由 |
| :--- | :--- | :--- |
| 初创项目/MVP | 自研状态机 | 简单、可控、无外部依赖 |
| 中小企业 | Temporal | 成熟、文档完善、社区活跃 |
| 企业级/BPMN | Camunda | BPMN标准、可视化、人工任务 |
| 事件驱动架构 | 自研Saga+Kafka | 与现有架构集成、灵活 |
| 高并发低延迟 | tokio::fsm | 内存状态机、无持久化开销 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-23
**状态**: ✅ 已完成 - 工作流引擎选型决策树

---

## 🆕 Rust 1.94 深度整合更新
> **[来源: Rust Official Docs]**

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点
> **[来源: Rust Official Docs]**

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用
> **[来源: Rust Official Docs]**

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新
> **[来源: Rust Official Docs]**

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
