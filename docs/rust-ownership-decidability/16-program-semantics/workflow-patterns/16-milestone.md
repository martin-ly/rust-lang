# 16 里程碑模式 (Milestone)

## 📋 目录

- [16 里程碑模式 (Milestone)](#16-里程碑模式-milestone)
  - [📋 目录](#-目录)
  - [模式定义与语义](#模式定义与语义)
    - [核心语义](#核心语义)
    - [状态条件语义](#状态条件语义)
  - [时序逻辑形式化](#时序逻辑形式化)
    - [LTL 表示](#ltl-表示)
    - [CTL 表示](#ctl-表示)
  - [BPMN 2.0 表示](#bpmn-20-表示)
  - [状态机语义](#状态机语义)
  - [正确性证明](#正确性证明)
    - [安全性证明](#安全性证明)
    - [活性证明](#活性证明)
  - [Rust 实现示例](#rust-实现示例)
    - [基础实现](#基础实现)
    - [组合里程碑](#组合里程碑)
    - [带超时的里程碑](#带超时的里程碑)
  - [与其他模式的关系](#与其他模式的关系)
  - [应用场景](#应用场景)
    - [注意事项](#注意事项)
  - [学术参考](#学术参考)

## 模式定义与语义

里程碑模式允许活动仅在达到特定状态（里程碑）时才能执行。它用于建模需要等待某些前置条件满足的场景。

### 核心语义

$$
\text{Milestone}(M, A) = \text{when } M = \text{true}: \text{enable}(A)
$$

其中 $M$ 是里程碑条件，$A$ 是被控制的活动。

**里程碑特性：**

| 特性 | 描述 |
|------|------|
| 持续性 | 一旦达成，里程碑保持有效 |
| 可测试性 | 活动可随时检查里程碑状态 |
| 触发器 | 里程碑达成可触发活动启动 |

### 状态条件语义

里程碑作为状态条件：

$$
\text{Enabled}(A, t) \iff M(t) \land \text{Preconditions}(A)
$$

里程碑的生命周期：

$$
\text{MilestoneLifecycle} = \text{Inactive} \to \text{Achieved} \to \text{Persistent}
$$

## 时序逻辑形式化

### LTL 表示

**线性时序逻辑（LTL）**用于描述里程碑的时序性质：

```
◇M - 里程碑 M 最终达成
□M - 里程碑 M 始终有效（达成后）
M → ◇A - 如果里程碑达成，活动 A 最终执行
□(M → □M) - 里程碑的持久性
```

**关键公式：**

$$
\Diamond (M \land \text{Enabled}(A)) \to \Diamond \text{Completed}(A)
$$

**直到（Until）语义：**

$$
\text{WaitForMilestone} = \neg M \mathcal{U} (M \land \text{Start}(A))
$$

### CTL 表示

**计算树逻辑（CTL）**用于描述里程碑的分支时序性质：

```
AG(M → AF Completed(A)) - 所有路径上，如果里程碑达成，A 最终完成
EF M - 存在一条路径使里程碑达成
AX(M → EX Enabled(A)) - 下一状态可以启用 A
```

**可达性公式：**

$$
\mathbf{E}\mathbf{F}(M \land \mathbf{A}\mathbf{F}\,\text{Done}(A))
$$

## BPMN 2.0 表示

在 BPMN 2.0 中，里程碑可以使用**条件事件（Conditional Event）**或**信号事件（Signal Event）**实现：

```xml
<?xml version="1.0" encoding="UTF-8"?>
<bpmn:definitions xmlns:bpmn="http://www.omg.org/spec/BPMN/20100524/MODEL">
  <bpmn:process id="MilestoneProcess" isExecutable="true">

    <!-- 里程碑：等待条件满足 -->
    <bpmn:intermediateCatchEvent id="MilestoneEvent" name="Payment Received">
      <bpmn:conditionalEventDefinition>
        <bpmn:condition>${paymentStatus == 'RECEIVED'}</bpmn:condition>
      </bpmn:conditionalEventDefinition>
    </bpmn:intermediateCatchEvent>

    <!-- 依赖于里程碑的活动 -->
    <bpmn:task id="ShipOrder" name="Ship Order">
      <bpmn:incoming>Flow_Milestone</bpmn:incoming>
    </bpmn:task>

    <!-- 设置里程碑的子流程 -->
    <bpmn:subProcess id="ProcessPayment" name="Process Payment">
      <!-- 支付处理任务 -->
      <bpmn:task id="ReceivePayment" name="Receive Payment"/>

      <!-- 发出信号（设置里程碑） -->
      <bpmn:intermediateThrowEvent id="SetMilestone" name="Payment Confirmed">
        <bpmn:signalEventDefinition signalRef="PaymentSignal"/>
      </bpmn:intermediateThrowEvent>
    </bpmn:subProcess>

  </bpmn:process>

  <!-- 信号定义 -->
  <bpmn:signal id="PaymentSignal" name="Payment Received Signal"/>
</bpmn:definitions>
```

**图形表示：**

```
    ┌─────────────────────────────┐
    │     Process Payment         │
    │  ┌───────────────────────┐  │
    │  │  Receive Payment      │  │
    │  └───────────┬───────────┘  │
    │              │               │
    │              ▼               │
    │  ┌───────────────────────┐  │
    │  │   ◇───────            │  │  ◄── 抛出信号
    │  │  Payment Confirmed    │  │      (设置里程碑)
    │  └───────────────────────┘  │
    └─────────────────────────────┘
              │
              │ PaymentSignal
              │
              ▼
    ┌─────────────────────────────┐
    │    ◇───────                 │  ◄── 等待里程碑
    │   Payment Received          │      (条件事件)
    │   (Conditional Event)       │
    └─────────────┬───────────────┘
                  │
                  ▼
          ┌───────────────┐
          │  Ship Order   │  ◄── 里程碑达成后执行
          │  (Enabled by  │
          │   Milestone)  │
          └───────────────┘
```

## 状态机语义

**完整状态机：**

$$
\begin{aligned}
& \text{States} = \{ \\
& \quad \text{INACTIVE}: \text{里程碑未激活}, \\
& \quad \text{WAITING}(A): \text{等待里程碑以启用 } A, \\
& \quad \text{ACHIEVED}: \text{里程碑已达成}, \\
& \quad \text{ENABLED}(A): \text{活动 } A \text{ 已启用}, \\
& \quad \text{EXECUTING}(A): \text{活动 } A \text{ 执行中}, \\
& \quad \text{COMPLETED}: \text{完成} \\
& \} \\
& \text{Transitions} = \{ \\
& \quad \text{INACTIVE} \xrightarrow{\text{activate}} \text{WAITING}(A), \\
& \quad \text{WAITING}(A) \xrightarrow{M} \text{ENABLED}(A), \\
& \quad \text{ENABLED}(A) \xrightarrow{\text{start}} \text{EXECUTING}(A), \\
& \quad \text{ACHIEVED} \xrightarrow{\text{trigger}} \text{ENABLED}(A), \\
& \quad \text{EXECUTING}(A) \xrightarrow{\text{done}} \text{COMPLETED} \\
& \}
\end{aligned}
$$

**Petri 网表示：**

```
    Set Milestone
          │
          ▼
    ┌─────────────┐
    │  ACHIEVED   │──────────────────┐
    │   Place     │                  │
    └─────────────┘                  │
                                     │
                                     │ M
                                     │
                                     ▼
    ┌─────────────┐           ┌─────────────┐
    │   WAITING   │           │   ENABLED   │
    │   Place     │──────────▶│   Place     │
    └─────────────┘           └──────┬──────┘
                                     │
                                     │
                                     ▼
                              ┌─────────────┐
                              │   Activity  │
                              │    Fire     │
                              └─────────────┘
```

## 正确性证明

### 安全性证明

**定理（条件检查）**: 活动只有在里程碑达成后才能执行。

**证明:**

1. 活动 $A$ 的起始守卫包含条件 $M$
2. 状态 `WAITING(A)` 只有在 $M$ 为真时才能转移到 `ENABLED(A)`
3. 从 `ENABLED(A)` 才能启动 $A$ 的执行
4. 因此 $A$ 的执行必然在 $M$ 达成之后

因此安全性得证。∎

### 活性证明

**定理（最终执行）**: 如果里程碑最终达成，依赖它的活动最终会被启用。

**证明:**

假设里程碑 $M$ 在时间 $t$ 达成。

1. 系统在时间 $t$ 检测到 $M$ 为真
2. 状态从 `WAITING(A)` 转移到 `ENABLED(A)`
3. 活动 $A$ 被标记为可执行
4. 调度器最终会选择 $A$ 执行

因此活动最终会被执行。∎

## Rust 实现示例

### 基础实现

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use tokio::sync::{watch, Notify};

/// 里程碑控制器
pub struct Milestone<T> {
    achieved: Arc<AtomicBool>,
    notify: Arc<Notify>,
    data: Arc<tokio::sync::RwLock<Option<T>>>,
}

impl<T: Clone + Send + Sync> Milestone<T> {
    pub fn new() -> Self {
        Self {
            achieved: Arc::new(AtomicBool::new(false)),
            notify: Arc::new(Notify::new()),
            data: Arc::new(tokio::sync::RwLock::new(None)),
        }
    }

    /// 检查里程碑是否达成
    pub fn is_achieved(&self) -> bool {
        self.achieved.load(Ordering::SeqCst)
    }

    /// 达成里程碑
    pub async fn achieve(&self, data: T) {
        let mut guard = self.data.write().await;
        *guard = Some(data);
        drop(guard);

        self.achieved.store(true, Ordering::SeqCst);
        self.notify.notify_waiters();
    }

    /// 等待里程碑达成
    pub async fn wait(&self) -> Option<T> {
        if self.is_achieved() {
            return self.data.read().await.clone();
        }

        self.notify.notified().await;
        self.data.read().await.clone()
    }

    /// 等待里程碑，带超时
    pub async fn wait_timeout(&self, duration: tokio::time::Duration) -> Option<T> {
        tokio::select! {
            result = self.wait() => result,
            _ = tokio::time::sleep(duration) => {
                println!("等待里程碑超时");
                None
            }
        }
    }
}

/// 使用示例：订单处理里程碑
#[derive(Clone, Debug)]
struct OrderMilestoneData {
    order_id: String,
    customer_approved: bool,
    payment_received: bool,
    inventory_reserved: bool,
}

pub struct OrderProcessor {
    payment_milestone: Arc<Milestone<OrderMilestoneData>>,
    inventory_milestone: Arc<Milestone<OrderMilestoneData>>,
}

impl OrderProcessor {
    pub fn new() -> Self {
        Self {
            payment_milestone: Arc::new(Milestone::new()),
            inventory_milestone: Arc::new(Milestone::new()),
        }
    }

    /// 只有在支付和库存都就绪后才能发货
    pub async fn process_shipment(&self, order_id: String) -> Result<String, String> {
        println!("订单 {} 等待支付里程碑...", order_id);

        // 等待支付里程碑
        let payment_data = self.payment_milestone.wait().await
            .ok_or("支付里程碑未达成")?;

        println!("支付完成: {:?}", payment_data);

        // 等待库存里程碑
        println!("订单 {} 等待库存里程碑...", order_id);
        let inventory_data = self.inventory_milestone.wait().await
            .ok_or("库存里程碑未达成")?;

        println!("库存就绪: {:?}", inventory_data);

        Ok(format!("订单 {} 发货成功", order_id))
    }

    /// 处理支付完成
    pub async fn on_payment_received(&self, order_id: String) {
        let data = OrderMilestoneData {
            order_id: order_id.clone(),
            customer_approved: true,
            payment_received: true,
            inventory_reserved: false,
        };

        println!("达成支付里程碑");
        self.payment_milestone.achieve(data).await;
    }

    /// 处理库存预留完成
    pub async fn on_inventory_reserved(&self, order_id: String) {
        let data = OrderMilestoneData {
            order_id: order_id.clone(),
            customer_approved: true,
            payment_received: true,
            inventory_reserved: true,
        };

        println!("达成库存里程碑");
        self.inventory_milestone.achieve(data).await;
    }
}
```

### 组合里程碑

```rust
/// 使用 watch 通道的实现
pub struct WatchMilestone<T: Clone> {
    tx: watch::Sender<Option<T>>,
    rx: watch::Receiver<Option<T>>,
}

impl<T: Clone + Send + 'static> WatchMilestone<T> {
    pub fn new() -> Self {
        let (tx, rx) = watch::channel(None);
        Self { tx, rx }
    }

    pub fn achieve(&self, data: T) {
        let _ = self.tx.send(Some(data));
    }

    pub async fn wait(&mut self) -> Option<T> {
        while self.rx.changed().await.is_ok() {
            if let Some(ref data) = *self.rx.borrow() {
                return Some(data.clone());
            }
        }
        None
    }

    pub fn is_achieved(&self) -> bool {
        self.rx.borrow().is_some()
    }
}

/// 多个里程碑的 AND 组合
pub struct MilestoneSet<T> {
    milestones: Vec<Arc<Milestone<T>>>,
}

impl<T: Clone + Send + Sync + 'static> MilestoneSet<T> {
    pub fn new(milestones: Vec<Arc<Milestone<T>>>) -> Self {
        Self { milestones }
    }

    /// 等待所有里程碑达成
    pub async fn wait_all(&self) -> Vec<Option<T>> {
        let mut results = Vec::new();
        for milestone in &self.milestones {
            results.push(milestone.wait().await);
        }
        results
    }

    /// 等待任意里程碑达成（OR）
    pub async fn wait_any(&self) -> Option<T> {
        // 使用 select! 等待第一个
        let (tx, mut rx) = tokio::sync::mpsc::channel(1);

        for milestone in &self.milestones {
            let tx = tx.clone();
            let m = Arc::clone(milestone);
            tokio::spawn(async move {
                if let Some(data) = m.wait().await {
                    let _ = tx.send(data).await;
                }
            });
        }

        rx.recv().await
    }
}

/// 使用示例
pub async fn milestone_example() {
    let processor = Arc::new(OrderProcessor::new());

    // 启动发货处理
    let processor_clone = Arc::clone(&processor);
    let shipment_handle = tokio::spawn(async move {
        let result = processor_clone.process_shipment("ORDER-001".to_string()).await;
        println!("发货结果: {:?}", result);
    });

    // 模拟异步完成支付和库存预留
    tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
    processor.on_payment_received("ORDER-001".to_string()).await;

    tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
    processor.on_inventory_reserved("ORDER-001".to_string()).await;

    let _ = shipment_handle.await;
}
```

### 带超时的里程碑

```rust
use tokio::time::{timeout, Duration};

/// 带超时的里程碑控制器
pub struct TimedMilestone<T> {
    milestone: Milestone<T>,
    default_timeout: Duration,
}

impl<T: Clone + Send + Sync> TimedMilestone<T> {
    pub fn new(default_timeout: Duration) -> Self {
        Self {
            milestone: Milestone::new(),
            default_timeout,
        }
    }

    pub async fn wait_with_timeout(&self, custom_timeout: Option<Duration>) -> Result<T, MilestoneError> {
        let duration = custom_timeout.unwrap_or(self.default_timeout);

        match timeout(duration, self.milestone.wait()).await {
            Ok(Some(data)) => Ok(data),
            Ok(None) => Err(MilestoneError::NoData),
            Err(_) => Err(MilestoneError::Timeout),
        }
    }

    pub fn achieve(&self, data: T) -> impl std::future::Future<Output = ()> + '_ {
        self.milestone.achieve(data)
    }
}

#[derive(Debug)]
pub enum MilestoneError {
    Timeout,
    NoData,
}

/// 条件里程碑：需要满足特定条件
pub struct ConditionalMilestone<T, C> {
    milestone: Milestone<T>,
    condition: Arc<dyn Fn(&C) -> bool + Send + Sync>,
}

impl<T: Clone + Send + Sync, C: Send + Sync> ConditionalMilestone<T, C> {
    pub fn new<F>(condition: F) -> Self
    where
        F: Fn(&C) -> bool + Send + Sync + 'static,
    {
        Self {
            milestone: Milestone::new(),
            condition: Arc::new(condition),
        }
    }

    pub async fn check_and_achieve(&self, context: &C, data: T) -> bool {
        if (self.condition)(context) {
            self.milestone.achieve(data).await;
            true
        } else {
            false
        }
    }

    pub async fn wait(&self) -> Option<T> {
        self.milestone.wait().await
    }
}

/// 可撤销的里程碑
pub struct RevocableMilestone<T> {
    milestone: Milestone<T>,
    revoke_tx: tokio::sync::mpsc::Sender<()>,
}

impl<T: Clone + Send + Sync> RevocableMilestone<T> {
    pub fn new() -> (Self, tokio::sync::mpsc::Receiver<()>) {
        let (tx, rx) = tokio::sync::mpsc::channel(1);
        (
            Self {
                milestone: Milestone::new(),
                revoke_tx: tx,
            },
            rx,
        )
    }

    pub async fn achieve(&self, data: T) {
        self.milestone.achieve(data).await;
    }

    pub async fn revoke(&self) -> Result<(), tokio::sync::mpsc::error::SendError<()>> {
        self.revoke_tx.send(()).await
    }

    pub fn is_achieved(&self) -> bool {
        self.milestone.is_achieved()
    }
}
```

## 与其他模式的关系

| 模式 | 触发方式 | 状态保持 |
|------|----------|----------|
| **里程碑** | 状态条件 | 持续有效 |
| 延迟选择 | 外部事件 | 一次性 |
| 瞬态触发器 | 事件信号 | 瞬态 |
| 持久触发器 | 事件信号 | 持久 |

**关系公式：**

$$
\text{Milestone} = \text{PersistentTrigger} + \text{StateCondition}
$$

## 应用场景

1. **订单处理**：等待支付确认后才能发货
2. **审批流程**：等待所有前置审批完成
3. **构建系统**：等待依赖构建完成
4. **项目管理**：等待前置任务里程碑
5. **数据同步**：等待数据到达阈值
6. **流程编排**：协调多个异步操作

### 注意事项

- 里程碑状态需要持久化以支持故障恢复
- 考虑里程碑的撤销机制
- 防止里程碑死锁（循环依赖）
- 提供超时和降级策略
- 监控里程碑达成时间

## 学术参考

1. **Clarke, E.M., Grumberg, O., & Peled, D.A.** (1999). *Model Checking*. MIT Press.

2. **Pnueli, A.** (1977). "The Temporal Logic of Programs." *Proceedings of the 18th IEEE Symposium on Foundations of Computer Science*, 46-57.

3. **Emerson, E.A., & Halpern, J.Y.** (1986). "Sometimes and Not Never Revisited: On Branching Versus Linear Time Temporal Logic." *Journal of the ACM*, 33(1), 151-178.

4. **van der Aalst, W.M.P.** (1998). "The Application of Petri Nets to Workflow Management." *Journal of Circuits, Systems and Computers*, 8(1), 21-66.

5. **Russell, N., ter Hofstede, A.H.M., van der Aalst, W.M.P., & Mulyar, N.** (2006). "Workflow Control-Flow Patterns: A Revised View." *BPM Center Report* BPM-06-22.
