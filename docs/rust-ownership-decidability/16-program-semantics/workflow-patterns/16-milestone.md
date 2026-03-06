# 16 里程碑模式 (Milestone)

## 模式定义与语义

里程碑模式允许活动仅在达到特定状态（里程碑）时才能执行。它用于建模需要等待某些前置条件满足的场景。

### 核心语义

$$
\text{Milestone}(M, A) = \text{when } M = \text{true}: \text{enable}(A)
$$

其中 $M$ 是里程碑条件，$A$ 是被控制的活动。

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State} = \{ \text{Inactive}, \text{Waiting}, \text{Enabled}, \text{Executing}, \text{Completed} \} \\
& \text{Transition} = \{ \\
& \quad (\text{Inactive}, \text{activate}, \text{Waiting}), \\
& \quad (\text{Waiting}, M=\text{true}, \text{Enabled}), \\
& \quad (\text{Enabled}, \text{start}, \text{Executing}), \\
& \quad (\text{Executing}, \text{done}, \text{Completed}) \\
& \}
\end{aligned}
$$

**时序逻辑：**

$$
\Diamond (M \land \text{Enabled}(A)) \to \Diamond \text{Completed}(A)
$$

## Rust 实现示例

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
        todo!("使用 tokio::select! 实现")
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

### 注意事项

- 里程碑状态需要持久化以支持故障恢复
- 考虑里程碑的撤销机制
- 防止里程碑死锁（循环依赖）
- 提供超时和降级策略
