# 14 延迟选择模式 (Deferred Choice)

## 模式定义与语义

延迟选择模式将分支决策推迟到运行时，基于外部事件或信号来决定执行路径。
与排他选择不同，决策不是在设计时静态确定的。

### 核心语义

$$
\text{DeferredChoice}(E_1 \to B_1, E_2 \to B_2, \ldots, E_n \to B_n) = \Box_{i=1}^{n} (E_i \to B_i)
$$

其中 $\Box$ 是外部选择算子，等待第一个发生的事件 $E_i$。

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State} = \{ \text{Waiting}, \text{Chosen}_1, \text{Chosen}_2, \ldots, \text{Chosen}_n, \text{Executing}, \text{Done} \} \\
& \text{Transition} = \{ \\
& \quad (\text{Waiting}, E_i, \text{Chosen}_i) \text{ for exactly one } i, \\
& \quad (\text{Chosen}_i, \text{start}, \text{Executing}), \\
& \quad (\text{Executing}, \text{complete}, \text{Done}) \\
& \}
\end{aligned}
}
$$

**CSP 表示：**

$$
\text{DeferredChoice} = (e_1 \to P_1) \Box (e_2 \to P_2) \Box \cdots \Box (e_n \to P_n)
$$

## Rust 实现示例

```rust
use std::future::Future;
use std::pin::Pin;
use tokio::sync::{mpsc, oneshot};
use tokio::select;

/// 延迟选择执行器
pub struct DeferredChoice<T, R> {
    branches: Vec<Branch<T, R>>,
}

pub struct Branch<T, R> {
    event_rx: mpsc::Receiver<Event<T>>,
    handler: Box<dyn Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync>,
    name: String,
}

pub struct Event<T> {
    pub data: T,
    pub timestamp: std::time::Instant,
}

impl<T: Send + 'static, R: Send + 'static> DeferredChoice<T, R> {
    pub fn new() -> Self {
        Self { branches: Vec::new() }
    }

    pub fn add_branch<F, Fut>(
        &mut self,
        name: impl Into<String>,
        handler: F,
    ) -> mpsc::Sender<Event<T>>
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        let (tx, rx) = mpsc::channel(1);

        self.branches.push(Branch {
            event_rx: rx,
            handler: Box::new(move |t| Box::pin(handler(t))),
            name: name.into(),
        });

        tx
    }

    /// 等待第一个事件并执行对应分支
    pub async fn wait_and_execute(mut self) -> Option<(String, R)> {
        if self.branches.is_empty() {
            return None;
        }

        // 使用 select! 等待第一个事件
        let result = tokio::select! {
            biased; // 按顺序检查

            // 为每个分支生成一个 select 分支
            result = self.wait_first_event() => result,
        };

        result
    }

    async fn wait_first_event(&mut self) -> Option<(String, R)> {
        // 简化的实现 - 实际使用时要处理多个 receiver
        for branch in &mut self.branches {
            if let Some(event) = branch.event_rx.recv().await {
                let handler = &branch.handler;
                let result = handler(event.data).await;
                return Some((branch.name.clone(), result));
            }
        }
        None
    }
}

/// 更实用的实现：使用通道和 select!
pub async fn deferred_choice_example() -> String {
    let (tx1, mut rx1) = mpsc::channel::<String>(1);
    let (tx2, mut rx2) = mpsc::channel::<String>(1);
    let (tx3, mut rx3) = mpsc::channel::<String>(1);

    // 模拟外部事件源
    tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;
        let _ = tx2.send("event_from_source_b".to_string()).await;
    });

    tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        let _ = tx1.send("event_from_source_a".to_string()).await;
    });

    // 延迟选择：等待第一个到达的事件
    let result = tokio::select! {
        Some(data) = rx1.recv() => {
            format!("路径 A 被选择: {}", process_path_a(data).await)
        }
        Some(data) = rx2.recv() => {
            format!("路径 B 被选择: {}", process_path_b(data).await)
        }
        Some(data) = rx3.recv() => {
            format!("路径 C 被选择: {}", process_path_c(data).await)
        }
        else => "没有路径被激活".to_string(),
    };

    result
}

async fn process_path_a(data: String) -> String {
    format!("处理 A: {}", data.to_uppercase())
}

async fn process_path_b(data: String) -> String {
    format!("处理 B: {}", data.len())
}

async fn process_path_c(data: String) -> String {
    format!("处理 C: {:?}", data.chars().next())
}

/// 使用 oneshot 的竞速实现
pub async fn race_choice<T>(receivers: Vec<oneshot::Receiver<T>>) -> Option<T> {
    let mut futures: Vec<_> = receivers
        .into_iter()
        .map(|rx| Box::pin(async move { rx.await.ok() }))
        .collect();

    loop {
        if futures.is_empty() {
            return None;
        }

        let (result, _, remaining) = futures::future::select_all(futures).await;

        if let Some(value) = result {
            return Some(value);
        }

        futures = remaining;
    }
}

/// 带超时的延迟选择
pub async fn deferred_choice_with_timeout<T>(
    receivers: Vec<oneshot::Receiver<T>>,
    timeout: tokio::time::Duration,
) -> Option<T> {
    tokio::select! {
        result = race_choice(receivers) => result,
        _ = tokio::time::sleep(timeout) => {
            println!("延迟选择超时");
            None
        }
    }
}

/// 使用示例：审批流程
# [derive(Debug, Clone)]
enum ApprovalEvent {
    Approved { by: String, comments: String },
    Rejected { by: String, reason: String },
    Escalated { to: String },
    Timeout,
}

pub async fn approval_workflow() -> ApprovalEvent {
    let (approve_tx, approve_rx) = oneshot::channel();
    let (reject_tx, reject_rx) = oneshot::channel();
    let (escalate_tx, escalate_rx) = oneshot::channel();

    // 模拟用户操作
    tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
        let _ = approve_tx.send(ApprovalEvent::Approved {
            by: "manager".to_string(),
            comments: "Looks good".to_string(),
        });
    });

    // 延迟选择：等待用户决策
    let timeout = tokio::time::Duration::from_secs(5);

    tokio::select! {
        Ok(event) = approve_rx => event,
        Ok(event) = reject_rx => event,
        Ok(event) = escalate_rx => event,
        _ = tokio::time::sleep(timeout) => ApprovalEvent::Timeout,
    }
}
```

## 与其他模式的关系

| 模式 | 决策时机 | 触发方式 |
|------|----------|----------|
| 排他选择 | 设计时/运行时求值 | 条件判断 |
| **延迟选择** | 运行时事件 | 外部事件 |
| 多路选择 | 运行时求值 | 多条件判断 |
| 鉴别器 | 运行时 | 竞速完成 |

**关系公式：**

$$
\text{DeferredChoice} = \text{ExternalChoice} = \text{Discriminator}(\text{event-based})
$$

## 应用场景

1. **用户决策**：等待用户从多个选项中选择
2. **外部事件响应**：基于最先到达的外部信号决策
3. **竞速条件**：多个数据源，采用最快响应
4. **中断处理**：正常流程与中断信号竞速

### 注意事项

- 确保事件源能够正确发送信号
- 考虑超时处理避免无限等待
- 处理竞态条件下的边界情况
- 提供取消机制
