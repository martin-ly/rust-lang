# 08 多路合并模式 (Multi-Merge)

## 模式定义与语义

多路合并模式允许多个分支独立地汇入同一个后续节点，无需同步。
每个分支完成时都会触发后续活动的执行。

### 核心语义

$$
\text{MultiMerge}(P_1, P_2, \ldots, P_n, Q) = \forall i \in [1,n]: P_i \gg Q_i
$$

其中每个 $Q_i$ 是 $Q$ 的一个独立实例。

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State}_i = \{ \text{Idle}_i, \text{Active}_i, \text{Completed}_i \} \quad \forall i \in [1,n] \\
& \text{Transition}_i = \{ \\
& \quad (\text{Idle}_i, \text{start}_i, \text{Active}_i), \\
& \quad (\text{Active}_i, \text{done}_i, \text{Completed}_i), \\
& \quad (\text{Completed}_i, \text{trigger}, Q\text{_instance}_i) \\
& \}
\end{aligned}
$$

**流程代数：**

$$
\text{MultiMerge} = (P_1 \gg Q) \parallel (P_2 \gg Q) \parallel \cdots \parallel (P_n \gg Q)
$$

## Rust 实现示例

```rust
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicUsize, Ordering};
use tokio::sync::mpsc;

/// 多路合并处理器
pub struct MultiMerge<T, R> {
    merger_fn: Arc<dyn Fn(T) -> R + Send + Sync>,
    execution_count: AtomicUsize,
    sender: mpsc::Sender<R>,
    receiver: Arc<Mutex<mpsc::Receiver<R>>>,
}

use std::sync::Arc;
use tokio::sync::Mutex;

impl<T: Send + 'static, R: Send + 'static> MultiMerge<T, R> {
    pub fn new(merger_fn: impl Fn(T) -> R + Send + Sync + 'static) -> (Self, mpsc::Receiver<R>) {
        let (sender, receiver) = mpsc::channel(100);
        let merge = Self {
            merger_fn: Arc::new(merger_fn),
            execution_count: AtomicUsize::new(0),
            sender,
            receiver: Arc::new(Mutex::new(receiver)),
        };

        // 返回一个独立的 receiver
        let (_, rx) = mpsc::channel(100);
        (merge, rx)
    }

    /// 创建分支处理器
    pub fn create_branch_handler(&self) -> BranchHandler<T, R> {
        BranchHandler {
            merger_fn: Arc::clone(&self.merger_fn),
            sender: self.sender.clone(),
            counter: &self.execution_count,
        }
    }

    pub fn get_execution_count(&self) -> usize {
        self.execution_count.load(Ordering::SeqCst)
    }
}

pub struct BranchHandler<'a, T, R> {
    merger_fn: Arc<dyn Fn(T) -> R + Send + Sync>,
    sender: mpsc::Sender<R>,
    counter: &'a AtomicUsize,
}

impl<'a, T: Send, R: Send> BranchHandler<'a, T, R> {
    pub async fn process(&self, input: T) {
        let result = (self.merger_fn)(input);
        self.counter.fetch_add(1, Ordering::SeqCst);
        let _ = self.sender.send(result).await;
    }
}

/// 使用示例：消息处理
#[derive(Clone, Debug)]
struct Message {
    source: String,
    payload: String,
}

#[derive(Clone, Debug)]
struct ProcessedMessage {
    from: String,
    processed_payload: String,
    timestamp: u64,
}

pub async fn multi_merge_example() {
    let (merge, mut rx) = MultiMerge::new(|msg: Message| {
        ProcessedMessage {
            from: msg.source.clone(),
            processed_payload: msg.payload.to_uppercase(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        }
    });

    // 模拟多个并行的消息源
    let sources = vec!["source_a", "source_b", "source_c"];
    let mut handles = vec![];

    for source in sources {
        let handler = merge.create_branch_handler();
        let handle = tokio::spawn(async move {
            let msg = Message {
                source: source.to_string(),
                payload: format!("data from {}", source),
            };
            handler.process(msg).await;
        });
        handles.push(handle);
    }

    // 等待所有分支
    for h in handles {
        let _ = h.await;
    }

    // 收集结果
    let mut count = 0;
    while let Ok(result) = rx.try_recv() {
        println!("处理结果: {:?}", result);
        count += 1;
    }

    println!("总共执行 {} 次后续活动", count);
}

/// 简化版：使用广播通道
use tokio::sync::broadcast;

pub struct SimpleMultiMerge<T> {
    sender: broadcast::Sender<T>,
}

impl<T: Clone + Send + 'static> SimpleMultiMerge<T> {
    pub fn new() -> Self {
        let (sender, _) = broadcast::channel(100);
        Self { sender }
    }

    pub fn subscribe(&self) -> broadcast::Receiver<T> {
        self.sender.subscribe()
    }

    pub fn merge(&self, result: T) {
        let _ = self.sender.send(result);
    }
}
```

## 与其他模式的关系

| 模式 | 同步性 | 触发次数 |
|------|--------|----------|
| 简单合并 | 无 | 1 次 |
| **多路合并** | 无 | n 次 |
| 同步合并 | 有 | 1 次 |
| 鉴别器 | 有（等第一个） | 1 次 |

**关系公式：**

$$
\text{MultiMerge}(n) = \underbrace{\text{SimpleMerge} \parallel \cdots \parallel \text{SimpleMerge}}_{n \text{ 次}}
$$

## 应用场景

1. **消息广播**：多个消息源独立触发同一处理逻辑
2. **日志聚合**：多个服务独立上报日志
3. **事件通知**：多个触发源产生的事件独立处理
4. **批量处理**：每个批次独立进入处理流程

### 注意事项

- 后续活动需要处理并发执行的情况
- 考虑使用幂等性设计
- 注意资源竞争问题
