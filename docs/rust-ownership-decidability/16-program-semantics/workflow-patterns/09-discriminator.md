# 09 鉴别器模式 (Discriminator)

## 模式定义与语义

鉴别器模式等待多个并行分支中的第一个完成，然后取消或忽略其他分支的执行结果，继续后续流程。

### 核心语义

$$
\text{Discriminator}(P_1, P_2, \ldots, P_n) = \text{first}(P_1, P_2, \ldots, P_n) \gg \text{cancel}(\text{others})
$$

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State} = \{ \text{Waiting}, \text{FirstCompleted}, \text{Cancelled}, \text{Done} \} \\
& \text{Transition} = \{ \\
& \quad (\text{Waiting}, \text{complete}_i, \text{FirstCompleted}), \\
& \quad (\text{FirstCompleted}, \text{cancel}_j, \text{Cancelled}) \quad \forall j \neq i, \\
& \quad (\text{Cancelled}, \text{proceed}, \text{Done}) \\
& \}
\end{aligned}
$$

**流程代数（CSP）：**

$$
\text{Discriminator} = (P_1 \Box P_2 \Box \cdots \Box P_n) ; Q
$$

其中 $\Box$ 表示外部选择（external choice）。

## Rust 实现示例

```rust
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use tokio::sync::oneshot;
use tokio::task::AbortHandle;

/// 鉴别器模式实现
pub struct Discriminator<T> {
    completed: AtomicBool,
    sender: Option<oneshot::Sender<T>>,
    abort_handles: Vec<AbortHandle>,
}

impl<T: Send + 'static> Discriminator<T> {
    pub fn new() -> (Self, oneshot::Receiver<T>) {
        let (tx, rx) = oneshot::channel();
        let discriminator = Self {
            completed: AtomicBool::new(false),
            sender: Some(tx),
            abort_handles: Vec::new(),
        };
        (discriminator, rx)
    }

    /// 注册一个分支任务
    pub fn spawn_branch<F>(&mut self, future: F) -> AbortHandle
    where
        F: Future<Output = T> + Send + 'static,
    {
        let handle = tokio::spawn(self.create_wrapped_future(future));
        let abort_handle = handle.abort_handle();
        self.abort_handles.push(abort_handle.clone());
        abort_handle
    }

    fn create_wrapped_future<F>(&self, future: F) -> impl Future<Output = ()>
    where
        F: Future<Output = T> + Send + 'static,
    {
        let completed_flag = AtomicBool::new(false);
        let mut sender = None;

        // 需要 Arc<Mutex> 来共享 sender
        async move {
            let result = future.await;

            // 尝试成为第一个完成的
            if completed_flag
                .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok()
            {
                if let Some(tx) = sender.take() {
                    let _ = tx.send(result);
                }
            }
        }
    }

    /// 取消所有其他分支
    pub fn cancel_others(&self, winner_index: usize) {
        for (i, handle) in self.abort_handles.iter().enumerate() {
            if i != winner_index {
                handle.abort();
            }
        }
    }
}

/// 基于 select! 的更简洁实现
use tokio::select;

pub async fn discriminator_select<T>(
    futures: Vec<impl Future<Output = T>>,
) -> (T, Vec<AbortHandle>) {
    let mut abort_handles = Vec::with_capacity(futures.len());

    // 包装所有 future
    let mut joined: Vec<Pin<Box<dyn Future<Output = T> + Send>>> = futures
        .into_iter()
        .map(|f| Box::pin(f) as Pin<Box<dyn Future<Output = T> + Send>>)
        .collect();

    // 使用 select! 等待第一个完成
    let result = match joined.len() {
        0 => panic!("No futures provided"),
        1 => joined.remove(0).await,
        _ => {
            let (result, _index, _) = futures::future::select_all(joined).await;
            result
        }
    };

    (result, abort_handles)
}

/// 使用示例：竞速查询
#[derive(Debug, Clone)]
struct QueryResult {
    source: String,
    data: String,
    latency_ms: u64,
}

pub async fn racing_query_example() {
    let queries = vec![
        query_database("primary", 100),
        query_database("replica1", 50),
        query_database("replica2", 150),
    ];

    let (first_result, _) = discriminator_select(queries).await;

    println!("最快响应来自: {}", first_result.source);
    println!("数据: {}", first_result.data);
}

async fn query_database(source: &str, latency_ms: u64) -> QueryResult {
    tokio::time::sleep(tokio::time::Duration::from_millis(latency_ms)).await;

    QueryResult {
        source: source.to_string(),
        data: format!("data from {}", source),
        latency_ms,
    }
}

/// 带取消通知的鉴别器
pub struct CancellableDiscriminator<T> {
    cancel_tx: broadcast::Sender<()>,
}

use tokio::sync::broadcast;

impl<T> CancellableDiscriminator<T> {
    pub fn new() -> (Self, broadcast::Receiver<()>) {
        let (cancel_tx, cancel_rx) = broadcast::channel(1);
        (Self { cancel_tx }, cancel_rx)
    }

    pub async fn race(
        &self,
        tasks: Vec<impl Future<Output = T> + Send>,
    ) -> T {
        let cancel_rx = self.cancel_tx.subscribe();

        // 实际实现会使用更复杂的逻辑
        todo!("Implement with proper cancellation")
    }
}
```

## 与其他模式的关系

| 模式 | 等待策略 | 结果处理 |
|------|----------|----------|
| **鉴别器** | 第一个完成 | 取消其他 |
| N选M | M 个完成 | 继续其他 |
| 同步合并 | 全部完成 | 合并结果 |
| 多路合并 | 不等待 | 全部触发 |

**关系公式：**

$$
\text{Discriminator} = \text{PartialJoin}(1) + \text{Cancel}(\text{others})
$$

## 应用场景

1. **竞速查询**：从多个数据源获取同一数据，采用最快响应
2. **故障转移**：多个服务实例，第一个可用即使用
3. **超时控制**：任务与超时竞速，先完成者决定结果
4. **负载均衡**：选择最快响应的服务器

### 实现要点

- 正确取消正在执行的其他任务
- 处理取消时的资源清理
- 避免竞态条件
- 考虑任务清理的延迟
