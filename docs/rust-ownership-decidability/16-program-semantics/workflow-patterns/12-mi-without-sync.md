# 12 多实例无同步模式 (Multiple Instances Without Synchronization)

## 模式定义与语义

多实例无同步模式允许在运行时并行创建多个活动实例，这些实例独立执行且不需要同步汇合。
实例数量通常在运行时才能确定。

### 核心语义

$$
\text{MIWithoutSync}(A, n) = \parallel_{i=1}^{n} A_i
$$

其中 $n$ 是运行时确定的实例数量，$A_i$ 相互独立。

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State} = \{ \text{Ready}, \text{Creating}, \text{Executing}, \text{Completed} \} \\
& \text{Transition} = \{ \\
& \quad (\text{Ready}, \text{determine\_count}(n), \text{Creating}), \\
& \quad (\text{Creating}, \text{spawn}_i, \text{Executing}) \quad \forall i \in [1,n], \\
& \quad (\text{Executing}, \text{complete}_i, \text{Executing}) \text{ 独立完成}, \\
& \quad (\text{Executing}, \text{all\_spawned}, \text{Completed}) \\
& \}
\end{aligned}
$$

**流程代数：**

$$
\text{MIWithoutSync}(A) = !A = A \parallel A \parallel \cdots \text{（无限制并行）}
$$

## Rust 实现示例

```rust
use std::future::Future;
use std::sync::atomic::{AtomicUsize, Ordering};
use tokio::task::JoinHandle;

/// 多实例无同步执行器
pub struct MultiInstanceNoSync<T, R> {
    factory: Arc<dyn Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync>,
    spawned_count: AtomicUsize,
}

use std::sync::Arc;
use std::pin::Pin;

impl<T: Send + 'static, R: Send + 'static> MultiInstanceNoSync<T, R> {
    pub fn new<F, Fut>(factory: F) -> Self
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        Self {
            factory: Arc::new(move |t| Box::pin(factory(t))),
            spawned_count: AtomicUsize::new(0),
        }
    }

    /// 创建指定数量的实例
    pub async fn spawn_instances(&self, items: Vec<T>) -> Vec<JoinHandle<R>> {
        let mut handles = Vec::with_capacity(items.len());

        for item in items {
            let factory = Arc::clone(&self.factory);

            let handle = tokio::spawn(async move {
                let future = factory(item);
                future.await
            });

            handles.push(handle);
            self.spawned_count.fetch_add(1, Ordering::SeqCst);
        }

        handles
    }

    /// 启动但不等待（真正的无同步）
    pub fn spawn_and_forget(&self, items: Vec<T>) {
        for item in items {
            let factory = Arc::clone(&self.factory);

            tokio::spawn(async move {
                let future = factory(item);
                let _ = future.await; // 忽略结果
            });

            self.spawned_count.fetch_add(1, Ordering::SeqCst);
        }
    }

    pub fn get_spawned_count(&self) -> usize {
        self.spawned_count.load(Ordering::SeqCst)
    }
}

/// 使用示例：批量邮件发送
#[derive(Clone)]
struct EmailTask {
    to: String,
    subject: String,
    body: String,
}

#[derive(Debug)]
struct SendResult {
    recipient: String,
    success: bool,
    message_id: Option<String>,
}

async fn send_email_task(task: EmailTask) -> SendResult {
    // 模拟异步发送
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    SendResult {
        recipient: task.to.clone(),
        success: true,
        message_id: Some(format!("msg_{}", task.to)),
    }
}

pub async fn multi_instance_example() {
    let sender = MultiInstanceNoSync::new(send_email_task);

    let emails = vec![
        EmailTask { to: "a@example.com".to_string(), subject: "Hello".to_string(), body: "...".to_string() },
        EmailTask { to: "b@example.com".to_string(), subject: "Hello".to_string(), body: "...".to_string() },
        EmailTask { to: "c@example.com".to_string(), subject: "Hello".to_string(), body: "...".to_string() },
    ];

    // 方式1：启动并获取句柄（如果需要结果）
    let handles = sender.spawn_instances(emails.clone()).await;

    // 方式2：完全无同步（fire and forget）
    // sender.spawn_and_forget(emails);

    println!("已创建 {} 个实例", sender.get_spawned_count());

    // 如果需要，稍后收集结果
    for handle in handles {
        if let Ok(result) = handle.await {
            println!("发送结果: {:?}", result);
        }
    }
}

/// 动态实例创建（基于流）
use tokio::sync::mpsc;

pub struct DynamicMultiInstance<T, R> {
    sender: mpsc::Sender<T>,
    result_receiver: Arc<tokio::sync::Mutex<mpsc::Receiver<R>>>,
}

impl<T: Send + 'static, R: Send + 'static> DynamicMultiInstance<T, R> {
    pub fn new<F, Fut>(factory: F) -> (Self, mpsc::Receiver<R>)
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        let (input_tx, mut input_rx) = mpsc::channel::<T>(100);
        let (output_tx, output_rx) = mpsc::channel::<R>(100);

        // 后台处理器
        tokio::spawn(async move {
            while let Some(item) = input_rx.recv().await {
                let factory = &factory;
                let output_tx = output_tx.clone();

                tokio::spawn(async move {
                    let result = factory(item).await;
                    let _ = output_tx.send(result).await;
                });
            }
        });

        let instance = Self {
            sender: input_tx,
            result_receiver: Arc::new(tokio::sync::Mutex::new(output_rx)),
        };

        (instance, output_rx)
    }

    pub async fn submit(&self, item: T) -> Result<(), mpsc::error::SendError<T>> {
        self.sender.send(item).await
    }
}

/// 使用 rayon 的 CPU 密集型并行
use rayon::prelude::*;

pub fn parallel_cpu_work(items: Vec<i32>) -> Vec<i32> {
    items
        .into_par_iter()
        .map(|x| x * x) // CPU 密集型计算
        .collect()
}
```

## 与其他模式的关系

| 模式 | 同步 | 实例数确定时机 |
|------|------|----------------|
| **MI 无同步** | 否 | 运行时 |
| MI 有同步 | 是 | 运行时 |
| 并行分支 | 是（AND-Join） | 设计时 |
| 动态并行 | 可选 | 运行时 |

**关系公式：**

$$
\text{MIWithoutSync} = \text{ParallelSplit} + \text{DynamicInstanceCount}
$$

## 应用场景

1. **批量处理**：处理大量独立记录
2. **通知发送**：同时发送多个独立通知
3. **数据转换**：并行转换大量数据项
4. **请求扇出**：并行调用多个独立服务

### 注意事项

- 注意资源限制，避免创建过多实例
- 考虑使用信号量控制并发度
- 独立实例间的数据竞争需要防范
- 监控实例完成情况（即使不等待）
