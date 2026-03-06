# 18 取消活动模式 (Cancel Activity)

## 模式定义与语义

取消活动模式允许在另一个活动的执行过程中取消一个已启用的活动。这是工作流异常处理的基础机制。

### 核心语义

$$
\text{CancelActivity}(A, C) = \text{when } C \text{ occurs}: \text{abort}(A)
$$

其中 $A$ 是被取消的活动，$C$ 是取消条件或取消事件。

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State}_A = \{ \text{Inactive}, \text{Active}, \text{Completing}, \text{Completed}, \text{Cancelling}, \text{Cancelled} \} \\
& \text{Transition} = \{ \\
& \quad (\text{Inactive}, \text{enable}, \text{Active}), \\
& \quad (\text{Active}, \text{normal\_complete}, \text{Completing}), \\
& \quad (\text{Active}, C, \text{Cancelling}), \\
& \quad (\text{Cancelling}, \text{cleanup}, \text{Cancelled}) \\
& \}
\end{aligned}
$

**进程代数：**

$$
A \triangleleft C = \text{if } C \text{ then } \text{cleanup} \to \text{stop} \text{ else } A
$$

## Rust 实现示例

```rust
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use tokio::sync::{mpsc, oneshot, watch};
use tokio::task::AbortHandle;

/// 可取消活动
pub struct CancellableActivity<T, R> {
    cancel_tx: watch::Sender<bool>,
    task_handle: Option<AbortHandle>,
    result_rx: Option<oneshot::Receiver<R>>,
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Send + 'static, R: Send + 'static> CancellableActivity<T, R> {
    pub fn new<F, Fut>(
        task: F,
        input: T,
    ) -> Self
    where
        F: Fn(T, watch::Receiver<bool>) -> Fut + Send + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        let (cancel_tx, cancel_rx) = watch::channel(false);
        let (result_tx, result_rx) = oneshot::channel();

        let handle = tokio::spawn(async move {
            let result = task(input, cancel_rx).await;
            let _ = result_tx.send(result);
        });

        Self {
            cancel_tx,
            task_handle: Some(handle.abort_handle()),
            result_rx: Some(result_rx),
            _phantom: std::marker::PhantomData,
        }
    }

    /// 取消活动
    pub fn cancel(&self) -> Result<(), String> {
        // 发送取消信号
        if self.cancel_tx.send(true).is_err() {
            return Err("取消通道已关闭".to_string());
        }

        // 中止任务
        if let Some(ref handle) = self.task_handle {
            handle.abort();
        }

        Ok(())
    }

    /// 等待结果
    pub async fn wait(mut self) -> Result<R, String> {
        match self.result_rx.take() {
            Some(rx) => rx.await.map_err(|_| "接收结果失败".to_string()),
            None => Err("结果已被获取".to_string()),
        }
    }
}

/// 使用示例：可取消的数据处理
async fn process_data_with_cancellation(
    data: Vec<u8>,
    mut cancel_rx: watch::Receiver<bool>,
) -> Result<String, String> {
    let chunks = data.chunks(1024);
    let mut processed = 0;

    for (i, chunk) in chunks.enumerate() {
        // 检查取消信号
        if *cancel_rx.borrow() {
            return Err("任务被取消".to_string());
        }

        // 异步处理块
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        processed += chunk.len();

        println!("处理块 {}: {} 字节", i, processed);
    }

    Ok(format!("成功处理 {} 字节", processed))
}

pub async fn cancellable_activity_example() {
    let data = vec![0u8; 10240]; // 10KB 数据

    let activity = CancellableActivity::new(process_data_with_cancellation, data);

    // 模拟一段时间后取消
    tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        println!("发送取消信号...");
        // 需要在某处保存 activity 的引用才能取消
    });

    match activity.wait().await {
        Ok(result) => println!("结果: {}", result),
        Err(e) => println!("错误: {}", e),
    }
}

/// 基于 select! 的取消
pub async fn cancellable_with_select<F, R>(
    future: F,
    cancel_rx: &mut mpsc::Receiver<()>,
) -> Option<R>
where
    F: Future<Output = R>,
{
    tokio::select! {
        result = future => Some(result),
        _ = cancel_rx.recv() => {
            println!("任务被取消");
            None
        }
    }
}

/// 取消令牌模式
pub struct CancellationToken {
    cancelled: Arc<AtomicBool>,
    waker: Arc<tokio::sync::Notify>,
}

impl CancellationToken {
    pub fn new() -> Self {
        Self {
            cancelled: Arc::new(AtomicBool::new(false)),
            waker: Arc::new(tokio::sync::Notify::new()),
        }
    }

    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::SeqCst);
        self.waker.notify_waiters();
    }

    pub fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::SeqCst)
    }

    pub async fn cancelled(&self) {
        while !self.is_cancelled() {
            self.waker.notified().await;
        }
    }

    /// 检查点 - 可以在任务中调用以响应取消
    pub fn check_cancel(&self) -> Result<(), String> {
        if self.is_cancelled() {
            Err("任务已取消".to_string())
        } else {
            Ok(())
        }
    }
}

/// 使用示例：检查点模式
pub async fn checkpoint_cancellation() {
    let token = Arc::new(CancellationToken::new());

    // 取消任务
    let token_clone = Arc::clone(&token);
    tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        println!("触发取消...");
        token_clone.cancel();
    });

    // 执行带检查点的任务
    for i in 0..10 {
        if let Err(e) = token.check_cancel() {
            println!("在第 {} 步取消: {}", i, e);
            return;
        }

        println!("执行步骤 {}", i);
        tokio::time::sleep(tokio::time::Duration::from_millis(30)).await;
    }

    println!("任务完成");
}

/// 组合取消 - 多个取消源
pub struct CombinedCancellation {
    tokens: Vec<Arc<CancellationToken>>,
}

impl CombinedCancellation {
    pub fn new(tokens: Vec<Arc<CancellationToken>>) -> Self {
        Self { tokens }
    }

    pub fn is_cancelled(&self) -> bool {
        self.tokens.iter().any(|t| t.is_cancelled())
    }

    pub async fn cancel(&self) {
        for token in &self.tokens {
            token.cancel();
        }
    }
}
```

## 与其他模式的关系

| 模式 | 取消范围 | 触发方式 |
|------|----------|----------|
| **取消活动** | 单个活动 | 事件/条件 |
| 取消案例 | 整个案例 | 事件 |
| 取消区域 | 区域内所有 | 事件 |
| 取消多实例 | 多个实例 | 事件 |

**关系公式：**

$$
\text{CancelActivity} \subset \text{CancelRegion} \subset \text{CancelCase}
$$

## 应用场景

1. **超时处理**：任务超时自动取消
2. **用户中断**：用户主动取消操作
3. **依赖失败**：前置任务失败取消后续任务
4. **资源限制**：资源不足时取消低优先级任务

### 注意事项

- 确保取消后资源正确释放
- 处理取消与完成的竞态条件
- 提供清理（cleanup）机制
- 支持协作式取消（检查点）
