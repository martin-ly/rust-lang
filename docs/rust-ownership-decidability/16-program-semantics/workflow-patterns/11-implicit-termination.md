# 11 隐式终止模式 (Implicit Termination)

## 模式定义与语义

隐式终止模式允许工作流在没有显式终止节点的情况下完成。
当所有活跃路径都自然结束时，工作流被视为完成。

### 核心语义

$$
\text{ImplicitTermination} = \text{when } \nexists \text{ active tokens}: \text{workflow completes}
$$

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State} = \{ \text{Running}, \text{NoActivePaths}, \text{Completed} \} \\
& \text{Transition} = \{ \\
& \quad (\text{Running}, \text{path\_completes}, \text{Running}) \text{ if other paths active}, \\
& \quad (\text{Running}, \text{last\_path\_completes}, \text{NoActivePaths}), \\
& \quad (\text{NoActivePaths}, \epsilon, \text{Completed}) \\
& \}
\end{aligned}
$$

**进程代数：**

$$
\text{ImplicitTermination} = P \parallel Q \parallel R \triangleright_{\text{all done}} \text{end}
$$

## Rust 实现示例

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use tokio::sync::watch;

/// 隐式终止工作流执行器
pub struct ImplicitTerminationFlow<T> {
    active_paths: Arc<AtomicUsize>,
    completion_tx: watch::Sender<bool>,
    completion_rx: watch::Receiver<bool>,
    result: Arc<tokio::sync::Mutex<Option<T>>>,
}

impl<T: Clone + Send + 'static> ImplicitTerminationFlow<T> {
    pub fn new() -> Self {
        let (tx, rx) = watch::channel(false);
        Self {
            active_paths: Arc::new(AtomicUsize::new(0)),
            completion_tx: tx,
            completion_rx: rx,
            result: Arc::new(tokio::sync::Mutex::new(None)),
        }
    }

    /// 创建一个新的执行路径
    pub fn create_path(&self) -> PathHandle<T> {
        self.active_paths.fetch_add(1, Ordering::SeqCst);

        PathHandle {
            active_paths: Arc::clone(&self.active_paths),
            completion_tx: self.completion_tx.clone(),
            result: Arc::clone(&self.result),
        }
    }

    /// 等待工作流完成
    pub async fn wait_for_completion(mut self) -> Option<T> {
        // 如果没有活跃路径，立即完成
        if self.active_paths.load(Ordering::SeqCst) == 0 {
            return self.result.lock().await.clone();
        }

        // 等待完成信号
        while !*self.completion_rx.borrow() {
            if self.completion_rx.changed().await.is_err() {
                break;
            }
        }

        self.result.lock().await.clone()
    }
}

pub struct PathHandle<T> {
    active_paths: Arc<AtomicUsize>,
    completion_tx: watch::Sender<bool>,
    result: Arc<tokio::sync::Mutex<Option<T>>>,
}

impl<T: Clone> PathHandle<T> {
    pub async fn complete(self, result: T) {
        // 存储结果
        let mut guard = self.result.lock().await;
        *guard = Some(result);
        drop(guard);

        // 减少活跃路径计数
        let remaining = self.active_paths.fetch_sub(1, Ordering::SeqCst);

        // 如果是最后一个路径，发送完成信号
        if remaining == 1 {
            let _ = self.completion_tx.send(true);
        }
    }
}

/// 使用示例：并行处理
pub async fn implicit_termination_example() {
    let flow: ImplicitTerminationFlow<Vec<String>> = ImplicitTerminationFlow::new();
    let mut handles = vec![];

    // 创建多个并行路径
    for i in 0..3 {
        let path = flow.create_path();
        let handle = tokio::spawn(async move {
            // 模拟处理
            tokio::time::sleep(tokio::time::Duration::from_millis(
                100 * (i + 1) as u64
            )).await;

            path.complete(vec![format!("result_{}", i)]).await;
        });
        handles.push(handle);
    }

    // 等待所有路径完成
    for handle in handles {
        let _ = handle.await;
    }

    let result = flow.wait_for_completion().await;
    println!("工作流完成，结果: {:?}", result);
}

/// 基于 Future 的隐式终止
use std::future::Future;

pub struct FutureFlow<T> {
    futures: Vec<Pin<Box<dyn Future<Output = T> + Send>>>,
}

use std::pin::Pin;

impl<T> FutureFlow<T> {
    pub fn new() -> Self {
        Self { futures: Vec::new() }
    }

    pub fn add_future(&mut self, future: impl Future<Output = T> + Send + 'static) {
        self.futures.push(Box::pin(future));
    }

    pub async fn execute(mut self) -> Vec<T>
    where
        T: Send + 'static,
    {
        if self.futures.is_empty() {
            return Vec::new();
        }

        let mut results = Vec::with_capacity(self.futures.len());

        // 使用 join_all 等待所有 future
        for result in futures::future::join_all(self.futures).await {
            results.push(result);
        }

        results
    }
}

/// 使用 tokio::spawn 的隐式终止
pub async fn spawn_based_termination() {
    let handles: Vec<tokio::task::JoinHandle<i32>> = vec![
        tokio::spawn(async { 1 }),
        tokio::spawn(async { 2 }),
        tokio::spawn(async { 3 }),
    ];

    // 隐式等待所有任务完成
    let results: Vec<i32> = futures::future::join_all(handles)
        .await
        .into_iter()
        .filter_map(|r| r.ok())
        .collect();

    println!("所有任务完成: {:?}", results);
}
```

## 与其他模式的关系

| 模式 | 终止方式 | 使用场景 |
|------|----------|----------|
| 显式终止 | 到达终止节点 | 需要明确结束点 |
| **隐式终止** | 所有路径结束 | 自然流程结束 |
| 取消终止 | 主动取消 | 异常处理 |

**关系公式：**

$$
\text{ExplicitTermination} \cong \text{ImplicitTermination} \text{（功能等价）}
$$

## 应用场景

1. **并行计算**：Map-Reduce 任务自然完成
2. **批处理**：所有记录处理完毕后自动结束
3. **事件驱动**：处理完所有待处理事件后停止
4. **数据流处理**：输入流结束后自动终止

### 注意事项

- 需要确保所有路径最终都会结束（终止性验证）
- 避免死锁导致工作流永不结束
- 考虑超时机制作为安全网
- 明确未完成路径的处理策略
