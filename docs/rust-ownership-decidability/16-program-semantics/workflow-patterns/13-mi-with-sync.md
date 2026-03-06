# 13 多实例有同步模式 (Multiple Instances With Synchronization)

## 模式定义与语义

多实例有同步模式在运行时创建多个活动实例，等待所有实例完成后才继续执行。
这是最常用的并行处理模式之一。

### 核心语义

$$
\text{MIWithSync}(A, n) = \text{join}(\parallel_{i=1}^{n} A_i)
$$

其中 $n$ 是运行时确定，必须等待所有 $n$ 个实例完成。

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State} = \{ \text{Ready}, \text{Spawning}, \text{Executing}, \text{Waiting}, \text{Completed} \} \\
& \text{Transition} = \{ \\
& \quad (\text{Ready}, \text{determine}(n), \text{Spawning}), \\
& \quad (\text{Spawning}, \text{spawn\_all}, \text{Executing}), \\
& \quad (\text{Executing}, \text{complete}_i, \text{Waiting}), \\
& \quad (\text{Waiting}, \text{all\_done}, \text{Completed}) \\
& \}
\end{aligned}
$$

**流程代数：**

$$
\text{MIWithSync} = \Pi_{i=1}^{n} A_i \triangleright \text{continue}
$$

## Rust 实现示例

```rust
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use tokio::sync::Barrier;

/// 多实例有同步执行器
pub struct MultiInstanceWithSync<T, R> {
    factory: Arc<dyn Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync>,
}

impl<T: Send + 'static, R: Send + 'static> MultiInstanceWithSync<T, R> {
    pub fn new<F, Fut>(factory: F) -> Self
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        Self {
            factory: Arc::new(move |t| Box::pin(factory(t))),
        }
    }

    /// 执行并等待所有实例
    pub async fn execute(&self, items: Vec<T>) -> Vec<R> {
        if items.is_empty() {
            return Vec::new();
        }

        let mut handles = Vec::with_capacity(items.len());

        for item in items {
            let factory = Arc::clone(&self.factory);

            let handle = tokio::spawn(async move {
                let future = factory(item);
                future.await
            });

            handles.push(handle);
        }

        // 等待所有实例完成
        let mut results = Vec::with_capacity(handles.len());
        for handle in handles {
            match handle.await {
                Ok(result) => results.push(result),
                Err(e) => {
                    eprintln!("任务执行失败: {:?}", e);
                    // 可以选择 panic 或返回部分结果
                }
            }
        }

        results
    }

    /// 使用 join_all 的实现
    pub async fn execute_join_all(&self, items: Vec<T>) -> Vec<R> {
        let futures: Vec<_> = items
            .into_iter()
            .map(|item| {
                let factory = Arc::clone(&self.factory);
                async move { factory(item).await }
            })
            .collect();

        futures::future::join_all(futures).await
    }

    /// 带超时的执行
    pub async fn execute_with_timeout(
        &self,
        items: Vec<T>,
        timeout: std::time::Duration,
    ) -> Result<Vec<R>, tokio::time::error::Elapsed> {
        tokio::time::timeout(timeout, self.execute(items)).await
    }
}

/// 使用示例：并行下载
#[derive(Clone)]
struct DownloadTask {
    url: String,
    filename: String,
}

#[derive(Debug)]
struct DownloadResult {
    filename: String,
    bytes_downloaded: usize,
    success: bool,
}

async fn download_file(task: DownloadTask) -> DownloadResult {
    // 模拟下载
    let delay = task.url.len() as u64 * 10;
    tokio::time::sleep(tokio::time::Duration::from_millis(delay)).await;

    DownloadResult {
        filename: task.filename.clone(),
        bytes_downloaded: 1024,
        success: true,
    }
}

pub async fn parallel_download_example() {
    let downloader = MultiInstanceWithSync::new(download_file);

    let tasks = vec![
        DownloadTask { url: "https://a.com/file1".to_string(), filename: "file1.txt".to_string() },
        DownloadTask { url: "https://b.com/file2".to_string(), filename: "file2.txt".to_string() },
        DownloadTask { url: "https://c.com/file3".to_string(), filename: "file3.txt".to_string() },
    ];

    println!("开始并行下载 {} 个文件...", tasks.len());

    let results = downloader.execute(tasks).await;

    println!("所有下载完成:");
    for result in &results {
        println!("  {}: {} bytes", result.filename, result.bytes_downloaded);
    }
}

/// 使用 Rayon 的 CPU 密集型并行
use rayon::prelude::*;

pub struct ParallelProcessor;

impl ParallelProcessor {
    /// 并行处理数据并收集结果
    pub fn process_data<T, R, F>(items: Vec<T>, processor: F) -> Vec<R>
    where
        T: Send + Sync,
        R: Send + Sync,
        F: Fn(&T) -> R + Send + Sync,
    {
        items.par_iter().map(processor).collect()
    }

    /// 并行求和
    pub fn parallel_sum(numbers: &[i32]) -> i32 {
        numbers.par_iter().sum()
    }
}

/// 带进度报告的多实例
use tokio::sync::mpsc;

pub struct ProgressMultiInstance<T, R> {
    factory: Arc<dyn Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync>,
}

impl<T: Send + 'static, R: Send + 'static> ProgressMultiInstance<T, R> {
    pub fn new<F, Fut>(factory: F) -> Self
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        Self {
            factory: Arc::new(move |t| Box::pin(factory(t))),
        }
    }

    pub async fn execute_with_progress(
        &self,
        items: Vec<T>,
        progress_tx: mpsc::Sender<(usize, usize)>, // (completed, total)
    ) -> Vec<R> {
        let total = items.len();
        let completed = Arc::new(tokio::sync::Mutex::new(0usize));

        let futures: Vec<_> = items
            .into_iter()
            .enumerate()
            .map(|(index, item)| {
                let factory = Arc::clone(&self.factory);
                let completed = Arc::clone(&completed);
                let progress_tx = progress_tx.clone();

                async move {
                    let result = factory(item).await;

                    let mut count = completed.lock().await;
                    *count += 1;
                    let current = *count;
                    drop(count);

                    let _ = progress_tx.send((current, total)).await;

                    (index, result)
                }
            })
            .collect();

        let mut indexed_results: Vec<_> = futures::future::join_all(futures).await;
        indexed_results.sort_by_key(|(i, _)| *i);

        indexed_results.into_iter().map(|(_, r)| r).collect()
    }
}

/// 错误处理变体：允许部分失败
pub struct FaultTolerantMultiInstance<T, R, E> {
    factory: Arc<dyn Fn(T) -> Pin<Box<dyn Future<Output = Result<R, E>> + Send>> + Send + Sync>,
}

impl<T, R, E> FaultTolerantMultiInstance<T, R, E>
where
    T: Send + 'static,
    R: Send + 'static,
    E: Send + 'static,
{
    pub fn new<F, Fut>(factory: F) -> Self
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<R, E>> + Send + 'static,
    {
        Self {
            factory: Arc::new(move |t| Box::pin(factory(t))),
        }
    }

    pub async fn try_execute(&self, items: Vec<T>) -> Vec<Result<R, E>> {
        let futures: Vec<_> = items
            .into_iter()
            .map(|item| {
                let factory = Arc::clone(&self.factory);
                async move { factory(item).await }
            })
            .collect();

        futures::future::join_all(futures).await
    }
}
```

## 与其他模式的关系

| 模式 | 同步 | 容错性 |
|------|------|--------|
| **MI 有同步** | 是 | 可配置 |
| MI 无同步 | 否 | 无保证 |
| 并行分支 | 是 | 设计时确定 |
| 部分汇合 | 等待部分 | 灵活 |

**关系公式：**

$$
\text{MIWithSync} = \text{MIWithoutSync} + \text{BarrierSynchronization}
$$

## 应用场景

1. **批量数据处理**：等待所有记录处理完成
2. **并行计算**：Map 阶段完成后进行 Reduce
3. **分布式事务**：等待所有参与者投票
4. **并发测试**：等待所有测试用例完成

### 注意事项

- 考虑超时处理，避免无限等待
- 实现适当的错误处理策略
- 注意内存使用随实例数增长
- 监控长时间运行的实例
