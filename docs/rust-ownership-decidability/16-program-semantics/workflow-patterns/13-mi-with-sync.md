# 13 多实例有同步模式 (Multiple Instances With Synchronization)

## 📋 目录

- [13 多实例有同步模式 (Multiple Instances With Synchronization)](#13-多实例有同步模式-multiple-instances-with-synchronization)
  - [📋 目录](#-目录)
  - [模式定义与语义](#模式定义与语义)
    - [核心语义](#核心语义)
    - [先验设计时知识](#先验设计时知识)
  - [BPMN 2.0 表示](#bpmn-20-表示)
  - [形式化语义](#形式化语义)
    - [状态机形式化](#状态机形式化)
    - [进程代数](#进程代数)
    - [屏障同步](#屏障同步)
  - [正确性证明](#正确性证明)
    - [汇合安全性](#汇合安全性)
    - [活性保证](#活性保证)
  - [Rust 实现示例](#rust-实现示例)
    - [基础实现](#基础实现)
    - [进度报告实现](#进度报告实现)
    - [容错实现](#容错实现)
  - [与其他模式的关系](#与其他模式的关系)
  - [应用场景](#应用场景)
    - [注意事项](#注意事项)
  - [学术参考](#学术参考)

## 模式定义与语义

多实例有同步模式在运行时创建多个活动实例，等待所有实例完成后才继续执行。
这是最常用的并行处理模式之一。

### 核心语义

$$
\text{MIWithSync}(A, n) = \text{join}(\parallel_{i=1}^{n} A_i)
$$

其中 $n$ 是运行时确定，必须等待所有 $n$ 个实例完成。

**执行流程：**

1. **创建阶段**: 动态确定实例数量 $n$
2. **执行阶段**: 所有 $n$ 个实例并行执行
3. **同步阶段**: 等待所有实例完成
4. **汇合阶段**: 收集结果，继续后续流程

### 先验设计时知识

**先验知识类型：**

| 类型 | 描述 | 示例 |
|------|------|------|
| 设计时已知 | 实例数在流程定义时确定 | 固定3个审批人 |
| 运行时已知 | 实例数在启动前确定 | 根据订单项数 |
| 运行时未知 | 实例数在执行中确定 | 动态发现子任务 |

本模式处理**运行时已知**的情况：

$$
\text{RuntimeKnown}(items) = |items| \text{ determined at } t_{start}
$$

## BPMN 2.0 表示

在 BPMN 2.0 中，多实例有同步使用 `isSequential="false"` 配合**并行网关**或**结束事件**实现：

```xml
<?xml version="1.0" encoding="UTF-8"?>
<bpmn:definitions xmlns:bpmn="http://www.omg.org/spec/BPMN/20100524/MODEL">
  <bpmn:process id="MIWithSyncProcess" isExecutable="true">

    <!-- 动态确定实例数 -->
    <bpmn:task id="DetermineItems" name="Get Items to Process"/>

    <!-- 多实例活动：并行执行，等待全部完成 -->
    <bpmn:task id="ParallelProcessing" name="Process Each Item">
      <bpmn:incoming>Flow_Determine</bpmn:incoming>
      <bpmn:outgoing>Flow_Join</bpmn:outgoing>
      <bpmn:multiInstanceLoopCharacteristics isSequential="false">
        <bpmn:loopDataInputRef>items</bpmn:loopDataInputRef>
        <bpmn:inputDataItem name="currentItem"/>
        <bpmn:completionCondition>${completionRate == 1.0}</bpmn:completionCondition>
      </bpmn:multiInstanceLoopCharacteristics>
    </bpmn:task>

    <!-- 同步汇合点 -->
    <bpmn:parallelGateway id="Synchronization" gatewayDirection="Converging">
      <bpmn:incoming>Flow_Join</bpmn:incoming>
      <bpmn:outgoing>Flow_Next</bpmn:outgoing>
    </bpmn:parallelGateway>

    <!-- 后续活动（等待所有实例完成后执行） -->
    <bpmn:task id="AggregateResults" name="Aggregate Results">
      <bpmn:incoming>Flow_Next</bpmn:incoming>
    </bpmn:task>

  </bpmn:process>
</bpmn:definitions>
```

**图形表示：**

```
                    ┌─────────┐
                    │  Start  │
                    └────┬────┘
                         │
                         ▼
              ┌─────────────────────┐
              │  Determine Items    │
              │  (Runtime Count)    │
              │  items = [A,B,C,D]  │
              └──────────┬──────────┘
                         │
                         ▼
              ┌─────────────────────┐
              │  [===]              │  ◄── 并行多实例
              │  Process Item       │
              │  ━━━━━━━━━━━━━━━━   │
              └──────────┬──────────┘
                         │
       ┌─────────────────┼─────────────────┐
       │                 │                 │
       ▼                 ▼                 ▼
  ┌─────────┐      ┌─────────┐      ┌─────────┐
  │Instance1│      │Instance2│      │Instance3│ ... InstanceN
  │  Item A │      │  Item B │      │  Item C │
  └────┬────┘      └────┬────┘      └────┬────┘
       │                 │                 │
       │                 │                 │
       └─────────────────┼─────────────────┘
                         │
                         ▼
              ┌─────────────────────┐
              │   Synchronization   │ ◄── 等待所有实例完成
              │   (Parallel Join)   │
              └──────────┬──────────┘
                         │
                         ▼
              ┌─────────────────────┐
              │  Aggregate Results  │
              │  (All results ready)│
              └─────────────────────┘
```

## 形式化语义

### 状态机形式化

$$
\begin{aligned}
& \text{States} = \{ \\
& \quad \text{READY}: \text{准备}, \\
& \quad \text{SPAWNING}(k, n): \text{已创建 } k \text{ 个，共 } n \text{ 个}, \\
& \quad \text{EXECUTING}(active): \text{执行中，活跃 } active \text{ 个}, \\
& \quad \text{WAITING}(remaining): \text{等待，剩余 } remaining \text{ 个}, \\
& \quad \text{SYNCING}: \text{同步中}, \\
& \quad \text{COMPLETED}(results): \text{完成，结果收集} \\
& \} \\
& \text{Transitions} = \{ \\
& \quad \text{READY} \xrightarrow{\text{determine}(n)} \text{SPAWNING}(0, n), \\
& \quad \text{SPAWNING}(k, n) \xrightarrow{\text{spawn}} \text{SPAWNING}(k+1, n), \\
& \quad \text{SPAWNING}(n, n) \xrightarrow{\tau} \text{EXECUTING}(n), \\
& \quad \text{EXECUTING}(k) \xrightarrow{\text{complete}_i} \text{WAITING}(k-1), \\
& \quad \text{WAITING}(0) \xrightarrow{\tau} \text{SYNCING}, \\
& \quad \text{SYNCING} \xrightarrow{\text{collect}} \text{COMPLETED} \\
& \}
\end{aligned}
$$

### 进程代数

**CSP 形式化：**

```csp
-- 多实例有同步的 CSP 形式化

-- 单个实例
Instance(i, item) = spawn.i -> process(item) -> complete.i!result -> SKIP

-- 屏障同步
Barrier(n) = barrier?(i=1..n) -> sync -> SKIP

-- 多实例有同步
MIWithSync(items) =
    let n = |items|
    within
        (||| i:items @ Instance(i))
        [|{complete}|]
        Barrier(n)
```

**CCS 表示：**

```ccs
-- 实例代理
Instance(i, item) ::= spawn_i.process_item_i.complete_i<r>.0

-- 汇合控制器
Controller(n) ::= complete_1?r1...complete_n?rn.collect<results>.0

-- 组合
MIWithSync(items) ::=
    (Instance(1, item1) | ... | Instance(n, itemn) | Controller(n))
    \ {complete_1, ..., complete_n}
```

### 屏障同步

**屏障语义：**

$$
\text{Barrier}(n) = \{ (P_1, P_2, \ldots, P_n) \mid \forall i: P_i \text{ arrives} \} \to \text{proceed}
$$

**实现模式：**

```
            Arrive(P1)          Arrive(P2)          Arrive(P3)
                │                   │                   │
                ▼                   ▼                   ▼
         ┌─────────────┐     ┌─────────────┐     ┌─────────────┐
         │   Wait at   │     │   Wait at   │     │   Wait at   │
         │   Barrier   │     │   Barrier   │     │   Barrier   │
         └──────┬──────┘     └──────┬──────┘     └──────┬──────┘
                │                   │                   │
                └───────────────────┼───────────────────┘
                                    │
                    ┌───────────────┴───────────────┐
                    ▼                               ▼
              Count == N?                      Not yet
                    │                               │
            ┌───────┴───────┐                       │
            ▼               ▼                       │
       ┌─────────┐    ┌─────────┐                   │
       │ Release │    │ Continue│◄──────────────────┘
       │ Barrier │    │ Waiting │
       └────┬────┘    └─────────┘
            │
            ▼
    All Proceed Together
```

## 正确性证明

### 汇合安全性

**定理（安全汇合）**: 只有所有 $n$ 个实例都完成后，同步点才会放行。

**证明:**

设实例集合 $I = \{1, 2, \ldots, n\}$，计数器 $c$ 跟踪已完成实例。

1. 初始化: $c = 0$
2. 不变式: $c = |\{i \in I \mid \text{instance}_i \text{ completed}\}|$
3. 每个完成事件使 $c \leftarrow c + 1$
4. 放行条件: $c = n \iff \forall i \in I: \text{instance}_i \text{ completed}$

因此安全性得证。∎

### 活性保证

**定理（最终汇合）**: 如果所有实例最终完成，则同步最终会发生。

**证明:**

假设每个实例 $i$ 最终完成。

1. 设实例 $i$ 在时间 $t_i$ 完成
2. 设 $T = \max(t_1, t_2, \ldots, t_n)$
3. 在时间 $T$，所有实例都已完成
4. 因此 $c = n$，触发同步
5. 后续流程继续

因此汇合最终发生。∎

**定理（无死锁）**: 多实例有同步模式不会导致死锁（假设实例有活性）。

**证明:**

考虑所有可能阻塞情况：

1. 如果某个实例无限执行：违反实例活性假设
2. 如果同步机制故障：实现层面的问题，非模式本身

在实例有活性的假设下，所有实例最终完成，同步发生。∎

## Rust 实现示例

### 基础实现

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
```

### 进度报告实现

```rust
use tokio::sync::mpsc;

/// 带进度报告的多实例
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

/// 使用示例：带进度条的下载
pub async fn download_with_progress() {
    let downloader = ProgressMultiInstance::new(|url: String| async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        format!("Downloaded: {}", url)
    });

    let urls = vec![
        "https://example.com/1".to_string(),
        "https://example.com/2".to_string(),
        "https://example.com/3".to_string(),
    ];

    let (tx, mut rx) = mpsc::channel(10);

    // 进度显示任务
    let progress_handle = tokio::spawn(async move {
        while let Some((completed, total)) = rx.recv().await {
            let percentage = (completed as f64 / total as f64) * 100.0;
            println!("进度: {}/{} ({:.1}%)", completed, total, percentage);
            if completed == total {
                break;
            }
        }
    });

    let results = downloader.execute_with_progress(urls, tx).await;
    println!("结果: {:?}", results);

    let _ = progress_handle.await;
}
```

### 容错实现

```rust
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

    /// 只返回成功的结果
    pub async fn execute_collect_success(&self, items: Vec<T>) -> Vec<R> {
        let results = self.try_execute(items).await;
        results.into_iter().filter_map(|r| r.ok()).collect()
    }

    /// 带成功阈值（至少 N 个成功）
    pub async fn execute_with_threshold(
        &self,
        items: Vec<T>,
        min_success: usize,
    ) -> Result<Vec<R>, ThresholdError> {
        let results = self.try_execute(items).await;

        let successes: Vec<_> = results.iter().filter(|r| r.is_ok()).collect();

        if successes.len() >= min_success {
            Ok(results.into_iter().filter_map(|r| r.ok()).collect())
        } else {
            Err(ThresholdError {
                required: min_success,
                actual: successes.len(),
            })
        }
    }
}

#[derive(Debug)]
pub struct ThresholdError {
    required: usize,
    actual: usize,
}

impl std::fmt::Display for ThresholdError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "需要 {} 个成功，实际只有 {}", self.required, self.actual)
    }
}

impl std::error::Error for ThresholdError {}

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
5. **分片处理**：等待所有分片处理完成
6. **聚合计算**：收集所有部分结果后汇总

### 注意事项

- 考虑超时处理，避免无限等待
- 实现适当的错误处理策略
- 注意内存使用随实例数增长
- 监控长时间运行的实例
- 实现部分失败处理
- 使用进度报告监控执行

## 学术参考

1. **Russell, N., ter Hofstede, A.H.M., van der Aalst, W.M.P., & Mulyar, N.** (2006). "Workflow Control-Flow Patterns: A Revised View." *BPM Center Report* BPM-06-22.

2. **Baude, F., et al.** (2009). "Petals: A Distributed Service-Oriented Component Framework for HPC Applications." *Parallel Processing Letters*, 19(4), 631-644.

3. **Kumar, A., & Zhao, J.L.** (2002). "Dynamic Routing and Operational Controls in Workflow Management Systems." *Management Science*, 50(3), 405-417.

4. **Reichert, M., & Dadam, P.** (1998). "ADEPTflex - Supporting Dynamic Changes of Workflows Without Losing Control." *Journal of Intelligent Information Systems*, 10(2), 93-129.

5. **Sadiq, W., & Orlowska, M.E.** (2000). "Analyzing Process Models Using Graph Reduction Techniques." *Information Systems*, 25(2), 117-134.
