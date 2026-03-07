# 12 多实例无同步模式 (Multiple Instances Without Synchronization)

## 📋 目录

- [12 多实例无同步模式 (Multiple Instances Without Synchronization)](#12-多实例无同步模式-multiple-instances-without-synchronization)
  - [📋 目录](#-目录)
  - [模式定义与语义](#模式定义与语义)
    - [核心语义](#核心语义)
    - [动态实例创建语义](#动态实例创建语义)
  - [BPMN 2.0 表示](#bpmn-20-表示)
    - [多实例活动](#多实例活动)
    - [循环活动](#循环活动)
  - [形式化语义](#形式化语义)
    - [状态机形式化](#状态机形式化)
    - [进程代数](#进程代数)
  - [正确性证明](#正确性证明)
    - [活性证明](#活性证明)
    - [资源安全性](#资源安全性)
  - [Rust 实现示例](#rust-实现示例)
    - [基础实现](#基础实现)
    - [动态实例池](#动态实例池)
    - [流式处理实现](#流式处理实现)
  - [与其他模式的关系](#与其他模式的关系)
  - [应用场景](#应用场景)
    - [注意事项](#注意事项)
  - [学术参考](#学术参考)

## 模式定义与语义

多实例无同步模式允许在运行时并行创建多个活动实例，这些实例独立执行且不需要同步汇合。
实例数量通常在运行时才能确定。

### 核心语义

$$
\text{MIWithoutSync}(A, n) = \parallel_{i=1}^{n} A_i
$$

其中 $n$ 是运行时确定的实例数量，$A_i$ 相互独立。

**关键特性：**

1. **运行时确定实例数**: $n$ 在流程执行时才能确定
2. **并行执行**: 所有实例同时执行
3. **无同步**: 实例之间不需要等待或汇合
4. **独立完成**: 每个实例独立开始和结束

### 动态实例创建语义

实例创建的时序语义：

$$
\text{CreateInstances}(items) = \forall item \in items: \text{spawn}(A(item))
$$

创建开销模型：

$$
\text{Overhead}(n) = n \times \text{spawn\_cost} + \text{coordination\_cost}
$$

## BPMN 2.0 表示

在 BPMN 2.0 中，多实例无同步使用**多实例活动（Multi-Instance Activity）**配合 `isSequential="false"` 和 `completionCondition` 实现：

```xml
<?xml version="1.0" encoding="UTF-8"?>
<bpmn:definitions xmlns:bpmn="http://www.omg.org/spec/BPMN/20100524/MODEL">
  <bpmn:process id="MIWithoutSyncProcess" isExecutable="true">

    <!-- 开始 -->
    <bpmn:startEvent id="Start"/>

    <!-- 动态确定实例数 -->
    <bpmn:task id="DetermineCount" name="Determine Instance Count"/>

    <!-- 多实例任务：并行执行，无同步 -->
    <bpmn:task id="MultiInstanceTask" name="Process Item">
      <bpmn:incoming>Flow_Determine</bpmn:incoming>
      <bpmn:multiInstanceLoopCharacteristics
          isSequential="false"
          behavior="none">  <!-- none = 不等待完成 -->
        <bpmn:loopCardinality>${items.size()}</bpmn:loopCardinality>
        <bpmn:loopDataInputRef>items</bpmn:loopDataInputRef>
        <bpmn:inputDataItem name="item"/>
      </bpmn:multiInstanceLoopCharacteristics>
    </bpmn:task>

    <!-- 注意：无汇聚网关，实例各自独立完成 -->

    <!-- 后续活动（与多实例并行执行） -->
    <bpmn:task id="NextTask" name="Next Task">
      <!-- 可能在前面的实例完成前就开始 -->
    </bpmn:task>

  </bpmn:process>
</bpmn:definitions>
```

### 多实例活动

**图形表示（并行多实例）：**

```
                    ┌─────────┐
                    │  Start  │
                    └────┬────┘
                         │
                         ▼
              ┌─────────────────────┐
              │  Determine Items    │
              │  (Runtime Count)    │
              └──────────┬──────────┘
                         │
                         │ items = [A, B, C, D]
                         ▼
              ┌─────────────────────┐
              │  [===]              │  ◄── 并行多实例标记
              │  Process Item       │      (三条竖线)
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
       ▼                 ▼                 ▼
  [Complete]        [Complete]        [Complete]
  (Independent)    (Independent)    (Independent)
       │                 │                 │
       └─────────────────┼─────────────────┘
                         │
              [No Synchronization]
                         │
                         ▼
                    ┌─────────┐
                    │  Next   │  (May start before all complete)
                    └─────────┘
```

### 循环活动

**标准循环（非多实例）：**

```
┌───────────────────────────────────┐
│  ⟳  Standard Loop                │  ◄── 循环标记
│      Process Item                 │      (箭头)
│  ━━━━━━━━━━━━━━━━━━━━━━━━         │
└───────────────────────────────────┘
```

**多实例 vs 循环：**

| 特性 | 标准循环 | 多实例 |
|------|----------|--------|
| 执行方式 | 顺序 | 并行 |
| 实例关系 | 共享状态 | 独立状态 |
| 同步 | 隐式 | 可选 |
| 性能 | 低 | 高 |

## 形式化语义

### 状态机形式化

$$
\begin{aligned}
& \text{States} = \{ \\
& \quad \text{READY}: \text{准备创建实例}, \\
& \quad \text{CREATING}(k, n): \text{已创建 } k \text{ 个，共 } n \text{ 个}, \\
& \quad \text{EXECUTING}: \text{实例执行中}, \\
& \quad \text{INDEPENDENT}_i: \text{实例 } i \text{ 独立完成}, \\
& \quad \text{COMPLETED}: \text{所有实例创建完成} \\
& \} \\
& \text{Transitions} = \{ \\
& \quad \text{READY} \xrightarrow{\text{determine}(n)} \text{CREATING}(0, n), \\
& \quad \text{CREATING}(k, n) \xrightarrow{\text{spawn}_i} \text{CREATING}(k+1, n) \text{ if } k < n, \\
& \quad \text{CREATING}(n, n) \xrightarrow{\tau} \text{EXECUTING}, \\
& \quad \text{EXECUTING} \xrightarrow{\text{complete}_i} \text{INDEPENDENT}_i, \\
& \quad \text{INDEPENDENT}_i \xrightarrow{\tau} \text{COMPLETED} \\
& \}
\end{aligned}
$$

### 进程代数

**CSP 形式化：**

```csp
-- 多实例无同步的 CSP 形式化

-- 单个实例
Instance(i, item) = process(item) -> complete.i -> SKIP

-- 多实例创建
MICreator(items) =
    if null(items) then SKIP
    else spawn(Instance(head(items))) ; MICreator(tail(items))

-- 无同步并行执行
MIWithoutSync(items) = ||| i:items @ Instance(i)

-- 其中 ||| 是交错并行（interleaving）
-- 无同步约束，各实例独立执行
```

**π-演算表示：**

```
MIWithoutSync(items) ::= spawn_instances(items)

spawn_instances([]) ::= 0
spawn_instances(item::rest) ::=
    νc.(Instance(c, item) | spawn_instances(rest))

Instance(c, item) ::= process(item).c<result>.0
```

## 正确性证明

### 活性证明

**定理（实例创建活性）**: 对于 $n$ 个需要创建的实例，系统将创建所有 $n$ 个实例。

**证明:**

通过归纳法：

**基础**: $n = 0$ 时，立即完成。

**归纳**: 假设对于 $k$ 个实例成立，证明对 $k+1$ 个实例成立。

1. 系统创建第 1 个实例
2. 递归创建剩余 $k$ 个实例（归纳假设）
3. 因此创建所有 $k+1$ 个实例

**定理（执行活性）**: 每个创建的实例都会完成执行。

**证明:**

1. 实例 $A_i$ 由 `spawn` 操作创建
2. 假设实例内部逻辑有活性（每个任务最终完成）
3. 因此 $A_i$ 最终完成
4. 由于实例间无依赖，一个实例的完成不影响其他实例

因此所有实例都会完成。∎

### 资源安全性

**定理（资源上限）**: 同时活跃的实例数不会超过系统资源限制。

**证明:**

设资源限制为 $R_{max}$，每个实例需要资源 $r$。

1. 系统维护信号量或计数器跟踪活跃实例
2. 当实例数达到 $\lfloor R_{max}/r \rfloor$ 时，新实例等待
3. 实例完成时释放资源，允许新实例创建
4. 因此活跃实例数始终受限于资源

因此不会发生资源耗尽。∎

## Rust 实现示例

### 基础实现

```rust
use std::future::Future;
use std::sync::atomic::{AtomicUsize, Ordering};
use tokio::task::JoinHandle;

use std::sync::Arc;
use std::pin::Pin;

/// 多实例无同步执行器
pub struct MultiInstanceNoSync<T, R> {
    factory: Arc<dyn Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync>,
    spawned_count: AtomicUsize,
    completed_count: AtomicUsize,
}

impl<T: Send + 'static, R: Send + 'static> MultiInstanceNoSync<T, R> {
    pub fn new<F, Fut>(factory: F) -> Self
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        Self {
            factory: Arc::new(move |t| Box::pin(factory(t))),
            spawned_count: AtomicUsize::new(0),
            completed_count: AtomicUsize::new(0),
        }
    }

    /// 创建指定数量的实例
    pub async fn spawn_instances(&self, items: Vec<T>) -> Vec<JoinHandle<()>> {
        let mut handles = Vec::with_capacity(items.len());

        for item in items {
            let factory = Arc::clone(&self.factory);
            let completed = &self.completed_count;

            let handle = tokio::spawn(async move {
                let future = factory(item);
                let _result = future.await;
                completed.fetch_add(1, Ordering::SeqCst);
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
            let completed = &self.completed_count;

            tokio::spawn(async move {
                let future = factory(item);
                let _ = future.await; // 忽略结果
                completed.fetch_add(1, Ordering::SeqCst);
            });

            self.spawned_count.fetch_add(1, Ordering::SeqCst);
        }
    }

    pub fn get_spawned_count(&self) -> usize {
        self.spawned_count.load(Ordering::SeqCst)
    }

    pub fn get_completed_count(&self) -> usize {
        self.completed_count.load(Ordering::SeqCst)
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
        let _ = handle.await;
    }

    println!("已完成 {} 个实例", sender.get_completed_count());
}
```

### 动态实例池

```rust
use tokio::sync::{mpsc, Semaphore};

/// 带资源限制的动态实例池
pub struct BoundedMIPool<T, R> {
    factory: Arc<dyn Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync>,
    semaphore: Arc<Semaphore>,
    result_tx: mpsc::Sender<R>,
}

impl<T: Send + 'static, R: Send + 'static> BoundedMIPool<T, R> {
    pub fn new<F, Fut>(
        max_concurrent: usize,
        factory: F,
    ) -> (Self, mpsc::Receiver<R>)
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        let (tx, rx) = mpsc::channel(100);
        (
            Self {
                factory: Arc::new(move |t| Box::pin(factory(t))),
                semaphore: Arc::new(Semaphore::new(max_concurrent)),
                result_tx: tx,
            },
            rx,
        )
    }

    /// 提交任务到池
    pub async fn submit(&self, item: T) -> Result<(), MIError> {
        let permit = self.semaphore.clone().acquire_owned().await
            .map_err(|_| MIError::PoolClosed)?;

        let factory = Arc::clone(&self.factory);
        let tx = self.result_tx.clone();

        tokio::spawn(async move {
            let _permit = permit; // 持有许可证直到完成
            let future = factory(item);
            let result = future.await;
            let _ = tx.send(result).await;
        });

        Ok(())
    }

    /// 批量提交
    pub async fn submit_batch(&self, items: Vec<T>) -> Vec<Result<(), MIError>> {
        let mut results = Vec::with_capacity(items.len());
        for item in items {
            results.push(self.submit(item).await);
        }
        results
    }
}

#[derive(Debug)]
pub enum MIError {
    PoolClosed,
    SubmitFailed,
}
```

### 流式处理实现

```rust
use tokio::sync::mpsc;
use tokio_stream::Stream;

/// 流式多实例处理
pub struct StreamedMIProcessor<T, R> {
    factory: Arc<dyn Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync>,
    input_tx: mpsc::Sender<T>,
}

impl<T: Send + 'static, R: Send + 'static> StreamedMIProcessor<T, R> {
    pub fn new<F, Fut>(
        max_concurrent: usize,
        factory: F,
    ) -> (Self, mpsc::Receiver<R>)
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        let (input_tx, mut input_rx) = mpsc::channel::<T>(1000);
        let (output_tx, output_rx) = mpsc::channel::<R>(1000);

        let factory = Arc::new(move |t: T| Box::pin(factory(t)) as Pin<Box<dyn Future<Output = R> + Send>>);

        // 后台处理器
        tokio::spawn(async move {
            let semaphore = Arc::new(Semaphore::new(max_concurrent));

            while let Some(item) = input_rx.recv().await {
                let factory = Arc::clone(&factory);
                let output_tx = output_tx.clone();
                let semaphore = Arc::clone(&semaphore);

                tokio::spawn(async move {
                    let _permit = semaphore.acquire().await;
                    let result = factory(item).await;
                    let _ = output_tx.send(result).await;
                });
            }
        });

        (
            Self { factory, input_tx },
            output_rx,
        )
    }

    pub async fn process(&self, item: T) -> Result<(), mpsc::error::SendError<T>> {
        self.input_tx.send(item).await
    }

    /// 从流处理
    pub async fn process_stream<S>(&self, stream: S) -> usize
    where
        S: Stream<Item = T>,
    {
        use tokio_stream::StreamExt;

        let mut count = 0;
        tokio::pin!(stream);

        while let Some(item) = stream.next().await {
            if self.process(item).await.is_ok() {
                count += 1;
            }
        }

        count
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

/// 混合实现：异步 I/O + 并行计算
pub async fn hybrid_processing<T, R>(
    items: Vec<T>,
    io_bound: impl Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync + Clone + 'static,
    cpu_bound: impl Fn(R) -> R + Send + Sync + Clone + 'static,
) -> Vec<R>
where
    T: Send + 'static,
    R: Send + 'static,
{
    // 第一步：并行 I/O
    let io_results: Vec<R> = futures::future::join_all(
        items.into_iter().map(|item| {
            let f = io_bound.clone();
            async move { f(item).await }
        })
    ).await;

    // 第二步：CPU 并行计算
    io_results
        .into_par_iter()
        .map(|r| cpu_bound(r))
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
5. **日志处理**：独立处理每条日志
6. **事件处理**：独立处理每个事件

### 注意事项

- 注意资源限制，避免创建过多实例
- 考虑使用信号量控制并发度
- 独立实例间的数据竞争需要防范
- 监控实例完成情况（即使不等待）
- 考虑使用背压机制防止过载
- 实现优雅关闭处理

## 学术参考

1. **Russell, N., ter Hofstede, A.H.M., van der Aalst, W.M.P., & Mulyar, N.** (2006). "Workflow Control-Flow Patterns: A Revised View." *BPM Center Report* BPM-06-22.

2. **van der Aalst, W.M.P., & ter Hofstede, A.H.M.** (2005). "YAWL: Yet Another Workflow Language." *Information Systems*, 30(4), 245-275.

3. **Kumar, A., & Zhao, J.L.** (2002). "Dynamic Routing and Operational Controls in Workflow Management Systems." *Management Science*, 50(3), 405-417.

4. **Reichert, M., & Dadam, P.** (1998). "ADEPTflex - Supporting Dynamic Changes of Workflows Without Losing Control." *Journal of Intelligent Information Systems*, 10(2), 93-129.

5. **Sadiq, S., & Orlowska, M.** (2000). "Analyzing Process Models Using Graph Reduction Techniques." *Information Systems*, 25(2), 117-134.
