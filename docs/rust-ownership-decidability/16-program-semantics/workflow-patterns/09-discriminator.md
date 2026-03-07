# 09 鉴别器模式 (Discriminator)

## 📋 目录

- [09 鉴别器模式 (Discriminator)](#09-鉴别器模式-discriminator)
  - [📋 目录](#-目录)
  - [模式定义与语义](#模式定义与语义)
    - [核心语义](#核心语义)
    - [First-Wins 语义](#first-wins-语义)
  - [BPMN 2.0 表示](#bpmn-20-表示)
    - [Cancel Event 实现](#cancel-event-实现)
  - [进程代数形式化](#进程代数形式化)
  - [超时语义](#超时语义)
  - [状态机语义](#状态机语义)
  - [正确性证明](#正确性证明)
    - [安全性证明](#安全性证明)
    - [活性证明](#活性证明)
  - [Rust 实现示例](#rust-实现示例)
    - [基础鉴别器](#基础鉴别器)
    - [带超时处理的鉴别器](#带超时处理的鉴别器)
    - [Race Condition 处理](#race-condition-处理)
  - [与其他模式的关系](#与其他模式的关系)
  - [应用场景](#应用场景)
    - [实现要点](#实现要点)
  - [学术参考](#学术参考)

## 模式定义与语义

鉴别器模式等待多个并行分支中的第一个完成，然后取消或忽略其他分支的执行结果，继续后续流程。

### 核心语义

$$
\text{Discriminator}(P_1, P_2, \ldots, P_n) = \text{first}(P_1, P_2, \ldots, P_n) \gg \text{cancel}(\text{others})
$$

### First-Wins 语义

First-Wins（先到先胜）是鉴别器的核心语义：

$$
\text{FirstWins}(n) = \Box_{i=1}^{n} (\text{complete}_i \to \text{winner}_i \to \text{cancel}_{\neq i} \to \text{continue})
$$

其中 $\Box$ 是外部选择算子，$\text{cancel}_{\neq i}$ 表示取消所有非获胜分支。

## BPMN 2.0 表示

在 BPMN 2.0 中，鉴别器可以使用**复杂网关（Complex Gateway）**或**基于事件的网关（Event-Based Gateway）**配合**取消事件（Cancel Event）**实现：

```xml
<?xml version="1.0" encoding="UTF-8"?>
<bpmn:definitions xmlns:bpmn="http://www.omg.org/spec/BPMN/20100524/MODEL"
                  id="Definitions_Discriminator">
  <bpmn:process id="DiscriminatorProcess" isExecutable="true">

    <!-- 并行拆分 -->
    <bpmn:parallelGateway id="Fork">
      <bpmn:outgoing>Flow_A</bpmn:outgoing>
      <bpmn:outgoing>Flow_B</bpmn:outgoing>
      <bpmn:outgoing>Flow_C</bpmn:outgoing>
    </bpmn:parallelGateway>

    <!-- 分支任务 -->
    <bpmn:task id="Task_A" name="Query Primary DB">
      <bpmn:incoming>Flow_A</bpmn:incoming>
      <bpmn:outgoing>Flow_A_Done</bpmn:outgoing>
    </bpmn:task>

    <bpmn:task id="Task_B" name="Query Replica 1">
      <bpmn:incoming>Flow_B</bpmn:incoming>
      <bpmn:outgoing>Flow_B_Done</bpmn:outgoing>
    </bpmn:task>

    <bpmn:task id="Task_C" name="Query Replica 2">
      <bpmn:incoming>Flow_C</bpmn:incoming>
      <bpmn:outgoing>Flow_C_Done</bpmn:outgoing>
    </bpmn:task>

    <!-- 基于事件的网关（鉴别器） -->
    <bpmn:eventBasedGateway id="DiscriminatorGateway" instantiate="false">
      <bpmn:incoming>Flow_A_Done</bpmn:incoming>
      <bpmn:incoming>Flow_B_Done</bpmn:incoming>
      <bpmn:incoming>Flow_C_Done</bpmn:incoming>
      <bpmn:outgoing>Flow_Winner</bpmn:outgoing>
    </bpmn:eventBasedGateway>

    <!-- 中间捕获事件 - 用于取消其他分支 -->
    <bpmn:intermediateCatchEvent id="CancelOthers" name="Cancel Others">
      <bpmn:cancelEventDefinition/>
    </bpmn:intermediateCatchEvent>

    <!-- 后续活动 -->
    <bpmn:task id="Next_Task" name="Process Result">
      <bpmn:incoming>Flow_Winner</bpmn:incoming>
    </bpmn:task>

  </bpmn:process>
</bpmn:definitions>
```

**BPMN 图形表示：**

```
                    ┌─────────┐
                    │  Start  │
                    └────┬────┘
                         │
                         ▼
              ┌─────────────────────┐
              │   Parallel Split    │
              └──────────┬──────────┘
                         │
         ┌───────────────┼───────────────┐
         │               │               │
         ▼               ▼               ▼
    ┌─────────┐    ┌─────────┐    ┌─────────┐
    │ Query A │    │ Query B │    │ Query C │
    └────┬────┘    └────┬────┘    └────┬────┘
         │               │               │
         └───────────────┼───────────────┘
                         │
                         ▼
              ┌─────────────────────┐
              │   Discriminator     │ ◄── 第一个完成触发
              │   (Event Gateway)   │     发送取消事件
              └──────────┬──────────┘
                         │
                         ▼
                    ┌─────────┐
                    │Process  │
                    └─────────┘
```

### Cancel Event 实现

```
                    ┌─────────────┐
                    │  Task A     │
                    └──────┬──────┘
                           │
         ┌─────────────────┼─────────────────┐
         │                 │                 │
         ▼                 ▼                 ▼
    ┌─────────┐      ┌─────────┐      ┌─────────┐
    │CompleteA│      │CompleteB│      │CompleteC│
    └────┬────┘      └────┬────┘      └────┬────┘
         │                 │                 │
         └─────────────────┼─────────────────┘
                           │
                           ▼
              ┌─────────────────────┐
              │  Discriminator      │
              │  (First Wins)       │
              └──────────┬──────────┘
                         │
           ┌─────────────┼─────────────┐
           ▼             ▼             ▼
    ┌─────────────┐┌─────────────┐┌─────────────┐
    │   Cancel B  ││   Cancel C  ││  Continue   │
    │  (if A wins)││  (if A wins)││   Process   │
    └─────────────┘└─────────────┘└─────────────┘
```

## 进程代数形式化

**CSP 形式化：**

```csp
-- 鉴别器的 CSP 形式化

-- 基本分支
Branch(i) = start.i -> work.i -> complete.i -> SKIP

-- 外部选择（鉴别器核心）
Discriminator =
    (complete?i -> winner!i -> cancel.others -> continue -> SKIP)
    [] timeout -> continue -> SKIP

-- 其中 cancel.others 取消所有 j != i 的分支
cancel.others = ||| j:{1..n} \ {i} @ cancel.j -> SKIP

-- 带超时的鉴别器
TimedDiscriminator(t) =
    Discriminator [|{complete}|] Timeout(t)

Timeout(t) = WAIT(t) ; timeout -> SKIP
```

**CCS 表示：**

```ccs
-- 分支代理
Bi ::= ai.Bi' | τ.Bi' | canceli.0
Bi' ::= bi.ci.0

-- 鉴别器组合
Discriminator ::=
    (B1 | B2 | ... | Bn | Controller) \ {c1, c2, ..., cn, cancel}

-- 控制器
Controller ::= c1.winner1.cancel2...cancelN.0
            + c2.cancel1.winner2.cancel3...cancelN.0
            + ...
            + cN.cancel1...cancel(N-1).winnerN.0
```

**带优先级的 π-演算：**

```
Discriminator ::= νc1...cn.(P1(c1) | ... | Pn(cn) | FirstWinner(c1,...,cn))

Pi(ci) ::= work_i.ci<result_i>.Pi_cleanup
Pi_cleanup ::= cancel?x.0 + τ.0

FirstWinner(c1,...,cn) ::=
    c1?x.winner!1.cancel!<others>.0
    + c2?x.winner!2.cancel!<others>.0
    + ...
    + timeout?x.0
```

## 超时语义

鉴别器的超时处理：

$$
\text{Discriminator}_{\text{timeout}}(t) = \text{Discriminator} \triangleright_t \text{Timeout}
$$

其中 $\triangleright_t$ 是超时操作符：

$$
P \triangleright_t Q = \begin{cases}
P & \text{if } P \text{ completes within } t \\
Q & \text{if } t \text{ elapsed}
\end{cases}
$$

## 状态机语义

**完整状态机：**

$$
\begin{aligned}
& \text{States} = \{ \\
& \quad \text{WAITING}: \text{等待分支完成}, \\
& \quad \text{RACING}: \text{竞速中}, \\
& \quad \text{WINNER}(i): \text{分支 } i \text{ 获胜}, \\
& \quad \text{CANCELLING}: \text{取消其他分支}, \\
& \quad \text{COMPLETED}: \text{完成}, \\
& \quad \text{TIMEOUT}: \text{超时状态} \\
& \} \\
& \text{Transitions} = \{ \\
& \quad \text{WAITING} \xrightarrow{\text{start}_i} \text{RACING}, \\
& \quad \text{RACING} \xrightarrow{\text{complete}_i} \text{WINNER}(i), \\
& \quad \text{WINNER}(i) \xrightarrow{\text{cancel}_{j \neq i}} \text{CANCELLING}, \\
& \quad \text{CANCELLING} \xrightarrow{\tau} \text{COMPLETED}, \\
& \quad \text{RACING} \xrightarrow{\text{timeout}} \text{TIMEOUT}, \\
& \quad \text{TIMEOUT} \xrightarrow{\text{default}} \text{COMPLETED} \\
& \}
\end{aligned}
$$

**Petri 网表示：**

```
                    start
                      │
                      ▼
    ┌─────────────────────────────────┐
    │         WAITING_PLACE           │
    └───────────────┬─────────────────┘
                    │
        ┌───────────┼───────────┐
        ▼           ▼           ▼
   ┌────────┐  ┌────────┐  ┌────────┐
   │ Task_1 │  │ Task_2 │  │ Task_3 │
   └───┬────┘  └───┬────┘  └───┬────┘
       │           │           │
       └───────────┼───────────┘
                   │
                   ▼
          ┌────────────────┐
          │ Discriminator  │ ◄── 第一个令牌通过
          │   Transition   │     其他令牌被阻塞
          └───────┬────────┘
                  │
          ┌───────┴───────┐
          ▼               ▼
    ┌───────────┐   ┌───────────┐
    │  WINNER   │   │  CANCEL   │
    └─────┬─────┘   └─────┬─────┘
          │               │
          └───────┬───────┘
                  │
                  ▼
           ┌────────────┐
           │  CONTINUE  │
           └────────────┘
```

## 正确性证明

### 安全性证明

**定理 1（唯一获胜者）**: 鉴别器保证只有一个分支成为获胜者。

**证明:**

设活跃分支集合为 $B = \{b_1, \ldots, b_n\}$

1. 初始状态: 所有分支在等待完成
2. 设 $b_i$ 是第一个完成的分支，时间戳为 $t_i$
3. 鉴别器在检测到 $b_i$ 完成时:
   - 原子性地将 $b_i$ 标记为获胜者
   - 向所有 $b_j (j \neq i)$ 发送取消信号
4. 由于原子操作，只有一个分支能被标记为获胜者
5. 后续完成的分支由于已收到取消信号，结果被忽略

因此只有一个获胜者。∎

**定理 2（正确取消）**: 获胜分支确定后，所有其他分支都会被取消。

**证明:**

1. 当分支 $b_i$ 获胜，执行 $\text{cancel}_{\neq i}$ 操作
2. 对于每个 $j \neq i$，发送取消信号到 $b_j$
3. 每个 $b_j$ 在收到取消信号后:
   - 如果仍在执行，则中止执行
   - 如果已完成，则结果被忽略
4. 取消操作覆盖所有 $j \in [1,n], j \neq i$

因此所有其他分支都被正确处理。∎

### 活性证明

**定理 3（最终完成）**: 如果至少有一个分支完成，鉴别器最终会继续执行。

**证明:**

情况 1: 正常完成

1. 假设分支 $b_i$ 在时间 $t$ 完成
2. 鉴别器检测到完成事件（响应时间 $\delta$）
3. 在 $t + \delta$ 时，$b_i$ 被确定为获胜者
4. 触发后续流程

情况 2: 超时

1. 如果在超时时间 $T$ 内没有分支完成
2. 触发超时处理（可能选择默认分支或报错）
3. 系统继续执行

因此系统最终会继续执行。∎

## Rust 实现示例

### 基础鉴别器

```rust
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use tokio::sync::oneshot;
use tokio::task::AbortHandle;

/// 鉴别器模式实现
pub struct Discriminator<T> {
    completed: AtomicBool,
    sender: Option<oneshot::Sender<(usize, T)>>,
    abort_handles: Vec<AbortHandle>,
}

impl<T: Send + 'static> Discriminator<T> {
    pub fn new() -> (Self, oneshot::Receiver<(usize, T)>) {
        let (tx, rx) = oneshot::channel();
        let discriminator = Self {
            completed: AtomicBool::new(false),
            sender: Some(tx),
            abort_handles: Vec::new(),
        };
        (discriminator, rx)
    }

    /// 注册一个分支任务
    pub fn spawn_branch<F>(&mut self, index: usize, future: F) -> AbortHandle
    where
        F: Future<Output = T> + Send + 'static,
    {
        let sender = self.sender.take();
        let completed_flag = Arc::new(AtomicBool::new(false));

        let handle = tokio::spawn(async move {
            let result = future.await;

            // 尝试成为第一个完成的
            if let Some(tx) = sender {
                let _ = tx.send((index, result));
            }

            result
        });

        let abort_handle = handle.abort_handle();
        self.abort_handles.push(abort_handle.clone());
        abort_handle
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

/// 使用 select! 的更简洁实现
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

    // 使用 select_all 等待第一个完成
    let result = match joined.len() {
        0 => panic!("No futures provided"),
        1 => joined.remove(0).await,
        _ => {
            let (result, _index, remaining) = futures::future::select_all(joined).await;
            // 取消其他任务
            for task in remaining {
                // 注意：select_all 返回的任务需要手动处理
            }
            result
        }
    };

    (result, abort_handles)
}
```

### 带超时处理的鉴别器

```rust
use tokio::time::{timeout, Duration};

/// 带超时的鉴别器
pub struct TimedDiscriminator<T> {
    duration: Duration,
    _phantom: std::marker::PhantomData<T>,
}

impl<T> TimedDiscriminator<T> {
    pub fn new(duration: Duration) -> Self {
        Self {
            duration,
            _phantom: std::marker::PhantomData,
        }
    }

    pub async fn race(
        &self,
        tasks: Vec<impl Future<Output = T> + Send>,
    ) -> Result<T, DiscriminatorError> {
        let race_future = async {
            let mut futures: Vec<Pin<Box<dyn Future<Output = T> + Send>>> = tasks
                .into_iter()
                .map(|f| Box::pin(f) as Pin<Box<dyn Future<Output = T> + Send>>)
                .collect();

            if futures.is_empty() {
                return Err(DiscriminatorError::NoTasks);
            }

            let (result, _, _) = futures::future::select_all(futures).await;
            Ok(result)
        };

        match timeout(self.duration, race_future).await {
            Ok(Ok(result)) => Ok(result),
            Ok(Err(e)) => Err(e),
            Err(_) => Err(DiscriminatorError::Timeout),
        }
    }
}

#[derive(Debug)]
pub enum DiscriminatorError {
    Timeout,
    NoTasks,
    Cancelled,
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

    let discriminator = TimedDiscriminator::<QueryResult>::new(Duration::from_secs(5));

    match discriminator.race(queries).await {
        Ok(result) => {
            println!("最快响应来自: {}", result.source);
            println!("数据: {}", result.data);
        }
        Err(DiscriminatorError::Timeout) => {
            println!("所有查询超时");
        }
        Err(e) => {
            println!("错误: {:?}", e);
        }
    }
}

async fn query_database(source: &str, latency_ms: u64) -> QueryResult {
    tokio::time::sleep(tokio::time::Duration::from_millis(latency_ms)).await;

    QueryResult {
        source: source.to_string(),
        data: format!("data from {}", source),
        latency_ms,
    }
}
```

### Race Condition 处理

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

/// 线程安全的鉴别器（处理竞态条件）
pub struct ThreadSafeDiscriminator<T> {
    winner: Arc<Mutex<Option<(usize, T)>>>,
    complete_tx: tokio::sync::mpsc::Sender<(usize, T)>,
    complete_rx: Arc<Mutex<tokio::sync::mpsc::Receiver<(usize, T)>>>,
}

impl<T: Send + 'static> ThreadSafeDiscriminator<T> {
    pub fn new() -> Self {
        let (tx, rx) = tokio::sync::mpsc::channel(1);
        Self {
            winner: Arc::new(Mutex::new(None)),
            complete_tx: tx,
            complete_rx: Arc::new(Mutex::new(rx)),
        }
    }

    /// 创建分支完成处理器
    pub fn create_completer(&self, index: usize) -> BranchCompleter<T> {
        BranchCompleter {
            index,
            winner: Arc::clone(&self.winner),
            tx: self.complete_tx.clone(),
        }
    }

    /// 等待获胜者
    pub async fn wait_winner(&self) -> Option<(usize, T)> {
        let mut rx = self.complete_rx.lock().await;
        rx.recv().await
    }
}

pub struct BranchCompleter<T> {
    index: usize,
    winner: Arc<Mutex<Option<(usize, T)>>>,
    tx: tokio::sync::mpsc::Sender<(usize, T)>,
}

impl<T: Send> BranchCompleter<T> {
    pub async fn complete(self, result: T) -> bool {
        let mut winner = self.winner.lock().await;

        // 检查是否已有获胜者
        if winner.is_some() {
            return false; // 已经有获胜者了
        }

        // 成为获胜者
        *winner = Some((self.index, result));
        let _ = self.tx.send((self.index, result)).await;
        true
    }
}

/// 带取消通知的鉴别器
pub struct CancellableDiscriminator<T> {
    cancel_tx: broadcast::Sender<()>,
    _phantom: std::marker::PhantomData<T>,
}

use tokio::sync::broadcast;

impl<T> CancellableDiscriminator<T> {
    pub fn new() -> (Self, broadcast::Receiver<()>) {
        let (cancel_tx, cancel_rx) = broadcast::channel(1);
        (
            Self {
                cancel_tx,
                _phantom: std::marker::PhantomData,
            },
            cancel_rx,
        )
    }

    pub async fn race(
        &self,
        tasks: Vec<impl Future<Output = T> + Send>,
    ) -> (T, usize) {
        let (tx, mut rx) = tokio::sync::mpsc::channel(1);
        let cancel_tx = self.cancel_tx.clone();

        for (index, task) in tasks.into_iter().enumerate() {
            let tx = tx.clone();
            tokio::spawn(async move {
                let result = task.await;
                // 尝试发送结果（只有第一个成功）
                let _ = tx.try_send((index, result));
            });
        }

        // 等待第一个结果
        let (winner_index, result) = rx.recv().await.expect("至少有一个任务");

        // 通知其他任务取消
        let _ = cancel_tx.send(());

        (result, winner_index)
    }
}

/// 取消感知任务包装器
pub async fn cancellable_task<F, T>(
    task: F,
    mut cancel_rx: broadcast::Receiver<()>,
) -> Option<T>
where
    F: Future<Output = T>,
{
    tokio::select! {
        result = task => Some(result),
        _ = cancel_rx.recv() => {
            println!("任务被取消");
            None
        }
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

**模式层次：**

```
        Parallel Split
              │
              ▼
    ┌─────────┬─────────┐
    ▼         ▼         ▼
 Branch1   Branch2   Branch3
    │         │         │
    └─────────┼─────────┘
              │
    ┌─────────┴─────────┐
    ▼         ▼         ▼
 Discriminator  SyncMerge  MultiMerge
 (1st wins)   (All wait) (All trigger)
```

## 应用场景

1. **竞速查询**：从多个数据源获取同一数据，采用最快响应
2. **故障转移**：多个服务实例，第一个可用即使用
3. **超时控制**：任务与超时竞速，先完成者决定结果
4. **负载均衡**：选择最快响应的服务器
5. **缓存穿透防护**：多个请求竞速查询数据库
6. **分布式锁竞争**：第一个获取锁的获胜

### 实现要点

- 正确取消正在执行的其他任务
- 处理取消时的资源清理
- 避免竞态条件（使用原子操作）
- 考虑任务清理的延迟
- 实现超时机制作为后备
- 监控获胜者分布以优化性能

## 学术参考

1. **van der Aalst, W.M.P., ter Hofstede, A.H.M., Kiepuszewski, B., & Barros, A.P.** (2003). "Workflow Patterns." *Distributed and Parallel Databases*, 14(1), 5-51.

2. **Hoare, C.A.R.** (1978). "Communicating Sequential Processes." *Communications of the ACM*, 21(8), 666-677.

3. **Milner, R.** (1989). *Communication and Concurrency*. Prentice Hall.

4. **Bultan, T., & Fu, X.** (2006). "Specification of Real-Time Properties with Temporal Logic." *IEEE Computer Society*.

5. **Russell, N., van der Aalst, W.M.P., & ter Hofstede, A.H.M.** (2006). "Design of Workflow Patterns." *Handbook of Research on Business Process Modeling*, 1, 1-24.

6. **Recker, J.** (2010). "Opportunities and Constraints: The Current Struggle with BPMN." *Business Process Management Journal*, 16(1), 181-201.
