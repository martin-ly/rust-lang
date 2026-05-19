# 07 同步合并模式 (Synchronizing Merge)

## 📋 目录

- [07 同步合并模式 (Synchronizing Merge)](#07-同步合并模式-synchronizing-merge)
  - [📋 目录](#-目录)
  - [模式定义与语义](#模式定义与语义)
    - [核心语义](#核心语义)
    - [形式化表示](#形式化表示)
  - [BPMN 2.0 表示](#bpmn-20-表示)
  - [进程代数形式化 (CSP/CCS)](#进程代数形式化-cspccs)
  - [状态机语义](#状态机语义)
  - [正确性证明](#正确性证明)
    - [安全性证明](#安全性证明)
    - [活性证明](#活性证明)
  - [Rust 实现示例](#rust-实现示例)
    - [基于 Barrier 的实现](#基于-barrier-的实现)
    - [基于 Channel 的合并](#基于-channel-的合并)
    - [动态分支同步](#动态分支同步)
  - [与其他模式的关系](#与其他模式的关系)
  - [应用场景](#应用场景)
    - [实现要点](#实现要点)
  - [学术参考](#学术参考)

## 模式定义与语义

同步合并模式等待所有活跃分支完成后才继续执行。
它与简单合并的区别在于能够正确处理多路选择产生的动态分支数。

### 核心语义

$$
\text{SyncMerge}(P_1, P_2, \ldots, P_n) =
\begin{cases}
\text{wait} & \text{if } \exists i: P_i \text{ active} \\
\text{proceed} & \text{if all active } P_i \text{ completed}
\end{cases}
$$

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State} = \{ \text{Waiting}, \text{Counting}, \text{Ready}, \text{Completed} \} \\
& \text{Transition} = \{ \\
& \quad (\text{Waiting}, \text{activate}_k, \text{Counting}) \text{ 激活 } k \text{ 个分支}, \\
& \quad (\text{Counting}, \text{complete}_i, \text{Counting}) \text{ 计数减一}, \\
& \quad (\text{Counting}, \text{count=0}, \text{Ready}), \\
& \quad (\text{Ready}, \text{proceed}, \text{Completed}) \\
& \}
\end{aligned}
$$

**流程代数：**

$$
\text{SyncMerge} = \Pi_{i=1}^{n} P_i \triangleright Q
$$

其中 $\triangleright$ 表示同步汇合操作。

## BPMN 2.0 表示

在 BPMN 2.0 中，同步合并使用**包容性网关（Inclusive Gateway, OR-Join）**表示：

```xml
<?xml version="1.0" encoding="UTF-8"?>
<bpmn:definitions xmlns:bpmn="http://www.omg.org/spec/BPMN/20100524/MODEL"
                  xmlns:bpmndi="http://www.omg.org/spec/BPMN/20100524/DI"
                  id="Definitions_1"
                  targetNamespace="http://bpmn.io/schema/bpmn">
  <bpmn:process id="SyncMergeProcess" isExecutable="true">

    <!-- 并行拆分（多路选择） -->
    <bpmn:inclusiveGateway id="InclusiveSplit" name="OR-Split">
      <bpmn:incoming>Flow_Start</bpmn:incoming>
      <bpmn:outgoing>Flow_A</bpmn:outgoing>
      <bpmn:outgoing>Flow_B</bpmn:outgoing>
      <bpmn:outgoing>Flow_C</bpmn:outgoing>
    </bpmn:inclusiveGateway>

    <!-- 分支 A -->
    <bpmn:task id="Task_A" name="Task A">
      <bpmn:incoming>Flow_A</bpmn:incoming>
      <bpmn:outgoing>Flow_A_End</bpmn:outgoing>
    </bpmn:task>

    <!-- 分支 B -->
    <bpmn:task id="Task_B" name="Task B">
      <bpmn:incoming>Flow_B</bpmn:incoming>
      <bpmn:outgoing>Flow_B_End</bpmn:outgoing>
    </bpmn:task>

    <!-- 分支 C -->
    <bpmn:task id="Task_C" name="Task C">
      <bpmn:incoming>Flow_C</bpmn:incoming>
      <bpmn:outgoing>Flow_C_End</bpmn:outgoing>
    </bpmn:task>

    <!-- 同步合并：包容性网关（OR-Join） -->
    <bpmn:inclusiveGateway id="SyncMergeGateway" name="Synchronizing Merge">
      <bpmn:incoming>Flow_A_End</bpmn:incoming>
      <bpmn:incoming>Flow_B_End</bpmn:incoming>
      <bpmn:incoming>Flow_C_End</bpmn:incoming>
      <bpmn:outgoing>Flow_Continue</bpmn:outgoing>
    </bpmn:inclusiveGateway>

    <!-- 后续活动 -->
    <bpmn:task id="Next_Task" name="Next Task">
      <bpmn:incoming>Flow_Continue</bpmn:incoming>
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
              │   Inclusive Split   │ ◄── OR-Split
              │  (多路选择网关)      │
              └──────────┬──────────┘
                         │
         ┌───────────────┼───────────────┐
         │               │               │
         ▼               ▼               ▼
    ┌─────────┐    ┌─────────┐    ┌─────────┐
    │ Task A  │    │ Task B  │    │ Task C  │
    └────┬────┘    └────┬────┘    └────┬────┘
         │               │               │
         │               │               │
         ▼               ▼               ▼
    ┌─────────┐    ┌─────────┐    ┌─────────┐
    │  End A  │    │  End B  │    │  End C  │
    └────┬────┘    └────┬────┘    └────┬────┘
         │               │               │
         └───────────────┼───────────────┘
                         │
                         ▼
              ┌─────────────────────┐
              │  SyncMergeGateway   │ ◄── OR-Join (同步合并)
              │   (包容性网关)       │
              └──────────┬──────────┘
                         │
                         ▼
                    ┌─────────┐
                    │  Next   │
                    └─────────┘
```

## 进程代数形式化 (CSP/CCS)

**CSP (Communicating Sequential Processes) 表示：**

```csp
-- 同步合并的 CSP 形式化

-- 基本进程定义
P(i) = start_i -> work_i -> complete_i -> SKIP

-- 同步合并算子
SyncMerge(n) = || i:{1..n} @ [i]P(i) ; continue -> SKIP

-- 带计数的同步
CountingMerge(n) = counting(0, n)
counting(k, n) =
    if k == n then continue -> SKIP
    else complete?i -> counting(k+1, n)

-- 外部选择变体
SyncMergeWithChoice =
    (complete_A -> SyncMergeWithChoice)
    [] (complete_B -> SyncMergeWithChoice)
    [] (complete_C -> continue -> SKIP)
```

**CCS (Calculus of Communicing Systems) 表示：**

```ccs
-- 同步合并的 CCS 形式化

-- 基本代理
Pi ::= ai.Pi' | τ.Pi'
Pi' ::= bi.0

-- 同步合并组合
SyncMerge ::= P1 | P2 | ... | Pn \ {ai}

-- 其中 ai 是内部同步动作，通过限制算子隐藏
```

**π-演算表示：**

```
-- π-演算表示动态分支数
SyncMerge(r) ::= νc.(P1(c) | P2(c) | ... | Pn(c))

Pi(c) ::= ci(x).Pi'(x)
Pi'(x) ::= c'<x>.Pi''
Pi'' ::= τ.0

-- 汇合点
Merger(k) ::= c?y.Merger'(k+1)
Merger'(k) ::= if k=n then continue else Merger(k)
```

## 状态机语义

**扩展状态机表示：**

$$
\begin{aligned}
& \text{States} = \{ \\
& \quad \text{INIT}: \text{初始状态}, \\
& \quad \text{WAITING}(S): \text{等待分支集合 } S, \\
& \quad \text{COUNTING}(k, n): \text{已完成 } k \text{ 个，共 } n \text{ 个}, \\
& \quad \text{READY}: \text{准备继续}, \\
& \quad \text{COMPLETED}: \text{已完成} \\
& \} \\
& \text{Transitions} = \{ \\
& \quad \text{INIT} \xrightarrow{\text{activate}(n)} \text{WAITING}(\{1,\ldots,n\}), \\
& \quad \text{WAITING}(S) \xrightarrow{\text{start}_i} \text{WAITING}(S), \\
& \quad \text{WAITING}(S) \xrightarrow{\text{complete}_i} \text{COUNTING}(k+1, n) \text{ if } i \in S, \\
& \quad \text{COUNTING}(k, n) \xrightarrow{\tau} \text{READY} \text{ if } k = n, \\
& \quad \text{COUNTING}(k, n) \xrightarrow{\text{complete}_j} \text{COUNTING}(k+1, n), \\
& \quad \text{READY} \xrightarrow{\text{proceed}} \text{COMPLETED} \\
& \}
\end{aligned}
$$

**Petri 网表示：**

```
         activate(n)
              │
              ▼
    ┌─────────────────┐
    │   WAITING_PLACE │──────────────────┐
    └────────┬────────┘                  │
             │                           │
    ┌────────┼────────┐                  │
    ▼        ▼        ▼                  │
┌───────┐┌───────┐┌───────┐             │
│Task_A ││Task_B ││Task_C │             │
└───┬───┘└───┬───┘└───┬───┘             │
    │        │        │                 │
    ▼        ▼        ▼                 │
┌───────┐┌───────┐┌───────┐             │
│Done_A ││Done_B ││Done_C │             │
└───┬───┘└───┬───┘└───┬───┘             │
    └────────┼────────┘                 │
             │                          │
             ▼                          │
    ┌─────────────────┐                 │
    │  COUNTER_PLACE  │◄────────────────┘
    │   (计数令牌)     │
    └────────┬────────┘
             │ k=n
             ▼
    ┌─────────────────┐
    │    SYNC_PLACE   │
    └────────┬────────┘
             │
             ▼
         CONTINUE
```

## 正确性证明

### 安全性证明

**定理 1（安全性）**: 同步合并只有在所有活跃分支都完成后才会继续执行。

**证明:**

设活跃分支集合为 $A = \{P_1, P_2, \ldots, P_n\}$，计数器为 $c$。

1. 初始化: $c = n$（待完成分支数）
2. 不变式: $c = |\{P_i \in A \mid P_i \text{ 未完成}\}|$
3. 每次 `complete_i` 事件，$c \leftarrow c - 1$
4. 继续条件: $c = 0 \Leftrightarrow \forall P_i \in A: P_i \text{ 已完成}$

因此，只有当所有分支完成时才会触发继续操作。∎

### 活性证明

**定理 2（活性）**: 如果所有活跃分支最终都完成，则同步合并最终会触发继续。

**证明:**

假设所有分支 $P_i$ 最终都会完成（活性假设）。

1. 对于每个 $P_i$，存在时间 $t_i$ 使得 $P_i$ 在 $t_i$ 前完成
2. 设 $T = \max(t_1, t_2, \ldots, t_n)$
3. 在时刻 $T$，所有分支都已完成
4. 因此 $c = 0$，触发 $\text{proceed}$ 动作
5. 系统进入 `READY` 状态

因此同步合并最终会触发继续。∎

**定理 3（无死锁）**: 同步合并不会产生死锁。

**证明:**

考虑所有可能状态：

- `WAITING`: 等待分支完成，只要分支有活性就会进展
- `COUNTING(k,n)`: $k < n$ 时等待更多完成事件
- 由于分支有活性（假设），最终会到达 `COUNTING(n,n)`
- `COUNTING(n,n)` 无条件转移到 `READY`

因此不存在永久等待的状态。∎

## Rust 实现示例

```rust
use std::sync::Arc;
use tokio::sync::{Barrier, Mutex};
use std::collections::HashMap;

/// 同步合并器
pub struct SynchronizingMerge<T> {
    active_count: Arc<Mutex<usize>>,
    results: Arc<Mutex<Vec<T>>>,
}

impl<T: Send + 'static> SynchronizingMerge<T> {
    pub fn new() -> Self {
        Self {
            active_count: Arc::new(Mutex::new(0)),
            results: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// 注册一个活跃分支
    pub async fn register_branch(&self) -> BranchHandle<T> {
        let mut count = self.active_count.lock().await;
        *count += 1;

        BranchHandle {
            results: Arc::clone(&self.results),
            active_count: Arc::clone(&self.active_count),
        }
    }

    /// 等待所有分支完成
    pub async fn wait_for_all(&self) -> Vec<T> {
        loop {
            let count = *self.active_count.lock().await;
            if count == 0 {
                return self.results.lock().await.clone();
            }
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        }
    }
}

pub struct BranchHandle<T> {
    results: Arc<Mutex<Vec<T>>>,
    active_count: Arc<Mutex<usize>>,
}

impl<T> BranchHandle<T> {
    pub async fn complete(self, result: T) {
        self.results.lock().await.push(result);
        let mut count = self.active_count.lock().await;
        *count -= 1;
    }
}
```

### 基于 Barrier 的实现

```rust
use tokio::sync::Barrier;
use std::sync::Arc;

/// 基于 Barrier 的同步合并（已知分支数）
pub struct BarrierSyncMerge<T> {
    barrier: Arc<Barrier>,
    results: Arc<Mutex<Vec<T>>>,
}

impl<T: Clone + Send + 'static> BarrierSyncMerge<T> {
    pub fn new(n: usize) -> Self {
        // +1 用于主线程等待
        Self {
            barrier: Arc::new(Barrier::new(n + 1)),
            results: Arc::new(Mutex::new(Vec::with_capacity(n))),
        }
    }

    /// 创建分支处理器
    pub fn create_branch(&self) -> BarrierBranch<T> {
        BarrierBranch {
            barrier: Arc::clone(&self.barrier),
            results: Arc::clone(&self.results),
        }
    }

    /// 等待所有分支
    pub async fn wait(self) -> Vec<T> {
        // 等待所有分支到达屏障
        let _ = self.barrier.wait().await;
        self.results.lock().await.clone()
    }
}

pub struct BarrierBranch<T> {
    barrier: Arc<Barrier>,
    results: Arc<Mutex<Vec<T>>>,
}

impl<T: Send> BarrierBranch<T> {
    pub async fn execute<F, Fut>(self, f: F) -> T
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        let result = f().await;
        self.results.lock().await.push(result);
        let _ = self.barrier.wait().await;
        result
    }
}

// 使用示例
pub async fn barrier_example() {
    let merger = BarrierSyncMerge::<i32>::new(3);

    let branch1 = merger.create_branch();
    let branch2 = merger.create_branch();
    let branch3 = merger.create_branch();

    tokio::spawn(async move {
        branch1.execute(|| async {
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            1
        }).await;
    });

    tokio::spawn(async move {
        branch2.execute(|| async {
            tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
            2
        }).await;
    });

    tokio::spawn(async move {
        branch3.execute(|| async {
            tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;
            3
        }).await;
    });

    let results = merger.wait().await;
    println!("所有分支完成: {:?}", results);
}
```

### 基于 Channel 的合并

```rust
use tokio::sync::mpsc;

/// 基于 Channel 的同步合并
pub struct ChannelSyncMerge<T> {
    tx: mpsc::Sender<T>,
    rx: Arc<Mutex<mpsc::Receiver<T>>>,
    expected_count: usize,
}

impl<T: Send + 'static> ChannelSyncMerge<T> {
    pub fn new(expected_count: usize) -> (Self, mpsc::Sender<T>) {
        let (tx, rx) = mpsc::channel(expected_count);
        (
            Self {
                tx: tx.clone(),
                rx: Arc::new(Mutex::new(rx)),
                expected_count,
            },
            tx,
        )
    }

    /// 等待所有结果
    pub async fn wait_for_all(&self) -> Vec<T> {
        let mut rx = self.rx.lock().await;
        let mut results = Vec::with_capacity(self.expected_count);

        for _ in 0..self.expected_count {
            if let Some(result) = rx.recv().await {
                results.push(result);
            }
        }

        results
    }

    /// 带超时的等待
    pub async fn wait_with_timeout(
        &self,
        timeout: std::time::Duration,
    ) -> Result<Vec<T>, tokio::time::error::Elapsed> {
        tokio::time::timeout(timeout, self.wait_for_all()).await
    }
}

/// 分支发送端
pub struct BranchSender<T> {
    tx: mpsc::Sender<T>,
}

impl<T> BranchSender<T> {
    pub async fn send(self, value: T) -> Result<(), mpsc::error::SendError<T>> {
        self.tx.send(value).await
    }
}
```

### 动态分支同步

```rust
use tokio::task::JoinHandle;
use std::sync::atomic::{AtomicUsize, Ordering};

/// 动态分支同步（运行时确定分支数）
pub struct DynamicSyncMerge<T> {
    active_count: Arc<AtomicUsize>,
    results: Arc<Mutex<Vec<T>>>,
    complete_tx: watch::Sender<bool>,
    complete_rx: watch::Receiver<bool>,
}

impl<T: Send + Clone + 'static> DynamicSyncMerge<T> {
    pub fn new() -> Self {
        let (tx, rx) = watch::channel(false);
        Self {
            active_count: Arc::new(AtomicUsize::new(0)),
            results: Arc::new(Mutex::new(Vec::new())),
            complete_tx: tx,
            complete_rx: rx,
        }
    }

    /// 注册新分支
    pub fn register(&self) -> DynamicBranchHandle<T> {
        self.active_count.fetch_add(1, Ordering::SeqCst);

        DynamicBranchHandle {
            active_count: Arc::clone(&self.active_count),
            results: Arc::clone(&self.results),
            complete_tx: self.complete_tx.clone(),
        }
    }

    /// 等待完成
    pub async fn wait(&mut self) -> Vec<T> {
        // 如果当前没有活跃分支，立即返回
        if self.active_count.load(Ordering::SeqCst) == 0 {
            return self.results.lock().await.clone();
        }

        // 等待完成信号
        while !*self.complete_rx.borrow() {
            if self.complete_rx.changed().await.is_err() {
                break;
            }
        }

        self.results.lock().await.clone()
    }
}

pub struct DynamicBranchHandle<T> {
    active_count: Arc<AtomicUsize>,
    results: Arc<Mutex<Vec<T>>>,
    complete_tx: watch::Sender<bool>,
}

impl<T: Send> DynamicBranchHandle<T> {
    pub async fn complete(self, result: T) {
        // 存储结果
        self.results.lock().await.push(result);

        // 减少计数
        let remaining = self.active_count.fetch_sub(1, Ordering::SeqCst);

        // 如果是最后一个，发送完成信号
        if remaining == 1 {
            let _ = self.complete_tx.send(true);
        }
    }
}

/// 使用示例：动态分支同步
pub async fn dynamic_sync_example() {
    let merger = Arc::new(DynamicSyncMerge::<String>::new());
    let mut handles: Vec<JoinHandle<()>> = Vec::new();

    // 模拟多路选择后的动态分支
    let active_branches = vec!["branch_a", "branch_b", "branch_c"];

    for branch_id in active_branches {
        let merger_clone = Arc::clone(&merger);
        let handle = tokio::spawn(async move {
            let branch = merger_clone.register();

            // 模拟分支工作
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

            branch.complete(format!("{} completed", branch_id)).await;
        });
        handles.push(handle);
    }

    // 等待所有分支
    for handle in handles {
        let _ = handle.await;
    }

    let results = merger.wait().await;
    println!("所有分支完成: {:?}", results);
}
```

## 与其他模式的关系

| 模式 | 特点 | 区别 |
|------|------|------|
| 简单合并 | 任意分支到达即继续 | 不等待其他分支 |
| **同步合并** | 等待所有活跃分支 | 动态确定等待数量 |
| 多路合并 | 每个分支独立继续 | 不汇合 |
| 鉴别器 | 等待第一个 | 取消其他分支 |

**关系公式：**

$$
\text{SyncMerge} = \text{MultiChoice} + \text{Barrier} + \text{AND-Join}
$$

**模式层次关系：**

```
                    WorkflowControlFlow
                           │
          ┌────────────────┼────────────────┐
          ▼                ▼                ▼
    SplitPatterns    JoinPatterns      Synchronization
          │                │                │
          ▼                ▼                ▼
    ┌──────────┐     ┌──────────┐     ┌──────────┐
    │AND-Split │     │AND-Join  │     │SyncMerge │
    │(Parallel)│     │(Sync)    │     │(Dynamic) │
    ├──────────┤     ├──────────┤     ├──────────┤
    │XOR-Split │     │XOR-Join  │     │MultiMerge│
    │(Choice)  │     │(Merge)   │     │(No Sync) │
    ├──────────┤     ├──────────┤     ├──────────┤
    │OR-Split  │     │OR-Join   │     │Discrim.  │
    │(Multi)   │     │(Sync)    │     │(1st wins)│
    └──────────┘     └──────────┘     └──────────┘
```

## 应用场景

1. **分布式计算**：等待所有 Map 任务完成后进行 Reduce
2. **数据聚合**：收集所有并行查询的结果
3. **事务处理**：等待所有参与者准备就绪
4. **工作流引擎**：同步多路选择后的所有分支
5. **微服务协调**：等待所有依赖服务响应
6. **CI/CD 流水线**：等待多个并行构建完成

### 实现要点

- 动态计数活跃分支数量
- 正确处理分支取消或失败
- 提供超时机制避免死等
- 支持部分失败处理策略
- 考虑内存使用（结果收集）
- 支持优雅降级

## 学术参考

1. **van der Aalst, W.M.P.** (1998). "The Application of Petri Nets to Workflow Management." *Journal of Circuits, Systems and Computers*, 8(1), 21-66.

2. **Russell, N., et al.** (2006). *Workflow Control-Flow Patterns: A Revised View*. BPM Center Report BPM-06-22.

3. **Hoare, C.A.R.** (1985). *Communicating Sequential Processes*. Prentice Hall.

4. **Milner, R.** (1999). *Communicating and Mobile Systems: The π-Calculus*. Cambridge University Press.

5. **Weske, M.** (2012). *Business Process Management: Concepts, Languages, Architectures*. Springer.

6. **OMG** (2011). *Business Process Model and Notation (BPMN) Version 2.0*. Object Management Group.

7. **Reisig, W.** (2013). *Understanding Petri Nets: Modeling Techniques, Analysis Methods, Case Studies*. Springer.
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
