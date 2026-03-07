# 08 多路合并模式 (Multi-Merge)

## 📋 目录

- [08 多路合并模式 (Multi-Merge)](#08-多路合并模式-multi-merge)
  - [📋 目录](#-目录)
  - [模式定义与语义](#模式定义与语义)
    - [核心语义](#核心语义)
    - [触发计数语义](#触发计数语义)
  - [BPMN 2.0 表示](#bpmn-20-表示)
    - [OR-Join 实现](#or-join-实现)
  - [形式化语义](#形式化语义)
    - [状态机形式化](#状态机形式化)
    - [进程代数 (CSP)](#进程代数-csp)
  - [正确性证明](#正确性证明)
    - [安全性](#安全性)
    - [活性](#活性)
  - [Rust 实现示例](#rust-实现示例)
    - [基础实现](#基础实现)
    - [广播通道实现](#广播通道实现)
    - [复杂工作流示例](#复杂工作流示例)
  - [与其他模式的关系](#与其他模式的关系)
  - [应用场景](#应用场景)
    - [注意事项](#注意事项)
  - [学术参考](#学术参考)

## 模式定义与语义

多路合并模式允许多个分支独立地汇入同一个后续节点，无需同步。
每个分支完成时都会触发后续活动的执行。

### 核心语义

$$
\text{MultiMerge}(P_1, P_2, \ldots, P_n, Q) = \forall i \in [1,n]: P_i \gg Q_i
$$

其中每个 $Q_i$ 是 $Q$ 的一个独立实例。

### 触发计数语义

多路合并的关键特性是**触发计数（Trigger Count）**：

$$
\text{TriggerCount}(Q) = \sum_{i=1}^{n} \mathbb{1}_{P_i \text{ completed}} = n
$$

每个分支完成都会独立触发一次后续活动：

$$
\text{MultiMerge} = \underbrace{Q \parallel Q \parallel \cdots \parallel Q}_{n \text{ times}}
$$

## BPMN 2.0 表示

在 BPMN 2.0 中，多路合并可以使用**无网关（No Gateway）**的多个序列流指向同一活动来表示：

```xml
<?xml version="1.0" encoding="UTF-8"?>
<bpmn:definitions xmlns:bpmn="http://www.omg.org/spec/BPMN/20100524/MODEL"
                  id="Definitions_MultiMerge">
  <bpmn:process id="MultiMergeProcess" isExecutable="true">

    <!-- 并行拆分 -->
    <bpmn:parallelGateway id="Fork" gatewayDirection="Diverging">
      <bpmn:outgoing>Flow_A</bpmn:outgoing>
      <bpmn:outgoing>Flow_B</bpmn:outgoing>
      <bpmn:outgoing>Flow_C</bpmn:outgoing>
    </bpmn:parallelGateway>

    <!-- 并行分支 -->
    <bpmn:task id="Task_A" name="Process A">
      <bpmn:incoming>Flow_A</bpmn:incoming>
      <bpmn:outgoing>Flow_A_Out</bpmn:outgoing>
    </bpmn:task>

    <bpmn:task id="Task_B" name="Process B">
      <bpmn:incoming>Flow_B</bpmn:incoming>
      <bpmn:outgoing>Flow_B_Out</bpmn:outgoing>
    </bpmn:task>

    <bpmn:task id="Task_C" name="Process C">
      <bpmn:incoming>Flow_C</bpmn:incoming>
      <bpmn:outgoing>Flow_C_Out</bpmn:outgoing>
    </bpmn:task>

    <!-- 多路合并：多个流入指向同一任务 -->
    <bpmn:task id="Notification_Task" name="Send Notification">
      <bpmn:incoming>Flow_A_Out</bpmn:incoming>
      <bpmn:incoming>Flow_B_Out</bpmn:incoming>
      <bpmn:incoming>Flow_C_Out</bpmn:incoming>
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
              │   Parallel Split    │ ◄── AND-Split
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
         └───────────────┼───────────────┘
                         │
                    ┌─────────┐
                    │  Send   │ ◄── 每个完成都触发一次
                    │ Notify  │     (Multi-Merge)
                    └────┬────┘
                         │
                         ▼
                    ┌─────────┐
                    │  Next   │
                    └─────────┘
```

### OR-Join 实现

也可以使用非排他性 OR-Join：

```
         ┌─────────┐
         │ Task A  │
         └────┬────┘
              │
              ▼
         ┌─────────┐
         │ Task B  │
         └────┬────┘
              │
              ▼
    ┌─────────────────────┐
    │      OR-Join        │ ◄── 非同步 OR-Join
    │   (非排他性合并)     │     每个流入触发一次流出
    └──────────┬──────────┘
               │
               ▼
          ┌─────────┐
          │  Next   │
          └─────────┘
```

## 形式化语义

### 状态机形式化

**扩展状态机：**

$$
\begin{aligned}
& \text{States} = \{ \\
& \quad \text{IDLE}_i: \text{分支 } i \text{ 空闲}, \\
& \quad \text{ACTIVE}_i: \text{分支 } i \text{ 执行中}, \\
& \quad \text{COMPLETED}_i: \text{分支 } i \text{ 完成}, \\
& \quad \text{TRIGGERED}_k: \text{已触发 } k \text{ 次后续活动}, \\
& \quad \text{FINISHED}: \text{全部完成} \\
& \} \\
& \text{Transitions} = \{ \\
& \quad \text{IDLE}_i \xrightarrow{\text{start}_i} \text{ACTIVE}_i, \\
& \quad \text{ACTIVE}_i \xrightarrow{\text{done}_i} \text{COMPLETED}_i, \\
& \quad \text{COMPLETED}_i \xrightarrow{\text{trigger}_i} \text{TRIGGERED}_{k+1}, \\
& \quad \text{TRIGGERED}_k \xrightarrow{\tau} \text{FINISHED} \text{ if } k = n \\
& \}
\end{aligned}
$$

### 进程代数 (CSP)

```csp
-- 多路合并的 CSP 形式化

-- 单个分支
Branch(i) = start.i -> work.i -> complete.i -> trigger.i -> SKIP

-- 多路合并：每个分支独立触发
MultiMerge(n) = || i:{1..n} @ [i](Branch(i) ; Next)

-- 其中 Next 是后续活动
Next = execute -> SKIP

-- 触发计数
TriggerCount = trigger?i -> count(i) ; TriggerCount
count(i) = increment -> SKIP
```

**CCS 表示：**

```ccs
-- 分支代理
Bi ::= ai.Bi' | τ.Bi'
Bi' ::= bi.ci.0

-- 多路合并
MultiMerge ::= B1 | B2 | ... | Bn

-- 每个 ci 独立触发后续
```

**π-演算：**

```
MultiMerge ::= νt1...tn.(P1(t1) | ... | Pn(tn) | Collector(t1, ..., tn))

Pi(ti) ::= work_i.ti<result_i>.0

Collector(t1, ..., tn) ::=
    t1?x.Q(x) | ... | tn?x.Q(x)

Q(x) ::= process(x).0
```

## 正确性证明

### 安全性

**定理 1（独立触发安全性）**: 多路合并保证每个分支完成都独立触发后续活动，且不会遗漏任何分支。

**证明:**

设分支集合 $B = \{b_1, b_2, \ldots, b_n\}$

1. 对于每个 $b_i$，定义完成事件 $c_i$
2. 多路合并监听所有 $c_i$ 事件
3. 当 $c_i$ 发生时，立即触发后续活动 $Q_i$
4. 由于没有同步屏障，$Q_i$ 的执行不依赖其他分支
5. 触发计数器保证每个 $c_i$ 都对应一次 $Q$ 的执行

因此每个分支完成都被正确处理。∎

### 活性

**定理 2（活性保证）**: 如果分支 $P_i$ 完成，则后续活动 $Q_i$ 最终会被执行。

**证明:**

1. 假设 $P_i$ 在时间 $t$ 完成
2. 完成事件 $c_i$ 被发送到多路合并
3. 由于没有等待其他分支的条件，立即调度 $Q_i$
4. $Q_i$ 在时间 $t + \delta$ 开始执行（$\delta$ 是调度延迟）
5. 由调度器公平性，$Q_i$ 最终完成

因此后续活动最终会被执行。∎

**定理 3（无阻塞）**: 多路合并不会阻塞任何分支的完成。

**证明:**

多路合并的特性：

- 不等待其他分支
- 立即响应完成事件
- 异步触发后续活动

因此分支完成不会被阻塞。∎

## Rust 实现示例

### 基础实现

```rust
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicUsize, Ordering};
use tokio::sync::mpsc;

use std::sync::Arc;
use tokio::sync::Mutex;

/// 多路合并处理器
pub struct MultiMerge<T, R> {
    merger_fn: Arc<dyn Fn(T) -> R + Send + Sync>,
    execution_count: AtomicUsize,
    sender: mpsc::Sender<R>,
    receiver: Arc<Mutex<mpsc::Receiver<R>>>,
}

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
```

### 广播通道实现

```rust
use tokio::sync::broadcast;

/// 基于广播通道的多路合并
pub struct BroadcastMultiMerge<T> {
    sender: broadcast::Sender<T>,
}

impl<T: Clone + Send + 'static> BroadcastMultiMerge<T> {
    pub fn new(capacity: usize) -> Self {
        let (sender, _) = broadcast::channel(capacity);
        Self { sender }
    }

    /// 分支完成时调用
    pub fn complete(&self, result: T) -> Result<usize, broadcast::error::SendError<T>> {
        self.sender.send(result)
    }

    /// 订阅合并结果
    pub fn subscribe(&self) -> broadcast::Receiver<T> {
        self.sender.subscribe()
    }

    /// 创建分支处理器
    pub fn create_branch(&self) -> BroadcastBranch<T> {
        BroadcastBranch {
            sender: self.sender.clone(),
        }
    }
}

pub struct BroadcastBranch<T> {
    sender: broadcast::Sender<T>,
}

impl<T: Clone> BroadcastBranch<T> {
    pub fn send(&self, value: T) -> Result<usize, broadcast::error::SendError<T>> {
        self.sender.send(value)
    }
}

/// 使用示例：广播通知
pub async fn broadcast_example() {
    let merge = BroadcastMultiMerge::<String>::new(100);
    let mut rx = merge.subscribe();

    // 创建多个分支
    let handles: Vec<_> = (0..5)
        .map(|i| {
            let branch = merge.create_branch();
            tokio::spawn(async move {
                // 模拟工作
                tokio::time::sleep(tokio::time::Duration::from_millis(i * 50)).await;
                let _ = branch.send(format!("Branch {} completed", i));
            })
        })
        .collect();

    // 收集所有通知
    let mut count = 0;
    while count < 5 {
        if let Ok(result) = rx.recv().await {
            println!("收到: {}", result);
            count += 1;
        }
    }

    for h in handles {
        let _ = h.await;
    }
}
```

### 复杂工作流示例

```rust
use tokio::task::JoinHandle;

/// 复杂多路合并工作流
pub struct ComplexMultiMergeWorkflow {
    notification_sender: mpsc::Sender<WorkflowEvent>,
}

#[derive(Clone, Debug)]
pub struct WorkflowEvent {
    pub source: String,
    pub event_type: EventType,
    pub timestamp: std::time::Instant,
}

#[derive(Clone, Debug)]
pub enum EventType {
    Completed,
    Failed(String),
    Timeout,
}

impl ComplexMultiMergeWorkflow {
    pub fn new() -> (Self, mpsc::Receiver<WorkflowEvent>) {
        let (tx, rx) = mpsc::channel(100);
        (Self { notification_sender: tx }, rx)
    }

    /// 执行并行工作流
    pub async fn execute(&self, tasks: Vec<Box<dyn Fn() -> Pin<Box<dyn Future<Output = Result<String, String>> + Send>> + Send>>) -> Vec<JoinHandle<()>> {
        let mut handles = Vec::new();

        for (i, task) in tasks.into_iter().enumerate() {
            let sender = self.notification_sender.clone();
            let task_name = format!("Task-{}", i);

            let handle = tokio::spawn(async move {
                let start_time = std::time::Instant::now();

                // 执行任务
                match task().await {
                    Ok(result) => {
                        println!("{} 完成: {}", task_name, result);
                        let _ = sender.send(WorkflowEvent {
                            source: task_name,
                            event_type: EventType::Completed,
                            timestamp: start_time,
                        }).await;
                    }
                    Err(e) => {
                        println!("{} 失败: {}", task_name, e);
                        let _ = sender.send(WorkflowEvent {
                            source: task_name,
                            event_type: EventType::Failed(e),
                            timestamp: start_time,
                        }).await;
                    }
                }
            });

            handles.push(handle);
        }

        handles
    }
}

/// 使用示例：订单处理
pub async fn order_processing_example() {
    let (workflow, mut event_rx) = ComplexMultiMergeWorkflow::new();

    // 定义订单处理任务
    let tasks: Vec<_> = vec![
        Box::new(|| Box::pin(async {
            // 验证库存
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            Ok("库存已验证".to_string())
        }) as Pin<Box<dyn Future<Output = Result<String, String>> + Send>>),

        Box::new(|| Box::pin(async {
            // 验证支付
            tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;
            Ok("支付已验证".to_string())
        }) as Pin<Box<dyn Future<Output = Result<String, String>> + Send>>),

        Box::new(|| Box::pin(async {
            // 验证地址
            tokio::time::sleep(tokio::time::Duration::from_millis(80)).await;
            Ok("地址已验证".to_string())
        }) as Pin<Box<dyn Future<Output = Result<String, String>> + Send>>),
    ];

    // 执行所有任务
    let handles = workflow.execute(tasks).await;

    // 处理事件流
    let mut completed_count = 0;
    while let Some(event) = event_rx.recv().await {
        println!("事件: {:?}", event);
        if matches!(event.event_type, EventType::Completed) {
            completed_count += 1;
            // 每个完成都触发通知
            println!("发送通知: {} 完成", event.source);
        }

        if completed_count >= 3 {
            break;
        }
    }

    // 等待所有任务完成
    for h in handles {
        let _ = h.await;
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

**模式转换关系：**

```
    Parallel Split (AND-Split)
            │
            ▼
    ┌───────────────┬───────────────┐
    ▼               ▼               ▼
┌─────────┐   ┌─────────┐   ┌─────────┐
│ Branch1 │   │ Branch2 │   │ Branch3 │
└────┬────┘   └────┬────┘   └────┬────┘
     │             │             │
     │             │             │
     ▼             ▼             ▼
┌─────────┐   ┌─────────┐   ┌─────────┐
│  Q1     │   │  Q2     │   │  Q3     │  ◄── 每个都触发
└────┬────┘   └────┬────┘   └────┬────┘
     │             │             │
     └─────────────┼─────────────┘
                   ▼
            ┌─────────────┐
            │ Multi-Merge │  (独立执行)
            └─────────────┘
```

## 应用场景

1. **消息广播**：多个消息源独立触发同一处理逻辑
2. **日志聚合**：多个服务独立上报日志，每条日志独立处理
3. **事件通知**：多个触发源产生的事件独立处理
4. **批量处理**：每个批次独立进入处理流程
5. **微服务监控**：多个服务健康检查独立报告
6. **数据流处理**：每个数据包独立处理

### 注意事项

- 后续活动需要处理并发执行的情况
- 考虑使用幂等性设计
- 注意资源竞争问题
- 监控触发次数防止资源耗尽
- 考虑批量处理优化性能

## 学术参考

1. **Russell, N., ter Hofstede, A.H.M., van der Aalst, W.M.P., & Mulyar, N.** (2006). "Workflow Control-Flow Patterns: A Revised View." *BPM Center Report* BPM-06-22.

2. **van der Aalst, W.M.P., & ter Hofstede, A.H.M.** (2005). "YAWL: Yet Another Workflow Language." *Information Systems*, 30(4), 245-275.

3. **Wohed, P., van der Aalst, W.M.P., Dumas, M., ter Hofstede, A.H.M., & Russell, N.** (2006). "On the Suitability of BPMN for Business Process Modelling." *Business Process Management*, 161-176.

4. **Recker, J., & Mendling, J.** (2006). "On the Translation between BPMN and BPEL: Conceptual Mismatch between Process Modeling Languages." *Proceedings of the 18th International Conference on Advanced Information Systems Engineering*, 521-532.

5. **Laue, R., & Mendling, J.** (2009). "The Impact of Structuredness on Error Probability of Process Models." *Information Systems and E-Business Management*, 7(2), 251-275.
