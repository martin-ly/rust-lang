# 14 延迟选择模式 (Deferred Choice)

## 📋 目录

- [14 延迟选择模式 (Deferred Choice)](#14-延迟选择模式-deferred-choice)
  - [📋 目录](#-目录)
  - [模式定义与语义](#模式定义与语义)
    - [核心语义](#核心语义)
    - [外部事件触发](#外部事件触发)
  - [BPMN 2.0 表示](#bpmn-20-表示)
    - [基于事件的网关](#基于事件的网关)
  - [形式化语义](#形式化语义)
    - [状态机形式化](#状态机形式化)
    - [进程代数 (CSP)](#进程代数-csp)
  - [Race Condition 分析](#race-condition-分析)
    - [竞态条件检测](#竞态条件检测)
    - [冲突解决策略](#冲突解决策略)
  - [超时处理](#超时处理)
  - [正确性证明](#正确性证明)
    - [互斥性证明](#互斥性证明)
    - [活性证明](#活性证明)
  - [Rust 实现示例](#rust-实现示例)
    - [基础实现](#基础实现)
    - [外部事件处理](#外部事件处理)
    - [超时处理实现](#超时处理实现)
  - [与其他模式的关系](#与其他模式的关系)
  - [应用场景](#应用场景)
    - [注意事项](#注意事项)
  - [学术参考](#学术参考)

## 模式定义与语义

延迟选择模式将分支决策推迟到运行时，基于外部事件或信号来决定执行路径。
与排他选择不同，决策不是在设计时静态确定的。

### 核心语义

延迟选择等待多个可能的事件，第一个发生的事件决定执行路径：

$$
\text{DeferredChoice}(E_1 \to B_1, E_2 \to B_2, \ldots, E_n \to B_n) = \Box_{i=1}^{n} (E_i \to B_i)
$$

其中 $\Box$ 是外部选择算子，等待第一个发生的事件 $E_i$。

### 外部事件触发

**事件类型：**

| 类型 | 描述 | 示例 |
|------|------|------|
| 消息事件 | 接收外部消息 | 用户提交表单 |
| 信号事件 | 广播信号 | 系统告警 |
| 定时事件 | 时间到达 | 超时触发 |
| 条件事件 | 条件满足 | 数据状态变化 |

**事件监听语义：**

$$
\text{WaitEvents}(\{E_1, \ldots, E_n\}) = \lambda \sigma. \min_{i} \{ t \mid E_i(\sigma, t) \}
$$

## BPMN 2.0 表示

在 BPMN 2.0 中，延迟选择使用**基于事件的网关（Event-Based Gateway）**实现：

```xml
<?xml version="1.0" encoding="UTF-8"?>
<bpmn:definitions xmlns:bpmn="http://www.omg.org/spec/BPMN/20100524/MODEL">
  <bpmn:process id="DeferredChoiceProcess" isExecutable="true">

    <!-- 基于事件的网关 -->
    <bpmn:eventBasedGateway id="DeferredChoiceGW" instantiate="false">
      <bpmn:incoming>Flow_Start</bpmn:incoming>
      <bpmn:outgoing>Flow_Message</bpmn:outgoing>
      <bpmn:outgoing>Flow_Signal</bpmn:outgoing>
      <bpmn:outgoing>Flow_Timer</bpmn:outgoing>
    </bpmn:eventBasedGateway>

    <!-- 消息事件分支 -->
    <bpmn:intermediateCatchEvent id="MessageEvent" name="Receive Message">
      <bpmn:incoming>Flow_Message</bpmn:incoming>
      <bpmn:outgoing>Flow_Process_A</bpmn:outgoing>
      <bpmn:messageEventDefinition/>
    </bpmn:intermediateCatchEvent>

    <bpmn:task id="Process_A" name="Process Message">
      <bpmn:incoming>Flow_Process_A</bpmn:incoming>
    </bpmn:task>

    <!-- 信号事件分支 -->
    <bpmn:intermediateCatchEvent id="SignalEvent" name="Receive Signal">
      <bpmn:incoming>Flow_Signal</bpmn:incoming>
      <bpmn:outgoing>Flow_Process_B</bpmn:outgoing>
      <bpmn:signalEventDefinition/>
    </bpmn:intermediateCatchEvent>

    <bpmn:task id="Process_B" name="Process Signal">
      <bpmn:incoming>Flow_Process_B</bpmn:incoming>
    </bpmn:task>

    <!-- 定时事件分支（超时） -->
    <bpmn:intermediateCatchEvent id="TimerEvent" name="Timeout">
      <bpmn:incoming>Flow_Timer</bpmn:incoming>
      <bpmn:outgoing>Flow_Process_C</bpmn:outgoing>
      <bpmn:timerEventDefinition>
        <bpmn:timeDuration>PT5M</bpmn:timeDuration>
      </bpmn:timerEventDefinition>
    </bpmn:intermediateCatchEvent>

    <bpmn:task id="Process_C" name="Handle Timeout">
      <bpmn:incoming>Flow_Process_C</bpmn:incoming>
    </bpmn:task>

  </bpmn:process>
</bpmn:definitions>
```

### 基于事件的网关

**图形表示：**

```
                    ┌─────────┐
                    │  Start  │
                    └────┬────┘
                         │
                         ▼
              ┌─────────────────────┐
              │      ◇◇◇           │  ◄── 基于事件的网关
              │  Deferred Choice    │      (双层菱形)
              │  (Event-Based GW)   │
              └──────────┬──────────┘
                         │
       ┌─────────────────┼─────────────────┐
       │                 │                 │
       ▼                 ▼                 ▼
  ┌──────────┐     ┌──────────┐     ┌──────────┐
  │ ◇──────  │     │ ◇──────  │     │ ◇──────  │
  │  Message │     │  Signal  │     │  Timer   │
  │  Event   │     │  Event   │     │  Event   │
  └────┬─────┘     └────┬─────┘     └────┬─────┘
       │                │                │
       ▼                ▼                ▼
  ┌─────────┐     ┌─────────┐     ┌─────────┐
  │ Process │     │ Process │     │ Process │
  │    A    │     │    B    │     │    C    │
  └─────────┘     └─────────┘     └─────────┘

  说明：等待 Message/Signal/Timer 中的第一个发生
        第一个触发后，其他分支被取消/忽略
```

## 形式化语义

### 状态机形式化

$$
\begin{aligned}
& \text{States} = \{ \\
& \quad \text{WAITING}: \text{等待事件}, \\
& \quad \text{RECEIVED}(i): \text{收到事件 } i, \\
& \quad \text{SELECTED}(i): \text{选择分支 } i, \\
& \quad \text{CANCELLING}: \text{取消其他分支}, \\
& \quad \text{EXECUTING}(i): \text{执行分支 } i, \\
& \quad \text{COMPLETED}: \text{完成} \\
& \} \\
& \text{Transitions} = \{ \\
& \quad \text{WAITING} \xrightarrow{E_i} \text{RECEIVED}(i), \\
& \quad \text{RECEIVED}(i) \xrightarrow{\tau} \text{SELECTED}(i), \\
& \quad \text{SELECTED}(i) \xrightarrow{\text{cancel}_{j \neq i}} \text{CANCELLING}, \\
& \quad \text{CANCELLING} \xrightarrow{\tau} \text{EXECUTING}(i), \\
& \quad \text{EXECUTING}(i) \xrightarrow{\text{done}} \text{COMPLETED} \\
& \}
\end{aligned}
$$

### 进程代数 (CSP)

```csp
-- 延迟选择的 CSP 形式化

-- 事件定义
channel E1, E2, E3  -- 外部事件
channel cancel1, cancel2, cancel3
channel proceed

-- 分支
Branch(i) =
    (Ei -> proceed -> SKIP)
    [] (canceli -> STOP)

-- 延迟选择
DeferredChoice =
    (E1 -> cancel2 -> cancel3 -> proceed -> Branch(1))
    []
    (E2 -> cancel1 -> cancel3 -> proceed -> Branch(2))
    []
    (E3 -> cancel1 -> cancel2 -> proceed -> Branch(3))

-- 带超时的延迟选择
TimedDeferredChoice(t) =
    DeferredChoice [|{E1,E2,E3}|] Timeout(t)

Timeout(t) = WAIT(t) -> E3 -> SKIP  -- 超时作为默认分支
```

## Race Condition 分析

### 竞态条件检测

**竞态条件类型：**

1. **同时到达**: 两个事件几乎同时到达
2. **消息丢失**: 选择后到达的事件被忽略
3. **状态不一致**: 选择后系统状态未正确更新

**检测算法：**

```rust
/// 竞态条件检测器
pub struct RaceDetector {
    event_log: Vec<(EventId, Timestamp)>,
    threshold: Duration, // 同时到达阈值
}

impl RaceDetector {
    pub fn detect_race(&self) -> Option<Vec<EventId>> {
        // 检查时间窗口内的事件
        let window_events: Vec<_> = self.event_log
            .iter()
            .filter(|(_, ts)| {
                let latest = self.event_log.last().unwrap().1;
                latest - *ts < self.threshold
            })
            .map(|(id, _)| *id)
            .collect();

        if window_events.len() > 1 {
            Some(window_events)
        } else {
            None
        }
    }
}
```

### 冲突解决策略

| 策略 | 描述 | 适用场景 |
|------|------|----------|
| 先到先胜 | 时间戳最早的获胜 | 大多数场景 |
| 优先级 | 高优先级事件优先 | 有明确优先级 |
| 随机 | 随机选择一个 | 无偏好 |
| 合并 | 同时处理多个 | 可并行处理 |

## 超时处理

超时是延迟选择的重要方面：

$$
\text{DeferredChoice}_{\text{timeout}}(t) = \text{DeferredChoice} \triangleright_t \text{TimeoutAction}
$$

**超时语义：**

```
    ┌─────────────────────┐
    │   Deferred Choice   │
    │   (Waiting Events)  │
    └──────────┬──────────┘
               │
    ┌──────────┴──────────┐
    │                     │
    ▼                     ▼
 Event Arrives        Timeout(t)
    │                     │
    ▼                     ▼
 Process Event      Default Action
    │                     │
    └──────────┬──────────┘
               ▼
          Continue
```

## 正确性证明

### 互斥性证明

**定理（互斥选择）**: 延迟选择保证只有一个分支被执行。

**证明:**

设事件集合 $E = \{E_1, E_2, \ldots, E_n\}$

1. 系统在 `WAITING` 状态监听所有事件
2. 当第一个事件 $E_i$ 到达时：
   - 原子性地从 `WAITING` 转移到 `SELECTED(i)`
   - 发送取消信号给所有其他分支
3. 由于原子操作，只有一个事件能被选中
4. 后续事件到达时，系统已不在 `WAITING` 状态

因此只有一个分支被执行。∎

### 活性证明

**定理（最终选择）**: 如果至少有一个事件最终发生，延迟选择最终会做出选择。

**证明:**

情况 1: 正常事件

1. 假设事件 $E_i$ 在时间 $t$ 发生
2. 系统在 `WAITING` 状态检测到 $E_i$
3. 转移到 `SELECTED(i)` 并继续

情况 2: 超时

1. 如果在时间 $T$ 内没有事件发生
2. 超时事件触发，选择默认分支
3. 系统继续执行

因此系统最终会继续执行。∎

## Rust 实现示例

### 基础实现

```rust
use std::future::Future;
use std::pin::Pin;
use tokio::sync::{mpsc, oneshot};
use tokio::select;

/// 延迟选择执行器
pub struct DeferredChoice<T, R> {
    branches: Vec<Branch<T, R>>,
}

pub struct Branch<T, R> {
    event_rx: mpsc::Receiver<Event<T>>,
    handler: Box<dyn Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync>,
    name: String,
}

pub struct Event<T> {
    pub data: T,
    pub timestamp: std::time::Instant,
}

impl<T: Send + 'static, R: Send + 'static> DeferredChoice<T, R> {
    pub fn new() -> Self {
        Self { branches: Vec::new() }
    }

    pub fn add_branch<F, Fut>(
        &mut self,
        name: impl Into<String>,
        handler: F,
    ) -> mpsc::Sender<Event<T>>
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        let (tx, rx) = mpsc::channel(1);

        self.branches.push(Branch {
            event_rx: rx,
            handler: Box::new(move |t| Box::pin(handler(t))),
            name: name.into(),
        });

        tx
    }

    /// 等待第一个事件并执行对应分支
    pub async fn wait_and_execute(mut self) -> Option<(String, R)> {
        if self.branches.is_empty() {
            return None;
        }

        // 使用 select! 等待第一个事件
        let result = tokio::select! {
            biased; // 按顺序检查

            // 为每个分支生成一个 select 分支
            result = self.wait_first_event() => result,
        };

        result
    }

    async fn wait_first_event(&mut self) -> Option<(String, R)> {
        // 简化的实现 - 实际使用时要处理多个 receiver
        for branch in &mut self.branches {
            if let Some(event) = branch.event_rx.recv().await {
                let handler = &branch.handler;
                let result = handler(event.data).await;
                return Some((branch.name.clone(), result));
            }
        }
        None
    }
}

/// 更实用的实现：使用通道和 select!
pub async fn deferred_choice_example() -> String {
    let (tx1, mut rx1) = mpsc::channel::<String>(1);
    let (tx2, mut rx2) = mpsc::channel::<String>(1);
    let (tx3, mut rx3) = mpsc::channel::<String>(1);

    // 模拟外部事件源
    tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;
        let _ = tx2.send("event_from_source_b".to_string()).await;
    });

    tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        let _ = tx1.send("event_from_source_a".to_string()).await;
    });

    // 延迟选择：等待第一个到达的事件
    let result = tokio::select! {
        Some(data) = rx1.recv() => {
            format!("路径 A 被选择: {}", process_path_a(data).await)
        }
        Some(data) = rx2.recv() => {
            format!("路径 B 被选择: {}", process_path_b(data).await)
        }
        Some(data) = rx3.recv() => {
            format!("路径 C 被选择: {}", process_path_c(data).await)
        }
        else => "没有路径被激活".to_string(),
    };

    result
}

async fn process_path_a(data: String) -> String {
    format!("处理 A: {}", data.to_uppercase())
}

async fn process_path_b(data: String) -> String {
    format!("处理 B: {}", data.len())
}

async fn process_path_c(data: String) -> String {
    format!("处理 C: {:?}", data.chars().next())
}

/// 使用 oneshot 的竞速实现
pub async fn race_choice<T>(receivers: Vec<oneshot::Receiver<T>>) -> Option<T> {
    let mut futures: Vec<_> = receivers
        .into_iter()
        .map(|rx| Box::pin(async move { rx.await.ok() }))
        .collect();

    loop {
        if futures.is_empty() {
            return None;
        }

        let (result, _, remaining) = futures::future::select_all(futures).await;

        if let Some(value) = result {
            return Some(value);
        }

        futures = remaining;
    }
}
```

### 外部事件处理

```rust
/// 带超时处理的延迟选择
pub async fn deferred_choice_with_timeout<T>(
    receivers: Vec<oneshot::Receiver<T>>,
    timeout: tokio::time::Duration,
) -> Option<T> {
    tokio::select! {
        result = race_choice(receivers) => result,
        _ = tokio::time::sleep(timeout) => {
            println!("延迟选择超时");
            None
        }
    }
}

/// 使用示例：审批流程
# [derive(Debug, Clone)]
enum ApprovalEvent {
    Approved { by: String, comments: String },
    Rejected { by: String, reason: String },
    Escalated { to: String },
    Timeout,
}

pub async fn approval_workflow() -> ApprovalEvent {
    let (approve_tx, approve_rx) = oneshot::channel();
    let (reject_tx, reject_rx) = oneshot::channel();
    let (escalate_tx, escalate_rx) = oneshot::channel();

    // 模拟用户操作
    tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
        let _ = approve_tx.send(ApprovalEvent::Approved {
            by: "manager".to_string(),
            comments: "Looks good".to_string(),
        });
    });

    // 延迟选择：等待用户决策
    let timeout = tokio::time::Duration::from_secs(5);

    tokio::select! {
        Ok(event) = approve_rx => event,
        Ok(event) = reject_rx => event,
        Ok(event) = escalate_rx => event,
        _ = tokio::time::sleep(timeout) => ApprovalEvent::Timeout,
    }
}
```

### 超时处理实现

```rust
use tokio::time::{timeout, Duration};

/// 带优先级的延迟选择
pub struct PriorityDeferredChoice<T, R> {
    branches: Vec<(Priority, Box<dyn Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync>)>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Priority(u8);

impl<T: Send + 'static, R: Send + 'static> PriorityDeferredChoice<T, R> {
    pub fn new() -> Self {
        Self { branches: Vec::new() }
    }

    pub fn add_branch<F, Fut>(&mut self, priority: u8, handler: F)
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        self.branches.push((
            Priority(priority),
            Box::new(move |t| Box::pin(handler(t))),
        ));
    }

    /// 执行带优先级的选择
    pub async fn execute(&self, events: Vec<(Priority, T)>) -> Option<R> {
        // 按优先级排序
        let mut sorted_events = events;
        sorted_events.sort_by_key(|(p, _)| *p);

        // 选择优先级最高的事件
        sorted_events.into_iter().next().map(|(_, data)| {
            // 找到对应处理器
            // 简化实现，实际应该根据事件类型选择
            self.branches.first().map(|(_, handler)| handler(data))
        })?.await
    }
}

/// 取消令牌模式集成
pub struct CancellableDeferredChoice<T, R> {
    cancel_token: tokio_util::sync::CancellationToken,
    branches: Vec<Branch<T, R>>,
}

impl<T: Send + 'static, R: Send + 'static> CancellableDeferredChoice<T, R> {
    pub fn new() -> Self {
        Self {
            cancel_token: tokio_util::sync::CancellationToken::new(),
            branches: Vec::new(),
        }
    }

    pub fn cancel(&self) {
        self.cancel_token.cancel();
    }

    pub async fn execute(&self, events: Vec<impl Future<Output = (String, T)>>) -> Option<(String, R)> {
        tokio::select! {
            _ = self.cancel_token.cancelled() => {
                println!("延迟选择被取消");
                None
            }
            result = Self::race_events(events) => {
                let (branch_name, data) = result;
                // 执行对应分支
                Some((branch_name, self.execute_branch(&branch_name, data).await))
            }
        }
    }

    async fn race_events<F>(events: Vec<F>) -> (String, T)
    where
        F: Future<Output = (String, T)>,
    {
        let futures: Vec<_> = events.into_iter()
            .map(|f| Box::pin(f))
            .collect();

        let (result, _, _) = futures::future::select_all(futures).await;
        result
    }

    async fn execute_branch(&self, name: &str, data: T) -> R {
        // 查找并执行对应分支
        todo!("实现分支查找和执行")
    }
}
```

## 与其他模式的关系

| 模式 | 决策时机 | 触发方式 |
|------|----------|----------|
| 排他选择 | 设计时/运行时求值 | 条件判断 |
| **延迟选择** | 运行时事件 | 外部事件 |
| 多路选择 | 运行时求值 | 多条件判断 |
| 鉴别器 | 运行时 | 竞速完成 |

**关系公式：**

$$
\text{DeferredChoice} = \text{ExternalChoice} = \text{Discriminator}(\text{event-based})
$$

## 应用场景

1. **用户决策**：等待用户从多个选项中选择
2. **外部事件响应**：基于最先到达的外部信号决策
3. **竞速条件**：多个数据源，采用最快响应
4. **中断处理**：正常流程与中断信号竞速
5. **审批流程**：等待多个审批人中的一个响应
6. **消息路由**：根据消息类型路由到不同处理器

### 注意事项

- 确保事件源能够正确发送信号
- 考虑超时处理避免无限等待
- 处理竞态条件下的边界情况
- 提供取消机制
- 记录选择决策用于审计

## 学术参考

1. **Hoare, C.A.R.** (1985). *Communicating Sequential Processes*. Prentice Hall.

2. **Roscoe, A.W.** (1997). *The Theory and Practice of Concurrency*. Prentice Hall.

3. **van der Aalst, W.M.P., & ter Hofstede, A.H.M.** (2005). "YAWL: Yet Another Workflow Language." *Information Systems*, 30(4), 245-275.

4. **Milner, R.** (1989). *Communication and Concurrency*. Prentice Hall.

5. **Winskel, G.** (1993). *The Formal Semantics of Programming Languages*. MIT Press.

6. **Russell, N., ter Hofstede, A.H.M., Edmond, D., & van der Aalst, W.M.P.** (2005). "Workflow Data Patterns: Identification, Representation and Tool Support." *Conceptual Modeling – ER 2005*, 353-368.
