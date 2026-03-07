# 15 交错路由模式 (Interleaved Routing)

## 📋 目录

- [15 交错路由模式 (Interleaved Routing)](#15-交错路由模式-interleaved-routing)
  - [📋 目录](#-目录)
  - [模式定义与语义](#模式定义与语义)
    - [核心语义](#核心语义)
    - [与并行和顺序的区别](#与并行和顺序的区别)
  - [偏序约束](#偏序约束)
    - [偏序关系定义](#偏序关系定义)
    - [交错语义](#交错语义)
  - [BPMN 2.0 表示](#bpmn-20-表示)
  - [形式化语义](#形式化语义)
    - [状态机形式化](#状态机形式化)
    - [进程代数](#进程代数)
  - [正确性证明](#正确性证明)
    - [互斥性证明](#互斥性证明)
    - [活性证明](#活性证明)
  - [Rust 实现示例](#rust-实现示例)
    - [基础实现](#基础实现)
    - [顺序执行器](#顺序执行器)
    - [优先级交错](#优先级交错)
  - [与其他模式的关系](#与其他模式的关系)
  - [应用场景](#应用场景)
    - [注意事项](#注意事项)
  - [学术参考](#学术参考)

## 模式定义与语义

交错路由模式允许多个活动以任意顺序执行，但任意时刻只有一个活动处于活跃状态。
与真正的并行不同，这是一种串行化的伪并行。

### 核心语义

$$
\text{Interleaved}(A_1, A_2, \ldots, A_n) = \text{shuffle}(A_1, A_2, \ldots, A_n)
$$

其中 $\text{shuffle}$ 表示活动的任意交错执行，满足：

- 每个活动的原子性得到保证
- 没有两个活动同时执行
- 执行顺序非确定

### 与并行和顺序的区别

| 模式 | 并发性 | 互斥性 | 顺序约束 |
|------|--------|--------|----------|
| 顺序执行 | 无 | N/A | 固定 |
| **交错路由** | 伪并行 | 有 | 任意 |
| 并行分支 | 真并行 | 无 | 无 |
| 临界区 | 真并行 | 区域内 | 无 |

## 偏序约束

### 偏序关系定义

交错路由定义了活动间的偏序关系：

$$
(A, \preceq) \text{ 其中 } a_i \preceq a_j \text{ 表示 } a_i \text{ 必须在 } a_j \text{ 之前}
$$

**性质：**

1. **自反性**: $\forall a \in A: a \preceq a$
2. **反对称性**: $a \preceq b \land b \preceq a \implies a = b$
3. **传递性**: $a \preceq b \land b \preceq c \implies a \preceq c$

**交错路由的偏序：**

$$
\forall a_i, a_j \in A: \neg(a_i \preceq a_j) \land \neg(a_j \preceq a_i)
$$

即活动间无顺序约束（可比较性除外）。

### 交错语义

**交错操作符（Interleaving）:**

$$
P \interleave Q = \{ s \mid s \text{ 是 } P \text{ 和 } Q \text{ 动作的交错} \}
$$

形式化定义：

$$
\frac{P \xrightarrow{a} P'}{P \interleave Q \xrightarrow{a} P' \interleave Q}
\quad
\frac{Q \xrightarrow{a} Q'}{P \interleave Q \xrightarrow{a} P \interleave Q'}
$$

## BPMN 2.0 表示

在 BPMN 2.0 中，交错路由可以使用**任务（Task）**配合**顺序流（Sequence Flow）**的特定模式实现：

```xml
<?xml version="1.0" encoding="UTF-8"?>
<bpmn:definitions xmlns:bpmn="http://www.omg.org/spec/BPMN/20100524/MODEL">
  <bpmn:process id="InterleavedRoutingProcess" isExecutable="true">

    <!-- 开始 -->
    <bpmn:startEvent id="Start"/>

    <!-- 任务 A -->
    <bpmn:task id="Task_A" name="Activity A">
      <bpmn:incoming>Flow_Start</bpmn:incoming>
      <bpmn:outgoing>Flow_A_Done</bpmn:outgoing>
    </bpmn:task>

    <!-- 任务 B -->
    <bpmn:task id="Task_B" name="Activity B">
      <bpmn:incoming>Flow_A_Done</bpmn:incoming>
      <bpmn:outgoing>Flow_B_Done</bpmn:outgoing>
    </bpmn:task>

    <!-- 任务 C -->
    <bpmn:task id="Task_C" name="Activity C">
      <bpmn:incoming>Flow_B_Done</bpmn:incoming>
    </bpmn:task>

    <!-- 注意：这里显示的是顺序执行
         实际交错路由允许 A, B, C 的任意顺序
         但任意时刻只有一个活动执行 -->

  </bpmn:process>
</bpmn:definitions>
```

**图形表示（概念图）：**

```
                    ┌─────────┐
                    │  Start  │
                    └────┬────┘
                         │
                         ▼
              ┌─────────────────────┐
              │  Interleaved Set    │
              │  {A, B, C}          │
              └──────────┬──────────┘
                         │
       ┌─────────────────┼─────────────────┐
       │                 │                 │
       │  (任意顺序)       │                 │
       ▼                 ▼                 ▼
  ┌─────────┐      ┌─────────┐      ┌─────────┐
  │    A    │      │    B    │      │    C    │
  │ Execute │      │ Execute │      │ Execute │
  └────┬────┘      └────┬────┘      └────┬────┘
       │                 │                 │
       │                 │                 │
       └─────────────────┼─────────────────┘
                         │
              ┌─────────────────────┐
              │   All Completed     │
              │   (Sequentialized)  │
              └──────────┬──────────┘
                         │
                         ▼
                    ┌─────────┐
                    │   End   │
                    └─────────┘

  说明：A, B, C 以任意顺序执行
        但任意时刻只有一个活动处于活跃状态
        互斥性通过信号量/互斥锁保证
```

## 形式化语义

### 状态机形式化

$$
\begin{aligned}
& \text{States} = \{ \\
& \quad \text{READY}: \text{准备}, \\
& \quad \text{SELECTING}: \text{选择下一个活动}, \\
& \quad \text{EXECUTING}(i): \text{执行活动 } i, \\
& \quad \text{COMPLETED}(i): \text{活动 } i \text{ 完成}, \\
& \quad \text{ALL_DONE}: \text{全部完成} \\
& \} \\
& \text{Transitions} = \{ \\
& \quad \text{READY} \xrightarrow{\tau} \text{SELECTING}, \\
& \quad \text{SELECTING} \xrightarrow{\text{select}_i} \text{EXECUTING}(i) \text{ if } i \text{ not completed}, \\
& \quad \text{EXECUTING}(i) \xrightarrow{\text{done}_i} \text{COMPLETED}(i), \\
& \quad \text{COMPLETED}(i) \xrightarrow{\tau} \text{SELECTING} \text{ if } \exists j \text{ not completed}, \\
& \quad \text{COMPLETED}(i) \xrightarrow{\tau} \text{ALL_DONE} \text{ if all completed} \\
& \}
\end{aligned}
$$

### 进程代数

**CSP 形式化：**

```csp
-- 交错路由的 CSP 形式化

-- 单个活动
Activity(i) = start.i -> work.i -> complete.i -> SKIP

-- 交错执行（使用交错操作符）
Interleaved =
    Activity(1) ||| Activity(2) ||| Activity(3)

-- 其中 ||| 是交错操作符
-- 活动以任意顺序执行，但任意时刻只有一个在进行

-- 带选择的交错
SelectiveInterleaved =
    (start?i -> work.i -> complete.i -> SelectiveInterleaved)
    [] (all_complete -> SKIP)
```

**CCS 表示：**

```ccs
-- 交错操作符
Ai ::= ai.Ai' | τ.Ai'
Ai' ::= bi.0

-- 交错组合
Interleaved ::= A1 ||| A2 ||| A3

-- 其中 ||| 表示交错，任意时刻只有一个 ai 或 bi 可以执行
```

## 正确性证明

### 互斥性证明

**定理（执行互斥）**: 交错路由保证任意时刻只有一个活动处于执行状态。

**证明:**

通过状态机归纳：

**基础**: 初始状态 `READY`，无活动执行。

**归纳**:

- 从 `SELECTING` 转移到 `EXECUTING(i)` 时，选择活动 $i$
- 状态变为 `EXECUTING(i)`，只有活动 $i$ 在执行
- 从 `EXECUTING(i)` 转移到 `COMPLETED(i)` 时，活动 $i$ 完成
- 转移到 `SELECTING` 时才可能选择新活动

因此任意时刻只有一个活动在执行。∎

### 活性证明

**定理（最终完成）**: 所有活动最终都会执行并完成。

**证明:**

设活动集合 $A = \{a_1, a_2, \ldots, a_n\}$

1. 每次从 `SELECTING` 状态，选择一个未完成的活动
2. 由于调度器公平性，每个未完成的活动最终会被选择
3. 被选中的活动最终完成（假设活动有活性）
4. 经过 $n$ 次选择和完成，所有活动都完成

因此所有活动最终完成。∎

## Rust 实现示例

### 基础实现

```rust
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use tokio::sync::{Mutex, Semaphore};

/// 交错执行器
pub struct InterleavedRouter<T, R> {
    tasks: VecDeque<Task<T, R>>,
    semaphore: Arc<Semaphore>,
}

type Task<T, R> = Box<dyn FnOnce(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send>;

impl<T: Send + Clone + 'static, R: Send + 'static> InterleavedRouter<T, R> {
    pub fn new() -> Self {
        Self {
            tasks: VecDeque::new(),
            semaphore: Arc::new(Semaphore::new(1)), // 只允许一个并发
        }
    }

    pub fn add_task<F, Fut>(&mut self, task: F)
    where
        F: FnOnce(T) -> Fut + Send + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        self.tasks.push_back(Box::new(|t| Box::pin(task(t))));
    }

    /// 以任意顺序交错执行所有任务
    pub async fn execute_interleaved(mut self, input: T) -> Vec<R> {
        let mut results = Vec::with_capacity(self.tasks.len());
        let mut handles = Vec::new();

        // 随机打乱任务顺序
        use rand::seq::SliceRandom;
        let mut tasks: Vec<_> = self.tasks.into_iter().collect();
        tasks.shuffle(&mut rand::thread_rng());

        for task in tasks {
            let permit = self.semaphore.clone().acquire_owned().await.unwrap();
            let input_clone = input.clone();

            let handle = tokio::spawn(async move {
                let _permit = permit; // 持有信号量
                let result = task(input_clone).await;
                result
            });

            handles.push(handle);
        }

        for handle in handles {
            if let Ok(result) = handle.await {
                results.push(result);
            }
        }

        results
    }
}

/// 使用示例：资源受限的处理
#[derive(Clone)]
struct ProcessingContext {
    resource_id: String,
    data: Vec<u8>,
}

#[derive(Debug)]
struct ProcessingResult {
    step: String,
    output: String,
}

async fn step_a(ctx: ProcessingContext) -> ProcessingResult {
    println!("执行步骤 A，使用资源 {}", ctx.resource_id);
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    ProcessingResult {
        step: "A".to_string(),
        output: format!("A 完成，处理 {} 字节", ctx.data.len()),
    }
}

async fn step_b(ctx: ProcessingContext) -> ProcessingResult {
    println!("执行步骤 B，使用资源 {}", ctx.resource_id);
    tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;
    ProcessingResult {
        step: "B".to_string(),
        output: "B 完成".to_string(),
    }
}

async fn step_c(ctx: ProcessingContext) -> ProcessingResult {
    println!("执行步骤 C，使用资源 {}", ctx.resource_id);
    tokio::time::sleep(tokio::time::Duration::from_millis(80)).await;
    ProcessingResult {
        step: "C".to_string(),
        output: "C 完成".to_string(),
    }
}

pub async fn interleaved_example() {
    let mut router = InterleavedRouter::<ProcessingContext, ProcessingResult>::new();

    router.add_task(step_a);
    router.add_task(step_b);
    router.add_task(step_c);

    let ctx = ProcessingContext {
        resource_id: "shared_resource_1".to_string(),
        data: vec![1, 2, 3, 4, 5],
    };

    println!("开始交错执行...");
    let results = router.execute_interleaved(ctx).await;

    println!("\n所有步骤完成:");
    for r in results {
        println!("  {:?}", r);
    }
}
```

### 顺序执行器

```rust
/// 基于 Tokio 的 Mutex 实现
pub struct SequentialExecutor<T, R> {
    tasks: Vec<Box<dyn Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send>>,
}

impl<T: Clone + Send + 'static, R: Send + 'static> SequentialExecutor<T, R> {
    pub fn new() -> Self {
        Self { tasks: Vec::new() }
    }

    pub fn add(&mut self, task: impl Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + 'static) {
        self.tasks.push(Box::new(task));
    }

    pub async fn run_in_order(self, input: T, order: Vec<usize>) -> Vec<R> {
        let mut results = Vec::new();

        for idx in order {
            if let Some(task) = self.tasks.get(idx) {
                let result = task(input.clone()).await;
                results.push(result);
            }
        }

        results
    }
}

/// 使用示例
pub async fn sequential_executor_example() {
    let mut executor = SequentialExecutor::<i32, i32>::new();

    executor.add(|x| Box::pin(async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        x * 2
    }));

    executor.add(|x| Box::pin(async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        x + 10
    }));

    // 以特定顺序执行
    let results = executor.run_in_order(5, vec![1, 0]).await;
    println!("结果: {:?}", results);
}
```

### 优先级交错

```rust
/// 优先级交错：按优先级而非随机
pub struct PriorityInterleaved<T, R> {
    tasks: Vec<(u32, Task<T, R>)>, // (priority, task)
}

impl<T: Send + Clone + 'static, R: Send + 'static> PriorityInterleaved<T, R> {
    pub fn new() -> Self {
        Self { tasks: Vec::new() }
    }

    pub fn add_task<F, Fut>(&mut self, priority: u32, task: F)
    where
        F: FnOnce(T) -> Fut + Send + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        self.tasks.push((priority, Box::new(|t| Box::pin(task(t)))));
    }

    pub async fn execute(mut self, input: T) -> Vec<R> {
        // 按优先级排序（数字越小优先级越高）
        self.tasks.sort_by_key(|(p, _)| *p);

        let semaphore = Arc::new(Semaphore::new(1));
        let mut handles = Vec::new();

        for (_, task) in self.tasks {
            let permit = semaphore.clone().acquire_owned().await.unwrap();
            let input_clone = input.clone();

            let handle = tokio::spawn(async move {
                let _permit = permit;
                task(input_clone).await
            });

            handles.push(handle);
        }

        let mut results = Vec::new();
        for handle in handles {
            if let Ok(r) = handle.await {
                results.push(r);
            }
        }
        results
    }
}

/// 依赖感知的交错
pub struct DependencyAwareInterleaved<T, R> {
    tasks: Vec<Task<T, R>>,
    dependencies: Vec<Vec<usize>>, // 每个任务的依赖列表
}

impl<T: Clone + Send + 'static, R: Send + 'static> DependencyAwareInterleaved<T, R> {
    pub fn new() -> Self {
        Self {
            tasks: Vec::new(),
            dependencies: Vec::new(),
        }
    }

    pub fn add_task<F, Fut>(&mut self, task: F, deps: Vec<usize>)
    where
        F: FnOnce(T) -> Fut + Send + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        self.tasks.push(Box::new(|t| Box::pin(task(t))));
        self.dependencies.push(deps);
    }

    /// 拓扑排序执行
    pub async fn execute_with_deps(self, input: T) -> Vec<Option<R>> {
        let n = self.tasks.len();
        let mut completed = vec![false; n];
        let mut results: Vec<Option<R>> = vec![None; n];
        let semaphore = Arc::new(Semaphore::new(1));

        while completed.iter().any(|&c| !c) {
            // 找到所有依赖已满足的任务
            let ready: Vec<usize> = (0..n)
                .filter(|&i| {
                    !completed[i] && self.dependencies[i].iter().all(|&d| completed[d])
                })
                .collect();

            if ready.is_empty() && !completed.iter().all(|&c| c) {
                panic!("循环依赖 detected");
            }

            // 串行执行就绪任务
            for idx in ready {
                let permit = semaphore.clone().acquire_owned().await.unwrap();
                let task = &self.tasks[idx];
                let input_clone = input.clone();

                let result = tokio::spawn(async move {
                    let _permit = permit;
                    task(input_clone).await
                }).await.unwrap();

                results[idx] = Some(result);
                completed[idx] = true;
            }
        }

        results
    }
}
```

## 与其他模式的关系

| 模式 | 并发性 | 互斥性 |
|------|--------|--------|
| **交错路由** | 伪并行 | 有 |
| 并行分支 | 真并行 | 无 |
| 顺序执行 | 无 | 有 |
| 临界区 | 真并行 | 区域内互斥 |

**关系公式：**

$$
\text{Interleaved} = \text{Parallel} \cap \text{SequentialConstraint}
$$

## 应用场景

1. **单资源访问**：多个任务需要独占访问同一资源
2. **事务处理**：保证每个事务的原子性
3. **调试模式**：串行化并行代码便于调试
4. **嵌入式系统**：单核处理器的任务调度
5. **数据库操作**：避免并发修改问题
6. **测试执行**：确保测试用例串行执行

### 注意事项

- 使用信号量或互斥锁保证互斥
- 考虑任务饥饿问题
- 可以引入优先级改善调度
- 监控执行时间确保公平性
- 避免优先级反转

## 学术参考

1. **Hoare, C.A.R.** (1978). "Communicating Sequential Processes." *Communications of the ACM*, 21(8), 666-677.

2. **Milner, R.** (1989). *Communication and Concurrency*. Prentice Hall.

3. **van der Aalst, W.M.P., & van Hee, K.** (2002). *Workflow Management: Models, Methods, and Systems*. MIT Press.

4. **Russell, N., ter Hofstede, A.H.M., van der Aalst, W.M.P., & Mulyar, N.** (2006). "Workflow Control-Flow Patterns: A Revised View." *BPM Center Report* BPM-06-22.

5. **Reisig, W.** (1985). *Petri Nets: An Introduction*. Springer.

6. **Best, E., & Devillers, R.** (1987). "Sequential and Concurrent Behaviour in Petri Net Theory." *Theoretical Computer Science*, 55(1), 87-136.
