# 15 交错路由模式 (Interleaved Routing)

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

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State} = \{ \text{Ready}, \text{Executing}_i, \text{Done}_i \} \\
& \text{Transition} = \{ \\
& \quad (\text{Ready}, \text{select}_i, \text{Executing}_i) \text{ non-deterministic}, \\
& \quad (\text{Executing}_i, \text{complete}, \text{Ready}) \text{ if } \exists j \neq i: \neg \text{Done}_j, \\
& \quad (\text{Executing}_i, \text{complete}, \text{AllDone}) \text{ if all others done} \\
& \}
\end{aligned}
$$

**进程代数：**

$$
\text{Interleaved} = A_1 \| A_2 \| \cdots \| A_n \text{ with interleaving semantics}
$$

## Rust 实现示例

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

### 注意事项

- 使用信号量或互斥锁保证互斥
- 考虑任务饥饿问题
- 可以引入优先级改善调度
- 监控执行时间确保公平性
