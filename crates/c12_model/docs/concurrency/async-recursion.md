# 递归异步：语义、等价与Rust 1.90 实践

> 关联：`async-sync-classification.md`、`../algorithms/models.md`

## 📋 目录

- [递归异步：语义、等价与Rust 1.90 实践](#递归异步语义等价与rust-190-实践)
  - [📋 目录](#-目录)
  - [问题动机](#问题动机)
  - [语义视角](#语义视角)
  - [设计策略](#设计策略)
  - [背压与取消](#背压与取消)
  - [Rust 1.90 实践片段](#rust-190-实践片段)
  - [等价关系与正确性](#等价关系与正确性)
  - [检查清单](#检查清单)
  - [递归异步：可终止性、可组合性与模式](#递归异步可终止性可组合性与模式)
  - [典型问题](#典型问题)
  - [模式](#模式)
  - [可终止性与安全](#可终止性与安全)
  - [示例参考](#示例参考)

## 问题动机

- 递归异步常见于分治、搜索、树/图遍历与工作流编排。
- 直接自引用 `async fn` 容易引入自引用状态与生命周期问题；需要 `Pin` 保障或改写策略。

## 语义视角

- `async fn` 编译为状态机；递归意味着状态机可再次入栈，若持有对自身局部的引用将违反移动与借用规则。
- 等价转化：尾递归/普通递归 → 显式栈/队列迭代；保证可终止性需度量或预算（深度/步数/时间）。

## 设计策略

1) 显式栈/队列迭代（推荐）
   - 用 `Vec`/`VecDeque` 管理待处理节点；每步 `await` 外移到循环体，便于背压与取消。

2) 分治 + 并发上限
   - 对子问题并发执行，使用 `Semaphore`/`JoinSet` 控制最大并行度，防止爆炸式任务膨胀。

3) 工作流状态机
   - 将递归定义为显式状态枚举并驱动推进；天然便于持久化/重放与可观测。

## 背压与取消

- 每个 `await` 前后设置预算检查（最大深度、最大在途任务数）。
- 父级取消向下传播：`JoinSet`/`scope`；对外部 I/O 一律 `timeout`。

## Rust 1.90 实践片段

```rust
use tokio::{sync::Semaphore, task::JoinSet};
use std::sync::Arc;

async fn process_node(id: usize) -> anyhow::Result<usize> {
    // ... 省略 I/O 或计算 ...
    Ok(id)
}

pub async fn dfs_bounded_concurrency(roots: Vec<usize>, max_concurrency: usize) -> anyhow::Result<usize> {
    let sem = Arc::new(Semaphore::new(max_concurrency));
    let mut sum = 0usize;
    let mut set = JoinSet::new();

    for r in roots {
        let permit = sem.clone().acquire_owned().await?;
        set.spawn(async move {
            let _p = permit; // 限流生命周期绑定
            process_node(r).await
        });
    }

    while let Some(res) = set.join_next().await {
        sum += res??;
    }
    Ok(sum)
}
```

要点：

- 以 `Semaphore` 限制并发；`JoinSet` 保证结构化并发与收割。
- 递归可改写为入队子节点；在循环中 `await`，避免深层自引用状态机。

## 等价关系与正确性

- 行为等价：以相同的遍历顺序/集合（允许重排）与相同的聚合结果作为可观测等价标准。
- 复杂度等价：工作量 W 恒定，跨度 D 取决于并发上限与依赖深度；优先降低 D。

## 检查清单

- 是否以显式栈/队列替代自引用递归？
- 是否设置并发上限与最大深度/预算？
- 是否对外部 I/O 设置 `timeout` 并传播取消？
- 是否记录在途任务数、队列长度、P99 延迟与失败/丢弃率？

## 递归异步：可终止性、可组合性与模式

## 典型问题

- 直接递归 `async fn` 形成自引用状态机可能需要 `Box::pin` 或 `async-recursion` crate。
- 非尾递归在大深度时造成堆分配与调度开销。

## 模式

- 显式堆栈：以 `Vec`/`VecDeque` 模拟递归栈，迭代解法避免深度状态机。
- 拆分 IO 与计算：IO 使用 `async`，计算使用 `spawn_blocking`。
- 结构化并发：对子任务使用 `JoinSet`/`scope` 管理生命周期与取消。

## 可终止性与安全

- 为递归引入度量函数（规模单调减少），可与属性测试联合验证。
- 明确取消传播：父任务取消应中断全部子任务并回收资源。

## 示例参考

- 参见 `examples/async_backpressure_demo.rs`：在递归/分治任务中结合限流与背压。
