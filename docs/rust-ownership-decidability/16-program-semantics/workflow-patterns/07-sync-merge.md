# 07 同步合并模式 (Synchronizing Merge)

## 📋 目录

- [07 同步合并模式 (Synchronizing Merge)](#07-同步合并模式-synchronizing-merge)
  - [📋 目录](#-目录)
  - [模式定义与语义](#模式定义与语义)
    - [核心语义](#核心语义)
    - [形式化表示](#形式化表示)
  - [Rust 实现示例](#rust-实现示例)
  - [与其他模式的关系](#与其他模式的关系)
  - [应用场景](#应用场景)
    - [实现要点](#实现要点)

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

/// 使用示例：动态分支同步
use tokio::task::JoinHandle;

pub async fn dynamic_sync_example() {
    let merger = Arc::new(SynchronizingMerge::<String>::new());
    let mut handles: Vec<JoinHandle<()>> = Vec::new();

    // 模拟多路选择后的动态分支
    let active_branches = vec!["branch_a", "branch_b", "branch_c"];

    for branch_id in active_branches {
        let merger_clone = Arc::clone(&merger);
        let handle = tokio::spawn(async move {
            let branch = merger_clone.register_branch().await;

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

    let results = merger.wait_for_all().await;
    println!("所有分支完成: {:?}", results);
}

/// 基于 Barrier 的实现（已知分支数时）
pub struct StaticSyncMerge<T> {
    barrier: Barrier,
    results: Arc<Mutex<Vec<T>>>,
}

impl<T: Clone + Send> StaticSyncMerge<T> {
    pub fn new(num_branches: usize) -> Self {
        Self {
            barrier: Barrier::new(num_branches + 1), // +1 用于主线程等待
            results: Arc::new(Mutex::new(Vec::with_capacity(num_branches))),
        }
    }

    pub async fn wait(&self) -> Vec<T> {
        self.barrier.wait().await;
        self.results.lock().await.clone()
    }

    pub async fn complete_branch(&self, result: T) {
        self.results.lock().await.push(result);
        self.barrier.wait().await;
    }
}
```

## 与其他模式的关系

| 模式 | 特点 | 区别 |
|------|------|------|
| 简单合并 | 任意分支到达即继续 | 不等待其他分支 |
| **同步合并** | 等待所有活跃分支 | 动态确定等待数量 |
| 多路合并 | 每个分支独立继续 | 不汇合 |
| 鉴别器 | 等待第一个 | 取消其他分支 |

## 应用场景

1. **分布式计算**：等待所有 Map 任务完成后进行 Reduce
2. **数据聚合**：收集所有并行查询的结果
3. **事务处理**：等待所有参与者准备就绪
4. **工作流引擎**：同步多路选择后的所有分支

### 实现要点

- 动态计数活跃分支数量
- 正确处理分支取消或失败
- 提供超时机制避免死等
