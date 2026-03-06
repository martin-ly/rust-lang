# 06 多路选择模式 (Multi-Choice)

## 模式定义与语义

多路选择模式允许从多个分支中选择一个或多个路径执行。
与排他选择（Exclusive Choice）不同，多路选择可以同时激活多个满足条件的分支。

### 核心语义

$$
\text{MultiChoice}(C, B_1, B_2, \ldots, B_n) = \{ B_i \mid C_i = \text{true} \}
$$

其中 $C = \{C_1, C_2, \ldots, C_n\}$ 是各分支的条件集合。

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State} = \{ \text{Ready}, \text{Evaluating}, \text{Branching}, \text{Executing}, \text{Completed} \} \\
& \text{Transition} = \{ \\
& \quad (\text{Ready}, \text{start}, \text{Evaluating}), \\
& \quad (\text{Evaluating}, \text{condition}_i, \text{Branching}) \text{ if } C_i, \\
& \quad (\text{Branching}, \text{fork}, \text{Executing}), \\
& \quad (\text{Executing}, \text{all\_done}, \text{Completed}) \\
& \}
\end{aligned}
$$

**流程代数表示：**

$$
\text{MultiChoice} = \sum_{i=1}^{n} [C_i] \to B_i
$$

## Rust 实现示例

```rust
use std::future::Future;
use std::pin::Pin;
use std::collections::HashSet;

/// 多路选择执行器
pub struct MultiChoice<T> {
    branches: Vec<Branch<T>>,
}

pub struct Branch<T> {
    condition: Box<dyn Fn(&T) -> bool + Send + Sync>,
    action: Box<dyn Fn(T) -> Pin<Box<dyn Future<Output = T> + Send>> + Send + Sync>,
}

impl<T: Clone + Send + 'static> MultiChoice<T> {
    pub fn new() -> Self {
        Self { branches: Vec::new() }
    }

    pub fn add_branch<F, Fut>(
        &mut self,
        condition: impl Fn(&T) -> bool + Send + Sync + 'static,
        action: F,
    ) where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = T> + Send + 'static,
    {
        self.branches.push(Branch {
            condition: Box::new(condition),
            action: Box::new(move |t| Box::pin(action(t))),
        });
    }

    /// 执行多路选择，返回所有满足条件的分支结果
    pub async fn execute(&self, input: T) -> Vec<T> {
        let mut results = Vec::new();
        let mut futures = Vec::new();

        for branch in &self.branches {
            if (branch.condition)(&input) {
                let future = (branch.action)(input.clone());
                futures.push(future);
            }
        }

        // 并行执行所有选中的分支
        for future in futures {
            results.push(future.await);
        }

        results
    }
}

/// 使用示例：订单处理
#[derive(Clone)]
struct Order {
    amount: f64,
    is_vip: bool,
    needs_gift_wrap: bool,
}

async fn process_multi_choice_order() {
    let mut processor = MultiChoice::<Order>::new();

    // VIP 折扣分支
    processor.add_branch(
        |order| order.is_vip,
        |mut order| async move {
            order.amount *= 0.9;
            order
        },
    );

    // 礼品包装分支
    processor.add_branch(
        |order| order.needs_gift_wrap,
        |order| async move {
            println!("添加礼品包装");
            order
        },
    );

    let order = Order {
        amount: 100.0,
        is_vip: true,
        needs_gift_wrap: true,
    };

    let results = processor.execute(order).await;
    println!("处理结果数量: {}", results.len());
}
```

## 与其他模式的关系

| 模式 | 区别 | 适用场景 |
|------|------|----------|
| 排他选择 | 只选一个分支 | 互斥条件 |
| **多路选择** | 可选多个分支 | 独立条件 |
| 并行分支 | 所有分支都执行 | 无条件并行 |
| 鉴别器 | 等待第一个完成 | 竞速场景 |

**关系公式：**

$$
\text{ExclusiveChoice} \subseteq \text{MultiChoice} \subseteq \text{ParallelSplit}
$$

## 应用场景

1. **订单处理**：同时应用多个独立的优惠规则
2. **审批流程**：根据条件并行发送给多个审批人
3. **数据处理**：对同一数据并行执行多个独立转换
4. **通知系统**：根据用户偏好选择多个通知渠道

### 注意事项

- 各分支条件应当是独立的，避免意外的交互
- 考虑分支执行结果合并的策略
- 注意资源消耗随分支数量线性增长
