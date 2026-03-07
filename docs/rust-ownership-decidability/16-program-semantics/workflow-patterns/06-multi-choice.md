# 06 多路选择模式 (Multi-Choice) - 完整形式化语义

## 目录

- [06 多路选择模式 (Multi-Choice) - 完整形式化语义](#06-多路选择模式-multi-choice---完整形式化语义)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [1.1 历史背景](#11-历史背景)
  - [2. 模式定义与语义](#2-模式定义与语义)
    - [2.1 概念定义](#21-概念定义)
    - [2.2 核心语义](#22-核心语义)
    - [2.3 形式化表示](#23-形式化表示)
      - [2.3.1 状态机表示](#231-状态机表示)
      - [2.3.2 流程代数表示 (CSP 风格)](#232-流程代数表示-csp-风格)
      - [2.3.3 Petri 网表示](#233-petri-网表示)
  - [3. BPMN 与标准规范](#3-bpmn-与标准规范)
    - [3.1 BPMN 表示](#31-bpmn-表示)
    - [3.2 UML 活动图](#32-uml-活动图)
    - [3.3 WfMC 标准](#33-wfmc-标准)
  - [4. 进程代数形式化](#4-进程代数形式化)
    - [4.1 CCS 表示](#41-ccs-表示)
    - [4.2 CSP 表示](#42-csp-表示)
    - [4.3 π-演算表示](#43-π-演算表示)
  - [5. Rust 实现](#5-rust-实现)
    - [5.1 基础实现](#51-基础实现)
    - [5.2 带错误处理的高级实现](#52-带错误处理的高级实现)
    - [5.3 订单处理完整示例](#53-订单处理完整示例)
  - [6. 正确性证明](#6-正确性证明)
    - [6.1 活性 (Liveness)](#61-活性-liveness)
    - [6.2 安全性 (Safety)](#62-安全性-safety)
    - [6.3 正确性条件](#63-正确性条件)
  - [7. 与其他模式的关系](#7-与其他模式的关系)
    - [7.1 模式层次](#71-模式层次)
    - [7.2 形式化关系](#72-形式化关系)
    - [7.3 与合并模式的配合](#73-与合并模式的配合)
  - [8. 应用场景与案例](#8-应用场景与案例)
    - [8.1 电商订单处理](#81-电商订单处理)
    - [8.2 数据ETL管道](#82-数据etl管道)
    - [8.3 多租户通知系统](#83-多租户通知系统)
  - [9. 变体与扩展](#9-变体与扩展)
    - [9.1 加权多路选择](#91-加权多路选择)
    - [9.2 动态多路选择](#92-动态多路选择)
    - [9.3 嵌套多路选择](#93-嵌套多路选择)
  - [10. 总结](#10-总结)
  - [参考文献](#参考文献)

---

## 1. 引言

多路选择模式（Multi-Choice，也称为 OR-Split）是工作流控制流模式中的核心模式之一，允许从多个分支中选择一个或多个路径执行。与排他选择（Exclusive Choice，XOR-Split）不同，多路选择可以同时激活多个满足条件的分支，为并行处理提供了灵活性。

### 1.1 历史背景

多路选择模式最早由 Wil van der Aalst 等人在 "Workflow Patterns" (2003) 中系统定义，成为工作流领域的标准术语。

---

## 2. 模式定义与语义

### 2.1 概念定义

**多路选择** 是一个控制流构造，它将单个执行线程分化为多个可能的执行路径，其中：

- **守卫条件** (Guard Conditions): 每个出边有一个布尔表达式
- **动态激活**: 运行时评估哪些路径被激活
- **并行执行**: 多个激活的路径可以并发执行

```
语法定义:

MultiChoice ::= "OR-Split" GuardedBranches GuardedBranches
GuardedBranches ::= Branch { "||" Branch }
Branch ::= Condition "->" Activity
Condition ::= BooleanExpression
```

### 2.2 核心语义

**激活语义**:

$$
\text{Activated}(C, B_1, ..., B_n) = \{ B_i \mid C_i = \text{true} \}
$$

**执行语义**:

$$
\llbracket \text{MultiChoice}(\{(C_i, B_i)\}) \rrbracket =
\begin{cases}
\text{fork}(\{B_i \mid \llbracket C_i \rrbracket = \text{true}\}) & \text{if } \exists i. \llbracket C_i \rrbracket = \text{true} \\
\text{error} & \text{otherwise}
\end{cases}
$$

**类型约束**:

$$
\frac{\Gamma \vdash C_i : \text{Bool} \quad \Gamma \vdash B_i : \text{Activity}}{\Gamma \vdash \text{MultiChoice}(\{(C_i, B_i)\}) : \text{ParallelActivities}}
$$

### 2.3 形式化表示

#### 2.3.1 状态机表示

$$
\begin{aligned}
\text{State} &= \{ \text{Ready}, \text{Evaluating}, \text{Selecting}, \text{Forking}, \\n             &\quad \text{Executing}_k, \text{Joining}, \text{Completed} \} \\
\text{Transition} &= \{ \\
&\quad (\text{Ready}, \text{start}, \text{Evaluating}), \\
&\quad (\text{Evaluating}, \text{eval}(C_i), \text{Selecting}), \\
&\quad (\text{Selecting}, |\{C_i = \text{true}\}| = k, \text{Forking}), \\
&\quad (\text{Forking}, \text{spawn}_k, \text{Executing}_k), \\
&\quad (\text{Executing}_k, \text{all\_done}, \text{Joining}), \\
&\quad (\text{Joining}, \text{merge}, \text{Completed}) \\
&\}
\end{aligned}
$$

#### 2.3.2 流程代数表示 (CSP 风格)

$$
\text{MultiChoice} = \square_{i \in I} [C_i] \rightarrow B_i
$$

其中 $\square$ 是外部选择算子，$[C_i]$ 是守卫条件。

#### 2.3.3 Petri 网表示

```
         ┌──[C1]──→ (B1) ──┐
         │                 │
(Start) ─┼──[C2]──→ (B2) ──┼──> (End)
         │                 │
         └──[Cn]──→ (Bn) ──┘

Ci: 守卫条件（变迁）
Bi: 活动（位置）
```

---

## 3. BPMN 与标准规范

### 3.1 BPMN 表示

在 BPMN 2.0 中，多路选择使用**包容网关** (Inclusive Gateway) 表示：

```
         ◇──→ [Task A]
         │
(Token) ─┼──→ [Task B]
         │
         └──→ [Task C]

◇ = 包容网关 (Gateway with O or diamond)
分支条件在出边上标注
```

**XML 表示**:

```xml
<inclusiveGateway id="or_split" name="OR Split" />
<sequenceFlow id="flow1" sourceRef="or_split" targetRef="task_a">
  <conditionExpression xsi:type="tFormalExpression">${amount > 100}</conditionExpression>
</sequenceFlow>
<sequenceFlow id="flow2" sourceRef="or_split" targetRef="task_b">
  <conditionExpression xsi:type="tFormalExpression">${isVip == true}</conditionExpression>
</sequenceFlow>
```

### 3.2 UML 活动图

在 UML 中，多路选择使用**分叉节点**配合守卫条件：

```
         ┌────> [Activity A]  {amount > 100}
         │
[Node] ──┼────> [Activity B]  {isVip}
         │
         └────> [Activity C]  {needsReview}
```

### 3.3 WfMC 标准

工作流管理联盟 (WfMC) 将多路选择定义为：

> "一个点，在此工作流的一个或多个分支根据条件被选择。"

**关键属性**:

- **Split Type**: OR
- **Join Type**: 需要 OR-Join 或 Discriminator 合并

---

## 4. 进程代数形式化

### 4.1 CCS 表示

**Calculus of Communicing Systems (CCS)**:

$$
\text{OR\_Split} = \sum_{i=1}^{n} c_i.B_i
$$

**并行执行**:

$$
B_1 | B_2 | ... | B_k \quad \text{(其中 } C_1, ..., C_k \text{ 为真)}
$$

### 4.2 CSP 表示

**Communicating Sequential Processes (CSP)**:

```
OR_Split = [] i:indices @ condition(i) & Branch(i)

Branch(i) = execute(i) -> SKIP

-- 并行组合所有激活的分支
Parallel = || i:Activated @ Branch(i)
```

### 4.3 π-演算表示

**Pi-Calculus**:

$$
\nu \bar{c}.(\text{OR} | \prod_{i=1}^{n} !c_i(\bar{x}).B_i)
$$

其中通道 $c_i$ 携带守卫条件的计算结果。

---

## 5. Rust 实现

### 5.1 基础实现

```rust
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use tokio::sync::Mutex;

/// 多路选择执行器
pub struct MultiChoice<T, R> {
    branches: Vec<Branch<T, R>>,
}

pub struct Branch<T, R> {
    condition: Box<dyn Fn(&T) -> bool + Send + Sync>,
    action: Box<dyn Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync>,
    name: String,
}

impl<T: Clone + Send + 'static, R: Send + 'static> MultiChoice<T, R> {
    pub fn new() -> Self {
        Self { branches: Vec::new() }
    }

    pub fn add_branch<F, Fut>(
        &mut self,
        name: impl Into<String>,
        condition: impl Fn(&T) -> bool + Send + Sync + 'static,
        action: F,
    ) where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = R> + Send + 'static,
    {
        self.branches.push(Branch {
            name: name.into(),
            condition: Box::new(condition),
            action: Box::new(move |t| Box::pin(action(t))),
        });
    }

    /// 执行多路选择，返回所有满足条件的分支结果
    pub async fn execute(&self, input: T) -> MultiChoiceResult<R> {
        let mut futures = Vec::new();
        let mut activated = Vec::new();

        // 评估条件，收集激活的分支
        for (idx, branch) in self.branches.iter().enumerate() {
            if (branch.condition)(&input) {
                let future = (branch.action)(input.clone());
                futures.push(future);
                activated.push(idx);
            }
        }

        // 并行执行
        let results = futures::future::join_all(futures).await;

        MultiChoiceResult {
            activated_branches: activated,
            results,
        }
    }
}

pub struct MultiChoiceResult<R> {
    pub activated_branches: Vec<usize>,
    pub results: Vec<R>,
}
```

### 5.2 带错误处理的高级实现

```rust
use std::collections::HashMap;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MultiChoiceError {
    #[error("No branch activated")]
    NoBranchActivated,
    #[error("Branch {0} failed: {1}")]
    BranchFailed(usize, String),
    #[error("All branches failed")]
    AllFailed,
}

/// 容错多路选择
pub struct ResilientMultiChoice<T, R> {
    branches: Vec<ResilientBranch<T, R>>,
    require_at_least_one: bool,
    continue_on_error: bool,
}

pub struct ResilientBranch<T, R> {
    name: String,
    condition: Box<dyn Fn(&T) -> bool + Send + Sync>,
    action: Box<dyn Fn(T) -> Pin<Box<dyn Future<Output = Result<R, String>> + Send>> + Send + Sync>,
    retry_count: u32,
}

impl<T: Clone + Send + 'static, R: Send + 'static> ResilientMultiChoice<T, R> {
    pub async fn execute(&self, input: T) -> Result<ResilientResult<R>, MultiChoiceError> {
        let mut tasks = Vec::new();

        for (idx, branch) in self.branches.iter().enumerate() {
            if (branch.condition)(&input) {
                let input_clone = input.clone();
                let branch_ref = Arc::new(branch);

                let handle = tokio::spawn(async move {
                    let mut last_error = None;

                    for attempt in 0..=branch_ref.retry_count {
                        match (branch_ref.action)(input_clone.clone()).await {
                            Ok(result) => return Ok((idx, result)),
                            Err(e) => {
                                last_error = Some(e);
                                if attempt < branch_ref.retry_count {
                                    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
                                }
                            }
                        }
                    }

                    Err((idx, last_error.unwrap_or_else(|| "Unknown error".to_string())))
                });

                tasks.push(handle);
            }
        }

        if tasks.is_empty() && self.require_at_least_one {
            return Err(MultiChoiceError::NoBranchActivated);
        }

        // 收集结果
        let mut successes = Vec::new();
        let mut failures = Vec::new();

        for task in tasks {
            match task.await {
                Ok(Ok((idx, result))) => successes.push((idx, result)),
                Ok(Err((idx, error))) => {
                    if !self.continue_on_error {
                        return Err(MultiChoiceError::BranchFailed(idx, error));
                    }
                    failures.push((idx, error));
                }
                Err(_) => failures.push((0, "Task panicked".to_string())),
            }
        }

        if successes.is_empty() {
            return Err(MultiChoiceError::AllFailed);
        }

        Ok(ResilientResult { successes, failures })
    }
}

pub struct ResilientResult<R> {
    pub successes: Vec<(usize, R)>,
    pub failures: Vec<(usize, String)>,
}
```

### 5.3 订单处理完整示例

```rust
#[derive(Clone, Debug)]
struct Order {
    id: String,
    amount: f64,
    is_vip: bool,
    needs_gift_wrap: bool,
    is_international: bool,
    has_promo_code: bool,
}

#[derive(Debug)]
struct ProcessedOrder {
    order_id: String,
    applied_discounts: Vec<String>,
    final_amount: f64,
    extras: Vec<String>,
}

async fn process_order_with_multichoice(order: Order) -> ProcessedOrder {
    let mut processor = MultiChoice::<Order, OrderModification>::new();

    // VIP 折扣分支
    processor.add_branch(
        "vip_discount",
        |o| o.is_vip,
        |mut o| async move {
            o.amount *= 0.9;
            OrderModification {
                order: o,
                description: "VIP 9折优惠".to_string(),
            }
        },
    );

    // 促销码分支
    processor.add_branch(
        "promo_discount",
        |o| o.has_promo_code,
        |mut o| async move {
            o.amount *= 0.95;
            OrderModification {
                order: o,
                description: "促销码95折".to_string(),
            }
        },
    );

    // 礼品包装分支
    processor.add_branch(
        "gift_wrap",
        |o| o.needs_gift_wrap,
        |o| async move {
            OrderModification {
                order: o,
                description: "添加礼品包装".to_string(),
            }
        },
    );

    // 国际运费分支
    processor.add_branch(
        "international_shipping",
        |o| o.is_international,
        |mut o| async move {
            o.amount += 20.0;
            OrderModification {
                order: o,
                description: "国际运费$20".to_string(),
            }
        },
    );

    let result = processor.execute(order).await;

    // 合并结果
    let mut final_order = result.results.first().unwrap().order.clone();
    let mut descriptions: Vec<String> = result.results.iter()
        .map(|r| r.description.clone())
        .collect();

    // 去重并按最新状态更新
    for modification in &result.results[1..] {
        final_order = modification.order.clone();
    }

    ProcessedOrder {
        order_id: final_order.id,
        applied_discounts: descriptions.iter()
            .filter(|d| d.contains("折") || d.contains("优惠"))
            .cloned()
            .collect(),
        final_amount: final_order.amount,
        extras: descriptions.iter()
            .filter(|d| !d.contains("折") && !d.contains("优惠"))
            .cloned()
            .collect(),
    }
}

#[derive(Clone)]
struct OrderModification {
    order: Order,
    description: String,
}
```

---

## 6. 正确性证明

### 6.1 活性 (Liveness)

**定理**: 若至少一个守卫条件为真，则多路选择最终会完成。

**证明**:

设多路选择有分支 $\{(C_i, B_i)\}_{i=1}^n$。

**前提**: $\exists j. C_j = \text{true}$

**步骤**:

1. 评估所有 $C_i$ 需要有限时间（假设条件评估终止）
2. 设激活集合 $A = \{i \mid C_i = \text{true}\}$
3. 每个 $B_i$ ($i \in A$) 并行执行
4. 若每个 $B_i$ 终止，则 `join_all` 终止
5. 因此多路选择终止

**结论**: 多路选择满足活性。

### 6.2 安全性 (Safety)

**定理**: 只有守卫条件为真的分支会被执行。

**证明**:

由执行语义定义:

$$
\text{Activated} = \{B_i \mid C_i = \text{true}\}
$$

执行器只创建 $\text{Activated}$ 中分支的任务，因此仅条件为真的分支被执行。

### 6.3 正确性条件

**完备性**: 所有条件为真的分支都被执行。

**可靠性**: 只有条件为真的分支被执行。

**一致性**: 结果与分支执行顺序无关。

---

## 7. 与其他模式的关系

### 7.1 模式层次

```
Parallel Split (AND-Split)
         │
         ├── Multi Choice (OR-Split) ← 本文模式
         │         │
         │         ├── Exclusive Choice (XOR-Split)
         │         │
         │         └── Discriminator
         │
         └── Deferred Choice
```

### 7.2 形式化关系

$$
\text{ExclusiveChoice} \subseteq \text{MultiChoice} \subseteq \text{ParallelSplit}
$$

**排他选择是多路选择的特例**:

$$
\text{ExclusiveChoice}(C, B_1, ..., B_n) = \text{MultiChoice}(\{(C_i, B_i)\})
$$

其中 $C_i$ 互斥：$\forall i \neq j. \neg(C_i \land C_j)$

### 7.3 与合并模式的配合

| 分割模式 | 推荐合并模式 | 说明 |
|----------|--------------|------|
| Multi-Choice | OR-Join | 等待所有激活的分支 |
| Multi-Choice | Discriminator | 等待第一个完成 |
| Multi-Choice | N-out-of-M | 等待N个完成 |

---

## 8. 应用场景与案例

### 8.1 电商订单处理

**场景**: 根据订单属性应用多个处理规则

```rust
rules:
  - 金额>1000 → 需要经理审批
  - 是VIP → 优先处理
  - 有促销码 → 应用折扣
  - 国际订单 → 添加关税计算
```

**实现**: 上述规则可以独立应用，使用多路选择并行执行。

### 8.2 数据ETL管道

**场景**: 对同一数据集应用多个转换

```rust
processors:
  - 数据清洗
  - 格式验证
  - 敏感信息检测
  - 统计分析
```

**优势**: 并行处理提高效率。

### 8.3 多租户通知系统

**场景**: 根据用户偏好发送多渠道通知

```rust
channels:
  - email_enabled → 发送邮件
  - sms_enabled → 发送短信
  - push_enabled → 推送通知
  - webhook_enabled → 调用Webhook
```

---

## 9. 变体与扩展

### 9.1 加权多路选择

引入概率权重：

```rust
struct WeightedBranch<T, R> {
    weight: f64,
    condition: Box<dyn Fn(&T) -> bool>,
    action: Box<dyn Fn(T) -> R>,
}
```

### 9.2 动态多路选择

守卫条件可在运行时动态添加/移除：

```rust
impl<T, R> DynamicMultiChoice<T, R> {
    pub fn add_branch_runtime(&mut self, branch: Branch<T, R>);
    pub fn remove_branch(&mut self, name: &str);
}
```

### 9.3 嵌套多路选择

分支本身可以是多路选择：

```
OR-Split
  ├── AND-Split
  │     ├── Task A
  │     └── Task B
  └── OR-Split
        ├── Task C
        └── Task D
```

---

## 10. 总结

多路选择模式提供了灵活的条件分支机制，允许根据运行时条件动态选择多个执行路径。其核心优势包括：

1. **灵活性**: 不同于排他选择的限制
2. **并行性**: 激活的分支可并发执行
3. **可扩展性**: 易于添加新的条件和分支
4. **形式化**: 有明确的数学语义

在 Rust 中实现时，利用其所有权和并发特性，可以构建类型安全、高性能的多路选择执行器。

---

## 参考文献

1. van der Aalst, W.M.P., et al. (2003). "Workflow Patterns". Distributed and Parallel Databases.
2. Russell, N., et al. (2006). "Workflow Control-Flow Patterns: A Revised View".
3. Hoare, C.A.R. (1978). "Communicating Sequential Processes".
4. Milner, R. (1989). "Communication and Concurrency".
5. Object Management Group. (2011). "BPMN 2.0 Specification".

---

**模式编号**: WP-06
**难度**: 🟡 中级
**相关模式**: Exclusive Choice, Parallel Split, Discriminator
**最后更新**: 2026-03-07
