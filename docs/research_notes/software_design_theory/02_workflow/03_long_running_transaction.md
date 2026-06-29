# 长事务模式

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L4-L6 (分析/评价/创造)
> **创建日期**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: 🔄 持续推进中（骨架已建立，形式化内容与反例待补全）
> **概念族**: 软件设计 / 工作流模式 / 长事务 / Saga
> **权威来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/) | [Tokio Tutorial](https://tokio.rs/tokio/tutorial) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

---

## 📑 目录

- [长事务模式](#长事务模式)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
  - [二、形式化定义](#二形式化定义)
    - [Def 3.1 长事务](#def-31-长事务)
    - [Axiom 3.1 局部提交可见性](#axiom-31-局部提交可见性)
    - [Theorem 3.1 业务一致性](#theorem-31-业务一致性)
  - [三、Rust 实现](#三rust-实现)
  - [四、反例与边界](#四反例与边界)
    - [反例 1：未持久化状态导致重复执行](#反例-1未持久化状态导致重复执行)
    - [反例 2：循环依赖](#反例-2循环依赖)
  - [五、与其他概念的关系](#五与其他概念的关系)
  - [六、权威来源索引](#六权威来源索引)

---

## 一、核心概念

长事务（Long-Running Transaction，LRT）跨越多个服务调用、数据库或时间窗口，无法使用传统数据库事务的 ACID 保证。其一致性通过**业务级协调**实现：

- **事务边界**：由业务流程定义，而非数据库会话。
- **局部提交**：每个步骤独立提交，释放资源。
- **最终一致性**：通过补偿、重试或状态机推进，最终达到一致状态。
- **持久化状态**：长事务的状态必须持久化，以支持崩溃恢复。

---

## 二、形式化定义

### Def 3.1 长事务

一个长事务是四元组

```text
LRT := (W, R, P, C)
```

其中：

- `W`：工作项集合，每个工作项是一个可独立提交的步骤。
- `R ⊆ W × W`：工作项之间的依赖/偏序关系。
- `P`：持久化状态存储。
- `C`：协调器，负责按 `R` 调度工作项并在失败时触发补偿。

### Axiom 3.1 局部提交可见性

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)

每个工作项 `w ∈ W` 完成后，其效果对外部可见；全局一致性由协调器 `C` 保证，而非数据库隔离级别：

```text
∀ w ∈ W, committed(w) → observable(w)
```

### Theorem 3.1 业务一致性

> **来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)

若协调器 `C` 满足：

1. 仅当所有前置工作项完成时才调度后续工作项；
2. 任意工作项失败时，按依赖逆序触发补偿；

则长事务在终止时要么全部工作项成功，要么所有已提交工作项被补偿，系统处于业务一致状态。

---

## 三、Rust 实现

```rust
#[derive(Clone, Debug)]
struct WorkItem {
    id: String,
    action: fn() -> Result<(), Error>,
    compensation: fn() -> Result<(), Error>,
    dependencies: Vec<String>,
}

struct LongRunningTransaction {
    items: Vec<WorkItem>,
    state_store: dyn StateStore, // 待实现
}

impl LongRunningTransaction {
    async fn execute(&mut self) -> Result<(), Error> {
        // 按依赖拓扑排序后执行
        // 失败时触发补偿
        todo!("实现拓扑执行与补偿逻辑")
    }
}
```

> **待补全**：持久化状态存储接口、恢复逻辑、超时与重试策略。

---

## 四、反例与边界

### 反例 1：未持久化状态导致重复执行

若协调器崩溃后无法恢复已执行的工作项，重启后可能重复执行，违反业务一致性。

> **待补全**：给出持久化状态缺失的示例与幂等性修复方案。

### 反例 2：循环依赖

`R` 中出现循环依赖时，拓扑排序无法完成，长事务无法启动。

---

## 五、与其他概念的关系

- **Saga 模式**：长事务的常用实现方式。
- **补偿链**：长事务失败时的撤销机制。
- **工作流状态机**：长事务可用状态机建模，状态即持久化状态。
- **Outbox 模式**：保证长事务事件至少一次投递。

---

## 六、权威来源索引

> **来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)
> **来源**: [Tokio Tutorial](https://tokio.rs/tokio/tutorial)
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
