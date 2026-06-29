# 补偿链模式

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L4-L6 (分析/评价/创造)
> **创建日期**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: 🔄 持续推进中（骨架已建立，形式化内容与反例待补全）
> **概念族**: 软件设计 / 工作流模式 / 补偿 / Saga
> **权威来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/) | [Tokio Tutorial](https://tokio.rs/tokio/tutorial) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

---

## 📑 目录

- [补偿链模式](#补偿链模式)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
  - [二、形式化定义](#二形式化定义)
    - [Def 2.1 补偿链](#def-21-补偿链)
    - [Axiom 2.1 补偿可逆性](#axiom-21-补偿可逆性)
    - [Theorem 2.1 最终一致性](#theorem-21-最终一致性)
  - [三、Rust 实现](#三rust-实现)
  - [四、反例与边界](#四反例与边界)
    - [反例 1：非幂等补偿](#反例-1非幂等补偿)
    - [反例 2：补偿顺序错误](#反例-2补偿顺序错误)
  - [五、与其他概念的关系](#五与其他概念的关系)
  - [六、权威来源索引](#六权威来源索引)

---

## 一、核心概念

补偿链模式用于处理分布式长事务：当某个步骤失败时，通过执行**补偿操作**撤销已完成的步骤，使系统最终恢复到一致状态。

- **正向操作（Action）**：执行业务逻辑并产生副作用。
- **补偿操作（Compensation）**：撤销正向操作的副作用。
- **补偿链（Compensation Chain）**：按正向操作逆序执行的补偿序列。

与数据库 ACID 事务不同，补偿链接受**语义撤销**而非物理回滚。

---

## 二、形式化定义

### Def 2.1 补偿链

一个补偿链是有序二元组序列

```text
C := [(a₁, c₁), (a₂, c₂), ..., (aₙ, cₙ)]
```

其中：

- `aᵢ`：第 `i` 步正向操作。
- `cᵢ`：对应补偿操作，满足 `cᵢ ∘ aᵢ ≈ id`（在业务语义上等价于恒等操作）。

### Axiom 2.1 补偿可逆性

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)

每个正向操作 `aᵢ` 必须存在补偿操作 `cᵢ`，使得执行 `cᵢ` 后业务状态在可观察层面回到执行 `aᵢ` 之前：

```text
∀ i, state(cᵢ(aᵢ(s))) ≈ state(s)
```

### Theorem 2.1 最终一致性

> **来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)

若前 `k` 步正向操作已成功，第 `k+1` 步失败，则按逆序执行 `cₖ, cₖ₋₁, ..., c₁` 后，系统状态与初始状态在业务层面一致。

---

## 三、Rust 实现

```rust
trait Compensable {
    type Error;
    async fn execute(&self) -> Result<(), Self::Error>;
    async fn compensate(&self) -> Result<(), Self::Error>;
}

struct Saga {
    steps: Vec<Box<dyn Compensable<Error = Box<dyn std::error::Error>>>>,
}

impl Saga {
    async fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut completed = Vec::new();
        for step in &self.steps {
            if let Err(e) = step.execute().await {
                for s in completed.iter().rev() {
                    s.compensate().await?;
                }
                return Err(e);
            }
            completed.push(step);
        }
        Ok(())
    }
}
```

> **待补全**：结合 Tokio 的异步补偿示例、幂等性保证、补偿失败处理。

---

## 四、反例与边界

### 反例 1：非幂等补偿

若补偿操作 `cᵢ` 执行两次导致状态偏离初始状态，则违反 Axiom 2.1。

> **待补全**：给出具体代码与修复方案（幂等键、状态检查）。

### 反例 2：补偿顺序错误

补偿必须按正向操作的**逆序**执行；顺序错误可能导致中间状态不一致。

---

## 五、与其他概念的关系

- **Saga 模式**：补偿链是 Saga 模式的核心实现机制。
- **工作流状态机**：补偿链可与状态机结合，定义失败状态与补偿迁移。
- **Outbox 模式**：补偿消息可通过 Outbox 保证至少一次投递。

---

## 六、权威来源索引

> **来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)
> **来源**: [Tokio Tutorial](https://tokio.rs/tokio/tutorial)
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
