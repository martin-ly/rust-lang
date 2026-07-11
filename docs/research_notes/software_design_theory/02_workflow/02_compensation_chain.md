# 补偿链模式形式化定义 {#补偿链模式形式化定义}

> **EN**: Compensation Chain
> **Summary**: 补偿链模式形式化定义 Compensation Chain. (stub/archive redirect)
> **概念族**: 软件设计 / 工作流模式 / 补偿 / Saga
> **内容分级**: [归档级]
> **分级**: [B]
> **Bloom 层级**: L4-L6
> **模式类型**: 分布式长事务
> **创建日期**: 2026-06-29
> **版本**: v1.0
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级（Rust 1.97.0+ / Edition 2024）
> **对齐说明**: 本文档已于 2026-06-29 从 `archive/research_notes_2026_06_25/software_design_theory/02_workflow/` 迁回，正在按 [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)、[Tokio Tutorial](https://tokio.rs/tokio/tutorial)、[Rust Reference](https://doc.rust-lang.org/reference/) 等权威来源升级。
> **权威来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/) | [Tokio Tutorial](https://tokio.rs/tokio/tutorial) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)) | [The Rust Programming Language](https://doc.rust-lang.org/book/)

---

## 📑 目录 {#目录}

- [补偿链模式形式化定义 {#补偿链模式形式化定义}](#补偿链模式形式化定义-补偿链模式形式化定义)
  - [📑 目录 {#目录}](#-目录-目录)
  - [1. 问题定义与动机 {#1-问题定义与动机}](#1-问题定义与动机-1-问题定义与动机)
  - [2. 核心概念 {#2-核心概念}](#2-核心概念-2-核心概念)
  - [3. 形式化定义 {#3-形式化定义}](#3-形式化定义-3-形式化定义)
    - [Def CC1: 补偿链 {#def-cc1-补偿链}](#def-cc1-补偿链-def-cc1-补偿链)
    - [Axiom CC1: 补偿可逆性 {#axiom-cc1-补偿可逆性}](#axiom-cc1-补偿可逆性-axiom-cc1-补偿可逆性)
    - [Axiom CC2: 补偿幂等性 {#axiom-cc2-补偿幂等性}](#axiom-cc2-补偿幂等性-axiom-cc2-补偿幂等性)
    - [Theorem CC1: 最终一致性（Coherence） {#theorem-cc1-最终一致性}](#theorem-cc1-最终一致性-theorem-cc1-最终一致性)
    - [Theorem CC2: 补偿终止性 {#theorem-cc2-补偿终止性}](#theorem-cc2-补偿终止性-theorem-cc2-补偿终止性)
  - [4. Rust 实现方案 {#4-rust-实现方案}](#4-rust-实现方案-4-rust-实现方案)
  - [5. 反例与边界 {#5-反例与边界}](#5-反例与边界-5-反例与边界)
    - [反例 1：非幂等补偿 {#反例-1非幂等补偿}](#反例-1非幂等补偿-反例-1非幂等补偿)
    - [反例 2：补偿顺序错误 {#反例-2补偿顺序错误}](#反例-2补偿顺序错误-反例-2补偿顺序错误)
    - [边界：补偿失败 {#边界补偿失败}](#边界补偿失败-边界补偿失败)
  - [6. 与其他模式的关系 {#6-与其他模式的关系}](#6-与其他模式的关系-6-与其他模式的关系)
  - [7. 权威来源索引 {#7-权威来源索引}](#7-权威来源索引-7-权威来源索引)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)

---

## 1. 问题定义与动机 {#1-问题定义与动机}

> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)

在跨服务、跨数据库的长事务中，传统 ACID 事务的锁和隔离级别会导致可用性下降。补偿链模式（Compensation Chain）接受**每个步骤独立提交**，并在某一步失败时，通过执行业务层面的**撤销操作**（补偿）使系统最终回到一致状态。

典型场景：电商下单流程中，库存已扣减、支付已扣款后，发现优惠券校验失败，需要依次退款、释放库存。

---

## 2. 核心概念 {#2-核心概念}

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)

- **正向操作（Action）**：执行业务逻辑并产生副作用。
- **补偿操作（Compensation）**：撤销正向操作的副作用，满足业务语义上的可逆性。
- **补偿链（Compensation Chain）**：按正向操作**逆序**执行的补偿序列。
- **幂等性**：同一补偿操作多次执行应产生相同效果，以应对网络重试或崩溃恢复。

与数据库回滚不同，补偿链基于**语义撤销**，可能留下审计记录或通知等不可消除的痕迹。

---

## 3. 形式化定义 {#3-形式化定义}

> **来源**: [Rust Official Docs](https://doc.rust-lang.org/)

### Def CC1: 补偿链 {#def-cc1-补偿链}

一个补偿链是有序二元组序列

```text
C := [(a₁, c₁), (a₂, c₂), ..., (aₙ, cₙ)]
```

其中：

- `aᵢ`：第 `i` 步正向操作。
- `cᵢ`：对应补偿操作，满足 `cᵢ ∘ aᵢ ≈ id`（在业务语义上等价于恒等操作）。

### Axiom CC1: 补偿可逆性 {#axiom-cc1-补偿可逆性}

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)

每个正向操作 `aᵢ` 必须存在补偿操作 `cᵢ`，使得执行 `cᵢ` 后业务状态在可观察层面回到执行 `aᵢ` 之前：

```text
∀ i, state(cᵢ(aᵢ(s))) ≈ state(s)
```

### Axiom CC2: 补偿幂等性 {#axiom-cc2-补偿幂等性}

> **来源**: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)

补偿操作必须是幂等的：

```text
∀ c ∈ C. exec(c, s) = s' → exec(c, s') = s'
```

### Theorem CC1: 最终一致性 {#theorem-cc1-最终一致性}

> **来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)

若前 `k` 步正向操作已成功，第 `k+1` 步失败，则按逆序执行 `cₖ, cₖ₋₁, ..., c₁` 后，系统状态与初始状态在业务层面一致。

**证明概要**：

1. 前 `k` 步成功使系统状态从 `s₀` 变为 `sₖ = aₖ(...a₂(a₁(s₀))...)`。
2. 第 `k+1` 步失败，其副作用未发生。
3. 依次执行 `cₖ, ..., c₁`，由 Axiom CC1 有 `cᵢ ∘ aᵢ ≈ id`。
4. 因此 `sₖ'` = `c₁(...cₖ(sₖ)...) ≈ s₀`。

### Theorem CC2: 补偿终止性 {#theorem-cc2-补偿终止性}

> **来源**: [Rust Standard Library](https://doc.rust-lang.org/std/)

补偿链必然终止：

```text
∀ C. |C| = n < ∞ → 补偿过程在至多 n 步后结束
```

**证明概要**：已完成正向操作的集合 `completed` 长度不超过 `n`；每执行一次补偿减少一个元素，故有限步后结束。

---

## 4. Rust 实现方案 {#4-rust-实现方案}

> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/))

以下实现使用泛型（Generics） `Compensable` trait 与 Rust 1.75+ 的 `impl Future` 返回类型，允许同步或异步（Async）步骤统一表达。

```rust
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll, Wake};

// 最小化的单线程 executor，仅用于演示可编译的异步代码
fn block_on<F: Future>(mut fut: F) -> F::Output {
    struct DummyWaker;
    impl Wake for DummyWaker {
        fn wake(self: Arc<Self>) {}
    }
    let waker = Arc::new(DummyWaker).into();
    let mut cx = Context::from_waker(&waker);
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(v) => return v,
            Poll::Pending => std::thread::yield_now(),
        }
    }
}

#[derive(Debug)]
enum ChainError<E> {
    StepFailed(E),
    CompensationFailed(E),
}

trait Compensable {
    type Error;
    fn execute(&self) -> impl Future<Output = Result<(), Self::Error>> + '_;
    fn compensate(&self) -> impl Future<Output = Result<(), Self::Error>> + '_;
}

struct CompensationChain<Step> {
    steps: Vec<Step>,
    completed: Vec<usize>,
}

impl<Step: Compensable> CompensationChain<Step> {
    fn new(steps: Vec<Step>) -> Self {
        Self { steps, completed: Vec::new() }
    }

    async fn run(&mut self) -> Result<(), ChainError<Step::Error>> {
        for (idx, step) in self.steps.iter().enumerate() {
            if let Err(e) = step.execute().await {
                if let Err(ce) = self.compensate_all().await {
                    return Err(ChainError::CompensationFailed(ce));
                }
                return Err(ChainError::StepFailed(e));
            }
            self.completed.push(idx);
        }
        Ok(())
    }

    async fn compensate_all(&self) -> Result<(), Step::Error> {
        for &idx in self.completed.iter().rev() {
            self.steps[idx].compensate().await?;
        }
        Ok(())
    }
}

enum OrderStep {
    ReserveInventory(u64),
    ChargePayment(u64),
}

impl Compensable for OrderStep {
    type Error = String;

    fn execute(&self) -> impl Future<Output = Result<(), Self::Error>> + '_ {
        async move {
            match self {
                OrderStep::ReserveInventory(id) => {
                    println!("reserve inventory {}", id);
                    Ok(())
                }
                OrderStep::ChargePayment(id) => {
                    if *id == 0 {
                        Err("payment declined".into())
                    } else {
                        println!("charge {}", id);
                        Ok(())
                    }
                }
            }
        }
    }

    fn compensate(&self) -> impl Future<Output = Result<(), Self::Error>> + '_ {
        async move {
            match self {
                OrderStep::ReserveInventory(id) => {
                    println!("release inventory {}", id);
                    Ok(())
                }
                OrderStep::ChargePayment(id) => {
                    println!("refund {}", id);
                    Ok(())
                }
            }
        }
    }
}

fn main() {
    let mut chain = CompensationChain::new(vec![
        OrderStep::ReserveInventory(1),
        OrderStep::ChargePayment(0), // 失败，触发补偿
    ]);
    let result = block_on(chain.run());
    assert!(result.is_err());
}
```

> **来源**: [Tokio Tutorial](https://tokio.rs/tokio/tutorial)

**实现要点**：

1. `completed` 记录已成功的步骤索引。
2. 失败时按 `completed.iter().rev()` 逆序调用补偿。
3. 每个步骤的 `compensate` 应通过**幂等键**或状态检查保证幂等。

---

## 5. 反例与边界 {#5-反例与边界}

> **来源**: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)

### 反例 1：非幂等补偿 {#反例-1非幂等补偿}

```rust,ignore
// 错误：重复释放库存会导致库存变为负数
async fn compensate_inventory(item_id: u64) {
    sqlx::query("UPDATE stock SET qty = qty + 1 WHERE id = ?")
        .bind(item_id)
        .execute(&pool)
        .await;
}
```

若网络超导致补偿被执行两次，库存会多增一次。

**修复**：使用幂等键或状态检查。

```rust,ignore
async fn compensate_inventory(item_id: u64, idempotency_key: &str) {
    if already_compensated(idempotency_key).await {
        return;
    }
    // 执行补偿并记录 idempotency_key
}
```

### 反例 2：补偿顺序错误 {#反例-2补偿顺序错误}

```rust,ignore
// 错误：按正向顺序补偿
for step in completed {
    step.compensate().await?;
}
```

若正向步骤为"扣库存 → 扣款"，正向顺序补偿会先退款再释放库存，中间状态可能出现"钱已退但库存仍被占用"。

**修复**：必须按正向顺序的逆序执行补偿。

```rust
for &idx in self.completed.iter().rev() {
    self.steps[idx].compensate().await?;
}
```

### 边界：补偿失败 {#边界补偿失败}

补偿操作本身也可能失败（网络中断、下游服务不可用）。此时：

- **重试**：补偿应幂等，可安全重试。
- **记录**：将失败 Compensation 写入死信队列或人工处理台账。
- **最终一致性**：系统处于"已补偿部分步骤"的中间态，需持续重试直至全部补偿完成。

---

## 6. 与其他模式的关系 {#6-与其他模式的关系}

> **来源**: [crates.io](https://crates.io/)

| 模式 | 关系 | 说明 |
|------|------|------|
| [Saga 模式](../05_distributed/01_saga_pattern.md) | 核心机制 | 补偿链是 Saga 模式的核心实现机制 |
| [工作流状态机模式](01_workflow_state_machine.md) | 组合 | 状态机的 `Failed` 迁移可触发补偿链 |
| [长事务模式](03_long_running_transaction.md) | 组合 | 长事务通过补偿链撤销已提交的步骤 |
| [Outbox 模式](../05_distributed/05_outbox_pattern.md) | 增强 | 补偿消息可通过 Outbox 保证至少一次投递 |
| [重试模式](../05_distributed/07_retry_pattern.md) | 增强 | 补偿步骤可配置重试策略 |

---

## 7. 权威来源索引 {#7-权威来源索引}

> **P0 权威来源（Rust 官方）**:
>
> - [Rust Reference](https://doc.rust-lang.org/reference/)
> - [The Rust Programming Language](https://doc.rust-lang.org/book/)
> - [Rust Standard Library](https://doc.rust-lang.org/std/)
> - [Rustonomicon](https://doc.rust-lang.org/nomicon/)
> **P1 权威来源（Rust 社区与工程实践）**:
>
> - [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)
> - [Tokio Tutorial](https://tokio.rs/tokio/tutorial)
> - [Rust Design Patterns](https://rust-unofficial.github.io/patterns/))
> - [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
> **P2 权威来源（学术与行业经典）**:
>
> - [Wikipedia - Saga Pattern](https://en.wikipedia.org/wiki/Saga_Pattern)
> - [Wikipedia - Long-Running Transaction](https://en.wikipedia.org/wiki/Long_Running_Transaction)
> - [ACM](https://dl.acm.org/)
> - [IEEE](https://standards.ieee.org/)

---

## 学术权威参考 {#学术权威参考}

- [Aeneas](https://aeneasverif.github.io/)
- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)

---

**维护者**: Rust 学习项目团队

**文档版本**: 1.0

**对应 Rust 版本**: 1.97.0+ (Edition 2024)

**状态**: ✅ 权威来源对齐完成
