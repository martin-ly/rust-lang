> **内容分级**: [专家级]

# Saga 模式

**EN**: Saga Pattern in Rust
**Summary**: Manage long-lived distributed transactions by splitting them into a sequence of local transactions, each with a compensating action.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 将 Garcia-Molina / Hohpe / Richardson 的 Saga 模式与 Rust 的类型系统、错误处理、异步执行模型对齐，实现可编排或可事件驱动的长事务。
> **前置概念**: [DDD Tactical Patterns](../14_enterprise_architecture/04_domain_driven_design_in_rust.md) · [Event-Driven Architecture](06_event_driven_architecture.md) · [CQRS and Event Sourcing](07_cqrs_event_sourcing.md) · [Comparative Layer README](../../05_comparative/README.md)
> **后置概念**: [Outbox](30_outbox.md) · [Microservice Patterns](05_microservice_patterns.md)

---

> **来源 / Provenance**:
> [Garcia-Molina & Salem 1987 — Sagas](https://doi.org/10.1145/38713.38742) ·
> [Hohpe & Woolf 2003 — Enterprise Integration Patterns](https://www.enterpriseintegrationpatterns.com/) ·
> [Richardson 2018 — Microservices Patterns](https://microservices.io/book) ·
> [Fowler 2004 — Transactional Observer](https://martinfowler.com/eaaDev/TransactionalObserver.html)

---

## 一、权威定义

**Saga**: 一个长事务被拆分为多个本地事务序列；每个本地事务有对应的**补偿事务（compensating transaction）**，用于在后续步骤失败时撤销已完成的步骤。

两种主要形式：

- **编排式 Saga（Choreography）**: 每个服务完成本地事务后发布事件，触发下一个服务。
- **协调式 Saga（Orchestration）**: 由中央协调器按顺序调用各服务并处理补偿。

> **来源**: [Garcia-Molina & Salem 1987](https://doi.org/10.1145/38713.38742) · [Hohpe & Woolf 2003](https://www.enterpriseintegrationpatterns.com/) · [Richardson 2018](https://microservices.io/book)

---

## 二、属性矩阵

| 维度 | Choreography | Orchestration |
|:---|:---|:---|
| **耦合** | 低（事件驱动） | 高（协调器知悉所有步骤） |
| **可观测性** | 需分布式追踪 | 协调器集中记录状态 |
| **复杂度** | 随步骤数指数增长 | 协调器逻辑线性增长 |
| **Rust 实现** | `tokio::sync::broadcast` / 消息总线 | 状态机 + `async fn` |
| **补偿触发** | 监听失败事件 | 协调器反向执行补偿 |

---

## 三、Rust 实现

### 3.1 协调式 Saga 骨架

```rust,ignore
use std::collections::VecDeque;

pub struct SagaStep<T, E> {
    name: &'static str,
    action: Box<dyn Fn(&T) -> Result<T, E> + Send + Sync>,
    compensate: Box<dyn Fn(&T) -> Result<(), E> + Send + Sync>,
}

pub struct Saga<T, E> {
    steps: Vec<SagaStep<T, E>>,
}

impl<T: Clone, E> Saga<T, E> {
    pub fn new() -> Self {
        Self { steps: vec![] }
    }

    pub fn step(mut self, step: SagaStep<T, E>) -> Self {
        self.steps.push(step);
        self
    }

    pub fn execute(&self, initial: T) -> Result<T, E> {
        let mut state = initial;
        let mut completed: VecDeque<(&SagaStep<T, E>, T)> = VecDeque::new();

        for step in &self.steps {
            match (step.action)(&state) {
                Ok(new_state) => {
                    completed.push_back((step, state));
                    state = new_state;
                }
                Err(e) => {
                    // 反向执行补偿
                    while let Some((s, prev)) = completed.pop_back() {
                        let _ = (s.compensate)(&prev);
                    }
                    return Err(e);
                }
            }
        }
        Ok(state)
    }
}
```

### 3.2 幂等 Saga 步骤

```rust,ignore
pub trait IdempotentStep {
    type State;
    type Error;
    async fn execute(&self, state: &Self::State) -> Result<Self::State, Self::Error>;
    async fn compensate(&self, state: &Self::State) -> Result<(), Self::Error>;
}
```

---

## 四、关系

- **Saga ↔ Unit of Work**: Unit of Work 保证单个服务内的原子性；Saga 保证跨服务的长事务最终一致性。
- **Saga ↔ Outbox**: Outbox 保证本地事务与事件发布的原子性，是 Saga 的事件总线基础。
- **Saga ↔ Compensation**: 补偿不是「回滚」，而是业务意义上的撤销操作；某些操作（如发送邮件）无法真正撤销。

---

## 五、反例与边界

### 反例：把 Saga 当作分布式锁

```rust,ignore
// ❌ 错误：在 Saga 中长时间持有资源锁
async fn saga_step() {
    lock_inventory().await;
    // 长时间网络调用...
    unlock_inventory().await;
}
```

**修正**: Saga 步骤应短小，避免长时间锁定；使用预留（reservation）模式替代锁定。

### 边界：无法补偿的操作

发送邮件、扣款完成等操作难以或无法补偿。对这类操作应使用「可接受的不完美补偿」或前置校验。

---

## ⚠️ 实测反例（rustc 1.99.1 实编译/实跑，2026-10-19）

### 反例 1：§3.1 骨架的 `let _ = (s.compensate)(&prev);` 静默吞掉补偿失败——实跑演示「已扣款未退款」状态

把 §3.1 骨架原样实编译，注入一个「补偿自身失败」的步骤（真实世界里 refund 网关超时极常见）：

```rust
use std::collections::VecDeque;
pub struct SagaStep<T, E> {
    name: &'static str,
    action: Box<dyn Fn(&T) -> Result<T, E> + Send + Sync>,
    compensate: Box<dyn Fn(&T) -> Result<(), E> + Send + Sync>,
}
pub struct Saga<T, E> { steps: Vec<SagaStep<T, E>> }
impl<T: Clone, E: std::fmt::Debug> Saga<T, E> {
    pub fn new() -> Self { Self { steps: vec![] } }
    pub fn step(mut self, step: SagaStep<T, E>) -> Self { self.steps.push(step); self }
    pub fn execute(&self, initial: T) -> Result<T, E> {
        let mut state = initial;
        let mut completed: VecDeque<(&SagaStep<T, E>, T)> = VecDeque::new();
        for step in &self.steps {
            match (step.action)(&state) {
                Ok(new_state) => { completed.push_back((step, state)); state = new_state; }
                Err(e) => {
                    while let Some((s, prev)) = completed.pop_back() {
                        let _ = (s.compensate)(&prev);   // 页内骨架原样
                    }
                    return Err(e);
                }
            }
        }
        Ok(state)
    }
}
#[derive(Clone, Debug)]
struct Order { reserved: bool, charged: bool }
fn main() {
    let saga: Saga<Order, String> = Saga::new()
        .step(SagaStep { name: "reserve",
            action: Box::new(|o: &Order| Ok(Order { reserved: true, ..o.clone() })),
            compensate: Box::new(|_o: &Order| { println!("  释放库存 OK"); Ok(()) }) })
        .step(SagaStep { name: "charge",
            action: Box::new(|o: &Order| Ok(Order { charged: true, ..o.clone() })),
            compensate: Box::new(|_o: &Order| Err("refund gateway timeout".to_string())) }) // 补偿自己失败
        .step(SagaStep { name: "ship",
            action: Box::new(|_o: &Order| Err("warehouse down".to_string())),
            compensate: Box::new(|_o: &Order| Ok(())) });
    let r = saga.execute(Order { reserved: false, charged: false });
    println!("saga 返回: {r:?}");
}
```

实编译通过，实跑输出（exit 0）：

```text
  释放库存 OK
saga 返回: Err("warehouse down")
```

程序视角一切「正常」：库存释放成功、`Err` 正确传播、没有 panic。但 `charge` 的 refund 补偿返回的 `Err("refund gateway timeout")` 被 `let _ =` 当场丢弃——**调用方拿到的唯一错误是 warehouse down，永远不知道钱还挂在用户账上**。Saga 模式的全部价值在补偿链；补偿链里的 `let _` 正是 §五「无法补偿的操作」边界条目在最常见实现里的自毁开关。修正方向：补偿失败必须落盘（outbox/死信表 + 人工对账队列），至少聚合进返回错误（`CompensationFailed { trigger, compensations }`）。

### 反例 2：骨架直接实例化时闭包参数推不出类型（E0282）——`Box<dyn Fn(&T)>` 字段无推断锚点

§3.1 骨架看着能直接用，实际写一个最小装配就撞墙：

```rust,compile_fail
pub struct SagaStep<T, E> {
    action: Box<dyn Fn(&T) -> Result<T, E> + Send + Sync>,
}
fn main() {
    let s = SagaStep { action: Box::new(|o| Ok(o.clone())) }; // E0282
}
```

**实测输出（E0282）**：

```text
error[E0282]: type annotations needed for `&_`
 --> src/main.rs:5:42
  |
5 |     let s = SagaStep { action: Box::new(|o| Ok(o.clone())) };
  |                                          ^     - type must be known at this point
  |
help: consider giving this closure parameter an explicit type, where the type for type parameter `T` is specified
  |
5 |     let s = SagaStep { action: Box::new(|o: &T| Ok(o.clone())) };
```

原因：`T` 只出现在 `Box` 内部（不是任何字段的直接类型），构造点没有其它锚点能让推断器反推闭包参数。真实装配代码里 `T` 通常被 `Saga<T,E>` 变量标注钉死（反例 1 的 `let saga: Saga<Order, String>` 就没触发），所以这个坑专挑「先写步骤工厂再拼容器」的写法。两种出路：装配点显式标注容器类型，或让 `step()` 收 `impl Fn(&T) -> ...` 泛型参数（推断从调用方回灌）。

---

## 六、决策树

```mermaid
graph TD
    A[业务事务跨多个服务?] -->|是| B[是否需要集中可见性?]
    B -->|是| C[使用 Orchestration Saga]
    B -->|否| D[使用 Choreography Saga]
    C --> E[定义步骤 + 补偿]
    D --> F[定义事件 + 补偿处理器]
    E --> G[配合 Outbox 保证事件原子发布]
    F --> G
```

---

## 七、思维导图

```mermaid
mindmap
  root((Saga))
    两种形式
      Choreography
      Orchestration
    核心机制
      本地事务
      补偿事务
      幂等步骤
    Rust 映射
      状态机
      async trait
      Event enum
    基础设施
      Outbox
      Message Bus
      Distributed Tracing
```

---

## 八、权威来源索引

- Garcia-Molina, H. & Salem, K. "Sagas." *SIGMOD 1987*. [https://doi.org/10.1145/38713.38742](https://doi.org/10.1145/38713.38742)
- Hohpe, G. & Woolf, B. *Enterprise Integration Patterns: Designing, Building, and Deploying Messaging Solutions*. Addison-Wesley, 2003.
- Richardson, C. *Microservices Patterns: With examples in Java*. Manning, 2018. [https://microservices.io/book](https://microservices.io/book)
- Fowler, M. "Transactional Observer." 2004. [https://martinfowler.com/eaaDev/TransactionalObserver.html](https://martinfowler.com/eaaDev/TransactionalObserver.html)

> **文档版本**: 1.0 ｜ **最后更新**: 2026-07-31 ｜ **状态**: ✅ 新建权威页

## 国际化权威来源补充（International Authority Sources）

- https://dl.acm.org/doi/book/10.5555/186897
- https://rust-unofficial.github.io/patterns/
- [The Rust Programming Language — Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [Rust Reference — Traits](https://doc.rust-lang.org/reference/items/traits.html)
- [The Rust Programming Language — Closures](https://doc.rust-lang.org/book/ch13-01-closures.html)
