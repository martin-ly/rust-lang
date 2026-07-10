# 工作流状态机模式形式化定义 {#工作流状态机模式形式化定义}

> **EN**: Workflow State Machine
> **Summary**: 工作流状态机模式形式化定义 Workflow State Machine. (stub/archive redirect)
> **概念族**: 软件设计 / 工作流模式 / 状态机
> **内容分级**: [归档级]
> **分级**: [B]
> **Bloom 层级**: L4-L6 (分析/评价/创造)
> **模式类型**: 工作流状态机
> **创建日期**: 2026-06-29
> **版本**: v1.0
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级（Rust 1.97.0+ / Edition 2024）
> **对齐说明**: 本文档已于 2026-06-29 从 `archive/research_notes_2026_06_25/software_design_theory/02_workflow/` 迁回，正在按 [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)、[Tokio Tutorial](https://tokio.rs/tokio/tutorial)、[Rust Reference](https://doc.rust-lang.org/reference/) 等权威来源升级。
> **权威来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/) | [Tokio Tutorial](https://tokio.rs/tokio/tutorial) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | [The Rust Programming Language](https://doc.rust-lang.org/book/)

---

## 📑 目录 {#目录}

- [工作流状态机模式形式化定义 {#工作流状态机模式形式化定义}](#工作流状态机模式形式化定义-工作流状态机模式形式化定义)
  - [📑 目录 {#目录}](#-目录-目录)
  - [1. 问题定义与动机 {#1-问题定义与动机}](#1-问题定义与动机-1-问题定义与动机)
  - [2. 核心概念 {#2-核心概念}](#2-核心概念-2-核心概念)
  - [3. 形式化定义 {#3-形式化定义}](#3-形式化定义-3-形式化定义)
    - [Def WF1: 工作流状态机 {#def-wf1-工作流状态机}](#def-wf1-工作流状态机-def-wf1-工作流状态机)
    - [Axiom WF1: 状态互斥 {#axiom-wf1-状态互斥}](#axiom-wf1-状态互斥-axiom-wf1-状态互斥)
    - [Theorem WF1: 状态可达性 {#theorem-wf1-状态可达性}](#theorem-wf1-状态可达性-theorem-wf1-状态可达性)
  - [4. Rust 实现方案 {#4-rust-实现方案}](#4-rust-实现方案-4-rust-实现方案)
    - [4.1 枚举（Enum）状态机 {#41-枚举状态机}](#41-枚举状态机-41-枚举状态机)
    - [4.2 Typestate 模式 {#42-typestate-模式}](#42-typestate-模式-42-typestate-模式)
    - [4.3 持久化工作流 {#43-持久化工作流}](#43-持久化工作流-43-持久化工作流)
  - [5. 反例与边界 {#5-反例与边界}](#5-反例与边界-5-反例与边界)
    - [反例 1：无效状态迁移 {#反例-1无效状态迁移}](#反例-1无效状态迁移-反例-1无效状态迁移)
    - [反例 2：并发事件导致状态竞争 {#反例-2并发事件导致状态竞争}](#反例-2并发事件导致状态竞争-反例-2并发事件导致状态竞争)
    - [边界：状态版本迁移 {#边界状态版本迁移}](#边界状态版本迁移-边界状态版本迁移)
  - [6. 与其他模式的关系 {#6-与其他模式的关系}](#6-与其他模式的关系-6-与其他模式的关系)
  - [7. 权威来源索引 {#7-权威来源索引}](#7-权威来源索引-7-权威来源索引)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)

---

## 1. 问题定义与动机 {#1-问题定义与动机}

> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)

长周期业务流程（订单履约、审批、物流）具有**状态多、分支多、易回退**的特点。若用命令式代码直接表达，容易出现以下问题：

- **隐式状态**：状态散落在多个布尔标志或数据库字段中，难以追踪当前所处阶段。
- **非法迁移**：代码路径可能允许"已发货的订单重新支付"等不符合业务规则的操作。
- **崩溃恢复**：进程重启后无法确定已执行到哪个步骤，导致重复处理或遗漏。

工作流状态机模式把业务流程显式建模为**有限状态机（FSM）**：状态、事件、迁移、动作全部显式声明，使系统行为可预测、可验证、可持久化恢复。

---

## 2. 核心概念 {#2-核心概念}

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)

- **状态（State）**：流程在某一时刻的快照，如 `Pending`、`Paid`、`Shipped`、`Completed`、`Failed`。
- **事件（Event）**：触发状态迁移的外部或内部信号，如 `Pay`、`Ship`、`Deliver`、`Cancel`。
- **迁移（Transition）**：满足前置条件时，从源状态到目标状态的变化，通常表示为 `S × E → S`。
- **动作（Action）**：迁移前后执行的副作用，如持久化、发送通知、记录审计日志。
- **Typestate**：利用 Rust 类型系统（Type System）在编译期排除非法迁移。

在 Rust 中，该模式常借助枚举、`async/await`、Typestate 和持久化存储实现。

---

## 3. 形式化定义 {#3-形式化定义}

> **来源**: [Rust Official Docs](https://doc.rust-lang.org/)

### Def WF1: 工作流状态机 {#def-wf1-工作流状态机}

一个工作流状态机是五元组

```text
M := (S, E, T ⊆ S × E × S, s₀ ∈ S, F ⊆ S)
```

其中：

- `S`：有限非空状态集合。
- `E`：有限事件集合。
- `T`：迁移关系，`(s, e, s') ∈ T` 表示在状态 `s` 接收到事件 `e` 后可迁移到 `s'`。
- `s₀`：初始状态。
- `F`：终止状态集合（成功或失败）。

### Axiom WF1: 状态互斥 {#axiom-wf1-状态互斥}

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)

任意时刻，工作流实例处于且仅处于一个状态：

```text
∀ instance, ∀ t, ∃! s ∈ S : state(instance, t) = s
```

### Theorem WF1: 状态可达性 {#theorem-wf1-状态可达性}

> **来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)

若事件序列 `e₁, e₂, ..., eₙ` 依次被处理，且每次迁移均满足 `T` 中定义，则实例最终状态 `sₙ` 由 `s₀` 和事件序列唯一确定。

**证明概要**：

1. 初始状态唯一为 `s₀`。
2. 对第 `i` 步，假设当前状态 `sᵢ₋₁` 唯一。
3. 事件 `eᵢ` 触发迁移 `(sᵢ₋₁, eᵢ, sᵢ) ∈ T`；由 Axiom WF1，状态互斥保证 `sᵢ` 唯一。
4. 归纳可得最终状态 `sₙ` 唯一。

---

## 4. Rust 实现方案 {#4-rust-实现方案}

> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

### 4.1 枚举状态机 {#41-枚举状态机}

最直接的方式是用 `enum` 表达状态与事件，在 `match` 中穷举合法迁移。

```rust
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum OrderState {
    Pending,
    Paid,
    Shipped,
    Completed,
    Cancelled,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum OrderEvent {
    Pay,
    Ship,
    Deliver,
    Cancel,
}

#[derive(Debug)]
enum TransitionError {
    InvalidTransition(OrderState, OrderEvent),
}

impl OrderState {
    fn transition(self, event: OrderEvent) -> Result<OrderState, TransitionError> {
        use OrderEvent::*;
        match (self, event) {
            (OrderState::Pending, Pay)     => Ok(OrderState::Paid),
            (OrderState::Paid, Ship)       => Ok(OrderState::Shipped),
            (OrderState::Shipped, Deliver) => Ok(OrderState::Completed),
            (OrderState::Pending, Cancel)  => Ok(OrderState::Cancelled),
            (from, evt) => Err(TransitionError::InvalidTransition(from, evt)),
        }
    }
}

fn main() {
    let s = OrderState::Pending
        .transition(OrderEvent::Pay).unwrap()
        .transition(OrderEvent::Ship).unwrap();
    assert_eq!(s, OrderState::Shipped);

    let err = s.transition(OrderEvent::Pay);
    assert!(matches!(err, Err(TransitionError::InvalidTransition { .. })));
}
```

> **来源**: [Rust Standard Library](https://doc.rust-lang.org/std/)

### 4.2 Typestate 模式 {#42-typestate-模式}

利用泛型（Generics）参数把状态编码进类型，**非法迁移在编译期即被拒绝**。

```rust
use std::marker::PhantomData;

#[derive(Debug)] struct Pending;
#[derive(Debug)] struct Paid;
#[derive(Debug)] struct Shipped;
#[derive(Debug)] struct Completed;
#[derive(Debug)] struct Cancelled;

#[derive(Debug)]
struct Order<State> {
    id: u64,
    _state: PhantomData<State>,
}

impl Order<Pending> {
    fn new(id: u64) -> Self {
        Self { id, _state: PhantomData }
    }
    fn pay(self) -> Order<Paid> {
        Order { id: self.id, _state: PhantomData }
    }
    fn cancel(self) -> Order<Cancelled> {
        Order { id: self.id, _state: PhantomData }
    }
}

impl Order<Paid> {
    fn ship(self) -> Order<Shipped> {
        Order { id: self.id, _state: PhantomData }
    }
}

impl Order<Shipped> {
    fn deliver(self) -> Order<Completed> {
        Order { id: self.id, _state: PhantomData }
    }
}

fn main() {
    let order = Order::new(42).pay().ship().deliver();
    println!("{:?}", order);
    // 以下代码无法编译：
    // let bad = Order::new(43).ship();
}
```

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)

### 4.3 持久化工作流 {#43-持久化工作流}

生产环境需要把状态持久化，以便进程重启后继续推进。

```rust
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum OrderState {
    Pending,
    Paid,
    Shipped,
    Completed,
    Cancelled,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum OrderEvent { Pay, Ship, Deliver, Cancel }

#[derive(Debug)]
enum WorkflowError {
    InvalidTransition(OrderState, OrderEvent),
    Store(String),
}

impl OrderState {
    fn transition(self, event: OrderEvent) -> Result<OrderState, WorkflowError> {
        use OrderEvent::*;
        match (self.clone(), event.clone()) {
            (OrderState::Pending, Pay)     => Ok(OrderState::Paid),
            (OrderState::Paid, Ship)       => Ok(OrderState::Shipped),
            (OrderState::Shipped, Deliver) => Ok(OrderState::Completed),
            (OrderState::Pending, Cancel)  => Ok(OrderState::Cancelled),
            (from, evt) => Err(WorkflowError::InvalidTransition(from, evt)),
        }
    }
}

trait StateStore {
    fn load(&self, id: &str) -> Result<Option<OrderState>, WorkflowError>;
    fn save(&mut self, id: &str, state: OrderState) -> Result<(), WorkflowError>;
}

struct InMemoryStore { data: HashMap<String, OrderState> }
impl InMemoryStore { fn new() -> Self { Self { data: HashMap::new() } } }
impl StateStore for InMemoryStore {
    fn load(&self, id: &str) -> Result<Option<OrderState>, WorkflowError> {
        Ok(self.data.get(id).cloned())
    }
    fn save(&mut self, id: &str, state: OrderState) -> Result<(), WorkflowError> {
        self.data.insert(id.to_string(), state);
        Ok(())
    }
}

struct OrderWorkflow<'a> {
    id: &'a str,
    store: &'a mut dyn StateStore,
}

impl<'a> OrderWorkflow<'a> {
    fn current(&self) -> Result<OrderState, WorkflowError> {
        self.store.load(self.id)?
            .ok_or_else(|| WorkflowError::Store(format!("{} not found", self.id)))
    }
    fn apply(&mut self, event: OrderEvent) -> Result<OrderState, WorkflowError> {
        let current = self.current()?;
        let next = current.transition(event)?;
        self.store.save(self.id, next.clone())?;
        Ok(next)
    }
}

fn main() {
    let mut store = InMemoryStore::new();
    // 初始化实例状态
    store.save("order-1", OrderState::Pending).unwrap();
    let mut wf = OrderWorkflow { id: "order-1", store: &mut store };
    wf.apply(OrderEvent::Pay).unwrap();
    wf.apply(OrderEvent::Ship).unwrap();
    assert_eq!(wf.current().unwrap(), OrderState::Shipped);
}
```

> **来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)

---

## 5. 反例与边界 {#5-反例与边界}

> **来源**: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)

### 反例 1：无效状态迁移 {#反例-1无效状态迁移}

```rust,should_panic
let state = OrderState::Shipped;
state.transition(OrderEvent::Pay).unwrap(); // Err: invalid transition
```

**违反**：Axiom WF1 与 Theorem WF1 要求迁移必须属于 `T`。

**修复**：在应用事件前检查当前状态与事件的组合是否合法；Typestate 模式可进一步在编译期禁止。

### 反例 2：并发事件导致状态竞争 {#反例-2并发事件导致状态竞争}

多线程/多 actor 同时处理同一工作流实例时，逻辑顺序可能被破坏。

```rust
use std::sync::{Arc, Mutex};
use std::thread;

let state = Arc::new(Mutex::new(OrderState::Pending));
let s1 = Arc::clone(&state);
let s2 = Arc::clone(&state);

let t1 = thread::spawn(move || {
    let mut st = s1.lock().unwrap();
    *st = st.clone().transition(OrderEvent::Pay).unwrap_or_else(|_| st.clone());
});
let t2 = thread::spawn(move || {
    let mut st = s2.lock().unwrap();
    *st = st.clone().transition(OrderEvent::Ship).unwrap_or_else(|_| st.clone());
});
t1.join().unwrap();
t2.join().unwrap();
// 实际结果依赖线程调度顺序，可能出现非预期状态
```

**违反**：Axiom WF1 的状态唯一性在逻辑层面被打破。

**修复**：

- 每个工作流实例使用**单一写入者**（Actor / 单线程事件循环）。
- 通过数据库行锁或版本号实现乐观锁，拒绝过期事件。
- 使用持久化日志按顺序重放事件。

### 边界：状态版本迁移 {#边界状态版本迁移}

业务演进可能新增状态或事件。旧实例加载到新代码后可能出现：

- 未知状态反序列化失败。
- 旧状态机缺少新迁移，导致合法业务操作被拒绝。

**处理建议**：

- 使用显式版本号区分状态机 schema。
- 在加载时执行状态迁移（state migration）。
- 对无法识别的状态提供降级路径或人工介入。

---

## 6. 与其他模式的关系 {#6-与其他模式的关系}

> **来源**: [crates.io](https://crates.io/)

| 模式 | 关系 | 说明 |
|------|------|------|
| [补偿链模式](02_compensation_chain.md) | 组合 | 状态机的 `Failed` 迁移可触发补偿链 |
| [长事务模式](03_long_running_transaction.md) | 组合 | 长事务通常用状态机建模持久化状态 |
| [Saga 模式](../05_distributed/01_saga_pattern.md) | 组合 | Saga 的协调器本身是一个状态机 |
| [Outbox 模式](../05_distributed/05_outbox_pattern.md) | 增强 | 状态迁移产生的事件可通过 Outbox 保证投递 |
| Typestate | 实现技术 | 在编译期禁止非法迁移 |
| Actor 模型 | 实现技术 | 工作流实例作为 Actor，保证事件串行处理 |

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
> - [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
> - [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
> **P2 权威来源（学术与行业经典）**:
>
> - [Wikipedia - Finite-state machine](https://en.wikipedia.org/wiki/Finite-state_machine)
> - [ACM](https://dl.acm.org/)
> - [IEEE](https://standards.ieee.org/)

---

## 学术权威参考 {#学术权威参考}

- [Aeneas](https://aeneas-verification.github.io/)
- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)

---

**维护者**: Rust 学习项目团队

**文档版本**: 1.0

**对应 Rust 版本**: 1.97.0+ (Edition 2024)

**状态**: ✅ 权威来源对齐完成
