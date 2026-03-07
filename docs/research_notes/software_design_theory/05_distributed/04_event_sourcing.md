# Event Sourcing 模式形式化定义

> **模式类型**: 数据持久化
> **创建日期**: 2026-03-08
> **版本**: v1.0

---

## 1. 概念定义 (Def)

### Def ES1: Event Sourcing

事件溯源是一种**状态持久化模式**，系统状态不直接存储，而是存储导致状态变更的**事件序列**，状态通过**重放事件**重建。

```
EventSourcing := (E, S, apply, snapshot)
  where:
    E = {e₁, e₂, ..., eₙ}       -- 不可变事件序列
    S                            -- 聚合状态
    apply: S × E → S             -- 状态应用函数
    snapshot: ℕ → S              -- 快照函数
```

### Def ES2: 事件不变性

```
∀e ∈ E. Immutable(e)
```

事件一旦创建，不可修改。

### Def ES3: 状态重建

```
State(tₙ) = apply(apply(...apply(S₀, e₁), e₂)...eₙ)
          = fold(apply, S₀, [e₁, e₂, ..., eₙ])
```

当前状态是初始状态应用所有事件的结果。

---

## 2. 基本假设 (Axiom)

### Axiom ES1: 事件顺序性

```
∀eᵢ, eⱼ ∈ E. i < j → timestamp(eᵢ) ≤ timestamp(eⱼ)
```

事件按时间顺序存储。

### Axiom ES2: 应用函数确定性

```
∀s, e. apply(s, e) = s' 是确定性的
```

给定相同状态和事件，结果总是相同。

### Axiom ES3: 版本控制

```
∀e ∈ E. version(e) = sequence_number ∈ ℕ
```

每个事件有唯一的版本号。

---

## 3. 定理 (Theorem)

### Theorem ES1: 状态可重现性

```
∀t. State(t) 可通过重放 E[0..t] 重建
```

**证明概要**:

1. 根据 Def ES3，状态是 fold 的结果
2. 事件序列 E 完整保存
3. apply 函数确定性保证 (Axiom ES2)
4. 因此给定相同事件序列，总能重建相同状态

### Theorem ES2: 审计完整性

```
∀t. 历史状态 State(t) 可查询
```

**证明概要**:

1. 事件不可变 (Def ES2)
2. 事件序列完整保存
3. 通过重放到任意位置 t，可重建历史状态

---

## 4. Rust 实现示例

```rust
// 事件特质
pub trait Event: Serialize + DeserializeOwned + Clone {
    type AggregateId;
    fn aggregate_id(&self) -> &Self::AggregateId;
    fn version(&self) -> u64;
}

// 聚合根
pub trait Aggregate: Default {
    type Event: Event;
    type Command;
    type Error;

    fn apply(&mut self, event: &Self::Event);
    fn handle(&self, cmd: Self::Command) -> Result<Vec<Self::Event>, Self::Error>;
}

// 事件存储
pub trait EventStore<E: Event> {
    async fn append(&self, events: &[E]) -> Result<(), StoreError>;
    async fn read(&self, aggregate_id: &E::AggregateId, from_version: u64)
        -> Result<Vec<E>, StoreError>;
}

// 仓储模式
pub struct EventSourcedRepository<A: Aggregate> {
    store: Box<dyn EventStore<A::Event>>,
}

impl<A: Aggregate> EventSourcedRepository<A> {
    pub async fn load(&self, id: &<A::Event as Event>::AggregateId)
        -> Result<A, RepositoryError>
    {
        let events = self.store.read(id, 0).await?;
        let mut aggregate = A::default();
        for event in events {
            aggregate.apply(&event);
        }
        Ok(aggregate)
    }

    pub async fn save(&self, aggregate: &A, events: Vec<A::Event>)
        -> Result<(), RepositoryError>
    {
        self.store.append(&events).await?;
        Ok(())
    }
}
```

---

## 5. 与 CQRS 的关系

```
┌─────────────┐     Events      ┌─────────────┐
│   Command   │ ───────────────→│ Event Store │
│   Handler   │                 │  (Append)   │
└─────────────┘                 └──────┬──────┘
       │                               │
       │ Projections                   │ Read
       ▼                               ▼
┌─────────────┐                 ┌─────────────┐
│   Query     │ ←───────────────│   Replay    │
│   Handler   │   Read Model    │   Events    │
└─────────────┘                 └─────────────┘
```

---

**相关阅读**:

- [CQRS 模式](./02_cqrs_pattern.md)
- [分布式概念族谱](../../DISTRIBUTED_CONCEPT_MINDMAP.md)
