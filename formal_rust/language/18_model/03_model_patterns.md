# 模型设计模式（Modeling Patterns for Rust Systems）

## 分类

- 结构模式：实体-值对象、聚合、领域事件、策略对象。
- 行为模式：有限状态机、命令-查询分离（CQRS）、事件溯源。
- 协议模式：请求-响应、补偿事务、两阶段提交、幂等等价类。
- 一致性模式：悲观锁、乐观并发控制、版本向量。

## 模式模板

- 名称、动机、上下文、问题、解法、结果、已知风险、验证要点、Rust 落地清单。

## 选型指南

- 根据一致性/延迟/吞吐/容错选择；提供决策表与权衡点。

---

## 模式目录

- 所有权与聚合根模式（Ownership & Aggregate Root）
- 不变式防护模式（Guarded Invariants）
- 有限状态机模式（FSM）
- CQRS 与事件溯源（CQRS & Event Sourcing）
- 幂等等价类与重试（Idempotency & Retry Classes）
- 事务语义编码（Typed Transactions）
- 一致性模式（Pessimistic/Optimistic/RwLock/Version Vector）
- 协议编排与补偿（Sagas/Two-phase Commit）

---

## 模式详解

### 1) 所有权与聚合根模式

- 动机：将跨实体的不变量收敛到聚合根，限制外部对内部的可变别名。
- Rust 落地：以结构体承载聚合根；通过不可变暴露、受控可变借用维护不变量；使用新类型封装 ID。
- 验证要点：对外仅暴露查询或事务性方法；不可导出内部可变引用；属性测试覆盖边界条件。

```rust
pub struct OrderId(pub u128);

pub struct Order {
    id: OrderId,
    items: Vec<Item>,
    total: u64,
}

impl Order {
    pub fn add_item(&mut self, item: Item) {
        self.total = self.total.checked_add(item.price).expect("overflow");
        self.items.push(item);
    }
}
```

### 2) 不变式防护模式

- 动机：用构造器与私有字段保证对象始终处于合法状态。
- Rust 落地：`new` 返回 `Result<Self, Error>`；在 `Drop`/RAII 中完成资源恢复。
- 验证要点：Creusot/Prusti 合约注明前置/后置；Proptest 随机生成边界输入。

### 3) 有限状态机（FSM）

- 动机：用类型系统编码状态空间与合法转移，拒绝不可达/非法转移。
- Rust 落地：枚举建模状态；方法返回新状态或错误；在异步场景下以 `Future` 驱动。

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JobState { Pending, Running, Completed, Failed }

impl JobState {
    pub fn start(self) -> Result<JobState, &'static str> {
        match self {
            JobState::Pending => Ok(JobState::Running),
            _ => Err("cannot start"),
        }
    }
}
```

### 4) CQRS 与事件溯源

- 动机：读写分离、以事件为真相来源，便于审计与回放。
- Rust 落地：命令处理器生成领域事件；事件存储与回放还原聚合；查询侧建立只读视图。
- 验证要点：事件幂等、顺序一致性、版本检查；Kani/loom 验证并发下的顺序性质。

### 5) 幂等等价类与重试

- 动机：网络/分布式失败下保障 at-least-once 与去重。
- Rust 落地：为命令引入幂等键；侧写持久化；重放时以等价类消歧。

### 6) 事务语义编码

- 动机：以类型限制事务范围与生命周期，强制提交/回滚路径完整。
- Rust 落地：`Transaction<'a>` 持有受限可变引用；`commit(self)`/`rollback(self)` 以 RAII 保证资源安全。

### 7) 一致性模式

- 动机：权衡延迟、吞吐、冲突概率与一致性目标。
- Rust 落地：悲观锁（`Mutex/RwLock`）、乐观并发（版本向量/校验和）、基于消息的序列化。

### 8) 协议编排与补偿（Sagas/2PC）

- 动机：跨服务事务管理。
- Rust 落地：编排器驱动步骤执行与补偿；2PC 以参与者/协调者抽象落地。

---

## 选型决策表（摘要）

- 强一致 + 低并发冲突：悲观锁 / 2PC
- 最终一致 + 高可用：Sagas + 幂等等价类
- 写多读多：CQRS + 事件溯源
- 别名复杂：聚合根 + 不变式防护

---

## 验证清单

- 不变式：构造与所有公开方法后置条件维持
- 状态机：非法转移不可构造（类型层拒绝）
- 并发：loom 探索关键交互无死锁/数据竞争
- 事件：回放与实时一致（可交换性/幂等性）
- 事务：异常路径必达回滚（Drop/RAII）

---

## 参考实现与进一步阅读

- Rustonomicon（所有权/生命周期边界）
- CQRS/ES 社区模式手册
- Lamport — 分布式一致性与时钟
