# 分布式事务语义 (Distributed Transaction Semantics)

## 目录

- [分布式事务语义 (Distributed Transaction Semantics)](#分布式事务语义-distributed-transaction-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 分布式事务基础](#2-分布式事务基础)
    - [2.1 ACID 在分布式环境中的挑战](#21-acid-在分布式环境中的挑战)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 两阶段提交 (2PC)](#3-两阶段提交-2pc)
    - [3.1 2PC 协议流程](#31-2pc-协议流程)
    - [3.2 2PC 状态机](#32-2pc-状态机)
    - [3.3 Rust 实现](#33-rust-实现)
    - [3.4 2PC 故障恢复](#34-2pc-故障恢复)
  - [4. 三阶段提交 (3PC)](#4-三阶段提交-3pc)
    - [4.1 3PC 改进](#41-3pc-改进)
  - [5. Saga 模式](#5-saga-模式)
    - [5.1 Saga 基本模型](#51-saga-基本模型)
    - [5.2 Rust 实现](#52-rust-实现)
  - [6. 事务隔离级别](#6-事务隔离级别)
    - [6.1 分布式隔离级别](#61-分布式隔离级别)
  - [7. 形式化性质](#7-形式化性质)
    - [7.1 ACID 形式化](#71-acid-形式化)
  - [8. 总结](#8-总结)

## 1. 引言

分布式事务跨越多节点执行操作，需要保证 ACID 特性。
本文档深入分析 2PC、3PC、Saga 等分布式事务协议的形式化语义和 Rust 实现。

---

## 2. 分布式事务基础

### 2.1 ACID 在分布式环境中的挑战

```
单机 ACID vs 分布式 ACID:

单机事务:                    分布式事务:
┌──────────┐                ┌──────────┐
│ Atomic   │                │ Atomic   │  ← 需要协调
│ Consistent│                │ Consistent│  ← 需要共识
│ Isolated │                │ Isolated │  ← 需要锁/时间戳
│ Durable  │                │ Durable  │  ← 需要复制
└──────────┘                └────┬─────┘
                                 │
                    ┌────────────┼────────────┐
                    ↓            ↓            ↓
               ┌────────┐   ┌────────┐   ┌────────┐
               │Node A  │   │Node B  │   │Node C  │
               │Database│   │Database│   │Database│
               └────────┘   └────────┘   └────────┘

核心挑战:
  • 网络延迟和分区
  • 部分故障
  • 性能开销
```

### 2.2 形式化定义

```
分布式事务:

T = {op₁, op₂, ..., opₙ} 跨越节点 {N₁, N₂, ..., Nₘ}

原子性要求:
  ∀T. commit(T) → (∀N. committed_on(N, T))

  或

  abort(T) → (∀N. aborted_on(N, T))

一致性要求:
  □ (global_state ⊨ invariants)

隔离性要求:
  schedule(T₁, T₂, ...) 等价于某个串行调度
```

---

## 3. 两阶段提交 (2PC)

### 3.1 2PC 协议流程

```
两阶段提交协议:

Phase 1: 投票阶段 (Voting)
─────────────────────────────────────────
Coordinator              Participants
   │                          │
   │──Prepare(T)────────────→│
   │                         │ 写入 undo/redo 日志
   │←──Vote(Yes/No)──────────│
   │                          │

   如果所有 Vote = Yes:

Phase 2: 提交阶段 (Commit)
─────────────────────────────────────────
   │                          │
   │──Commit(T)─────────────→│
   │                         │ 正式提交
   │←──Ack───────────────────│
   │                          │

   如果有 Vote = No:

   │──Abort(T)──────────────→│
   │                         │ 回滚
   │←──Ack───────────────────│
   │                          │
```

### 3.2 2PC 状态机

```
Coordinator 状态:
  INIT ──prepare──→ PREPARING ──all_yes──→ COMMITTING ──acks──→ COMMITTED
                      │                      │
                      └─any_no──→ ABORTING ──┘

Participant 状态:
  INIT ──prepare──→ PREPARED ──commit──→ COMMITTED
                      │
                      └─abort──→ ABORTED
```

### 3.3 Rust 实现

```rust
// 2PC 协调者
struct TwoPhaseCoordinator {
    transaction_id: TxId,
    participants: Vec<ParticipantRef>,
    state: CoordinatorState,
    vote_results: HashMap<NodeId, Vote>,
}

enum CoordinatorState {
    Init,
    Preparing,
    Prepared,    // 所有参与者已投票 Yes
    Committing,
    Committed,
    Aborting,
    Aborted,
}

enum Vote {
    Yes,           // 可以提交
    No(String),    // 无法提交（原因）
}

impl TwoPhaseCoordinator {
    async fn execute_transaction(&mut self, ops: Vec<Operation>) -> Result<(), TxError> {
        self.state = CoordinatorState::Preparing;

        // Phase 1: 发送 Prepare
        let mut votes = vec![];
        for participant in &self.participants {
            let vote = participant.prepare(self.transaction_id, &ops).await?;
            votes.push(vote);
        }

        // 检查投票结果
        let all_yes = votes.iter().all(|v| matches!(v, Vote::Yes));

        // Phase 2: 提交或中止
        if all_yes {
            self.state = CoordinatorState::Committing;
            self.commit_all().await?;
            self.state = CoordinatorState::Committed;
        } else {
            self.state = CoordinatorState::Aborting;
            self.abort_all().await?;
            self.state = CoordinatorState::Aborted;
            return Err(TxError::Aborted);
        }

        Ok(())
    }

    async fn commit_all(&self) -> Result<(), TxError> {
        for participant in &self.participants {
            if let Err(e) = participant.commit(self.transaction_id).await {
                // 记录待处理事务，由恢复机制处理
                self.log_pending_commit(participant.id(), self.transaction_id).await;
            }
        }
        Ok(())
    }
}

// 2PC 参与者
struct TwoPhaseParticipant {
    node_id: NodeId,
    prepared_txns: HashMap<TxId, PreparedData>,
}

struct PreparedData {
    undo_log: Vec<UndoOperation>,
    redo_log: Vec<RedoOperation>,
}

impl TwoPhaseParticipant {
    async fn prepare(&mut self, tx_id: TxId, ops: &[Operation]) -> Result<Vote, TxError> {
        // 1. 执行操作（但不提交）
        let (undo_log, redo_log) = self.execute_tentatively(ops).await?;

        // 2. 持久化日志
        self.persist_logs(tx_id, &undo_log, &redo_log).await?;

        // 3. 记录 prepared 状态
        self.prepared_txns.insert(tx_id, PreparedData {
            undo_log,
            redo_log,
        });

        Ok(Vote::Yes)
    }

    async fn commit(&mut self, tx_id: TxId) -> Result<(), TxError> {
        let data = self.prepared_txns.remove(&tx_id)
            .ok_or(TxError::NotPrepared)?;

        // 应用 redo log
        for op in data.redo_log {
            op.apply().await?;
        }

        // 清理日志
        self.cleanup_logs(tx_id).await;

        Ok(())
    }

    async fn abort(&mut self, tx_id: TxId) -> Result<(), TxError> {
        let data = self.prepared_txns.remove(&tx_id)
            .ok_or(TxError::NotPrepared)?;

        // 应用 undo log（回滚）
        for op in data.undo_log.iter().rev() {
            op.apply().await?;
        }

        self.cleanup_logs(tx_id).await;

        Ok(())
    }
}
```

### 3.4 2PC 故障恢复

```rust
// 协调者故障恢复
struct CoordinatorRecovery {
    log: TransactionLog,
}

impl CoordinatorRecovery {
    async fn recover(&self) -> Vec<PendingTransaction> {
        let pending = self.log.get_incomplete_transactions().await;

        for tx in pending {
            match tx.state {
                // 不知道参与者是否收到 Prepare - 询问参与者
                CoordinatorState::Preparing => {
                    self.heuristic_rollback(tx.id).await;
                }

                // 已发送 Commit - 重试提交
                CoordinatorState::Committing => {
                    self.retry_commit(tx.id).await;
                }

                // 已发送 Abort - 重试中止
                CoordinatorState::Aborting => {
                    self.retry_abort(tx.id).await;
                }

                _ => {}
            }
        }
    }
}

// 参与者故障恢复
struct ParticipantRecovery {
    prepared_log: PreparedLog,
}

impl ParticipantRecovery {
    async fn recover(&self) {
        let prepared = self.prepared_log.get_all().await;

        for (tx_id, data) in prepared {
            // 询问协调者事务状态
            match self.query_coordinator(tx_id).await {
                Some(true) => self.commit(tx_id).await,
                Some(false) => self.abort(tx_id).await,
                None => {
                    // 协调者不可用 - 阻塞等待或启发式决策
                    self.wait_or_heuristic_decision(tx_id).await;
                }
            }
        }
    }
}
```

---

## 4. 三阶段提交 (3PC)

### 4.1 3PC 改进

```
三阶段提交协议 (解决 2PC 阻塞问题):

Phase 1: CanCommit?
─────────────────────────────────────────
Coordinator → Participants: CanCommit?
Participants → Coordinator: Yes/No

Phase 2: PreCommit
─────────────────────────────────────────
If all Yes:
  Coordinator → Participants: PreCommit
  Participants: 准备提交，设置超时
  Participants → Coordinator: Ack

Phase 3: DoCommit/Abort
─────────────────────────────────────────
Coordinator → Participants: DoCommit
Participants: 正式提交

超时处理:
  - 参与者在等待 PreCommit 时超时 → 可以安全中止
  - 参与者在等待 DoCommit 时超时 → 可以安全提交（已 PreCommit）
```

```rust
// 3PC 协调者
struct ThreePhaseCoordinator {
    state: ThreePCState,
    timeout: Duration,
}

enum ThreePCState {
    Init,
    CanCommitSent,
    PreCommitSent,
    Committed,
    Aborted,
}

impl ThreePhaseCoordinator {
    async fn execute(&mut self) -> Result<(), TxError> {
        // Phase 1
        self.state = ThreePCState::CanCommitSent;
        let can_commits = self.ask_can_commit().await?;

        if can_commits.iter().all(|r| r.is_yes()) {
            // Phase 2
            self.state = ThreePCState::PreCommitSent;
            self.send_pre_commit().await?;

            // Phase 3
            self.send_do_commit().await?;
            self.state = ThreePCState::Committed;
        } else {
            self.send_abort().await?;
            self.state = ThreePCState::Aborted;
        }

        Ok(())
    }
}

// 3PC 参与者（带超时）
struct ThreePhaseParticipant {
    state: ThreePCParticipantState,
}

enum ThreePCParticipantState {
    Init,
    CanCommitYes,  // 已同意 CanCommit
    PreCommitted,  // 已 PreCommit（必须能提交）
    Committed,
    Aborted,
}

impl ThreePhaseParticipant {
    // 超时处理
    async fn on_timeout(&mut self, current_state: ThreePCParticipantState) {
        match current_state {
            // 还未收到 PreCommit - 可以安全中止
            ThreePCParticipantState::CanCommitYes => {
                self.abort().await;
            }

            // 已 PreCommit - 必须能提交（咨询其他节点或等待）
            ThreePCParticipantState::PreCommitted => {
                // 由于已承诺能提交，必须提交
                // 可以咨询其他参与者或等待协调者恢复
                if self.other_participants_committed().await {
                    self.commit().await;
                } else {
                    self.wait_for_recovery().await;
                }
            }

            _ => {}
        }
    }
}
```

---

## 5. Saga 模式

### 5.1 Saga 基本模型

```
Saga 模式 (长事务分解):

传统事务:                    Saga 模式:
┌──────────┐                ┌─────────┐
│ Begin    │                │ Step 1  │
│ TX       │                │  本地事务│
├──────────┤                └────┬────┘
│ Op 1     │                     │
│ Op 2     │                ┌────▼────┐
│ ...      │                │ Step 2  │
│ Op n     │                │  本地事务│
├──────────┤                └────┬────┘
│ Commit   │                     │
└──────────┘                     ↓
                           ┌─────────┐
                           │ Step N  │
                           │  本地事务│
                           └─────────┘

补偿机制:
  如果 Step k 失败:
    执行 Step k-1 的补偿
    执行 Step k-2 的补偿
    ...
    执行 Step 1 的补偿
```

### 5.2 Rust 实现

```rust
// Saga 步骤 trait
trait SagaStep: Send + Sync {
    type Input;
    type Output;
    type Error;
    type CompensationInput;

    // 正向操作
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error>;

    // 补偿操作
    async fn compensate(&self, input: Self::CompensationInput) -> Result<(), Self::Error>;
}

// Saga 编排器
struct SagaOrchestrator {
    steps: Vec<Box<dyn DynSagaStep>>,
    executed: Vec<CompensationRecord>,
}

struct CompensationRecord {
    step_index: usize,
    compensation_input: Box<dyn Any + Send>,
}

impl SagaOrchestrator {
    async fn execute(&mut self, initial_input: Value) -> Result<Value, SagaError> {
        let mut current_input = initial_input;

        for (i, step) in self.steps.iter().enumerate() {
            match step.execute_dyn(current_input.clone()).await {
                Ok(output) => {
                    // 记录补偿信息
                    self.executed.push(CompensationRecord {
                        step_index: i,
                        compensation_input: Box::new(current_input),
                    });
                    current_input = output;
                }
                Err(e) => {
                    // 执行补偿
                    tracing::error!("Step {} failed: {:?}", i, e);
                    self.compensate().await?;
                    return Err(SagaError::StepFailed(i, e));
                }
            }
        }

        Ok(current_input)
    }

    async fn compensate(&mut self) -> Result<(), SagaError> {
        // 逆向执行补偿
        for record in self.executed.iter().rev() {
            let step = &self.steps[record.step_index];
            if let Err(e) = step.compensate_dyn(&*record.compensation_input).await {
                // 补偿失败 - 需要人工介入
                return Err(SagaError::CompensationFailed(record.step_index, e));
            }
        }
        Ok(())
    }
}

// 示例：订单处理 Saga
struct CreateOrderStep;
struct ProcessPaymentStep;
struct ReserveInventoryStep;
struct ShipOrderStep;

#[async_trait]
impl SagaStep for CreateOrderStep {
    type Input = OrderRequest;
    type Output = Order;
    type Error = OrderError;
    type CompensationInput = OrderId;

    async fn execute(&self, input: OrderRequest) -> Result<Order, OrderError> {
        // 创建订单
        let order = db::create_order(&input).await?;
        Ok(order)
    }

    async fn compensate(&self, order_id: OrderId) -> Result<(), OrderError> {
        // 取消订单
        db::cancel_order(order_id).await
    }
}

#[async_trait]
impl SagaStep for ProcessPaymentStep {
    type Input = Order;
    type Output = PaymentConfirmation;
    type Error = PaymentError;
    type CompensationInput = PaymentId;

    async fn execute(&self, order: Order) -> Result<PaymentConfirmation, PaymentError> {
        let payment = payment_gateway::charge(&order).await?;
        Ok(payment)
    }

    async fn compensate(&self, payment_id: PaymentId) -> Result<(), PaymentError> {
        // 退款
        payment_gateway::refund(payment_id).await
    }
}

// 使用示例
async fn place_order(request: OrderRequest) -> Result<Order, SagaError> {
    let mut saga = SagaOrchestrator::new();

    saga.add_step(CreateOrderStep);
    saga.add_step(ReserveInventoryStep);
    saga.add_step(ProcessPaymentStep);
    saga.add_step(ShipOrderStep);

    saga.execute(Box::new(request)).await
}
```

---

## 6. 事务隔离级别

### 6.1 分布式隔离级别

```rust
// SQL 标准隔离级别
enum IsolationLevel {
    ReadUncommitted,  // 读未提交
    ReadCommitted,    // 读已提交
    RepeatableRead,   // 可重复读
    Serializable,     // 串行化
}

// 分布式扩展
enum DistributedIsolation {
    SnapshotIsolation,      // 快照隔离
    SerializableSnapshot,   // 串行化快照
    StrictSerializable,     // 严格串行化
}

// 快照隔离实现
struct SnapshotIsolationManager {
    timestamp_oracle: TimestampOracle,
    active_transactions: HashMap<TxId, Timestamp>,
    committed_writes: BTreeMap<Timestamp, Vec<(Key, Value)>>,
}

impl SnapshotIsolationManager {
    fn begin_transaction(&mut self) -> TxId {
        let tx_id = generate_tx_id();
        let start_ts = self.timestamp_oracle.now();
        self.active_transactions.insert(tx_id, start_ts);
        tx_id
    }

    fn read(&self, tx_id: TxId, key: &Key) -> Option<Value> {
        let start_ts = self.active_transactions.get(&tx_id)?;

        // 读取快照时间戳之前的最新提交值
        self.committed_writes
            .range(..=*start_ts)
            .rev()
            .flat_map(|(_, writes)| writes.iter())
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.clone())
    }

    fn commit(&mut self, tx_id: TxId, writes: Vec<(Key, Value)>) -> Result<(), ConflictError> {
        let start_ts = self.active_transactions.get(&tx_id).unwrap();
        let commit_ts = self.timestamp_oracle.now();

        // 冲突检测: 检查读取的数据是否被其他事务修改
        for (key, _) in &writes {
            if self.is_write_conflict(key, *start_ts, commit_ts) {
                return Err(ConflictError::WriteWriteConflict);
            }
        }

        self.committed_writes.insert(commit_ts, writes);
        self.active_transactions.remove(&tx_id);

        Ok(())
    }
}
```

---

## 7. 形式化性质

### 7.1 ACID 形式化

```
原子性 (Atomicity):
  commit(T) → ∀n. committed(n, T)
  abort(T) → ∀n. aborted(n, T)

一致性 (Consistency):
  □ (db_state ⊨ invariants)

隔离性 (Isolation):
  schedule(S) ~ serial_schedule(S')

  其中 ~ 表示等价关系（如冲突等价、视图等价）

持久性 (Durability):
  commit(T) → ◇□ committed(T)
```

---

## 8. 总结

| 协议 | 阻塞 | 性能 | 适用场景 |
|------|------|------|----------|
| 2PC | 协调者故障时 | 低 | 强一致性需求 |
| 3PC | 网络分区时 | 中 | 需要非阻塞 |
| Saga | 无 | 高 | 长事务、微服务 |
| TCC | 无 | 高 | 电商、金融 |

关键公式:

$$
\text{DistributedTransaction} = \text{AtomicCommit} \times \text{IsolationLevel} \times \text{RecoveryProtocol}
$$
