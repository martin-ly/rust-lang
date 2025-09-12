# Wikipedia 概念映射到代码模块

本表将常见分布式系统 Wikipedia 主题映射到本 crate 的模块、类型与 API，便于知识点到代码的跳转学习。

- Failure detector → `swim`（`SwimMemberState`，`SwimEvent`）
- Gossip/Anti-entropy → `swim`，`membership`
- Consistent hashing → `topology::ConsistentHashRing`，`partitioning`
- Quorum/Replication → `replication::{QuorumPolicy, MajorityQuorum, Replicator}`
- Consensus (Raft/Paxos/VR) → `consensus` 抽象，`consensus_raft` 可选特性
- Consistency models → `consistency::ConsistencyLevel` 与 `replication` 中 ACK 规则
- State machine replication → `storage::{StateMachineStorage, LogStorage}`
- Idempotency → `storage::IdempotencyStore` + `replication::LocalReplicator::replicate_idempotent`
- Logical clock/Timeouts → `scheduling::{LogicalClock, TimerService}`
- Saga/Compensation → `transactions::{Saga, SagaStep}`

占位：后续将为每个条目增加“定义/性质/可观测行为/典型陷阱/相关公式或判据”小节。
