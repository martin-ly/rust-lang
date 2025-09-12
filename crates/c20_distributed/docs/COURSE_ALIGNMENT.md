# 分布式系统课程对标（国际一流课程与本仓库模块映射）

本文件对标国际名校课程（示例：MIT 6.824/6.5840、CMU 15-440/15-745、Stanford CS244B、Berkeley CS262A、Cornell CS7410）与 Wikipedia 经典主题，将其核心单元映射到本 crate 的模块与示例代码，支持“概念-代码-实验”一体化学习路径。

- 本 crate 模块：`membership`、`topology`、`consensus`、`partitioning`、`consistency`、`transport`、`storage`、`scheduling`、`codec`、`swim`、`replication`、`transactions`（Saga）。

## 1) 节点与成员管理（Membership）

- 课程对标：MIT 6.824 Lab: Fault Tolerance 前置；CMU 15-440 Gossip & Membership；Cornell CS7410 Group Membership。
- Wikipedia：Failure detector、Gossip protocol、Membership service。
- 代码映射：`src/membership.rs`，`src/swim.rs`（SWIM 事件/状态、传播）。
- 学习要点：故障检测强弱完备性、视图一致性、反熵与传播周期参数。

## 2) 集群拓扑与分片（Topology/Partitioning）

- 课程对标：MIT 6.824 Sharding/Partitioning；Berkeley CS262A Scalable storage；CMU 15-440 Consistent Hashing。
- Wikipedia：Consistent hashing、Shard、Virtual node。
- 代码映射：`src/topology.rs`（一致性哈希环）、`src/partitioning.rs`。
- 学习要点：虚拟节点、再均衡代价、热点与倾斜控制。

## 3) 共识与复制（Consensus & Replication）

- 课程对标：MIT 6.824 Raft Labs；Stanford Raft/Paxos lectures；Cornell Paxos/VRR。
- Wikipedia：Paxos、Raft、Viewstamped Replication、Quorum。
- 代码映射：`src/consensus.rs` 抽象；可选 `consensus-raft`；`src/replication.rs` 中 MajorityQuorum、Replicator。
- 学习要点：日志复制、一致性语义、过半法定人数、领导者选举与任期。

## 4) 一致性级别（Consistency Levels）

- 课程对标：Berkeley CS262A CAP/PACELC；MIT 6.824 Linearizability vs Eventual；CMU 15-440 Consistency models。
- Wikipedia：Linearizability、Sequential consistency、Eventual consistency、Quorum reads/writes。
- 代码映射：`src/consistency.rs`（Level 枚举）与 `replication.rs` 的 `required_acks` 计算。
- 学习要点：线性一致/顺序一致/最终一致的可观测差异与测试方法（Jepsen 思路）。

## 5) 存储与状态机（Storage & State Machine）

- 课程对标：MIT 6.824 KV/SMR；Berkeley 事务存储；CMU 日志结构存储。
- Wikipedia：State machine replication、Write-ahead logging、Idempotency。
- 代码映射：`src/storage.rs`（`StateMachineStorage`、`LogStorage`、`IdempotencyStore`）。
- 学习要点：确定性状态机、去重幂等、快照与日志截断。

## 6) 事务与补偿（Transactions & Saga）

- 课程对标：CMU 分布式事务；Berkeley Sagas/2PC/3PC；Cornell Fault-tolerant transactions。
- Wikipedia：Two-phase commit、Three-phase commit、Saga pattern。
- 代码映射：`src/transactions.rs`（`Saga`/`SagaStep`）。
- 学习要点：严格事务 vs Saga 补偿；幂等补偿步骤；跨分区写入策略。

## 7) 传输与调度（Transport & Scheduling）

- 课程对标：CMU RPC/Time；Berkeley Async I/O；MIT 心跳与时钟。
- Wikipedia：RPC、Logical clock、Failure detectors、Timeouts。
- 代码映射：`src/transport.rs`、`src/scheduling.rs`（`LogicalClock`、`TimerService`）。
- 学习要点：超时与重试、逻辑时钟对顺序与重放的影响。

## 8) 故障与健康（SWIM 与反熵）

- 课程对标：CMU Gossip；Berkeley Epidemic algorithms；Cornell Probabilistic failure detectors。
- Wikipedia：SWIM、Gossip-style membership、Anti-entropy。
- 代码映射：`src/swim.rs`（`SwimMemberState`、`SwimEvent`、`SwimTransport`）。
- 学习要点：传播因子、可达性、谣言终止时间上界。

## 学习路径建议（与本仓库实验结合）

1. 阅读 `membership`/`swim` 并实现基本心跳与传播测试。
2. 使用 `topology` 构建一致性哈希环，模拟扩缩容再均衡。
3. 在 `replication` 上实现不同 `ConsistencyLevel` 写入策略与 ACK 统计。
4. 打通 `storage` 幂等存储，结合 `transactions::Saga` 编写两步业务补偿 Demo。
5. 若开启 `consensus-raft` 特性，完成简化日志复制与 Leader 切换实验。

## 参考资料（建议检索）

- MIT 6.824/6.5840: Distributed Systems
- CMU 15-440, 15-745: Distributed Systems
- Berkeley CS262A: Advanced Topics in Computer Systems
- Stanford CS244B: Distributed Systems
- Cornell CS7410: Distributed Computing Principles
- Wikipedia：Raft, Paxos, Consistent hashing, SWIM, Saga, Linearizability 等词条
