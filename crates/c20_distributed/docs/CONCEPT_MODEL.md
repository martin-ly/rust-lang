# 概念-关系-属性（CRA）模型：分布式系统核心

目标：以课程/工业标准对标的方式，统一“概念-关系-属性-约束-可证性”结构，支撑后续形式化与验证。

核心概念（节选）：

- 节点（Node）：属性：`id`、`role`、`addr`、`health`；关系：参与 `Cluster`、拥有 `Replica`。
- 集群（Cluster）：属性：`members`、`topology`；关系：包含 `Shard`、`Partition`、`ConsensusGroup`。
- 视图（View）：属性：`epoch/term`、`membership-set`；关系：约束复制与仲裁规则。
- 分片（Shard/Partition）：属性：`shard_id`、`replication_factor`；关系：映射到 `nodes`（一致性哈希）。
- 法定人数（Quorum）：属性：`size`、`policy`；关系：绑定 `ConsistencyLevel`。
- 一致性（ConsistencyLevel）：取值：Strong/Quorum/Eventual；约束：`required_acks(total)`。
- 共识组（ConsensusGroup）：属性：`leader`、`term`、`log`；关系：复制到 `followers`。
- 事务（Transaction/Saga）：属性：`steps`、`compensation`；关系：跨 `Shard` 的写集合。
- 存储（StateMachine/Log）：属性：`deterministic`、`idempotency`；关系：被 `replication` 驱动。

约束与不变量（示意）：

- Quorum 安全性：`ack_count >= required_acks(N, level)` ⇒ 提交可见。
- 线性一致需要：单领导者、日志前缀匹配、单调任期；读需防陈旧（lease/读屏障）。
- Saga 可补偿性：每一步存在幂等 `compensate`；部分失败不破坏存储不变量。

代码落点：

- `topology::ConsistentHashRing`（分片映射）；`replication::{QuorumPolicy, MajorityQuorum}`（仲裁）；
- `transactions::{Saga, SagaStep}`（补偿编排）；`storage::{StateMachineStorage, IdempotencyStore}`（确定性/幂等）。

后续将为每个概念补充：形式化定义（数学/逻辑）、可验证性质、测试/实验模版。
