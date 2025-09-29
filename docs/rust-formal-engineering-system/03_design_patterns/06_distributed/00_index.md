# 分布式模式（Distributed Patterns）索引

## 目的

- 介绍分布式系统中的设计模式在 Rust 中的实现与应用。
- 提供分布式系统设计与一致性保证的最佳实践。

## 核心模式

- 一致性哈希（Consistent Hashing）：负载均衡与分片
- 复制模式（Replication）：数据冗余与可用性
- 分片模式（Sharding）：数据分区与扩展
- 选举模式（Leader Election）：主节点选择
- 共识模式（Consensus）：分布式一致性
- 两阶段提交（Two-Phase Commit）：分布式事务
- Saga 模式（Saga Pattern）：分布式事务补偿
- 事件溯源（Event Sourcing）：状态管理
- CQRS 模式（Command Query Responsibility Segregation）：读写分离

## Rust 化要点

- 异步编程：`tokio` 异步运行时
- 消息传递：`mpsc`/`broadcast` 通道
- 序列化：`serde` 数据序列化
- 网络编程：`tokio` 网络库

## 术语（Terminology）

- 分布式模式（Distributed Patterns）
- 一致性哈希（Consistent Hashing）
- 复制（Replication）、分片（Sharding）
- 选举（Leader Election）、共识（Consensus）
- 两阶段提交（Two-Phase Commit）
- Saga 模式（Saga Pattern）、事件溯源（Event Sourcing）

## 实践与样例（Practice）

- 分布式系统：参见 [crates/c20_distributed](../../../crates/c20_distributed/)
- 网络编程：[crates/c10_networks](../../../crates/c10_networks/)
- 微服务：[crates/c13_microservice](../../../crates/c13_microservice/)

### 文件级清单（精选）

- `crates/c20_distributed/src/`：
  - `consensus_raft.rs`：Raft 共识算法
  - `consistent_hashing.rs`：一致性哈希
  - `replication.rs`：数据复制
  - `sharding.rs`：数据分片
  - `leader_election.rs`：主节点选举
- `crates/c13_microservice/src/`：
  - `distributed_transaction.rs`：分布式事务
  - `event_sourcing.rs`：事件溯源
  - `cqrs.rs`：CQRS 模式

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（异步）：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- 应用领域（云基础设施）：[`../../04_application_domains/06_cloud_infrastructure/00_index.md`](../../04_application_domains/06_cloud_infrastructure/00_index.md)

## 导航

- 返回设计模式：[`../00_index.md`](../00_index.md)
- 并发模式：[`../04_concurrent/00_index.md`](../04_concurrent/00_index.md)
- 并行模式：[`../05_parallel/00_index.md`](../05_parallel/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
