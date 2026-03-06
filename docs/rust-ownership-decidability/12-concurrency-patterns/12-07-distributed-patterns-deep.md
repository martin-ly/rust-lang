# 分布式系统模式深度解析

> **Rust版本**: 1.94
> **难度级别**: 🔴 高级
> **阅读时间**: 约4-5小时
> **覆盖范围**: 分布式系统理论、共识算法、容错模式、服务发现、Rust生态系统
> **权威参考**: *Designing Data-Intensive Applications* (Martin Kleppmann), Raft Paper, Paxos Made Simple

---

## 目录

- [分布式系统模式深度解析](#分布式系统模式深度解析)
  - [目录](#目录)
  - [1. 分布式系统理论基础](#1-分布式系统理论基础)
    - [1.1 CAP 定理形式化](#11-cap-定理形式化)
      - [形式化定义](#形式化定义)
      - [Rust 实现：CAP 策略框架](#rust-实现cap-策略框架)
      - [Counter-Example: 错误配置导致的 CAP 冲突](#counter-example-错误配置导致的-cap-冲突)
    - [1.2 网络故障模型](#12-网络故障模型)
      - [故障类型分类](#故障类型分类)
      - [Rust 的 Result 类型在分布式故障处理中的应用](#rust-的-result-类型在分布式故障处理中的应用)
  - [2. 共识模式](#2-共识模式)
    - [2.1 两阶段提交 (2PC)](#21-两阶段提交-2pc)
      - [协议流程](#协议流程)
      - [Rust 实现](#rust-实现)
      - [Counter-Example: 协调者故障导致阻塞](#counter-example-协调者故障导致阻塞)
    - [2.2 Raft 共识算法](#22-raft-共识算法)
      - [算法核心](#算法核心)
      - [Raft 安全性定理](#raft-安全性定理)
  - [3. 分布式消息传递](#3-分布式消息传递)
    - [3.1 消息序列化语义](#31-消息序列化语义)
      - [Counter-Example: 自引用类型的序列化问题](#counter-example-自引用类型的序列化问题)
    - [3.2 消息传递保证](#32-消息传递保证)
      - [Counter-Example: 重复处理问题](#counter-example-重复处理问题)
  - [4. 服务发现模式](#4-服务发现模式)
    - [4.1 注册表模式](#41-注册表模式)
      - [Counter-Example: 过期注册表条目](#counter-example-过期注册表条目)
    - [4.2 Gossip 协议](#42-gossip-协议)
  - [5. 熔断器模式](#5-熔断器模式)
    - [5.1 状态机模型](#51-状态机模型)
      - [熔断器状态机定理](#熔断器状态机定理)
    - [5.2 分布式熔断器](#52-分布式熔断器)
      - [Counter-Example: 脑裂熔断器](#counter-example-脑裂熔断器)
  - [6. 背压与流量控制](#6-背压与流量控制)
    - [6.1 负载削减](#61-负载削减)
      - [Counter-Example: 级联故障](#counter-example-级联故障)
    - [6.2 准入控制](#62-准入控制)
  - [7. 分布式追踪](#7-分布式追踪)
  - [8. 案例研究: 分布式键值存储](#8-案例研究-分布式键值存储)
  - [9. Rust 生态系统](#9-rust-生态系统)
    - [9.1 Tonic (gRPC)](#91-tonic-grpc)
    - [9.2 Tarpc](#92-tarpc)
  - [总结](#总结)

---

## 1. 分布式系统理论基础

### 1.1 CAP 定理形式化

CAP 定理指出，在分布式数据存储系统中，**一致性 (Consistency)**、**可用性 (Availability)**、**分区容错性 (Partition Tolerance)** 这三个属性最多只能同时满足其中两个。

#### 形式化定义

```text
┌─────────────────────────────────────────────────────────────────┐
│                        CAP Theorem                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   C (Consistency)                                               │
│   ∀ read operations: read(r) returns value(write(r, v))         │
│   or a later value                                              │
│                                                                 │
│   A (Availability)                                              │
│   ∀ requests: non-failing node responds without timeout         │
│                                                                 │
│   P (Partition Tolerance)                                       │
│   System continues despite network partitions                   │
│                                                                 │
│   Theorem: A distributed system can satisfy at most 2 of C, A, P│
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

#### Rust 实现：CAP 策略框架

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

/// CAP 定理的三种策略选择
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CAPStrategy {
    /// CP 系统：保证一致性和分区容错性，在网络分区时可能拒绝请求
    ///
    /// 适用场景：
    /// - 金融交易系统
    /// - 库存管理系统
    /// - 关键配置管理
    ConsistencyPartitionTolerance,

    /// AP 系统：保证可用性和分区容错性，允许数据暂时不一致
    ///
    /// 适用场景：
    /// - 社交网络 feed
    /// - 日志聚合系统
    /// - 内容分发网络
    AvailabilityPartitionTolerance,

    /// CA 系统：仅在非分布式系统或完美网络下可能
    /// ⚠️ 实际上分布式系统必须容忍分区
    #[deprecated(
        since = "1.0.0",
        note = "CA systems cannot tolerate network partitions in distributed environments"
    )]
    ConsistencyAvailability,
}

/// 一致性级别定义
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConsistencyLevel {
    /// 强一致性：线性一致性 (Linearizability)
    /// 所有操作看起来像是原子的，并且在操作完成时立即对所有节点可见
    Strong,

    /// 顺序一致性：保持操作程序顺序，但允许全局重排序
    Sequential,

    /// 因果一致性：保持因果关系，并发操作可能以不同顺序被看到
    Causal,

    /// 读己之写：客户端能看到自己的所有写操作
    ReadYourWrites,

    /// 单调读：如果客户端读取了某个值，后续读取不会看到更早的值
    MonotonicReads,

    /// 最终一致性：保证在无新更新的情况下，最终所有副本会一致
    Eventual,
}

/// CAP 配置验证器
pub struct CAPConfig {
    pub strategy: CAPStrategy,
    pub consistency_level: ConsistencyLevel,
    pub replication_factor: u32,
    pub quorum_size: Option<usize>,
}

#[derive(Debug)]
pub enum CAPError {
    InvalidConfiguration(String),
    InconsistentStrategy {
        strategy: CAPStrategy,
        consistency: ConsistencyLevel,
        reason: String,
    },
    InsufficientReplicas {
        required: usize,
        actual: usize,
    },
}

impl CAPConfig {
    /// 创建新的 CAP 配置
    pub fn new(
        strategy: CAPStrategy,
        consistency: ConsistencyLevel,
        replication_factor: u32,
    ) -> Result<Self, CAPError> {
        let config = Self {
            strategy,
            consistency_level: consistency,
            replication_factor,
            quorum_size: None,
        };
        config.validate()?;
        Ok(config)
    }

    /// 验证 CAP 配置的一致性
    ///
    /// # 形式化验证
    ///
    /// ```
    /// Theorem CAP-VALIDITY:
    ///   ∀ config: CAPConfig |
    ///     config.strategy = CP → config.consistency ≠ Eventual
    ///     ∧
    ///     config.consistency = Eventual → config.strategy ≠ CP
    /// ```
    pub fn validate(&self) -> Result<(), CAPError> {
        // 检查策略与一致性级别的兼容性
        match (self.strategy, self.consistency_level) {
            (CAPStrategy::ConsistencyPartitionTolerance, ConsistencyLevel::Eventual) => {
                return Err(CAPError::InconsistentStrategy {
                    strategy: self.strategy,
                    consistency: self.consistency_level,
                    reason: "CP systems should not use eventual consistency".to_string(),
                });
            }
            (CAPStrategy::AvailabilityPartitionTolerance, ConsistencyLevel::Strong) => {
                // 警告：AP 系统中使用强一致性会降低可用性
                tracing::warn!(
                    "Strong consistency in AP system may impact availability during partitions"
                );
            }
            _ => {}
        }

        // 检查复制因子
        if self.replication_factor < 1 {
            return Err(CAPError::InvalidConfiguration(
                "Replication factor must be at least 1".to_string(),
            ));
        }

        // CP 系统需要计算仲裁数
        if matches!(self.strategy, CAPStrategy::ConsistencyPartitionTolerance) {
            let quorum = (self.replication_factor as usize / 2) + 1;
            if self.replication_factor as usize > 1 && quorum < 2 {
                return Err(CAPError::InsufficientReplicas {
                    required: 2,
                    actual: self.replication_factor as usize,
                });
            }
        }

        Ok(())
    }

    /// 计算写入仲裁数
    pub fn write_quorum(&self) -> usize {
        match self.strategy {
            CAPStrategy::ConsistencyPartitionTolerance => {
                (self.replication_factor as usize / 2) + 1
            }
            _ => 1, // AP 系统可以异步复制
        }
    }

    /// 计算读取仲裁数
    pub fn read_quorum(&self) -> usize {
        match self.strategy {
            CAPStrategy::ConsistencyPartitionTolerance => {
                (self.replication_factor as usize / 2) + 1
            }
            _ => 1,
        }
    }
}

/// CAP 策略选择器 - 根据场景推荐最佳策略
pub struct CAPSelector;

impl CAPSelector {
    /// 根据业务场景选择 CAP 策略
    pub fn select(scenario: Scenario) -> CAPConfig {
        match scenario {
            Scenario::FinancialTransaction => CAPConfig {
                strategy: CAPStrategy::ConsistencyPartitionTolerance,
                consistency_level: ConsistencyLevel::Strong,
                replication_factor: 5,
                quorum_size: Some(3),
            },
            Scenario::InventoryManagement => CAPConfig {
                strategy: CAPStrategy::ConsistencyPartitionTolerance,
                consistency_level: ConsistencyLevel::Strong,
                replication_factor: 3,
                quorum_size: Some(2),
            },
            Scenario::SocialFeed => CAPConfig {
                strategy: CAPStrategy::AvailabilityPartitionTolerance,
                consistency_level: ConsistencyLevel::Eventual,
                replication_factor: 3,
                quorum_size: None,
            },
            Scenario::SessionStore => CAPConfig {
                strategy: CAPStrategy::AvailabilityPartitionTolerance,
                consistency_level: ConsistencyLevel::ReadYourWrites,
                replication_factor: 2,
                quorum_size: None,
            },
            Scenario::ConfigManagement => CAPConfig {
                strategy: CAPStrategy::ConsistencyPartitionTolerance,
                consistency_level: ConsistencyLevel::Strong,
                replication_factor: 3,
                quorum_size: Some(2),
            },
        }
    }
}

#[derive(Debug)]
pub enum Scenario {
    FinancialTransaction,
    InventoryManagement,
    SocialFeed,
    SessionStore,
    ConfigManagement,
}
```

#### Counter-Example: 错误配置导致的 CAP 冲突

```rust
/// ❌ Counter-Example: 违反 CAP 原则的配置
///
/// 问题：在 CP 系统中使用最终一致性会导致
/// 数据不一致的隐患
#[allow(dead_code)]
fn bad_cap_config() -> Result<CAPConfig, CAPError> {
    // 错误：CP 系统要求强一致性
    CAPConfig::new(
        CAPStrategy::ConsistencyPartitionTolerance,
        ConsistencyLevel::Eventual, // ❌ 错误：CP 系统不能使用最终一致性
        3,
    )
}

/// ✅ 正确的 CP 系统配置
fn good_cp_config() -> Result<CAPConfig, CAPError> {
    CAPConfig::new(
        CAPStrategy::ConsistencyPartitionTolerance,
        ConsistencyLevel::Strong, // ✅ 正确：CP 系统使用强一致性
        3,
    )
}
```

### 1.2 网络故障模型

分布式系统中的故障比单机系统复杂得多。理解故障模型是设计容错系统的基础。

#### 故障类型分类

```rust
use std::time::{Duration, Instant};
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;

/// 分布式系统故障模型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FailureType {
    /// 崩溃停止故障 (Crash-Stop)
    /// 节点崩溃后永久停止
    CrashStop,

    /// 崩溃恢复故障 (Crash-Recovery)
    /// 节点崩溃后可能恢复，可能丢失内存状态
    CrashRecovery,

    /// 遗漏故障 (Omission)
    /// 节点偶尔不响应请求或发送消息
    Omission,

    /// 时序故障 (Timing)
    /// 响应时间超出预期
    Timing { expected: Duration, actual: Duration },

    /// 响应故障 (Response)
    /// 返回错误响应
    Response,

    /// 任意故障 (Byzantine)
    /// 节点可能发送任意错误信息，包括恶意行为
    Byzantine,
}

/// 故障检测器 - 基于超时机制
pub struct FailureDetector {
    /// 心跳超时时间
    heartbeat_timeout: Duration,
    /// 怀疑阈值
    suspicion_threshold: u32,
    /// 节点状态表
    node_states: Arc<RwLock<HashMap<NodeId, NodeStatus>>>,
    /// 最后一次心跳时间
    last_heartbeat: Arc<RwLock<HashMap<NodeId, Instant>>>,
}

#[derive(Debug, Clone)]
pub struct NodeStatus {
    pub state: NodeState,
    pub suspicion_level: u32,
    pub last_updated: Instant,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeState {
    Healthy,
    Suspected,
    Failed,
    Unknown,
}

pub type NodeId = String;

impl FailureDetector {
    pub fn new(
        heartbeat_timeout: Duration,
        suspicion_threshold: u32,
    ) -> Self {
        Self {
            heartbeat_timeout,
            suspicion_threshold,
            node_states: Arc::new(RwLock::new(HashMap::new())),
            last_heartbeat: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 报告心跳
    pub async fn heartbeat(&self, node_id: NodeId) {
        let mut states = self.node_states.write().await;
        let mut heartbeats = self.last_heartbeat.write().await;

        heartbeats.insert(node_id.clone(), Instant::now());
        states.insert(node_id, NodeStatus {
            state: NodeState::Healthy,
            suspicion_level: 0,
            last_updated: Instant::now(),
        });
    }

    /// 检查节点状态（基于 Phi Accrual 算法简化）
    pub async fn check_node(&self, node_id: &NodeId) -> NodeState {
        let mut states = self.node_states.write().await;
        let heartbeats = self.last_heartbeat.read().await;

        if let Some(last) = heartbeats.get(node_id) {
            let elapsed = last.elapsed();

            if elapsed < self.heartbeat_timeout {
                states.get(node_id)
                    .map(|s| s.state)
                    .unwrap_or(NodeState::Healthy)
            } else if elapsed < self.heartbeat_timeout * 2 {
                // 怀疑阶段
                if let Some(status) = states.get_mut(node_id) {
                    if status.state == NodeState::Healthy {
                        status.state = NodeState::Suspected;
                        status.suspicion_level = 1;
                    } else if status.suspicion_level < self.suspicion_threshold {
                        status.suspicion_level += 1;
                    } else {
                        status.state = NodeState::Failed;
                    }
                    status.state
                } else {
                    NodeState::Suspected
                }
            } else {
                // 超时，标记为失败
                if let Some(status) = states.get_mut(node_id) {
                    status.state = NodeState::Failed;
                    status.state
                } else {
                    NodeState::Failed
                }
            }
        } else {
            NodeState::Unknown
        }
    }

    /// 获取所有健康节点
    pub async fn healthy_nodes(&self) -> Vec<NodeId> {
        let states = self.node_states.read().await;
        states
            .iter()
            .filter(|(_, status)| matches!(status.state, NodeState::Healthy))
            .map(|(id, _)| id.clone())
            .collect()
    }
}
```

#### Rust 的 Result 类型在分布式故障处理中的应用

```rust
use thiserror::Error;

/// 分布式操作错误类型
#[derive(Error, Debug, Clone)]
pub enum DistributedError {
    #[error("Network partition detected: {partition_id}")]
    NetworkPartition { partition_id: String },

    #[error("Node {node_id} failed: {reason}")]
    NodeFailure { node_id: String, reason: String },

    #[error("Timeout after {duration:?}: {operation}")]
    Timeout { duration: Duration, operation: String },

    #[error("Consensus not reached: {details}")]
    ConsensusFailure { details: String },

    #[error("Quorum not reached: {received}/{required}")]
    QuorumFailure { received: usize, required: usize },

    #[error("Version conflict: expected {expected}, found {actual}")]
    VersionConflict { expected: u64, actual: u64 },

    #[error("Serialization error: {0}")]
    Serialization(String),

    #[error("Byzantine fault detected: {node_id}")]
    ByzantineFault { node_id: String },
}

/// 分布式操作结果类型
pub type DistributedResult<T> = Result<T, DistributedError>;

/// 带重试的分布式操作
pub async fn with_retry<F, Fut, T>(
    operation: F,
    max_retries: u32,
    base_delay: Duration,
) -> DistributedResult<T>
where
    F: Fn() -> Fut,
    Fut: std::future::Future<Output = DistributedResult<T>>,
{
    let mut last_error = None;

    for attempt in 0..max_retries {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                // 某些错误不应该重试
                if matches!(e, DistributedError::ByzantineFault { .. }) {
                    return Err(e);
                }

                last_error = Some(e);
                let delay = base_delay * 2_u32.pow(attempt);
                tokio::time::sleep(delay).await;
            }
        }
    }

    Err(last_error.unwrap_or_else(|| {
        DistributedError::Timeout {
            duration: base_delay * max_retries,
            operation: "retry loop".to_string(),
        }
    }))
}
```

---

## 2. 共识模式

### 2.1 两阶段提交 (2PC)

两阶段提交是一种经典的分布式事务协议，确保跨多个节点的操作要么全部成功，要么全部失败。

#### 协议流程

```text
Coordinator                    Participants
     |                             |
     |-------- PREPARE ----------->|  Phase 1: 准备阶段
     |                             |  - 执行本地事务
     |                             |  - 写 undo/redo 日志
     |<------- YES/NO ------------|  - 锁定资源
     |                             |
     |  If all YES:                |
     |-------- COMMIT ----------->|  Phase 2: 提交阶段
     |<------- ACK ---------------|  - 提交本地事务
     |                             |  - 释放锁
     |  If any NO:                 |
     |-------- ROLLBACK --------->|  - 回滚本地事务
     |<------- ACK ---------------|
```

#### Rust 实现

```rust
use std::collections::HashMap;
use tokio::sync::{mpsc, oneshot};
use std::time::Duration;

/// 两阶段提交协调器
pub struct TwoPhaseCoordinator {
    participants: Vec<ParticipantHandle>,
    transaction_log: Arc<RwLock<TransactionLog>>,
}

#[derive(Clone)]
struct ParticipantHandle {
    id: String,
    sender: mpsc::Sender<CoordinatorMessage>,
}

#[derive(Debug)]
enum CoordinatorMessage {
    Prepare { tx_id: String, operation: Operation },
    Commit { tx_id: String },
    Rollback { tx_id: String },
}

#[derive(Debug, Clone)]
pub enum Operation {
    Insert { key: String, value: Vec<u8> },
    Update { key: String, value: Vec<u8>, version: u64 },
    Delete { key: String },
}

#[derive(Debug)]
enum ParticipantResponse {
    Prepared { tx_id: String },
    PrepareFailed { tx_id: String, reason: String },
    Committed { tx_id: String },
    Aborted { tx_id: String },
}

#[derive(Debug)]
enum TransactionState {
    Preparing,
    Prepared,
    Committing,
    Committed,
    Aborting,
    Aborted,
}

struct TransactionLog {
    transactions: HashMap<String, TransactionRecord>,
}

struct TransactionRecord {
    tx_id: String,
    state: TransactionState,
    participants: Vec<String>,
    votes: HashMap<String, bool>,
}

impl TwoPhaseCoordinator {
    pub fn new() -> Self {
        Self {
            participants: Vec::new(),
            transaction_log: Arc::new(RwLock::new(TransactionLog {
                transactions: HashMap::new(),
            })),
        }
    }

    /// 执行两阶段提交
    ///
    /// # 所有权流程
    /// 1. 协调器创建事务记录（所有权）
    /// 2. 向参与者发送 PREPARE（借用检查）
    /// 3. 收集响应（聚合所有权）
    /// 4. 决定提交或回滚（所有权转移）
    pub async fn execute_transaction(
        &self,
        tx_id: String,
        operation: Operation,
    ) -> Result<(), TransactionError> {
        // Phase 1: Prepare
        let prepared = self.phase_one_prepare(&tx_id, &operation).await?;

        if prepared {
            // Phase 2: Commit
            self.phase_two_commit(&tx_id).await
        } else {
            // Phase 2: Rollback
            self.phase_two_rollback(&tx_id).await?;
            Err(TransactionError::PrepareFailed)
        }
    }

    async fn phase_one_prepare(
        &self,
        tx_id: &str,
        operation: &Operation,
    ) -> Result<bool, TransactionError> {
        let mut prepared_count = 0;
        let total = self.participants.len();

        // 并行发送 PREPARE 请求
        let prepare_futures: Vec<_> = self
            .participants
            .iter()
            .map(|p| {
                let msg = CoordinatorMessage::Prepare {
                    tx_id: tx_id.to_string(),
                    operation: operation.clone(),
                };
                let sender = p.sender.clone();
                async move {
                    let (tx, rx) = oneshot::channel();
                    sender.send(msg).await.ok();
                    tokio::time::timeout(Duration::from_secs(5), rx).await
                }
            })
            .collect();

        let results = futures::future::join_all(prepare_futures).await;

        for result in results {
            match result {
                Ok(Ok(ParticipantResponse::Prepared { .. })) => {
                    prepared_count += 1;
                }
                Ok(Ok(ParticipantResponse::PrepareFailed { reason, .. })) => {
                    tracing::warn!("Participant prepare failed: {}", reason);
                    return Ok(false);
                }
                Ok(Err(_)) | Err(_) => {
                    return Ok(false);
                }
                _ => {}
            }
        }

        Ok(prepared_count == total)
    }

    async fn phase_two_commit(&self, tx_id: &str) -> Result<(), TransactionError> {
        // 先写本地日志（WAL 原则）
        {
            let mut log = self.transaction_log.write().await;
            if let Some(tx) = log.transactions.get_mut(tx_id) {
                tx.state = TransactionState::Committing;
            }
        }

        // 向所有参与者发送 COMMIT
        let commit_futures: Vec<_> = self
            .participants
            .iter()
            .map(|p| {
                let msg = CoordinatorMessage::Commit {
                    tx_id: tx_id.to_string(),
                };
                let sender = p.sender.clone();
                async move {
                    sender.send(msg).await.ok();
                }
            })
            .collect();

        futures::future::join_all(commit_futures).await;

        // 更新日志状态
        {
            let mut log = self.transaction_log.write().await;
            if let Some(tx) = log.transactions.get_mut(tx_id) {
                tx.state = TransactionState::Committed;
            }
        }

        Ok(())
    }

    async fn phase_two_rollback(&self, tx_id: &str) -> Result<(), TransactionError> {
        let rollback_futures: Vec<_> = self
            .participants
            .iter()
            .map(|p| {
                let msg = CoordinatorMessage::Rollback {
                    tx_id: tx_id.to_string(),
                };
                let sender = p.sender.clone();
                async move {
                    sender.send(msg).await.ok();
                }
            })
            .collect();

        futures::future::join_all(rollback_futures).await;

        {
            let mut log = self.transaction_log.write().await;
            if let Some(tx) = log.transactions.get_mut(tx_id) {
                tx.state = TransactionState::Aborted;
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
pub enum TransactionError {
    PrepareFailed,
    CommitFailed(String),
    RollbackFailed(String),
    Timeout,
    CoordinatorFailure,
}
```

#### Counter-Example: 协调者故障导致阻塞

```rust
/// ❌ Counter-Example: 协调者单点故障问题
///
/// 问题：如果在 Phase 2 期间协调者崩溃，
/// 参与者会一直持有锁等待协调者恢复
///
/// 解决方案：使用三阶段提交 (3PC) 或 Paxos/Raft
#[derive(Debug)]
pub struct CoordinatorFailureScenario;

impl CoordinatorFailureScenario {
    /// 模拟协调者故障
    pub fn demonstrate_blocking_problem() {
        // 场景：
        // 1. 协调者发送了 PREPARE
        // 2. 所有参与者回复了 YES
        // 3. 协调者在发送 COMMIT 前崩溃
        // 4. 参与者持有锁，等待 COMMIT 或 ROLLBACK
        // 5. 其他事务无法访问被锁定的资源

        // 在 2PC 中，参与者无法单方面决定是提交还是回滚
        // 因为协调者可能已经向部分参与者发送了 COMMIT

        // 解决方案：
        // 1. 超时机制（可能导致不一致）
        // 2. 协调者恢复后重放日志
        // 3. 使用 3PC（增加 CanCommit 阶段）
        // 4. 使用共识算法（Paxos/Raft）替代 2PC
    }
}

/// 参与者超时处理（不完美解决方案）
pub struct ParticipantWithTimeout {
    tx_state: HashMap<String, ParticipantTxState>,
    timeout: Duration,
}

#[derive(Debug)]
enum ParticipantTxState {
    Prepared { since: Instant },
    Committed,
    Aborted,
}

impl ParticipantWithTimeout {
    /// 检查超时并做出决策
    /// ⚠️ 注意：这可能导致不一致
    pub async fn check_timeout(&mut self, tx_id: &str) -> TimeoutDecision {
        if let Some(state) = self.tx_state.get(tx_id) {
            if let ParticipantTxState::Prepared { since } = state {
                if since.elapsed() > self.timeout {
                    self.tx_state.insert(
                        tx_id.to_string(),
                        ParticipantTxState::Aborted,
                    );
                    return TimeoutDecision::Rollback;
                }
            }
        }
        TimeoutDecision::Wait
    }
}

enum TimeoutDecision {
    Wait,
    Rollback, // ⚠️ 可能导致不一致
}
```

### 2.2 Raft 共识算法

Raft 是一种为可理解性设计的共识算法。它将共识问题分解为三个子问题：领导者选举、日志复制和安全性。

#### 算法核心

```rust
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tokio::sync::{RwLock, mpsc};
use std::time::{Duration, Instant};

/// Raft 节点状态机
#[derive(Debug, Clone, PartialEq)]
pub enum RaftState {
    Follower {
        leader: Option<NodeId>,
        voted_for: Option<NodeId>,
    },
    Candidate {
        votes_received: HashSet<NodeId>,
        election_start: Instant,
    },
    Leader {
        next_index: HashMap<NodeId, LogIndex>,
        match_index: HashMap<NodeId, LogIndex>,
    },
}

pub type NodeId = String;
pub type LogIndex = u64;
pub type Term = u64;

/// 日志条目
#[derive(Debug, Clone, PartialEq)]
pub struct LogEntry {
    pub term: Term,
    pub index: LogIndex,
    pub command: Vec<u8>,
    pub respond_to: Option<tokio::sync::oneshot::Sender<ClientResponse>>,
}

/// Raft 节点核心结构
pub struct RaftNode {
    id: NodeId,
    state: Arc<RwLock<RaftState>>,
    current_term: Arc<RwLock<Term>>,
    voted_for: Arc<RwLock<Option<NodeId>>>,
    log: Arc<RwLock<Vec<LogEntry>>>,
    commit_index: Arc<RwLock<LogIndex>>,
    last_applied: Arc<RwLock<LogIndex>>,
    peers: Vec<NodeId>,
    msg_tx: mpsc::Sender<RaftMessage>,
    election_config: ElectionConfig,
}

#[derive(Debug, Clone)]
pub enum RaftMessage {
    RequestVote {
        term: Term,
        candidate_id: NodeId,
        last_log_index: LogIndex,
        last_log_term: Term,
    },
    RequestVoteResponse {
        term: Term,
        vote_granted: bool,
        voter_id: NodeId,
    },
    AppendEntries {
        term: Term,
        leader_id: NodeId,
        prev_log_index: LogIndex,
        prev_log_term: Term,
        entries: Vec<LogEntry>,
        leader_commit: LogIndex,
    },
    AppendEntriesResponse {
        term: Term,
        success: bool,
        node_id: NodeId,
        match_index: LogIndex,
    },
    ClientRequest {
        command: Vec<u8>,
        respond_to: tokio::sync::oneshot::Sender<ClientResponse>,
    },
}

#[derive(Debug, Clone)]
pub enum ClientResponse {
    Success { result: Vec<u8> },
    NotLeader { leader_hint: Option<NodeId> },
    Timeout,
    CommitFailed(String),
}

#[derive(Debug, Clone)]
pub struct ElectionConfig {
    pub min_timeout_ms: u64,
    pub max_timeout_ms: u64,
    pub heartbeat_interval_ms: u64,
}

impl Default for ElectionConfig {
    fn default() -> Self {
        Self {
            min_timeout_ms: 150,
            max_timeout_ms: 300,
            heartbeat_interval_ms: 50,
        }
    }
}

impl RaftNode {
    pub fn new(id: NodeId, peers: Vec<NodeId>, config: ElectionConfig) -> Self {
        let (msg_tx, _msg_rx) = mpsc::channel(1000);

        Self {
            id: id.clone(),
            state: Arc::new(RwLock::new(RaftState::Follower {
                leader: None,
                voted_for: None,
            })),
            current_term: Arc::new(RwLock::new(0)),
            voted_for: Arc::new(RwLock::new(None)),
            log: Arc::new(RwLock::new(vec![])),
            commit_index: Arc::new(RwLock::new(0)),
            last_applied: Arc::new(RwLock::new(0)),
            peers,
            msg_tx,
            election_config: config,
        }
    }

    /// 处理请求投票 RPC
    pub async fn handle_request_vote(&self, req: RaftMessage) -> RaftMessage {
        match req {
            RaftMessage::RequestVote {
                term,
                candidate_id,
                last_log_index,
                last_log_term,
            } => {
                let mut current_term = self.current_term.write().await;
                let mut voted_for = self.voted_for.write().await;
                let log = self.log.read().await;

                if term > *current_term {
                    *current_term = term;
                    *voted_for = None;
                }

                let can_vote = term >= *current_term
                    && (voted_for.is_none() || voted_for.as_ref() == Some(&candidate_id))
                    && self.is_log_up_to_date(&log, last_log_index, last_log_term);

                if can_vote {
                    *voted_for = Some(candidate_id.clone());
                }

                RaftMessage::RequestVoteResponse {
                    term: *current_term,
                    vote_granted: can_vote,
                    voter_id: self.id.clone(),
                }
            }
            _ => panic!("Expected RequestVote message"),
        }
    }

    /// 处理追加日志 RPC
    pub async fn handle_append_entries(&self, req: RaftMessage) -> RaftMessage {
        match req {
            RaftMessage::AppendEntries {
                term,
                leader_id,
                prev_log_index,
                prev_log_term,
                entries,
                leader_commit,
            } => {
                let mut current_term = self.current_term.write().await;
                let mut state = self.state.write().await;
                let mut log = self.log.write().await;
                let mut commit_index = self.commit_index.write().await;

                if term > *current_term {
                    *current_term = term;
                    *state = RaftState::Follower {
                        leader: Some(leader_id.clone()),
                        voted_for: None,
                    };
                }

                if term < *current_term {
                    return RaftMessage::AppendEntriesResponse {
                        term: *current_term,
                        success: false,
                        node_id: self.id.clone(),
                        match_index: 0,
                    };
                }

                // 检查前置日志条目
                let log_ok = if prev_log_index == 0 {
                    true
                } else if prev_log_index > log.len() as u64 {
                    false
                } else {
                    log.get((prev_log_index - 1) as usize)
                        .map(|e| e.term == prev_log_term)
                        .unwrap_or(false)
                };

                if !log_ok {
                    return RaftMessage::AppendEntriesResponse {
                        term: *current_term,
                        success: false,
                        node_id: self.id.clone(),
                        match_index: 0,
                    };
                }

                // 追加新条目
                for entry in entries {
                    let idx = entry.index as usize;
                    if idx <= log.len() {
                        if log.get(idx - 1).map(|e| e.term) != Some(entry.term) {
                            log.truncate(idx - 1);
                        } else {
                            continue;
                        }
                    }
                    log.push(entry);
                }

                if leader_commit > *commit_index {
                    *commit_index = leader_commit.min(log.len() as u64);
                }

                RaftMessage::AppendEntriesResponse {
                    term: *current_term,
                    success: true,
                    node_id: self.id.clone(),
                    match_index: log.len() as u64,
                }
            }
            _ => panic!("Expected AppendEntries message"),
        }
    }

    fn is_log_up_to_date(&self, log: &[LogEntry], last_index: LogIndex, last_term: Term) -> bool {
        let my_last_term = log.last().map(|e| e.term).unwrap_or(0);
        let my_last_index = log.len() as u64;
        last_term > my_last_term || (last_term == my_last_term && last_index >= my_last_index)
    }

    pub async fn replicate_log(&self, entry: LogEntry) -> Result<(), String> {
        // 简化的日志复制实现
        let mut log = self.log.write().await;
        log.push(entry);
        Ok(())
    }
}
```

#### Raft 安全性定理

```text
┌─────────────────────────────────────────────────────────────────┐
│                    Raft Safety Properties                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Theorem ELECTION-SAFETY:                                       │
│    At most one leader can be elected in a given term.           │
│                                                                 │
│  Proof Sketch:                                                  │
│    - A node votes at most once per term                         │
│    - Candidate needs majority votes                             │
│    - Two different majorities must overlap                      │
│    - Overlapping node cannot vote twice                         │
│    ∴ At most one leader per term                                │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Theorem LOG-MATCHING:                                          │
│    If two entries have same index and term, then:               │
│    (1) They store the same command                              │
│    (2) The logs are identical in all preceding entries          │
│                                                                 │
│  Proof: By induction on index, maintained by AppendEntries RPC  │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Theorem LEADER-COMPLETENESS:                                   │
│    If a log entry is committed in a given term,                 │
│    then that entry will be present in the logs of the           │
│    leaders for all higher-numbered terms.                       │
│                                                                 │
│  Proof: By contradiction using Log Matching Property            │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 3. 分布式消息传递

### 3.1 消息序列化语义

```rust
use serde::{Serialize, Deserialize};

/// 分布式消息 trait
pub trait DistributedMessage: Serialize + for<'de> Deserialize<'de> + Send + 'static {
    fn message_type() -> &'static str;
    fn validate(&self) -> Result<(), ValidationError>;
}

/// 请求消息示例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RequestMessage<T> {
    pub request_id: uuid::Uuid,
    pub sender_id: String,
    pub timestamp: u64,
    pub payload: T,
    pub sequence_number: u64,
}

/// 响应消息示例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResponseMessage<T> {
    pub request_id: uuid::Uuid,
    pub sender_id: String,
    pub timestamp: u64,
    pub result: Result<T, RpcError>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RpcError {
    Timeout,
    ServiceUnavailable,
    InvalidRequest(String),
    InternalError(String),
}
```

#### Counter-Example: 自引用类型的序列化问题

```rust
/// ❌ Counter-Example: 尝试序列化自引用结构
#[derive(Debug)]
pub struct SelfReferential<'a> {
    data: String,
    pointer: *const String,
    _marker: std::marker::PhantomData<&'a String>,
}

impl<'a> SelfReferential<'a> {
    pub fn new(data: String) -> Self {
        let pointer = &data as *const String;
        Self { data, pointer, _marker: std::marker::PhantomData }
    }
}

/// ✅ 解决方案：使用索引代替指针
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SafeSelfReferential {
    data: String,
    start_index: usize,
    end_index: usize,
}

impl SafeSelfReferential {
    pub fn new(data: String) -> Self {
        let len = data.len();
        Self { data, start_index: 0, end_index: len }
    }

    pub fn get_substring(&self) -> &str {
        &self.data[self.start_index..self.end_index]
    }
}
```

### 3.2 消息传递保证

```rust
use std::collections::HashSet;
use std::sync::Arc;
use tokio::sync::{RwLock, mpsc};
use std::time::Duration;

/// 至少一次消息传递器
pub struct AtLeastOnceDelivery {
    pending: Arc<RwLock<HashMap<MessageId, PendingMessage>>>,
    processed: Arc<RwLock<HashSet<MessageId>>>,
    retry_config: RetryConfig,
    sender: mpsc::Sender<NetworkMessage>,
}

#[derive(Debug, Clone)]
struct PendingMessage {
    id: MessageId,
    payload: Vec<u8>,
    recipient: String,
    attempts: u32,
    last_sent: std::time::Instant,
}

#[derive(Debug, Clone)]
pub struct RetryConfig {
    pub max_retries: u32,
    pub base_delay_ms: u64,
    pub max_delay_ms: u64,
}

pub type MessageId = uuid::Uuid;

impl AtLeastOnceDelivery {
    pub async fn send(&self, recipient: String, payload: Vec<u8>) -> Result<MessageId, DeliveryError> {
        let id = uuid::Uuid::new_v4();

        let pending = PendingMessage {
            id,
            payload: payload.clone(),
            recipient: recipient.clone(),
            attempts: 0,
            last_sent: std::time::Instant::now(),
        };

        {
            let mut pending_map = self.pending.write().await;
            pending_map.insert(id, pending);
        }

        let network_msg = NetworkMessage {
            id,
            recipient,
            payload,
            requires_ack: true,
        };

        self.sender.send(network_msg).await
            .map_err(|_| DeliveryError::ChannelClosed)?;

        self.spawn_retry_task(id);
        Ok(id)
    }

    fn spawn_retry_task(&self, id: MessageId) {
        let pending = self.pending.clone();
        let config = self.retry_config.clone();
        let sender = self.sender.clone();

        tokio::spawn(async move {
            loop {
                tokio::time::sleep(Duration::from_millis(config.base_delay_ms)).await;

                let should_retry = {
                    let map = pending.read().await;
                    if let Some(msg) = map.get(&id) {
                        msg.attempts < config.max_retries
                    } else {
                        return;
                    }
                };

                if !should_retry {
                    pending.write().await.remove(&id);
                    return;
                }
            }
        });
    }
}

#[derive(Debug)]
pub enum DeliveryError {
    ChannelClosed,
    Timeout,
    MaxRetriesExceeded,
}

#[derive(Debug, Clone)]
struct NetworkMessage {
    id: MessageId,
    recipient: String,
    payload: Vec<u8>,
    requires_ack: bool,
}
```

#### Counter-Example: 重复处理问题

```rust
/// ❌ Counter-Example: 非幂等的重复消息处理
pub struct NonIdempotentProcessor {
    balance: AtomicI64,
}

impl NonIdempotentProcessor {
    /// ❌ 危险：转账操作没有幂等保护
    pub async fn process_transfer(&self, transfer: TransferMessage) {
        let current = self.balance.load(Ordering::SeqCst);
        if current >= transfer.amount {
            self.balance.fetch_sub(transfer.amount, Ordering::SeqCst);
        }
    }
}

/// 转账消息
#[derive(Debug, Clone)]
pub struct TransferMessage {
    pub from_account: String,
    pub to_account: String,
    pub amount: i64,
    pub message_id: uuid::Uuid,
}

/// ✅ 解决方案：幂等处理器
pub struct IdempotentProcessor {
    balance: AtomicI64,
    processed_ids: Arc<RwLock<HashSet<uuid::Uuid>>>,
}

impl IdempotentProcessor {
    /// ✅ 安全：幂等处理
    pub async fn process_transfer(&self, transfer: TransferMessage) -> Result<(), TransferError> {
        {
            let processed = self.processed_ids.read().await;
            if processed.contains(&transfer.message_id) {
                return Ok(());
            }
        }

        let current = self.balance.load(Ordering::SeqCst);
        if current < transfer.amount {
            return Err(TransferError::InsufficientFunds);
        }

        self.balance.fetch_sub(transfer.amount, Ordering::SeqCst);

        {
            let mut processed = self.processed_ids.write().await;
            processed.insert(transfer.message_id);
        }

        Ok(())
    }
}

#[derive(Debug)]
pub enum TransferError {
    InsufficientFunds,
    AccountNotFound,
}

use std::sync::atomic::{AtomicI64, Ordering};
```

---

## 4. 服务发现模式

### 4.1 注册表模式

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};

/// 服务注册表
pub struct ServiceRegistry {
    services: Arc<RwLock<HashMap<ServiceName, Vec<ServiceInstance>>>>,
    health_config: HealthCheckConfig,
    subscribers: Arc<RwLock<HashMap<ServiceName, Vec<mpsc::Sender<RegistryEvent>>>>>,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct ServiceName(pub String);

#[derive(Debug, Clone)]
pub struct ServiceInstance {
    pub id: String,
    pub service_name: ServiceName,
    pub address: String,
    pub port: u16,
    pub metadata: HashMap<String, String>,
    pub health_status: HealthStatus,
    pub last_heartbeat: Instant,
    pub registered_at: Instant,
    pub ttl: Duration,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct HealthCheckConfig {
    pub check_interval: Duration,
    pub timeout: Duration,
    pub unhealthy_threshold: u32,
    pub healthy_threshold: u32,
}

#[derive(Debug, Clone)]
pub enum RegistryEvent {
    ServiceRegistered(ServiceInstance),
    ServiceDeregistered(String),
    HealthStatusChanged { instance_id: String, new_status: HealthStatus },
}

use tokio::sync::mpsc;

impl ServiceRegistry {
    pub fn new(health_config: HealthCheckConfig) -> Self {
        let registry = Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            health_config,
            subscribers: Arc::new(RwLock::new(HashMap::new())),
        };
        registry.spawn_health_check_task();
        registry
    }

    pub async fn register(&self, instance: ServiceInstance) -> Result<(), RegistryError> {
        let mut services = self.services.write().await;

        let instances = services
            .entry(instance.service_name.clone())
            .or_insert_with(Vec::new);

        if instances.iter().any(|i| i.id == instance.id) {
            return Err(RegistryError::DuplicateInstance(instance.id));
        }

        instances.push(instance.clone());
        self.notify_subscribers(&instance.service_name, RegistryEvent::ServiceRegistered(instance)).await;
        Ok(())
    }

    pub async fn discover(&self, service_name: &ServiceName) -> Vec<ServiceInstance> {
        let services = self.services.read().await;

        if let Some(instances) = services.get(service_name) {
            instances
                .iter()
                .filter(|i| matches!(i.health_status, HealthStatus::Healthy))
                .cloned()
                .collect()
        } else {
            Vec::new()
        }
    }

    fn spawn_health_check_task(&self) {
        let services = self.services.clone();
        let config = self.health_config.clone();
        let subscribers = self.subscribers.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.check_interval);

            loop {
                interval.tick().await;

                let mut services_guard = services.write().await;
                let now = Instant::now();

                for (service_name, instances) in services_guard.iter_mut() {
                    instances.retain(|instance| {
                        let is_expired = now.duration_since(instance.last_heartbeat) > instance.ttl;
                        if is_expired {
                            let _ = async {
                                let subs = subscribers.read().await;
                                if let Some(senders) = subs.get(service_name) {
                                    for sender in senders {
                                        let _ = sender.send(RegistryEvent::ServiceDeregistered(instance.id.clone())).await;
                                    }
                                }
                            };
                        }
                        !is_expired
                    });
                }
            }
        });
    }

    async fn notify_subscribers(&self, service_name: &ServiceName, event: RegistryEvent) {
        let subscribers = self.subscribers.read().await;
        if let Some(senders) = subscribers.get(service_name) {
            for sender in senders {
                let _ = sender.send(event.clone()).await;
            }
        }
    }
}

#[derive(Debug)]
pub enum RegistryError {
    DuplicateInstance(String),
    InstanceNotFound(String),
    StorageError(String),
}
```

#### Counter-Example: 过期注册表条目

```rust
/// ❌ Counter-Example: 未清理的过期服务实例
pub struct StaleRegistryProblem;

impl StaleRegistryProblem {
    pub fn demonstrate() {
        // 场景：
        // 1. Service A 注册到注册表
        // 2. Service A 崩溃（未发送注销请求）
        // 3. 注册表仍保留 Service A 的信息
        // 4. 客户端查询到 Service A，尝试连接失败
    }
}

/// ✅ 解决方案：TTL + 心跳机制
#[derive(Debug, Clone)]
pub struct TtlBasedRegistry {
    instances: Arc<RwLock<HashMap<String, (ServiceInstance, Instant)>>>,
    default_ttl: Duration,
}

impl TtlBasedRegistry {
    pub async fn register_with_ttl(&self, mut instance: ServiceInstance) -> Result<(), RegistryError> {
        instance.last_heartbeat = Instant::now();
        instance.ttl = self.default_ttl;

        let mut instances = self.instances.write().await;
        let expiry = Instant::now() + self.default_ttl;
        instances.insert(instance.id.clone(), (instance, expiry));
        Ok(())
    }

    pub fn spawn_cleanup_task(&self) {
        let instances = self.instances.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(10));

            loop {
                interval.tick().await;

                let now = Instant::now();
                let mut guard = instances.write().await;

                guard.retain(|id, (_, expiry)| {
                    let is_valid = *expiry > now;
                    if !is_valid {
                        tracing::info!("Cleaning up expired instance: {}", id);
                    }
                    is_valid
                });
            }
        });
    }
}
```

### 4.2 Gossip 协议

```rust
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};

/// Gossip 协议实现
pub struct GossipProtocol {
    node_id: NodeId,
    membership: Arc<RwLock<MembershipList>>,
    config: GossipConfig,
    sequence_number: Arc<RwLock<u64>>,
}

#[derive(Debug, Clone)]
pub struct GossipConfig {
    pub gossip_interval: Duration,
    pub fanout: usize,
    pub suspect_timeout: Duration,
    pub dead_timeout: Duration,
}

#[derive(Debug, Clone)]
pub struct MembershipList {
    nodes: HashMap<NodeId, NodeState>,
    versions: HashMap<NodeId, u64>,
}

#[derive(Debug, Clone)]
pub struct NodeState {
    pub id: NodeId,
    pub address: String,
    pub port: u16,
    pub status: NodeStatus,
    pub last_updated: Instant,
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeStatus {
    Alive,
    Suspect,
    Dead,
}

impl GossipProtocol {
    pub fn new(node_id: NodeId, config: GossipConfig) -> Self {
        Self {
            node_id,
            membership: Arc::new(RwLock::new(MembershipList {
                nodes: HashMap::new(),
                versions: HashMap::new(),
            })),
            config,
            sequence_number: Arc::new(RwLock::new(0)),
        }
    }

    pub fn start(&self) {
        self.spawn_gossip_task();
        self.spawn_failure_detection_task();
    }

    fn spawn_gossip_task(&self) {
        let membership = self.membership.clone();
        let config = self.config.clone();
        let node_id = self.node_id.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.gossip_interval);

            loop {
                interval.tick().await;

                let targets = {
                    let guard = membership.read().await;
                    let alive_nodes: Vec<_> = guard
                        .nodes
                        .values()
                        .filter(|n| matches!(n.status, NodeStatus::Alive))
                        .filter(|n| n.id != node_id)
                        .cloned()
                        .collect();

                    // 随机选择 fanout 个节点
                    alive_nodes.into_iter().take(config.fanout).collect::<Vec<_>>()
                };

                for target in targets {
                    tracing::debug!("Gossiping to node {}", target.id);
                }
            }
        });
    }

    fn spawn_failure_detection_task(&self) {
        let membership = self.membership.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(1));

            loop {
                interval.tick().await;
                let now = Instant::now();

                let mut guard = membership.write().await;
                for (_id, node) in guard.nodes.iter_mut() {
                    match node.status {
                        NodeStatus::Alive => {
                            if now.duration_since(node.last_updated) > config.suspect_timeout {
                                node.status = NodeStatus::Suspect;
                            }
                        }
                        NodeStatus::Suspect => {
                            if now.duration_since(node.last_updated) > config.dead_timeout {
                                node.status = NodeStatus::Dead;
                            }
                        }
                        NodeStatus::Dead => {}
                    }
                }
            }
        });
    }
}
```

---

## 5. 熔断器模式

### 5.1 状态机模型

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

/// 熔断器状态机
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}

/// 熔断器配置
#[derive(Debug, Clone)]
pub struct CircuitBreakerConfig {
    pub failure_threshold: f64,
    pub slow_call_threshold_ms: u64,
    pub open_duration: Duration,
    pub half_open_max_calls: u32,
    pub sliding_window_size: u32,
    pub minimum_number_of_calls: u32,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 50.0,
            slow_call_threshold_ms: 1000,
            open_duration: Duration::from_secs(30),
            half_open_max_calls: 5,
            sliding_window_size: 100,
            minimum_number_of_calls: 10,
        }
    }
}

/// 熔断器
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: Arc<RwLock<CircuitStateInternal>>,
    metrics: Arc<RwLock<Metrics>>,
}

struct CircuitStateInternal {
    state: CircuitState,
    last_state_change: Instant,
    half_open_attempts: u32,
}

#[derive(Debug, Default)]
struct Metrics {
    successes: Vec<bool>,
    slow_calls: Vec<bool>,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            state: Arc::new(RwLock::new(CircuitStateInternal {
                state: CircuitState::Closed,
                last_state_change: Instant::now(),
                half_open_attempts: 0,
            })),
            metrics: Arc::new(RwLock::new(Metrics::default())),
        }
    }

    pub async fn call<F, Fut, T>(&self, operation: F) -> Result<T, CircuitBreakerError>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, CallError>>,
    {
        let can_execute = self.can_execute().await;

        match can_execute {
            ExecutionDecision::Allow => {
                let start = Instant::now();
                let result = operation().await;
                let duration = start.elapsed();

                self.record_result(&result, duration).await;

                match result {
                    Ok(value) => Ok(value),
                    Err(e) => Err(CircuitBreakerError::CallFailed(e)),
                }
            }
            ExecutionDecision::Reject => {
                Err(CircuitBreakerError::CircuitOpen)
            }
            ExecutionDecision::LimitedAllow => {
                let start = Instant::now();
                let result = operation().await;
                let duration = start.elapsed();

                self.record_result(&result, duration).await;
                self.handle_half_open_result(&result).await;

                match result {
                    Ok(value) => Ok(value),
                    Err(e) => Err(CircuitBreakerError::CallFailed(e)),
                }
            }
        }
    }

    async fn can_execute(&self) -> ExecutionDecision {
        let mut state = self.state.write().await;

        match state.state {
            CircuitState::Closed => ExecutionDecision::Allow,
            CircuitState::Open => {
                if state.last_state_change.elapsed() > self.config.open_duration {
                    state.state = CircuitState::HalfOpen;
                    state.half_open_attempts = 0;
                    state.last_state_change = Instant::now();
                    ExecutionDecision::LimitedAllow
                } else {
                    ExecutionDecision::Reject
                }
            }
            CircuitState::HalfOpen => {
                if state.half_open_attempts < self.config.half_open_max_calls {
                    state.half_open_attempts += 1;
                    ExecutionDecision::LimitedAllow
                } else {
                    ExecutionDecision::Reject
                }
            }
        }
    }

    async fn record_result<T>(&self, result: &Result<T, CallError>, _duration: Duration) {
        let mut metrics = self.metrics.write().await;
        metrics.successes.push(result.is_ok());
        self.check_threshold().await;
    }

    async fn check_threshold(&self) {
        let metrics = self.metrics.read().await;

        if metrics.successes.len() < self.config.minimum_number_of_calls as usize {
            return;
        }

        let failures = metrics.successes.iter().filter(|&&s| !s).count() as f64;
        let total = metrics.successes.len() as f64;
        let failure_rate = (failures / total) * 100.0;

        if failure_rate >= self.config.failure_threshold {
            drop(metrics);

            let mut state = self.state.write().await;
            if matches!(state.state, CircuitState::Closed) {
                state.state = CircuitState::Open;
                state.last_state_change = Instant::now();
                tracing::warn!("Circuit breaker opened: failure rate {:.2}%", failure_rate);
            }
        }
    }

    async fn handle_half_open_result<T>(&self, result: &Result<T, CallError>) {
        let mut state = self.state.write().await;

        match result {
            Ok(_) => {
                state.state = CircuitState::Closed;
                state.half_open_attempts = 0;
                state.last_state_change = Instant::now();
                tracing::info!("Circuit breaker closed after successful test");
            }
            Err(_) => {
                state.state = CircuitState::Open;
                state.half_open_attempts = 0;
                state.last_state_change = Instant::now();
                tracing::warn!("Circuit breaker reopened after failed test");
            }
        }
    }

    pub async fn current_state(&self) -> CircuitState {
        self.state.read().await.state
    }
}

#[derive(Debug, Clone, Copy)]
enum ExecutionDecision {
    Allow,
    Reject,
    LimitedAllow,
}

#[derive(Debug)]
pub enum CircuitBreakerError {
    CircuitOpen,
    CallFailed(CallError),
}

#[derive(Debug)]
pub enum CallError {
    Timeout,
    ConnectionRefused,
    ServiceUnavailable(String),
    InternalError(String),
}
```

#### 熔断器状态机定理

```text
┌─────────────────────────────────────────────────────────────────┐
│               Circuit Breaker State Machine                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│                         ┌──────────┐                            │
│              ┌─────────│  CLOSED  │◄────────┐                   │
│              │          │ (正常)   │         │                   │
│              │          └────┬─────┘         │                   │
│              │               │               │                   │
│              │  failure_rate │               │                   │
│              │  >= threshold │               │                   │
│              │               ▼               │                   │
│              │          ┌──────────┐         │                   │
│              │    ┌────│   OPEN   │────┐    │                   │
│              │    │    │ (熔断)   │    │    │                   │
│              │    │    └────┬─────┘    │    │                   │
│              │    │         │          │    │                   │
│              │    │ timeout │          │    │                   │
│              │    │ expired │          │    │                   │
│              │    │         ▼          │    │                   │
│              │    │    ┌──────────┐    │    │                   │
│              │    └───►│ HALF_OPEN│────┘    │                   │
│              │         │ (探测)   │         │                   │
│              │         └────┬─────┘         │                   │
│              │              │               │                   │
│              │    success   │  failure      │                   │
│              └──────────────┴───────────────┘                   │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Theorem CIRCUIT-STABILITY:                                     │
│    The circuit breaker will stabilize in CLOSED or OPEN state   │
│    under sustained load conditions.                             │
│                                                                 │
│  Proof:                                                         │
│    - HALF_OPEN is transient by design                           │
│    - Each HALF_OPEN state transition leads to CLOSED or OPEN    │
│    - CLOSED transitions to OPEN on sustained failures           │
│    - OPEN transitions to HALF_OPEN after timeout                │
│    ∴ System cannot loop indefinitely                            │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 5.2 分布式熔断器

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 分布式熔断器
pub struct DistributedCircuitBreaker {
    local: CircuitBreaker,
    shared_state: Arc<RwLock<SharedCircuitState>>,
    node_id: String,
}

#[derive(Debug)]
struct SharedCircuitState {
    services: HashMap<String, ServiceCircuitState>,
}

#[derive(Debug, Clone)]
struct ServiceCircuitState {
    global_state: CircuitState,
    node_states: HashMap<String, CircuitState>,
    version: u64,
}

impl DistributedCircuitBreaker {
    pub async fn sync_state(&self, service_name: &str) -> Result<(), SyncError> {
        let local_state = self.local.current_state().await;

        let mut shared = self.shared_state.write().await;
        let service_state = shared.services
            .entry(service_name.to_string())
            .or_insert_with(|| ServiceCircuitState {
                global_state: CircuitState::Closed,
                node_states: HashMap::new(),
                version: 0,
            });

        service_state.node_states.insert(self.node_id.clone(), local_state);

        let new_global = self.compute_global_state(&service_state.node_states);

        if new_global != service_state.global_state {
            service_state.global_state = new_global;
            service_state.version += 1;
            self.broadcast_state_change(service_name, new_global).await?;
        }

        Ok(())
    }

    fn compute_global_state(&self, node_states: &HashMap<String, CircuitState>) -> CircuitState {
        let mut has_open = false;
        let mut has_half_open = false;

        for state in node_states.values() {
            match state {
                CircuitState::Open => has_open = true,
                CircuitState::HalfOpen => has_half_open = true,
                CircuitState::Closed => {}
            }
        }

        if has_open {
            CircuitState::Open
        } else if has_half_open {
            CircuitState::HalfOpen
        } else {
            CircuitState::Closed
        }
    }

    async fn broadcast_state_change(&self, _service: &str, _state: CircuitState) -> Result<(), SyncError> {
        Ok(())
    }
}

#[derive(Debug)]
pub enum SyncError {
    NetworkError(String),
    ConsensusFailed,
}
```

#### Counter-Example: 脑裂熔断器

```rust
/// ❌ Counter-Example: 分布式熔断器脑裂问题
pub struct SplitBrainScenario;

impl SplitBrainScenario {
    pub fn demonstrate() {
        // 场景：
        // 1. 节点 A、B、C 都在监控 Service X
        // 2. 网络分区：{A} 和 {B, C} 被分开
        // 3. A 认为 Service X 健康（CLOSED）
        // 4. B 和 C 检测到 Service X 故障，切换到 OPEN
        // 5. 客户端访问 A 时请求被允许（可能失败）
        // 6. 客户端访问 B/C 时请求被拒绝
        //
        // 结果：不一致的客户端体验
    }
}

/// ✅ 解决方案：基于共识的熔断器状态
pub struct ConsensusBasedCircuitBreaker {
    local: CircuitBreaker,
    raft: Arc<RaftNode>,
}

impl ConsensusBasedCircuitBreaker {
    pub async fn propose_state_change(
        &self,
        service: String,
        new_state: CircuitState,
    ) -> Result<(), ConsensusError> {
        let entry = LogEntry {
            term: *self.raft.current_term.read().await,
            index: self.raft.log.read().await.len() as u64 + 1,
            command: serde_json::to_vec(&CircuitBreakerCommand::SetState {
                service,
                state: new_state,
            }).unwrap(),
            respond_to: None,
        };

        self.raft.replicate_log(entry).await
            .map_err(|e| ConsensusError::ReplicationFailed(e.to_string()))?;

        Ok(())
    }
}

#[derive(Debug, Serialize, Deserialize)]
enum CircuitBreakerCommand {
    SetState { service: String, state: CircuitState },
    RecordFailure { service: String, timestamp: u64 },
}

#[derive(Debug)]
pub enum ConsensusError {
    ReplicationFailed(String),
}

use serde::{Serialize, Deserialize};
```

---

## 6. 背压与流量控制

### 6.1 负载削减

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::Semaphore;

/// 负载削减器
pub struct LoadShedder {
    metrics: Arc<LoadMetrics>,
    config: LoadShedConfig,
    semaphore: Arc<Semaphore>,
}

#[derive(Debug)]
struct LoadMetrics {
    active_requests: AtomicU64,
    queue_wait_ms: AtomicU64,
    error_rate: AtomicU64,
    latency_p99_ms: AtomicU64,
}

#[derive(Debug, Clone)]
pub struct LoadShedConfig {
    pub max_concurrent: usize,
    pub target_latency_ms: u64,
    pub latency_threshold_ms: u64,
    pub error_threshold_percent: u64,
    pub priority_levels: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RequestPriority {
    Critical = 0,
    High = 1,
    Normal = 2,
    Low = 3,
    Background = 4,
}

impl LoadShedder {
    pub fn new(config: LoadShedConfig) -> Self {
        Self {
            metrics: Arc::new(LoadMetrics {
                active_requests: AtomicU64::new(0),
                queue_wait_ms: AtomicU64::new(0),
                error_rate: AtomicU64::new(0),
                latency_p99_ms: AtomicU64::new(0),
            }),
            config: config.clone(),
            semaphore: Arc::new(Semaphore::new(config.max_concurrent)),
        }
    }

    pub async fn acquire_permit(
        &self,
        priority: RequestPriority,
    ) -> Result<Permit, LoadShedError> {
        let shed_probability = self.calculate_shed_probability(priority);

        if shed_probability > 0.0 {
            let should_shed = if shed_probability >= 1.0 {
                true
            } else {
                rand::random::<f64>() < shed_probability
            };

            if should_shed {
                return Err(LoadShedError::Shed(priority));
            }
        }

        let permit = self.semaphore.clone().acquire_owned().await
            .map_err(|_| LoadShedError::Internal)?;

        self.metrics.active_requests.fetch_add(1, Ordering::SeqCst);

        Ok(Permit {
            permit,
            metrics: self.metrics.clone(),
            start_time: Instant::now(),
        })
    }

    fn calculate_shed_probability(&self, priority: RequestPriority) -> f64 {
        let active = self.metrics.active_requests.load(Ordering::Relaxed);
        let latency = self.metrics.latency_p99_ms.load(Ordering::Relaxed);
        let error_rate = self.metrics.error_rate.load(Ordering::Relaxed) as f64 / 100.0;

        let load_factor = active as f64 / self.config.max_concurrent as f64;
        let latency_factor = if latency > self.config.latency_threshold_ms {
            (latency - self.config.latency_threshold_ms) as f64 /
                self.config.latency_threshold_ms as f64
        } else {
            0.0
        };
        let error_factor = error_rate / self.config.error_threshold_percent as f64;

        let base_probability = load_factor.max(latency_factor).max(error_factor);

        let priority_adjustment = match priority {
            RequestPriority::Critical => 0.0,
            RequestPriority::High => base_probability * 0.5,
            RequestPriority::Normal => base_probability,
            RequestPriority::Low => base_probability * 1.5,
            RequestPriority::Background => 1.0,
        };

        priority_adjustment.min(1.0)
    }
}

pub struct Permit {
    permit: tokio::sync::OwnedSemaphorePermit,
    metrics: Arc<LoadMetrics>,
    start_time: Instant,
}

impl Permit {
    pub fn success(self) {
        self.metrics.active_requests.fetch_sub(1, Ordering::SeqCst);
    }

    pub fn failed(self) {
        self.metrics.active_requests.fetch_sub(1, Ordering::SeqCst);
    }
}

#[derive(Debug)]
pub enum LoadShedError {
    Shed(RequestPriority),
    Timeout,
    Internal,
}
```

#### Counter-Example: 级联故障

```rust
/// ❌ Counter-Example: 没有背压导致的级联故障
pub struct CascadingFailureScenario;

impl CascadingFailureScenario {
    pub async fn demonstrate() {
        // 场景：
        // 1. 客户端向 Service A 发送 1000 请求/秒
        // 2. Service A 需要调用 Service B
        // 3. Service B 变慢（500ms 延迟）
        // 4. Service A 的线程池被占满等待 Service B
        // 5. 新请求在 Service A 排队，最终超时
    }
}

/// ✅ 解决方案：带超时的级联调用
pub struct ResilientServiceA {
    http_client: reqwest::Client,
    circuit_breaker: CircuitBreaker,
    load_shedder: LoadShedder,
}

impl ResilientServiceA {
    pub async fn handle_request(&self) -> Result<Response, Error> {
        let permit = self.load_shedder.acquire_permit(RequestPriority::Normal).await?;

        let result = self.circuit_breaker.call(|| async {
            self.http_client
                .get("http://service-b/api")
                .timeout(Duration::from_millis(100))
                .send()
                .await
                .map_err(|e| CallError::ServiceUnavailable(e.to_string()))
        }).await;

        match result {
            Ok(response) => {
                permit.success();
                Ok(response)
            }
            Err(e) => {
                permit.failed();
                Err(Error::from(e))
            }
        }
    }
}

pub struct Response;
pub struct Error;

impl From<CircuitBreakerError> for Error {
    fn from(_: CircuitBreakerError) -> Self {
        Error
    }
}
impl From<LoadShedError> for Error {
    fn from(_: LoadShedError) -> Self {
        Error
    }
}
```

### 6.2 准入控制

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

/// 分布式令牌桶
pub struct DistributedTokenBucket {
    local_tokens: AtomicU64,
    config: TokenBucketConfig,
    last_refill: Arc<RwLock<Instant>>,
    coordinator: Option<Arc<dyn TokenCoordinator>>,
}

#[derive(Debug, Clone)]
pub struct TokenBucketConfig {
    pub capacity: u64,
    pub refill_rate_per_sec: u64,
    pub tokens_per_request: u64,
}

#[async_trait::async_trait]
pub trait TokenCoordinator: Send + Sync {
    async fn acquire_tokens(&self, count: u64) -> Result<bool, CoordinatorError>;
    async fn return_tokens(&self, count: u64) -> Result<(), CoordinatorError>;
}

impl DistributedTokenBucket {
    pub fn new(config: TokenBucketConfig) -> Self {
        Self {
            local_tokens: AtomicU64::new(config.capacity),
            config,
            last_refill: Arc::new(RwLock::new(Instant::now())),
            coordinator: None,
        }
    }

    pub async fn try_acquire(&self) -> Result<Token, TokenError> {
        self.refill().await;

        let tokens_needed = self.config.tokens_per_request;
        let current = self.local_tokens.load(Ordering::SeqCst);

        if current >= tokens_needed {
            match self.local_tokens.compare_exchange(
                current,
                current - tokens_needed,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return Ok(Token::new(tokens_needed, self)),
                Err(_) => {}
            }
        }

        if let Some(coordinator) = &self.coordinator {
            if coordinator.acquire_tokens(tokens_needed).await? {
                return Ok(Token::new(tokens_needed, self));
            }
        }

        Err(TokenError::RateLimited)
    }

    async fn refill(&self) {
        let mut last = self.last_refill.write().await;
        let now = Instant::now();
        let elapsed = now.duration_since(*last);

        let tokens_to_add = (elapsed.as_secs_f64() * self.config.refill_rate_per_sec as f64) as u64;

        if tokens_to_add > 0 {
            let current = self.local_tokens.load(Ordering::Relaxed);
            let new_tokens = (current + tokens_to_add).min(self.config.capacity);
            self.local_tokens.store(new_tokens, Ordering::Relaxed);
            *last = now;
        }
    }
}

pub struct Token<'a> {
    count: u64,
    bucket: &'a DistributedTokenBucket,
}

impl<'a> Token<'a> {
    fn new(count: u64, bucket: &'a DistributedTokenBucket) -> Self {
        Self { count, bucket }
    }
}

#[derive(Debug)]
pub enum TokenError {
    RateLimited,
    CoordinatorError(String),
}

#[derive(Debug)]
pub enum CoordinatorError {
    NetworkError,
    QuorumNotReached,
}
```

---

## 7. 分布式追踪

```rust
use std::sync::Arc;
use std::collections::HashMap;
use tokio::task_local;

/// 追踪上下文
#[derive(Debug, Clone)]
pub struct TraceContext {
    pub trace_id: String,
    pub parent_span_id: Option<String>,
    pub span_id: String,
    pub sampled: bool,
    pub baggage: HashMap<String, String>,
    pub format: PropagationFormat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropagationFormat {
    W3C,
    B3,
    Jaeger,
    Custom(String),
}

pub mod context {
    use super::*;

    task_local! {
        pub static CURRENT_CONTEXT: TraceContext;
    }

    pub async fn with_context<F, Fut, R>(
        context: TraceContext,
        f: F,
    ) -> R
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = R>,
    {
        CURRENT_CONTEXT.scope(context, f()).await
    }

    pub fn current() -> Option<TraceContext> {
        CURRENT_CONTEXT.try_with(|ctx| ctx.clone()).ok()
    }
}

impl TraceContext {
    pub fn new_root(sampled: bool) -> Self {
        Self {
            trace_id: generate_id(),
            parent_span_id: None,
            span_id: generate_id(),
            sampled,
            baggage: HashMap::new(),
            format: PropagationFormat::W3C,
        }
    }

    pub fn child(&self) -> Self {
        Self {
            trace_id: self.trace_id.clone(),
            parent_span_id: Some(self.span_id.clone()),
            span_id: generate_id(),
            sampled: self.sampled,
            baggage: self.baggage.clone(),
            format: self.format,
        }
    }

    pub fn to_headers(&self) -> HashMap<String, String> {
        let mut headers = HashMap::new();

        match self.format {
            PropagationFormat::W3C => {
                let flags = if self.sampled { "01" } else { "00" };
                headers.insert(
                    "traceparent".to_string(),
                    format!("00-{}-{}-{}", self.trace_id, self.span_id, flags),
                );
            }
            _ => {}
        }

        headers
    }

    pub fn from_headers(headers: &HashMap<String, String>) -> Option<Self> {
        if let Some(traceparent) = headers.get("traceparent") {
            let parts: Vec<&str> = traceparent.split('-').collect();
            if parts.len() >= 4 {
                return Some(Self {
                    trace_id: parts[1].to_string(),
                    span_id: parts[2].to_string(),
                    parent_span_id: None,
                    sampled: parts[3] == "01",
                    baggage: HashMap::new(),
                    format: PropagationFormat::W3C,
                });
            }
        }
        None
    }
}

fn generate_id() -> String {
    uuid::Uuid::new_v4().to_string().replace("-", "")
}

pub struct Span {
    context: TraceContext,
    name: String,
    start_time: std::time::Instant,
}

impl Span {
    pub fn new(name: impl Into<String>, parent: Option<&TraceContext>) -> Self {
        let context = parent.map(|p| p.child()).unwrap_or_else(|| TraceContext::new_root(true));
        Self {
            context,
            name: name.into(),
            start_time: std::time::Instant::now(),
        }
    }

    pub async fn enter<F, Fut, R>(self, f: F) -> R
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = R>,
    {
        context::with_context(self.context.clone(), f).await
    }
}

impl Drop for Span {
    fn drop(&mut self) {
        let duration = self.start_time.elapsed();
        tracing::info!(
            trace_id = %self.context.trace_id,
            span_id = %self.context.span_id,
            name = %self.name,
            duration_ms = %duration.as_millis(),
            "Span completed"
        );
    }
}
```

---

## 8. 案例研究: 分布式键值存储

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{RwLock, mpsc};
use std::time::{Duration, Instant};

/// 分布式键值存储
pub struct DistributedKVStore {
    node_id: String,
    storage: Arc<RwLock<HashMap<String, VersionedValue>>>,
    raft: Arc<RaftNode>,
    shard_manager: Arc<ShardManager>,
    circuit_breaker: CircuitBreaker,
    load_shedder: LoadShedder,
    service_registry: Arc<ServiceRegistry>,
    config: KVStoreConfig,
}

#[derive(Debug, Clone)]
struct VersionedValue {
    value: Vec<u8>,
    version: u64,
    timestamp: u64,
}

#[derive(Debug, Clone)]
pub struct KVStoreConfig {
    pub num_nodes: usize,
    pub replication_factor: usize,
    pub num_shards: usize,
    pub consistency: ConsistencyLevel,
}

pub struct ShardManager {
    shard_map: Arc<RwLock<HashMap<ShardId, Vec<NodeId>>>>,
    virtual_nodes: usize,
}

pub type ShardId = u16;

impl ShardManager {
    pub fn key_to_shard(&self, key: &str, num_shards: usize) -> ShardId {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish();
        (hash % num_shards as u64) as ShardId
    }

    pub async fn get_shard_nodes(&self, shard: ShardId) -> Vec<NodeId> {
        let map = self.shard_map.read().await;
        map.get(&shard).cloned().unwrap_or_default()
    }
}

#[derive(Debug, Clone)]
pub enum KVOperation {
    Get { key: String },
    Put { key: String, value: Vec<u8> },
    Delete { key: String },
}

#[derive(Debug, Clone)]
pub enum KVResult {
    Value(Option<Vec<u8>>),
    Success,
    NotFound,
    Error(String),
}

impl DistributedKVStore {
    pub async fn new(node_id: String, config: KVStoreConfig) -> Result<Self, StoreError> {
        Ok(Self {
            node_id,
            storage: Arc::new(RwLock::new(HashMap::new())),
            raft: Arc::new(RaftNode::new(node_id.clone(), vec![], ElectionConfig::default())),
            shard_manager: Arc::new(ShardManager {
                shard_map: Arc::new(RwLock::new(HashMap::new())),
                virtual_nodes: 150,
            }),
            circuit_breaker: CircuitBreaker::new(CircuitBreakerConfig::default()),
            load_shedder: LoadShedder::new(LoadShedConfig {
                max_concurrent: 1000,
                target_latency_ms: 10,
                latency_threshold_ms: 50,
                error_threshold_percent: 10,
                priority_levels: 3,
            }),
            service_registry: Arc::new(ServiceRegistry::new(HealthCheckConfig {
                check_interval: Duration::from_secs(5),
                timeout: Duration::from_secs(2),
                unhealthy_threshold: 3,
                healthy_threshold: 2,
            })),
            config,
        })
    }

    pub async fn get(&self, key: &str) -> Result<Option<Vec<u8>>, StoreError> {
        let _permit = self.load_shedder.acquire_permit(RequestPriority::Normal).await
            .map_err(|_| StoreError::Overloaded)?;

        let shard = self.shard_manager.key_to_shard(key, self.config.num_shards);
        let nodes = self.shard_manager.get_shard_nodes(shard).await;

        if nodes.is_empty() {
            return Err(StoreError::NoReplicasAvailable);
        }

        match self.config.consistency {
            ConsistencyLevel::Strong => self.read_quorum(key, &nodes).await,
            _ => self.read_any(key, &nodes).await,
        }
    }

    async fn read_quorum(&self, key: &str, nodes: &[NodeId]) -> Result<Option<Vec<u8>>, StoreError> {
        let quorum = (nodes.len() / 2) + 1;

        for node in nodes.iter().take(quorum) {
            if let Ok(value) = self.read_from_node(node, key).await {
                return Ok(value);
            }
        }

        Err(StoreError::QuorumNotReached { required: quorum, received: 0 })
    }

    async fn read_from_node(&self, node: &NodeId, key: &str) -> Result<Option<Vec<u8>>, CallError> {
        if node == &self.node_id {
            let storage = self.storage.read().await;
            return Ok(storage.get(key).map(|v| v.value.clone()));
        }
        Err(CallError::ServiceUnavailable("Remote read not implemented".to_string()))
    }
}

#[derive(Debug)]
pub enum StoreError {
    NoReplicasAvailable,
    QuorumNotReached { required: usize, received: usize },
    Overloaded,
    ConsensusFailed(String),
    Serialization(String),
    Network(String),
}
```

---

## 9. Rust 生态系统

### 9.1 Tonic (gRPC)

```rust
use tonic::{transport::Server, Request, Response, Status};

/// gRPC 服务定义
pub mod kv_store {
    tonic::include_proto!("kv_store");
}

use kv_store::{
    kv_store_server::{KvStore, KvStoreServer},
    GetRequest, GetResponse,
    PutRequest, PutResponse,
};

pub struct KvStoreService {
    store: Arc<DistributedKVStore>,
}

#[tonic::async_trait]
impl KvStore for KvStoreService {
    async fn get(&self, request: Request<GetRequest>) -> Result<Response<GetResponse>, Status> {
        let req = request.into_inner();

        match self.store.get(&req.key).await {
            Ok(Some(value)) => Ok(Response::new(GetResponse { value, found: true })),
            Ok(None) => Ok(Response::new(GetResponse { value: Vec::new(), found: false })),
            Err(e) => Err(Status::internal(e.to_string())),
        }
    }

    async fn put(&self, request: Request<PutRequest>) -> Result<Response<PutResponse>, Status> {
        let req = request.into_inner();

        match self.store.put(req.key, req.value).await {
            Ok(()) => Ok(Response::new(PutResponse { success: true })),
            Err(e) => Err(Status::internal(e.to_string())),
        }
    }
}
```

### 9.2 Tarpc

```rust
use tarpc::{client, context, server};

/// Tarpc 服务定义
#[tarpc::service]
pub trait KVStore {
    async fn get(key: String) -> Option<Vec<u8>>;
    async fn put(key: String, value: Vec<u8>) -> bool;
    async fn delete(key: String) -> bool;
}

/// 服务实现
#[derive(Clone)]
pub struct KVStoreServerImpl {
    store: Arc<DistributedKVStore>,
}

#[tarpc::server]
impl KVStore for KVStoreServerImpl {
    async fn get(self, _: context::Context, key: String) -> Option<Vec<u8>> {
        self.store.get(&key).await.ok().flatten()
    }

    async fn put(self, _: context::Context, key: String, value: Vec<u8>) -> bool {
        self.store.put(key, value).await.is_ok()
    }

    async fn delete(self, _: context::Context, key: String) -> bool {
        // 实现删除逻辑
        true
    }
}
```

---

## 总结

本文档深入探讨了分布式系统的核心模式及其在 Rust 中的实现：

1. **CAP 定理** - 理解分布式系统的基本权衡
2. **共识算法** - 2PC 和 Raft 保证分布式一致性
3. **消息传递** - 序列化语义和传递保证
4. **服务发现** - 注册表模式和 Gossip 协议
5. **熔断器模式** - 防止级联故障
6. **背压控制** - 负载削减和准入控制
7. **分布式追踪** - 跨服务请求追踪
8. **案例研究** - 完整的分布式 KV 存储设计
9. **Rust 生态** - Tonic 和 Tarpc RPC 框架

---

*文档版本: 1.0.0*
*Rust 版本: 1.94*
*最后更新: 2026-03-06*
