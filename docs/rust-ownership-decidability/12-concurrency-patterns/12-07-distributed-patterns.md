# Rust 分布式模式

> **Rust版本**: 1.93.1
> **覆盖范围**: 一致性模型、共识算法、分布式事务、容错设计
> **权威参考**: Designing Data-Intensive Applications (Martin Kleppmann), Raft Paper

---

## 目录

- [Rust 分布式模式](#rust-分布式模式)
  - [目录](#目录)
  - [1. 分布式系统理论](#1-分布式系统理论)
    - [1.1 CAP定理](#11-cap定理)
    - [1.2 一致性模型](#12-一致性模型)
    - [1.3 故障模型](#13-故障模型)
  - [2. 共识算法](#2-共识算法)
    - [2.1 Raft协议](#21-raft协议)
    - [2.2 领导者选举](#22-领导者选举)

---

## 1. 分布式系统理论

### 1.1 CAP定理

```rust
/// CAP 定理：在分布式系统中，一致性、可用性、分区容错性
/// 最多只能同时满足其中两个
///
/// C - Consistency: 所有节点在同一时间看到相同的数据
/// A - Availability: 每个请求都能收到响应（成功或失败）
/// P - Partition Tolerance: 系统在网络分区时仍能继续运行

/// CAP 权衡决策枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CAPStrategy {
    /// CP: 保证一致性和分区容错，可能牺牲可用性
    /// 适用：金融交易、库存系统
    CP,

    /// AP: 保证可用性和分区容错，可能牺牲一致性
    /// 适用：社交网络、日志系统
    AP,

    /// CA: 仅在非分布式系统或完美网络下可能
    /// 实际上分布式系统必须容忍分区
    CA,
}

/// 系统配置
pub struct DistributedSystemConfig {
    pub cap_strategy: CAPStrategy,
    pub replication_factor: u32,
    pub consistency_level: ConsistencyLevel,
}

#[derive(Debug, Clone, Copy)]
pub enum ConsistencyLevel {
    /// 强一致性：所有副本写入后才返回成功
    Strong,
    /// 最终一致性：异步复制，保证最终一致
    Eventual,
    /// 因果一致性：保持因果关系的一致性
    Causal,
    /// 读己之写一致性
    ReadYourWrites,
    /// 会话一致性
    Session,
}

/// 验证 CAP 选择
impl DistributedSystemConfig {
    pub fn validate(&self) -> Result<(), ConfigError> {
        match self.cap_strategy {
            CAPStrategy::CP => {
                // CP 系统在分区期间可能拒绝写入
                if matches!(self.consistency_level, ConsistencyLevel::Eventual) {
                    return Err(ConfigError::InconsistentConfig(
                        "CP system should not use Eventual consistency".into()
                    ));
                }
            }
            CAPStrategy::AP => {
                // AP 系统通常使用最终一致性
                if matches!(self.consistency_level, ConsistencyLevel::Strong) {
                    println!("Warning: Strong consistency in AP system may impact availability");
                }
            }
            CAPStrategy::CA => {
                return Err(ConfigError::InvalidStrategy(
                    "CA systems cannot tolerate network partitions".into()
                ));
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum ConfigError {
    InconsistentConfig(String),
    InvalidStrategy(String),
}
```

### 1.2 一致性模型

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 一致性模型定义
pub trait ConsistencyModel {
    type Key: Clone + Send + Sync;
    type Value: Clone + Send + Sync;

    /// 写入操作
    async fn write(&self, key: Self::Key, value: Self::Value) -> Result<(), ConsistencyError>;

    /// 读取操作
    async fn read(&self, key: &Self::Key) -> Result<Option<Self::Value>, ConsistencyError>;
}

/// 强一致性实现
pub struct StrongConsistency<K, V> {
    data: Arc<RwLock<HashMap<K, V>>>,
    replicas: Vec<ReplicaHandle>,
    write_quorum: usize,
    read_quorum: usize,
}

#[derive(Clone)]
struct ReplicaHandle;

#[derive(Debug)]
pub enum ConsistencyError {
    QuorumNotReached,
    ConflictDetected,
    Timeout,
    NetworkError,
}

impl<K, V> StrongConsistency<K, V>
where
    K: Clone + Send + Sync + std::hash::Hash + Eq + 'static,
    V: Clone + Send + Sync + 'static,
{
    pub fn new(replicas: Vec<ReplicaHandle>) -> Self {
        let n = replicas.len();
        let write_quorum = n / 2 + 1; // 多数派写入
        let read_quorum = n / 2 + 1;  // 多数派读取

        Self {
            data: Arc::new(RwLock::new(HashMap::new())),
            replicas,
            write_quorum,
            read_quorum,
        }
    }

    pub async fn write(&self, key: K, value: V) -> Result<(), ConsistencyError> {
        // 1. 写入所有副本
        let mut success_count = 0;

        // 先写本地
        {
            let mut data = self.data.write().await;
            data.insert(key.clone(), value.clone());
            success_count += 1;
        }

        // 写远程副本（简化模拟）
        for _replica in &self.replicas {
            // 模拟网络请求
            match self.replicate_write(&key, &value).await {
                Ok(()) => success_count += 1,
                Err(_) => continue,
            }
        }

        // 2. 检查是否达到写入仲裁
        if success_count >= self.write_quorum {
            Ok(())
        } else {
            Err(ConsistencyError::QuorumNotReached)
        }
    }

    pub async fn read(&self, key: &K) -> Result<Option<V>, ConsistencyError> {
        // 1. 从多个副本读取
        let mut values = vec![];

        // 读本地
        {
            let data = self.data.read().await;
            if let Some(v) = data.get(key) {
                values.push(v.clone());
            }
        }

        // 读远程副本
        for _replica in &self.replicas {
            if let Ok(Some(v)) = self.replicate_read(key).await {
                values.push(v);
            }
        }

        // 2. 检查是否达到读取仲裁
        if values.len() >= self.read_quorum {
            // 3. 版本向量解决冲突（简化：取最新版本）
            Ok(values.into_iter().next())
        } else {
            Err(ConsistencyError::QuorumNotReached)
        }
    }

    async fn replicate_write(&self, _key: &K, _value: &V) -> Result<(), ()> {
        // 模拟网络请求
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        Ok(())
    }

    async fn replicate_read(&self, _key: &K) -> Result<Option<V>, ()> {
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        Ok(None)
    }
}

/// 因果一致性实现
use std::collections::VecDeque;

pub struct CausalConsistency<K, V> {
    data: Arc<RwLock<HashMap<K, VersionedValue<V>>>>,
    vector_clock: Arc<RwLock<HashMap<String, u64>>>,
    node_id: String,
}

struct VersionedValue<V> {
    value: V,
    vector_clock: HashMap<String, u64>,
}

impl<K, V> CausalConsistency<K, V>
where
    K: Clone + Send + Sync + std::hash::Hash + Eq,
    V: Clone + Send + Sync,
{
    pub async fn write(&self, key: K, value: V) -> Result<(), ConsistencyError> {
        let mut vc = self.vector_clock.write().await;
        let counter = vc.entry(self.node_id.clone()).or_insert(0);
        *counter += 1;

        let versioned = VersionedValue {
            value,
            vector_clock: vc.clone(),
        };

        let mut data = self.data.write().await;
        data.insert(key, versioned);

        Ok(())
    }

    /// 检查因果依赖
    pub fn check_causal_order(
        &self,
        vc1: &HashMap<String, u64>,
        vc2: &HashMap<String, u64>,
    ) -> CausalOrder {
        let mut v1_less = false;
        let mut v2_less = false;

        for (node, &t1) in vc1 {
            let t2 = vc2.get(node).copied().unwrap_or(0);
            if t1 < t2 {
                v1_less = true;
            }
        }

        for (node, &t2) in vc2 {
            let t1 = vc1.get(node).copied().unwrap_or(0);
            if t2 < t1 {
                v2_less = true;
            }
        }

        match (v1_less, v2_less) {
            (true, false) => CausalOrder::HappensBefore,
            (false, true) => CausalOrder::HappensAfter,
            (false, false) => CausalOrder::Concurrent,
            (true, true) => unreachable!(),
        }
    }
}

pub enum CausalOrder {
    HappensBefore,  // vc1 -> vc2
    HappensAfter,   // vc2 -> vc1
    Concurrent,     // 并发，需要冲突解决
}
```

### 1.3 故障模型

```rust
/// 分布式系统故障模型

/// 故障检测器
pub struct FailureDetector {
    /// 心跳超时
    heartbeat_timeout: std::time::Duration,
    /// 怀疑阈值
    suspicion_threshold: u32,
    /// 节点状态表
    node_states: Arc<RwLock<HashMap<String, NodeState>>>,
}

#[derive(Debug, Clone)]
pub enum NodeState {
    /// 健康
    Healthy,
    /// 可疑
    Suspect { since: std::time::Instant, count: u32 },
    /// 故障
    Failed,
}

impl FailureDetector {
    pub fn new(heartbeat_timeout: std::time::Duration, suspicion_threshold: u32) -> Self {
        Self {
            heartbeat_timeout,
            suspicion_threshold,
            node_states: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 接收心跳
    pub async fn heartbeat(&self, node_id: &str) {
        let mut states = self.node_states.write().await;
        states.insert(node_id.to_string(), NodeState::Healthy);
    }

    /// 检查节点状态
    pub async fn check_node(&self, node_id: &str) -> NodeState {
        let mut states = self.node_states.write().await;

        if let Some(state) = states.get(node_id).cloned() {
            match state {
                NodeState::Healthy => {
                    // 检查是否超时
                    // 简化：这里假设外部会定期调用 check_all_nodes
                    state
                }
                NodeState::Suspect { since, count } => {
                    if since.elapsed() > self.heartbeat_timeout && count >= self.suspicion_threshold {
                        states.insert(node_id.to_string(), NodeState::Failed);
                        NodeState::Failed
                    } else {
                        state
                    }
                }
                NodeState::Failed => state,
            }
        } else {
            NodeState::Failed
        }
    }

    /// 标记节点可疑
    pub async fn suspect(&self, node_id: &str) {
        let mut states = self.node_states.write().await;

        match states.get(node_id) {
            Some(NodeState::Healthy) | None => {
                states.insert(node_id.to_string(), NodeState::Suspect {
                    since: std::time::Instant::now(),
                    count: 1,
                });
            }
            Some(NodeState::Suspect { since, count }) => {
                states.insert(node_id.to_string(), NodeState::Suspect {
                    since: *since,
                    count: count + 1,
                });
            }
            Some(NodeState::Failed) => {}
        }
    }
}

/// 拜占庭故障容错（BFT）
/// 在 f 个拜占庭故障节点存在时，需要 3f + 1 个节点才能保证安全

pub struct BFTConfig {
    pub total_nodes: usize,
    pub byzantine_faults: usize,
}

impl BFTConfig {
    pub fn validate(&self) -> Result<(), String> {
        // 需要 n >= 3f + 1
        let min_nodes = 3 * self.byzantine_faults + 1;
        if self.total_nodes < min_nodes {
            return Err(format!(
                "Need at least {} nodes to tolerate {} Byzantine faults, got {}",
                min_nodes, self.byzantine_faults, self.total_nodes
            ));
        }
        Ok(())
    }

    /// 计算所需的仲裁数
    pub fn quorum_size(&self) -> usize {
        // 2f + 1
        2 * self.byzantine_faults + 1
    }
}
```

---

## 2. 共识算法

### 2.1 Raft协议

```rust
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tokio::sync::{RwLock, mpsc};

/// Raft 节点状态
#[derive(Debug, Clone, PartialEq)]
pub enum RaftState {
    /// 跟随者
    Follower { leader: Option<NodeId> },
    /// 候选者
    Candidate { votes_received: HashSet<NodeId> },
    /// 领导者
    Leader {
        next_index: HashMap<NodeId, LogIndex>,
        match_index: HashMap<NodeId, LogIndex>,
    },
}

pub type NodeId = String;
pub type LogIndex = u64;
pub type Term = u64;

/// 日志条目
#[derive(Debug, Clone)]
pub struct LogEntry {
    pub term: Term,
    pub index: LogIndex,
    pub command: Vec<u8>,
}

/// Raft 节点
pub struct RaftNode {
    /// 节点 ID
    id: NodeId,
    /// 当前状态
    state: Arc<RwLock<RaftState>>,
    /// 当前任期
    current_term: Arc<RwLock<Term>>,
    /// 投票给谁
    voted_for: Arc<RwLock<Option<NodeId>>>,
    /// 日志
    log: Arc<RwLock<Vec<LogEntry>>>,
    /// 已提交索引
    commit_index: Arc<RwLock<LogIndex>>,
    /// 已应用索引
    last_applied: Arc<RwLock<LogIndex>>,
    /// 其他节点
    peers: Vec<NodeId>,
    /// 消息通道
    msg_tx: mpsc::Sender<RaftMessage>,
    msg_rx: mpsc::Receiver<RaftMessage>,
}

/// Raft 消息
#[derive(Debug)]
pub enum RaftMessage {
    /// 请求投票
    RequestVote {
        term: Term,
        candidate_id: NodeId,
        last_log_index: LogIndex,
        last_log_term: Term,
    },
    /// 投票响应
    RequestVoteResponse {
        term: Term,
        vote_granted: bool,
    },
    /// 追加日志
    AppendEntries {
        term: Term,
        leader_id: NodeId,
        prev_log_index: LogIndex,
        prev_log_term: Term,
        entries: Vec<LogEntry>,
        leader_commit: LogIndex,
    },
    /// 追加日志响应
    AppendEntriesResponse {
        term: Term,
        success: bool,
        match_index: LogIndex,
    },
    /// 客户端请求
    ClientRequest {
        command: Vec<u8>,
        respond_to: oneshot::Sender<ClientResponse>,
    },
}

#[derive(Debug)]
pub enum ClientResponse {
    Success { result: Vec<u8> },
    NotLeader { leader: Option<NodeId> },
    Timeout,
}

use tokio::sync::oneshot;

impl RaftNode {
    pub fn new(id: NodeId, peers: Vec<NodeId>) -> Self {
        let (msg_tx, msg_rx) = mpsc::channel(100);

        Self {
            id,
            state: Arc::new(RwLock::new(RaftState::Follower { leader: None })),
            current_term: Arc::new(RwLock::new(0)),
            voted_for: Arc::new(RwLock::new(None)),
            log: Arc::new(RwLock::new(vec![])),
            commit_index: Arc::new(RwLock::new(0)),
            last_applied: Arc::new(RwLock::new(0)),
            peers,
            msg_tx,
            msg_rx,
        }
    }

    /// 处理请求投票
    pub async fn handle_request_vote(&self, req: RaftMessage) -> RaftMessage {
        match req {
            RaftMessage::RequestVote { term, candidate_id, last_log_index, last_log_term } => {
                let mut current_term = self.current_term.write().await;
                let mut voted_for = self.voted_for.write().await;
                let log = self.log.read().await;

                // 如果任期更高，转为跟随者
                if term > *current_term {
                    *current_term = term;
                    *voted_for = None;
                    // 更新状态...
                }

                // 检查是否可以投票
                let can_vote = term >= *current_term
                    && (voted_for.is_none() || voted_for.as_ref() == Some(&candidate_id))
                    && self.is_log_up_to_date(&log, last_log_index, last_log_term);

                if can_vote {
                    *voted_for = Some(candidate_id);
                }

                RaftMessage::RequestVoteResponse {
                    term: *current_term,
                    vote_granted: can_vote,
                }
            }
            _ => panic!("Expected RequestVote message"),
        }
    }

    /// 处理追加日志
    pub async fn handle_append_entries(&self, req: RaftMessage) -> RaftMessage {
        match req {
            RaftMessage::AppendEntries { term, leader_id, prev_log_index, prev_log_term, entries, leader_commit } => {
                let mut current_term = self.current_term.write().await;
                let mut state = self.state.write().await;
                let mut log = self.log.write().await;

                // 如果任期更高
                if term > *current_term {
                    *current_term = term;
                    *state = RaftState::Follower { leader: Some(leader_id.clone()) };
                }

                // 检查前置日志匹配
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
                        match_index: 0,
                    };
                }

                // 追加新日志条目
                for entry in entries {
                    if entry.index <= log.len() as u64 {
                        // 冲突，删除后续所有条目
                        log.truncate((entry.index - 1) as usize);
                    }
                    log.push(entry);
                }

                // 更新提交索引
                let mut commit_index = self.commit_index.write().await;
                if leader_commit > *commit_index {
                    *commit_index = leader_commit.min(log.len() as u64);
                }

                RaftMessage::AppendEntriesResponse {
                    term: *current_term,
                    success: true,
                    match_index: log.len() as u64,
                }
            }
            _ => panic!("Expected AppendEntries message"),
        }
    }

    fn is_log_up_to_date(&self, log: &[LogEntry], last_index: LogIndex, last_term: Term) -> bool {
        let my_last_term = log.last().map(|e| e.term).unwrap_or(0);
        let my_last_index = log.len() as u64;

        last_term > my_last_term ||
            (last_term == my_last_term && last_index >= my_last_index)
    }
}
```

### 2.2 领导者选举

```rust
use rand::Rng;
use std::time::Duration;

/// Raft 选举超时配置
pub struct ElectionConfig {
    /// 最小超时（毫秒）
    pub min_timeout_ms: u64,
    /// 最大超时（毫秒）
    pub max_timeout_ms: u64,
    /// 心跳间隔（毫秒）
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

/// 领导者选举实现
pub struct Election {
    node: Arc<RaftNode>,
    config: ElectionConfig,
}

impl Election {
    pub fn new(node: Arc<RaftNode>, config: ElectionConfig) -> Self {
        Self { node, config }
    }

    /// 启动选举超时循环
    pub async fn run(self) {
        let mut timeout = self.random_timeout();

        loop {
            tokio::select! {
                _ = tokio::time::sleep(timeout) => {
                    // 超时，开始选举
                    self.start_election().await;
                    timeout = self.random_timeout();
                }
                // 其他消息处理...
            }
        }
    }

    /// 随机超时（避免活锁）
    fn random_timeout(&self) -> Duration {
        let mut rng = rand::thread_rng();
        let ms = rng.gen_range(self.config.min_timeout_ms..self.config.max_timeout_ms);
        Duration::from_millis(ms)
    }

    /// 开始选举
    async fn start_election(&self) {
        // 1. 增加任期，转为候选者
        {
            let mut term = self.node.current_term.write().await;
            *term += 1;
        }

        {
            let mut voted_for = self.node.voted_for.write().await;
            *voted_for = Some(self.node.id.clone());
        }

        {
            let mut state = self.node.state.write().await;
            *state = RaftState::Candidate { votes_received: {
                let mut set = HashSet::new();
                set.insert(self.node.id.clone());
                set
            }};
        }

        // 2. 获取日志信息
        let (last_log_index, last_log_term) = {
            let log = self.node.log.read().await;
            let last = log.last();
            (
                log.len() as u64,
                last.map(|e| e.term).unwrap_or(0),
            )
        };

        let current_term = *self.node.current_term.read().await;

        // 3. 向所有节点发送请求投票
        let vote_req = RaftMessage::RequestVote {
            term: current_term,
            candidate_id: self.node.id.clone(),
            last_log_index,
            last_log_term,
        };

        // 并行发送投票请求
        let mut vote_futures = vec![];
        for peer in &self.node.peers {
            let req = vote_req.clone();
            let peer_id = peer.clone();

            vote_futures.push(async move {
                // 模拟网络请求
                tokio::time::sleep(Duration::from_millis(10)).await;

                // 返回模拟响应
                RaftMessage::RequestVoteResponse {
                    term: current_term,
                    vote_granted: true, // 简化
                }
            });
        }

        // 收集投票
        let responses = futures::future::join_all(vote_futures).await;

        // 4. 统计票数
        let mut votes = 1; // 自己
        for resp in responses {
            if let RaftMessage::RequestVoteResponse { term, vote_granted } = resp {
                if vote_granted {
                    votes += 1;
                }

                // 检查是否发现更高任期
                if term > current_term {
                    // 转为跟随者
                    let mut state = self.node.state.write().await;
                    *state = RaftState::Follower { leader: None };
                    return;
                }
            }
        }

        // 5. 检查是否当选
        let majority = (self.node.peers.len() + 1) / 2 + 1;
        if votes >= majority {
            self.become_leader().await;
        }
    }

    /// 转为领导者
    async fn become_leader(&self) {
        let log_len = self.node.log.read().await.len() as u64;

        let mut next_index = HashMap::new();
        let mut match_index = HashMap::new();

        for peer in &self.node.peers {
            next_index.insert(peer.clone(), log_len + 1);
            match_index.insert(peer.clone(), 0);
        }

        {
            let mut state = self.node.state.write().await;
            *state = RaftState::Leader { next_index, match_index };
        }

        println!("Node {} became leader", self.node.id);

        // 立即发送心跳
        self.send_heartbeats().await;
    }

    /// 发送心跳
    async fn send_heartbeats(&self) {
        // 实现...
    }
}
```

（继续...）
