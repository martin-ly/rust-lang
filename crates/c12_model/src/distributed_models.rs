//! 分布式设计机制和多线程多任务模型
//! 
//! 本模块实现了分布式系统的设计模式和建模，包括：
//! - 一致性模型
//! - 分区容错机制
//! - CAP定理实现
//! - 分布式共识算法
//! - 多线程多任务模型
//! - 负载均衡策略
//! - 故障检测和恢复
//! - 分布式事务
//! 
//! 充分利用 Rust 1.90 的并发安全特性

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, RwLock, Mutex, atomic::{AtomicU64, AtomicBool, Ordering}};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use std::thread::{self, JoinHandle};
use std::net::SocketAddr;
use serde::{Deserialize, Serialize};
use crate::error::ModelError;


/// 分布式模型结果类型
pub type DistributedResult<T> = Result<T, ModelError>;

/// 节点标识符
pub type NodeId = String;

/// 消息标识符
pub type MessageId = u64;

/// 时间戳类型
pub type Timestamp = u64;

/// 一致性级别
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ConsistencyLevel {
    /// 强一致性
    Strong,
    /// 最终一致性
    Eventual,
    /// 因果一致性
    Causal,
    /// 会话一致性
    Session,
    /// 单调读一致性
    MonotonicRead,
    /// 单调写一致性
    MonotonicWrite,
    /// 读写一致性
    ReadYourWrites,
}

/// CAP定理属性
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CAPProperty {
    /// 一致性 (Consistency)
    Consistency,
    /// 可用性 (Availability)
    Availability,
    /// 分区容错性 (Partition Tolerance)
    PartitionTolerance,
}

/// 分布式系统配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistributedSystemConfig {
    /// 节点数量
    pub node_count: usize,
    /// 复制因子
    pub replication_factor: usize,
    /// 一致性级别
    pub consistency_level: ConsistencyLevel,
    /// 选择的CAP属性（最多2个）
    pub cap_properties: Vec<CAPProperty>,
    /// 心跳间隔
    pub heartbeat_interval: Duration,
    /// 故障检测超时
    pub failure_detection_timeout: Duration,
    /// 消息重试次数
    pub max_retries: u32,
    /// 分区恢复策略
    pub partition_recovery_strategy: PartitionRecoveryStrategy,
}

impl Default for DistributedSystemConfig {
    fn default() -> Self {
        Self {
            node_count: 3,
            replication_factor: 2,
            consistency_level: ConsistencyLevel::Eventual,
            cap_properties: vec![CAPProperty::Availability, CAPProperty::PartitionTolerance],
            heartbeat_interval: Duration::from_secs(1),
            failure_detection_timeout: Duration::from_secs(5),
            max_retries: 3,
            partition_recovery_strategy: PartitionRecoveryStrategy::LastWriterWins,
        }
    }
}

/// 分区恢复策略
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PartitionRecoveryStrategy {
    /// 最后写入者获胜
    LastWriterWins,
    /// 向量时钟
    VectorClock,
    /// 多版本并发控制
    MVCC,
    /// 手动解决
    Manual,
}

/// 节点状态
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NodeState {
    /// 活跃
    Active,
    /// 可疑
    Suspected,
    /// 失败
    Failed,
    /// 恢复中
    Recovering,
    /// 离线
    Offline,
}

/// 分布式节点
#[derive(Debug, Clone)]
pub struct DistributedNode {
    pub id: NodeId,
    pub address: SocketAddr,
    pub state: NodeState,
    pub last_heartbeat: Instant,
    pub vector_clock: VectorClock,
    pub data_store: Arc<RwLock<HashMap<String, VersionedValue>>>,
    pub message_log: Arc<RwLock<Vec<LogEntry>>>,
}

impl DistributedNode {
    pub fn new(id: NodeId, address: SocketAddr) -> Self {
        Self {
            id: id.clone(),
            address,
            state: NodeState::Active,
            last_heartbeat: Instant::now(),
            vector_clock: VectorClock::new(id),
            data_store: Arc::new(RwLock::new(HashMap::new())),
            message_log: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    /// 更新心跳
    pub fn update_heartbeat(&mut self) {
        self.last_heartbeat = Instant::now();
        if self.state == NodeState::Suspected {
            self.state = NodeState::Active;
        }
    }
    
    /// 检查是否超时
    pub fn is_timeout(&self, timeout: Duration) -> bool {
        self.last_heartbeat.elapsed() > timeout
    }
    
    /// 设置为可疑状态
    pub fn mark_suspected(&mut self) {
        if self.state == NodeState::Active {
            self.state = NodeState::Suspected;
        }
    }
    
    /// 设置为失败状态
    pub fn mark_failed(&mut self) {
        self.state = NodeState::Failed;
    }
    
    /// 读取数据
    pub fn read(&self, key: &str) -> Option<VersionedValue> {
        self.data_store.read().unwrap().get(key).cloned()
    }
    
    /// 写入数据
    pub fn write(&mut self, key: String, value: String) -> DistributedResult<()> {
        self.vector_clock.increment(&self.id);
        let versioned_value = VersionedValue {
            value,
            version: self.vector_clock.clone(),
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis() as u64,
        };
        
        self.data_store.write().unwrap().insert(key.clone(), versioned_value.clone());
        
        // 记录到消息日志
        let log_entry = LogEntry {
            id: self.generate_message_id(),
            operation: Operation::Write { key, value: versioned_value },
            timestamp: self.vector_clock.get_time(&self.id),
            node_id: self.id.clone(),
        };
        
        self.message_log.write().unwrap().push(log_entry);
        Ok(())
    }
    
    fn generate_message_id(&self) -> MessageId {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        COUNTER.fetch_add(1, Ordering::SeqCst)
    }
}

/// 向量时钟
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VectorClock {
    clocks: HashMap<NodeId, Timestamp>,
    node_id: NodeId,
}

impl VectorClock {
    pub fn new(node_id: NodeId) -> Self {
        let mut clocks = HashMap::new();
        clocks.insert(node_id.clone(), 0);
        Self { clocks, node_id }
    }
    
    /// 递增本地时钟
    pub fn increment(&mut self, node_id: &NodeId) {
        let current = self.clocks.get(node_id).unwrap_or(&0);
        self.clocks.insert(node_id.clone(), current + 1);
    }
    
    /// 更新时钟（接收到消息时）
    pub fn update(&mut self, other: &VectorClock) {
        for (node_id, &timestamp) in &other.clocks {
            let current = self.clocks.get(node_id).unwrap_or(&0);
            self.clocks.insert(node_id.clone(), (*current).max(timestamp));
        }
        // 递增本地时钟
        let node_id = self.node_id.clone();
        self.increment(&node_id);
    }
    
    /// 获取指定节点的时间戳
    pub fn get_time(&self, node_id: &NodeId) -> Timestamp {
        *self.clocks.get(node_id).unwrap_or(&0)
    }
    
    /// 比较两个向量时钟
    pub fn compare(&self, other: &VectorClock) -> ClockOrdering {
        let mut less_than = false;
        let mut greater_than = false;
        
        // 获取所有节点ID
        let all_nodes: HashSet<_> = self.clocks.keys()
            .chain(other.clocks.keys())
            .collect();
        
        for node_id in all_nodes {
            let self_time = self.get_time(node_id);
            let other_time = other.get_time(node_id);
            
            if self_time < other_time {
                less_than = true;
            } else if self_time > other_time {
                greater_than = true;
            }
        }
        
        match (less_than, greater_than) {
            (true, false) => ClockOrdering::Before,
            (false, true) => ClockOrdering::After,
            (false, false) => ClockOrdering::Equal,
            (true, true) => ClockOrdering::Concurrent,
        }
    }
}

/// 时钟排序
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ClockOrdering {
    Before,
    After,
    Equal,
    Concurrent,
}

/// 版本化值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VersionedValue {
    pub value: String,
    pub version: VectorClock,
    pub timestamp: Timestamp,
}

/// 操作类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Operation {
    Read { key: String },
    Write { key: String, value: VersionedValue },
    Delete { key: String },
}

/// 日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub id: MessageId,
    pub operation: Operation,
    pub timestamp: Timestamp,
    pub node_id: NodeId,
}

/// 分布式消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DistributedMessage {
    pub id: MessageId,
    pub sender: NodeId,
    pub receiver: NodeId,
    pub message_type: MessageType,
    pub payload: MessagePayload,
    pub vector_clock: VectorClock,
    pub timestamp: Timestamp,
}

/// 消息类型
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum MessageType {
    Heartbeat,
    DataReplication,
    ConsensusProposal,
    ConsensusVote,
    PartitionRecovery,
    LeaderElection,
}

/// 消息载荷
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MessagePayload {
    Heartbeat { node_state: NodeState },
    DataReplication { entries: Vec<LogEntry> },
    ConsensusProposal { proposal_id: u64, value: String },
    ConsensusVote { proposal_id: u64, vote: bool },
    PartitionRecovery { data_snapshot: HashMap<String, VersionedValue> },
    LeaderElection { term: u64, candidate_id: NodeId },
}

/// 共识算法实现（简化的Raft）
#[derive(Debug)]
pub struct ConsensusAlgorithm {
    node_id: NodeId,
    current_term: AtomicU64,
    voted_for: Arc<RwLock<Option<NodeId>>>,
    log: Arc<RwLock<Vec<LogEntry>>>,
    #[allow(dead_code)]
    commit_index: AtomicU64,
    #[allow(dead_code)]
    last_applied: AtomicU64,
    state: Arc<RwLock<ConsensusState>>,
    peers: Arc<RwLock<HashMap<NodeId, DistributedNode>>>,
}

/// 共识状态
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConsensusState {
    Follower,
    Candidate,
    Leader,
}

impl ConsensusAlgorithm {
    pub fn new(node_id: NodeId) -> Self {
        Self {
            node_id,
            current_term: AtomicU64::new(0),
            voted_for: Arc::new(RwLock::new(None)),
            log: Arc::new(RwLock::new(Vec::new())),
            commit_index: AtomicU64::new(0),
            last_applied: AtomicU64::new(0),
            state: Arc::new(RwLock::new(ConsensusState::Follower)),
            peers: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 开始选举
    pub fn start_election(&self) -> DistributedResult<()> {
        let mut state = self.state.write().unwrap();
        *state = ConsensusState::Candidate;
        
        // 递增任期
        let new_term = self.current_term.fetch_add(1, Ordering::SeqCst) + 1;
        
        // 投票给自己
        *self.voted_for.write().unwrap() = Some(self.node_id.clone());
        
        println!("Node {} starting election for term {}", self.node_id, new_term);
        
        // 发送投票请求给所有节点
        let peers = self.peers.read().unwrap();
        let mut votes = 1; // 自己的票
        
        for (peer_id, _peer) in peers.iter() {
            // 简化实现：假设所有节点都会投票
            if self.request_vote(peer_id, new_term)? {
                votes += 1;
            }
        }
        
        // 检查是否获得多数票
        let majority = (peers.len() + 1) / 2 + 1;
        if votes >= majority {
            *self.state.write().unwrap() = ConsensusState::Leader;
            println!("Node {} became leader for term {}", self.node_id, new_term);
        } else {
            *self.state.write().unwrap() = ConsensusState::Follower;
        }
        
        Ok(())
    }
    
    fn request_vote(&self, peer_id: &NodeId, term: u64) -> DistributedResult<bool> {
        // 简化实现：总是返回true
        println!("Requesting vote from {} for term {}", peer_id, term);
        Ok(true)
    }
    
    /// 追加日志条目
    pub fn append_entry(&self, entry: LogEntry) -> DistributedResult<()> {
        let state = self.state.read().unwrap();
        if *state != ConsensusState::Leader {
            return Err(ModelError::ValidationError("Only leader can append entries".to_string()));
        }
        
        self.log.write().unwrap().push(entry);
        
        // 复制到所有跟随者
        self.replicate_to_followers()?;
        
        Ok(())
    }
    
    fn replicate_to_followers(&self) -> DistributedResult<()> {
        let peers = self.peers.read().unwrap();
        for (peer_id, _peer) in peers.iter() {
            // 简化实现：假设复制总是成功
            println!("Replicating log to {}", peer_id);
        }
        Ok(())
    }
    
    /// 获取当前状态
    pub fn get_state(&self) -> ConsensusState {
        self.state.read().unwrap().clone()
    }
    
    /// 获取当前任期
    pub fn get_current_term(&self) -> u64 {
        self.current_term.load(Ordering::SeqCst)
    }
}

/// 分布式系统管理器
#[derive(Debug)]
pub struct DistributedSystemManager {
    config: DistributedSystemConfig,
    nodes: Arc<RwLock<HashMap<NodeId, DistributedNode>>>,
    consensus: Arc<RwLock<HashMap<NodeId, ConsensusAlgorithm>>>,
    partition_detector: PartitionDetector,
    load_balancer: LoadBalancer,
    failure_detector: FailureDetector,
    is_running: AtomicBool,
}

impl DistributedSystemManager {
    pub fn new(config: DistributedSystemConfig) -> Self {
        Self {
            config: config.clone(),
            nodes: Arc::new(RwLock::new(HashMap::new())),
            consensus: Arc::new(RwLock::new(HashMap::new())),
            partition_detector: PartitionDetector::new(config.clone()),
            load_balancer: LoadBalancer::new(LoadBalancingStrategy::RoundRobin),
            failure_detector: FailureDetector::new(config.failure_detection_timeout),
            is_running: AtomicBool::new(false),
        }
    }
    
    /// 添加节点
    pub fn add_node(&self, node: DistributedNode) -> DistributedResult<()> {
        let node_id = node.id.clone();
        
        // 添加节点
        self.nodes.write().unwrap().insert(node_id.clone(), node);
        
        // 创建共识算法实例
        let consensus = ConsensusAlgorithm::new(node_id.clone());
        self.consensus.write().unwrap().insert(node_id.clone(), consensus);
        
        // 更新负载均衡器
        self.load_balancer.add_node(node_id.clone());
        
        println!("Added node: {}", node_id);
        Ok(())
    }
    
    /// 移除节点
    pub fn remove_node(&self, node_id: &NodeId) -> DistributedResult<()> {
        self.nodes.write().unwrap().remove(node_id);
        self.consensus.write().unwrap().remove(node_id);
        self.load_balancer.remove_node(node_id);
        
        println!("Removed node: {}", node_id);
        Ok(())
    }
    
    /// 启动系统
    pub fn start(&self) -> DistributedResult<()> {
        self.is_running.store(true, Ordering::SeqCst);
        
        // 启动心跳检测
        self.start_heartbeat_monitoring();
        
        // 启动故障检测
        self.failure_detector.start();
        
        // 启动分区检测
        self.partition_detector.start();
        
        println!("Distributed system started");
        Ok(())
    }
    
    /// 停止系统
    pub fn stop(&self) -> DistributedResult<()> {
        self.is_running.store(false, Ordering::SeqCst);
        
        self.failure_detector.stop();
        self.partition_detector.stop();
        
        println!("Distributed system stopped");
        Ok(())
    }
    
    fn start_heartbeat_monitoring(&self) {
        let nodes = Arc::clone(&self.nodes);
        let interval = self.config.heartbeat_interval;
        let is_running = Arc::new(AtomicBool::new(true));
        
        thread::spawn(move || {
            while is_running.load(Ordering::SeqCst) {
                {
                    let mut nodes_guard = nodes.write().unwrap();
                    for (node_id, node) in nodes_guard.iter_mut() {
                        if node.is_timeout(interval * 3) {
                            node.mark_suspected();
                            println!("Node {} marked as suspected", node_id);
                        }
                    }
                }
                
                thread::sleep(interval);
            }
        });
    }
    
    /// 读取数据
    pub fn read(&self, key: &str) -> DistributedResult<Option<String>> {
        // 根据一致性级别选择读取策略
        match self.config.consistency_level {
            ConsistencyLevel::Strong => self.strong_consistent_read(key),
            ConsistencyLevel::Eventual => self.eventual_consistent_read(key),
            _ => self.eventual_consistent_read(key), // 简化实现
        }
    }
    
    fn strong_consistent_read(&self, key: &str) -> DistributedResult<Option<String>> {
        // 从多数节点读取并比较版本
        let nodes = self.nodes.read().unwrap();
        let mut values = Vec::new();
        
        for (_, node) in nodes.iter() {
            if let Some(versioned_value) = node.read(key) {
                values.push(versioned_value);
            }
        }
        
        if values.is_empty() {
            return Ok(None);
        }
        
        // 选择最新版本
        values.sort_by(|a, b| b.timestamp.cmp(&a.timestamp));
        Ok(Some(values[0].value.clone()))
    }
    
    fn eventual_consistent_read(&self, key: &str) -> DistributedResult<Option<String>> {
        // 从任意可用节点读取
        let node_id = self.load_balancer.select_node()?;
        let nodes = self.nodes.read().unwrap();
        
        if let Some(node) = nodes.get(&node_id) {
            if let Some(versioned_value) = node.read(key) {
                return Ok(Some(versioned_value.value));
            }
        }
        
        Ok(None)
    }
    
    /// 写入数据
    pub fn write(&self, key: String, value: String) -> DistributedResult<()> {
        match self.config.consistency_level {
            ConsistencyLevel::Strong => self.strong_consistent_write(key, value),
            ConsistencyLevel::Eventual => self.eventual_consistent_write(key, value),
            _ => self.eventual_consistent_write(key, value), // 简化实现
        }
    }
    
    fn strong_consistent_write(&self, key: String, value: String) -> DistributedResult<()> {
        // 写入到多数节点
        let mut nodes = self.nodes.write().unwrap();
        let majority = (nodes.len() / 2) + 1;
        let mut successful_writes = 0;
        
        for (_, node) in nodes.iter_mut() {
            if node.write(key.clone(), value.clone()).is_ok() {
                successful_writes += 1;
                if successful_writes >= majority {
                    break;
                }
            }
        }
        
        if successful_writes >= majority {
            Ok(())
        } else {
            Err(ModelError::ValidationError("Failed to achieve majority write".to_string()))
        }
    }
    
    fn eventual_consistent_write(&self, key: String, value: String) -> DistributedResult<()> {
        // 写入到任意可用节点，然后异步复制
        let node_id = self.load_balancer.select_node()?;
        let mut nodes = self.nodes.write().unwrap();
        
        if let Some(node) = nodes.get_mut(&node_id) {
            node.write(key.clone(), value.clone())?;
            
            // 异步复制到其他节点
            self.async_replicate(key, value, &node_id);
            
            Ok(())
        } else {
            Err(ModelError::ValidationError("No available nodes".to_string()))
        }
    }
    
    fn async_replicate(&self, key: String, value: String, exclude_node: &NodeId) {
        let nodes = Arc::clone(&self.nodes);
        let exclude_node = exclude_node.clone();
        
        thread::spawn(move || {
            let mut nodes_guard = nodes.write().unwrap();
            for (node_id, node) in nodes_guard.iter_mut() {
                if node_id != &exclude_node {
                    let _ = node.write(key.clone(), value.clone());
                }
            }
        });
    }
    
    /// 获取系统状态
    pub fn get_system_status(&self) -> SystemStatus {
        let nodes = self.nodes.read().unwrap();
        let mut node_states = HashMap::new();
        let mut active_nodes = 0;
        let mut failed_nodes = 0;
        
        for (node_id, node) in nodes.iter() {
            node_states.insert(node_id.clone(), node.state.clone());
            match node.state {
                NodeState::Active => active_nodes += 1,
                NodeState::Failed => failed_nodes += 1,
                _ => {}
            }
        }
        
        let is_partitioned = self.partition_detector.is_partitioned();
        let current_leader = self.get_current_leader();
        
        SystemStatus {
            total_nodes: nodes.len(),
            active_nodes,
            failed_nodes,
            is_partitioned,
            current_leader,
            node_states,
            consistency_level: self.config.consistency_level.clone(),
            cap_properties: self.config.cap_properties.clone(),
        }
    }
    
    fn get_current_leader(&self) -> Option<NodeId> {
        let consensus_map = self.consensus.read().unwrap();
        for (node_id, consensus) in consensus_map.iter() {
            if consensus.get_state() == ConsensusState::Leader {
                return Some(node_id.clone());
            }
        }
        None
    }
}

/// 系统状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemStatus {
    pub total_nodes: usize,
    pub active_nodes: usize,
    pub failed_nodes: usize,
    pub is_partitioned: bool,
    pub current_leader: Option<NodeId>,
    pub node_states: HashMap<NodeId, NodeState>,
    pub consistency_level: ConsistencyLevel,
    pub cap_properties: Vec<CAPProperty>,
}

/// 负载均衡策略
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LoadBalancingStrategy {
    RoundRobin,
    LeastConnections,
    WeightedRoundRobin,
    Random,
    ConsistentHashing,
}

/// 负载均衡器
#[derive(Debug)]
pub struct LoadBalancer {
    strategy: LoadBalancingStrategy,
    nodes: Arc<RwLock<Vec<NodeId>>>,
    current_index: AtomicU64,
    node_weights: Arc<RwLock<HashMap<NodeId, u32>>>,
}

impl LoadBalancer {
    pub fn new(strategy: LoadBalancingStrategy) -> Self {
        Self {
            strategy,
            nodes: Arc::new(RwLock::new(Vec::new())),
            current_index: AtomicU64::new(0),
            node_weights: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub fn add_node(&self, node_id: NodeId) {
        self.nodes.write().unwrap().push(node_id.clone());
        self.node_weights.write().unwrap().insert(node_id, 1);
    }
    
    pub fn remove_node(&self, node_id: &NodeId) {
        let mut nodes = self.nodes.write().unwrap();
        nodes.retain(|id| id != node_id);
        self.node_weights.write().unwrap().remove(node_id);
    }
    
    pub fn select_node(&self) -> DistributedResult<NodeId> {
        let nodes = self.nodes.read().unwrap();
        if nodes.is_empty() {
            return Err(ModelError::ValidationError("No available nodes".to_string()));
        }
        
        match self.strategy {
            LoadBalancingStrategy::RoundRobin => {
                let index = self.current_index.fetch_add(1, Ordering::SeqCst) as usize % nodes.len();
                Ok(nodes[index].clone())
            }
            LoadBalancingStrategy::Random => {
                let index = fastrand::usize(0..nodes.len());
                Ok(nodes[index].clone())
            }
            _ => {
                // 简化实现：默认使用轮询
                let index = self.current_index.fetch_add(1, Ordering::SeqCst) as usize % nodes.len();
                Ok(nodes[index].clone())
            }
        }
    }
}

/// 故障检测器
#[allow(dead_code)]
#[derive(Debug)]
pub struct FailureDetector {
    timeout: Duration,
    is_running: AtomicBool,
    suspected_nodes: Arc<RwLock<HashSet<NodeId>>>,
}

impl FailureDetector {
    pub fn new(timeout: Duration) -> Self {
        Self {
            timeout,
            is_running: AtomicBool::new(false),
            suspected_nodes: Arc::new(RwLock::new(HashSet::new())),
        }
    }
    
    pub fn start(&self) {
        self.is_running.store(true, Ordering::SeqCst);
        println!("Failure detector started");
    }
    
    pub fn stop(&self) {
        self.is_running.store(false, Ordering::SeqCst);
        println!("Failure detector stopped");
    }
    
    pub fn suspect_node(&self, node_id: NodeId) {
        self.suspected_nodes.write().unwrap().insert(node_id.clone());
        println!("Node {} suspected of failure", node_id);
    }
    
    pub fn clear_suspicion(&self, node_id: &NodeId) {
        self.suspected_nodes.write().unwrap().remove(node_id);
        println!("Suspicion cleared for node {}", node_id);
    }
    
    pub fn is_suspected(&self, node_id: &NodeId) -> bool {
        self.suspected_nodes.read().unwrap().contains(node_id)
    }
}

/// 分区检测器
#[allow(dead_code)]
#[derive(Debug)]
pub struct PartitionDetector {
    config: DistributedSystemConfig,
    is_running: AtomicBool,
    partitioned: AtomicBool,
}

impl PartitionDetector {
    pub fn new(config: DistributedSystemConfig) -> Self {
        Self {
            config,
            is_running: AtomicBool::new(false),
            partitioned: AtomicBool::new(false),
        }
    }
    
    pub fn start(&self) {
        self.is_running.store(true, Ordering::SeqCst);
        println!("Partition detector started");
    }
    
    pub fn stop(&self) {
        self.is_running.store(false, Ordering::SeqCst);
        println!("Partition detector stopped");
    }
    
    pub fn is_partitioned(&self) -> bool {
        self.partitioned.load(Ordering::SeqCst)
    }
    
    pub fn detect_partition(&self, active_nodes: usize, total_nodes: usize) -> bool {
        let majority = (total_nodes / 2) + 1;
        let is_partitioned = active_nodes < majority;
        
        self.partitioned.store(is_partitioned, Ordering::SeqCst);
        
        if is_partitioned {
            println!("Network partition detected: {}/{} nodes active", active_nodes, total_nodes);
        }
        
        is_partitioned
    }
}

/// 多线程任务执行器
#[allow(dead_code)]
pub struct MultiThreadTaskExecutor {
    thread_pool: Vec<JoinHandle<()>>,
    task_queue: Arc<Mutex<VecDeque<Box<dyn FnOnce() + Send + 'static>>>>,
    is_running: Arc<AtomicBool>,
    #[allow(dead_code)]
    thread_count: usize,
}

impl std::fmt::Debug for MultiThreadTaskExecutor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MultiThreadTaskExecutor")
            .field("thread_count", &self.thread_count)
            .field("is_running", &self.is_running)
            .field("task_queue_len", &self.task_queue.lock().unwrap().len())
            .finish()
    }
}

impl MultiThreadTaskExecutor {
    pub fn new(thread_count: usize) -> Self {
        Self {
            thread_pool: Vec::new(),
            task_queue: Arc::new(Mutex::new(VecDeque::new())),
            is_running: Arc::new(AtomicBool::new(false)),
            thread_count,
        }
    }
    
    pub fn start(&mut self) -> DistributedResult<()> {
        self.is_running.store(true, Ordering::SeqCst);
        
        for i in 0..self.thread_count {
            let task_queue = Arc::clone(&self.task_queue);
            let is_running = Arc::clone(&self.is_running);
            
            let handle = thread::spawn(move || {
                println!("Worker thread {} started", i);
                
                while is_running.load(Ordering::SeqCst) {
                    let task = {
                        let mut queue = task_queue.lock().unwrap();
                        queue.pop_front()
                    };
                    
                    if let Some(task) = task {
                        task();
                    } else {
                        thread::sleep(Duration::from_millis(10));
                    }
                }
                
                println!("Worker thread {} stopped", i);
            });
            
            self.thread_pool.push(handle);
        }
        
        println!("Multi-thread task executor started with {} threads", self.thread_count);
        Ok(())
    }
    
    pub fn submit_task<F>(&self, task: F) -> DistributedResult<()>
    where
        F: FnOnce() + Send + 'static,
    {
        if !self.is_running.load(Ordering::SeqCst) {
            return Err(ModelError::ValidationError("Executor is not running".to_string()));
        }
        
        self.task_queue.lock().unwrap().push_back(Box::new(task));
        Ok(())
    }
    
    pub fn stop(&mut self) -> DistributedResult<()> {
        self.is_running.store(false, Ordering::SeqCst);
        
        // 等待所有线程完成
        while let Some(handle) = self.thread_pool.pop() {
            handle.join().map_err(|_| {
                ModelError::ValidationError("Failed to join thread".to_string())
            })?;
        }
        
        println!("Multi-thread task executor stopped");
        Ok(())
    }
    
    pub fn get_queue_size(&self) -> usize {
        self.task_queue.lock().unwrap().len()
    }
}

/// CAP定理分析器
#[allow(dead_code)]
#[derive(Debug)]
pub struct CAPTheoremAnalyzer;

impl CAPTheoremAnalyzer {
    /// 分析CAP属性组合的权衡
    pub fn analyze_tradeoffs(properties: &[CAPProperty]) -> CAPAnalysis {
        if properties.len() > 2 {
            return CAPAnalysis {
                is_valid: false,
                selected_properties: properties.to_vec(),
                sacrificed_property: None,
                tradeoffs: vec!["CAP theorem states that only 2 out of 3 properties can be guaranteed".to_string()],
                recommendations: vec!["Choose at most 2 properties".to_string()],
            };
        }
        
        let all_properties = vec![
            CAPProperty::Consistency,
            CAPProperty::Availability,
            CAPProperty::PartitionTolerance,
        ];
        
        let sacrificed = all_properties.into_iter()
            .find(|p| !properties.contains(p));
        
        let (tradeoffs, recommendations) = match properties {
            props if props.contains(&CAPProperty::Consistency) && props.contains(&CAPProperty::Availability) => {
                (
                    vec![
                        "System cannot handle network partitions".to_string(),
                        "Single point of failure risk".to_string(),
                    ],
                    vec![
                        "Use in environments with reliable networks".to_string(),
                        "Implement redundancy at infrastructure level".to_string(),
                    ]
                )
            }
            props if props.contains(&CAPProperty::Consistency) && props.contains(&CAPProperty::PartitionTolerance) => {
                (
                    vec![
                        "System may become unavailable during partitions".to_string(),
                        "Higher latency due to consensus requirements".to_string(),
                    ],
                    vec![
                        "Implement timeout mechanisms".to_string(),
                        "Use strong consistency algorithms like Raft".to_string(),
                    ]
                )
            }
            props if props.contains(&CAPProperty::Availability) && props.contains(&CAPProperty::PartitionTolerance) => {
                (
                    vec![
                        "Eventual consistency only".to_string(),
                        "Potential for conflicting updates".to_string(),
                    ],
                    vec![
                        "Implement conflict resolution strategies".to_string(),
                        "Use vector clocks for causality tracking".to_string(),
                    ]
                )
            }
            _ => (vec![], vec![])
        };
        
        CAPAnalysis {
            is_valid: properties.len() <= 2,
            selected_properties: properties.to_vec(),
            sacrificed_property: sacrificed,
            tradeoffs,
            recommendations,
        }
    }
}

/// CAP分析结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CAPAnalysis {
    pub is_valid: bool,
    pub selected_properties: Vec<CAPProperty>,
    pub sacrificed_property: Option<CAPProperty>,
    pub tradeoffs: Vec<String>,
    pub recommendations: Vec<String>,
}

/// Paxos共识算法实现
/// 
/// Paxos是一种经典的分布式共识算法，能在异步网络中达成一致
#[derive(Debug, Clone)]
pub struct PaxosProtocol {
    /// 节点ID
    node_id: NodeId,
    /// 提议编号
    proposal_number: Arc<AtomicU64>,
    /// 已接受的提议
    accepted_proposal: Arc<RwLock<Option<(u64, String)>>>,
    /// 已承诺的最大编号
    promised_number: Arc<AtomicU64>,
    /// 参与者列表
    participants: Arc<RwLock<Vec<NodeId>>>,
}

/// Paxos消息类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PaxosMessage {
    /// Prepare阶段 - 准备消息 (proposal_number)
    Prepare(u64),
    /// Promise阶段 - 承诺消息 (proposal_number, accepted_value)
    Promise(u64, Option<(u64, String)>),
    /// Accept阶段 - 接受请求 (proposal_number, value)
    Accept(u64, String),
    /// Accepted阶段 - 已接受消息 (proposal_number, value)
    Accepted(u64, String),
    /// Learn阶段 - 学习消息 (value)
    Learn(String),
}

impl PaxosProtocol {
    /// 创建新的Paxos协议实例
    pub fn new(node_id: NodeId) -> Self {
        Self {
            node_id,
            proposal_number: Arc::new(AtomicU64::new(0)),
            accepted_proposal: Arc::new(RwLock::new(None)),
            promised_number: Arc::new(AtomicU64::new(0)),
            participants: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    /// 添加参与者
    pub fn add_participant(&self, participant: NodeId) -> DistributedResult<()> {
        let mut participants = self.participants.write()
            .map_err(|e| ModelError::LockError(format!("无法获取参与者写锁: {}", e)))?;
        
        if !participants.contains(&participant) {
            participants.push(participant);
        }
        Ok(())
    }
    
    /// 提议者角色：发起提议
    pub fn propose(&self, _value: String) -> DistributedResult<u64> {
        // 生成唯一的提议编号
        let proposal_num = self.proposal_number.fetch_add(1, Ordering::SeqCst);
        Ok(proposal_num)
    }
    
    /// 获取节点ID
    pub fn node_id(&self) -> &str {
        &self.node_id
    }
    
    /// 接受者角色：处理Prepare消息
    pub fn handle_prepare(&self, proposal_number: u64) -> DistributedResult<PaxosMessage> {
        let promised = self.promised_number.load(Ordering::SeqCst);
        
        if proposal_number > promised {
            // 更新承诺的编号
            self.promised_number.store(proposal_number, Ordering::SeqCst);
            
            // 返回已接受的提议（如果有）
            let accepted = self.accepted_proposal.read()
                .map_err(|e| ModelError::LockError(format!("无法获取已接受提议读锁: {}", e)))?;
            
            Ok(PaxosMessage::Promise(proposal_number, accepted.clone()))
        } else {
            Err(ModelError::ComputationError(
                format!("提议编号{}小于等于已承诺的编号{}", proposal_number, promised)
            ))
        }
    }
    
    /// 接受者角色：处理Accept消息
    pub fn handle_accept(&self, proposal_number: u64, value: String) -> DistributedResult<PaxosMessage> {
        let promised = self.promised_number.load(Ordering::SeqCst);
        
        if proposal_number >= promised {
            // 接受这个提议
            let mut accepted = self.accepted_proposal.write()
                .map_err(|e| ModelError::LockError(format!("无法获取已接受提议写锁: {}", e)))?;
            
            *accepted = Some((proposal_number, value.clone()));
            Ok(PaxosMessage::Accepted(proposal_number, value))
        } else {
            Err(ModelError::ComputationError(
                format!("提议编号{}小于已承诺的编号{}", proposal_number, promised)
            ))
        }
    }
    
    /// 学习者角色：学习已达成共识的值
    pub fn learn(&self, value: String) -> DistributedResult<()> {
        let mut accepted = self.accepted_proposal.write()
            .map_err(|e| ModelError::LockError(format!("无法获取已接受提议写锁: {}", e)))?;
        
        *accepted = Some((self.proposal_number.load(Ordering::SeqCst), value));
        Ok(())
    }
    
    /// 获取当前已接受的值
    pub fn get_accepted_value(&self) -> DistributedResult<Option<String>> {
        let accepted = self.accepted_proposal.read()
            .map_err(|e| ModelError::LockError(format!("无法获取已接受提议读锁: {}", e)))?;
        
        Ok(accepted.as_ref().map(|(_, v)| v.clone()))
    }
}

/// 两阶段提交协议（2PC）
/// 
/// 用于分布式事务的原子提交协议
#[derive(Debug)]
pub struct TwoPhaseCommit {
    /// 协调者节点ID
    coordinator_id: NodeId,
    /// 参与者列表
    participants: Arc<RwLock<Vec<NodeId>>>,
    /// 事务状态
    transaction_state: Arc<RwLock<TransactionState>>,
    /// 投票结果
    votes: Arc<RwLock<HashMap<NodeId, VoteResult>>>,
    /// 事务ID
    transaction_id: String,
}

/// 事务状态
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransactionState {
    /// 初始状态
    Init,
    /// 准备阶段
    Preparing,
    /// 已准备
    Prepared,
    /// 提交阶段
    Committing,
    /// 已提交
    Committed,
    /// 回滚阶段
    Aborting,
    /// 已回滚
    Aborted,
}

/// 投票结果
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum VoteResult {
    /// 同意提交
    Yes,
    /// 拒绝提交
    No,
    /// 超时
    Timeout,
}

/// 2PC消息类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TwoPhaseMessage {
    /// 准备请求
    Prepare(String), // transaction_id
    /// 投票响应
    Vote(String, VoteResult), // transaction_id, vote
    /// 提交命令
    Commit(String), // transaction_id
    /// 回滚命令
    Abort(String), // transaction_id
    /// 确认消息
    Ack(String), // transaction_id
}

impl TwoPhaseCommit {
    /// 创建新的2PC协议实例（协调者）
    pub fn new_coordinator(coordinator_id: NodeId, transaction_id: String) -> Self {
        Self {
            coordinator_id,
            participants: Arc::new(RwLock::new(Vec::new())),
            transaction_state: Arc::new(RwLock::new(TransactionState::Init)),
            votes: Arc::new(RwLock::new(HashMap::new())),
            transaction_id,
        }
    }
    
    /// 添加参与者
    pub fn add_participant(&self, participant: NodeId) -> DistributedResult<()> {
        let mut participants = self.participants.write()
            .map_err(|e| ModelError::LockError(format!("无法获取参与者写锁: {}", e)))?;
        
        participants.push(participant);
        Ok(())
    }
    
    /// 阶段1：准备阶段（协调者发起）
    pub fn prepare_phase(&self) -> DistributedResult<bool> {
        // 更新状态
        let mut state = self.transaction_state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态写锁: {}", e)))?;
        
        *state = TransactionState::Preparing;
        drop(state);
        
        // 这里应该向所有参与者发送Prepare消息
        // 实际实现需要网络通信
        
        Ok(true)
    }
    
    /// 处理投票（协调者收集投票）
    pub fn collect_vote(&self, participant: NodeId, vote: VoteResult) -> DistributedResult<()> {
        let mut votes = self.votes.write()
            .map_err(|e| ModelError::LockError(format!("无法获取投票写锁: {}", e)))?;
        
        votes.insert(participant, vote);
        Ok(())
    }
    
    /// 检查所有投票是否通过
    pub fn check_votes(&self) -> DistributedResult<bool> {
        let votes = self.votes.read()
            .map_err(|e| ModelError::LockError(format!("无法获取投票读锁: {}", e)))?;
        
        let participants = self.participants.read()
            .map_err(|e| ModelError::LockError(format!("无法获取参与者读锁: {}", e)))?;
        
        // 检查是否所有参与者都投票了
        if votes.len() != participants.len() {
            return Ok(false);
        }
        
        // 检查是否所有投票都是Yes
        Ok(votes.values().all(|v| *v == VoteResult::Yes))
    }
    
    /// 阶段2：提交阶段
    pub fn commit_phase(&self) -> DistributedResult<()> {
        let mut state = self.transaction_state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态写锁: {}", e)))?;
        
        if self.check_votes()? {
            *state = TransactionState::Committing;
            // 向所有参与者发送Commit消息
            *state = TransactionState::Committed;
        } else {
            *state = TransactionState::Aborting;
            // 向所有参与者发送Abort消息
            *state = TransactionState::Aborted;
        }
        
        Ok(())
    }
    
    /// 参与者：准备事务
    pub fn prepare_transaction(&self) -> DistributedResult<VoteResult> {
        // 参与者检查是否可以提交
        // 这里简化处理，实际需要检查资源、锁等
        
        let mut state = self.transaction_state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态写锁: {}", e)))?;
        
        *state = TransactionState::Prepared;
        Ok(VoteResult::Yes)
    }
    
    /// 参与者：提交事务
    pub fn commit_transaction(&self) -> DistributedResult<()> {
        let mut state = self.transaction_state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态写锁: {}", e)))?;
        
        *state = TransactionState::Committed;
        Ok(())
    }
    
    /// 参与者：回滚事务
    pub fn abort_transaction(&self) -> DistributedResult<()> {
        let mut state = self.transaction_state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态写锁: {}", e)))?;
        
        *state = TransactionState::Aborted;
        Ok(())
    }
    
    /// 获取事务状态
    pub fn get_state(&self) -> DistributedResult<TransactionState> {
        let state = self.transaction_state.read()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态读锁: {}", e)))?;
        
        Ok(state.clone())
    }
    
    /// 获取协调者ID
    pub fn coordinator_id(&self) -> &str {
        &self.coordinator_id
    }
    
    /// 获取事务ID
    pub fn transaction_id(&self) -> &str {
        &self.transaction_id
    }
}

/// 三阶段提交协议（3PC）
/// 
/// 2PC的改进版本，引入超时机制和CanCommit阶段
#[derive(Debug)]
pub struct ThreePhaseCommit {
    /// 协调者节点ID
    coordinator_id: NodeId,
    /// 参与者列表
    participants: Arc<RwLock<Vec<NodeId>>>,
    /// 事务状态
    transaction_state: Arc<RwLock<ThreePhaseState>>,
    /// 投票结果
    can_commit_votes: Arc<RwLock<HashMap<NodeId, bool>>>,
    /// PreCommit确认
    pre_commit_acks: Arc<RwLock<HashSet<NodeId>>>,
    /// 事务ID
    transaction_id: String,
    /// 超时设置
    timeout: Duration,
}

/// 三阶段提交状态
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ThreePhaseState {
    /// 初始状态
    Init,
    /// CanCommit阶段
    CanCommit,
    /// PreCommit阶段
    PreCommit,
    /// DoCommit阶段
    DoCommit,
    /// 已提交
    Committed,
    /// 已回滚
    Aborted,
}

/// 3PC消息类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ThreePhaseMessage {
    /// CanCommit请求
    CanCommit(String), // transaction_id
    /// CanCommit响应
    CanCommitResponse(String, bool), // transaction_id, can_commit
    /// PreCommit请求
    PreCommit(String), // transaction_id
    /// PreCommit确认
    PreCommitAck(String), // transaction_id
    /// DoCommit请求
    DoCommit(String), // transaction_id
    /// DoAbort请求
    DoAbort(String), // transaction_id
    /// 完成确认
    HaveCommitted(String), // transaction_id
}

impl ThreePhaseCommit {
    /// 创建新的3PC协议实例（协调者）
    pub fn new_coordinator(
        coordinator_id: NodeId,
        transaction_id: String,
        timeout: Duration,
    ) -> Self {
        Self {
            coordinator_id,
            participants: Arc::new(RwLock::new(Vec::new())),
            transaction_state: Arc::new(RwLock::new(ThreePhaseState::Init)),
            can_commit_votes: Arc::new(RwLock::new(HashMap::new())),
            pre_commit_acks: Arc::new(RwLock::new(HashSet::new())),
            transaction_id,
            timeout,
        }
    }
    
    /// 添加参与者
    pub fn add_participant(&self, participant: NodeId) -> DistributedResult<()> {
        let mut participants = self.participants.write()
            .map_err(|e| ModelError::LockError(format!("无法获取参与者写锁: {}", e)))?;
        
        participants.push(participant);
        Ok(())
    }
    
    /// 阶段1：CanCommit阶段
    pub fn can_commit_phase(&self) -> DistributedResult<bool> {
        let mut state = self.transaction_state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态写锁: {}", e)))?;
        
        *state = ThreePhaseState::CanCommit;
        drop(state);
        
        // 向所有参与者发送CanCommit请求
        // 实际实现需要网络通信和超时处理
        
        Ok(true)
    }
    
    /// 收集CanCommit投票
    pub fn collect_can_commit_vote(&self, participant: NodeId, can_commit: bool) -> DistributedResult<()> {
        let mut votes = self.can_commit_votes.write()
            .map_err(|e| ModelError::LockError(format!("无法获取投票写锁: {}", e)))?;
        
        votes.insert(participant, can_commit);
        Ok(())
    }
    
    /// 检查CanCommit投票
    pub fn check_can_commit_votes(&self) -> DistributedResult<bool> {
        let votes = self.can_commit_votes.read()
            .map_err(|e| ModelError::LockError(format!("无法获取投票读锁: {}", e)))?;
        
        let participants = self.participants.read()
            .map_err(|e| ModelError::LockError(format!("无法获取参与者读锁: {}", e)))?;
        
        if votes.len() != participants.len() {
            return Ok(false);
        }
        
        Ok(votes.values().all(|&v| v))
    }
    
    /// 阶段2：PreCommit阶段
    pub fn pre_commit_phase(&self) -> DistributedResult<()> {
        let mut state = self.transaction_state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态写锁: {}", e)))?;
        
        if self.check_can_commit_votes()? {
            *state = ThreePhaseState::PreCommit;
            // 向所有参与者发送PreCommit请求
        } else {
            *state = ThreePhaseState::Aborted;
            // 向所有参与者发送Abort请求
        }
        
        Ok(())
    }
    
    /// 收集PreCommit确认
    pub fn collect_pre_commit_ack(&self, participant: NodeId) -> DistributedResult<()> {
        let mut acks = self.pre_commit_acks.write()
            .map_err(|e| ModelError::LockError(format!("无法获取确认写锁: {}", e)))?;
        
        acks.insert(participant);
        Ok(())
    }
    
    /// 检查PreCommit确认
    pub fn check_pre_commit_acks(&self) -> DistributedResult<bool> {
        let acks = self.pre_commit_acks.read()
            .map_err(|e| ModelError::LockError(format!("无法获取确认读锁: {}", e)))?;
        
        let participants = self.participants.read()
            .map_err(|e| ModelError::LockError(format!("无法获取参与者读锁: {}", e)))?;
        
        Ok(acks.len() == participants.len())
    }
    
    /// 阶段3：DoCommit阶段
    pub fn do_commit_phase(&self) -> DistributedResult<()> {
        let mut state = self.transaction_state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态写锁: {}", e)))?;
        
        if self.check_pre_commit_acks()? {
            *state = ThreePhaseState::DoCommit;
            // 向所有参与者发送DoCommit请求
            *state = ThreePhaseState::Committed;
        } else {
            *state = ThreePhaseState::Aborted;
            // 向所有参与者发送Abort请求
        }
        
        Ok(())
    }
    
    /// 参与者：处理CanCommit请求
    pub fn handle_can_commit(&self) -> DistributedResult<bool> {
        // 参与者检查是否可以提交
        // 简化处理，实际需要检查资源可用性
        Ok(true)
    }
    
    /// 参与者：处理PreCommit请求
    pub fn handle_pre_commit(&self) -> DistributedResult<()> {
        let mut state = self.transaction_state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态写锁: {}", e)))?;
        
        *state = ThreePhaseState::PreCommit;
        // 准备提交（但还没有真正提交）
        Ok(())
    }
    
    /// 参与者：处理DoCommit请求
    pub fn handle_do_commit(&self) -> DistributedResult<()> {
        let mut state = self.transaction_state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态写锁: {}", e)))?;
        
        *state = ThreePhaseState::Committed;
        // 真正提交事务
        Ok(())
    }
    
    /// 参与者：超时处理
    pub fn handle_timeout(&self) -> DistributedResult<()> {
        let state = self.transaction_state.read()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态读锁: {}", e)))?
            .clone();
        
        match state {
            ThreePhaseState::CanCommit => {
                // CanCommit超时：回滚
                self.abort()?;
            }
            ThreePhaseState::PreCommit => {
                // PreCommit超时：继续提交（3PC的关键改进）
                self.handle_do_commit()?;
            }
            _ => {}
        }
        
        Ok(())
    }
    
    /// 回滚事务
    pub fn abort(&self) -> DistributedResult<()> {
        let mut state = self.transaction_state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态写锁: {}", e)))?;
        
        *state = ThreePhaseState::Aborted;
        Ok(())
    }
    
    /// 获取事务状态
    pub fn get_state(&self) -> DistributedResult<ThreePhaseState> {
        let state = self.transaction_state.read()
            .map_err(|e| ModelError::LockError(format!("无法获取事务状态读锁: {}", e)))?;
        
        Ok(state.clone())
    }
    
    /// 获取超时设置
    pub fn get_timeout(&self) -> Duration {
        self.timeout
    }
    
    /// 获取协调者ID
    pub fn coordinator_id(&self) -> &str {
        &self.coordinator_id
    }
    
    /// 获取事务ID
    pub fn transaction_id(&self) -> &str {
        &self.transaction_id
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{IpAddr, Ipv4Addr};
    
    #[test]
    fn test_vector_clock() {
        let mut clock1 = VectorClock::new("node1".to_string());
        let mut clock2 = VectorClock::new("node2".to_string());
        
        clock1.increment(&"node1".to_string());
        clock2.increment(&"node2".to_string());
        
        assert_eq!(clock1.compare(&clock2), ClockOrdering::Concurrent);
        
        clock1.update(&clock2);
        assert_eq!(clock1.compare(&clock2), ClockOrdering::After);
    }
    
    #[test]
    fn test_distributed_node() {
        let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);
        let mut node = DistributedNode::new("node1".to_string(), addr);
        
        node.write("key1".to_string(), "value1".to_string()).unwrap();
        let result = node.read("key1");
        
        assert!(result.is_some());
        assert_eq!(result.unwrap().value, "value1");
    }
    
    #[test]
    fn test_consensus_algorithm() {
        let consensus = ConsensusAlgorithm::new("node1".to_string());
        
        assert_eq!(consensus.get_state(), ConsensusState::Follower);
        assert_eq!(consensus.get_current_term(), 0);
        
        consensus.start_election().unwrap();
        assert_eq!(consensus.get_current_term(), 1);
    }
    
    #[test]
    fn test_load_balancer() {
        let lb = LoadBalancer::new(LoadBalancingStrategy::RoundRobin);
        
        lb.add_node("node1".to_string());
        lb.add_node("node2".to_string());
        lb.add_node("node3".to_string());
        
        let node1 = lb.select_node().unwrap();
        let node2 = lb.select_node().unwrap();
        let node3 = lb.select_node().unwrap();
        let node4 = lb.select_node().unwrap(); // Should wrap around
        
        assert_eq!(node1, "node1");
        assert_eq!(node2, "node2");
        assert_eq!(node3, "node3");
        assert_eq!(node4, "node1");
    }
    
    #[test]
    fn test_cap_theorem_analyzer() {
        let analysis = CAPTheoremAnalyzer::analyze_tradeoffs(&[
            CAPProperty::Consistency,
            CAPProperty::Availability,
        ]);
        
        assert!(analysis.is_valid);
        assert_eq!(analysis.sacrificed_property, Some(CAPProperty::PartitionTolerance));
        assert!(!analysis.tradeoffs.is_empty());
        assert!(!analysis.recommendations.is_empty());
    }
    
    #[test]
    fn test_distributed_system_manager() {
        let config = DistributedSystemConfig::default();
        let manager = DistributedSystemManager::new(config);
        
        let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);
        let node = DistributedNode::new("node1".to_string(), addr);
        
        manager.add_node(node).unwrap();
        
        let status = manager.get_system_status();
        assert_eq!(status.total_nodes, 1);
        assert_eq!(status.active_nodes, 1);
    }
    
    #[test]
    fn test_multi_thread_task_executor() {
        let mut executor = MultiThreadTaskExecutor::new(2);
        executor.start().unwrap();
        
        let counter = Arc::new(AtomicU64::new(0));
        
        for _ in 0..10 {
            let counter_clone = Arc::clone(&counter);
            executor.submit_task(move || {
                counter_clone.fetch_add(1, Ordering::SeqCst);
            }).unwrap();
        }
        
        // 等待任务完成
        thread::sleep(Duration::from_millis(100));
        
        assert_eq!(counter.load(Ordering::SeqCst), 10);
        
        executor.stop().unwrap();
    }
    
    #[test]
    fn test_failure_detector() {
        let detector = FailureDetector::new(Duration::from_secs(5));
        
        detector.start();
        detector.suspect_node("node1".to_string());
        
        assert!(detector.is_suspected(&"node1".to_string()));
        
        detector.clear_suspicion(&"node1".to_string());
        assert!(!detector.is_suspected(&"node1".to_string()));
        
        detector.stop();
    }
    
    #[test]
    fn test_paxos_protocol() {
        let paxos = PaxosProtocol::new("node1".to_string());
        
        // 测试添加参与者
        paxos.add_participant("node2".to_string()).unwrap();
        paxos.add_participant("node3".to_string()).unwrap();
        
        // 测试提议
        let proposal_num = paxos.propose("value1".to_string()).unwrap();
        assert_eq!(proposal_num, 0);
        
        // 测试Prepare阶段
        let promise = paxos.handle_prepare(1).unwrap();
        match promise {
            PaxosMessage::Promise(num, _) => assert_eq!(num, 1),
            _ => panic!("Expected Promise message"),
        }
        
        // 测试Accept阶段
        let accepted = paxos.handle_accept(1, "value1".to_string()).unwrap();
        match accepted {
            PaxosMessage::Accepted(num, val) => {
                assert_eq!(num, 1);
                assert_eq!(val, "value1");
            }
            _ => panic!("Expected Accepted message"),
        }
        
        // 验证已接受的值
        let value = paxos.get_accepted_value().unwrap();
        assert_eq!(value, Some("value1".to_string()));
    }
    
    #[test]
    fn test_two_phase_commit() {
        let tx_id = "tx_001".to_string();
        let coordinator = TwoPhaseCommit::new_coordinator("coordinator".to_string(), tx_id.clone());
        
        // 添加参与者
        coordinator.add_participant("node1".to_string()).unwrap();
        coordinator.add_participant("node2".to_string()).unwrap();
        
        // 准备阶段
        coordinator.prepare_phase().unwrap();
        
        // 收集投票
        coordinator.collect_vote("node1".to_string(), VoteResult::Yes).unwrap();
        coordinator.collect_vote("node2".to_string(), VoteResult::Yes).unwrap();
        
        // 检查投票
        assert!(coordinator.check_votes().unwrap());
        
        // 提交阶段
        coordinator.commit_phase().unwrap();
        
        // 验证最终状态
        let state = coordinator.get_state().unwrap();
        assert_eq!(state, TransactionState::Committed);
    }
    
    #[test]
    fn test_two_phase_commit_abort() {
        let tx_id = "tx_002".to_string();
        let coordinator = TwoPhaseCommit::new_coordinator("coordinator".to_string(), tx_id);
        
        coordinator.add_participant("node1".to_string()).unwrap();
        coordinator.add_participant("node2".to_string()).unwrap();
        
        coordinator.prepare_phase().unwrap();
        
        // 一个参与者投反对票
        coordinator.collect_vote("node1".to_string(), VoteResult::Yes).unwrap();
        coordinator.collect_vote("node2".to_string(), VoteResult::No).unwrap();
        
        // 检查投票失败
        assert!(!coordinator.check_votes().unwrap());
        
        // 提交阶段会回滚
        coordinator.commit_phase().unwrap();
        
        let state = coordinator.get_state().unwrap();
        assert_eq!(state, TransactionState::Aborted);
    }
    
    #[test]
    fn test_three_phase_commit() {
        let tx_id = "tx_003".to_string();
        let coordinator = ThreePhaseCommit::new_coordinator(
            "coordinator".to_string(),
            tx_id.clone(),
            Duration::from_secs(5),
        );
        
        // 添加参与者
        coordinator.add_participant("node1".to_string()).unwrap();
        coordinator.add_participant("node2".to_string()).unwrap();
        
        // CanCommit阶段
        coordinator.can_commit_phase().unwrap();
        
        // 收集CanCommit投票
        coordinator.collect_can_commit_vote("node1".to_string(), true).unwrap();
        coordinator.collect_can_commit_vote("node2".to_string(), true).unwrap();
        
        assert!(coordinator.check_can_commit_votes().unwrap());
        
        // PreCommit阶段
        coordinator.pre_commit_phase().unwrap();
        
        // 收集PreCommit确认
        coordinator.collect_pre_commit_ack("node1".to_string()).unwrap();
        coordinator.collect_pre_commit_ack("node2".to_string()).unwrap();
        
        assert!(coordinator.check_pre_commit_acks().unwrap());
        
        // DoCommit阶段
        coordinator.do_commit_phase().unwrap();
        
        // 验证最终状态
        let state = coordinator.get_state().unwrap();
        assert_eq!(state, ThreePhaseState::Committed);
    }
    
    #[test]
    fn test_three_phase_commit_timeout() {
        let paxos = ThreePhaseCommit::new_coordinator(
            "coordinator".to_string(),
            "tx_timeout".to_string(),
            Duration::from_millis(100),
        );
        
        // 验证超时设置
        assert_eq!(paxos.get_timeout(), Duration::from_millis(100));
        
        // 测试PreCommit超时处理
        paxos.handle_pre_commit().unwrap();
        paxos.handle_timeout().unwrap();
        
        // PreCommit超时应该继续提交（3PC的关键特性）
        let state = paxos.get_state().unwrap();
        assert_eq!(state, ThreePhaseState::Committed);
    }
}

/// Raft共识算法完整实现
/// 
/// Raft是一种易于理解的分布式共识算法，将共识问题分解为：
/// 1. Leader选举
/// 2. 日志复制
/// 3. 安全性保证
#[derive(Debug)]
pub struct RaftProtocol {
    /// 节点ID
    node_id: NodeId,
    /// 当前任期
    current_term: Arc<AtomicU64>,
    /// 投票给谁
    voted_for: Arc<RwLock<Option<NodeId>>>,
    /// 日志条目
    log: Arc<RwLock<Vec<RaftLogEntry>>>,
    /// 已提交的索引
    commit_index: Arc<AtomicU64>,
    /// 已应用的索引
    #[allow(dead_code)]
    last_applied: Arc<AtomicU64>,
    /// 节点状态
    state: Arc<RwLock<RaftState>>,
    /// 参与者列表
    peers: Arc<RwLock<Vec<NodeId>>>,
    /// Leader专用：下一个要发送给每个节点的日志索引
    next_index: Arc<RwLock<HashMap<NodeId, u64>>>,
    /// Leader专用：已复制到每个节点的最高日志索引
    match_index: Arc<RwLock<HashMap<NodeId, u64>>>,
    /// 选举超时
    election_timeout: Duration,
    /// 心跳间隔
    #[allow(dead_code)]
    heartbeat_interval: Duration,
    /// 最后收到心跳的时间
    last_heartbeat: Arc<RwLock<Instant>>,
}

/// Raft节点状态
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RaftState {
    /// 跟随者
    Follower,
    /// 候选人
    Candidate,
    /// 领导者
    Leader,
}

/// Raft日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RaftLogEntry {
    /// 日志索引
    pub index: u64,
    /// 任期号
    pub term: u64,
    /// 命令
    pub command: String,
    /// 时间戳
    pub timestamp: Timestamp,
}

/// Raft消息类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RaftMessage {
    /// RequestVote RPC - 请求投票
    RequestVote {
        /// 候选人任期
        term: u64,
        /// 候选人ID
        candidate_id: NodeId,
        /// 候选人最后日志索引
        last_log_index: u64,
        /// 候选人最后日志任期
        last_log_term: u64,
    },
    /// RequestVote响应
    RequestVoteResponse {
        /// 当前任期
        term: u64,
        /// 是否投票
        vote_granted: bool,
    },
    /// AppendEntries RPC - 追加日志/心跳
    AppendEntries {
        /// Leader任期
        term: u64,
        /// Leader ID
        leader_id: NodeId,
        /// 前一个日志索引
        prev_log_index: u64,
        /// 前一个日志任期
        prev_log_term: u64,
        /// 日志条目（心跳时为空）
        entries: Vec<RaftLogEntry>,
        /// Leader已提交的索引
        leader_commit: u64,
    },
    /// AppendEntries响应
    AppendEntriesResponse {
        /// 当前任期
        term: u64,
        /// 是否成功
        success: bool,
        /// 匹配的日志索引
        match_index: u64,
    },
}

impl RaftProtocol {
    /// 创建新的Raft协议实例
    pub fn new(
        node_id: NodeId,
        election_timeout: Duration,
        heartbeat_interval: Duration,
    ) -> Self {
        Self {
            node_id,
            current_term: Arc::new(AtomicU64::new(0)),
            voted_for: Arc::new(RwLock::new(None)),
            log: Arc::new(RwLock::new(Vec::new())),
            commit_index: Arc::new(AtomicU64::new(0)),
            last_applied: Arc::new(AtomicU64::new(0)),
            state: Arc::new(RwLock::new(RaftState::Follower)),
            peers: Arc::new(RwLock::new(Vec::new())),
            next_index: Arc::new(RwLock::new(HashMap::new())),
            match_index: Arc::new(RwLock::new(HashMap::new())),
            election_timeout,
            heartbeat_interval,
            last_heartbeat: Arc::new(RwLock::new(Instant::now())),
        }
    }
    
    /// 添加对等节点
    pub fn add_peer(&self, peer_id: NodeId) -> DistributedResult<()> {
        let mut peers = self.peers.write()
            .map_err(|e| ModelError::LockError(format!("无法获取对等节点写锁: {}", e)))?;
        
        if !peers.contains(&peer_id) {
            peers.push(peer_id);
        }
        Ok(())
    }
    
    /// 获取当前状态
    pub fn get_state(&self) -> DistributedResult<RaftState> {
        let state = self.state.read()
            .map_err(|e| ModelError::LockError(format!("无法获取状态读锁: {}", e)))?;
        
        Ok(state.clone())
    }
    
    /// 获取当前任期
    pub fn get_current_term(&self) -> u64 {
        self.current_term.load(Ordering::SeqCst)
    }
    
    /// 开始选举
    pub fn start_election(&self) -> DistributedResult<bool> {
        // 转换为候选人状态
        let mut state = self.state.write()
            .map_err(|e| ModelError::LockError(format!("无法获取状态写锁: {}", e)))?;
        
        *state = RaftState::Candidate;
        drop(state);
        
        // 递增当前任期
        let new_term = self.current_term.fetch_add(1, Ordering::SeqCst) + 1;
        
        // 投票给自己
        let mut voted_for = self.voted_for.write()
            .map_err(|e| ModelError::LockError(format!("无法获取投票写锁: {}", e)))?;
        
        *voted_for = Some(self.node_id.clone());
        drop(voted_for);
        
        println!("Node {} starting election for term {}", self.node_id, new_term);
        
        // 获取最后日志信息
        let (_last_log_index, _last_log_term) = self.get_last_log_info()?;
        
        // 发送RequestVote RPC给所有对等节点
        let peers = self.peers.read()
            .map_err(|e| ModelError::LockError(format!("无法获取对等节点读锁: {}", e)))?;
        
        let mut votes = 1; // 自己的票
        let total_nodes = peers.len() + 1;
        let majority = (total_nodes / 2) + 1;
        
        // 在实际实现中，这里需要真正的网络通信
        // 简化处理：假设所有节点都会投票
        for _peer in peers.iter() {
            // 模拟投票请求
            votes += 1;
        }
        
        // 检查是否获得多数票
        if votes >= majority {
            let mut state = self.state.write()
                .map_err(|e| ModelError::LockError(format!("无法获取状态写锁: {}", e)))?;
            
            *state = RaftState::Leader;
            println!("Node {} became leader for term {}", self.node_id, new_term);
            
            // 初始化Leader状态
            self.initialize_leader_state()?;
            
            Ok(true)
        } else {
            let mut state = self.state.write()
                .map_err(|e| ModelError::LockError(format!("无法获取状态写锁: {}", e)))?;
            
            *state = RaftState::Follower;
            Ok(false)
        }
    }
    
    /// 初始化Leader状态
    fn initialize_leader_state(&self) -> DistributedResult<()> {
        let log = self.log.read()
            .map_err(|e| ModelError::LockError(format!("无法获取日志读锁: {}", e)))?;
        
        let last_log_index = log.len() as u64;
        drop(log);
        
        let peers = self.peers.read()
            .map_err(|e| ModelError::LockError(format!("无法获取对等节点读锁: {}", e)))?;
        
        let mut next_index = self.next_index.write()
            .map_err(|e| ModelError::LockError(format!("无法获取next_index写锁: {}", e)))?;
        
        let mut match_index = self.match_index.write()
            .map_err(|e| ModelError::LockError(format!("无法获取match_index写锁: {}", e)))?;
        
        for peer in peers.iter() {
            next_index.insert(peer.clone(), last_log_index + 1);
            match_index.insert(peer.clone(), 0);
        }
        
        Ok(())
    }
    
    /// 获取最后日志信息
    fn get_last_log_info(&self) -> DistributedResult<(u64, u64)> {
        let log = self.log.read()
            .map_err(|e| ModelError::LockError(format!("无法获取日志读锁: {}", e)))?;
        
        if let Some(last_entry) = log.last() {
            Ok((last_entry.index, last_entry.term))
        } else {
            Ok((0, 0))
        }
    }
    
    /// 追加日志条目（Leader调用）
    pub fn append_entry(&self, command: String) -> DistributedResult<u64> {
        let state = self.state.read()
            .map_err(|e| ModelError::LockError(format!("无法获取状态读锁: {}", e)))?;
        
        if *state != RaftState::Leader {
            return Err(ModelError::ValidationError("Only leader can append entries".to_string()));
        }
        drop(state);
        
        let current_term = self.current_term.load(Ordering::SeqCst);
        
        let mut log = self.log.write()
            .map_err(|e| ModelError::LockError(format!("无法获取日志写锁: {}", e)))?;
        
        let index = log.len() as u64 + 1;
        let entry = RaftLogEntry {
            index,
            term: current_term,
            command,
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis() as u64,
        };
        
        log.push(entry);
        
        println!("Leader {} appended entry at index {}", self.node_id, index);
        
        // 复制到跟随者（实际需要网络通信）
        self.replicate_to_followers()?;
        
        Ok(index)
    }
    
    /// 复制日志到跟随者
    fn replicate_to_followers(&self) -> DistributedResult<()> {
        let peers = self.peers.read()
            .map_err(|e| ModelError::LockError(format!("无法获取对等节点读锁: {}", e)))?;
        
        for peer in peers.iter() {
            println!("Replicating log to {}", peer);
            // 实际实现需要发送AppendEntries RPC
        }
        
        Ok(())
    }
    
    /// 处理RequestVote RPC
    pub fn handle_request_vote(
        &self,
        term: u64,
        candidate_id: NodeId,
        last_log_index: u64,
        last_log_term: u64,
    ) -> DistributedResult<RaftMessage> {
        let current_term = self.current_term.load(Ordering::SeqCst);
        
        // 如果请求的任期小于当前任期，拒绝投票
        if term < current_term {
            return Ok(RaftMessage::RequestVoteResponse {
                term: current_term,
                vote_granted: false,
            });
        }
        
        // 如果请求的任期大于当前任期，更新任期并转为跟随者
        if term > current_term {
            self.current_term.store(term, Ordering::SeqCst);
            
            let mut state = self.state.write()
                .map_err(|e| ModelError::LockError(format!("无法获取状态写锁: {}", e)))?;
            
            *state = RaftState::Follower;
            drop(state);
            
            let mut voted_for = self.voted_for.write()
                .map_err(|e| ModelError::LockError(format!("无法获取投票写锁: {}", e)))?;
            
            *voted_for = None;
        }
        
        // 检查是否已经投票
        let mut voted_for = self.voted_for.write()
            .map_err(|e| ModelError::LockError(format!("无法获取投票写锁: {}", e)))?;
        
        let can_vote = voted_for.is_none() || voted_for.as_ref() == Some(&candidate_id);
        
        if !can_vote {
            return Ok(RaftMessage::RequestVoteResponse {
                term: self.current_term.load(Ordering::SeqCst),
                vote_granted: false,
            });
        }
        
        // 检查候选人日志是否至少和自己一样新
        let (my_last_log_index, my_last_log_term) = self.get_last_log_info()?;
        
        let log_is_ok = last_log_term > my_last_log_term || 
                       (last_log_term == my_last_log_term && last_log_index >= my_last_log_index);
        
        if log_is_ok {
            *voted_for = Some(candidate_id.clone());
            
            Ok(RaftMessage::RequestVoteResponse {
                term: self.current_term.load(Ordering::SeqCst),
                vote_granted: true,
            })
        } else {
            Ok(RaftMessage::RequestVoteResponse {
                term: self.current_term.load(Ordering::SeqCst),
                vote_granted: false,
            })
        }
    }
    
    /// 处理AppendEntries RPC
    pub fn handle_append_entries(
        &self,
        term: u64,
        _leader_id: NodeId,
        prev_log_index: u64,
        prev_log_term: u64,
        entries: Vec<RaftLogEntry>,
        leader_commit: u64,
    ) -> DistributedResult<RaftMessage> {
        let current_term = self.current_term.load(Ordering::SeqCst);
        
        // 如果Leader任期小于当前任期，拒绝
        if term < current_term {
            return Ok(RaftMessage::AppendEntriesResponse {
                term: current_term,
                success: false,
                match_index: 0,
            });
        }
        
        // 更新心跳时间
        let mut last_heartbeat = self.last_heartbeat.write()
            .map_err(|e| ModelError::LockError(format!("无法获取心跳写锁: {}", e)))?;
        
        *last_heartbeat = Instant::now();
        drop(last_heartbeat);
        
        // 如果是新的Leader或更高任期，转为跟随者
        if term > current_term {
            self.current_term.store(term, Ordering::SeqCst);
            
            let mut state = self.state.write()
                .map_err(|e| ModelError::LockError(format!("无法获取状态写锁: {}", e)))?;
            
            *state = RaftState::Follower;
        }
        
        // 检查日志一致性
        let mut log = self.log.write()
            .map_err(|e| ModelError::LockError(format!("无法获取日志写锁: {}", e)))?;
        
        // 如果prev_log_index位置的日志不匹配，拒绝
        if prev_log_index > 0 {
            if let Some(entry) = log.get((prev_log_index - 1) as usize) {
                if entry.term != prev_log_term {
                    return Ok(RaftMessage::AppendEntriesResponse {
                        term: self.current_term.load(Ordering::SeqCst),
                        success: false,
                        match_index: 0,
                    });
                }
            } else {
                return Ok(RaftMessage::AppendEntriesResponse {
                    term: self.current_term.load(Ordering::SeqCst),
                    success: false,
                    match_index: 0,
                });
            }
        }
        
        // 追加新日志条目
        if !entries.is_empty() {
            // 删除冲突的日志
            log.truncate(prev_log_index as usize);
            
            // 追加新条目
            for entry in entries {
                log.push(entry);
            }
        }
        
        let match_index = log.len() as u64;
        drop(log);
        
        // 更新commit_index
        if leader_commit > self.commit_index.load(Ordering::SeqCst) {
            let new_commit_index = leader_commit.min(match_index);
            self.commit_index.store(new_commit_index, Ordering::SeqCst);
        }
        
        Ok(RaftMessage::AppendEntriesResponse {
            term: self.current_term.load(Ordering::SeqCst),
            success: true,
            match_index,
        })
    }
    
    /// 检查选举超时
    pub fn check_election_timeout(&self) -> DistributedResult<bool> {
        let last_heartbeat = self.last_heartbeat.read()
            .map_err(|e| ModelError::LockError(format!("无法获取心跳读锁: {}", e)))?;
        
        Ok(last_heartbeat.elapsed() > self.election_timeout)
    }
    
    /// 发送心跳（Leader调用）
    pub fn send_heartbeat(&self) -> DistributedResult<()> {
        let state = self.state.read()
            .map_err(|e| ModelError::LockError(format!("无法获取状态读锁: {}", e)))?;
        
        if *state != RaftState::Leader {
            return Ok(());
        }
        drop(state);
        
        println!("Leader {} sending heartbeat", self.node_id);
        
        // 向所有跟随者发送空的AppendEntries（心跳）
        self.replicate_to_followers()?;
        
        Ok(())
    }
    
    /// 获取节点ID
    pub fn node_id(&self) -> &str {
        &self.node_id
    }
    
    /// 获取日志长度
    pub fn log_len(&self) -> DistributedResult<usize> {
        let log = self.log.read()
            .map_err(|e| ModelError::LockError(format!("无法获取日志读锁: {}", e)))?;
        
        Ok(log.len())
    }
}

/// 分布式快照（Chandy-Lamport算法）
/// 
/// 用于在分布式系统中捕获全局一致的快照
#[derive(Debug, Clone)]
pub struct DistributedSnapshot {
    /// 快照ID
    snapshot_id: String,
    /// 发起快照的节点
    initiator: NodeId,
    /// 节点状态快照
    node_states: Arc<RwLock<HashMap<NodeId, NodeSnapshot>>>,
    /// 通道状态快照（记录快照期间传输的消息）
    channel_states: Arc<RwLock<HashMap<(NodeId, NodeId), Vec<SnapshotMessage>>>>,
    /// 是否完成
    completed: Arc<AtomicBool>,
    /// 参与节点
    participants: Arc<RwLock<HashSet<NodeId>>>,
}

/// 节点快照
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeSnapshot {
    /// 节点ID
    pub node_id: NodeId,
    /// 快照时的数据
    pub data: HashMap<String, VersionedValue>,
    /// 快照时的向量时钟
    pub vector_clock: VectorClock,
    /// 快照时间戳
    pub timestamp: Timestamp,
}

/// 快照消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SnapshotMessage {
    /// 消息ID
    pub message_id: MessageId,
    /// 发送者
    pub sender: NodeId,
    /// 接收者
    pub receiver: NodeId,
    /// 消息内容
    pub content: String,
    /// 时间戳
    pub timestamp: Timestamp,
}

/// 快照标记消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SnapshotMarker {
    /// 开始快照
    Start {
        snapshot_id: String,
        initiator: NodeId,
    },
    /// 完成快照
    Complete {
        snapshot_id: String,
    },
}

impl DistributedSnapshot {
    /// 创建新的分布式快照
    pub fn new(snapshot_id: String, initiator: NodeId) -> Self {
        Self {
            snapshot_id,
            initiator,
            node_states: Arc::new(RwLock::new(HashMap::new())),
            channel_states: Arc::new(RwLock::new(HashMap::new())),
            completed: Arc::new(AtomicBool::new(false)),
            participants: Arc::new(RwLock::new(HashSet::new())),
        }
    }
    
    /// 发起快照
    pub fn initiate(&self, node_id: NodeId, node_data: HashMap<String, VersionedValue>) -> DistributedResult<()> {
        println!("Node {} initiating snapshot {}", node_id, self.snapshot_id);
        
        // 记录本节点状态
        let vector_clock = VectorClock::new(node_id.clone());
        let snapshot = NodeSnapshot {
            node_id: node_id.clone(),
            data: node_data,
            vector_clock,
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis() as u64,
        };
        
        let mut node_states = self.node_states.write()
            .map_err(|e| ModelError::LockError(format!("无法获取节点状态写锁: {}", e)))?;
        
        node_states.insert(node_id.clone(), snapshot);
        
        // 添加到参与者列表
        let mut participants = self.participants.write()
            .map_err(|e| ModelError::LockError(format!("无法获取参与者写锁: {}", e)))?;
        
        participants.insert(node_id);
        
        // 向所有其他节点发送快照标记
        // 实际实现需要网络通信
        
        Ok(())
    }
    
    /// 接收快照标记
    pub fn receive_marker(
        &self,
        from_node: NodeId,
        receiving_node: NodeId,
        node_data: HashMap<String, VersionedValue>,
    ) -> DistributedResult<()> {
        let mut participants = self.participants.write()
            .map_err(|e| ModelError::LockError(format!("无法获取参与者写锁: {}", e)))?;
        
        // 如果是第一次收到标记
        if !participants.contains(&receiving_node) {
            println!("Node {} received snapshot marker from {}", receiving_node, from_node);
            
            // 记录本节点状态
            let vector_clock = VectorClock::new(receiving_node.clone());
            let snapshot = NodeSnapshot {
                node_id: receiving_node.clone(),
                data: node_data,
                vector_clock,
                timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis() as u64,
            };
            
            let mut node_states = self.node_states.write()
                .map_err(|e| ModelError::LockError(format!("无法获取节点状态写锁: {}", e)))?;
            
            node_states.insert(receiving_node.clone(), snapshot);
            participants.insert(receiving_node.clone());
            
            // 向所有其他节点转发标记
            // 实际实现需要网络通信
        }
        
        // 停止记录从from_node到receiving_node的通道消息
        let channel_key = (from_node, receiving_node);
        let mut channel_states = self.channel_states.write()
            .map_err(|e| ModelError::LockError(format!("无法获取通道状态写锁: {}", e)))?;
        
        channel_states.entry(channel_key).or_insert_with(Vec::new);
        
        Ok(())
    }
    
    /// 记录通道消息（在收到快照标记之前）
    pub fn record_channel_message(
        &self,
        from_node: NodeId,
        to_node: NodeId,
        message: SnapshotMessage,
    ) -> DistributedResult<()> {
        let participants = self.participants.read()
            .map_err(|e| ModelError::LockError(format!("无法获取参与者读锁: {}", e)))?;
        
        // 只记录发送者已经快照但接收者还未快照的消息
        if participants.contains(&from_node) && !participants.contains(&to_node) {
            let channel_key = (from_node, to_node);
            let mut channel_states = self.channel_states.write()
                .map_err(|e| ModelError::LockError(format!("无法获取通道状态写锁: {}", e)))?;
            
            channel_states.entry(channel_key)
                .or_insert_with(Vec::new)
                .push(message);
        }
        
        Ok(())
    }
    
    /// 获取快照结果
    pub fn get_snapshot(&self) -> DistributedResult<GlobalSnapshot> {
        let node_states = self.node_states.read()
            .map_err(|e| ModelError::LockError(format!("无法获取节点状态读锁: {}", e)))?;
        
        let channel_states = self.channel_states.read()
            .map_err(|e| ModelError::LockError(format!("无法获取通道状态读锁: {}", e)))?;
        
        Ok(GlobalSnapshot {
            snapshot_id: self.snapshot_id.clone(),
            initiator: self.initiator.clone(),
            node_states: node_states.clone(),
            channel_states: channel_states.clone(),
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis() as u64,
        })
    }
    
    /// 标记快照完成
    pub fn mark_completed(&self) {
        self.completed.store(true, Ordering::SeqCst);
        println!("Snapshot {} completed", self.snapshot_id);
    }
    
    /// 检查是否完成
    pub fn is_completed(&self) -> bool {
        self.completed.load(Ordering::SeqCst)
    }
    
    /// 获取快照ID
    pub fn snapshot_id(&self) -> &str {
        &self.snapshot_id
    }
}

/// 全局快照结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobalSnapshot {
    /// 快照ID
    pub snapshot_id: String,
    /// 发起者
    pub initiator: NodeId,
    /// 所有节点状态
    pub node_states: HashMap<NodeId, NodeSnapshot>,
    /// 所有通道状态
    pub channel_states: HashMap<(NodeId, NodeId), Vec<SnapshotMessage>>,
    /// 快照时间戳
    pub timestamp: Timestamp,
}