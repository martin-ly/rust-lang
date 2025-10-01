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
}
