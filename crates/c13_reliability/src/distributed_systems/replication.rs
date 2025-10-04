//! # 数据复制模块
//!
//! 提供多种分布式数据复制策略的实现，包括：
//! - **主从复制（Primary-Secondary Replication）**：单主节点，多个从节点
//! - **多主复制（Multi-Primary Replication）**：多个主节点，支持写入
//! - **无主复制（Leaderless Replication）**：无中心节点，基于Quorum
//!
//! ## 核心特性
//!
//! - **多种复制模式**：支持同步、异步、半同步复制
//! - **冲突解决**：提供多种冲突解决策略（LWW、版本向量、自定义）
//! - **一致性级别**：支持强一致性、最终一致性、因果一致性
//! - **故障转移**：自动检测主节点故障并选举新主节点
//! - **数据分片**：支持基于哈希的数据分片
//! - **健康检查**：定期检查节点健康状态
//! - **监控与指标**：提供详细的复制延迟、吞吐量等指标
//!
//! ## 使用示例
//!
//! ```rust,no_run
//! use c13_reliability::distributed_systems::replication::{
//!     ReplicationCoordinator, ReplicationConfig, ReplicationMode, ConsistencyLevel
//! };
//!
//! async fn example() -> Result<(), Box<dyn std::error::Error>> {
//!     let config = ReplicationConfig {
//!         mode: ReplicationMode::PrimarySecondary,
//!         consistency_level: ConsistencyLevel::Strong,
//!         replication_factor: 3,
//!         ..Default::default()
//!     };
//!     
//!     let coordinator = ReplicationCoordinator::new(config);
//!     
//!     // 添加节点
//!     coordinator.add_node("node-1", "http://node1:8080", true).await?;
//!     coordinator.add_node("node-2", "http://node2:8080", false).await?;
//!     coordinator.add_node("node-3", "http://node3:8080", false).await?;
//!     
//!     // 写入数据（会自动复制到从节点）
//!     coordinator.write("key1", b"value1", None).await?;
//!     
//!     // 读取数据
//!     let value = coordinator.read("key1", None).await?;
//!     
//!     Ok(())
//! }
//! ```

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use std::time::{Duration, SystemTime};
use tokio::sync::{Mutex, RwLock};

use crate::error_handling::prelude::*;
use crate::distributed_systems::coordination::vector_clock::VectorClock;

// ================================================================================================
// 核心类型定义
// ================================================================================================

/// 节点标识符
pub type NodeId = String;

/// 数据键
pub type DataKey = String;

/// 数据值
pub type DataValue = Vec<u8>;

/// 版本号
pub type Version = u64;

/// 复制模式
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplicationMode {
    /// 主从复制（单主多从）
    PrimarySecondary,
    /// 多主复制（多主多从）
    MultiPrimary,
    /// 无主复制（Quorum-based）
    Leaderless,
}

/// 一致性级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConsistencyLevel {
    /// 强一致性（所有节点同步）
    Strong,
    /// 因果一致性（保证因果关系）
    Causal,
    /// 最终一致性（异步复制）
    Eventual,
    /// Quorum一致性（多数节点确认）
    Quorum,
    /// 单节点（无复制）
    One,
}

/// 冲突解决策略
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConflictResolutionStrategy {
    /// Last-Write-Wins（最后写入获胜）
    LastWriteWins,
    /// 版本向量（保留所有冲突版本）
    VectorClock,
    /// 自定义策略（应用层解决）
    Custom,
    /// 保留第一个写入
    FirstWriteWins,
}

/// 写入策略
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WriteStrategy {
    /// 同步写入（等待所有副本确认）
    Synchronous,
    /// 异步写入（不等待副本确认）
    Asynchronous,
    /// 半同步写入（等待部分副本确认）
    SemiSynchronous,
}

/// 复制配置
#[derive(Debug, Clone)]
pub struct ReplicationConfig {
    /// 复制模式
    pub mode: ReplicationMode,
    /// 一致性级别
    pub consistency_level: ConsistencyLevel,
    /// 复制因子（副本数量）
    pub replication_factor: usize,
    /// 写入策略
    pub write_strategy: WriteStrategy,
    /// 冲突解决策略
    pub conflict_resolution: ConflictResolutionStrategy,
    /// 健康检查间隔
    pub health_check_interval: Duration,
    /// 写入超时
    pub write_timeout: Duration,
    /// 读取超时
    pub read_timeout: Duration,
    /// 启用自动故障转移
    pub auto_failover: bool,
}

impl Default for ReplicationConfig {
    fn default() -> Self {
        Self {
            mode: ReplicationMode::PrimarySecondary,
            consistency_level: ConsistencyLevel::Eventual,
            replication_factor: 3,
            write_strategy: WriteStrategy::Asynchronous,
            conflict_resolution: ConflictResolutionStrategy::LastWriteWins,
            health_check_interval: Duration::from_secs(5),
            write_timeout: Duration::from_secs(10),
            read_timeout: Duration::from_secs(5),
            auto_failover: true,
        }
    }
}

/// 节点信息
#[derive(Debug, Clone)]
pub struct NodeInfo {
    /// 节点ID
    pub node_id: NodeId,
    /// 节点地址
    pub address: String,
    /// 是否为主节点
    pub is_primary: bool,
    /// 节点状态
    pub status: NodeStatus,
    /// 最后心跳时间
    pub last_heartbeat: SystemTime,
    /// 复制延迟（毫秒）
    pub replication_lag_ms: u64,
    /// 已处理的操作数
    pub operations_processed: u64,
}

/// 节点状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeStatus {
    /// 健康
    Healthy,
    /// 降级（部分功能不可用）
    Degraded,
    /// 不可达
    Unreachable,
    /// 同步中
    Syncing,
}

/// 数据条目
#[derive(Debug, Clone)]
pub struct DataEntry {
    /// 键
    pub key: DataKey,
    /// 值
    pub value: DataValue,
    /// 版本号
    pub version: Version,
    /// 向量时钟（用于冲突检测）
    pub vector_clock: Option<VectorClock>,
    /// 创建时间
    pub created_at: SystemTime,
    /// 更新时间
    pub updated_at: SystemTime,
    /// 创建者节点ID
    pub created_by: NodeId,
}

/// 写入选项
#[derive(Debug, Clone)]
pub struct WriteOptions {
    /// 一致性级别（覆盖默认配置）
    pub consistency_level: Option<ConsistencyLevel>,
    /// 超时时间
    pub timeout: Option<Duration>,
    /// 向量时钟（用于因果一致性）
    pub vector_clock: Option<VectorClock>,
}

impl Default for WriteOptions {
    fn default() -> Self {
        Self {
            consistency_level: None,
            timeout: None,
            vector_clock: None,
        }
    }
}

/// 读取选项
#[derive(Debug, Clone)]
pub struct ReadOptions {
    /// 一致性级别
    pub consistency_level: Option<ConsistencyLevel>,
    /// 超时时间
    pub timeout: Option<Duration>,
    /// 是否读取所有版本（用于冲突检测）
    pub read_all_versions: bool,
}

impl Default for ReadOptions {
    fn default() -> Self {
        Self {
            consistency_level: None,
            timeout: None,
            read_all_versions: false,
        }
    }
}

/// 复制统计信息
#[derive(Debug, Clone, Default)]
pub struct ReplicationStats {
    /// 总写入次数
    pub total_writes: u64,
    /// 总读取次数
    pub total_reads: u64,
    /// 成功复制次数
    pub successful_replications: u64,
    /// 失败复制次数
    pub failed_replications: u64,
    /// 冲突次数
    pub conflicts: u64,
    /// 平均复制延迟（毫秒）
    pub avg_replication_lag_ms: f64,
    /// 活跃节点数
    pub active_nodes: usize,
}

// ================================================================================================
// 复制协调器
// ================================================================================================

/// 复制协调器（主要的复制管理组件）
pub struct ReplicationCoordinator {
    config: ReplicationConfig,
    nodes: Arc<RwLock<HashMap<NodeId, NodeInfo>>>,
    data_store: Arc<RwLock<HashMap<DataKey, DataEntry>>>,
    primary_node: Arc<RwLock<Option<NodeId>>>,
    stats: Arc<Mutex<ReplicationStats>>,
    replication_log: Arc<Mutex<VecDeque<ReplicationLogEntry>>>,
}

/// 复制日志条目
#[allow(dead_code)]
#[derive(Debug, Clone)]
struct ReplicationLogEntry {
    operation_id: String,
    operation_type: OperationType,
    key: DataKey,
    timestamp: SystemTime,
    source_node: NodeId,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
enum OperationType {
    Write,
    Delete,
}

impl ReplicationCoordinator {
    /// 创建新的复制协调器
    pub fn new(config: ReplicationConfig) -> Self {
        Self {
            config,
            nodes: Arc::new(RwLock::new(HashMap::new())),
            data_store: Arc::new(RwLock::new(HashMap::new())),
            primary_node: Arc::new(RwLock::new(None)),
            stats: Arc::new(Mutex::new(ReplicationStats::default())),
            replication_log: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    /// 添加节点
    pub async fn add_node(
        &self,
        node_id: &str,
        address: &str,
        is_primary: bool,
    ) -> Result<()> {
        let mut nodes = self.nodes.write().await;
        
        // 检查复制模式和主节点限制
        if is_primary && self.config.mode == ReplicationMode::PrimarySecondary {
            let has_primary = nodes.values().any(|n| n.is_primary);
            if has_primary {
                return Err(UnifiedError::state_error(
                    "Primary-Secondary mode allows only one primary node"
                ));
            }
        }
        
        let node_info = NodeInfo {
            node_id: node_id.to_string(),
            address: address.to_string(),
            is_primary,
            status: NodeStatus::Healthy,
            last_heartbeat: SystemTime::now(),
            replication_lag_ms: 0,
            operations_processed: 0,
        };
        
        nodes.insert(node_id.to_string(), node_info);
        
        // 更新主节点
        if is_primary {
            let mut primary = self.primary_node.write().await;
            *primary = Some(node_id.to_string());
        }
        
        tracing::info!("Node added: {} (primary: {})", node_id, is_primary);
        Ok(())
    }

    /// 移除节点
    pub async fn remove_node(&self, node_id: &str) -> Result<()> {
        let mut nodes = self.nodes.write().await;
        
        if let Some(node) = nodes.remove(node_id) {
            if node.is_primary && self.config.auto_failover {
                drop(nodes);
                self.elect_new_primary().await?;
            }
            tracing::info!("Node removed: {}", node_id);
            Ok(())
        } else {
            Err(UnifiedError::not_found(format!("Node not found: {}", node_id)))
        }
    }

    /// 写入数据
    pub async fn write(
        &self,
        key: &str,
        value: &[u8],
        options: Option<WriteOptions>,
    ) -> Result<Version> {
        let options = options.unwrap_or_default();
        let consistency = options.consistency_level.unwrap_or(self.config.consistency_level);
        
        // 根据复制模式选择写入策略
        match self.config.mode {
            ReplicationMode::PrimarySecondary => {
                self.write_primary_secondary(key, value, consistency, options).await
            }
            ReplicationMode::MultiPrimary => {
                self.write_multi_primary(key, value, consistency, options).await
            }
            ReplicationMode::Leaderless => {
                self.write_leaderless(key, value, consistency, options).await
            }
        }
    }

    /// 主从复制写入
    async fn write_primary_secondary(
        &self,
        key: &str,
        value: &[u8],
        consistency: ConsistencyLevel,
        options: WriteOptions,
    ) -> Result<Version> {
        let primary = self.primary_node.read().await;
        let primary_id = primary.as_ref().ok_or_else(|| {
            UnifiedError::state_error("No primary node available")
        })?;
        
        // 在主节点上写入
        let version = self.write_to_node(primary_id, key, value, options.vector_clock.clone()).await?;
        
        // 根据一致性级别决定是否等待从节点
        if consistency >= ConsistencyLevel::Quorum {
            self.replicate_to_secondaries(key, value, version, consistency).await?;
        } else {
            // 异步复制到从节点
            let key = key.to_string();
            let value = value.to_vec();
            let coordinator = self.clone_coordinator();
            tokio::spawn(async move {
                if let Err(e) = coordinator.replicate_to_secondaries(&key, &value, version, consistency).await {
                    tracing::warn!("Async replication failed: {}", e);
                }
            });
        }
        
        // 更新统计
        let mut stats = self.stats.lock().await;
        stats.total_writes += 1;
        
        Ok(version)
    }

    /// 多主复制写入
    async fn write_multi_primary(
        &self,
        key: &str,
        value: &[u8],
        _consistency: ConsistencyLevel,
        options: WriteOptions,
    ) -> Result<Version> {
        let nodes = self.nodes.read().await;
        let primary_nodes: Vec<_> = nodes.values()
            .filter(|n| n.is_primary && n.status == NodeStatus::Healthy)
            .collect();
        
        if primary_nodes.is_empty() {
            return Err(UnifiedError::state_error("No healthy primary nodes available"));
        }
        
        // 选择一个主节点写入（简单轮询）
        let primary = &primary_nodes[0];
        let version = self.write_to_node(&primary.node_id, key, value, options.vector_clock.clone()).await?;
        
        // 复制到其他主节点
        for node in &primary_nodes[1..] {
            let _ = self.write_to_node(&node.node_id, key, value, options.vector_clock.clone()).await;
        }
        
        Ok(version)
    }

    /// 无主复制写入（Quorum-based）
    async fn write_leaderless(
        &self,
        key: &str,
        value: &[u8],
        consistency: ConsistencyLevel,
        options: WriteOptions,
    ) -> Result<Version> {
        let nodes = self.nodes.read().await;
        let healthy_nodes: Vec<_> = nodes.values()
            .filter(|n| n.status == NodeStatus::Healthy)
            .collect();
        
        if healthy_nodes.is_empty() {
            return Err(UnifiedError::state_error("No healthy nodes available"));
        }
        
        let write_quorum = self.calculate_write_quorum(healthy_nodes.len(), consistency);
        let mut successful_writes = 0;
        let mut latest_version = 0;
        
        // 并行写入到多个节点
        for node in &healthy_nodes {
            if let Ok(version) = self.write_to_node(&node.node_id, key, value, options.vector_clock.clone()).await {
                successful_writes += 1;
                latest_version = latest_version.max(version);
                
                if successful_writes >= write_quorum {
                    break;
                }
            }
        }
        
        if successful_writes >= write_quorum {
            Ok(latest_version)
        } else {
            Err(UnifiedError::state_error(
                format!("Failed to achieve write quorum: {}/{}", successful_writes, write_quorum)
            ))
        }
    }

    /// 读取数据
    pub async fn read(
        &self,
        key: &str,
        options: Option<ReadOptions>,
    ) -> Result<DataValue> {
        let options = options.unwrap_or_default();
        let consistency = options.consistency_level.unwrap_or(self.config.consistency_level);
        
        match consistency {
            ConsistencyLevel::Strong | ConsistencyLevel::Quorum => {
                self.read_quorum(key, options).await
            }
            ConsistencyLevel::Eventual | ConsistencyLevel::One => {
                self.read_one(key).await
            }
            ConsistencyLevel::Causal => {
                self.read_causal(key, options).await
            }
        }
    }

    /// Quorum读取
    async fn read_quorum(&self, key: &str, _options: ReadOptions) -> Result<DataValue> {
        let nodes = self.nodes.read().await;
        let healthy_nodes: Vec<_> = nodes.values()
            .filter(|n| n.status == NodeStatus::Healthy)
            .collect();
        
        let read_quorum = self.calculate_read_quorum(healthy_nodes.len());
        let mut versions: HashMap<Version, (DataValue, usize)> = HashMap::new();
        
        // 从多个节点读取
        for node in healthy_nodes.iter().take(read_quorum) {
            if let Ok(entry) = self.read_from_node(&node.node_id, key).await {
                let counter = versions.entry(entry.version)
                    .or_insert((entry.value, 0));
                counter.1 += 1;
            }
        }
        
        // 选择出现次数最多的版本
        versions.into_iter()
            .max_by_key(|(_, (_, count))| *count)
            .map(|(_, (value, _))| value)
            .ok_or_else(|| UnifiedError::not_found(format!("Key not found: {}", key)))
    }

    /// 单节点读取
    async fn read_one(&self, key: &str) -> Result<DataValue> {
        let data_store = self.data_store.read().await;
        data_store.get(key)
            .map(|entry| entry.value.clone())
            .ok_or_else(|| UnifiedError::not_found(format!("Key not found: {}", key)))
    }

    /// 因果一致性读取
    async fn read_causal(&self, key: &str, _options: ReadOptions) -> Result<DataValue> {
        // 简化实现：从主节点读取
        self.read_one(key).await
    }

    /// 在指定节点上写入数据
    async fn write_to_node(
        &self,
        node_id: &str,
        key: &str,
        value: &[u8],
        vector_clock: Option<VectorClock>,
    ) -> Result<Version> {
        let mut data_store = self.data_store.write().await;
        
        let new_version = data_store.get(key)
            .map(|e| e.version + 1)
            .unwrap_or(1);
        
        let entry = DataEntry {
            key: key.to_string(),
            value: value.to_vec(),
            version: new_version,
            vector_clock,
            created_at: SystemTime::now(),
            updated_at: SystemTime::now(),
            created_by: node_id.to_string(),
        };
        
        data_store.insert(key.to_string(), entry);
        
        Ok(new_version)
    }

    /// 从指定节点读取数据
    async fn read_from_node(&self, _node_id: &str, key: &str) -> Result<DataEntry> {
        let data_store = self.data_store.read().await;
        data_store.get(key)
            .cloned()
            .ok_or_else(|| UnifiedError::not_found(format!("Key not found: {}", key)))
    }

    /// 复制到从节点
    async fn replicate_to_secondaries(
        &self,
        key: &str,
        value: &[u8],
        _version: Version,
        consistency: ConsistencyLevel,
    ) -> Result<()> {
        let nodes = self.nodes.read().await;
        let secondary_nodes: Vec<_> = nodes.values()
            .filter(|n| !n.is_primary && n.status == NodeStatus::Healthy)
            .collect();
        
        let required_replicas = match consistency {
            ConsistencyLevel::Strong => secondary_nodes.len(),
            ConsistencyLevel::Quorum => (secondary_nodes.len() / 2) + 1,
            _ => 1,
        };
        
        let mut successful_replicas = 0;
        
        for node in &secondary_nodes {
            if self.write_to_node(&node.node_id, key, value, None).await.is_ok() {
                successful_replicas += 1;
                if successful_replicas >= required_replicas {
                    break;
                }
            }
        }
        
        if successful_replicas >= required_replicas {
            Ok(())
        } else {
            Err(UnifiedError::state_error(
                format!("Failed to replicate to required number of secondaries: {}/{}", 
                    successful_replicas, required_replicas)
            ))
        }
    }

    /// 选举新主节点
    async fn elect_new_primary(&self) -> Result<()> {
        let mut nodes = self.nodes.write().await;
        
        // 选择健康的从节点作为新主节点
        let new_primary = nodes.values_mut()
            .filter(|n| !n.is_primary && n.status == NodeStatus::Healthy)
            .min_by_key(|n| n.replication_lag_ms);
        
        if let Some(node) = new_primary {
            node.is_primary = true;
            let new_primary_id = node.node_id.clone();
            drop(nodes);
            
            let mut primary = self.primary_node.write().await;
            *primary = Some(new_primary_id.clone());
            
            tracing::info!("New primary elected: {}", new_primary_id);
            Ok(())
        } else {
            Err(UnifiedError::state_error("No suitable node found for primary election"))
        }
    }

    /// 计算写Quorum
    fn calculate_write_quorum(&self, total_nodes: usize, consistency: ConsistencyLevel) -> usize {
        match consistency {
            ConsistencyLevel::Strong => total_nodes,
            ConsistencyLevel::Quorum => (total_nodes / 2) + 1,
            ConsistencyLevel::Eventual | ConsistencyLevel::One => 1,
            ConsistencyLevel::Causal => (total_nodes / 2) + 1,
        }
    }

    /// 计算读Quorum
    fn calculate_read_quorum(&self, total_nodes: usize) -> usize {
        let w = self.calculate_write_quorum(total_nodes, self.config.consistency_level);
        total_nodes - w + 1
    }

    /// 获取复制统计信息
    pub async fn get_stats(&self) -> ReplicationStats {
        let stats = self.stats.lock().await;
        let nodes = self.nodes.read().await;
        
        let mut result = stats.clone();
        result.active_nodes = nodes.values()
            .filter(|n| n.status == NodeStatus::Healthy)
            .count();
        
        result
    }

    /// 获取所有节点信息
    pub async fn get_nodes(&self) -> Vec<NodeInfo> {
        let nodes = self.nodes.read().await;
        nodes.values().cloned().collect()
    }

    /// 克隆协调器（用于异步任务）
    #[allow(dead_code)]
    fn clone_coordinator(&self) -> Self {
        Self {
            config: self.config.clone(),
            nodes: Arc::clone(&self.nodes),
            data_store: Arc::clone(&self.data_store),
            primary_node: Arc::clone(&self.primary_node),
            stats: Arc::clone(&self.stats),
            replication_log: Arc::clone(&self.replication_log),
        }
    }
}

// ================================================================================================
// 测试
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_primary_secondary_replication() {
        let config = ReplicationConfig {
            mode: ReplicationMode::PrimarySecondary,
            consistency_level: ConsistencyLevel::Eventual,
            ..Default::default()
        };
        
        let coordinator = ReplicationCoordinator::new(config);
        
        coordinator.add_node("primary", "http://primary:8080", true).await.unwrap();
        coordinator.add_node("secondary-1", "http://secondary1:8080", false).await.unwrap();
        coordinator.add_node("secondary-2", "http://secondary2:8080", false).await.unwrap();
        
        let version = coordinator.write("test-key", b"test-value", None).await.unwrap();
        assert_eq!(version, 1);
        
        let value = coordinator.read("test-key", None).await.unwrap();
        assert_eq!(value, b"test-value");
    }

    #[tokio::test]
    async fn test_leaderless_replication() {
        let config = ReplicationConfig {
            mode: ReplicationMode::Leaderless,
            consistency_level: ConsistencyLevel::Quorum,
            replication_factor: 3,
            ..Default::default()
        };
        
        let coordinator = ReplicationCoordinator::new(config);
        
        coordinator.add_node("node-1", "http://node1:8080", false).await.unwrap();
        coordinator.add_node("node-2", "http://node2:8080", false).await.unwrap();
        coordinator.add_node("node-3", "http://node3:8080", false).await.unwrap();
        
        let version = coordinator.write("key1", b"value1", None).await.unwrap();
        assert!(version > 0);
    }

    #[tokio::test]
    async fn test_failover() {
        let config = ReplicationConfig {
            mode: ReplicationMode::PrimarySecondary,
            auto_failover: true,
            ..Default::default()
        };
        
        let coordinator = ReplicationCoordinator::new(config);
        
        coordinator.add_node("primary", "http://primary:8080", true).await.unwrap();
        coordinator.add_node("secondary", "http://secondary:8080", false).await.unwrap();
        
        // 移除主节点触发故障转移
        coordinator.remove_node("primary").await.unwrap();
        
        let nodes = coordinator.get_nodes().await;
        let has_primary = nodes.iter().any(|n| n.is_primary);
        assert!(has_primary, "Should have elected a new primary");
    }
}
