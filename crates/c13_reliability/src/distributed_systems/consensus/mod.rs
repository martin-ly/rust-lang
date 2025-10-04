//! # 分布式共识算法模块
//!
//! 提供多种分布式共识算法实现。

pub mod raft;
pub mod types;

pub use raft::*;
pub use types::*;

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use crate::error_handling::UnifiedError;

/// 共识算法接口
#[async_trait]
pub trait ConsensusAlgorithm: Send + Sync {
    /// 提交提案
    async fn propose(&mut self, value: Vec<u8>) -> Result<ProposalId, UnifiedError>;
    
    /// 等待提案被提交
    async fn wait_committed(&self, proposal_id: ProposalId) -> Result<Vec<u8>, UnifiedError>;
    
    /// 获取当前状态
    fn get_state(&self) -> ConsensusState;
    
    /// 是否为 Leader
    fn is_leader(&self) -> bool;
    
    /// 获取当前任期
    fn current_term(&self) -> u64;
}

/// 提案 ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ProposalId(pub u64);

/// 共识状态
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConsensusState {
    /// Follower 状态
    Follower,
    /// Candidate 状态 (正在选举)
    Candidate,
    /// Leader 状态
    Leader,
}

/// 节点 ID
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NodeId(pub String);

impl NodeId {
    pub fn new(id: impl Into<String>) -> Self {
        Self(id.into())
    }
}

/// 日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    /// 任期号
    pub term: u64,
    /// 日志索引
    pub index: u64,
    /// 日志数据
    pub data: Vec<u8>,
}

/// 集群配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClusterConfig {
    /// 节点列表
    pub nodes: Vec<NodeId>,
    /// 当前节点 ID
    pub self_id: NodeId,
    /// 心跳间隔 (毫秒)
    pub heartbeat_interval_ms: u64,
    /// 选举超时范围 (毫秒)
    pub election_timeout_range_ms: (u64, u64),
}

/// 共识指标
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ConsensusMetrics {
    /// Leader 变更次数
    pub leader_changes: u64,
    /// 提交的日志数量
    pub committed_logs: u64,
    /// 当前日志长度
    pub log_length: u64,
    /// 当前任期
    pub current_term: u64,
    /// 最后心跳时间戳
    pub last_heartbeat_ms: u64,
    /// 自定义指标
    pub custom_metrics: HashMap<String, f64>,
}

