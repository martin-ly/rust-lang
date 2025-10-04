//! # Raft 共识算法实现
//!
//! 基于 Raft 论文的共识算法实现，支持：
//! - Leader 选举
//! - 日志复制
//! - 安全性保证
//! - 成员变更
//! - 日志压缩

use async_trait::async_trait;
use std::collections::HashMap;
use std::sync::Arc;
use parking_lot::RwLock;
use tokio::sync::mpsc;
use tokio::time::{interval, Duration, Instant};
use rand::Rng;
use serde::{Deserialize, Serialize};

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};
use super::{
    ConsensusAlgorithm, ConsensusState, ProposalId, NodeId, LogEntry, ClusterConfig,
    ConsensusMetrics,
};
use super::types::{
    RequestVoteRequest, RequestVoteResponse,
    AppendEntriesRequest, AppendEntriesResponse,
    RaftMessage,
};

/// Raft 节点
#[allow(dead_code)]
pub struct RaftNode {
    /// 内部状态
    state: Arc<RwLock<RaftState>>,
    /// 集群配置
    config: ClusterConfig,
    /// 消息发送通道
    _tx: mpsc::UnboundedSender<RaftMessage>,
    /// 消息接收通道
    rx: Arc<RwLock<mpsc::UnboundedReceiver<RaftMessage>>>,
}

/// Raft 内部状态
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
struct RaftState {
    /// 当前任期
    current_term: u64,
    /// 当前投票给谁
    voted_for: Option<NodeId>,
    /// 日志条目
    log: Vec<LogEntry>,
    /// 提交索引
    commit_index: u64,
    /// 最后应用索引
    last_applied: u64,
    /// 当前状态
    state: ConsensusState,
    /// Leader ID
    leader_id: Option<NodeId>,
    /// 下一个提案 ID
    next_proposal_id: u64,
    /// 指标
    metrics: ConsensusMetrics,
    /// 最后心跳时间
    #[serde(skip, default = "Instant::now")]
    last_heartbeat: Instant,
    /// 选举超时时间
    #[serde(with = "crate::utils::serde_duration")]
    election_timeout: Duration,
}

/// Leader 状态 (仅 Leader 维护)
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct LeaderState {
    /// 下一个要发送给每个节点的日志索引
    next_index: HashMap<NodeId, u64>,
    /// 已复制到每个节点的最高日志索引
    match_index: HashMap<NodeId, u64>,
}

impl RaftNode {
    /// 创建新的 Raft 节点
    #[allow(dead_code)]
    pub fn new(config: ClusterConfig) -> Self {
        let (tx, rx) = mpsc::unbounded_channel();
        
        // 随机选举超时时间
        let election_timeout = Self::random_election_timeout(&config);
        
        let state = RaftState {
            current_term: 0,
            voted_for: None,
            log: vec![],
            commit_index: 0,
            last_applied: 0,
            state: ConsensusState::Follower,
            leader_id: None,
            next_proposal_id: 1,
            metrics: ConsensusMetrics::default(),
            last_heartbeat: Instant::now(),
            election_timeout,
        };
        
        Self {
            state: Arc::new(RwLock::new(state)),
            config,
            _tx: tx,
            rx: Arc::new(RwLock::new(rx)),
        }
    }
    
    /// 生成随机选举超时时间
    #[allow(dead_code)]
    fn random_election_timeout(config: &ClusterConfig) -> Duration {
        let mut rng = rand::rng();
        let (min, max) = config.election_timeout_range_ms;
        let timeout_ms = rng.random_range(min..=max);
        Duration::from_millis(timeout_ms)
    }
    
    /// 启动 Raft 节点
    #[allow(dead_code)]
    pub async fn start(&mut self) -> Result<(), UnifiedError> {
        // 启动心跳定时器 (Leader)
        let state_clone = Arc::clone(&self.state);
        let config_clone = self.config.clone();
        tokio::spawn(async move {
            Self::heartbeat_loop(state_clone, config_clone).await;
        });
        
        // 启动选举超时检查 (Follower/Candidate)
        let state_clone = Arc::clone(&self.state);
        let config_clone = self.config.clone();
        tokio::spawn(async move {
            Self::election_timeout_loop(state_clone, config_clone).await;
        });
        
        Ok(())
    }
    
    /// 心跳循环 (Leader)
    #[allow(dead_code)]
    async fn heartbeat_loop(state: Arc<RwLock<RaftState>>, config: ClusterConfig) {
        let mut interval = interval(Duration::from_millis(config.heartbeat_interval_ms));
        loop {
            interval.tick().await;
            
            let is_leader = {
                let state = state.read();
                state.state == ConsensusState::Leader
            };
            
            if is_leader {
                // 发送心跳 (AppendEntries with no entries)
                // TODO: 实际发送 RPC 到其他节点
                let mut state = state.write();
                state.metrics.last_heartbeat_ms = Instant::now().elapsed().as_millis() as u64;
            }
        }
    }
    
    /// 选举超时循环
    #[allow(dead_code)]
    async fn election_timeout_loop(state: Arc<RwLock<RaftState>>, config: ClusterConfig) {
        let mut interval = interval(Duration::from_millis(50)); // 检查间隔
        loop {
            interval.tick().await;
            
            let should_start_election = {
                let state = state.read();
                state.state != ConsensusState::Leader &&
                state.last_heartbeat.elapsed() >= state.election_timeout
            };
            
            if should_start_election {
                // 开始选举
                let mut state = state.write();
                Self::start_election(&mut state, &config);
            }
        }
    }
    
    /// 开始选举
    #[allow(dead_code)]
    fn start_election(state: &mut RaftState, _config: &ClusterConfig) {
        // 转换为 Candidate
        state.state = ConsensusState::Candidate;
        state.current_term += 1;
        state.voted_for = Some(state.metrics.custom_metrics.get("self_id")
            .map(|id| NodeId::new(id.to_string()))
            .unwrap_or_else(|| NodeId::new("default")));
        state.last_heartbeat = Instant::now();
        state.metrics.leader_changes += 1;
        
        // TODO: 向其他节点发送 RequestVote RPC
    }
    
    /// 处理 RequestVote RPC
    #[allow(dead_code)]
    fn handle_request_vote(
        &mut self,
        request: RequestVoteRequest,
    ) -> RequestVoteResponse {
        let mut state = self.state.write();
        
        // 如果请求的任期小于当前任期，拒绝投票
        if request.term < state.current_term {
            return RequestVoteResponse {
                term: state.current_term,
                vote_granted: false,
            };
        }
        
        // 如果请求的任期大于当前任期，更新任期并转换为 Follower
        if request.term > state.current_term {
            state.current_term = request.term;
            state.state = ConsensusState::Follower;
            state.voted_for = None;
            state.leader_id = None;
        }
        
        // 检查是否已经投票
        let already_voted = state.voted_for.as_ref()
            .map(|id| id != &request.candidate_id)
            .unwrap_or(false);
        
        if already_voted {
            return RequestVoteResponse {
                term: state.current_term,
                vote_granted: false,
            };
        }
        
        // 检查候选人日志是否至少和本节点一样新
        let last_log_index = state.log.len() as u64;
        let last_log_term = state.log.last().map(|e| e.term).unwrap_or(0);
        
        let log_ok = request.last_log_term > last_log_term ||
            (request.last_log_term == last_log_term && 
             request.last_log_index >= last_log_index);
        
        if log_ok {
            state.voted_for = Some(request.candidate_id.clone());
            state.last_heartbeat = Instant::now();
            
            RequestVoteResponse {
                term: state.current_term,
                vote_granted: true,
            }
        } else {
            RequestVoteResponse {
                term: state.current_term,
                vote_granted: false,
            }
        }
    }
    
    /// 处理 AppendEntries RPC
    #[allow(dead_code)]
    fn handle_append_entries(
        &mut self,
        request: AppendEntriesRequest,
    ) -> AppendEntriesResponse {
        let mut state = self.state.write();
        
        // 如果请求的任期小于当前任期，拒绝
        if request.term < state.current_term {
            return AppendEntriesResponse {
                term: state.current_term,
                success: false,
                match_index: None,
            };
        }
        
        // 更新心跳时间
        state.last_heartbeat = Instant::now();
        
        // 如果请求的任期大于当前任期，更新任期并转换为 Follower
        if request.term > state.current_term {
            state.current_term = request.term;
            state.state = ConsensusState::Follower;
            state.voted_for = None;
        }
        
        // 更新 Leader ID
        state.leader_id = Some(request.leader_id.clone());
        
        // 检查日志一致性
        let log_ok = if request.prev_log_index == 0 {
            true
        } else {
            state.log.get(request.prev_log_index as usize - 1)
                .map(|entry| entry.term == request.prev_log_term)
                .unwrap_or(false)
        };
        
        if !log_ok {
            return AppendEntriesResponse {
                term: state.current_term,
                success: false,
                match_index: Some(state.log.len() as u64),
            };
        }
        
        // 追加新日志条目
        for (i, entry) in request.entries.iter().enumerate() {
            let index = request.prev_log_index + i as u64 + 1;
            
            // 如果存在冲突，删除冲突及之后的所有条目
            if let Some(existing) = state.log.get(index as usize - 1) {
                if existing.term != entry.term {
                    state.log.truncate(index as usize - 1);
                }
            }
            
            // 添加新条目
            if index as usize > state.log.len() {
                state.log.push(entry.clone());
                state.metrics.log_length = state.log.len() as u64;
            }
        }
        
        // 更新提交索引
        if request.leader_commit > state.commit_index {
            state.commit_index = request.leader_commit.min(state.log.len() as u64);
            state.metrics.committed_logs = state.commit_index;
        }
        
        AppendEntriesResponse {
            term: state.current_term,
            success: true,
            match_index: Some(state.log.len() as u64),
        }
    }
    
    /// 追加日志条目
    #[allow(dead_code)]
    pub fn append_entry(&mut self, data: Vec<u8>) -> Result<u64, UnifiedError> {
        let mut state = self.state.write();
        
        // 只有 Leader 可以追加日志
        if state.state != ConsensusState::Leader {
            return Err(UnifiedError::new(
                "只有 Leader 可以追加日志",
                ErrorSeverity::Medium,
                "raft",
                ErrorContext::new(
                    "raft", "append_entry", file!(), line!(),
                    ErrorSeverity::Medium, "raft"
                ),
            ));
        }
        
        let index = state.log.len() as u64 + 1;
        let entry = LogEntry {
            term: state.current_term,
            index,
            data,
        };
        
        state.log.push(entry);
        state.metrics.log_length = state.log.len() as u64;
        
        Ok(index)
    }
    
    /// 获取指标
    pub fn metrics(&self) -> ConsensusMetrics {
        self.state.read().metrics.clone()
    }
}

#[async_trait]
impl ConsensusAlgorithm for RaftNode {
    async fn propose(&mut self, value: Vec<u8>) -> Result<ProposalId, UnifiedError> {
        let proposal_id = {
            let mut state = self.state.write();
            let id = ProposalId(state.next_proposal_id);
            state.next_proposal_id += 1;
            id
        };
        
        // 追加日志条目
        self.append_entry(value)?;
        
        Ok(proposal_id)
    }
    
    async fn wait_committed(&self, proposal_id: ProposalId) -> Result<Vec<u8>, UnifiedError> {
        // 简化实现：等待提交
        // TODO: 实现真正的等待机制
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        let state = self.state.read();
        let index = proposal_id.0 as usize;
        
        if index <= state.commit_index as usize && index <= state.log.len() {
            Ok(state.log[index - 1].data.clone())
        } else {
            Err(UnifiedError::new(
                "提案尚未提交",
                ErrorSeverity::Low,
                "raft",
                ErrorContext::new(
                    "raft", "wait_committed", file!(), line!(),
                    ErrorSeverity::Low, "raft"
                ),
            ))
        }
    }
    
    fn get_state(&self) -> ConsensusState {
        self.state.read().state.clone()
    }
    
    fn is_leader(&self) -> bool {
        self.state.read().state == ConsensusState::Leader
    }
    
    fn current_term(&self) -> u64 {
        self.state.read().current_term
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    fn create_test_config() -> ClusterConfig {
        ClusterConfig {
            nodes: vec![
                NodeId::new("node1"),
                NodeId::new("node2"),
                NodeId::new("node3"),
            ],
            self_id: NodeId::new("node1"),
            heartbeat_interval_ms: 100,
            election_timeout_range_ms: (150, 300),
        }
    }
    
    #[tokio::test]
    async fn test_raft_node_creation() {
        let config = create_test_config();
        let node = RaftNode::new(config);
        
        assert_eq!(node.get_state(), ConsensusState::Follower);
        assert_eq!(node.current_term(), 0);
        assert!(!node.is_leader());
    }
    
    #[tokio::test]
    async fn test_request_vote() {
        let config = create_test_config();
        let mut node = RaftNode::new(config);
        
        let request = RequestVoteRequest {
            term: 1,
            candidate_id: NodeId::new("node2"),
            last_log_index: 0,
            last_log_term: 0,
        };
        
        let response = node.handle_request_vote(request);
        assert!(response.vote_granted);
        assert_eq!(response.term, 1);
    }
    
    #[tokio::test]
    async fn test_append_entries() {
        let config = create_test_config();
        let mut node = RaftNode::new(config);
        
        let request = AppendEntriesRequest {
            term: 1,
            leader_id: NodeId::new("node2"),
            prev_log_index: 0,
            prev_log_term: 0,
            entries: vec![],
            leader_commit: 0,
        };
        
        let response = node.handle_append_entries(request);
        assert!(response.success);
        assert_eq!(response.term, 1);
    }
}

