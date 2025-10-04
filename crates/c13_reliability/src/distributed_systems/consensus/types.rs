// ! # 共识算法类型定义

use serde::{Deserialize, Serialize};
use super::{NodeId, LogEntry};

/// RequestVote RPC 请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RequestVoteRequest {
    /// 候选人任期号
    pub term: u64,
    /// 候选人 ID
    pub candidate_id: NodeId,
    /// 候选人最后日志索引
    pub last_log_index: u64,
    /// 候选人最后日志任期
    pub last_log_term: u64,
}

/// RequestVote RPC 响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RequestVoteResponse {
    /// 当前任期号
    pub term: u64,
    /// 是否投票
    pub vote_granted: bool,
}

/// AppendEntries RPC 请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppendEntriesRequest {
    /// Leader 任期号
    pub term: u64,
    /// Leader ID
    pub leader_id: NodeId,
    /// 前一个日志索引
    pub prev_log_index: u64,
    /// 前一个日志任期
    pub prev_log_term: u64,
    /// 日志条目
    pub entries: Vec<LogEntry>,
    /// Leader 提交索引
    pub leader_commit: u64,
}

/// AppendEntries RPC 响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppendEntriesResponse {
    /// 当前任期号
    pub term: u64,
    /// 是否成功
    pub success: bool,
    /// 匹配的日志索引 (用于快速回退)
    pub match_index: Option<u64>,
}

/// InstallSnapshot RPC 请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstallSnapshotRequest {
    /// Leader 任期号
    pub term: u64,
    /// Leader ID
    pub leader_id: NodeId,
    /// 快照最后包含的日志索引
    pub last_included_index: u64,
    /// 快照最后包含的日志任期
    pub last_included_term: u64,
    /// 快照数据偏移量
    pub offset: u64,
    /// 快照数据块
    pub data: Vec<u8>,
    /// 是否为最后一块
    pub done: bool,
}

/// InstallSnapshot RPC 响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstallSnapshotResponse {
    /// 当前任期号
    pub term: u64,
}

/// Raft 消息类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RaftMessage {
    /// 请求投票
    RequestVote(RequestVoteRequest),
    /// 投票响应
    RequestVoteResponse(RequestVoteResponse),
    /// 追加日志
    AppendEntries(AppendEntriesRequest),
    /// 追加日志响应
    AppendEntriesResponse(AppendEntriesResponse),
    /// 安装快照
    InstallSnapshot(InstallSnapshotRequest),
    /// 安装快照响应
    InstallSnapshotResponse(InstallSnapshotResponse),
}

