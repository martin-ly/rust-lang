//! 分布式系统模块
//! 
//! 对齐 Rust 1.89 特性，提供分布式系统基础能力：成员管理、拓扑、共识抽象、分区与一致性、故障与恢复等。

/// 分布式系统配置
#[derive(Debug, Clone)]
pub struct DistributedConfig {
    pub nodes: Vec<String>,
    pub replication_factor: usize,
}

impl Default for DistributedConfig {
    fn default() -> Self {
        Self {
            nodes: Vec::new(),
            replication_factor: 3,
        }
    }
}

pub mod errors;
pub mod membership;
pub mod topology;
pub mod consensus;
pub mod partitioning;
pub mod consistency;
pub mod transport;
pub mod storage;
pub mod scheduling;
pub mod codec;
pub mod swim;
pub mod replication;
pub mod transactions;

#[cfg(feature = "consensus-raft")]
pub mod consensus_raft;

pub use errors::DistributedError;
pub use membership::{ClusterNodeId, ClusterMembership};
pub use topology::{ClusterTopology, ShardId};
pub use consensus::{ConsensusRole, ConsensusApi};
pub use partitioning::{Partitioner, HashPartitioner};
pub use consistency::ConsistencyLevel;
pub use transport::{RpcClient, RpcServer};
pub use storage::{StateMachineStorage, LogStorage};
pub use scheduling::{LogicalClock, TimerService};
pub use codec::{BinaryCodec, BytesCodec, StringUtf8Codec};
pub use swim::{SwimMemberState, SwimEvent, SwimTransport};
pub use replication::{Replicator, QuorumPolicy, MajorityQuorum};
pub use transactions::{Saga, SagaStep};

#[cfg(feature = "consensus-raft")]
pub use consensus_raft::{RaftState, Term, LogIndex, AppendEntriesReq, AppendEntriesResp, RequestVoteReq, RequestVoteResp, RaftNode, MinimalRaft};
