//! # 分布式系统模型
//!
//! 本模块提供分布式系统的核心算法和模型实现：
//! - 分布式共识算法 (Raft, Paxos, etc.)
//! - 分布式事务 (2PC, 3PC, Saga, TCC)
//! - 分布式协调 (Gossip, Vector Clocks, HLC)
//! - 一致性哈希
//! - 分布式锁

pub mod consensus;
pub mod transaction;
pub mod coordination;
pub mod consistent_hashing;
pub mod distributed_lock;
pub mod replication;

// 重新导出核心类型（避免命名冲突）
pub use consensus::types::*;
pub use consensus::raft::RaftNode;
pub use transaction::saga::SagaCoordinator;
// pub use coordination::gossip::GossipProtocol;  // GossipProtocol类型不存在，使用Gossip
pub use coordination::vector_clock::VectorClock;
pub use coordination::hybrid_logical_clock::HybridLogicalClock;
pub use consistent_hashing::{ConsistentHashRing, JumpConsistentHash, RendezvousHash};
pub use distributed_lock::{DistributedLock, RedlockLock, LocalDistributedLock, LockOptions};
pub use replication::{ReplicationCoordinator, ReplicationConfig, ReplicationMode};

