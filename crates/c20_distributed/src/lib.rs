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

pub mod byzantine_fault_tolerance;
pub mod cap_theorem;
pub mod chaos;
pub mod codec;
pub mod config_management;
pub mod consensus;
pub mod consistency;
pub mod errors;
pub mod load_balancing;
pub mod membership;
pub mod partitioning;
pub mod replication;
pub mod scheduling;
pub mod security;
pub mod service_discovery;
pub mod storage;
pub mod swim;
pub mod topology;
pub mod transactions;
pub mod transport;

#[cfg(feature = "consensus-raft")]
pub mod consensus_raft;

pub use byzantine_fault_tolerance::{
    ByzantineMessage, ByzantineNetwork, ByzantineNetworkStats, ByzantineNodeState, PBFTNode,
    PreparedCertificate, ViewChangeCertificate,
};
pub use cap_theorem::{
    CAPAnalysisReport, CAPAnalyzer, CAPManager, ConsistencyDecision, PartitionDetector,
    PartitionStats, PerformanceMetrics,
};
pub use chaos::{ChaosConfig, ChaosInjector};
pub use codec::{BinaryCodec, BytesCodec, StringUtf8Codec};
pub use config_management::{
    ConfigManager, ConfigSnapshot, ConfigSource, ConfigValue, EnvSource, FileSource, InMemorySource,
};
pub use consensus::{ConsensusApi, ConsensusRole};
pub use consistency::{
    CAPStrategy, ConsistencyLevel, MonotonicConsistencyManager, SessionConsistencyManager,
    VectorClock,
};
pub use errors::DistributedError;
pub use load_balancing::{
    ConsistentHashBalancer, GeographicBalancer, LeastConnectionsBalancer,
    LeastResponseTimeBalancer, LoadBalancerManager, LoadBalancingStrategy, RandomBalancer,
    RoundRobinBalancer, ServerStats, WeightedRandomBalancer, WeightedRoundRobinBalancer,
};
pub use membership::{ClusterMembership, ClusterNodeId};
pub use partitioning::{HashPartitioner, Partitioner};
pub use replication::{MajorityQuorum, QuorumPolicy, Replicator};
pub use scheduling::{LogicalClock, TimerService};
pub use security::{
    AclManager, AclRule, Action, AuditEvent, Auditor, CircuitBreaker, CircuitConfig, CircuitState,
    Governance, Principal, RateLimitConfig, Resource, TokenBucket,
};
pub use service_discovery::{
    ConfigServiceDiscovery, DiscoveryStrategy, DnsServiceDiscovery, HealthChecker,
    RegistryServiceDiscovery, ServiceDiscoveryConfig, ServiceDiscoveryManager, ServiceInstance,
};
pub use storage::{LogStorage, StateMachineStorage};
pub use swim::{
    EnhancedSwimTransport, MembershipView, SwimEvent, SwimMemberState, SwimNode, SwimTransport,
};
pub use topology::{ClusterTopology, ShardId};
pub use transactions::{Saga, SagaStep};
pub use transport::{RpcClient, RpcServer};

#[cfg(feature = "consensus-raft")]
pub use consensus_raft::{
    AppendEntriesReq, AppendEntriesResp, LogIndex, MinimalRaft, RaftNode, RaftState,
    RequestVoteReq, RequestVoteResp, Term,
};
