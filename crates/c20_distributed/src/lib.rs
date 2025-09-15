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
pub mod cap_theorem;
pub mod byzantine_fault_tolerance;
pub mod service_discovery;
pub mod load_balancing;
pub mod config_management;
pub mod chaos;
pub mod security;

#[cfg(feature = "consensus-raft")]
pub mod consensus_raft;

pub use errors::DistributedError;
pub use membership::{ClusterNodeId, ClusterMembership};
pub use topology::{ClusterTopology, ShardId};
pub use consensus::{ConsensusRole, ConsensusApi};
pub use partitioning::{Partitioner, HashPartitioner};
pub use consistency::{
    ConsistencyLevel, CAPStrategy, VectorClock, 
    SessionConsistencyManager, MonotonicConsistencyManager
};
pub use transport::{RpcClient, RpcServer};
pub use storage::{StateMachineStorage, LogStorage};
pub use scheduling::{LogicalClock, TimerService};
pub use codec::{BinaryCodec, BytesCodec, StringUtf8Codec};
pub use swim::{
    SwimMemberState, SwimEvent, SwimTransport, SwimNode, 
    MembershipView, EnhancedSwimTransport
};
pub use replication::{Replicator, QuorumPolicy, MajorityQuorum};
pub use transactions::{Saga, SagaStep};
pub use cap_theorem::{
    CAPManager, CAPAnalyzer, PartitionDetector, PartitionStats,
    ConsistencyDecision, PerformanceMetrics, CAPAnalysisReport
};
pub use byzantine_fault_tolerance::{
    PBFTNode, ByzantineNetwork, ByzantineMessage, ByzantineNodeState,
    PreparedCertificate, ViewChangeCertificate, ByzantineNetworkStats
};
pub use service_discovery::{
    ServiceInstance, DiscoveryStrategy, ServiceDiscoveryConfig,
    DnsServiceDiscovery, ConfigServiceDiscovery, RegistryServiceDiscovery,
    ServiceDiscoveryManager, HealthChecker
};
pub use load_balancing::{
    LoadBalancingStrategy, ServerStats, RoundRobinBalancer, WeightedRoundRobinBalancer,
    LeastConnectionsBalancer, ConsistentHashBalancer, RandomBalancer, WeightedRandomBalancer,
    LeastResponseTimeBalancer, GeographicBalancer, LoadBalancerManager
};
pub use config_management::{
    ConfigValue, ConfigSource, InMemorySource, FileSource, EnvSource,
    ConfigSnapshot, ConfigManager
};
pub use chaos::{ChaosConfig, ChaosInjector};
pub use security::{
    Principal, Resource, Action, AclRule, AclManager,
    AuditEvent, Auditor,
    RateLimitConfig, TokenBucket,
    CircuitState, CircuitConfig, CircuitBreaker,
    Governance,
};

#[cfg(feature = "consensus-raft")]
pub use consensus_raft::{RaftState, Term, LogIndex, AppendEntriesReq, AppendEntriesResp, RequestVoteReq, RequestVoteResp, RaftNode, MinimalRaft};
