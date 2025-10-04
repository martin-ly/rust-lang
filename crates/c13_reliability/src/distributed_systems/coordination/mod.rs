// Distributed Coordination Module
//
// Provides mechanisms for coordinating distributed systems:
// - Gossip Protocol: Epidemic-style information dissemination
// - Vector Clocks: Causal ordering and conflict detection
// - Hybrid Logical Clocks (HLC): Physical + logical time ordering

pub mod gossip;
pub mod hybrid_logical_clock;
pub mod vector_clock;

// Re-export commonly used types
pub use gossip::{
    GossipConfig, GossipData, GossipMessage, GossipMessageType, GossipMode, GossipNode,
    GossipNodeId, GossipStats, PeerInfo,
};

pub use vector_clock::{
    CausalityTracker, ClockOrdering, NodeId, VectorClock, VectorClockBuilder, VectorClockSnapshot,
};

pub use hybrid_logical_clock::{
    HLCBuilder, HLCTimestamp, HybridLogicalClock, utils as hlc_utils,
};

/// Coordination protocol trait
///
/// Defines a common interface for distributed coordination mechanisms
pub trait CoordinationProtocol: Send + Sync {
    /// Start the coordination protocol
    fn start(&self) -> impl std::future::Future<Output = crate::error_handling::prelude::Result<()>> + Send;

    /// Stop the coordination protocol
    fn stop(&self) -> impl std::future::Future<Output = crate::error_handling::prelude::Result<()>> + Send;

    /// Check if the protocol is running
    fn is_running(&self) -> impl std::future::Future<Output = bool> + Send;
}

/// Timestamp trait for ordering events
pub trait Timestamp: Send + Sync + Clone + Ord {
    /// Create a new timestamp
    fn new() -> Self;

    /// Compare with another timestamp
    fn compare(&self, other: &Self) -> std::cmp::Ordering;

    /// Check if this timestamp happened before another
    fn happened_before(&self, other: &Self) -> bool {
        self.compare(other) == std::cmp::Ordering::Less
    }

    /// Check if this timestamp happened after another
    fn happened_after(&self, other: &Self) -> bool {
        self.compare(other) == std::cmp::Ordering::Greater
    }
}

// Implement Timestamp for HLCTimestamp
impl Timestamp for HLCTimestamp {
    fn new() -> Self {
        Self::now()
    }

    fn compare(&self, other: &Self) -> std::cmp::Ordering {
        self.cmp(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_exports() {
        // Test that all main types are accessible
        let _gossip_config = GossipConfig::default();
        let _vector_clock = VectorClock::new("test".to_string());
        let _hlc = HybridLogicalClock::new();
    }

    #[tokio::test]
    async fn test_gossip_protocol() {
        let config = GossipConfig {
            node_id: GossipNodeId::new("node1"),
            mode: GossipMode::Hybrid,
            gossip_interval_ms: 1000,
            fanout: 3,
            anti_entropy_interval_ms: 10000,
            max_message_size: 1024 * 1024,
            data_ttl: std::time::Duration::from_secs(3600),
        };

        let node = GossipNode::new(config);
        node.set("key1".to_string(), b"value1".to_vec())
            .await
            .unwrap();

        let value = node.get("key1");
        assert_eq!(value, Some(b"value1".to_vec()));
    }

    #[test]
    fn test_vector_clock_causality() {
        let mut clock1 = VectorClock::new("node1".to_string());
        let mut clock2 = VectorClock::new("node2".to_string());

        clock1.increment();
        clock2.increment();

        // These events are concurrent
        assert_eq!(clock1.compare(&clock2), ClockOrdering::Concurrent);
    }

    #[test]
    fn test_hlc_timestamp_ordering() {
        let clock = HybridLogicalClock::new();

        let ts1 = clock.tick();
        let ts2 = clock.tick();

        assert!(ts2 > ts1);
    }
}
