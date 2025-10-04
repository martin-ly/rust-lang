// Gossip Protocol Implementation
//
// Implements epidemic-style information dissemination for distributed systems.
// Supports Push, Pull, and Hybrid gossip modes with anti-entropy mechanisms.

use crate::error_handling::prelude::*;
use chrono::{DateTime, Utc};
use dashmap::DashMap;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use tokio::time;
use uuid::Uuid;

/// Unique identifier for a gossip node
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct GossipNodeId(String);

impl GossipNodeId {
    pub fn new(id: impl Into<String>) -> Self {
        Self(id.into())
    }

    pub fn random() -> Self {
        Self(Uuid::new_v4().to_string())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Gossip message types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum GossipMessageType {
    /// Push: Send updates to peer
    Push,
    /// Pull: Request updates from peer
    Pull,
    /// PullResponse: Respond to pull request
    PullResponse,
    /// Ack: Acknowledge receipt
    Ack,
}

/// A piece of gossip data with versioning
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GossipData {
    pub key: String,
    pub value: Vec<u8>,
    pub version: u64,
    pub timestamp: DateTime<Utc>,
    pub source_node: GossipNodeId,
}

/// Gossip message envelope
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GossipMessage {
    pub id: String,
    pub message_type: GossipMessageType,
    pub sender: GossipNodeId,
    pub data: Vec<GossipData>,
    pub digest: Option<HashMap<String, u64>>, // For anti-entropy: key -> version
}

impl GossipMessage {
    pub fn new_push(sender: GossipNodeId, data: Vec<GossipData>) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            message_type: GossipMessageType::Push,
            sender,
            data,
            digest: None,
        }
    }

    pub fn new_pull(sender: GossipNodeId, digest: HashMap<String, u64>) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            message_type: GossipMessageType::Pull,
            sender,
            data: vec![],
            digest: Some(digest),
        }
    }

    pub fn new_pull_response(sender: GossipNodeId, data: Vec<GossipData>) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            message_type: GossipMessageType::PullResponse,
            sender,
            data,
            digest: None,
        }
    }
}

/// Gossip protocol mode
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GossipMode {
    /// Push-based: Actively send updates to peers
    Push,
    /// Pull-based: Request updates from peers
    Pull,
    /// Hybrid: Combine push and pull for faster convergence
    Hybrid,
}

/// Gossip protocol configuration
#[derive(Debug, Clone)]
pub struct GossipConfig {
    /// Node identifier
    pub node_id: GossipNodeId,
    /// Gossip protocol mode
    pub mode: GossipMode,
    /// Gossip interval (milliseconds)
    pub gossip_interval_ms: u64,
    /// Number of peers to gossip with per round
    pub fanout: usize,
    /// Anti-entropy interval (milliseconds) - for digest synchronization
    pub anti_entropy_interval_ms: u64,
    /// Maximum message size (bytes)
    pub max_message_size: usize,
    /// Garbage collection: Remove data older than this duration
    pub data_ttl: Duration,
}

impl Default for GossipConfig {
    fn default() -> Self {
        Self {
            node_id: GossipNodeId::random(),
            mode: GossipMode::Hybrid,
            gossip_interval_ms: 1000,
            fanout: 3,
            anti_entropy_interval_ms: 10000,
            max_message_size: 1024 * 1024, // 1MB
            data_ttl: Duration::from_secs(3600), // 1 hour
        }
    }
}

/// Peer node information
#[derive(Debug, Clone)]
pub struct PeerInfo {
    pub node_id: GossipNodeId,
    pub address: String,
    pub last_seen: DateTime<Utc>,
    pub failure_count: u32,
}

impl PeerInfo {
    pub fn new(node_id: GossipNodeId, address: String) -> Self {
        Self {
            node_id,
            address,
            last_seen: Utc::now(),
            failure_count: 0,
        }
    }

    pub fn mark_seen(&mut self) {
        self.last_seen = Utc::now();
        self.failure_count = 0;
    }

    pub fn mark_failed(&mut self) {
        self.failure_count += 1;
    }

    pub fn is_alive(&self, timeout: Duration) -> bool {
        let elapsed = Utc::now() - self.last_seen;
        elapsed.to_std().unwrap_or(Duration::MAX) < timeout && self.failure_count < 3
    }
}

/// Gossip node statistics
#[derive(Debug, Default, Clone)]
pub struct GossipStats {
    pub messages_sent: u64,
    pub messages_received: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub push_count: u64,
    pub pull_count: u64,
    pub anti_entropy_rounds: u64,
    pub data_items: usize,
}

/// Gossip protocol node
pub struct GossipNode {
    config: GossipConfig,
    /// Local data store: key -> GossipData
    data_store: Arc<DashMap<String, GossipData>>,
    /// Known peers
    peers: Arc<RwLock<Vec<PeerInfo>>>,
    /// Statistics
    stats: Arc<RwLock<GossipStats>>,
    /// Running state
    running: Arc<RwLock<bool>>,
}

impl GossipNode {
    /// Create a new gossip node
    pub fn new(config: GossipConfig) -> Self {
        Self {
            config,
            data_store: Arc::new(DashMap::new()),
            peers: Arc::new(RwLock::new(Vec::new())),
            stats: Arc::new(RwLock::new(GossipStats::default())),
            running: Arc::new(RwLock::new(false)),
        }
    }

    /// Start the gossip protocol
    pub async fn start(&self) -> Result<()> {
        let mut running = self.running.write().await;
        if *running {
            return Err(UnifiedError::new(
                "Gossip node already running",
                ErrorSeverity::Medium,
                "gossip",
                ErrorContext::new(
                    "gossip",
                    "start",
                    file!(),
                    line!(),
                    ErrorSeverity::Medium,
                    "gossip",
                ),
            ));
        }

        *running = true;
        drop(running);

        // Start gossip task
        self.start_gossip_task();

        // Start anti-entropy task
        self.start_anti_entropy_task();

        // Start garbage collection task
        self.start_gc_task();

        Ok(())
    }

    /// Stop the gossip protocol
    pub async fn stop(&self) -> Result<()> {
        let mut running = self.running.write().await;
        *running = false;
        Ok(())
    }

    /// Add a peer to the gossip network
    pub async fn add_peer(&self, peer_info: PeerInfo) {
        let mut peers = self.peers.write().await;
        if !peers.iter().any(|p| p.node_id == peer_info.node_id) {
            peers.push(peer_info);
        }
    }

    /// Remove a peer from the gossip network
    pub async fn remove_peer(&self, node_id: &GossipNodeId) {
        let mut peers = self.peers.write().await;
        peers.retain(|p| &p.node_id != node_id);
    }

    /// Set a local data item
    pub async fn set(&self, key: String, value: Vec<u8>) -> Result<()> {
        let version = self
            .data_store
            .get(&key)
            .map(|d| d.version + 1)
            .unwrap_or(1);

        let data = GossipData {
            key: key.clone(),
            value,
            version,
            timestamp: Utc::now(),
            source_node: self.config.node_id.clone(),
        };

        self.data_store.insert(key, data);

        let mut stats = self.stats.write().await;
        stats.data_items = self.data_store.len();

        Ok(())
    }

    /// Get a local data item
    pub fn get(&self, key: &str) -> Option<Vec<u8>> {
        self.data_store.get(key).map(|d| d.value.clone())
    }

    /// Get all keys
    pub fn keys(&self) -> Vec<String> {
        self.data_store.iter().map(|e| e.key().clone()).collect()
    }

    /// Handle incoming gossip message
    pub async fn handle_message(&self, message: GossipMessage) -> Result<Option<GossipMessage>> {
        let mut stats = self.stats.write().await;
        stats.messages_received += 1;
        drop(stats);

        match message.message_type {
            GossipMessageType::Push => self.handle_push(message).await,
            GossipMessageType::Pull => self.handle_pull(message).await,
            GossipMessageType::PullResponse => self.handle_pull_response(message).await,
            GossipMessageType::Ack => {
                // Just acknowledge
                Ok(None)
            }
        }
    }

    /// Get current statistics
    pub async fn get_stats(&self) -> GossipStats {
        self.stats.read().await.clone()
    }

    // Private methods
    #[allow(dead_code)]
    #[allow(unused_variables)]
    fn start_gossip_task(&self) {
        let config = self.config.clone();
        let data_store = Arc::clone(&self.data_store);
        let peers = Arc::clone(&self.peers);
        let stats = Arc::clone(&self.stats);
        let running = Arc::clone(&self.running);

        tokio::spawn(async move {
            let mut interval = time::interval(Duration::from_millis(config.gossip_interval_ms));

            while *running.read().await {
                interval.tick().await;

                // Select random peers
                let peers_list = peers.read().await;
                let alive_peers: Vec<_> = peers_list
                    .iter()
                    .filter(|p| p.is_alive(Duration::from_secs(30)))
                    .collect();

                if alive_peers.is_empty() {
                    continue;
                }

                let fanout = config.fanout.min(alive_peers.len());
                let selected_peers: Vec<_> = (0..fanout)
                    .map(|i| alive_peers[i % alive_peers.len()].clone())
                    .collect();
                drop(peers_list);

                // Collect data to gossip
                let data_to_send: Vec<GossipData> = data_store
                    .iter()
                    .take(100) // Limit batch size
                    .map(|e| e.value().clone())
                    .collect();

                if data_to_send.is_empty() {
                    continue;
                }

                // Send gossip messages
                for peer in selected_peers {
                    let message = match config.mode {
                        GossipMode::Push => {
                            GossipMessage::new_push(config.node_id.clone(), data_to_send.clone())
                        }
                        GossipMode::Pull => {
                            let digest = Self::create_digest(&data_store);
                            GossipMessage::new_pull(config.node_id.clone(), digest)
                        }
                        GossipMode::Hybrid => {
                            // In hybrid mode, alternate or do both
                            GossipMessage::new_push(config.node_id.clone(), data_to_send.clone())
                        }
                    };

                    // TODO: Actually send the message over the network
                    // For now, just update stats
                    let mut stats_guard = stats.write().await;
                    stats_guard.messages_sent += 1;
                    match config.mode {
                        GossipMode::Push | GossipMode::Hybrid => stats_guard.push_count += 1,
                        GossipMode::Pull => stats_guard.pull_count += 1,
                    }
                }
            }
        });
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    fn start_anti_entropy_task(&self) {
        let config = self.config.clone();
        let data_store = Arc::clone(&self.data_store);
        let peers = Arc::clone(&self.peers);
        let stats = Arc::clone(&self.stats);
        let running = Arc::clone(&self.running);

        tokio::spawn(async move {
            let mut interval =
                time::interval(Duration::from_millis(config.anti_entropy_interval_ms));

            while *running.read().await {
                interval.tick().await;

                let peers_list = peers.read().await;
                if peers_list.is_empty() {
                    continue;
                }

                // Select a random peer for anti-entropy
                let peer = &peers_list[0]; // Simplified: just take first peer
                drop(peers_list);

                // Create digest of local data
                let digest = Self::create_digest(&data_store);

                // Create pull request with digest
                let _message = GossipMessage::new_pull(config.node_id.clone(), digest);

                // TODO: Send pull request and reconcile differences

                let mut stats_guard = stats.write().await;
                stats_guard.anti_entropy_rounds += 1;
            }
        });
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    fn start_gc_task(&self) {
        let config = self.config.clone();
        let data_store = Arc::clone(&self.data_store);
        let running = Arc::clone(&self.running);

        tokio::spawn(async move {
            let mut interval = time::interval(Duration::from_secs(60)); // Every minute

            while *running.read().await {
                interval.tick().await;

                let now = Utc::now();
                let ttl = config.data_ttl;

                // Remove expired data
                data_store.retain(|_, data| {
                    let age = now - data.timestamp;
                    age.to_std().unwrap_or(Duration::ZERO) < ttl
                });
            }
        });
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    fn create_digest(data_store: &DashMap<String, GossipData>) -> HashMap<String, u64> {
        data_store
            .iter()
            .map(|e| (e.key().clone(), e.value().version))
            .collect()
    }

    async fn handle_push(&self, message: GossipMessage) -> Result<Option<GossipMessage>> {
        // Merge incoming data
        for data in message.data {
            self.merge_data(data);
        }

        let mut stats = self.stats.write().await;
        stats.push_count += 1;
        stats.data_items = self.data_store.len();

        Ok(None)
    }

    async fn handle_pull(&self, message: GossipMessage) -> Result<Option<GossipMessage>> {
        let digest = message.digest.unwrap_or_default();

        // Find data that peer is missing or has older versions of
        let mut data_to_send = Vec::new();

        for entry in self.data_store.iter() {
            let key = entry.key();
            let local_data = entry.value();

            let peer_version = digest.get(key).copied().unwrap_or(0);

            if local_data.version > peer_version {
                data_to_send.push(local_data.clone());
            }
        }

        let mut stats = self.stats.write().await;
        stats.pull_count += 1;

        // Create pull response
        let response = GossipMessage::new_pull_response(self.config.node_id.clone(), data_to_send);

        Ok(Some(response))
    }

    async fn handle_pull_response(&self, message: GossipMessage) -> Result<Option<GossipMessage>> {
        // Merge incoming data
        for data in message.data {
            self.merge_data(data);
        }

        let mut stats = self.stats.write().await;
        stats.data_items = self.data_store.len();

        Ok(None)
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    fn merge_data(&self, incoming: GossipData) {
        let key = incoming.key.clone();

        if let Some(mut local) = self.data_store.get_mut(&key) {
            // Only update if incoming version is newer
            if incoming.version > local.version {
                *local = incoming;
            }
        } else {
            // New key, insert it
            self.data_store.insert(key, incoming);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_gossip_node_creation() {
        let config = GossipConfig::default();
        let node = GossipNode::new(config);

        assert_eq!(node.data_store.len(), 0);
    }

    #[tokio::test]
    async fn test_set_and_get() {
        let config = GossipConfig::default();
        let node = GossipNode::new(config);

        node.set("key1".to_string(), b"value1".to_vec())
            .await
            .unwrap();

        let value = node.get("key1");
        assert_eq!(value, Some(b"value1".to_vec()));
    }

    #[tokio::test]
    async fn test_add_peer() {
        let config = GossipConfig::default();
        let node = GossipNode::new(config);

        let peer = PeerInfo::new(GossipNodeId::new("peer1"), "127.0.0.1:8000".to_string());
        node.add_peer(peer).await;

        let peers = node.peers.read().await;
        assert_eq!(peers.len(), 1);
    }

    #[tokio::test]
    async fn test_message_push() {
        let config = GossipConfig::default();
        let node = GossipNode::new(config.clone());

        let data = GossipData {
            key: "test".to_string(),
            value: b"test_value".to_vec(),
            version: 1,
            timestamp: Utc::now(),
            source_node: GossipNodeId::new("source"),
        };

        let message = GossipMessage::new_push(GossipNodeId::new("sender"), vec![data]);

        let response = node.handle_message(message).await.unwrap();
        assert!(response.is_none());

        let value = node.get("test");
        assert_eq!(value, Some(b"test_value".to_vec()));
    }

    #[tokio::test]
    async fn test_version_conflict_resolution() {
        let config = GossipConfig::default();
        let node = GossipNode::new(config);

        // Set initial data with version 1
        let data_v1 = GossipData {
            key: "key".to_string(),
            value: b"value_v1".to_vec(),
            version: 1,
            timestamp: Utc::now(),
            source_node: GossipNodeId::new("node1"),
        };
        node.merge_data(data_v1);

        // Try to merge older version
        let data_v0 = GossipData {
            key: "key".to_string(),
            value: b"value_v0".to_vec(),
            version: 0,
            timestamp: Utc::now(),
            source_node: GossipNodeId::new("node2"),
        };
        node.merge_data(data_v0);

        // Should still have v1
        let value = node.get("key");
        assert_eq!(value, Some(b"value_v1".to_vec()));

        // Merge newer version
        let data_v2 = GossipData {
            key: "key".to_string(),
            value: b"value_v2".to_vec(),
            version: 2,
            timestamp: Utc::now(),
            source_node: GossipNodeId::new("node3"),
        };
        node.merge_data(data_v2);

        // Should now have v2
        let value = node.get("key");
        assert_eq!(value, Some(b"value_v2".to_vec()));
    }
}
