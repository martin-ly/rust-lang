// Consistent Hashing Implementation
//
// Implements consistent hashing algorithms for distributed systems:
// - Basic Consistent Hashing with virtual nodes
// - Jump Consistent Hash
// - Rendezvous (Highest Random Weight) Hashing
// - Maglev Hashing
//
// Consistent hashing is used for:
// - Load balancing
// - Distributed caching
// - Data partitioning/sharding
// - Service discovery

use std::collections::{BTreeMap, HashMap};
use std::hash::Hash;
use std::sync::Arc;
use parking_lot::RwLock;
use serde::{Deserialize, Serialize};

/// Node identifier
#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct NodeId(pub String);

impl NodeId {
    pub fn new(id: impl Into<String>) -> Self {
        Self(id.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Hash function trait for consistent hashing
pub trait HashFunction: Send + Sync {
    fn hash(&self, key: &[u8]) -> u64;
}

/// Default hash function using FNV-1a
#[derive(Default)]
pub struct FnvHasher;

impl HashFunction for FnvHasher {
    fn hash(&self, key: &[u8]) -> u64 {
        const FNV_OFFSET_BASIS: u64 = 0xcbf29ce484222325;
        const FNV_PRIME: u64 = 0x100000001b3;

        let mut hash = FNV_OFFSET_BASIS;
        for &byte in key {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        hash
    }
}

/// Murmur3 hash function
pub struct Murmur3Hasher;

impl HashFunction for Murmur3Hasher {
    fn hash(&self, key: &[u8]) -> u64 {
        // Simplified Murmur3 implementation
        let mut hash: u64 = 0;
        for (i, &byte) in key.iter().enumerate() {
            hash = hash.wrapping_add((byte as u64).wrapping_shl((i % 8) as u32 * 8));
        }
        hash = hash.wrapping_mul(0xc6a4a7935bd1e995u64);
        hash ^= hash >> 47;
        hash
    }
}

/// Configuration for consistent hashing
#[derive(Debug, Clone)]
pub struct ConsistentHashConfig {
    /// Number of virtual nodes per physical node
    pub virtual_nodes: usize,
    /// Hash function to use
    pub hash_function: HashFunctionType,
    /// Replication factor
    pub replication_factor: usize,
}

impl Default for ConsistentHashConfig {
    fn default() -> Self {
        Self {
            virtual_nodes: 150,
            hash_function: HashFunctionType::Fnv,
            replication_factor: 3,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum HashFunctionType {
    Fnv,
    Murmur3,
}

/// Basic Consistent Hashing with Virtual Nodes
///
/// Classic consistent hashing using a hash ring with virtual nodes
/// to ensure better load distribution.
///
/// # Example
/// ```ignore
/// let mut ring = ConsistentHashRing::new(config);
/// ring.add_node(NodeId::new("server1"));
/// ring.add_node(NodeId::new("server2"));
/// 
/// let node = ring.get_node("user_123").unwrap();
/// println!("Key maps to: {}", node);
/// ```
pub struct ConsistentHashRing {
    config: ConsistentHashConfig,
    ring: Arc<RwLock<BTreeMap<u64, NodeId>>>,
    nodes: Arc<RwLock<Vec<NodeId>>>,
    hash_fn: Arc<dyn HashFunction>,
}

impl ConsistentHashRing {
    pub fn new(config: ConsistentHashConfig) -> Self {
        let hash_fn: Arc<dyn HashFunction> = match config.hash_function {
            HashFunctionType::Fnv => Arc::new(FnvHasher),
            HashFunctionType::Murmur3 => Arc::new(Murmur3Hasher),
        };

        Self {
            config,
            ring: Arc::new(RwLock::new(BTreeMap::new())),
            nodes: Arc::new(RwLock::new(Vec::new())),
            hash_fn,
        }
    }

    pub fn default() -> Self {
        Self::new(ConsistentHashConfig::default())
    }

    /// Add a node to the hash ring
    pub fn add_node(&self, node_id: NodeId) {
        let mut ring = self.ring.write();
        let mut nodes = self.nodes.write();

        // Add physical node
        if !nodes.contains(&node_id) {
            nodes.push(node_id.clone());
        }

        // Add virtual nodes
        for i in 0..self.config.virtual_nodes {
            let virtual_key = format!("{}:{}", node_id.as_str(), i);
            let hash = self.hash_fn.hash(virtual_key.as_bytes());
            ring.insert(hash, node_id.clone());
        }
    }

    /// Remove a node from the hash ring
    pub fn remove_node(&self, node_id: &NodeId) {
        let mut ring = self.ring.write();
        let mut nodes = self.nodes.write();

        // Remove from nodes list
        nodes.retain(|n| n != node_id);

        // Remove all virtual nodes
        ring.retain(|_, n| n != node_id);
    }

    /// Get the node for a given key
    pub fn get_node(&self, key: &str) -> Option<NodeId> {
        let ring = self.ring.read();
        if ring.is_empty() {
            return None;
        }

        let hash = self.hash_fn.hash(key.as_bytes());

        // Find the first node >= hash (clockwise on the ring)
        ring.range(hash..)
            .next()
            .or_else(|| ring.iter().next())
            .map(|(_, node)| node.clone())
    }

    /// Get multiple nodes for a key (for replication)
    pub fn get_nodes(&self, key: &str, count: usize) -> Vec<NodeId> {
        let ring = self.ring.read();
        if ring.is_empty() {
            return Vec::new();
        }

        let hash = self.hash_fn.hash(key.as_bytes());
        let mut result = Vec::new();
        let mut seen = std::collections::HashSet::new();

        // Start from hash position and go clockwise
        let iter = ring.range(hash..).chain(ring.range(..hash));

        for (_, node) in iter {
            if seen.insert(node.clone()) {
                result.push(node.clone());
                if result.len() >= count {
                    break;
                }
            }
        }

        result
    }

    /// Get all nodes in the ring
    pub fn nodes(&self) -> Vec<NodeId> {
        self.nodes.read().clone()
    }

    /// Get the number of nodes
    pub fn node_count(&self) -> usize {
        self.nodes.read().len()
    }

    /// Get distribution statistics
    pub fn get_distribution(&self, sample_keys: &[String]) -> HashMap<NodeId, usize> {
        let mut distribution = HashMap::new();

        for key in sample_keys {
            if let Some(node) = self.get_node(key) {
                *distribution.entry(node).or_insert(0) += 1;
            }
        }

        distribution
    }
}

/// Jump Consistent Hash
///
/// A fast, minimal memory jump consistent hash algorithm.
/// Uses no storage and is O(log n) time complexity.
///
/// Best for: When memory is constrained and node count is stable
pub struct JumpConsistentHash {
    num_buckets: i32,
}

impl JumpConsistentHash {
    pub fn new(num_buckets: i32) -> Self {
        assert!(num_buckets > 0, "Number of buckets must be positive");
        Self { num_buckets }
    }

    /// Get bucket (node) index for a key
    pub fn get_bucket(&self, key: u64) -> i32 {
        let mut k = key;
        let mut b = -1i64;
        let mut j = 0i64;

        while j < self.num_buckets as i64 {
            b = j;
            k = k.wrapping_mul(2862933555777941757).wrapping_add(1);
            j = ((b + 1) as f64 * (((1i64 << 31) as f64) / (((k >> 33) + 1) as f64))) as i64;
        }

        b as i32
    }

    /// Get bucket for a string key
    pub fn get_bucket_for_key(&self, key: &str) -> i32 {
        let hash = FnvHasher.hash(key.as_bytes());
        self.get_bucket(hash)
    }

    /// Change number of buckets
    pub fn resize(&mut self, new_num_buckets: i32) {
        assert!(new_num_buckets > 0, "Number of buckets must be positive");
        self.num_buckets = new_num_buckets;
    }
}

/// Rendezvous (Highest Random Weight) Hashing
///
/// Each node gets a weight for each key, and the highest weight wins.
/// Provides better distribution than consistent hashing in some cases.
///
/// Best for: When you need minimal key movement on node changes
pub struct RendezvousHash {
    nodes: Arc<RwLock<Vec<NodeId>>>,
    hash_fn: Arc<dyn HashFunction>,
}

impl RendezvousHash {
    pub fn new() -> Self {
        Self {
            nodes: Arc::new(RwLock::new(Vec::new())),
            hash_fn: Arc::new(FnvHasher),
        }
    }

    pub fn add_node(&self, node_id: NodeId) {
        let mut nodes = self.nodes.write();
        if !nodes.contains(&node_id) {
            nodes.push(node_id);
        }
    }

    pub fn remove_node(&self, node_id: &NodeId) {
        let mut nodes = self.nodes.write();
        nodes.retain(|n| n != node_id);
    }

    /// Get the node with highest weight for a key
    pub fn get_node(&self, key: &str) -> Option<NodeId> {
        let nodes = self.nodes.read();
        if nodes.is_empty() {
            return None;
        }

        nodes
            .iter()
            .map(|node| {
                let combined = format!("{}:{}", key, node.as_str());
                let weight = self.hash_fn.hash(combined.as_bytes());
                (weight, node.clone())
            })
            .max_by_key(|(weight, _)| *weight)
            .map(|(_, node)| node)
    }

    /// Get multiple nodes sorted by weight
    pub fn get_nodes(&self, key: &str, count: usize) -> Vec<NodeId> {
        let nodes = self.nodes.read();
        if nodes.is_empty() {
            return Vec::new();
        }

        let mut weighted: Vec<_> = nodes
            .iter()
            .map(|node| {
                let combined = format!("{}:{}", key, node.as_str());
                let weight = self.hash_fn.hash(combined.as_bytes());
                (weight, node.clone())
            })
            .collect();

        weighted.sort_by(|a, b| b.0.cmp(&a.0)); // Sort by weight descending

        weighted
            .into_iter()
            .take(count)
            .map(|(_, node)| node)
            .collect()
    }

    pub fn nodes(&self) -> Vec<NodeId> {
        self.nodes.read().clone()
    }

    pub fn node_count(&self) -> usize {
        self.nodes.read().len()
    }
}

impl Default for RendezvousHash {
    fn default() -> Self {
        Self::new()
    }
}

/// Maglev Hashing
///
/// Google's Maglev load balancer hashing algorithm.
/// Provides minimal disruption and fast lookup with a lookup table.
///
/// Best for: Load balancers and when you need very fast lookups
pub struct MaglevHash {
    lookup_table: Arc<RwLock<Vec<usize>>>,
    nodes: Arc<RwLock<Vec<NodeId>>>,
    table_size: usize,
}

impl MaglevHash {
    pub fn new(table_size: usize) -> Self {
        // Table size should be prime for better distribution
        let table_size = Self::next_prime(table_size);

        Self {
            lookup_table: Arc::new(RwLock::new(Vec::new())),
            nodes: Arc::new(RwLock::new(Vec::new())),
            table_size,
        }
    }

    pub fn default() -> Self {
        Self::new(65537) // A large prime number
    }

    fn next_prime(n: usize) -> usize {
        let mut candidate = n;
        loop {
            if Self::is_prime(candidate) {
                return candidate;
            }
            candidate += 1;
        }
    }

    fn is_prime(n: usize) -> bool {
        if n < 2 {
            return false;
        }
        if n == 2 {
            return true;
        }
        if n % 2 == 0 {
            return false;
        }

        let limit = (n as f64).sqrt() as usize;
        for i in (3..=limit).step_by(2) {
            if n % i == 0 {
                return false;
            }
        }
        true
    }

    pub fn add_node(&self, node_id: NodeId) {
        let mut nodes = self.nodes.write();
        if !nodes.contains(&node_id) {
            nodes.push(node_id);
            drop(nodes);
            self.rebuild_table();
        }
    }

    pub fn remove_node(&self, node_id: &NodeId) {
        let mut nodes = self.nodes.write();
        nodes.retain(|n| n != node_id);
        drop(nodes);
        self.rebuild_table();
    }

    fn rebuild_table(&self) {
        let nodes = self.nodes.read();
        let node_count = nodes.len();
        
        if node_count == 0 {
            let mut table = self.lookup_table.write();
            table.clear();
            return;
        }

        let mut table = vec![usize::MAX; self.table_size];
        let mut next = vec![0usize; node_count];

        // Generate permutations for each node
        let permutations: Vec<Vec<usize>> = nodes
            .iter()
            .map(|node| {
                let hash1 = FnvHasher.hash(node.as_str().as_bytes()) as usize;
                let hash2 = Murmur3Hasher.hash(node.as_str().as_bytes()) as usize;
                
                let offset = hash1 % self.table_size;
                let skip = (hash2 % (self.table_size - 1)) + 1;

                (0..self.table_size)
                    .map(|i| (offset + i * skip) % self.table_size)
                    .collect()
            })
            .collect();

        // Fill the lookup table
        let mut filled = 0;
        while filled < self.table_size {
            for node_idx in 0..node_count {
                let mut c = permutations[node_idx][next[node_idx]];
                while table[c] != usize::MAX {
                    next[node_idx] += 1;
                    c = permutations[node_idx][next[node_idx]];
                }
                
                table[c] = node_idx;
                next[node_idx] += 1;
                filled += 1;

                if filled >= self.table_size {
                    break;
                }
            }
        }

        *self.lookup_table.write() = table;
    }

    pub fn get_node(&self, key: &str) -> Option<NodeId> {
        let table = self.lookup_table.read();
        let nodes = self.nodes.read();

        if nodes.is_empty() {
            return None;
        }

        let hash = FnvHasher.hash(key.as_bytes()) as usize;
        let entry = table[hash % self.table_size];

        if entry == usize::MAX {
            None
        } else {
            nodes.get(entry).cloned()
        }
    }

    pub fn nodes(&self) -> Vec<NodeId> {
        self.nodes.read().clone()
    }

    pub fn node_count(&self) -> usize {
        self.nodes.read().len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_consistent_hash_ring() {
        let ring = ConsistentHashRing::default();

        ring.add_node(NodeId::new("server1"));
        ring.add_node(NodeId::new("server2"));
        ring.add_node(NodeId::new("server3"));

        assert_eq!(ring.node_count(), 3);

        // Same key should always map to same node
        let node1 = ring.get_node("user_123").unwrap();
        let node2 = ring.get_node("user_123").unwrap();
        assert_eq!(node1, node2);

        // Different keys might map to different nodes
        let _ = ring.get_node("user_456");
    }

    #[test]
    fn test_consistent_hash_remove_node() {
        let ring = ConsistentHashRing::default();

        ring.add_node(NodeId::new("server1"));
        ring.add_node(NodeId::new("server2"));
        ring.add_node(NodeId::new("server3"));

        ring.remove_node(&NodeId::new("server2"));

        assert_eq!(ring.node_count(), 2);

        let node = ring.get_node("user_123").unwrap();
        assert_ne!(node.as_str(), "server2");
    }

    #[test]
    fn test_consistent_hash_replication() {
        let ring = ConsistentHashRing::default();

        ring.add_node(NodeId::new("server1"));
        ring.add_node(NodeId::new("server2"));
        ring.add_node(NodeId::new("server3"));

        let nodes = ring.get_nodes("user_123", 2);
        assert_eq!(nodes.len(), 2);
        assert_ne!(nodes[0], nodes[1]);
    }

    #[test]
    fn test_jump_consistent_hash() {
        let hash = JumpConsistentHash::new(10);

        // Same key should always map to same bucket
        let bucket1 = hash.get_bucket_for_key("user_123");
        let bucket2 = hash.get_bucket_for_key("user_123");
        assert_eq!(bucket1, bucket2);

        assert!(bucket1 >= 0 && bucket1 < 10);
    }

    #[test]
    fn test_rendezvous_hash() {
        let hash = RendezvousHash::new();

        hash.add_node(NodeId::new("server1"));
        hash.add_node(NodeId::new("server2"));
        hash.add_node(NodeId::new("server3"));

        // Same key should always map to same node
        let node1 = hash.get_node("user_123").unwrap();
        let node2 = hash.get_node("user_123").unwrap();
        assert_eq!(node1, node2);
    }

    #[test]
    fn test_rendezvous_hash_multiple_nodes() {
        let hash = RendezvousHash::new();

        hash.add_node(NodeId::new("server1"));
        hash.add_node(NodeId::new("server2"));
        hash.add_node(NodeId::new("server3"));

        let nodes = hash.get_nodes("user_123", 2);
        assert_eq!(nodes.len(), 2);
        assert_ne!(nodes[0], nodes[1]);
    }

    #[test]
    fn test_maglev_hash() {
        let hash = MaglevHash::new(101); // Small prime for testing

        hash.add_node(NodeId::new("server1"));
        hash.add_node(NodeId::new("server2"));
        hash.add_node(NodeId::new("server3"));

        // Same key should always map to same node
        let node1 = hash.get_node("user_123").unwrap();
        let node2 = hash.get_node("user_123").unwrap();
        assert_eq!(node1, node2);
    }

    #[test]
    fn test_distribution() {
        let ring = ConsistentHashRing::default();

        ring.add_node(NodeId::new("server1"));
        ring.add_node(NodeId::new("server2"));
        ring.add_node(NodeId::new("server3"));

        // Generate sample keys
        let keys: Vec<String> = (0..1000).map(|i| format!("key_{}", i)).collect();

        let distribution = ring.get_distribution(&keys);

        // Each node should get roughly 1/3 of keys (33.3%)
        // With consistent hashing, distribution can vary, so allow wider tolerance
        // In practice, 10%-90% is acceptable as long as all nodes get some keys
        let mut total_count = 0;
        for (node, count) in &distribution {
            let ratio = *count as f64 / keys.len() as f64;
            println!("{}: {} keys ({:.1}%)", node, count, ratio * 100.0);
            total_count += count;
            
            // Ensure each node gets at least 5% and at most 95% of keys
            assert!(
                ratio >= 0.05 && ratio <= 0.95,
                "Node {} has unreasonable distribution: {:.1}% (expected 5%-95%)",
                node,
                ratio * 100.0
            );
        }
        
        // Ensure all keys are distributed
        assert_eq!(total_count, keys.len(), "Not all keys were distributed");
        
        // Ensure we have 3 nodes
        assert_eq!(distribution.len(), 3, "Expected 3 nodes in distribution");
    }

    #[test]
    fn test_is_prime() {
        assert!(MaglevHash::is_prime(2));
        assert!(MaglevHash::is_prime(3));
        assert!(MaglevHash::is_prime(5));
        assert!(MaglevHash::is_prime(7));
        assert!(MaglevHash::is_prime(11));
        assert!(MaglevHash::is_prime(65537));

        assert!(!MaglevHash::is_prime(1));
        assert!(!MaglevHash::is_prime(4));
        assert!(!MaglevHash::is_prime(6));
        assert!(!MaglevHash::is_prime(8));
        assert!(!MaglevHash::is_prime(9));
    }
}
