// Vector Clock Implementation
//
// Implements vector clocks for tracking causality in distributed systems.
// Enables detection of concurrent events and causal relationships.

use crate::error_handling::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

/// Node identifier in the vector clock
pub type NodeId = String;

/// Comparison result for vector clocks
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClockOrdering {
    /// This clock happened before the other
    Before,
    /// This clock happened after the other
    After,
    /// Clocks are concurrent (neither happened before the other)
    Concurrent,
    /// Clocks are equal
    Equal,
}

/// Vector clock for tracking causality
///
/// A vector clock is a data structure used for determining the partial ordering
/// of events in a distributed system and detecting causality violations.
///
/// # Example
/// ```ignore
/// let mut clock1 = VectorClock::new("node1".to_string());
/// clock1.increment();  // [node1: 1]
///
/// let mut clock2 = VectorClock::new("node2".to_string());
/// clock2.increment();  // [node2: 1]
///
/// // These events are concurrent
/// assert_eq!(clock1.compare(&clock2), ClockOrdering::Concurrent);
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VectorClock {
    /// The node that owns this clock
    node_id: NodeId,
    /// Vector of logical timestamps: node_id -> counter
    vector: HashMap<NodeId, u64>,
}

impl VectorClock {
    /// Create a new vector clock for a node
    pub fn new(node_id: NodeId) -> Self {
        let mut vector = HashMap::new();
        vector.insert(node_id.clone(), 0);

        Self { node_id, vector }
    }

    /// Get the node ID
    pub fn node_id(&self) -> &str {
        &self.node_id
    }

    /// Get the current timestamp for this node
    pub fn get_time(&self) -> u64 {
        *self.vector.get(&self.node_id).unwrap_or(&0)
    }

    /// Get the timestamp for a specific node
    pub fn get_node_time(&self, node_id: &str) -> u64 {
        *self.vector.get(node_id).unwrap_or(&0)
    }

    /// Increment the clock (on local event)
    ///
    /// Call this when a local event occurs (e.g., sending a message, processing a request)
    pub fn increment(&mut self) {
        let counter = self.vector.entry(self.node_id.clone()).or_insert(0);
        *counter += 1;
    }

    /// Merge with another vector clock (on message receive)
    ///
    /// Updates this clock to reflect that an event occurred after the event
    /// represented by `other`. This is typically called when receiving a message.
    ///
    /// The merge operation:
    /// - Takes the maximum of each component
    /// - Increments the local clock
    pub fn merge(&mut self, other: &VectorClock) {
        // Take max of each component
        for (node_id, &timestamp) in &other.vector {
            let entry = self.vector.entry(node_id.clone()).or_insert(0);
            *entry = (*entry).max(timestamp);
        }

        // Increment local clock
        self.increment();
    }

    /// Compare this clock with another to determine causality
    ///
    /// Returns:
    /// - `Before` if this clock happened before `other`
    /// - `After` if this clock happened after `other`
    /// - `Concurrent` if events are concurrent
    /// - `Equal` if clocks are identical
    pub fn compare(&self, other: &VectorClock) -> ClockOrdering {
        let mut less_than = false;
        let mut greater_than = false;

        // Get all unique node IDs from both clocks
        let mut all_nodes: Vec<&NodeId> = self.vector.keys().collect();
        for node_id in other.vector.keys() {
            if !all_nodes.contains(&node_id) {
                all_nodes.push(node_id);
            }
        }

        // Compare each component
        for node_id in all_nodes {
            let self_time = self.vector.get(node_id).copied().unwrap_or(0);
            let other_time = other.vector.get(node_id).copied().unwrap_or(0);

            if self_time < other_time {
                less_than = true;
            } else if self_time > other_time {
                greater_than = true;
            }
        }

        match (less_than, greater_than) {
            (false, false) => ClockOrdering::Equal,
            (true, false) => ClockOrdering::Before,
            (false, true) => ClockOrdering::After,
            (true, true) => ClockOrdering::Concurrent,
        }
    }

    /// Check if this clock happened before another
    pub fn happens_before(&self, other: &VectorClock) -> bool {
        matches!(self.compare(other), ClockOrdering::Before)
    }

    /// Check if this clock happened after another
    pub fn happens_after(&self, other: &VectorClock) -> bool {
        matches!(self.compare(other), ClockOrdering::After)
    }

    /// Check if two events are concurrent
    pub fn is_concurrent(&self, other: &VectorClock) -> bool {
        matches!(self.compare(other), ClockOrdering::Concurrent)
    }

    /// Check if this clock is equal to another
    pub fn is_equal(&self, other: &VectorClock) -> bool {
        matches!(self.compare(other), ClockOrdering::Equal)
    }

    /// Detect if there's a conflict between two clocks
    ///
    /// Returns true if clocks are concurrent, indicating a potential conflict
    pub fn has_conflict(&self, other: &VectorClock) -> bool {
        self.is_concurrent(other)
    }

    /// Get a copy of the internal vector
    pub fn get_vector(&self) -> HashMap<NodeId, u64> {
        self.vector.clone()
    }

    /// Get the size (number of nodes) in the vector
    pub fn size(&self) -> usize {
        self.vector.len()
    }

    /// Create a snapshot of the current clock
    pub fn snapshot(&self) -> VectorClockSnapshot {
        VectorClockSnapshot {
            vector: self.vector.clone(),
        }
    }

    /// Reset the clock to initial state
    pub fn reset(&mut self) {
        self.vector.clear();
        self.vector.insert(self.node_id.clone(), 0);
    }
}

impl fmt::Display for VectorClock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "VectorClock[")?;
        let mut first = true;
        let mut sorted: Vec<_> = self.vector.iter().collect();
        sorted.sort_by_key(|(k, _)| *k);

        for (node_id, timestamp) in sorted {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", node_id, timestamp)?;
            first = false;
        }
        write!(f, "]")
    }
}

impl PartialEq for VectorClock {
    fn eq(&self, other: &Self) -> bool {
        self.is_equal(other)
    }
}

impl Eq for VectorClock {}

/// Snapshot of a vector clock (immutable view)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VectorClockSnapshot {
    vector: HashMap<NodeId, u64>,
}

impl VectorClockSnapshot {
    /// Get the timestamp for a specific node
    pub fn get_node_time(&self, node_id: &str) -> u64 {
        *self.vector.get(node_id).unwrap_or(&0)
    }

    /// Get all timestamps
    pub fn get_all(&self) -> &HashMap<NodeId, u64> {
        &self.vector
    }
}

/// Builder for creating vector clocks with specific initial states
pub struct VectorClockBuilder {
    node_id: NodeId,
    vector: HashMap<NodeId, u64>,
}

impl VectorClockBuilder {
    pub fn new(node_id: NodeId) -> Self {
        Self {
            node_id,
            vector: HashMap::new(),
        }
    }

    pub fn with_time(mut self, node_id: NodeId, time: u64) -> Self {
        self.vector.insert(node_id, time);
        self
    }

    pub fn build(mut self) -> VectorClock {
        // Ensure the owner node is in the vector
        self.vector.entry(self.node_id.clone()).or_insert(0);

        VectorClock {
            node_id: self.node_id,
            vector: self.vector,
        }
    }
}

/// Utility for tracking causality across multiple operations
pub struct CausalityTracker {
    clocks: HashMap<NodeId, VectorClock>,
}

impl CausalityTracker {
    pub fn new() -> Self {
        Self {
            clocks: HashMap::new(),
        }
    }

    /// Register a new node
    pub fn register_node(&mut self, node_id: NodeId) {
        self.clocks
            .entry(node_id.clone())
            .or_insert_with(|| VectorClock::new(node_id));
    }

    /// Record a local event for a node
    pub fn record_event(&mut self, node_id: &str) -> Result<()> {
        let clock = self.clocks.get_mut(node_id).ok_or_else(|| {
            UnifiedError::new(
                format!("Node {} not registered", node_id),
                ErrorSeverity::Medium,
                "vector_clock",
                ErrorContext::new(
                    "vector_clock",
                    "record_event",
                    file!(),
                    line!(),
                    ErrorSeverity::Medium,
                    "vector_clock",
                ),
            )
        })?;

        clock.increment();
        Ok(())
    }

    /// Record a message send from sender to receiver
    #[allow(dead_code)]
    #[allow(unused_variables)]
    pub fn record_send(
        &mut self,
        sender: &str,
        receiver: &str,
    ) -> Result<VectorClockSnapshot> {
        // Increment sender's clock
        self.record_event(sender)?;

        // Get snapshot to send with message
        let snapshot = self
            .clocks
            .get(sender)
            .ok_or_else(|| {
                UnifiedError::new(
                    format!("Sender {} not registered", sender),
                    ErrorSeverity::Medium,
                    "vector_clock",
                    ErrorContext::new(
                        "vector_clock",
                        "record_send",
                        file!(),
                        line!(),
                        ErrorSeverity::Medium,
                        "vector_clock",
                    ),
                )
            })?
            .snapshot();

        Ok(snapshot)
    }

    /// Record a message receive at receiver from snapshot
    #[allow(dead_code)]
    #[allow(unused_variables)]
    pub fn record_receive(&mut self, receiver: &str, snapshot: &VectorClockSnapshot) -> Result<()> {
        let receiver_clock = self.clocks.get_mut(receiver).ok_or_else(|| {
            UnifiedError::new(
                format!("Receiver {} not registered", receiver),
                ErrorSeverity::Medium,
                "vector_clock",
                ErrorContext::new(
                    "vector_clock",
                    "record_receive",
                    file!(),
                    line!(),
                    ErrorSeverity::Medium,
                    "vector_clock",
                ),
            )
        })?;

        // Merge with received snapshot
        let temp_clock = VectorClock {
            node_id: receiver.to_string(),
            vector: snapshot.vector.clone(),
        };
        receiver_clock.merge(&temp_clock);

        Ok(())
    }

    /// Get the clock for a node
    pub fn get_clock(&self, node_id: &str) -> Option<&VectorClock> {
        self.clocks.get(node_id)
    }

    /// Check if event A happened before event B
    pub fn happened_before(&self, node_a: &str, node_b: &str) -> Result<bool> {
        let clock_a = self.clocks.get(node_a).ok_or_else(|| {
            UnifiedError::new(
                format!("Node {} not found", node_a),
                ErrorSeverity::Medium,
                "vector_clock",
                ErrorContext::new(
                    "vector_clock",
                    "happened_before",
                    file!(),
                    line!(),
                    ErrorSeverity::Medium,
                    "vector_clock",
                ),
            )
        })?;

        let clock_b = self.clocks.get(node_b).ok_or_else(|| {
            UnifiedError::new(
                format!("Node {} not found", node_b),
                ErrorSeverity::Medium,
                "vector_clock",
                ErrorContext::new(
                    "vector_clock",
                    "happened_before",
                    file!(),
                    line!(),
                    ErrorSeverity::Medium,
                    "vector_clock",
                ),
            )
        })?;

        Ok(clock_a.happens_before(clock_b))
    }
}

impl Default for CausalityTracker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vector_clock_creation() {
        let clock = VectorClock::new("node1".to_string());
        assert_eq!(clock.get_time(), 0);
        assert_eq!(clock.node_id(), "node1");
    }

    #[test]
    fn test_increment() {
        let mut clock = VectorClock::new("node1".to_string());
        clock.increment();
        assert_eq!(clock.get_time(), 1);

        clock.increment();
        assert_eq!(clock.get_time(), 2);
    }

    #[test]
    fn test_merge() {
        let mut clock1 = VectorClock::new("node1".to_string());
        clock1.increment(); // [node1: 1]

        let mut clock2 = VectorClock::new("node2".to_string());
        clock2.increment(); // [node2: 1]

        clock1.merge(&clock2); // [node1: 2, node2: 1]

        assert_eq!(clock1.get_time(), 2);
        assert_eq!(clock1.get_node_time("node2"), 1);
    }

    #[test]
    fn test_happens_before() {
        let mut clock1 = VectorClock::new("node1".to_string());
        clock1.increment(); // [node1: 1]

        let mut clock2 = VectorClock::new("node1".to_string());
        clock2.increment(); // [node1: 1]
        clock2.increment(); // [node1: 2]

        assert_eq!(clock1.compare(&clock2), ClockOrdering::Before);
        assert!(clock1.happens_before(&clock2));
        assert!(!clock2.happens_before(&clock1));
    }

    #[test]
    fn test_concurrent_events() {
        let mut clock1 = VectorClock::new("node1".to_string());
        clock1.increment(); // [node1: 1]

        let mut clock2 = VectorClock::new("node2".to_string());
        clock2.increment(); // [node2: 1]

        assert_eq!(clock1.compare(&clock2), ClockOrdering::Concurrent);
        assert!(clock1.is_concurrent(&clock2));
        assert!(clock1.has_conflict(&clock2));
    }

    #[test]
    fn test_equal_clocks() {
        let mut clock1 = VectorClock::new("node1".to_string());
        clock1.increment();

        let mut clock2 = VectorClock::new("node1".to_string());
        clock2.increment();

        assert_eq!(clock1.compare(&clock2), ClockOrdering::Equal);
        assert!(clock1.is_equal(&clock2));
    }

    #[test]
    fn test_message_passing_scenario() {
        // Node 1 sends a message
        let mut clock1 = VectorClock::new("node1".to_string());
        clock1.increment(); // Event: send message
        let snapshot = clock1.snapshot();

        // Node 2 receives and processes
        let mut clock2 = VectorClock::new("node2".to_string());
        let temp = VectorClock {
            node_id: "node2".to_string(),
            vector: snapshot.get_all().clone(),
        };
        clock2.merge(&temp); // Event: receive message

        // clock1 should happen before clock2
        assert!(clock1.happens_before(&clock2));
        assert!(!clock1.is_concurrent(&clock2));
    }

    #[test]
    fn test_causality_tracker() {
        let mut tracker = CausalityTracker::new();

        tracker.register_node("node1".to_string());
        tracker.register_node("node2".to_string());

        // Node 1 sends to Node 2
        let snapshot = tracker.record_send("node1", "node2").unwrap();
        tracker.record_receive("node2", &snapshot).unwrap();

        // Node 1's event should happen before Node 2's event
        assert!(tracker.happened_before("node1", "node2").unwrap());
    }

    #[test]
    fn test_builder() {
        let clock = VectorClockBuilder::new("node1".to_string())
            .with_time("node1".to_string(), 5)
            .with_time("node2".to_string(), 3)
            .build();

        assert_eq!(clock.get_time(), 5);
        assert_eq!(clock.get_node_time("node2"), 3);
    }

    #[test]
    fn test_display() {
        let mut clock = VectorClock::new("node1".to_string());
        clock.increment();
        clock.vector.insert("node2".to_string(), 2);

        let display = format!("{}", clock);
        assert!(display.contains("node1: 1"));
        assert!(display.contains("node2: 2"));
    }
}
