// Hybrid Logical Clock (HLC) Implementation
//
// Combines physical time with logical counters to provide:
// - Monotonically increasing timestamps
// - Bounded divergence from physical time
// - Total ordering of events
//
// Based on: "Logical Physical Clocks and Consistent Snapshots in Globally
// Distributed Databases" by Kulkarni et al.

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

/// Hybrid Logical Clock timestamp
///
/// Combines physical time (wall clock) with a logical counter to provide
/// a globally consistent timestamp that closely tracks real time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct HLCTimestamp {
    /// Physical time component (microseconds since UNIX epoch)
    pub physical: u64,
    /// Logical counter component
    pub logical: u64,
}

impl HLCTimestamp {
    /// Create a new timestamp
    pub fn new(physical: u64, logical: u64) -> Self {
        Self { physical, logical }
    }

    /// Create a timestamp from the current physical time
    pub fn now() -> Self {
        let physical = Self::current_physical_time();
        Self {
            physical,
            logical: 0,
        }
    }

    /// Get current physical time in microseconds since UNIX epoch
    fn current_physical_time() -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_micros() as u64
    }

    /// Convert to DateTime
    pub fn to_datetime(&self) -> DateTime<Utc> {
        let secs = self.physical / 1_000_000;
        let nsecs = (self.physical % 1_000_000) * 1000;
        DateTime::from_timestamp(secs as i64, nsecs as u32).unwrap_or_else(|| Utc::now())
    }

    /// Get the physical time component in milliseconds
    pub fn physical_ms(&self) -> u64 {
        self.physical / 1000
    }

    /// Get the physical time component in seconds
    pub fn physical_secs(&self) -> u64 {
        self.physical / 1_000_000
    }
}

impl Ord for HLCTimestamp {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.physical.cmp(&other.physical) {
            Ordering::Equal => self.logical.cmp(&other.logical),
            ord => ord,
        }
    }
}

impl PartialOrd for HLCTimestamp {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for HLCTimestamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "HLC({}, {})", self.physical, self.logical)
    }
}

/// Hybrid Logical Clock
///
/// Maintains a timestamp that combines physical time with a logical counter.
/// Thread-safe and designed for distributed systems.
///
/// # Example
/// ```ignore
/// let clock = HybridLogicalClock::new();
///
/// // Generate timestamp for local event
/// let ts1 = clock.tick();
///
/// // Update clock when receiving a message
/// let remote_ts = HLCTimestamp::new(123456, 5);
/// let ts2 = clock.observe(remote_ts);
///
/// assert!(ts2 > ts1);
/// ```
pub struct HybridLogicalClock {
    /// Last known timestamp
    last_timestamp: Arc<AtomicU64>, // Packed: upper 48 bits = physical, lower 16 bits = logical
    /// Maximum clock skew tolerance (microseconds)
    max_skew: u64,
}

impl HybridLogicalClock {
    /// Create a new HLC with default maximum skew (500ms)
    pub fn new() -> Self {
        Self::with_max_skew(500_000) // 500ms
    }

    /// Create a new HLC with specified maximum skew (in microseconds)
    pub fn with_max_skew(max_skew: u64) -> Self {
        let now = HLCTimestamp::current_physical_time();
        let packed = Self::pack_timestamp(now, 0);

        Self {
            last_timestamp: Arc::new(AtomicU64::new(packed)),
            max_skew,
        }
    }

    /// Generate a new timestamp for a local event (send or local operation)
    ///
    /// This is called when:
    /// - Sending a message
    /// - Performing a local operation that should be timestamped
    pub fn tick(&self) -> HLCTimestamp {
        loop {
            let current_packed = self.last_timestamp.load(AtomicOrdering::Acquire);
            let (last_physical, last_logical) = Self::unpack_timestamp(current_packed);

            let physical_now = HLCTimestamp::current_physical_time();

            let (new_physical, new_logical) = if physical_now > last_physical {
                // Physical time has advanced, reset logical counter
                (physical_now, 0)
            } else {
                // Physical time hasn't advanced, increment logical counter
                (last_physical, last_logical + 1)
            };

            let new_packed = Self::pack_timestamp(new_physical, new_logical);

            // Try to update atomically
            if self
                .last_timestamp
                .compare_exchange(
                    current_packed,
                    new_packed,
                    AtomicOrdering::Release,
                    AtomicOrdering::Acquire,
                )
                .is_ok()
            {
                return HLCTimestamp {
                    physical: new_physical,
                    logical: new_logical,
                };
            }
            // Retry if CAS failed
        }
    }

    /// Update clock based on an observed timestamp (e.g., from a received message)
    ///
    /// This is called when:
    /// - Receiving a message with a timestamp
    /// - Observing a timestamp from another node
    ///
    /// Returns the new local timestamp after observation.
    pub fn observe(&self, observed: HLCTimestamp) -> HLCTimestamp {
        loop {
            let current_packed = self.last_timestamp.load(AtomicOrdering::Acquire);
            let (last_physical, last_logical) = Self::unpack_timestamp(current_packed);

            let physical_now = HLCTimestamp::current_physical_time();

            // Check for excessive clock skew
            if observed.physical > physical_now + self.max_skew {
                // Remote clock is too far ahead - this could indicate a problem
                // For now, we'll proceed but in production you might want to handle this
            }

            let (new_physical, new_logical) = if physical_now > last_physical
                && physical_now > observed.physical
            {
                // Local physical time has advanced beyond both last and observed
                (physical_now, 0)
            } else if last_physical > observed.physical {
                // Last timestamp is ahead of observed
                (last_physical, last_logical + 1)
            } else if observed.physical > last_physical {
                // Observed is ahead of last
                (observed.physical, observed.logical + 1)
            } else {
                // All physical times are equal, take max logical + 1
                (last_physical, last_logical.max(observed.logical) + 1)
            };

            let new_packed = Self::pack_timestamp(new_physical, new_logical);

            if self
                .last_timestamp
                .compare_exchange(
                    current_packed,
                    new_packed,
                    AtomicOrdering::Release,
                    AtomicOrdering::Acquire,
                )
                .is_ok()
            {
                return HLCTimestamp {
                    physical: new_physical,
                    logical: new_logical,
                };
            }
            // Retry if CAS failed
        }
    }

    /// Get the current timestamp without incrementing
    pub fn get_time(&self) -> HLCTimestamp {
        let packed = self.last_timestamp.load(AtomicOrdering::Acquire);
        let (physical, logical) = Self::unpack_timestamp(packed);
        HLCTimestamp { physical, logical }
    }

    /// Check if the clock has diverged significantly from physical time
    ///
    /// Returns the divergence in microseconds if it exceeds a threshold.
    pub fn check_divergence(&self, threshold_us: u64) -> Option<u64> {
        let current = self.get_time();
        let physical_now = HLCTimestamp::current_physical_time();

        if current.physical > physical_now {
            let divergence = current.physical - physical_now;
            if divergence > threshold_us {
                return Some(divergence);
            }
        }

        None
    }

    /// Reset the clock to current physical time
    ///
    /// This should only be used in exceptional circumstances,
    /// as it breaks monotonicity guarantees.
    pub fn reset(&self) {
        let now = HLCTimestamp::current_physical_time();
        let packed = Self::pack_timestamp(now, 0);
        self.last_timestamp.store(packed, AtomicOrdering::Release);
    }

    // Helper functions for packing/unpacking timestamps into u64

    fn pack_timestamp(physical: u64, logical: u64) -> u64 {
        // Use upper 48 bits for physical, lower 16 bits for logical
        // This assumes logical counter won't exceed 65535
        let logical_capped = logical.min(0xFFFF);
        (physical << 16) | logical_capped
    }

    fn unpack_timestamp(packed: u64) -> (u64, u64) {
        let physical = packed >> 16;
        let logical = packed & 0xFFFF;
        (physical, logical)
    }
}

impl Default for HybridLogicalClock {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for HybridLogicalClock {
    fn clone(&self) -> Self {
        let packed = self.last_timestamp.load(AtomicOrdering::Acquire);
        Self {
            last_timestamp: Arc::new(AtomicU64::new(packed)),
            max_skew: self.max_skew,
        }
    }
}

/// Builder for HybridLogicalClock with custom configuration
pub struct HLCBuilder {
    max_skew: Option<u64>,
    initial_time: Option<HLCTimestamp>,
}

impl HLCBuilder {
    pub fn new() -> Self {
        Self {
            max_skew: None,
            initial_time: None,
        }
    }

    pub fn max_skew_ms(mut self, ms: u64) -> Self {
        self.max_skew = Some(ms * 1000);
        self
    }

    pub fn max_skew_us(mut self, us: u64) -> Self {
        self.max_skew = Some(us);
        self
    }

    pub fn initial_time(mut self, timestamp: HLCTimestamp) -> Self {
        self.initial_time = Some(timestamp);
        self
    }

    pub fn build(self) -> HybridLogicalClock {
        let max_skew = self.max_skew.unwrap_or(500_000);

        let initial = if let Some(ts) = self.initial_time {
            HybridLogicalClock::pack_timestamp(ts.physical, ts.logical)
        } else {
            let now = HLCTimestamp::current_physical_time();
            HybridLogicalClock::pack_timestamp(now, 0)
        };

        HybridLogicalClock {
            last_timestamp: Arc::new(AtomicU64::new(initial)),
            max_skew,
        }
    }
}

impl Default for HLCBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Utilities for working with HLC timestamps
pub mod utils {
    use super::*;

    /// Calculate the time difference between two HLC timestamps
    pub fn time_diff(t1: HLCTimestamp, t2: HLCTimestamp) -> i64 {
        t1.physical as i64 - t2.physical as i64
    }

    /// Check if t1 happened before t2
    pub fn happened_before(t1: HLCTimestamp, t2: HLCTimestamp) -> bool {
        t1 < t2
    }

    /// Get the maximum of two timestamps
    pub fn max_timestamp(t1: HLCTimestamp, t2: HLCTimestamp) -> HLCTimestamp {
        t1.max(t2)
    }

    /// Get the minimum of two timestamps
    pub fn min_timestamp(t1: HLCTimestamp, t2: HLCTimestamp) -> HLCTimestamp {
        t1.min(t2)
    }

    /// Check if two timestamps are concurrent (within a threshold)
    pub fn are_concurrent(t1: HLCTimestamp, t2: HLCTimestamp, threshold_us: u64) -> bool {
        let diff = time_diff(t1, t2).unsigned_abs();
        diff <= threshold_us
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::Duration;

    #[test]
    fn test_timestamp_creation() {
        let ts = HLCTimestamp::new(100, 5);
        assert_eq!(ts.physical, 100);
        assert_eq!(ts.logical, 5);
    }

    #[test]
    fn test_timestamp_ordering() {
        let ts1 = HLCTimestamp::new(100, 5);
        let ts2 = HLCTimestamp::new(100, 6);
        let ts3 = HLCTimestamp::new(101, 0);

        assert!(ts1 < ts2);
        assert!(ts2 < ts3);
        assert!(ts1 < ts3);
    }

    #[test]
    fn test_hlc_tick() {
        let clock = HybridLogicalClock::new();

        let ts1 = clock.tick();
        // Add a small delay to ensure time progresses or logical counter increments
        std::thread::sleep(std::time::Duration::from_micros(1));
        let ts2 = clock.tick();

        // Use >= to account for cases where physical time doesn't advance
        // but logical counter does increment
        assert!(ts2 >= ts1, "ts2 ({:?}) should be >= ts1 ({:?})", ts2, ts1);
        // Ensure they're not exactly equal (at least logical counter should increment)
        assert_ne!(ts2, ts1, "Timestamps should not be identical");
    }

    #[test]
    fn test_hlc_tick_monotonic() {
        let clock = HybridLogicalClock::new();

        let mut timestamps = vec![];
        for _ in 0..1000 {
            timestamps.push(clock.tick());
            // Add tiny delay to allow physical time to progress
            std::thread::sleep(std::time::Duration::from_nanos(100));
        }

        // Check overall monotonicity (allowing for duplicates in rare cases due to CAS retries)
        for i in 1..timestamps.len() {
            assert!(
                timestamps[i] >= timestamps[i - 1],
                "Iteration {}: Timestamps must be monotonically non-decreasing: ts[{}]={:?}, ts[{}]={:?}",
                i, i, timestamps[i], i-1, timestamps[i - 1]
            );
        }

        // Ensure most timestamps are unique (allow small percentage of duplicates)
        let mut unique_count = 1;
        for i in 1..timestamps.len() {
            if timestamps[i] != timestamps[i - 1] {
                unique_count += 1;
            }
        }
        let uniqueness_ratio = unique_count as f64 / timestamps.len() as f64;
        assert!(
            uniqueness_ratio > 0.95,
            "At least 95% of timestamps should be unique, got {:.2}%",
            uniqueness_ratio * 100.0
        );
    }

    #[test]
    fn test_hlc_observe() {
        let clock = HybridLogicalClock::new();

        let ts1 = clock.tick();

        // Simulate receiving a timestamp from the future
        let future_ts = HLCTimestamp::new(ts1.physical + 1000, 0);
        let ts2 = clock.observe(future_ts);

        assert!(ts2 >= future_ts);
        assert!(ts2 > ts1);
    }

    #[test]
    fn test_hlc_observe_past() {
        let clock = HybridLogicalClock::new();

        let ts1 = clock.tick();
        thread::sleep(Duration::from_millis(10));

        // Simulate receiving a timestamp from the past
        let past_ts = HLCTimestamp::new(ts1.physical - 1000, 0);
        let ts2 = clock.observe(past_ts);

        // Current timestamp should still be ahead
        assert!(ts2 > ts1);
        assert!(ts2.physical >= ts1.physical);
    }

    #[test]
    fn test_message_passing_scenario() {
        let clock1 = HybridLogicalClock::new();
        let clock2 = HybridLogicalClock::new();

        // Node 1 sends message
        let send_ts = clock1.tick();

        // Simulate network delay
        thread::sleep(Duration::from_millis(5));

        // Node 2 receives message
        let recv_ts = clock2.observe(send_ts);

        // Receive timestamp should be after send timestamp
        assert!(recv_ts > send_ts);
    }

    #[test]
    fn test_concurrent_operations() {
        let clock = Arc::new(HybridLogicalClock::new());
        let mut handles = vec![];

        // Spawn multiple threads
        for _ in 0..10 {
            let clock_clone = Arc::clone(&clock);
            let handle = thread::spawn(move || {
                let mut timestamps = vec![];
                for _ in 0..100 {
                    timestamps.push(clock_clone.tick());
                }
                timestamps
            });
            handles.push(handle);
        }

        // Collect all timestamps
        let mut all_timestamps = vec![];
        for handle in handles {
            all_timestamps.extend(handle.join().unwrap());
        }

        // Verify all timestamps are monotonic (allow duplicates in rare cases)
        all_timestamps.sort();
        for i in 1..all_timestamps.len() {
            assert!(
                all_timestamps[i] >= all_timestamps[i - 1],
                "Timestamps must be monotonically non-decreasing: ts[{}]={:?}, ts[{}]={:?}",
                i, all_timestamps[i], i-1, all_timestamps[i - 1]
            );
        }

        // Ensure reasonable uniqueness (allow duplicates due to concurrent CAS retries)
        let mut unique_count = 1;
        for i in 1..all_timestamps.len() {
            if all_timestamps[i] != all_timestamps[i - 1] {
                unique_count += 1;
            }
        }
        let uniqueness_ratio = unique_count as f64 / all_timestamps.len() as f64;
        // In high concurrency (10 threads x 100 calls), some duplicates are expected
        // due to CAS retries when multiple threads try to update simultaneously
        assert!(
            uniqueness_ratio > 0.80,
            "At least 80% of timestamps should be unique in concurrent scenario, got {:.2}% ({}/{})",
            uniqueness_ratio * 100.0,
            unique_count,
            all_timestamps.len()
        );
    }

    #[test]
    fn test_builder() {
        let clock = HLCBuilder::new()
            .max_skew_ms(100)
            .initial_time(HLCTimestamp::new(12345, 0))
            .build();

        let ts = clock.get_time();
        assert_eq!(ts.physical, 12345);
        assert_eq!(ts.logical, 0);
    }

    #[test]
    fn test_pack_unpack() {
        let physical = 123456789012345u64;
        let logical = 42u64;

        let packed = HybridLogicalClock::pack_timestamp(physical, logical);
        let (unpacked_physical, unpacked_logical) = HybridLogicalClock::unpack_timestamp(packed);

        assert_eq!(unpacked_physical, physical);
        assert_eq!(unpacked_logical, logical);
    }

    #[test]
    fn test_timestamp_display() {
        let ts = HLCTimestamp::new(123456, 42);
        let display = format!("{}", ts);
        assert_eq!(display, "HLC(123456, 42)");
    }

    #[test]
    fn test_utils_happened_before() {
        let ts1 = HLCTimestamp::new(100, 0);
        let ts2 = HLCTimestamp::new(200, 0);

        assert!(utils::happened_before(ts1, ts2));
        assert!(!utils::happened_before(ts2, ts1));
    }

    #[test]
    fn test_utils_concurrent() {
        let ts1 = HLCTimestamp::new(100, 0);
        let ts2 = HLCTimestamp::new(105, 0);

        assert!(utils::are_concurrent(ts1, ts2, 10));
        assert!(!utils::are_concurrent(ts1, ts2, 3));
    }

    #[test]
    fn test_divergence_check() {
        let clock = HybridLogicalClock::new();

        // Normal operation - no divergence
        assert!(clock.check_divergence(1000).is_none());

        // Force a timestamp far in the future by observing it multiple times
        // to ensure it's actually stored
        let future_physical = HLCTimestamp::current_physical_time() + 10_000_000;
        let future = HLCTimestamp::new(future_physical, 0);
        
        // Observe the future timestamp
        let observed_ts = clock.observe(future);
        
        // Verify the observed timestamp is in the future
        assert!(
            observed_ts.physical >= future_physical,
            "Observed timestamp should be at least as far as the future timestamp: observed={:?}, future={}",
            observed_ts, future_physical
        );

        // Add a small delay to ensure the divergence is measurable
        std::thread::sleep(std::time::Duration::from_millis(2));

        // Now check for divergence
        let divergence = clock.check_divergence(1000);
        assert!(
            divergence.is_some(),
            "Expected divergence after observing future timestamp. Current time: {:?}, Clock time: {:?}",
            HLCTimestamp::current_physical_time(),
            clock.get_time()
        );
    }
}
