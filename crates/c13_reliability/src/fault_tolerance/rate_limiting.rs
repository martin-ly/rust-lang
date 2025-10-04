// Rate Limiting Algorithms
//
// Implements various rate limiting algorithms for controlling request rates:
// - Token Bucket: Allows bursts while maintaining average rate
// - Leaky Bucket: Smooths out bursts with constant output rate
// - Fixed Window: Simple time-window based limiting
// - Sliding Window: More accurate than fixed window
// - Sliding Window Log: Most accurate but more memory intensive

use crate::error_handling::prelude::*;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::Mutex;
use parking_lot::RwLock;

/// Rate limiter trait
#[async_trait::async_trait]
pub trait RateLimiter: Send + Sync {
    /// Try to acquire permission to proceed
    async fn try_acquire(&self) -> bool;

    /// Wait until permission is granted
    async fn acquire(&self) -> Result<()>;

    /// Get current rate limit
    fn rate(&self) -> u64;

    /// Get current usage statistics
    fn stats(&self) -> RateLimiterStats;
}

/// Rate limiter statistics
#[derive(Debug, Clone)]
pub struct RateLimiterStats {
    pub total_requests: u64,
    pub allowed_requests: u64,
    pub rejected_requests: u64,
    pub current_tokens: f64,
    pub capacity: u64,
}

impl RateLimiterStats {
    pub fn acceptance_rate(&self) -> f64 {
        if self.total_requests == 0 {
            1.0
        } else {
            self.allowed_requests as f64 / self.total_requests as f64
        }
    }

    pub fn rejection_rate(&self) -> f64 {
        1.0 - self.acceptance_rate()
    }
}

/// Token Bucket Rate Limiter
///
/// Allows bursts up to capacity while maintaining average rate.
/// Best for: APIs that can handle occasional bursts
///
/// # Example
/// ```ignore
/// let limiter = TokenBucket::new(100, Duration::from_secs(1)); // 100 req/sec
/// if limiter.try_acquire().await {
///     // Process request
/// } else {
///     // Reject request (rate limited)
/// }
/// ```
pub struct TokenBucket {
    capacity: u64,
    tokens: Arc<Mutex<f64>>,
    refill_rate: f64, // tokens per millisecond
    last_refill: Arc<Mutex<Instant>>,
    stats: Arc<RwLock<RateLimiterStats>>,
}

impl TokenBucket {
    /// Create a new token bucket
    ///
    /// * `capacity` - Maximum number of tokens (burst size)
    /// * `refill_period` - Time to fully refill the bucket
    pub fn new(capacity: u64, refill_period: Duration) -> Self {
        let refill_rate = capacity as f64 / refill_period.as_millis() as f64;

        Self {
            capacity,
            tokens: Arc::new(Mutex::new(capacity as f64)),
            refill_rate,
            last_refill: Arc::new(Mutex::new(Instant::now())),
            stats: Arc::new(RwLock::new(RateLimiterStats {
                total_requests: 0,
                allowed_requests: 0,
                rejected_requests: 0,
                current_tokens: capacity as f64,
                capacity,
            })),
        }
    }

    /// Create with rate per second
    pub fn per_second(rate: u64) -> Self {
        Self::new(rate, Duration::from_secs(1))
    }

    /// Create with rate per minute
    pub fn per_minute(rate: u64) -> Self {
        Self::new(rate, Duration::from_secs(60))
    }

    async fn refill(&self) {
        let now = Instant::now();
        let mut last_refill = self.last_refill.lock().await;
        let elapsed = now.duration_since(*last_refill);

        let tokens_to_add = elapsed.as_millis() as f64 * self.refill_rate;

        if tokens_to_add > 0.0 {
            let mut tokens = self.tokens.lock().await;
            *tokens = (*tokens + tokens_to_add).min(self.capacity as f64);
            *last_refill = now;

            // Update stats
            let mut stats = self.stats.write();
            stats.current_tokens = *tokens;
        }
    }
}

#[async_trait::async_trait]
impl RateLimiter for TokenBucket {
    async fn try_acquire(&self) -> bool {
        self.refill().await;

        let mut tokens = self.tokens.lock().await;
        let mut stats = self.stats.write();
        stats.total_requests += 1;

        if *tokens >= 1.0 {
            *tokens -= 1.0;
            stats.allowed_requests += 1;
            stats.current_tokens = *tokens;
            true
        } else {
            stats.rejected_requests += 1;
            false
        }
    }

    async fn acquire(&self) -> Result<()> {
        loop {
            if self.try_acquire().await {
                return Ok(());
            }
            // Wait a bit before retrying
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }

    fn rate(&self) -> u64 {
        self.capacity
    }

    fn stats(&self) -> RateLimiterStats {
        self.stats.read().clone()
    }
}

/// Leaky Bucket Rate Limiter
///
/// Processes requests at a constant rate, smoothing out bursts.
/// Best for: Systems that need steady output rate
///
/// # Example
/// ```ignore
/// let limiter = LeakyBucket::new(10, Duration::from_secs(1)); // 10 req/sec
/// limiter.acquire().await?; // Will wait if bucket is full
/// ```
pub struct LeakyBucket {
    capacity: u64,
    queue: Arc<Mutex<Vec<Instant>>>,
    leak_rate: Duration, // time between leaks
    last_leak: Arc<Mutex<Instant>>,
    stats: Arc<RwLock<RateLimiterStats>>,
}

impl LeakyBucket {
    /// Create a new leaky bucket
    pub fn new(capacity: u64, leak_period: Duration) -> Self {
        let leak_rate = Duration::from_millis(leak_period.as_millis() as u64 / capacity.max(1));

        Self {
            capacity,
            queue: Arc::new(Mutex::new(Vec::new())),
            leak_rate,
            last_leak: Arc::new(Mutex::new(Instant::now())),
            stats: Arc::new(RwLock::new(RateLimiterStats {
                total_requests: 0,
                allowed_requests: 0,
                rejected_requests: 0,
                current_tokens: capacity as f64,
                capacity,
            })),
        }
    }

    pub fn per_second(rate: u64) -> Self {
        Self::new(rate, Duration::from_secs(1))
    }

    async fn leak(&self) {
        let now = Instant::now();
        let mut last_leak = self.last_leak.lock().await;
        let elapsed = now.duration_since(*last_leak);

        let leaks = elapsed.as_millis() / self.leak_rate.as_millis();

        if leaks > 0 {
            let mut queue = self.queue.lock().await;
            let to_remove = leaks.min(queue.len() as u128) as usize;
            queue.drain(0..to_remove);
            *last_leak = now;

            // Update stats
            let mut stats = self.stats.write();
            stats.current_tokens = (self.capacity - queue.len() as u64) as f64;
        }
    }
}

#[async_trait::async_trait]
impl RateLimiter for LeakyBucket {
    async fn try_acquire(&self) -> bool {
        self.leak().await;

        let mut queue = self.queue.lock().await;
        let mut stats = self.stats.write();
        stats.total_requests += 1;

        if queue.len() < self.capacity as usize {
            queue.push(Instant::now());
            stats.allowed_requests += 1;
            stats.current_tokens = (self.capacity - queue.len() as u64) as f64;
            true
        } else {
            stats.rejected_requests += 1;
            false
        }
    }

    async fn acquire(&self) -> Result<()> {
        loop {
            if self.try_acquire().await {
                return Ok(());
            }
            tokio::time::sleep(self.leak_rate).await;
        }
    }

    fn rate(&self) -> u64 {
        self.capacity
    }

    fn stats(&self) -> RateLimiterStats {
        self.stats.read().clone()
    }
}

/// Fixed Window Rate Limiter
///
/// Simple time-window based limiting. May allow 2x rate at window boundaries.
/// Best for: Simple use cases where precision isn't critical
pub struct FixedWindow {
    max_requests: u64,
    window_size: Duration,
    current_count: Arc<Mutex<u64>>,
    window_start: Arc<Mutex<Instant>>,
    stats: Arc<RwLock<RateLimiterStats>>,
}

impl FixedWindow {
    pub fn new(max_requests: u64, window_size: Duration) -> Self {
        Self {
            max_requests,
            window_size,
            current_count: Arc::new(Mutex::new(0)),
            window_start: Arc::new(Mutex::new(Instant::now())),
            stats: Arc::new(RwLock::new(RateLimiterStats {
                total_requests: 0,
                allowed_requests: 0,
                rejected_requests: 0,
                current_tokens: max_requests as f64,
                capacity: max_requests,
            })),
        }
    }

    pub fn per_second(rate: u64) -> Self {
        Self::new(rate, Duration::from_secs(1))
    }

    async fn reset_if_needed(&self) {
        let now = Instant::now();
        let mut window_start = self.window_start.lock().await;
        let elapsed = now.duration_since(*window_start);

        if elapsed >= self.window_size {
            *window_start = now;
            let mut count = self.current_count.lock().await;
            *count = 0;

            let mut stats = self.stats.write();
            stats.current_tokens = self.max_requests as f64;
        }
    }
}

#[async_trait::async_trait]
impl RateLimiter for FixedWindow {
    async fn try_acquire(&self) -> bool {
        self.reset_if_needed().await;

        let mut count = self.current_count.lock().await;
        let mut stats = self.stats.write();
        stats.total_requests += 1;

        if *count < self.max_requests {
            *count += 1;
            stats.allowed_requests += 1;
            stats.current_tokens = (self.max_requests - *count) as f64;
            true
        } else {
            stats.rejected_requests += 1;
            false
        }
    }

    async fn acquire(&self) -> Result<()> {
        loop {
            if self.try_acquire().await {
                return Ok(());
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    }

    fn rate(&self) -> u64 {
        self.max_requests
    }

    fn stats(&self) -> RateLimiterStats {
        self.stats.read().clone()
    }
}

/// Sliding Window Rate Limiter
///
/// More accurate than fixed window, uses weighted count.
/// Best for: When you need better accuracy than fixed window
pub struct SlidingWindow {
    max_requests: u64,
    window_size: Duration,
    previous_count: Arc<Mutex<u64>>,
    current_count: Arc<Mutex<u64>>,
    window_start: Arc<Mutex<Instant>>,
    stats: Arc<RwLock<RateLimiterStats>>,
}

impl SlidingWindow {
    pub fn new(max_requests: u64, window_size: Duration) -> Self {
        Self {
            max_requests,
            window_size,
            previous_count: Arc::new(Mutex::new(0)),
            current_count: Arc::new(Mutex::new(0)),
            window_start: Arc::new(Mutex::new(Instant::now())),
            stats: Arc::new(RwLock::new(RateLimiterStats {
                total_requests: 0,
                allowed_requests: 0,
                rejected_requests: 0,
                current_tokens: max_requests as f64,
                capacity: max_requests,
            })),
        }
    }

    pub fn per_second(rate: u64) -> Self {
        Self::new(rate, Duration::from_secs(1))
    }

    async fn roll_window_if_needed(&self) {
        let now = Instant::now();
        let mut window_start = self.window_start.lock().await;
        let elapsed = now.duration_since(*window_start);

        if elapsed >= self.window_size {
            *window_start = now;
            let mut previous = self.previous_count.lock().await;
            let mut current = self.current_count.lock().await;
            *previous = *current;
            *current = 0;
        }
    }

    async fn weighted_count(&self) -> u64 {
        let now = Instant::now();
        let window_start = self.window_start.lock().await;
        let elapsed = now.duration_since(*window_start);
        let progress = elapsed.as_secs_f64() / self.window_size.as_secs_f64();

        let previous = *self.previous_count.lock().await;
        let current = *self.current_count.lock().await;

        ((1.0 - progress) * previous as f64 + current as f64) as u64
    }
}

#[async_trait::async_trait]
impl RateLimiter for SlidingWindow {
    async fn try_acquire(&self) -> bool {
        self.roll_window_if_needed().await;

        let weighted = self.weighted_count().await;
        
        {
            let mut stats = self.stats.write();
            stats.total_requests += 1;
        }

        if weighted < self.max_requests {
            let mut current = self.current_count.lock().await;
            *current += 1;
            {
                let mut stats = self.stats.write();
                stats.allowed_requests += 1;
                stats.current_tokens = (self.max_requests - weighted - 1) as f64;
            }
            true
        } else {
            {
                let mut stats = self.stats.write();
                stats.rejected_requests += 1;
            }
            false
        }
    }

    async fn acquire(&self) -> Result<()> {
        loop {
            if self.try_acquire().await {
                return Ok(());
            }
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    }

    fn rate(&self) -> u64 {
        self.max_requests
    }

    fn stats(&self) -> RateLimiterStats {
        self.stats.read().clone()
    }
}

/// Sliding Window Log Rate Limiter
///
/// Most accurate algorithm, keeps log of all timestamps.
/// Best for: When accuracy is critical and memory isn't a concern
pub struct SlidingWindowLog {
    max_requests: u64,
    window_size: Duration,
    log: Arc<Mutex<Vec<Instant>>>,
    stats: Arc<RwLock<RateLimiterStats>>,
}

impl SlidingWindowLog {
    pub fn new(max_requests: u64, window_size: Duration) -> Self {
        Self {
            max_requests,
            window_size,
            log: Arc::new(Mutex::new(Vec::new())),
            stats: Arc::new(RwLock::new(RateLimiterStats {
                total_requests: 0,
                allowed_requests: 0,
                rejected_requests: 0,
                current_tokens: max_requests as f64,
                capacity: max_requests,
            })),
        }
    }

    pub fn per_second(rate: u64) -> Self {
        Self::new(rate, Duration::from_secs(1))
    }

    async fn clean_old_entries(&self) {
        let now = Instant::now();
        let mut log = self.log.lock().await;

        // Remove entries older than window
        log.retain(|&timestamp| {
            now.duration_since(timestamp) < self.window_size
        });

        let mut stats = self.stats.write();
        stats.current_tokens = (self.max_requests - log.len() as u64) as f64;
    }
}

#[async_trait::async_trait]
impl RateLimiter for SlidingWindowLog {
    async fn try_acquire(&self) -> bool {
        self.clean_old_entries().await;

        let mut log = self.log.lock().await;
        
        {
            let mut stats = self.stats.write();
            stats.total_requests += 1;
        }

        if log.len() < self.max_requests as usize {
            log.push(Instant::now());
            let log_len = log.len();
            drop(log); // 提前释放 Mutex
            
            {
                let mut stats = self.stats.write();
                stats.allowed_requests += 1;
                stats.current_tokens = (self.max_requests - log_len as u64) as f64;
            }
            true
        } else {
            drop(log); // 提前释放 Mutex
            
            {
                let mut stats = self.stats.write();
                stats.rejected_requests += 1;
            }
            false
        }
    }

    async fn acquire(&self) -> Result<()> {
        loop {
            if self.try_acquire().await {
                return Ok(());
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }

    fn rate(&self) -> u64 {
        self.max_requests
    }

    fn stats(&self) -> RateLimiterStats {
        self.stats.read().clone()
    }
}

/// Rate limiter builder for convenient construction
pub struct RateLimiterBuilder {
    algorithm: RateLimiterAlgorithm,
    rate: u64,
    period: Duration,
}

#[derive(Debug, Clone, Copy)]
pub enum RateLimiterAlgorithm {
    TokenBucket,
    LeakyBucket,
    FixedWindow,
    SlidingWindow,
    SlidingWindowLog,
}

impl RateLimiterBuilder {
    pub fn new(algorithm: RateLimiterAlgorithm) -> Self {
        Self {
            algorithm,
            rate: 100,
            period: Duration::from_secs(1),
        }
    }

    pub fn rate(mut self, rate: u64) -> Self {
        self.rate = rate;
        self
    }

    pub fn per_second(mut self, rate: u64) -> Self {
        self.rate = rate;
        self.period = Duration::from_secs(1);
        self
    }

    pub fn per_minute(mut self, rate: u64) -> Self {
        self.rate = rate;
        self.period = Duration::from_secs(60);
        self
    }

    pub fn period(mut self, period: Duration) -> Self {
        self.period = period;
        self
    }

    pub fn build(self) -> Arc<dyn RateLimiter> {
        match self.algorithm {
            RateLimiterAlgorithm::TokenBucket => {
                Arc::new(TokenBucket::new(self.rate, self.period))
            }
            RateLimiterAlgorithm::LeakyBucket => {
                Arc::new(LeakyBucket::new(self.rate, self.period))
            }
            RateLimiterAlgorithm::FixedWindow => {
                Arc::new(FixedWindow::new(self.rate, self.period))
            }
            RateLimiterAlgorithm::SlidingWindow => {
                Arc::new(SlidingWindow::new(self.rate, self.period))
            }
            RateLimiterAlgorithm::SlidingWindowLog => {
                Arc::new(SlidingWindowLog::new(self.rate, self.period))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::time::sleep;

    #[tokio::test]
    async fn test_token_bucket_basic() {
        let limiter = TokenBucket::per_second(10);

        // Should allow first 10 requests
        for _ in 0..10 {
            assert!(limiter.try_acquire().await);
        }

        // Should reject 11th request
        assert!(!limiter.try_acquire().await);
    }

    #[tokio::test]
    async fn test_token_bucket_refill() {
        let limiter = TokenBucket::new(5, Duration::from_millis(100));

        // Exhaust tokens
        for _ in 0..5 {
            assert!(limiter.try_acquire().await);
        }
        assert!(!limiter.try_acquire().await);

        // Wait for refill
        sleep(Duration::from_millis(150)).await;

        // Should work again
        assert!(limiter.try_acquire().await);
    }

    #[tokio::test]
    async fn test_leaky_bucket() {
        let limiter = LeakyBucket::per_second(10);

        // Should allow up to capacity
        for _ in 0..10 {
            assert!(limiter.try_acquire().await);
        }

        // Should reject when full
        assert!(!limiter.try_acquire().await);
    }

    #[tokio::test]
    async fn test_fixed_window() {
        let limiter = FixedWindow::per_second(5);

        for _ in 0..5 {
            assert!(limiter.try_acquire().await);
        }

        assert!(!limiter.try_acquire().await);

        // Wait for window to reset
        sleep(Duration::from_secs(1)).await;

        assert!(limiter.try_acquire().await);
    }

    #[tokio::test]
    async fn test_sliding_window() {
        let limiter = SlidingWindow::per_second(10);

        for _ in 0..10 {
            assert!(limiter.try_acquire().await);
        }

        assert!(!limiter.try_acquire().await);
    }

    #[tokio::test]
    async fn test_sliding_window_log() {
        let limiter = SlidingWindowLog::new(5, Duration::from_millis(100));

        for _ in 0..5 {
            assert!(limiter.try_acquire().await);
        }

        assert!(!limiter.try_acquire().await);

        // Wait for window to slide
        sleep(Duration::from_millis(150)).await;

        assert!(limiter.try_acquire().await);
    }

    #[tokio::test]
    async fn test_builder() {
        let limiter = RateLimiterBuilder::new(RateLimiterAlgorithm::TokenBucket)
            .per_second(100)
            .build();

        assert!(limiter.try_acquire().await);
        assert_eq!(limiter.rate(), 100);
    }

    #[tokio::test]
    async fn test_stats() {
        let limiter = TokenBucket::per_second(5);

        for _ in 0..3 {
            limiter.try_acquire().await;
        }

        let stats = limiter.stats();
        assert_eq!(stats.total_requests, 3);
        assert_eq!(stats.allowed_requests, 3);
        assert_eq!(stats.rejected_requests, 0);
    }

    #[tokio::test]
    async fn test_acquire_blocking() {
        let limiter = TokenBucket::new(1, Duration::from_millis(50));

        // First acquire should work immediately
        limiter.acquire().await.unwrap();

        // Second acquire should wait for refill
        let start = Instant::now();
        limiter.acquire().await.unwrap();
        let elapsed = start.elapsed();

        assert!(elapsed >= Duration::from_millis(40));
    }
}

