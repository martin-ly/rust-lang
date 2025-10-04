//! 舱壁模式实现
//!
//! 提供资源隔离和限制功能，防止一个组件的故障影响整个系统。

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;
use serde::{Serialize, Deserialize};
use tracing::{debug, warn};

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

/// 舱壁配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BulkheadConfig {
    /// 最大并发请求数
    pub max_concurrent_requests: u64,
    /// 最大等待时间
    pub max_wait_time: Duration,
    /// 是否启用舱壁
    pub enabled: bool,
    /// 舱壁名称
    pub name: String,
}

impl Default for BulkheadConfig {
    fn default() -> Self {
        Self {
            max_concurrent_requests: 10,
            max_wait_time: Duration::from_secs(30),
            enabled: true,
            name: "default".to_string(),
        }
    }
}

/// 舱壁状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BulkheadState {
    /// 当前活跃请求数
    pub active_requests: u64,
    /// 最大并发请求数
    pub max_concurrent_requests: u64,
    /// 可用容量
    pub available_capacity: u64,
    /// 利用率
    pub utilization: f64,
}

/// 舱壁统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BulkheadStats {
    /// 总请求数
    pub total_requests: u64,
    /// 接受的请求数
    pub accepted_requests: u64,
    /// 拒绝的请求数
    pub rejected_requests: u64,
    /// 当前活跃请求数
    pub active_requests: u64,
    /// 最大并发请求数
    pub max_concurrent_requests: u64,
    /// 平均等待时间
    pub average_wait_time: Duration,
    /// 最后更新时间
    pub last_updated: chrono::DateTime<chrono::Utc>,
}

impl Default for BulkheadStats {
    fn default() -> Self {
        Self {
            total_requests: 0,
            accepted_requests: 0,
            rejected_requests: 0,
            active_requests: 0,
            max_concurrent_requests: 0,
            average_wait_time: Duration::ZERO,
            last_updated: chrono::Utc::now(),
        }
    }
}

/// 舱壁许可
#[derive(Debug)]
#[allow(dead_code)]
pub struct BulkheadPermit {
    bulkhead: Arc<Bulkhead>,
    acquired_at: std::time::Instant,
}

impl Drop for BulkheadPermit {
    fn drop(&mut self) {
        self.bulkhead.release_permit();
    }
}

/// 舱壁实现
#[derive(Debug)]
#[allow(dead_code)]
pub struct Bulkhead {
    config: BulkheadConfig,
    active_requests: AtomicU64,
    total_requests: AtomicU64,
    accepted_requests: AtomicU64,
    rejected_requests: AtomicU64,
    total_wait_time: AtomicU64,
    stats: std::sync::Mutex<BulkheadStats>,
}

impl Bulkhead {
    /// 创建新的舱壁
    pub fn new(config: BulkheadConfig) -> Self {
        Self {
            config,
            active_requests: AtomicU64::new(0),
            total_requests: AtomicU64::new(0),
            accepted_requests: AtomicU64::new(0),
            rejected_requests: AtomicU64::new(0),
            total_wait_time: AtomicU64::new(0),
            stats: std::sync::Mutex::new(BulkheadStats::default()),
        }
    }

    /// 获取舱壁许可
    pub async fn acquire(&self) -> Result<BulkheadPermit, UnifiedError> {
        if !self.config.enabled {
            return Ok(BulkheadPermit {
                bulkhead: Arc::new(self.clone()),
                acquired_at: std::time::Instant::now(),
            });
        }

        let start_time = std::time::Instant::now();
        self.total_requests.fetch_add(1, Ordering::Relaxed);

        // 尝试获取许可
        loop {
            let current_active = self.active_requests.load(Ordering::Relaxed);
            
            if current_active < self.config.max_concurrent_requests {
                // 尝试原子性地增加活跃请求数
                if self.active_requests.compare_exchange_weak(
                    current_active,
                    current_active + 1,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ).is_ok() {
                    // 成功获取许可
                    self.accepted_requests.fetch_add(1, Ordering::Relaxed);
                    let wait_time = start_time.elapsed();
                    self.total_wait_time.fetch_add(wait_time.as_millis() as u64, Ordering::Relaxed);
                    
                    debug!("舱壁 {} 获取许可成功，当前活跃请求数: {}", 
                           self.config.name, current_active + 1);
                    
                    self.update_stats();
                    
                    return Ok(BulkheadPermit {
                        bulkhead: Arc::new(self.clone()),
                        acquired_at: start_time,
                    });
                }
            } else {
                // 检查是否超过最大等待时间
                if start_time.elapsed() >= self.config.max_wait_time {
                    self.rejected_requests.fetch_add(1, Ordering::Relaxed);
                    self.update_stats();
                    
                    warn!("舱壁 {} 请求被拒绝，超过最大等待时间", self.config.name);
                    
                    return Err(self.create_bulkhead_rejected_error());
                }
                
                // 等待一小段时间后重试
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }
    }

    /// 释放舱壁许可
    fn release_permit(&self) {
        let current_active = self.active_requests.fetch_sub(1, Ordering::Relaxed);
        debug!("舱壁 {} 释放许可，当前活跃请求数: {}", 
               self.config.name, current_active - 1);
        self.update_stats();
    }

    /// 创建舱壁拒绝错误
    fn create_bulkhead_rejected_error(&self) -> UnifiedError {
        let context = ErrorContext::new(
            "bulkhead",
            "acquire",
            file!(),
            line!(),
            ErrorSeverity::High,
            "bulkhead"
        );

        UnifiedError::new(
            &format!("舱壁 {} 请求被拒绝，资源不足", self.config.name),
            ErrorSeverity::High,
            "bulkhead_rejected",
            context
        ).with_code("BH_001")
        .with_suggestion("等待资源释放或增加舱壁容量")
    }

    /// 获取当前状态
    pub fn state(&self) -> BulkheadState {
        let active = self.active_requests.load(Ordering::Relaxed);
        let max = self.config.max_concurrent_requests;
        let available = max.saturating_sub(active);
        let utilization = if max > 0 {
            active as f64 / max as f64
        } else {
            0.0
        };

        BulkheadState {
            active_requests: active,
            max_concurrent_requests: max,
            available_capacity: available,
            utilization,
        }
    }

    /// 更新统计信息
    fn update_stats(&self) {
        let mut stats = self.stats.lock().unwrap();
        stats.total_requests = self.total_requests.load(Ordering::Relaxed);
        stats.accepted_requests = self.accepted_requests.load(Ordering::Relaxed);
        stats.rejected_requests = self.rejected_requests.load(Ordering::Relaxed);
        stats.active_requests = self.active_requests.load(Ordering::Relaxed);
        stats.max_concurrent_requests = self.config.max_concurrent_requests;
        
        if stats.accepted_requests > 0 {
            let total_wait_ms = self.total_wait_time.load(Ordering::Relaxed);
            stats.average_wait_time = Duration::from_millis(total_wait_ms / stats.accepted_requests);
        } else {
            stats.average_wait_time = Duration::ZERO;
        }
        
        stats.last_updated = chrono::Utc::now();
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> BulkheadStats {
        // Return current stats with updated values from atomic counters
        BulkheadStats {
            total_requests: self.total_requests.load(Ordering::Relaxed),
            accepted_requests: self.accepted_requests.load(Ordering::Relaxed),
            rejected_requests: self.rejected_requests.load(Ordering::Relaxed),
            active_requests: self.active_requests.load(Ordering::Relaxed),
            max_concurrent_requests: self.config.max_concurrent_requests,
            average_wait_time: {
                let total_wait = self.total_wait_time.load(Ordering::Relaxed);
                let total = self.total_requests.load(Ordering::Relaxed);
                if total > 0 {
                    Duration::from_nanos(total_wait / total)
                } else {
                    Duration::ZERO
                }
            },
            last_updated: chrono::Utc::now(),
        }
    }

    /// 重置统计信息
    pub fn reset_stats(&self) {
        self.total_requests.store(0, Ordering::Relaxed);
        self.accepted_requests.store(0, Ordering::Relaxed);
        self.rejected_requests.store(0, Ordering::Relaxed);
        self.total_wait_time.store(0, Ordering::Relaxed);
        
        let mut stats = self.stats.lock().unwrap();
        *stats = BulkheadStats::default();
    }

    /// 获取配置
    pub fn get_config(&self) -> &BulkheadConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: BulkheadConfig) {
        self.config = config;
    }

    /// 检查是否有可用容量
    pub fn has_capacity(&self) -> bool {
        if !self.config.enabled {
            return true;
        }
        
        self.active_requests.load(Ordering::Relaxed) < self.config.max_concurrent_requests
    }

    /// 获取可用容量
    pub fn available_capacity(&self) -> u64 {
        if !self.config.enabled {
            return u64::MAX;
        }
        
        let active = self.active_requests.load(Ordering::Relaxed);
        self.config.max_concurrent_requests.saturating_sub(active)
    }
}

impl Clone for Bulkhead {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            active_requests: AtomicU64::new(self.active_requests.load(Ordering::Relaxed)),
            total_requests: AtomicU64::new(self.total_requests.load(Ordering::Relaxed)),
            accepted_requests: AtomicU64::new(self.accepted_requests.load(Ordering::Relaxed)),
            rejected_requests: AtomicU64::new(self.rejected_requests.load(Ordering::Relaxed)),
            total_wait_time: AtomicU64::new(self.total_wait_time.load(Ordering::Relaxed)),
            stats: std::sync::Mutex::new(self.stats.lock().unwrap().clone()),
        }
    }
}

/// 舱壁构建器
pub struct BulkheadBuilder {
    config: BulkheadConfig,
}

impl BulkheadBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: BulkheadConfig::default(),
        }
    }

    /// 设置最大并发请求数
    pub fn max_concurrent_requests(mut self, max_requests: u64) -> Self {
        self.config.max_concurrent_requests = max_requests;
        self
    }

    /// 设置最大等待时间
    pub fn max_wait_time(mut self, wait_time: Duration) -> Self {
        self.config.max_wait_time = wait_time;
        self
    }

    /// 设置舱壁名称
    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.config.name = name.into();
        self
    }

    /// 启用或禁用舱壁
    pub fn enabled(mut self, enabled: bool) -> Self {
        self.config.enabled = enabled;
        self
    }

    /// 构建舱壁
    pub fn build(self) -> Bulkhead {
        Bulkhead::new(self.config)
    }
}

impl Default for BulkheadBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_bulkhead_config_default() {
        let config = BulkheadConfig::default();
        assert_eq!(config.max_concurrent_requests, 10);
        assert_eq!(config.max_wait_time, Duration::from_secs(30));
        assert!(config.enabled);
        assert_eq!(config.name, "default");
    }

    #[test]
    fn test_bulkhead_creation() {
        let bulkhead = Bulkhead::new(BulkheadConfig::default());
        assert!(bulkhead.has_capacity());
        assert_eq!(bulkhead.available_capacity(), 10);
    }

    #[test]
    fn test_bulkhead_builder() {
        let bulkhead = BulkheadBuilder::new()
            .max_concurrent_requests(5)
            .max_wait_time(Duration::from_secs(10))
            .name("test_bulkhead")
            .enabled(true)
            .build();

        let config = bulkhead.get_config();
        assert_eq!(config.max_concurrent_requests, 5);
        assert_eq!(config.max_wait_time, Duration::from_secs(10));
        assert_eq!(config.name, "test_bulkhead");
        assert!(config.enabled);
    }

    #[tokio::test]
    async fn test_bulkhead_acquire_success() {
        let bulkhead = Bulkhead::new(BulkheadConfig::default());
        
        let permit = bulkhead.acquire().await;
        assert!(permit.is_ok());
        
        let state = bulkhead.state();
        assert_eq!(state.active_requests, 1);
        assert_eq!(state.available_capacity, 9);
        assert_eq!(state.utilization, 0.1);
    }

    #[tokio::test]
    async fn test_bulkhead_acquire_reject() {
        let config = BulkheadConfig {
            max_concurrent_requests: 1,
            max_wait_time: Duration::from_millis(100),
            ..Default::default()
        };
        let bulkhead = Bulkhead::new(config);
        
        // 获取第一个许可
        let _permit1 = bulkhead.acquire().await.unwrap();
        
        // 尝试获取第二个许可，应该被拒绝
        let permit2 = bulkhead.acquire().await;
        assert!(permit2.is_err());
        
        let error = permit2.unwrap_err();
        assert!(error.message().contains("舱壁"));
        assert!(error.message().contains("请求被拒绝"));
    }

    #[tokio::test]
    async fn test_bulkhead_permit_drop() {
        let bulkhead = Arc::new(Bulkhead::new(BulkheadConfig::default()));
        
        {
            let permit = bulkhead.acquire().await.unwrap();
            let state = bulkhead.state();
            assert_eq!(state.active_requests, 1);
            // Explicitly drop the permit
            drop(permit);
        }
        
        // Yield to allow drop to complete
        tokio::task::yield_now().await;
        
        // Wait for the drop to complete with retry mechanism
        // Drop should be immediate, but in async context might need a yield
        let mut attempts = 0;
        loop {
            let state = bulkhead.state();
            if state.active_requests == 0 {
                break;
            }
            
            attempts += 1;
            if attempts > 10 {
                panic!(
                    "Active requests should be 0 after permit drop, but got {} after {} attempts",
                    state.active_requests, attempts
                );
            }
            
            tokio::task::yield_now().await;
            tokio::time::sleep(tokio::time::Duration::from_millis(5)).await;
        }
        
        // 许可被释放
        let state = bulkhead.state();
        assert_eq!(state.active_requests, 0);
        assert_eq!(state.available_capacity, 10);
    }

    #[test]
    fn test_bulkhead_state() {
        let bulkhead = Bulkhead::new(BulkheadConfig::default());
        let state = bulkhead.state();
        
        assert_eq!(state.active_requests, 0);
        assert_eq!(state.max_concurrent_requests, 10);
        assert_eq!(state.available_capacity, 10);
        assert_eq!(state.utilization, 0.0);
    }

    #[test]
    fn test_bulkhead_stats() {
        let bulkhead = Bulkhead::new(BulkheadConfig::default());
        let stats = bulkhead.get_stats();
        
        assert_eq!(stats.total_requests, 0);
        assert_eq!(stats.accepted_requests, 0);
        assert_eq!(stats.rejected_requests, 0);
        assert_eq!(stats.active_requests, 0);
        assert_eq!(stats.max_concurrent_requests, 10);
        assert_eq!(stats.average_wait_time, Duration::ZERO);
    }

    #[test]
    fn test_bulkhead_reset() {
        let bulkhead = Bulkhead::new(BulkheadConfig::default());
        
        // 重置统计
        bulkhead.reset_stats();
        
        let stats = bulkhead.get_stats();
        assert_eq!(stats.total_requests, 0);
        assert_eq!(stats.accepted_requests, 0);
        assert_eq!(stats.rejected_requests, 0);
    }

    #[test]
    fn test_bulkhead_disabled() {
        let config = BulkheadConfig {
            enabled: false,
            ..Default::default()
        };
        let bulkhead = Bulkhead::new(config);
        
        assert!(bulkhead.has_capacity());
        assert_eq!(bulkhead.available_capacity(), u64::MAX);
    }
}
