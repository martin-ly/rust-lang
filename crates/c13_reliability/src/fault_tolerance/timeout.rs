//! 超时处理实现
//!
//! 提供操作超时控制功能，防止长时间阻塞。

use std::time::Duration;
use std::sync::{Arc, atomic::{AtomicU64, Ordering}};
use serde::{Serialize, Deserialize};
use tracing::warn;

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

/// 超时配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeoutConfig {
    /// 超时时间
    pub duration: Duration,
    /// 是否启用超时
    pub enabled: bool,
    /// 超时名称
    pub name: String,
}

impl Default for TimeoutConfig {
    fn default() -> Self {
        Self {
            duration: Duration::from_secs(30),
            enabled: true,
            name: "default".to_string(),
        }
    }
}

/// 超时统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeoutStats {
    /// 总请求数
    pub total_requests: u64,
    /// 超时请求数
    pub timed_out_requests: u64,
    /// 成功请求数
    pub successful_requests: u64,
    /// 平均执行时间
    pub average_execution_time: Duration,
    /// 最大执行时间
    pub max_execution_time: Duration,
    /// 最后更新时间
    pub last_updated: chrono::DateTime<chrono::Utc>,
}

impl Default for TimeoutStats {
    fn default() -> Self {
        Self {
            total_requests: 0,
            timed_out_requests: 0,
            successful_requests: 0,
            average_execution_time: Duration::ZERO,
            max_execution_time: Duration::ZERO,
            last_updated: chrono::Utc::now(),
        }
    }
}

/// 超时实现
pub struct Timeout {
    config: TimeoutConfig,
    total_requests: AtomicU64,
    timed_out_requests: AtomicU64,
    successful_requests: AtomicU64,
    total_execution_time: AtomicU64,
    max_execution_time: AtomicU64,
    stats: std::sync::Mutex<TimeoutStats>,
}

impl Timeout {
    /// 创建新的超时处理器
    pub fn new(config: TimeoutConfig) -> Self {
        Self {
            config,
            total_requests: AtomicU64::new(0),
            timed_out_requests: AtomicU64::new(0),
            successful_requests: AtomicU64::new(0),
            total_execution_time: AtomicU64::new(0),
            max_execution_time: AtomicU64::new(0),
            stats: std::sync::Mutex::new(TimeoutStats::default()),
        }
    }

    /// 执行带超时的操作
    pub async fn execute<T, F, Fut>(&self, operation: F) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        if !self.config.enabled {
            return operation().await;
        }

        self.total_requests.fetch_add(1, Ordering::Relaxed);
        let start_time = std::time::Instant::now();

        match tokio::time::timeout(self.config.duration, operation()).await {
            Ok(result) => {
                let execution_time = start_time.elapsed();
                self.record_success(execution_time);
                result
            }
            Err(_) => {
                let execution_time = start_time.elapsed();
                self.record_timeout(execution_time);
                Err(self.create_timeout_error())
            }
        }
    }

    /// 记录成功请求
    fn record_success(&self, execution_time: Duration) {
        self.successful_requests.fetch_add(1, Ordering::Relaxed);
        self.total_execution_time.fetch_add(execution_time.as_millis() as u64, Ordering::Relaxed);
        
        // 更新最大执行时间
        let current_max = self.max_execution_time.load(Ordering::Relaxed);
        let new_max = execution_time.as_millis() as u64;
        if new_max > current_max {
            self.max_execution_time.store(new_max, Ordering::Relaxed);
        }
        
        self.update_stats();
    }

    /// 记录超时请求
    fn record_timeout(&self, execution_time: Duration) {
        self.timed_out_requests.fetch_add(1, Ordering::Relaxed);
        self.total_execution_time.fetch_add(execution_time.as_millis() as u64, Ordering::Relaxed);
        
        // 更新最大执行时间
        let current_max = self.max_execution_time.load(Ordering::Relaxed);
        let new_max = execution_time.as_millis() as u64;
        if new_max > current_max {
            self.max_execution_time.store(new_max, Ordering::Relaxed);
        }
        
        self.update_stats();
        
        warn!("操作超时: {}，执行时间: {:?}", self.config.name, execution_time);
    }

    /// 创建超时错误
    fn create_timeout_error(&self) -> UnifiedError {
        let context = ErrorContext::new(
            "timeout",
            "execute",
            file!(),
            line!(),
            ErrorSeverity::High,
            "timeout"
        );

        UnifiedError::new(
            &format!("操作 {} 超时，超时时间: {:?}", self.config.name, self.config.duration),
            ErrorSeverity::High,
            "timeout",
            context
        ).with_code("TO_001")
        .with_suggestion("增加超时时间或优化操作性能")
    }

    /// 更新统计信息
    fn update_stats(&self) {
        let mut stats = self.stats.lock().unwrap();
        stats.total_requests = self.total_requests.load(Ordering::Relaxed);
        stats.timed_out_requests = self.timed_out_requests.load(Ordering::Relaxed);
        stats.successful_requests = self.successful_requests.load(Ordering::Relaxed);
        stats.max_execution_time = Duration::from_millis(self.max_execution_time.load(Ordering::Relaxed));
        
        if stats.total_requests > 0 {
            let total_time_ms = self.total_execution_time.load(Ordering::Relaxed);
            stats.average_execution_time = Duration::from_millis(total_time_ms / stats.total_requests);
        } else {
            stats.average_execution_time = Duration::ZERO;
        }
        
        stats.last_updated = chrono::Utc::now();
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> TimeoutStats {
        self.stats.lock().unwrap().clone()
    }

    /// 重置统计信息
    pub fn reset_stats(&self) {
        self.total_requests.store(0, Ordering::Relaxed);
        self.timed_out_requests.store(0, Ordering::Relaxed);
        self.successful_requests.store(0, Ordering::Relaxed);
        self.total_execution_time.store(0, Ordering::Relaxed);
        self.max_execution_time.store(0, Ordering::Relaxed);
        
        let mut stats = self.stats.lock().unwrap();
        *stats = TimeoutStats::default();
    }

    /// 获取配置
    pub fn get_config(&self) -> &TimeoutConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: TimeoutConfig) {
        self.config = config;
    }

    /// 获取超时时间
    pub fn get_timeout(&self) -> Duration {
        self.config.duration
    }

    /// 设置超时时间
    pub fn set_timeout(&mut self, duration: Duration) {
        self.config.duration = duration;
    }

    /// 检查是否启用超时
    pub fn is_enabled(&self) -> bool {
        self.config.enabled
    }

    /// 启用或禁用超时
    pub fn set_enabled(&mut self, enabled: bool) {
        self.config.enabled = enabled;
    }
}

/// 超时构建器
pub struct TimeoutBuilder {
    config: TimeoutConfig,
}

impl TimeoutBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: TimeoutConfig::default(),
        }
    }

    /// 设置超时时间
    pub fn duration(mut self, duration: Duration) -> Self {
        self.config.duration = duration;
        self
    }

    /// 设置超时名称
    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.config.name = name.into();
        self
    }

    /// 启用或禁用超时
    pub fn enabled(mut self, enabled: bool) -> Self {
        self.config.enabled = enabled;
        self
    }

    /// 构建超时处理器
    pub fn build(self) -> Timeout {
        Timeout::new(self.config)
    }
}

impl Default for TimeoutBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// 超时监控器
pub struct TimeoutMonitor {
    timeouts: std::sync::Mutex<std::collections::HashMap<String, Arc<Timeout>>>,
    global_stats: std::sync::Mutex<TimeoutStats>,
}

impl TimeoutMonitor {
    /// 创建新的超时监控器
    pub fn new() -> Self {
        Self {
            timeouts: std::sync::Mutex::new(std::collections::HashMap::new()),
            global_stats: std::sync::Mutex::new(TimeoutStats::default()),
        }
    }

    /// 注册超时处理器
    pub fn register_timeout(&self, name: String, timeout: Arc<Timeout>) {
        let mut timeouts = self.timeouts.lock().unwrap();
        timeouts.insert(name, timeout);
    }

    /// 获取超时处理器
    pub fn get_timeout(&self, name: &str) -> Option<Arc<Timeout>> {
        let timeouts = self.timeouts.lock().unwrap();
        timeouts.get(name).cloned()
    }

    /// 获取全局统计信息
    pub fn get_global_stats(&self) -> TimeoutStats {
        let mut global_stats = self.global_stats.lock().unwrap().clone();
        
        // 聚合所有超时处理器的统计信息
        let timeouts = self.timeouts.lock().unwrap();
        for timeout in timeouts.values() {
            let stats = timeout.get_stats();
            global_stats.total_requests += stats.total_requests;
            global_stats.timed_out_requests += stats.timed_out_requests;
            global_stats.successful_requests += stats.successful_requests;
            
            if stats.max_execution_time > global_stats.max_execution_time {
                global_stats.max_execution_time = stats.max_execution_time;
            }
        }
        
        // 重新计算平均执行时间
        if global_stats.total_requests > 0 {
            let total_time = timeouts.values()
                .map(|t| t.get_stats().average_execution_time.as_millis() as u64 * t.get_stats().total_requests)
                .sum::<u64>();
            global_stats.average_execution_time = Duration::from_millis(total_time / global_stats.total_requests);
        }
        
        global_stats
    }

    /// 生成监控报告
    pub fn generate_report(&self) -> String {
        let stats = self.get_global_stats();
        let mut report = String::new();

        report.push_str("=== 超时监控报告 ===\n\n");
        report.push_str(&format!("总请求数: {}\n", stats.total_requests));
        report.push_str(&format!("超时请求数: {}\n", stats.timed_out_requests));
        report.push_str(&format!("成功请求数: {}\n", stats.successful_requests));
        report.push_str(&format!("超时率: {:.2}%\n", 
            if stats.total_requests > 0 {
                stats.timed_out_requests as f64 / stats.total_requests as f64 * 100.0
            } else {
                0.0
            }
        ));
        report.push_str(&format!("平均执行时间: {:?}\n", stats.average_execution_time));
        report.push_str(&format!("最大执行时间: {:?}\n", stats.max_execution_time));

        report
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_timeout_config_default() {
        let config = TimeoutConfig::default();
        assert_eq!(config.duration, Duration::from_secs(30));
        assert!(config.enabled);
        assert_eq!(config.name, "default");
    }

    #[test]
    fn test_timeout_creation() {
        let timeout = Timeout::new(TimeoutConfig::default());
        assert_eq!(timeout.get_timeout(), Duration::from_secs(30));
        assert!(timeout.is_enabled());
    }

    #[test]
    fn test_timeout_builder() {
        let timeout = TimeoutBuilder::new()
            .duration(Duration::from_secs(10))
            .name("test_timeout")
            .enabled(true)
            .build();

        let config = timeout.get_config();
        assert_eq!(config.duration, Duration::from_secs(10));
        assert_eq!(config.name, "test_timeout");
        assert!(config.enabled);
    }

    #[tokio::test]
    async fn test_timeout_success() {
        let timeout = Timeout::new(TimeoutConfig::default());
        
        let result = timeout.execute(|| async {
            Ok::<String, UnifiedError>("成功".to_string())
        }).await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "成功");
        
        let stats = timeout.get_stats();
        assert_eq!(stats.total_requests, 1);
        assert_eq!(stats.successful_requests, 1);
        assert_eq!(stats.timed_out_requests, 0);
    }

    #[tokio::test]
    async fn test_timeout_timeout() {
        let config = TimeoutConfig {
            duration: Duration::from_millis(100),
            ..Default::default()
        };
        let timeout = Timeout::new(config);
        
        let result = timeout.execute(|| async {
            tokio::time::sleep(Duration::from_millis(200)).await;
            Ok::<String, UnifiedError>("成功".to_string())
        }).await;

        assert!(result.is_err());
        let error = result.unwrap_err();
        assert!(error.message().contains("超时"));
        
        let stats = timeout.get_stats();
        assert_eq!(stats.total_requests, 1);
        assert_eq!(stats.successful_requests, 0);
        assert_eq!(stats.timed_out_requests, 1);
    }

    #[tokio::test]
    async fn test_timeout_disabled() {
        let config = TimeoutConfig {
            enabled: false,
            ..Default::default()
        };
        let timeout = Timeout::new(config);
        
        let result = timeout.execute(|| async {
            tokio::time::sleep(Duration::from_millis(100)).await;
            Ok::<String, UnifiedError>("成功".to_string())
        }).await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "成功");
    }

    #[test]
    fn test_timeout_stats() {
        let timeout = Timeout::new(TimeoutConfig::default());
        let stats = timeout.get_stats();
        
        assert_eq!(stats.total_requests, 0);
        assert_eq!(stats.timed_out_requests, 0);
        assert_eq!(stats.successful_requests, 0);
        assert_eq!(stats.average_execution_time, Duration::ZERO);
        assert_eq!(stats.max_execution_time, Duration::ZERO);
    }

    #[test]
    fn test_timeout_reset() {
        let timeout = Timeout::new(TimeoutConfig::default());
        
        // 重置统计
        timeout.reset_stats();
        
        let stats = timeout.get_stats();
        assert_eq!(stats.total_requests, 0);
        assert_eq!(stats.timed_out_requests, 0);
        assert_eq!(stats.successful_requests, 0);
    }

    #[test]
    fn test_timeout_monitor() {
        let monitor = TimeoutMonitor::new();
        let stats = monitor.get_global_stats();
        
        assert_eq!(stats.total_requests, 0);
        assert_eq!(stats.timed_out_requests, 0);
        assert_eq!(stats.successful_requests, 0);
    }

    #[test]
    fn test_timeout_set_timeout() {
        let mut timeout = Timeout::new(TimeoutConfig::default());
        timeout.set_timeout(Duration::from_secs(10));
        
        assert_eq!(timeout.get_timeout(), Duration::from_secs(10));
    }

    #[test]
    fn test_timeout_set_enabled() {
        let mut timeout = Timeout::new(TimeoutConfig::default());
        timeout.set_enabled(false);
        
        assert!(!timeout.is_enabled());
    }
}
