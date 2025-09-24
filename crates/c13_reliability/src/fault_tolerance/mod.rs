//! 容错机制
//!
//! 提供企业级的容错模式，包括断路器、重试、超时、降级等。

//use std::time::Duration;
use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use serde::{Serialize, Deserialize};
//use tracing::{debug, warn, error, info};

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

pub mod circuit_breaker;
pub mod retry_policies;
pub mod bulkhead;
pub mod timeout;
pub mod fallback;
pub mod config;

pub use circuit_breaker::*;
pub use retry_policies::*;
pub use bulkhead::*;
pub use timeout::*;
pub use fallback::*;
pub use config::*;

/// 容错配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FaultToleranceConfig {
    /// 断路器配置
    pub circuit_breaker: CircuitBreakerConfig,
    /// 重试配置
    pub retry: RetryConfig,
    /// 舱壁配置
    pub bulkhead: BulkheadConfig,
    /// 超时配置
    pub timeout: TimeoutConfig,
    /// 降级配置
    pub fallback: FallbackConfig,
}

impl Default for FaultToleranceConfig {
    fn default() -> Self {
        Self {
            circuit_breaker: CircuitBreakerConfig::default(),
            retry: RetryConfig::default(),
            bulkhead: BulkheadConfig::default(),
            timeout: TimeoutConfig::default(),
            fallback: FallbackConfig::default(),
        }
    }
}

/// 容错构建器
pub struct ResilienceBuilder {
    config: FaultToleranceConfig,
}

impl ResilienceBuilder {
    /// 创建新的容错构建器
    pub fn new() -> Self {
        Self {
            config: FaultToleranceConfig::default(),
        }
    }

    /// 设置断路器配置
    pub fn circuit_breaker(mut self, config: CircuitBreakerConfig) -> Self {
        self.config.circuit_breaker = config;
        self
    }

    /// 设置重试配置
    pub fn retry(mut self, config: RetryConfig) -> Self {
        self.config.retry = config;
        self
    }

    /// 设置舱壁配置
    pub fn bulkhead(mut self, config: BulkheadConfig) -> Self {
        self.config.bulkhead = config;
        self
    }

    /// 设置超时配置
    pub fn timeout(mut self, config: TimeoutConfig) -> Self {
        self.config.timeout = config;
        self
    }

    /// 设置降级配置
    pub fn fallback(mut self, config: FallbackConfig) -> Self {
        self.config.fallback = config;
        self
    }

    /// 构建容错配置
    pub fn build(self) -> FaultToleranceConfig {
        self.config
    }
}

impl Default for ResilienceBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// 容错执行器
pub struct FaultToleranceExecutor {
    circuit_breaker: Arc<CircuitBreaker>,
    retry_policy: Arc<RetryPolicy>,
    bulkhead: Arc<Bulkhead>,
    timeout: Arc<Timeout>,
    fallback: Arc<Fallback>,
    config: FaultToleranceConfig,
}

impl FaultToleranceExecutor {
    /// 创建新的容错执行器
    pub fn new(config: FaultToleranceConfig) -> Self {
        Self {
            circuit_breaker: Arc::new(CircuitBreaker::new(config.circuit_breaker.clone())),
            retry_policy: Arc::new(RetryPolicy::new(config.retry.clone())),
            bulkhead: Arc::new(Bulkhead::new(config.bulkhead.clone())),
            timeout: Arc::new(Timeout::new(config.timeout.clone())),
            fallback: Arc::new(Fallback::new(config.fallback.clone())),
            config,
        }
    }

    /// 执行带容错的操作
    pub async fn execute<T, F, Fut>(&self, operation: F) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut + Clone,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
        T: Default + Clone,
    {
        // 1. 检查断路器状态
        if !self.circuit_breaker.can_execute() {
            return Err(self.create_circuit_open_error());
        }

        // 2. 获取舱壁资源
        let _permit = self.bulkhead.acquire().await?;

        // 3. 执行带超时的操作
        let result = self.timeout.execute(|| {
            self.retry_policy.execute(|| {
                operation()
            })
        }).await;

        // 4. 处理结果
        match result {
            Ok(value) => {
                self.circuit_breaker.record_success();
                Ok(value)
            }
            Err(error) => {
                self.circuit_breaker.record_failure();
                
                // 尝试降级
                if self.config.fallback.enabled {
                    self.fallback.execute(|| async { Err(error.clone()) }).await
                } else {
                    Err(error)
                }
            }
        }
    }

    /// 创建断路器开启错误
    fn create_circuit_open_error(&self) -> UnifiedError {
        let context = ErrorContext::new(
            "fault_tolerance",
            "execute",
            file!(),
            line!(),
            ErrorSeverity::High,
            "circuit_breaker"
        );

        UnifiedError::new(
            "断路器已开启，操作被拒绝",
            ErrorSeverity::High,
            "circuit_breaker_open",
            context
        ).with_code("CB_001")
        .with_suggestion("等待断路器恢复或检查服务状态")
    }

    /// 获取断路器状态
    pub fn circuit_breaker_state(&self) -> CircuitBreakerState {
        self.circuit_breaker.state()
    }

    /// 获取舱壁状态
    pub fn bulkhead_state(&self) -> BulkheadState {
        self.bulkhead.state()
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> FaultToleranceStats {
        FaultToleranceStats {
            circuit_breaker: self.circuit_breaker.get_stats(),
            retry: self.retry_policy.get_stats(),
            bulkhead: self.bulkhead.get_stats(),
            timeout: self.timeout.get_stats(),
            fallback: self.fallback.get_stats(),
        }
    }

    /// 重置统计信息
    pub fn reset_stats(&self) {
        self.circuit_breaker.reset_stats();
        self.retry_policy.reset_stats();
        self.bulkhead.reset_stats();
        self.timeout.reset_stats();
        self.fallback.reset_stats();
    }
}

/// 容错统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FaultToleranceStats {
    /// 断路器统计
    pub circuit_breaker: CircuitBreakerStats,
    /// 重试统计
    pub retry: RetryStats,
    /// 舱壁统计
    pub bulkhead: BulkheadStats,
    /// 超时统计
    pub timeout: TimeoutStats,
    /// 降级统计
    pub fallback: FallbackStats,
}

/// 容错监控器
pub struct FaultToleranceMonitor {
    executors: Arc<Mutex<HashMap<String, Arc<FaultToleranceExecutor>>>>,
    global_stats: Arc<Mutex<FaultToleranceStats>>,
}

impl FaultToleranceMonitor {
    /// 创建新的容错监控器
    pub fn new() -> Self {
        Self {
            executors: Arc::new(Mutex::new(HashMap::new())),
            global_stats: Arc::new(Mutex::new(FaultToleranceStats {
                circuit_breaker: CircuitBreakerStats::default(),
                retry: RetryStats::default(),
                bulkhead: BulkheadStats::default(),
                timeout: TimeoutStats::default(),
                fallback: FallbackStats::default(),
            })),
        }
    }

    /// 注册容错执行器
    pub fn register_executor(&self, name: String, executor: Arc<FaultToleranceExecutor>) {
        let mut executors = self.executors.lock().unwrap();
        executors.insert(name, executor);
    }

    /// 获取执行器
    pub fn get_executor(&self, name: &str) -> Option<Arc<FaultToleranceExecutor>> {
        let executors = self.executors.lock().unwrap();
        executors.get(name).cloned()
    }

    /// 获取全局统计信息
    pub fn get_global_stats(&self) -> FaultToleranceStats {
        let mut global_stats = self.global_stats.lock().unwrap().clone();
        
        // 聚合所有执行器的统计信息
        let executors = self.executors.lock().unwrap();
        for executor in executors.values() {
            let stats = executor.get_stats();
            global_stats.circuit_breaker.total_requests += stats.circuit_breaker.total_requests;
            global_stats.circuit_breaker.successful_requests += stats.circuit_breaker.successful_requests;
            global_stats.circuit_breaker.failed_requests += stats.circuit_breaker.failed_requests;
            global_stats.retry.total_attempts += stats.retry.total_attempts;
            global_stats.retry.successful_attempts += stats.retry.successful_attempts;
            global_stats.retry.failed_attempts += stats.retry.failed_attempts;
            global_stats.bulkhead.total_requests += stats.bulkhead.total_requests;
            global_stats.bulkhead.accepted_requests += stats.bulkhead.accepted_requests;
            global_stats.bulkhead.rejected_requests += stats.bulkhead.rejected_requests;
            global_stats.timeout.total_requests += stats.timeout.total_requests;
            global_stats.timeout.timed_out_requests += stats.timeout.timed_out_requests;
            global_stats.fallback.total_requests += stats.fallback.total_requests;
            global_stats.fallback.fallback_used += stats.fallback.fallback_used;
        }
        
        global_stats
    }

    /// 生成监控报告
    pub fn generate_report(&self) -> String {
        let stats = self.get_global_stats();
        let mut report = String::new();

        report.push_str("=== 容错机制监控报告 ===\n\n");

        // 断路器报告
        report.push_str("断路器状态:\n");
        report.push_str(&format!("  总请求数: {}\n", stats.circuit_breaker.total_requests));
        report.push_str(&format!("  成功请求数: {}\n", stats.circuit_breaker.successful_requests));
        report.push_str(&format!("  失败请求数: {}\n", stats.circuit_breaker.failed_requests));
        report.push_str(&format!("  成功率: {:.2}%\n", 
            if stats.circuit_breaker.total_requests > 0 {
                stats.circuit_breaker.successful_requests as f64 / stats.circuit_breaker.total_requests as f64 * 100.0
            } else {
                0.0
            }
        ));

        // 重试报告
        report.push_str("\n重试状态:\n");
        report.push_str(&format!("  总尝试数: {}\n", stats.retry.total_attempts));
        report.push_str(&format!("  成功尝试数: {}\n", stats.retry.successful_attempts));
        report.push_str(&format!("  失败尝试数: {}\n", stats.retry.failed_attempts));

        // 舱壁报告
        report.push_str("\n舱壁状态:\n");
        report.push_str(&format!("  总请求数: {}\n", stats.bulkhead.total_requests));
        report.push_str(&format!("  接受请求数: {}\n", stats.bulkhead.accepted_requests));
        report.push_str(&format!("  拒绝请求数: {}\n", stats.bulkhead.rejected_requests));

        // 超时报告
        report.push_str("\n超时状态:\n");
        report.push_str(&format!("  总请求数: {}\n", stats.timeout.total_requests));
        report.push_str(&format!("  超时请求数: {}\n", stats.timeout.timed_out_requests));

        // 降级报告
        report.push_str("\n降级状态:\n");
        report.push_str(&format!("  总请求数: {}\n", stats.fallback.total_requests));
        report.push_str(&format!("  使用降级数: {}\n", stats.fallback.fallback_used));

        report
    }
}

/// 全局容错监控器
pub struct GlobalFaultToleranceMonitor {
    monitor: Arc<FaultToleranceMonitor>,
}

impl GlobalFaultToleranceMonitor {
    /// 创建全局容错监控器
    pub fn new() -> Self {
        Self {
            monitor: Arc::new(FaultToleranceMonitor::new()),
        }
    }

    /// 获取全局监控器实例
    pub fn get_monitor(&self) -> Arc<FaultToleranceMonitor> {
        self.monitor.clone()
    }

    /// 注册全局执行器
    pub fn register_executor(&self, name: String, executor: Arc<FaultToleranceExecutor>) {
        self.monitor.register_executor(name, executor);
    }

    /// 获取全局统计信息
    pub fn get_global_stats(&self) -> FaultToleranceStats {
        self.monitor.get_global_stats()
    }

    /// 生成全局报告
    pub fn generate_global_report(&self) -> String {
        self.monitor.generate_report()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_fault_tolerance_config_default() {
        let config = FaultToleranceConfig::default();
        assert_eq!(config.circuit_breaker.failure_threshold, 5);
        assert_eq!(config.retry.max_attempts, 3);
        assert_eq!(config.bulkhead.max_concurrent_requests, 10);
        assert_eq!(config.timeout.duration, Duration::from_secs(30));
        assert!(config.fallback.enabled);
    }

    #[test]
    fn test_resilience_builder() {
        let config = ResilienceBuilder::new()
            .circuit_breaker(CircuitBreakerConfig {
                failure_threshold: 10,
                ..Default::default()
            })
            .retry(RetryConfig {
                max_attempts: 5,
                ..Default::default()
            })
            .build();

        assert_eq!(config.circuit_breaker.failure_threshold, 10);
        assert_eq!(config.retry.max_attempts, 5);
    }

    #[tokio::test]
    async fn test_fault_tolerance_executor() {
        let config = FaultToleranceConfig::default();
        let executor = FaultToleranceExecutor::new(config);

        let result = executor.execute(|| async {
            Ok::<String, UnifiedError>("成功".to_string())
        }).await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "成功");
    }

    #[test]
    fn test_fault_tolerance_monitor() {
        let monitor = FaultToleranceMonitor::new();
        let stats = monitor.get_global_stats();
        
        assert_eq!(stats.circuit_breaker.total_requests, 0);
        assert_eq!(stats.retry.total_attempts, 0);
        assert_eq!(stats.bulkhead.total_requests, 0);
    }

    #[test]
    fn test_global_fault_tolerance_monitor() {
        let global_monitor = GlobalFaultToleranceMonitor::new();
        let stats = global_monitor.get_global_stats();
        
        assert_eq!(stats.circuit_breaker.total_requests, 0);
        assert_eq!(stats.retry.total_attempts, 0);
    }
}
