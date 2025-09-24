//! 降级策略实现
//!
//! 提供服务降级功能，在服务不可用时提供备用方案。

use std::sync::{Arc, atomic::{AtomicU64, Ordering}};
use serde::{Serialize, Deserialize};
use tracing::{debug, error, info};

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

/// 降级配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackConfig {
    /// 是否启用降级
    pub enabled: bool,
    /// 降级名称
    pub name: String,
    /// 降级策略
    pub strategy: FallbackStrategy,
    /// 降级条件
    pub conditions: Vec<FallbackCondition>,
}

impl Default for FallbackConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            name: "default".to_string(),
            strategy: FallbackStrategy::DefaultValue,
            conditions: vec![FallbackCondition::AnyError],
        }
    }
}

/// 降级策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FallbackStrategy {
    /// 使用默认值
    DefaultValue,
    /// 使用缓存值
    CachedValue,
    /// 使用备用服务
    BackupService,
    /// 返回空结果
    EmptyResult,
    /// 自定义降级策略
    Custom {
        name: String,
        parameters: std::collections::HashMap<String, String>,
    },
}

/// 降级条件
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum FallbackCondition {
    /// 任何错误
    AnyError,
    /// 特定错误类型
    ErrorType(String),
    /// 特定错误严重程度
    ErrorSeverity(ErrorSeverity),
    /// 超时错误
    TimeoutError,
    /// 网络错误
    NetworkError,
    /// 自定义条件
    Custom {
        name: String,
        parameters: std::collections::HashMap<String, String>,
    },
}

/// 降级统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackStats {
    /// 总请求数
    pub total_requests: u64,
    /// 使用降级数
    pub fallback_used: u64,
    /// 降级成功率
    pub fallback_success_rate: f64,
    /// 最后更新时间
    pub last_updated: chrono::DateTime<chrono::Utc>,
}

impl Default for FallbackStats {
    fn default() -> Self {
        Self {
            total_requests: 0,
            fallback_used: 0,
            fallback_success_rate: 0.0,
            last_updated: chrono::Utc::now(),
        }
    }
}

/// 降级实现
pub struct Fallback {
    config: FallbackConfig,
    total_requests: AtomicU64,
    fallback_used: AtomicU64,
    fallback_successes: AtomicU64,
    stats: std::sync::Mutex<FallbackStats>,
}

impl Fallback {
    /// 创建新的降级处理器
    pub fn new(config: FallbackConfig) -> Self {
        Self {
            config,
            total_requests: AtomicU64::new(0),
            fallback_used: AtomicU64::new(0),
            fallback_successes: AtomicU64::new(0),
            stats: std::sync::Mutex::new(FallbackStats::default()),
        }
    }

    /// 执行带降级的操作
    pub async fn execute<T, F, Fut>(&self, operation: F) -> Result<T, UnifiedError>
    where
        T: Default + Clone,
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        if !self.config.enabled {
            return operation().await;
        }

        self.total_requests.fetch_add(1, Ordering::Relaxed);

        match operation().await {
            Ok(result) => Ok(result),
            Err(error) => {
                if self.should_fallback(&error) {
                    self.fallback_used.fetch_add(1, Ordering::Relaxed);
                    
                    match self.execute_fallback().await {
                        Ok(result) => {
                            self.fallback_successes.fetch_add(1, Ordering::Relaxed);
                            self.update_stats();
                            
                            info!("降级策略 {} 执行成功", self.config.name);
                            Ok(result)
                        }
                        Err(fallback_error) => {
                            self.update_stats();
                            
                            error!("降级策略 {} 执行失败: {}", self.config.name, fallback_error);
                            Err(fallback_error)
                        }
                    }
                } else {
                    self.update_stats();
                    Err(error)
                }
            }
        }
    }

    /// 检查是否应该降级
    fn should_fallback(&self, error: &UnifiedError) -> bool {
        self.config.conditions.iter().any(|condition| {
            match condition {
                FallbackCondition::AnyError => true,
                FallbackCondition::ErrorType(error_type) => {
                    error.category().contains(error_type)
                }
                FallbackCondition::ErrorSeverity(severity) => {
                    error.severity() == *severity
                }
                FallbackCondition::TimeoutError => {
                    error.category() == "timeout"
                }
                FallbackCondition::NetworkError => {
                    error.category() == "network"
                }
                FallbackCondition::Custom { name, parameters } => {
                    debug!("检查自定义降级条件: {}, 参数: {:?}", name, parameters);
                    // 这里可以根据具体需求实现自定义条件检查
                    false
                }
            }
        })
    }

    /// 执行降级策略
    async fn execute_fallback<T>(&self) -> Result<T, UnifiedError>
    where
        T: Default + Clone,
    {
        match &self.config.strategy {
            FallbackStrategy::DefaultValue => {
                debug!("使用默认值降级策略");
                Ok(T::default())
            }
            FallbackStrategy::CachedValue => {
                debug!("使用缓存值降级策略");
                // 这里应该从缓存中获取值
                // 简化实现，返回默认值
                Ok(T::default())
            }
            FallbackStrategy::BackupService => {
                debug!("使用备用服务降级策略");
                // 这里应该调用备用服务
                // 简化实现，返回默认值
                Ok(T::default())
            }
            FallbackStrategy::EmptyResult => {
                debug!("使用空结果降级策略");
                // 对于某些类型，空结果可能不是有效的默认值
                // 这里需要根据具体类型处理
                Err(self.create_fallback_error("空结果降级策略不适用于此类型"))
            }
            FallbackStrategy::Custom { name, parameters } => {
                debug!("使用自定义降级策略: {}, 参数: {:?}", name, parameters);
                // 这里应该根据自定义策略执行降级
                // 简化实现，返回默认值
                Ok(T::default())
            }
        }
    }

    /// 创建降级错误
    fn create_fallback_error(&self, message: &str) -> UnifiedError {
        let context = ErrorContext::new(
            "fallback",
            "execute_fallback",
            file!(),
            line!(),
            ErrorSeverity::High,
            "fallback"
        );

        UnifiedError::new(
            &format!("降级策略 {} 失败: {}", self.config.name, message),
            ErrorSeverity::High,
            "fallback_failed",
            context
        ).with_code("FB_001")
        .with_suggestion("检查降级策略配置或备用服务状态")
    }

    /// 更新统计信息
    fn update_stats(&self) {
        let mut stats = self.stats.lock().unwrap();
        stats.total_requests = self.total_requests.load(Ordering::Relaxed);
        stats.fallback_used = self.fallback_used.load(Ordering::Relaxed);
        
        if stats.fallback_used > 0 {
            stats.fallback_success_rate = self.fallback_successes.load(Ordering::Relaxed) as f64 / stats.fallback_used as f64;
        } else {
            stats.fallback_success_rate = 0.0;
        }
        
        stats.last_updated = chrono::Utc::now();
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> FallbackStats {
        self.stats.lock().unwrap().clone()
    }

    /// 重置统计信息
    pub fn reset_stats(&self) {
        self.total_requests.store(0, Ordering::Relaxed);
        self.fallback_used.store(0, Ordering::Relaxed);
        self.fallback_successes.store(0, Ordering::Relaxed);
        
        let mut stats = self.stats.lock().unwrap();
        *stats = FallbackStats::default();
    }

    /// 获取配置
    pub fn get_config(&self) -> &FallbackConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: FallbackConfig) {
        self.config = config;
    }

    /// 检查是否启用降级
    pub fn is_enabled(&self) -> bool {
        self.config.enabled
    }

    /// 启用或禁用降级
    pub fn set_enabled(&mut self, enabled: bool) {
        self.config.enabled = enabled;
    }
}

/// 降级构建器
pub struct FallbackBuilder {
    config: FallbackConfig,
}

impl FallbackBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: FallbackConfig::default(),
        }
    }

    /// 设置降级名称
    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.config.name = name.into();
        self
    }

    /// 设置降级策略
    pub fn strategy(mut self, strategy: FallbackStrategy) -> Self {
        self.config.strategy = strategy;
        self
    }

    /// 设置降级条件
    pub fn conditions(mut self, conditions: Vec<FallbackCondition>) -> Self {
        self.config.conditions = conditions;
        self
    }

    /// 启用或禁用降级
    pub fn enabled(mut self, enabled: bool) -> Self {
        self.config.enabled = enabled;
        self
    }

    /// 构建降级处理器
    pub fn build(self) -> Fallback {
        Fallback::new(self.config)
    }
}

impl Default for FallbackBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// 降级监控器
pub struct FallbackMonitor {
    fallbacks: std::sync::Mutex<std::collections::HashMap<String, Arc<Fallback>>>,
    global_stats: std::sync::Mutex<FallbackStats>,
}

impl FallbackMonitor {
    /// 创建新的降级监控器
    pub fn new() -> Self {
        Self {
            fallbacks: std::sync::Mutex::new(std::collections::HashMap::new()),
            global_stats: std::sync::Mutex::new(FallbackStats::default()),
        }
    }

    /// 注册降级处理器
    pub fn register_fallback(&self, name: String, fallback: Arc<Fallback>) {
        let mut fallbacks = self.fallbacks.lock().unwrap();
        fallbacks.insert(name, fallback);
    }

    /// 获取降级处理器
    pub fn get_fallback(&self, name: &str) -> Option<Arc<Fallback>> {
        let fallbacks = self.fallbacks.lock().unwrap();
        fallbacks.get(name).cloned()
    }

    /// 获取全局统计信息
    pub fn get_global_stats(&self) -> FallbackStats {
        let mut global_stats = self.global_stats.lock().unwrap().clone();
        
        // 聚合所有降级处理器的统计信息
        let fallbacks = self.fallbacks.lock().unwrap();
        for fallback in fallbacks.values() {
            let stats = fallback.get_stats();
            global_stats.total_requests += stats.total_requests;
            global_stats.fallback_used += stats.fallback_used;
        }
        
        // 重新计算降级成功率
        if global_stats.fallback_used > 0 {
            let total_successes = fallbacks.values()
                .map(|f| f.get_stats().fallback_used as f64 * f.get_stats().fallback_success_rate)
                .sum::<f64>();
            global_stats.fallback_success_rate = total_successes / global_stats.fallback_used as f64;
        }
        
        global_stats
    }

    /// 生成监控报告
    pub fn generate_report(&self) -> String {
        let stats = self.get_global_stats();
        let mut report = String::new();

        report.push_str("=== 降级监控报告 ===\n\n");
        report.push_str(&format!("总请求数: {}\n", stats.total_requests));
        report.push_str(&format!("使用降级数: {}\n", stats.fallback_used));
        report.push_str(&format!("降级率: {:.2}%\n", 
            if stats.total_requests > 0 {
                stats.fallback_used as f64 / stats.total_requests as f64 * 100.0
            } else {
                0.0
            }
        ));
        report.push_str(&format!("降级成功率: {:.2}%\n", stats.fallback_success_rate * 100.0));

        report
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_handling::ErrorSeverity;

    #[test]
    fn test_fallback_config_default() {
        let config = FallbackConfig::default();
        assert!(config.enabled);
        assert_eq!(config.name, "default");
        assert!(matches!(config.strategy, FallbackStrategy::DefaultValue));
        assert!(!config.conditions.is_empty());
    }

    #[test]
    fn test_fallback_creation() {
        let fallback = Fallback::new(FallbackConfig::default());
        assert!(fallback.is_enabled());
    }

    #[test]
    fn test_fallback_builder() {
        let fallback = FallbackBuilder::new()
            .name("test_fallback")
            .strategy(FallbackStrategy::CachedValue)
            .conditions(vec![FallbackCondition::NetworkError])
            .enabled(true)
            .build();

        let config = fallback.get_config();
        assert_eq!(config.name, "test_fallback");
        assert!(matches!(config.strategy, FallbackStrategy::CachedValue));
        assert!(config.conditions.contains(&FallbackCondition::NetworkError));
        assert!(config.enabled);
    }

    #[tokio::test]
    async fn test_fallback_success() {
        let fallback = Fallback::new(FallbackConfig::default());
        
        let result: Result<String, UnifiedError> = fallback.execute(|| async {
            Ok::<String, UnifiedError>("成功".to_string())
        }).await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "成功");
        
        let stats = fallback.get_stats();
        assert_eq!(stats.total_requests, 1);
        assert_eq!(stats.fallback_used, 0);
    }

    #[tokio::test]
    async fn test_fallback_fallback() {
        let config = FallbackConfig {
            strategy: FallbackStrategy::DefaultValue,
            conditions: vec![FallbackCondition::AnyError],
            ..Default::default()
        };
        let fallback = Fallback::new(config);
        
        let result: Result<String, UnifiedError> = fallback.execute(|| async {
            Err(UnifiedError::new(
                "测试错误",
                ErrorSeverity::Medium,
                "test",
                ErrorContext::new("test", "test", "test.rs", 1, ErrorSeverity::Medium, "test")
            ))
        }).await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), ""); // 默认值
        
        let stats = fallback.get_stats();
        assert_eq!(stats.total_requests, 1);
        assert_eq!(stats.fallback_used, 1);
        assert_eq!(stats.fallback_success_rate, 1.0);
    }

    #[tokio::test]
    async fn test_fallback_disabled() {
        let config = FallbackConfig {
            enabled: false,
            ..Default::default()
        };
        let fallback = Fallback::new(config);
        
        let result: Result<String, UnifiedError> = fallback.execute(|| async {
            Err(UnifiedError::new(
                "测试错误",
                ErrorSeverity::Medium,
                "test",
                ErrorContext::new("test", "test", "test.rs", 1, ErrorSeverity::Medium, "test")
            ))
        }).await;

        assert!(result.is_err());
        
        let stats = fallback.get_stats();
        assert_eq!(stats.total_requests, 1);
        assert_eq!(stats.fallback_used, 0);
    }

    #[test]
    fn test_fallback_stats() {
        let fallback = Fallback::new(FallbackConfig::default());
        let stats = fallback.get_stats();
        
        assert_eq!(stats.total_requests, 0);
        assert_eq!(stats.fallback_used, 0);
        assert_eq!(stats.fallback_success_rate, 0.0);
    }

    #[test]
    fn test_fallback_reset() {
        let fallback = Fallback::new(FallbackConfig::default());
        
        // 重置统计
        fallback.reset_stats();
        
        let stats = fallback.get_stats();
        assert_eq!(stats.total_requests, 0);
        assert_eq!(stats.fallback_used, 0);
    }

    #[test]
    fn test_fallback_monitor() {
        let monitor = FallbackMonitor::new();
        let stats = monitor.get_global_stats();
        
        assert_eq!(stats.total_requests, 0);
        assert_eq!(stats.fallback_used, 0);
        assert_eq!(stats.fallback_success_rate, 0.0);
    }

    #[test]
    fn test_fallback_conditions() {
        let config = FallbackConfig {
            conditions: vec![
                FallbackCondition::ErrorType("network".to_string()),
                FallbackCondition::ErrorSeverity(ErrorSeverity::High),
            ],
            ..Default::default()
        };
        let fallback = Fallback::new(config);
        
        let config = fallback.get_config();
        assert_eq!(config.conditions.len(), 2);
    }

    #[test]
    fn test_fallback_set_enabled() {
        let mut fallback = Fallback::new(FallbackConfig::default());
        fallback.set_enabled(false);
        
        assert!(!fallback.is_enabled());
    }
}
