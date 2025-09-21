//! 错误处理和恢复策略模块
//! 
//! 提供统一的错误处理机制、自动恢复策略和错误监控功能

use std::collections::HashMap;
use std::time::Duration;
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use thiserror::Error;

/// 错误严重程度
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ErrorSeverity {
    /// 低 - 不影响核心功能
    Low,
    /// 中 - 影响部分功能
    Medium,
    /// 高 - 影响核心功能
    High,
    /// 严重 - 系统不可用
    Critical,
}

/// 错误类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum ErrorType {
    /// 网络错误
    Network,
    /// 设备错误
    Device,
    /// 数据错误
    Data,
    /// 配置错误
    Configuration,
    /// 认证错误
    Authentication,
    /// 权限错误
    Authorization,
    /// 资源错误
    Resource,
    /// 系统错误
    System,
    /// 未知错误
    Unknown,
}

/// 错误记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorRecord {
    /// 错误ID
    pub id: String,
    /// 错误类型
    pub error_type: ErrorType,
    /// 严重程度
    pub severity: ErrorSeverity,
    /// 错误消息
    pub message: String,
    /// 错误详情
    pub details: Option<String>,
    /// 发生时间
    pub timestamp: DateTime<Utc>,
    /// 组件名称
    pub component: String,
    /// 操作名称
    pub operation: Option<String>,
    /// 是否已恢复
    pub recovered: bool,
    /// 恢复时间
    pub recovery_time: Option<DateTime<Utc>>,
    /// 重试次数
    pub retry_count: u32,
    /// 最大重试次数
    pub max_retries: u32,
}

/// 恢复策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RecoveryStrategy {
    /// 立即重试
    ImmediateRetry,
    /// 指数退避重试
    ExponentialBackoff,
    /// 固定间隔重试
    FixedInterval,
    /// 手动恢复
    ManualRecovery,
    /// 自动恢复
    AutoRecovery,
    /// 降级服务
    GracefulDegradation,
    /// 故障转移
    Failover,
}

/// 恢复配置
#[derive(Debug, Clone)]
pub struct RecoveryConfig {
    /// 最大重试次数
    pub max_retries: u32,
    /// 初始重试间隔
    pub initial_retry_interval: Duration,
    /// 最大重试间隔
    pub max_retry_interval: Duration,
    /// 退避乘数
    pub backoff_multiplier: f64,
    /// 恢复策略
    pub strategy: RecoveryStrategy,
    /// 是否启用自动恢复
    pub auto_recovery_enabled: bool,
    /// 恢复超时时间
    pub recovery_timeout: Duration,
}

impl Default for RecoveryConfig {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_retry_interval: Duration::from_secs(1),
            max_retry_interval: Duration::from_secs(60),
            backoff_multiplier: 2.0,
            strategy: RecoveryStrategy::ExponentialBackoff,
            auto_recovery_enabled: true,
            recovery_timeout: Duration::from_secs(300),
        }
    }
}

/// 错误处理器
pub struct ErrorHandler {
    /// 错误记录存储
    errors: Arc<RwLock<HashMap<String, ErrorRecord>>>,
    /// 恢复配置
    config: RecoveryConfig,
    /// 错误统计
    stats: Arc<RwLock<ErrorStats>>,
    /// 恢复回调
    recovery_callbacks: Arc<RwLock<HashMap<String, Box<dyn Fn(&ErrorRecord) -> Result<(), Box<dyn std::error::Error>> + Send + Sync>>>>,
}

/// 错误统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorStats {
    /// 总错误数
    pub total_errors: u64,
    /// 按严重程度统计
    pub errors_by_severity: HashMap<ErrorSeverity, u64>,
    /// 按类型统计
    pub errors_by_type: HashMap<ErrorType, u64>,
    /// 按组件统计
    pub errors_by_component: HashMap<String, u64>,
    /// 恢复成功率
    pub recovery_success_rate: f64,
    /// 平均恢复时间
    pub avg_recovery_time: Duration,
    /// 最后更新时间
    pub last_updated: DateTime<Utc>,
}

impl Default for ErrorStats {
    fn default() -> Self {
        Self {
            total_errors: 0,
            errors_by_severity: HashMap::new(),
            errors_by_type: HashMap::new(),
            errors_by_component: HashMap::new(),
            recovery_success_rate: 0.0,
            avg_recovery_time: Duration::ZERO,
            last_updated: Utc::now(),
        }
    }
}

impl ErrorHandler {
    /// 创建新的错误处理器
    pub fn new(config: RecoveryConfig) -> Self {
        Self {
            errors: Arc::new(RwLock::new(HashMap::new())),
            config,
            stats: Arc::new(RwLock::new(ErrorStats::default())),
            recovery_callbacks: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 记录错误
    pub async fn record_error(
        &self,
        error_type: ErrorType,
        severity: ErrorSeverity,
        message: String,
        component: String,
        operation: Option<String>,
        details: Option<String>,
    ) -> String {
        let error_id = uuid::Uuid::new_v4().to_string();
        let error_record = ErrorRecord {
            id: error_id.clone(),
            error_type: error_type.clone(),
            severity,
            message: message.clone(),
            details,
            timestamp: Utc::now(),
            component: component.clone(),
            operation,
            recovered: false,
            recovery_time: None,
            retry_count: 0,
            max_retries: self.config.max_retries,
        };

        // 存储错误记录
        {
            let mut errors = self.errors.write().await;
            errors.insert(error_id.clone(), error_record.clone());
        }

        // 更新统计信息
        self.update_stats(&error_record).await;

        // 尝试自动恢复
        if self.config.auto_recovery_enabled {
            let _ = self.attempt_recovery(&error_record).await;
        }

        error_id
    }

    /// 尝试恢复错误
    pub async fn attempt_recovery(&self, error_record: &ErrorRecord) -> Result<(), Box<dyn std::error::Error>> {
        if error_record.retry_count >= error_record.max_retries {
            return Err("超过最大重试次数".into());
        }

        // 根据恢复策略计算重试间隔
        let retry_interval = self.calculate_retry_interval(error_record.retry_count);
        
        // 等待重试间隔
        tokio::time::sleep(retry_interval).await;

        // 执行恢复操作
        let recovery_result = self.execute_recovery(error_record).await;

        // 更新错误记录
        {
            let mut errors = self.errors.write().await;
            if let Some(record) = errors.get_mut(&error_record.id) {
                record.retry_count += 1;
                if recovery_result.is_ok() {
                    record.recovered = true;
                    record.recovery_time = Some(Utc::now());
                }
            }
        }

        recovery_result
    }

    /// 执行恢复操作
    async fn execute_recovery(&self, error_record: &ErrorRecord) -> Result<(), Box<dyn std::error::Error>> {
        match &error_record.error_type {
            ErrorType::Network => {
                self.recover_network_error(error_record).await
            },
            ErrorType::Device => {
                self.recover_device_error(error_record).await
            },
            ErrorType::Data => {
                self.recover_data_error(error_record).await
            },
            ErrorType::Configuration => {
                self.recover_configuration_error(error_record).await
            },
            ErrorType::Authentication => {
                self.recover_authentication_error(error_record).await
            },
            ErrorType::Authorization => {
                self.recover_authorization_error(error_record).await
            },
            ErrorType::Resource => {
                self.recover_resource_error(error_record).await
            },
            ErrorType::System => {
                self.recover_system_error(error_record).await
            },
            ErrorType::Unknown => {
                self.recover_unknown_error(error_record).await
            },
        }
    }

    /// 恢复网络错误
    async fn recover_network_error(&self, error_record: &ErrorRecord) -> Result<(), Box<dyn std::error::Error>> {
        // 实现网络错误恢复逻辑
        // 例如：重新连接、切换网络接口等
        println!("尝试恢复网络错误: {}", error_record.message);
        Ok(())
    }

    /// 恢复设备错误
    async fn recover_device_error(&self, error_record: &ErrorRecord) -> Result<(), Box<dyn std::error::Error>> {
        // 实现设备错误恢复逻辑
        // 例如：重启设备、重新初始化等
        println!("尝试恢复设备错误: {}", error_record.message);
        Ok(())
    }

    /// 恢复数据错误
    async fn recover_data_error(&self, error_record: &ErrorRecord) -> Result<(), Box<dyn std::error::Error>> {
        // 实现数据错误恢复逻辑
        // 例如：数据验证、重新获取数据等
        println!("尝试恢复数据错误: {}", error_record.message);
        Ok(())
    }

    /// 恢复配置错误
    async fn recover_configuration_error(&self, error_record: &ErrorRecord) -> Result<(), Box<dyn std::error::Error>> {
        // 实现配置错误恢复逻辑
        // 例如：重新加载配置、使用默认配置等
        println!("尝试恢复配置错误: {}", error_record.message);
        Ok(())
    }

    /// 恢复认证错误
    async fn recover_authentication_error(&self, error_record: &ErrorRecord) -> Result<(), Box<dyn std::error::Error>> {
        // 实现认证错误恢复逻辑
        // 例如：重新认证、刷新令牌等
        println!("尝试恢复认证错误: {}", error_record.message);
        Ok(())
    }

    /// 恢复权限错误
    async fn recover_authorization_error(&self, error_record: &ErrorRecord) -> Result<(), Box<dyn std::error::Error>> {
        // 实现权限错误恢复逻辑
        // 例如：重新授权、降级权限等
        println!("尝试恢复权限错误: {}", error_record.message);
        Ok(())
    }

    /// 恢复资源错误
    async fn recover_resource_error(&self, error_record: &ErrorRecord) -> Result<(), Box<dyn std::error::Error>> {
        // 实现资源错误恢复逻辑
        // 例如：释放资源、重新分配资源等
        println!("尝试恢复资源错误: {}", error_record.message);
        Ok(())
    }

    /// 恢复系统错误
    async fn recover_system_error(&self, error_record: &ErrorRecord) -> Result<(), Box<dyn std::error::Error>> {
        // 实现系统错误恢复逻辑
        // 例如：重启服务、清理内存等
        println!("尝试恢复系统错误: {}", error_record.message);
        Ok(())
    }

    /// 恢复未知错误
    async fn recover_unknown_error(&self, error_record: &ErrorRecord) -> Result<(), Box<dyn std::error::Error>> {
        // 实现未知错误恢复逻辑
        // 例如：通用恢复策略、日志记录等
        println!("尝试恢复未知错误: {}", error_record.message);
        Ok(())
    }

    /// 计算重试间隔
    fn calculate_retry_interval(&self, retry_count: u32) -> Duration {
        match self.config.strategy {
            RecoveryStrategy::ImmediateRetry => Duration::ZERO,
            RecoveryStrategy::ExponentialBackoff => {
                let interval = self.config.initial_retry_interval.as_nanos() as f64 
                    * self.config.backoff_multiplier.powi(retry_count as i32);
                let max_interval = self.config.max_retry_interval.as_nanos() as f64;
                Duration::from_nanos(interval.min(max_interval) as u64)
            },
            RecoveryStrategy::FixedInterval => self.config.initial_retry_interval,
            _ => self.config.initial_retry_interval,
        }
    }

    /// 更新统计信息
    async fn update_stats(&self, error_record: &ErrorRecord) {
        let mut stats = self.stats.write().await;
        
        stats.total_errors += 1;
        
        // 按严重程度统计
        *stats.errors_by_severity.entry(error_record.severity).or_insert(0) += 1;
        
        // 按类型统计
        *stats.errors_by_type.entry(error_record.error_type.clone()).or_insert(0) += 1;
        
        // 按组件统计
        *stats.errors_by_component.entry(error_record.component.clone()).or_insert(0) += 1;
        
        stats.last_updated = Utc::now();
    }

    /// 获取错误记录
    pub async fn get_error(&self, error_id: &str) -> Option<ErrorRecord> {
        let errors = self.errors.read().await;
        errors.get(error_id).cloned()
    }

    /// 获取所有错误记录
    pub async fn get_all_errors(&self) -> Vec<ErrorRecord> {
        let errors = self.errors.read().await;
        errors.values().cloned().collect()
    }

    /// 获取错误统计信息
    pub async fn get_stats(&self) -> ErrorStats {
        let stats = self.stats.read().await;
        stats.clone()
    }

    /// 清理过期错误记录
    pub async fn cleanup_expired_errors(&self, max_age: Duration) {
        let cutoff_time = Utc::now() - chrono::Duration::from_std(max_age).unwrap();
        
        let mut errors = self.errors.write().await;
        errors.retain(|_, record| record.timestamp > cutoff_time);
    }

    /// 注册恢复回调
    pub async fn register_recovery_callback<F>(&self, error_type: ErrorType, callback: F)
    where
        F: Fn(&ErrorRecord) -> Result<(), Box<dyn std::error::Error>> + Send + Sync + 'static,
    {
        let mut callbacks = self.recovery_callbacks.write().await;
        callbacks.insert(format!("{:?}", error_type), Box::new(callback));
    }

    /// 生成错误报告
    pub async fn generate_error_report(&self) -> String {
        let stats = self.get_stats().await;
        let errors = self.get_all_errors().await;
        
        let mut report = String::new();
        report.push_str("# 错误处理报告\n\n");
        report.push_str(&format!("生成时间: {}\n", Utc::now().format("%Y-%m-%d %H:%M:%S UTC")));
        report.push_str(&format!("总错误数: {}\n", stats.total_errors));
        report.push_str(&format!("恢复成功率: {:.1}%\n", stats.recovery_success_rate * 100.0));
        report.push_str(&format!("平均恢复时间: {:?}\n\n", stats.avg_recovery_time));

        // 按严重程度统计
        report.push_str("## 按严重程度统计\n\n");
        for (severity, count) in &stats.errors_by_severity {
            report.push_str(&format!("- {:?}: {} 个\n", severity, count));
        }

        // 按类型统计
        report.push_str("\n## 按类型统计\n\n");
        for (error_type, count) in &stats.errors_by_type {
            report.push_str(&format!("- {:?}: {} 个\n", error_type, count));
        }

        // 按组件统计
        report.push_str("\n## 按组件统计\n\n");
        for (component, count) in &stats.errors_by_component {
            report.push_str(&format!("- {}: {} 个\n", component, count));
        }

        // 最近错误
        report.push_str("\n## 最近错误\n\n");
        let mut recent_errors: Vec<_> = errors.into_iter().collect();
        recent_errors.sort_by_key(|e| e.timestamp);
        recent_errors.reverse();
        
        for error in recent_errors.iter().take(10) {
            report.push_str(&format!("- [{}] {}: {} ({:?})\n", 
                error.timestamp.format("%Y-%m-%d %H:%M:%S"),
                error.component,
                error.message,
                error.severity
            ));
        }

        report
    }
}

/// 错误处理宏
#[macro_export]
macro_rules! handle_error {
    ($handler:expr, $error_type:expr, $severity:expr, $component:expr, $operation:expr, $result:expr) => {{
        match $result {
            Ok(value) => Ok(value),
            Err(e) => {
                let error_id = $handler.record_error(
                    $error_type,
                    $severity,
                    e.to_string(),
                    $component.to_string(),
                    Some($operation.to_string()),
                    None,
                ).await;
                Err(format!("错误ID: {} - {}", error_id, e).into())
            }
        }
    }};
}

/// 错误处理错误类型
#[derive(Debug, Error)]
pub enum ErrorHandlingError {
    #[error("错误记录失败: {0}")]
    RecordingError(String),
    
    #[error("恢复操作失败: {0}")]
    RecoveryError(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("回调注册失败: {0}")]
    CallbackRegistrationError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_error_handler_creation() {
        let config = RecoveryConfig::default();
        let handler = ErrorHandler::new(config);
        
        let stats = handler.get_stats().await;
        assert_eq!(stats.total_errors, 0);
    }

    #[tokio::test]
    async fn test_error_recording() {
        let config = RecoveryConfig::default();
        let handler = ErrorHandler::new(config);
        
        let error_id = handler.record_error(
            ErrorType::Network,
            ErrorSeverity::Medium,
            "网络连接失败".to_string(),
            "network_manager".to_string(),
            Some("connect".to_string()),
            None,
        ).await;
        
        assert!(!error_id.is_empty());
        
        let error_record = handler.get_error(&error_id).await;
        assert!(error_record.is_some());
        assert_eq!(error_record.unwrap().message, "网络连接失败");
    }

    #[tokio::test]
    async fn test_error_stats() {
        let config = RecoveryConfig::default();
        let handler = ErrorHandler::new(config);
        
        // 记录几个错误
        handler.record_error(
            ErrorType::Network,
            ErrorSeverity::Medium,
            "网络错误1".to_string(),
            "component1".to_string(),
            None,
            None,
        ).await;
        
        handler.record_error(
            ErrorType::Device,
            ErrorSeverity::High,
            "设备错误1".to_string(),
            "component2".to_string(),
            None,
            None,
        ).await;
        
        let stats = handler.get_stats().await;
        assert_eq!(stats.total_errors, 2);
        assert_eq!(stats.errors_by_type.len(), 2);
        assert_eq!(stats.errors_by_component.len(), 2);
    }
}
