//! 错误监控和报告
//!
//! 提供错误监控、统计、告警和报告功能。

use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use serde::{Serialize, Deserialize};
use tracing::{error, warn, info, debug};

use crate::error_handling::{
    UnifiedError, ErrorSeverity,
};

/// 错误统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorStats {
    /// 总错误数
    pub total_errors: u64,
    /// 按严重程度分类的错误数
    pub errors_by_severity: HashMap<String, u64>,
    /// 按分类统计的错误数
    pub errors_by_category: HashMap<String, u64>,
    /// 按模块统计的错误数
    pub errors_by_module: HashMap<String, u64>,
    /// 最近1小时的错误数
    pub recent_errors: u64,
    /// 错误率（错误数/总操作数）
    pub error_rate: f64,
    /// 最后更新时间
    pub last_updated: chrono::DateTime<chrono::Utc>,
}

impl Default for ErrorStats {
    fn default() -> Self {
        Self {
            total_errors: 0,
            errors_by_severity: HashMap::new(),
            errors_by_category: HashMap::new(),
            errors_by_module: HashMap::new(),
            recent_errors: 0,
            error_rate: 0.0,
            last_updated: chrono::Utc::now(),
        }
    }
}

/// 告警配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertConfig {
    /// 错误数量阈值
    pub error_count_threshold: u64,
    /// 错误率阈值
    pub error_rate_threshold: f64,
    /// 严重错误阈值
    pub critical_error_threshold: u64,
    /// 告警间隔
    pub alert_interval: Duration,
    /// 是否启用告警
    pub enabled: bool,
    /// 告警接收者
    pub recipients: Vec<String>,
}

impl Default for AlertConfig {
    fn default() -> Self {
        Self {
            error_count_threshold: 100,
            error_rate_threshold: 0.1,
            critical_error_threshold: 10,
            alert_interval: Duration::from_secs(300), // 5分钟
            enabled: true,
            recipients: Vec::new(),
        }
    }
}

/// 错误监控器
pub struct ErrorMonitor {
    /// 错误日志
    error_log: Arc<Mutex<Vec<UnifiedError>>>,
    /// 错误统计
    error_stats: Arc<Mutex<ErrorStats>>,
    /// 告警配置
    alert_config: AlertConfig,
    /// 上次告警时间
    last_alert: Arc<Mutex<Option<Instant>>>,
    /// 最大日志大小
    max_log_size: usize,
    /// 统计窗口大小
    stats_window: Duration,
}

impl ErrorMonitor {
    /// 创建新的错误监控器
    pub fn new(max_log_size: usize, alert_config: AlertConfig) -> Self {
        Self {
            error_log: Arc::new(Mutex::new(Vec::new())),
            error_stats: Arc::new(Mutex::new(ErrorStats::default())),
            alert_config,
            last_alert: Arc::new(Mutex::new(None)),
            max_log_size,
            stats_window: Duration::from_secs(3600), // 1小时
        }
    }

    /// 记录错误
    pub fn record_error(&self, error: UnifiedError) {
        let severity = error.severity();
        let category = error.category().to_string();
        let module = error.context().module.clone();
        let _timestamp = error.timestamp();

        // 记录到日志
        {
            let mut log = self.error_log.lock().unwrap();
            if log.len() >= self.max_log_size {
                log.remove(0); // 移除最旧的错误
            }
            log.push(error.clone());
        }

        // 更新统计
        {
            let mut stats = self.error_stats.lock().unwrap();
            stats.total_errors += 1;
            
            // 按严重程度统计
            let severity_key = format!("{:?}", severity);
            *stats.errors_by_severity.entry(severity_key).or_insert(0) += 1;
            
            // 按分类统计
            *stats.errors_by_category.entry(category).or_insert(0) += 1;
            
            // 按模块统计
            *stats.errors_by_module.entry(module).or_insert(0) += 1;
            
            // 计算最近错误数
            let cutoff_time = chrono::Utc::now() - chrono::Duration::seconds(self.stats_window.as_secs() as i64);
            stats.recent_errors = self.count_recent_errors(cutoff_time);
            
            stats.last_updated = chrono::Utc::now();
        }

        // 记录到日志系统
        match severity {
            ErrorSeverity::Critical => error!("严重错误: {}", error),
            ErrorSeverity::High => error!("高严重程度错误: {}", error),
            ErrorSeverity::Medium => warn!("中等严重程度错误: {}", error),
            ErrorSeverity::Low => info!("低严重程度错误: {}", error),
        }

        // 检查是否需要告警
        if self.alert_config.enabled {
            self.check_and_send_alert();
        }
    }

    /// 计算最近错误数
    fn count_recent_errors(&self, cutoff_time: chrono::DateTime<chrono::Utc>) -> u64 {
        let log = self.error_log.lock().unwrap();
        log.iter()
            .filter(|error| error.timestamp() > cutoff_time)
            .count() as u64
    }

    /// 检查并发送告警
    fn check_and_send_alert(&self) {
        let now = Instant::now();
        let mut last_alert = self.last_alert.lock().unwrap();
        
        // 检查告警间隔
        if let Some(last) = *last_alert {
            if now.duration_since(last) < self.alert_config.alert_interval {
                return;
            }
        }

        let stats = self.error_stats.lock().unwrap();
        let mut should_alert = false;
        let mut alert_reasons = Vec::new();

        // 检查错误数量阈值
        if stats.total_errors >= self.alert_config.error_count_threshold {
            should_alert = true;
            alert_reasons.push(format!(
                "错误数量超过阈值: {} >= {}",
                stats.total_errors,
                self.alert_config.error_count_threshold
            ));
        }

        // 检查错误率阈值
        if stats.error_rate >= self.alert_config.error_rate_threshold {
            should_alert = true;
            alert_reasons.push(format!(
                "错误率超过阈值: {:.2}% >= {:.2}%",
                stats.error_rate * 100.0,
                self.alert_config.error_rate_threshold * 100.0
            ));
        }

        // 检查严重错误阈值
        let critical_count = stats.errors_by_severity
            .get("Critical")
            .copied()
            .unwrap_or(0);
        if critical_count >= self.alert_config.critical_error_threshold {
            should_alert = true;
            alert_reasons.push(format!(
                "严重错误数量超过阈值: {} >= {}",
                critical_count,
                self.alert_config.critical_error_threshold
            ));
        }

        if should_alert {
            self.send_alert(&alert_reasons);
            *last_alert = Some(now);
        }
    }

    /// 发送告警
    fn send_alert(&self, reasons: &[String]) {
        let alert_message = format!(
            "错误监控告警:\n{}\n\n当前统计:\n{}",
            reasons.join("\n"),
            self.generate_stats_report()
        );

        error!("{}", alert_message);

        // 这里可以集成实际的告警系统，如：
        // - 发送邮件
        // - 发送短信
        // - 推送到Slack/钉钉
        // - 调用Webhook
        for recipient in &self.alert_config.recipients {
            debug!("发送告警到: {}", recipient);
            // 实际实现中这里会调用相应的告警服务
        }
    }

    /// 获取错误统计
    pub fn get_error_stats(&self) -> ErrorStats {
        self.error_stats.lock().unwrap().clone()
    }

    /// 获取最近的错误
    pub fn get_recent_errors(&self, count: usize) -> Vec<UnifiedError> {
        let log = self.error_log.lock().unwrap();
        let start = if log.len() > count {
            log.len() - count
        } else {
            0
        };
        log[start..].to_vec()
    }

    /// 获取指定时间范围内的错误
    pub fn get_errors_in_range(&self, start: chrono::DateTime<chrono::Utc>, end: chrono::DateTime<chrono::Utc>) -> Vec<UnifiedError> {
        let log = self.error_log.lock().unwrap();
        log.iter()
            .filter(|error| {
                let timestamp = error.timestamp();
                timestamp >= start && timestamp <= end
            })
            .cloned()
            .collect()
    }

    /// 按严重程度获取错误
    pub fn get_errors_by_severity(&self, severity: ErrorSeverity) -> Vec<UnifiedError> {
        let log = self.error_log.lock().unwrap();
        log.iter()
            .filter(|error| error.severity() == severity)
            .cloned()
            .collect()
    }

    /// 按分类获取错误
    pub fn get_errors_by_category(&self, category: &str) -> Vec<UnifiedError> {
        let log = self.error_log.lock().unwrap();
        log.iter()
            .filter(|error| error.category() == category)
            .cloned()
            .collect()
    }

    /// 生成统计报告
    pub fn generate_stats_report(&self) -> String {
        let stats = self.error_stats.lock().unwrap();
        let mut report = String::new();

        report.push_str(&format!("总错误数: {}\n", stats.total_errors));
        report.push_str(&format!("最近1小时错误数: {}\n", stats.recent_errors));
        report.push_str(&format!("错误率: {:.2}%\n", stats.error_rate * 100.0));
        report.push_str(&format!("最后更新: {}\n", stats.last_updated.format("%Y-%m-%d %H:%M:%S UTC")));

        report.push_str("\n按严重程度统计:\n");
        for (severity, count) in &stats.errors_by_severity {
            report.push_str(&format!("  {}: {}\n", severity, count));
        }

        report.push_str("\n按分类统计:\n");
        for (category, count) in &stats.errors_by_category {
            report.push_str(&format!("  {}: {}\n", category, count));
        }

        report.push_str("\n按模块统计:\n");
        for (module, count) in &stats.errors_by_module {
            report.push_str(&format!("  {}: {}\n", module, count));
        }

        report
    }

    /// 清空错误日志
    pub fn clear_errors(&self) {
        self.error_log.lock().unwrap().clear();
        *self.error_stats.lock().unwrap() = ErrorStats::default();
    }

    /// 更新错误率
    pub fn update_error_rate(&self, total_operations: u64) {
        let mut stats = self.error_stats.lock().unwrap();
        if total_operations > 0 {
            stats.error_rate = stats.total_errors as f64 / total_operations as f64;
        } else {
            stats.error_rate = 0.0;
        }
        stats.last_updated = chrono::Utc::now();
    }

    /// 设置告警配置
    pub fn set_alert_config(&mut self, config: AlertConfig) {
        self.alert_config = config;
    }

    /// 获取告警配置
    pub fn get_alert_config(&self) -> &AlertConfig {
        &self.alert_config
    }
}

/// 全局错误监控器
pub struct GlobalErrorMonitor {
    monitor: Arc<ErrorMonitor>,
}

impl GlobalErrorMonitor {
    /// 创建全局错误监控器
    pub fn new() -> Self {
        let alert_config = AlertConfig::default();
        Self {
            monitor: Arc::new(ErrorMonitor::new(1000, alert_config)),
        }
    }

    /// 初始化全局错误监控器
    pub async fn init() -> Result<(), UnifiedError> {
        info!("全局错误监控器初始化完成");
        Ok(())
    }

    /// 关闭全局错误监控器
    pub async fn shutdown() -> Result<(), UnifiedError> {
        info!("全局错误监控器关闭完成");
        Ok(())
    }

    /// 记录错误到全局监控器
    pub fn record_error(&self, error: UnifiedError) {
        self.monitor.record_error(error);
    }

    /// 获取全局错误统计
    pub fn get_global_stats(&self) -> ErrorStats {
        self.monitor.get_error_stats()
    }

    /// 获取全局错误监控器实例
    pub fn get_monitor(&self) -> Arc<ErrorMonitor> {
        self.monitor.clone()
    }
}

/// 错误监控构建器
pub struct ErrorMonitorBuilder {
    max_log_size: Option<usize>,
    alert_config: Option<AlertConfig>,
}

impl ErrorMonitorBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            max_log_size: None,
            alert_config: None,
        }
    }

    /// 设置最大日志大小
    pub fn max_log_size(mut self, size: usize) -> Self {
        self.max_log_size = Some(size);
        self
    }

    /// 设置告警配置
    pub fn alert_config(mut self, config: AlertConfig) -> Self {
        self.alert_config = Some(config);
        self
    }

    /// 构建错误监控器
    pub fn build(self) -> ErrorMonitor {
        let max_log_size = self.max_log_size.unwrap_or(1000);
        let alert_config = self.alert_config.unwrap_or_default();
        
        ErrorMonitor::new(max_log_size, alert_config)
    }
}

impl Default for ErrorMonitorBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;
    use crate::error_handling::ErrorContext;

    #[test]
    fn test_error_stats_default() {
        let stats = ErrorStats::default();
        assert_eq!(stats.total_errors, 0);
        assert_eq!(stats.recent_errors, 0);
        assert_eq!(stats.error_rate, 0.0);
    }

    #[test]
    fn test_alert_config_default() {
        let config = AlertConfig::default();
        assert_eq!(config.error_count_threshold, 100);
        assert_eq!(config.error_rate_threshold, 0.1);
        assert!(config.enabled);
    }

    #[test]
    fn test_error_monitor_creation() {
        let monitor = ErrorMonitor::new(100, AlertConfig::default());
        let stats = monitor.get_error_stats();
        assert_eq!(stats.total_errors, 0);
    }

    #[test]
    fn test_error_monitor_record_error() {
        let monitor = ErrorMonitor::new(100, AlertConfig::default());
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        let error = UnifiedError::new("测试错误", ErrorSeverity::High, "test", context);
        
        monitor.record_error(error);
        
        let stats = monitor.get_error_stats();
        assert_eq!(stats.total_errors, 1);
        assert_eq!(stats.errors_by_severity.get("High"), Some(&1));
        assert_eq!(stats.errors_by_category.get("test"), Some(&1));
    }

    #[test]
    fn test_error_monitor_recent_errors() {
        let monitor = ErrorMonitor::new(100, AlertConfig::default());
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        
        for i in 0..5 {
            let error = UnifiedError::new(&format!("错误 {}", i), ErrorSeverity::Low, "test", context.clone());
            monitor.record_error(error);
        }
        
        let recent = monitor.get_recent_errors(3);
        assert_eq!(recent.len(), 3);
    }

    #[test]
    fn test_error_monitor_builder() {
        let alert_config = AlertConfig {
            error_count_threshold: 50,
            error_rate_threshold: 0.05,
            critical_error_threshold: 5,
            alert_interval: Duration::from_secs(600),
            enabled: true,
            recipients: vec!["admin@example.com".to_string()],
        };

        let monitor = ErrorMonitorBuilder::new()
            .max_log_size(500)
            .alert_config(alert_config.clone())
            .build();

        let config = monitor.get_alert_config();
        assert_eq!(config.error_count_threshold, 50);
        assert_eq!(config.recipients.len(), 1);
    }

    #[test]
    fn test_global_error_monitor() {
        let global_monitor = GlobalErrorMonitor::new();
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        let error = UnifiedError::new("全局错误", ErrorSeverity::Critical, "global", context);
        
        global_monitor.record_error(error);
        
        let stats = global_monitor.get_global_stats();
        assert_eq!(stats.total_errors, 1);
        assert_eq!(stats.errors_by_severity.get("Critical"), Some(&1));
    }

    #[test]
    fn test_error_monitor_update_error_rate() {
        let monitor = ErrorMonitor::new(100, AlertConfig::default());
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        
        // 记录一些错误
        for i in 0..10 {
            let error = UnifiedError::new(&format!("错误 {}", i), ErrorSeverity::Low, "test", context.clone());
            monitor.record_error(error);
        }
        
        // 更新错误率
        monitor.update_error_rate(1000);
        
        let stats = monitor.get_error_stats();
        assert_eq!(stats.error_rate, 0.01); // 10/1000 = 0.01
    }
}
