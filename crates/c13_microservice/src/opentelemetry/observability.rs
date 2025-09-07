//! 可观测性模块
//! 
//! 提供健康检查、性能监控、错误追踪和系统状态报告功能

use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{SystemTime, UNIX_EPOCH, Duration, Instant};
use tracing::{info, warn, error, debug};
use serde::{Serialize, Deserialize};

// 使用前向声明避免循环依赖
// 这些类型将在运行时通过参数传递

/// 日志统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogStatistics {
    pub total_count: u64,
    pub error_count: u64,
    pub warn_count: u64,
    pub info_count: u64,
    pub debug_count: u64,
}

/// 健康检查状态
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
}

impl ToString for HealthStatus {
    fn to_string(&self) -> String {
        match self {
            HealthStatus::Healthy => "healthy".to_string(),
            HealthStatus::Degraded => "degraded".to_string(),
            HealthStatus::Unhealthy => "unhealthy".to_string(),
        }
    }
}

/// 健康检查结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheck {
    pub name: String,
    pub status: HealthStatus,
    pub message: String,
    pub timestamp: u64,
    pub duration_ms: u64,
    pub details: HashMap<String, String>,
}

/// 健康检查器trait
pub trait HealthChecker {
    fn name(&self) -> &str;
    fn check(&self) -> HealthCheck;
}

/// 数据库健康检查器
#[derive(Debug)]
pub struct DatabaseHealthChecker {
    name: String,
    connection_string: String,
}

impl DatabaseHealthChecker {
    pub fn new(name: String, connection_string: String) -> Self {
        Self { name, connection_string }
    }
}

impl HealthChecker for DatabaseHealthChecker {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn check(&self) -> HealthCheck {
        let start_time = Instant::now();
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        // 模拟数据库连接检查
        let mut details = HashMap::new();
        details.insert("connection_string".to_string(), self.connection_string.clone());
        
        // 这里应该实际检查数据库连接
        // 为了演示，我们模拟一个健康的检查
        let status = HealthStatus::Healthy;
        let message = "Database connection is healthy".to_string();
        
        let duration_ms = start_time.elapsed().as_millis() as u64;
        
        HealthCheck {
            name: self.name.clone(),
            status,
            message,
            timestamp,
            duration_ms,
            details,
        }
    }
}

/// Redis健康检查器
#[derive(Debug)]
pub struct RedisHealthChecker {
    name: String,
    redis_url: String,
}

impl RedisHealthChecker {
    pub fn new(name: String, redis_url: String) -> Self {
        Self { name, redis_url }
    }
}

impl HealthChecker for RedisHealthChecker {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn check(&self) -> HealthCheck {
        let start_time = Instant::now();
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let mut details = HashMap::new();
        details.insert("redis_url".to_string(), self.redis_url.clone());
        
        // 模拟Redis连接检查
        let status = HealthStatus::Healthy;
        let message = "Redis connection is healthy".to_string();
        
        let duration_ms = start_time.elapsed().as_millis() as u64;
        
        HealthCheck {
            name: self.name.clone(),
            status,
            message,
            timestamp,
            duration_ms,
            details,
        }
    }
}

/// 系统资源健康检查器
#[derive(Debug)]
pub struct SystemResourceHealthChecker {
    name: String,
    max_cpu_usage: f64,
    max_memory_usage: f64,
}

impl SystemResourceHealthChecker {
    pub fn new(name: String, max_cpu_usage: f64, max_memory_usage: f64) -> Self {
        Self {
            name,
            max_cpu_usage,
            max_memory_usage,
        }
    }
}

impl HealthChecker for SystemResourceHealthChecker {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn check(&self) -> HealthCheck {
        let start_time = Instant::now();
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let mut details = HashMap::new();
        
        // 模拟获取系统资源使用情况
        let cpu_usage = 25.5; // 模拟CPU使用率
        let memory_usage = 60.0; // 模拟内存使用率
        
        details.insert("cpu_usage_percent".to_string(), cpu_usage.to_string());
        details.insert("memory_usage_percent".to_string(), memory_usage.to_string());
        details.insert("max_cpu_threshold".to_string(), self.max_cpu_usage.to_string());
        details.insert("max_memory_threshold".to_string(), self.max_memory_usage.to_string());
        
        let (status, message) = if cpu_usage > self.max_cpu_usage || memory_usage > self.max_memory_usage {
            (HealthStatus::Unhealthy, "System resources exceeded thresholds".to_string())
        } else if cpu_usage > self.max_cpu_usage * 0.8 || memory_usage > self.max_memory_usage * 0.8 {
            (HealthStatus::Degraded, "System resources approaching thresholds".to_string())
        } else {
            (HealthStatus::Healthy, "System resources are healthy".to_string())
        };
        
        let duration_ms = start_time.elapsed().as_millis() as u64;
        
        HealthCheck {
            name: self.name.clone(),
            status,
            message,
            timestamp,
            duration_ms,
            details,
        }
    }
}

/// 性能监控器
pub struct PerformanceMonitor {
    performance_data: Arc<RwLock<HashMap<String, PerformanceData>>>,
    alert_thresholds: Arc<RwLock<HashMap<String, f64>>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceData {
    pub operation: String,
    pub avg_duration_ms: f64,
    pub max_duration_ms: f64,
    pub min_duration_ms: f64,
    pub p95_duration_ms: f64,
    pub p99_duration_ms: f64,
    pub total_calls: u64,
    pub error_rate: f64,
    pub last_updated: u64,
}

impl PerformanceMonitor {
    pub fn new() -> Self {
        Self {
            performance_data: Arc::new(RwLock::new(HashMap::new())),
            alert_thresholds: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 设置性能告警阈值
    pub fn set_alert_threshold(&self, operation: &str, threshold_ms: f64) {
        if let Ok(mut thresholds) = self.alert_thresholds.write() {
            thresholds.insert(operation.to_string(), threshold_ms);
        }
    }
    
    /// 记录操作性能
    pub fn record_operation(&self, operation: &str, duration: Duration, success: bool) {
        let duration_ms = duration.as_millis() as f64;
        
        // 注意：这里应该记录到指标收集器，但PerformanceMonitor没有metrics字段
        // 在实际使用中，应该通过OpenTelemetryManager来记录指标
        
        // 更新性能数据
        if let Ok(mut data) = self.performance_data.write() {
            let entry = data.entry(operation.to_string()).or_insert_with(|| PerformanceData {
                operation: operation.to_string(),
                avg_duration_ms: 0.0,
                max_duration_ms: 0.0,
                min_duration_ms: f64::MAX,
                p95_duration_ms: 0.0,
                p99_duration_ms: 0.0,
                total_calls: 0,
                error_rate: 0.0,
                last_updated: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(),
            });
            
            entry.total_calls += 1;
            entry.max_duration_ms = entry.max_duration_ms.max(duration_ms);
            entry.min_duration_ms = entry.min_duration_ms.min(duration_ms);
            
            // 简化的平均值计算
            entry.avg_duration_ms = (entry.avg_duration_ms * (entry.total_calls - 1) as f64 + duration_ms) / entry.total_calls as f64;
            
            if !success {
                entry.error_rate = (entry.error_rate * (entry.total_calls - 1) as f64 + 1.0) / entry.total_calls as f64;
            }
            
            entry.last_updated = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        }
        
        // 检查告警阈值
        self.check_performance_alerts(operation, duration_ms);
    }
    
    /// 检查性能告警
    fn check_performance_alerts(&self, operation: &str, duration_ms: f64) {
        if let Ok(thresholds) = self.alert_thresholds.read() {
            if let Some(threshold) = thresholds.get(operation) {
                if duration_ms > *threshold {
                    warn!("Performance alert: {} took {}ms, exceeding threshold of {}ms", 
                          operation, duration_ms, threshold);
                }
            }
        }
    }
    
    /// 获取操作性能数据
    pub fn get_operation_performance(&self, operation: &str) -> Option<PerformanceData> {
        if let Ok(data) = self.performance_data.read() {
            data.get(operation).cloned()
        } else {
            None
        }
    }
    
    /// 获取所有性能数据
    pub fn get_all_performance_data(&self) -> HashMap<String, PerformanceData> {
        if let Ok(data) = self.performance_data.read() {
            data.clone()
        } else {
            HashMap::new()
        }
    }
    
    /// 获取性能摘要
    pub fn get_performance_summary(&self) -> PerformanceSummary {
        if let Ok(data) = self.performance_data.read() {
            let mut total_operations = 0;
            let mut total_errors = 0;
            let mut avg_response_time = 0.0;
            let mut slowest_operation = String::new();
            let mut max_duration = 0.0;
            
            for (operation, perf_data) in data.iter() {
                total_operations += perf_data.total_calls;
                total_errors += (perf_data.error_rate * perf_data.total_calls as f64) as u64;
                avg_response_time += perf_data.avg_duration_ms;
                
                if perf_data.max_duration_ms > max_duration {
                    max_duration = perf_data.max_duration_ms;
                    slowest_operation = operation.clone();
                }
            }
            
            if !data.is_empty() {
                avg_response_time /= data.len() as f64;
            }
            
            PerformanceSummary {
                total_operations,
                total_errors,
                error_rate: if total_operations > 0 { total_errors as f64 / total_operations as f64 } else { 0.0 },
                avg_response_time_ms: avg_response_time,
                slowest_operation,
                max_duration_ms: max_duration,
                monitored_operations: data.len(),
            }
        } else {
            PerformanceSummary::default()
        }
    }
}

#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct PerformanceSummary {
    pub total_operations: u64,
    pub total_errors: u64,
    pub error_rate: f64,
    pub avg_response_time_ms: f64,
    pub slowest_operation: String,
    pub max_duration_ms: f64,
    pub monitored_operations: usize,
}

/// 错误追踪器
#[derive(Debug)]
pub struct ErrorTracker {
    errors: Arc<RwLock<Vec<ErrorRecord>>>,
    error_patterns: Arc<RwLock<HashMap<String, u64>>>,
    alert_thresholds: Arc<RwLock<HashMap<String, u64>>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorRecord {
    pub id: String,
    pub error_type: String,
    pub message: String,
    pub stack_trace: Option<String>,
    pub context: HashMap<String, String>,
    pub timestamp: u64,
    pub severity: ErrorSeverity,
    pub resolved: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum ErrorSeverity {
    Low,
    Medium,
    High,
    Critical,
}

impl ToString for ErrorSeverity {
    fn to_string(&self) -> String {
        match self {
            ErrorSeverity::Low => "low".to_string(),
            ErrorSeverity::Medium => "medium".to_string(),
            ErrorSeverity::High => "high".to_string(),
            ErrorSeverity::Critical => "critical".to_string(),
        }
    }
}

impl ErrorTracker {
    pub fn new() -> Self {
        Self {
            errors: Arc::new(RwLock::new(Vec::new())),
            error_patterns: Arc::new(RwLock::new(HashMap::new())),
            alert_thresholds: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 记录错误
    pub fn record_error(&self, error_type: &str, message: &str, context: HashMap<String, String>, severity: ErrorSeverity) -> String {
        let error_id = format!("err_{}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis());
        let timestamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        
        let error_record = ErrorRecord {
            id: error_id.clone(),
            error_type: error_type.to_string(),
            message: message.to_string(),
            stack_trace: None, // 在实际实现中应该捕获堆栈跟踪
            context,
            timestamp,
            severity,
            resolved: false,
        };
        
        // 添加到错误列表
        if let Ok(mut errors) = self.errors.write() {
            errors.push(error_record.clone());
            
            // 保持最近1000个错误
            if errors.len() > 1000 {
                let excess = errors.len() - 1000;
                errors.drain(0..excess);
            }
        }
        
        // 更新错误模式统计
        if let Ok(mut patterns) = self.error_patterns.write() {
            *patterns.entry(error_type.to_string()).or_insert(0) += 1;
        }
        
        // 检查告警
        self.check_error_alerts(error_type);
        
        // 记录日志
        match severity {
            ErrorSeverity::Low => debug!("Error recorded: {} - {}", error_type, message),
            ErrorSeverity::Medium => info!("Error recorded: {} - {}", error_type, message),
            ErrorSeverity::High => warn!("Error recorded: {} - {}", error_type, message),
            ErrorSeverity::Critical => error!("Critical error recorded: {} - {}", error_type, message),
        }
        
        error_id
    }
    
    /// 设置错误告警阈值
    pub fn set_error_alert_threshold(&self, error_type: &str, threshold: u64) {
        if let Ok(mut thresholds) = self.alert_thresholds.write() {
            thresholds.insert(error_type.to_string(), threshold);
        }
    }
    
    /// 检查错误告警
    fn check_error_alerts(&self, error_type: &str) {
        if let Ok(thresholds) = self.alert_thresholds.read() {
            if let Some(threshold) = thresholds.get(error_type) {
                if let Ok(patterns) = self.error_patterns.read() {
                    if let Some(count) = patterns.get(error_type) {
                        if *count >= *threshold {
                            error!("Error alert: {} errors of type '{}' exceeded threshold of {}", 
                                   count, error_type, threshold);
                        }
                    }
                }
            }
        }
    }
    
    /// 获取错误统计
    pub fn get_error_statistics(&self) -> ErrorStatistics {
        if let Ok(errors) = self.errors.read() {
            let mut stats = ErrorStatistics::default();
            
            for error in errors.iter() {
                stats.total_errors += 1;
                
                match error.severity {
                    ErrorSeverity::Low => stats.low_severity += 1,
                    ErrorSeverity::Medium => stats.medium_severity += 1,
                    ErrorSeverity::High => stats.high_severity += 1,
                    ErrorSeverity::Critical => stats.critical_severity += 1,
                }
                
                if error.resolved {
                    stats.resolved_errors += 1;
                }
            }
            
            stats.unresolved_errors = stats.total_errors - stats.resolved_errors;
            stats
        } else {
            ErrorStatistics::default()
        }
    }
    
    /// 获取错误模式
    pub fn get_error_patterns(&self) -> HashMap<String, u64> {
        if let Ok(patterns) = self.error_patterns.read() {
            patterns.clone()
        } else {
            HashMap::new()
        }
    }
    
    /// 获取最近的错误
    pub fn get_recent_errors(&self, count: usize) -> Vec<ErrorRecord> {
        if let Ok(errors) = self.errors.read() {
            errors.iter().rev().take(count).cloned().collect()
        } else {
            Vec::new()
        }
    }
    
    /// 标记错误为已解决
    pub fn resolve_error(&self, error_id: &str) -> bool {
        if let Ok(mut errors) = self.errors.write() {
            for error in errors.iter_mut() {
                if error.id == error_id {
                    error.resolved = true;
                    return true;
                }
            }
        }
        false
    }
}

#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct ErrorStatistics {
    pub total_errors: u64,
    pub resolved_errors: u64,
    pub unresolved_errors: u64,
    pub low_severity: u64,
    pub medium_severity: u64,
    pub high_severity: u64,
    pub critical_severity: u64,
}

/// 系统状态报告器
pub struct SystemStatusReporter {
    health_checkers: Vec<Box<dyn HealthChecker + Send + Sync>>,
    performance_monitor: Arc<PerformanceMonitor>,
    error_tracker: Arc<ErrorTracker>,
}

impl SystemStatusReporter {
    pub fn new(
        performance_monitor: Arc<PerformanceMonitor>,
        error_tracker: Arc<ErrorTracker>,
    ) -> Self {
        Self {
            health_checkers: Vec::new(),
            performance_monitor,
            error_tracker,
        }
    }
    
    /// 添加健康检查器
    pub fn add_health_checker(&mut self, checker: Box<dyn HealthChecker + Send + Sync>) {
        self.health_checkers.push(checker);
    }
    
    /// 生成完整的系统状态报告
    pub fn generate_system_report(&self) -> SystemReport {
        let timestamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        
        // 执行健康检查
        let mut health_checks = Vec::new();
        for checker in &self.health_checkers {
            health_checks.push(checker.check());
        }
        
        // 获取性能数据
        let performance_summary = self.performance_monitor.get_performance_summary();
        
        // 获取错误统计
        let error_statistics = self.error_tracker.get_error_statistics();
        
        // 获取日志统计（使用默认值）
        let log_statistics = LogStatistics {
            total_count: 0,
            error_count: 0,
            warn_count: 0,
            info_count: 0,
            debug_count: 0,
        };
        
        // 获取指标统计（使用默认值）
        let metrics_summary = MetricsSummary {
            total_counters: 0,
            total_gauges: 0,
            total_histograms: 0,
            total_timers: 0,
        };
        
        // 获取追踪统计（使用默认值）
        let tracing_summary = TracingSummary {
            active_spans: 0,
            total_spans: 0,
        };
        
        // 计算整体健康状态
        let overall_health = self.calculate_overall_health(&health_checks, &error_statistics, &performance_summary);
        
        SystemReport {
            timestamp,
            overall_health,
            health_checks,
            performance_summary,
            error_statistics,
            log_statistics,
            metrics_summary,
            tracing_summary,
        }
    }
    
    /// 计算整体健康状态
    fn calculate_overall_health(
        &self,
        health_checks: &[HealthCheck],
        error_stats: &ErrorStatistics,
        perf_summary: &PerformanceSummary,
    ) -> HealthStatus {
        // 检查健康检查结果
        for check in health_checks {
            match check.status {
                HealthStatus::Unhealthy => return HealthStatus::Unhealthy,
                HealthStatus::Degraded => return HealthStatus::Degraded,
                HealthStatus::Healthy => continue,
            }
        }
        
        // 检查错误率
        if error_stats.critical_severity > 0 {
            return HealthStatus::Unhealthy;
        }
        
        let error_rate = if error_stats.total_errors > 0 { 
            error_stats.unresolved_errors as f64 / error_stats.total_errors as f64 
        } else { 
            0.0 
        };
        if error_rate > 0.1 { // 10%错误率
            return HealthStatus::Degraded;
        }
        
        // 检查性能
        if perf_summary.avg_response_time_ms > 5000.0 { // 5秒平均响应时间
            return HealthStatus::Degraded;
        }
        
        HealthStatus::Healthy
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemReport {
    pub timestamp: u64,
    pub overall_health: HealthStatus,
    pub health_checks: Vec<HealthCheck>,
    pub performance_summary: PerformanceSummary,
    pub error_statistics: ErrorStatistics,
    pub log_statistics: LogStatistics,
    pub metrics_summary: MetricsSummary,
    pub tracing_summary: TracingSummary,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricsSummary {
    pub total_counters: usize,
    pub total_gauges: usize,
    pub total_histograms: usize,
    pub total_timers: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TracingSummary {
    pub active_spans: usize,
    pub total_spans: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_health_check() {
        let checker = DatabaseHealthChecker::new(
            "database".to_string(),
            "postgresql://localhost:5432/test".to_string(),
        );
        
        let result = checker.check();
        assert_eq!(result.name, "database");
        assert!(matches!(result.status, HealthStatus::Healthy));
    }
    
    #[test]
    fn test_performance_monitor() {
        let monitor = PerformanceMonitor::new();
        
        monitor.record_operation("test_op", Duration::from_millis(100), true);
        monitor.record_operation("test_op", Duration::from_millis(200), false);
        
        let perf_data = monitor.get_operation_performance("test_op");
        assert!(perf_data.is_some());
        let data = perf_data.unwrap();
        assert_eq!(data.total_calls, 2);
        assert!(data.error_rate > 0.0);
    }
    
    #[test]
    fn test_error_tracker() {
        let tracker = ErrorTracker::new();
        
        let mut context = HashMap::new();
        context.insert("user_id".to_string(), "123".to_string());
        
        let error_id = tracker.record_error(
            "database_error",
            "Connection failed",
            context,
            ErrorSeverity::High,
        );
        
        assert!(!error_id.is_empty());
        
        let stats = tracker.get_error_statistics();
        assert_eq!(stats.total_errors, 1);
        assert_eq!(stats.high_severity, 1);
    }
}
