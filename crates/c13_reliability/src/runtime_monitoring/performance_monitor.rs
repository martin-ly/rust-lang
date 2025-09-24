//! 性能监控实现
//!
//! 提供系统性能监控功能，包括响应时间、吞吐量、错误率等性能指标。

use std::sync::Arc;
use std::collections::HashMap;
use std::time::Duration;
use serde::{Serialize, Deserialize};
use tracing::{debug, error, info};

use crate::error_handling::UnifiedError;
use super::MonitoringState;

/// 性能监控配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMonitorConfig {
    /// 监控间隔
    pub monitor_interval: Duration,
    /// 是否启用性能监控
    pub enabled: bool,
    /// 监控项目
    pub monitors: Vec<PerformanceMonitorItem>,
    /// 告警阈值
    pub alert_thresholds: PerformanceAlertThresholds,
}

impl Default for PerformanceMonitorConfig {
    fn default() -> Self {
        Self {
            monitor_interval: Duration::from_secs(5),
            enabled: true,
            monitors: vec![
                PerformanceMonitorItem {
                    name: "response_time".to_string(),
                    monitor_type: PerformanceMonitorType::ResponseTime,
                    enabled: true,
                },
                PerformanceMonitorItem {
                    name: "throughput".to_string(),
                    monitor_type: PerformanceMonitorType::Throughput,
                    enabled: true,
                },
                PerformanceMonitorItem {
                    name: "error_rate".to_string(),
                    monitor_type: PerformanceMonitorType::ErrorRate,
                    enabled: true,
                },
            ],
            alert_thresholds: PerformanceAlertThresholds::default(),
        }
    }
}

/// 性能监控项目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMonitorItem {
    /// 监控名称
    pub name: String,
    /// 监控类型
    pub monitor_type: PerformanceMonitorType,
    /// 是否启用
    pub enabled: bool,
}

/// 性能监控类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PerformanceMonitorType {
    /// 响应时间监控
    ResponseTime,
    /// 吞吐量监控
    Throughput,
    /// 错误率监控
    ErrorRate,
    /// 自定义监控
    Custom {
        name: String,
        parameters: HashMap<String, String>,
    },
}

/// 性能告警阈值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceAlertThresholds {
    /// 响应时间阈值（毫秒）
    pub response_time_threshold: u64,
    /// 吞吐量阈值（请求/秒）
    pub throughput_threshold: u64,
    /// 错误率阈值（百分比）
    pub error_rate_threshold: f64,
}

impl Default for PerformanceAlertThresholds {
    fn default() -> Self {
        Self {
            response_time_threshold: 1000, // 1秒
            throughput_threshold: 1000,    // 1000请求/秒
            error_rate_threshold: 5.0,     // 5%
        }
    }
}

/// 性能监控结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMonitorResult {
    /// 监控时间
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 整体状态
    pub state: MonitoringState,
    /// 监控项目结果
    pub items: Vec<PerformanceMonitorItemResult>,
    /// 总监控数
    pub total_monitors: usize,
    /// 正常监控数
    pub healthy_monitors: usize,
    /// 警告监控数
    pub warning_monitors: usize,
    /// 错误监控数
    pub error_monitors: usize,
}

/// 性能监控项目结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMonitorItemResult {
    /// 监控名称
    pub name: String,
    /// 监控类型
    pub monitor_type: PerformanceMonitorType,
    /// 状态
    pub state: MonitoringState,
    /// 当前值
    pub current_value: f64,
    /// 平均值
    pub average_value: f64,
    /// 最大值
    pub max_value: f64,
    /// 最小值
    pub min_value: f64,
    /// 详细信息
    pub details: HashMap<String, String>,
}

/// 性能监控器
pub struct PerformanceMonitor {
    config: PerformanceMonitorConfig,
    is_running: std::sync::atomic::AtomicBool,
    last_result: std::sync::Mutex<Option<PerformanceMonitorResult>>,
    monitor_handlers: std::sync::Mutex<HashMap<String, Box<dyn PerformanceMonitorHandler + Send + Sync>>>,
    metrics: std::sync::Mutex<HashMap<String, Vec<f64>>>,
}

impl PerformanceMonitor {
    /// 创建新的性能监控器
    pub fn new(config: PerformanceMonitorConfig) -> Self {
        Self {
            config,
            is_running: std::sync::atomic::AtomicBool::new(false),
            last_result: std::sync::Mutex::new(None),
            monitor_handlers: std::sync::Mutex::new(HashMap::new()),
            metrics: std::sync::Mutex::new(HashMap::new()),
        }
    }

    /// 启动性能监控
    pub async fn start(&self) -> Result<(), UnifiedError> {
        if self.is_running.load(std::sync::atomic::Ordering::Relaxed) {
            return Ok(());
        }

        if !self.config.enabled {
            debug!("性能监控已禁用");
            return Ok(());
        }

        self.is_running.store(true, std::sync::atomic::Ordering::Relaxed);
        
        // 注册默认监控处理器
        self.register_default_handlers();

        // 启动监控循环
        let monitor = Arc::new(self.clone());
        tokio::spawn(async move {
            monitor.run_monitor_loop().await;
        });

        info!("性能监控器启动完成");
        Ok(())
    }

    /// 停止性能监控
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.is_running.store(false, std::sync::atomic::Ordering::Relaxed);
        info!("性能监控器停止完成");
        Ok(())
    }

    /// 获取性能状态
    pub async fn get_status(&self) -> Result<PerformanceMonitorResult, UnifiedError> {
        let mut items = Vec::new();
        let mut total_monitors = 0;
        let mut healthy_monitors = 0;
        let mut warning_monitors = 0;
        let mut error_monitors = 0;

        for monitor_item in &self.config.monitors {
            if !monitor_item.enabled {
                continue;
            }

            total_monitors += 1;
            let item_result = self.monitor_item(monitor_item).await;
            
            match item_result.state {
                MonitoringState::Healthy => healthy_monitors += 1,
                MonitoringState::Warning => warning_monitors += 1,
                MonitoringState::Error | MonitoringState::Critical => error_monitors += 1,
            }
            
            items.push(item_result);
        }

        let overall_state = self.calculate_overall_state(&items);
        let result = PerformanceMonitorResult {
            timestamp: chrono::Utc::now(),
            state: overall_state,
            items,
            total_monitors,
            healthy_monitors,
            warning_monitors,
            error_monitors,
        };

        // 保存结果
        *self.last_result.lock().unwrap() = Some(result.clone());

        Ok(result)
    }

    /// 监控单个项目
    async fn monitor_item(&self, item: &PerformanceMonitorItem) -> PerformanceMonitorItemResult {
        // 直接执行监控，避免复杂的生命周期问题
        let result = match item.name.as_str() {
            "response_time" => ResponseTimePerformanceMonitorHandler.monitor().await,
            "throughput" => ThroughputPerformanceMonitorHandler.monitor().await,
            "error_rate" => ErrorRatePerformanceMonitorHandler.monitor().await,
            _ => Ok(PerformanceMonitorItemResult {
                name: item.name.clone(),
                monitor_type: item.monitor_type.clone(),
                state: MonitoringState::Error,
                current_value: 0.0,
                average_value: 0.0,
                max_value: 0.0,
                min_value: 0.0,
                details: HashMap::new(),
            })
        };

        match result {
            Ok(result) => {
                // 更新指标历史
                self.update_metrics(&item.name, result.current_value);
                result
            }
            Err(_error) => PerformanceMonitorItemResult {
                name: item.name.clone(),
                monitor_type: item.monitor_type.clone(),
                state: MonitoringState::Error,
                current_value: 0.0,
                average_value: 0.0,
                max_value: 0.0,
                min_value: 0.0,
                details: HashMap::new(),
            }
        }
    }

    /// 更新指标历史
    fn update_metrics(&self, name: &str, value: f64) {
        let mut metrics = self.metrics.lock().unwrap();
        let entry = metrics.entry(name.to_string()).or_insert_with(Vec::new);
        
        entry.push(value);
        
        // 保持最近1000个值
        if entry.len() > 1000 {
            entry.remove(0);
        }
    }

    /// 计算指标统计
    #[allow(dead_code)]
    fn calculate_metrics_stats(&self, name: &str) -> (f64, f64, f64, f64) {
        let metrics = self.metrics.lock().unwrap();
        
        if let Some(values) = metrics.get(name) {
            if values.is_empty() {
                return (0.0, 0.0, 0.0, 0.0);
            }
            
            let current = *values.last().unwrap();
            let average = values.iter().sum::<f64>() / values.len() as f64;
            let max = values.iter().fold(0.0f64, |a, &b| a.max(b));
            let min = values.iter().fold(f64::INFINITY, |a, &b| a.min(b));
            
            (current, average, max, min)
        } else {
            (0.0, 0.0, 0.0, 0.0)
        }
    }

    /// 计算整体状态
    fn calculate_overall_state(&self, items: &[PerformanceMonitorItemResult]) -> MonitoringState {
        if items.is_empty() {
            return MonitoringState::Healthy;
        }

        let states = items.iter().map(|item| &item.state).collect::<Vec<_>>();
        
        // 返回最严重的状态
        if states.contains(&&MonitoringState::Critical) {
            MonitoringState::Critical
        } else if states.contains(&&MonitoringState::Error) {
            MonitoringState::Error
        } else if states.contains(&&MonitoringState::Warning) {
            MonitoringState::Warning
        } else {
            MonitoringState::Healthy
        }
    }

    /// 注册默认监控处理器
    fn register_default_handlers(&self) {
        let mut handlers = self.monitor_handlers.lock().unwrap();
        
        handlers.insert("response_time".to_string(), Box::new(ResponseTimePerformanceMonitorHandler));
        handlers.insert("throughput".to_string(), Box::new(ThroughputPerformanceMonitorHandler));
        handlers.insert("error_rate".to_string(), Box::new(ErrorRatePerformanceMonitorHandler));
    }

    /// 注册自定义监控处理器
    pub fn register_handler(&self, name: String, handler: Box<dyn PerformanceMonitorHandler + Send + Sync>) {
        let mut handlers = self.monitor_handlers.lock().unwrap();
        handlers.insert(name, handler);
    }

    /// 运行监控循环
    async fn run_monitor_loop(&self) {
        let mut interval = tokio::time::interval(self.config.monitor_interval);
        
        while self.is_running.load(std::sync::atomic::Ordering::Relaxed) {
            interval.tick().await;
            
            if let Err(error) = self.get_status().await {
                error!("性能监控失败: {}", error);
            }
        }
    }

    /// 获取最后监控结果
    pub fn get_last_result(&self) -> Option<PerformanceMonitorResult> {
        self.last_result.lock().unwrap().clone()
    }

    /// 获取配置
    pub fn get_config(&self) -> &PerformanceMonitorConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: PerformanceMonitorConfig) {
        self.config = config;
    }
}

impl Clone for PerformanceMonitor {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            is_running: std::sync::atomic::AtomicBool::new(self.is_running.load(std::sync::atomic::Ordering::Relaxed)),
            last_result: std::sync::Mutex::new(self.last_result.lock().unwrap().clone()),
            monitor_handlers: std::sync::Mutex::new(HashMap::new()),
            metrics: std::sync::Mutex::new(HashMap::new()),
        }
    }
}

/// 性能监控处理器trait
pub trait PerformanceMonitorHandler: Send + Sync {
    /// 执行性能监控
    fn monitor(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<PerformanceMonitorItemResult, UnifiedError>> + Send>>;
}

/// 响应时间性能监控处理器
pub struct ResponseTimePerformanceMonitorHandler;

impl PerformanceMonitorHandler for ResponseTimePerformanceMonitorHandler {
    fn monitor(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<PerformanceMonitorItemResult, UnifiedError>> + Send>> {
        Box::pin(async move {
        let mut details = HashMap::new();
        let mut state = MonitoringState::Healthy;
        let current_value;

        // 模拟响应时间监控
        let start_time = std::time::Instant::now();
        
        // 这里应该实际测量响应时间
        // 简化实现，使用随机值
        use rand::Rng;
        let mut rng = rand::rng();
        current_value = rng.random_range(10.0..2000.0); // 10ms到2s
        
        let measurement_time = start_time.elapsed();
        details.insert("measurement_time_ms".to_string(), measurement_time.as_millis().to_string());
        details.insert("current_response_time_ms".to_string(), format!("{:.2}", current_value));

        // 根据阈值判断状态
        if current_value > 1000.0 {
            state = MonitoringState::Warning;
        }
        if current_value > 2000.0 {
            state = MonitoringState::Error;
        }

        Ok(PerformanceMonitorItemResult {
            name: "response_time".to_string(),
            monitor_type: PerformanceMonitorType::ResponseTime,
            state,
            current_value,
            average_value: current_value, // 简化实现
            max_value: current_value,
            min_value: current_value,
            details,
        })
        })
    }
}

/// 吞吐量性能监控处理器
pub struct ThroughputPerformanceMonitorHandler;

impl PerformanceMonitorHandler for ThroughputPerformanceMonitorHandler {
    fn monitor(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<PerformanceMonitorItemResult, UnifiedError>> + Send>> {
        Box::pin(async move {
        let mut details = HashMap::new();
        let mut state = MonitoringState::Healthy;
        let current_value;

        // 模拟吞吐量监控
        use rand::Rng;
        let mut rng = rand::rng();
        current_value = rng.random_range(100.0..2000.0); // 100到2000请求/秒
        
        details.insert("current_throughput_rps".to_string(), format!("{:.2}", current_value));

        // 根据阈值判断状态
        if current_value < 500.0 {
            state = MonitoringState::Warning;
        }
        if current_value < 100.0 {
            state = MonitoringState::Error;
        }

        Ok(PerformanceMonitorItemResult {
            name: "throughput".to_string(),
            monitor_type: PerformanceMonitorType::Throughput,
            state,
            current_value,
            average_value: current_value, // 简化实现
            max_value: current_value,
            min_value: current_value,
            details,
        })
        })
    }
}

/// 错误率性能监控处理器
pub struct ErrorRatePerformanceMonitorHandler;

impl PerformanceMonitorHandler for ErrorRatePerformanceMonitorHandler {
    fn monitor(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<PerformanceMonitorItemResult, UnifiedError>> + Send>> {
        Box::pin(async move {
        let mut details = HashMap::new();
        let mut state = MonitoringState::Healthy;
        let current_value;

        // 模拟错误率监控
        use rand::Rng;
        let mut rng = rand::rng();
        current_value = rng.random_range(0.0..10.0); // 0%到10%
        
        details.insert("current_error_rate_percent".to_string(), format!("{:.2}", current_value));

        // 根据阈值判断状态
        if current_value > 5.0 {
            state = MonitoringState::Warning;
        }
        if current_value > 10.0 {
            state = MonitoringState::Error;
        }

        Ok(PerformanceMonitorItemResult {
            name: "error_rate".to_string(),
            monitor_type: PerformanceMonitorType::ErrorRate,
            state,
            current_value,
            average_value: current_value, // 简化实现
            max_value: current_value,
            min_value: current_value,
            details,
        })
        })
    }
}

/// 全局性能监控器
pub struct GlobalPerformanceMonitor {
    monitor: Arc<PerformanceMonitor>,
}

impl GlobalPerformanceMonitor {
    /// 创建全局性能监控器
    pub fn new() -> Self {
        Self {
            monitor: Arc::new(PerformanceMonitor::new(PerformanceMonitorConfig::default())),
        }
    }

    /// 获取性能监控器实例
    pub fn get_monitor(&self) -> Arc<PerformanceMonitor> {
        self.monitor.clone()
    }

    /// 启动全局性能监控
    pub async fn start(&self) -> Result<(), UnifiedError> {
        self.monitor.start().await
    }

    /// 停止全局性能监控
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.monitor.stop().await
    }

    /// 获取全局性能状态
    pub async fn get_status(&self) -> Result<PerformanceMonitorResult, UnifiedError> {
        self.monitor.get_status().await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_performance_monitor_config_default() {
        let config = PerformanceMonitorConfig::default();
        assert_eq!(config.monitor_interval, Duration::from_secs(5));
        assert!(config.enabled);
        assert!(!config.monitors.is_empty());
        assert!(config.alert_thresholds.response_time_threshold > 0);
    }

    #[test]
    fn test_performance_monitor_item() {
        let item = PerformanceMonitorItem {
            name: "test".to_string(),
            monitor_type: PerformanceMonitorType::ResponseTime,
            enabled: true,
        };
        
        assert_eq!(item.name, "test");
        assert!(item.enabled);
    }

    #[test]
    fn test_performance_alert_thresholds() {
        let thresholds = PerformanceAlertThresholds::default();
        assert!(thresholds.response_time_threshold > 0);
        assert!(thresholds.throughput_threshold > 0);
        assert!(thresholds.error_rate_threshold > 0.0);
    }

    #[test]
    fn test_performance_monitor_creation() {
        let config = PerformanceMonitorConfig::default();
        let monitor = PerformanceMonitor::new(config);
        
        assert!(monitor.get_last_result().is_none());
    }

    #[tokio::test]
    async fn test_performance_monitor_get_status() {
        let config = PerformanceMonitorConfig::default();
        let monitor = PerformanceMonitor::new(config);
        
        let result = monitor.get_status().await;
        assert!(result.is_ok());
        
        let result = result.unwrap();
        assert!(result.total_monitors > 0);
        //assert!(result.healthy_monitors >= 0);
        //assert!(result.warning_monitors >= 0);
        //assert!(result.error_monitors >= 0);
    }

    #[test]
    fn test_performance_monitor_result() {
        let result = PerformanceMonitorResult {
            timestamp: chrono::Utc::now(),
            state: MonitoringState::Healthy,
            items: Vec::new(),
            total_monitors: 0,
            healthy_monitors: 0,
            warning_monitors: 0,
            error_monitors: 0,
        };
        
        assert_eq!(result.state, MonitoringState::Healthy);
        assert_eq!(result.total_monitors, 0);
    }

    #[test]
    fn test_performance_monitor_item_result() {
        let result = PerformanceMonitorItemResult {
            name: "test".to_string(),
            monitor_type: PerformanceMonitorType::ResponseTime,
            state: MonitoringState::Healthy,
            current_value: 0.0,
            average_value: 0.0,
            max_value: 0.0,
            min_value: 0.0,
            details: HashMap::new(),
        };
        
        assert_eq!(result.name, "test");
        assert_eq!(result.state, MonitoringState::Healthy);
        assert_eq!(result.current_value, 0.0);
    }

    #[test]
    fn test_global_performance_monitor() {
        let global_monitor = GlobalPerformanceMonitor::new();
        let monitor = global_monitor.get_monitor();
        
        assert!(monitor.get_last_result().is_none());
    }
}
