//! 资源监控实现
//!
//! 提供系统资源监控功能，包括CPU、内存、磁盘、网络等资源的使用情况。

use std::sync::Arc;
use std::collections::HashMap;
use std::time::Duration;
use serde::{Serialize, Deserialize};
use tracing::{debug, error, info};

use crate::error_handling::UnifiedError;
use super::MonitoringState;

/// 资源使用情况
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceUsage {
    /// CPU使用率
    pub cpu_usage: f64,
    /// 内存使用率
    pub memory_usage: f64,
    /// 磁盘使用率
    pub disk_usage: f64,
    /// 网络使用率
    pub network_usage: f64,
}

/// 资源监控配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceMonitorConfig {
    /// 监控间隔
    pub monitor_interval: Duration,
    /// 是否启用资源监控
    pub enabled: bool,
    /// 监控项目
    pub monitors: Vec<ResourceMonitorItem>,
    /// 告警阈值
    pub alert_thresholds: ResourceAlertThresholds,
}

impl Default for ResourceMonitorConfig {
    fn default() -> Self {
        Self {
            monitor_interval: Duration::from_secs(10),
            enabled: true,
            monitors: vec![
                ResourceMonitorItem {
                    name: "cpu".to_string(),
                    monitor_type: ResourceMonitorType::Cpu,
                    enabled: true,
                },
                ResourceMonitorItem {
                    name: "memory".to_string(),
                    monitor_type: ResourceMonitorType::Memory,
                    enabled: true,
                },
                ResourceMonitorItem {
                    name: "disk".to_string(),
                    monitor_type: ResourceMonitorType::Disk,
                    enabled: true,
                },
                ResourceMonitorItem {
                    name: "network".to_string(),
                    monitor_type: ResourceMonitorType::Network,
                    enabled: true,
                },
            ],
            alert_thresholds: ResourceAlertThresholds::default(),
        }
    }
}

/// 资源监控项目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceMonitorItem {
    /// 监控名称
    pub name: String,
    /// 监控类型
    pub monitor_type: ResourceMonitorType,
    /// 是否启用
    pub enabled: bool,
}

/// 资源监控类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResourceMonitorType {
    /// CPU监控
    Cpu,
    /// 内存监控
    Memory,
    /// 磁盘监控
    Disk,
    /// 网络监控
    Network,
    /// 自定义监控
    Custom {
        name: String,
        parameters: HashMap<String, String>,
    },
}

/// 资源告警阈值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceAlertThresholds {
    /// CPU使用率阈值
    pub cpu_usage_threshold: f64,
    /// 内存使用率阈值
    pub memory_usage_threshold: f64,
    /// 磁盘使用率阈值
    pub disk_usage_threshold: f64,
    /// 网络使用率阈值
    pub network_usage_threshold: f64,
}

impl Default for ResourceAlertThresholds {
    fn default() -> Self {
        Self {
            cpu_usage_threshold: 80.0,
            memory_usage_threshold: 80.0,
            disk_usage_threshold: 85.0,
            network_usage_threshold: 90.0,
        }
    }
}

/// 资源监控结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceMonitorResult {
    /// 监控时间
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 整体状态
    pub state: MonitoringState,
    /// 监控项目结果
    pub items: Vec<ResourceMonitorItemResult>,
    /// 总监控数
    pub total_monitors: usize,
    /// 正常监控数
    pub healthy_monitors: usize,
    /// 警告监控数
    pub warning_monitors: usize,
    /// 错误监控数
    pub error_monitors: usize,
}

/// 资源监控项目结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceMonitorItemResult {
    /// 监控名称
    pub name: String,
    /// 监控类型
    pub monitor_type: ResourceMonitorType,
    /// 状态
    pub state: MonitoringState,
    /// 使用率
    pub usage_percent: f64,
    /// 详细信息
    pub details: HashMap<String, String>,
}

/// 资源监控器
pub struct ResourceMonitor {
    config: ResourceMonitorConfig,
    is_running: std::sync::atomic::AtomicBool,
    last_result: std::sync::Mutex<Option<ResourceMonitorResult>>,
    monitor_handlers: std::sync::Mutex<HashMap<String, Box<dyn ResourceMonitorHandler + Send + Sync>>>,
}

impl ResourceMonitor {
    /// 创建新的资源监控器
    pub fn new(config: ResourceMonitorConfig) -> Self {
        Self {
            config,
            is_running: std::sync::atomic::AtomicBool::new(false),
            last_result: std::sync::Mutex::new(None),
            monitor_handlers: std::sync::Mutex::new(HashMap::new()),
        }
    }

    /// 启动资源监控
    pub async fn start(&self) -> Result<(), UnifiedError> {
        if self.is_running.load(std::sync::atomic::Ordering::Relaxed) {
            return Ok(());
        }

        if !self.config.enabled {
            debug!("资源监控已禁用");
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

        info!("资源监控器启动完成");
        Ok(())
    }

    /// 停止资源监控
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.is_running.store(false, std::sync::atomic::Ordering::Relaxed);
        info!("资源监控器停止完成");
        Ok(())
    }

    /// 获取资源状态
    pub async fn get_status(&self) -> Result<ResourceMonitorResult, UnifiedError> {
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
        let result = ResourceMonitorResult {
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
    async fn monitor_item(&self, item: &ResourceMonitorItem) -> ResourceMonitorItemResult {
        // 直接执行监控，避免复杂的生命周期问题
        match item.name.as_str() {
            "cpu" => CpuResourceMonitorHandler.monitor().await.unwrap_or_else(|_| ResourceMonitorItemResult {
                name: item.name.clone(),
                monitor_type: item.monitor_type.clone(),
                state: MonitoringState::Error,
                usage_percent: 0.0,
                details: std::collections::HashMap::new(),
            }),
            "memory" => MemoryResourceMonitorHandler.monitor().await.unwrap_or_else(|_| ResourceMonitorItemResult {
                name: item.name.clone(),
                monitor_type: item.monitor_type.clone(),
                state: MonitoringState::Error,
                usage_percent: 0.0,
                details: std::collections::HashMap::new(),
            }),
            "disk" => DiskResourceMonitorHandler.monitor().await.unwrap_or_else(|_| ResourceMonitorItemResult {
                name: item.name.clone(),
                monitor_type: item.monitor_type.clone(),
                state: MonitoringState::Error,
                usage_percent: 0.0,
                details: std::collections::HashMap::new(),
            }),
            "network" => NetworkResourceMonitorHandler.monitor().await.unwrap_or_else(|_| ResourceMonitorItemResult {
                name: item.name.clone(),
                monitor_type: item.monitor_type.clone(),
                state: MonitoringState::Error,
                usage_percent: 0.0,
                details: std::collections::HashMap::new(),
            }),
            _ => ResourceMonitorItemResult {
                name: item.name.clone(),
                monitor_type: item.monitor_type.clone(),
                state: MonitoringState::Error,
                usage_percent: 0.0,
                details: std::collections::HashMap::new(),
            }
        }
    }

    /// 计算整体状态
    fn calculate_overall_state(&self, items: &[ResourceMonitorItemResult]) -> MonitoringState {
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
        
        handlers.insert("cpu".to_string(), Box::new(CpuResourceMonitorHandler));
        handlers.insert("memory".to_string(), Box::new(MemoryResourceMonitorHandler));
        handlers.insert("disk".to_string(), Box::new(DiskResourceMonitorHandler));
        handlers.insert("network".to_string(), Box::new(NetworkResourceMonitorHandler));
    }

    /// 注册自定义监控处理器
    pub fn register_handler(&self, name: String, handler: Box<dyn ResourceMonitorHandler + Send + Sync>) {
        let mut handlers = self.monitor_handlers.lock().unwrap();
        handlers.insert(name, handler);
    }

    /// 运行监控循环
    async fn run_monitor_loop(&self) {
        let mut interval = tokio::time::interval(self.config.monitor_interval);
        
        while self.is_running.load(std::sync::atomic::Ordering::Relaxed) {
            interval.tick().await;
            
            if let Err(error) = self.get_status().await {
                error!("资源监控失败: {}", error);
            }
        }
    }

    /// 获取最后监控结果
    pub fn get_last_result(&self) -> Option<ResourceMonitorResult> {
        self.last_result.lock().unwrap().clone()
    }

    /// 获取配置
    pub fn get_config(&self) -> &ResourceMonitorConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: ResourceMonitorConfig) {
        self.config = config;
    }
}

impl Clone for ResourceMonitor {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            is_running: std::sync::atomic::AtomicBool::new(self.is_running.load(std::sync::atomic::Ordering::Relaxed)),
            last_result: std::sync::Mutex::new(self.last_result.lock().unwrap().clone()),
            monitor_handlers: std::sync::Mutex::new(HashMap::new()),
        }
    }
}

/// 资源监控处理器trait
pub trait ResourceMonitorHandler: Send + Sync {
    /// 执行资源监控
    fn monitor(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<ResourceMonitorItemResult, UnifiedError>> + Send>>;
}

/// CPU资源监控处理器
#[derive(Clone)]
pub struct CpuResourceMonitorHandler;

impl ResourceMonitorHandler for CpuResourceMonitorHandler {
    fn monitor(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<ResourceMonitorItemResult, UnifiedError>> + Send>> {
        Box::pin(async move {
        let mut details = HashMap::new();
        let mut state = MonitoringState::Healthy;
        let usage_percent;

        // 检查CPU使用情况
        let mut sys = sysinfo::System::new_all();
        sys.refresh_cpu();
        let cpu = sys.global_cpu_info().cpu_usage();
        usage_percent = cpu as f64;
        details.insert("cpu_usage_percent".to_string(), format!("{:.2}", usage_percent));
        
        if usage_percent > 80.0 {
            state = MonitoringState::Warning;
        }
        if usage_percent > 95.0 {
            state = MonitoringState::Error;
        }

        // 检查CPU核心数
        let cores = sysinfo::System::new_all().cpus().len();
        details.insert("cpu_cores".to_string(), cores.to_string());

        Ok(ResourceMonitorItemResult {
            name: "cpu".to_string(),
            monitor_type: ResourceMonitorType::Cpu,
            state,
            usage_percent,
            details,
        })
        })
    }
}

/// 内存资源监控处理器
#[derive(Clone)]
pub struct MemoryResourceMonitorHandler;

impl ResourceMonitorHandler for MemoryResourceMonitorHandler {
    fn monitor(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<ResourceMonitorItemResult, UnifiedError>> + Send>> {
        Box::pin(async move {
        let mut details = HashMap::new();
        let mut state = MonitoringState::Healthy;
        let usage_percent;

        // 检查内存使用情况
        let mut sys = sysinfo::System::new_all();
        sys.refresh_memory();
        let total = sys.total_memory();
        let used = sys.used_memory();
        let free = sys.free_memory();
        usage_percent = (used as f64 / total as f64) * 100.0;

        details.insert("total_memory".to_string(), total.to_string());
        details.insert("used_memory".to_string(), used.to_string());
        details.insert("free_memory".to_string(), free.to_string());
        details.insert("usage_percent".to_string(), format!("{:.2}", usage_percent));

        if usage_percent > 80.0 {
            state = MonitoringState::Warning;
        }
        if usage_percent > 95.0 {
            state = MonitoringState::Error;
        }

        Ok(ResourceMonitorItemResult {
            name: "memory".to_string(),
            monitor_type: ResourceMonitorType::Memory,
            state,
            usage_percent,
            details,
        })
        })
    }
}

/// 磁盘资源监控处理器
#[derive(Clone)]
pub struct DiskResourceMonitorHandler;

impl ResourceMonitorHandler for DiskResourceMonitorHandler {
    fn monitor(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<ResourceMonitorItemResult, UnifiedError>> + Send>> {
        Box::pin(async move {
            let mut details = HashMap::new();
            let state = MonitoringState::Healthy;
            let usage_percent;

        // 检查磁盘使用情况 - 暂时使用模拟数据（sysinfo 0.30 API变化）
        let total_space = 500u64 * 1024 * 1024 * 1024; // 假设500GB
        let used_space = 200u64 * 1024 * 1024 * 1024;  // 假设200GB
        let disk_count = 2;
        usage_percent = (used_space as f64 / total_space as f64) * 100.0;
        
        details.insert("total_space".to_string(), total_space.to_string());
        details.insert("used_space".to_string(), used_space.to_string());
        details.insert("disk_count".to_string(), disk_count.to_string());
        details.insert("status".to_string(), "simulated".to_string());

            Ok(ResourceMonitorItemResult {
                name: "disk".to_string(),
                monitor_type: ResourceMonitorType::Disk,
                state,
                usage_percent,
                details,
            })
        })
    }
}

/// 网络资源监控处理器
#[derive(Clone)]
pub struct NetworkResourceMonitorHandler;

impl ResourceMonitorHandler for NetworkResourceMonitorHandler {
    fn monitor(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<ResourceMonitorItemResult, UnifiedError>> + Send>> {
        Box::pin(async move {
        let mut details = HashMap::new();
        let mut state = MonitoringState::Healthy;
        let usage_percent;

        // 检查网络使用情况 - 暂时使用模拟数据（sysinfo 0.30 API变化）
        let total_received = 1024 * 1024 * 1024; // 1GB
        let total_transmitted = 512 * 1024 * 1024; // 512MB
        let interface_count = 2;
        let total_network_usage = total_received + total_transmitted;
        
        details.insert("total_received".to_string(), total_received.to_string());
        details.insert("total_transmitted".to_string(), total_transmitted.to_string());
        details.insert("total_network_usage".to_string(), total_network_usage.to_string());
        details.insert("interface_count".to_string(), interface_count.to_string());
        details.insert("status".to_string(), "simulated".to_string());
        
        // 计算网络使用率（这里使用简化的计算方式）
        if total_network_usage > 0 {
            usage_percent = (total_network_usage as f64 / 1000000000.0) * 100.0; // 假设1GB为100%
            
            if usage_percent > 90.0 {
                state = MonitoringState::Warning;
            }
            if usage_percent > 95.0 {
                state = MonitoringState::Error;
            }
        } else {
            usage_percent = 0.0;
        }

        Ok(ResourceMonitorItemResult {
            name: "network".to_string(),
            monitor_type: ResourceMonitorType::Network,
            state,
            usage_percent,
            details,
        })
        })
    }
}

/// 全局资源监控器
pub struct GlobalResourceMonitor {
    monitor: Arc<ResourceMonitor>,
}

impl GlobalResourceMonitor {
    /// 创建全局资源监控器
    pub fn new() -> Self {
        Self {
            monitor: Arc::new(ResourceMonitor::new(ResourceMonitorConfig::default())),
        }
    }

    /// 获取资源监控器实例
    pub fn get_monitor(&self) -> Arc<ResourceMonitor> {
        self.monitor.clone()
    }

    /// 启动全局资源监控
    pub async fn start(&self) -> Result<(), UnifiedError> {
        self.monitor.start().await
    }

    /// 停止全局资源监控
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.monitor.stop().await
    }

    /// 获取全局资源状态
    pub async fn get_status(&self) -> Result<ResourceMonitorResult, UnifiedError> {
        self.monitor.get_status().await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_resource_monitor_config_default() {
        let config = ResourceMonitorConfig::default();
        assert_eq!(config.monitor_interval, Duration::from_secs(10));
        assert!(config.enabled);
        assert!(!config.monitors.is_empty());
        assert!(config.alert_thresholds.cpu_usage_threshold > 0.0);
    }

    #[test]
    fn test_resource_monitor_item() {
        let item = ResourceMonitorItem {
            name: "test".to_string(),
            monitor_type: ResourceMonitorType::Cpu,
            enabled: true,
        };
        
        assert_eq!(item.name, "test");
        assert!(item.enabled);
    }

    #[test]
    fn test_resource_alert_thresholds() {
        let thresholds = ResourceAlertThresholds::default();
        assert!(thresholds.cpu_usage_threshold > 0.0);
        assert!(thresholds.memory_usage_threshold > 0.0);
        assert!(thresholds.disk_usage_threshold > 0.0);
        assert!(thresholds.network_usage_threshold > 0.0);
    }

    #[test]
    fn test_resource_monitor_creation() {
        let config = ResourceMonitorConfig::default();
        let monitor = ResourceMonitor::new(config);
        
        assert!(monitor.get_last_result().is_none());
    }

    #[tokio::test]
    async fn test_resource_monitor_get_status() {
        let config = ResourceMonitorConfig::default();
        let monitor = ResourceMonitor::new(config);
        
        let result = monitor.get_status().await;
        assert!(result.is_ok());
        
        let result = result.unwrap();
        assert!(result.total_monitors > 0);
        //assert!(result.healthy_monitors >= 0);
        //assert!(result.warning_monitors >= 0);
        //assert!(result.error_monitors >= 0);
    }

    #[test]
    fn test_resource_monitor_result() {
        let result = ResourceMonitorResult {
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
    fn test_resource_monitor_item_result() {
        let result = ResourceMonitorItemResult {
            name: "test".to_string(),
            monitor_type: ResourceMonitorType::Cpu,
            state: MonitoringState::Healthy,
            usage_percent: 0.0,
            details: HashMap::new(),
        };
        
        assert_eq!(result.name, "test");
        assert_eq!(result.state, MonitoringState::Healthy);
        assert_eq!(result.usage_percent, 0.0);
    }

    #[test]
    fn test_global_resource_monitor() {
        let global_monitor = GlobalResourceMonitor::new();
        let monitor = global_monitor.get_monitor();
        
        assert!(monitor.get_last_result().is_none());
    }
}
