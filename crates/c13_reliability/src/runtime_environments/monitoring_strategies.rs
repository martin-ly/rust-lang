//! # 环境特定监控策略
//!
//! 本模块为不同的运行时环境提供了特定的监控策略和优化配置。

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::time::Duration;
//use crate::error_handling::UnifiedError;
use super::{RuntimeEnvironment, EnvironmentCapabilities};

/// 监控策略接口
#[async_trait]
pub trait MonitoringStrategy: Send + Sync {
    /// 获取策略名称
    fn name(&self) -> &str;
    
    /// 获取监控间隔
    fn monitoring_interval(&self) -> Duration;
    
    /// 获取健康检查间隔
    fn health_check_interval(&self) -> Duration;
    
    /// 获取指标收集间隔
    fn metrics_collection_interval(&self) -> Duration;
    
    /// 是否启用详细监控
    fn enable_detailed_monitoring(&self) -> bool;
    
    /// 是否启用性能监控
    fn enable_performance_monitoring(&self) -> bool;
    
    /// 是否启用资源监控
    fn enable_resource_monitoring(&self) -> bool;
    
    /// 是否启用混沌工程
    fn enable_chaos_engineering(&self) -> bool;
    
    /// 获取监控配置
    fn get_monitoring_config(&self) -> MonitoringConfig;
}

/// 监控配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringConfig {
    /// 监控间隔
    pub monitoring_interval: Duration,
    /// 健康检查间隔
    pub health_check_interval: Duration,
    /// 指标收集间隔
    pub metrics_collection_interval: Duration,
    /// 启用详细监控
    pub enable_detailed_monitoring: bool,
    /// 启用性能监控
    pub enable_performance_monitoring: bool,
    /// 启用资源监控
    pub enable_resource_monitoring: bool,
    /// 启用网络监控
    pub enable_network_monitoring: bool,
    /// 启用文件系统监控
    pub enable_filesystem_monitoring: bool,
    /// 启用进程监控
    pub enable_process_monitoring: bool,
    /// 启用中断监控
    pub enable_interrupt_monitoring: bool,
    /// 启用定时器监控
    pub enable_timer_monitoring: bool,
    /// 启用混沌工程
    pub enable_chaos_engineering: bool,
    /// 最大监控数据保留时间
    pub max_data_retention: Duration,
    /// 监控数据压缩
    pub enable_data_compression: bool,
}

/// 操作系统环境监控策略
pub struct OperatingSystemMonitoringStrategy {
    config: MonitoringConfig,
}

impl OperatingSystemMonitoringStrategy {
    pub fn new() -> Self {
        Self {
            config: MonitoringConfig {
                monitoring_interval: Duration::from_secs(5),
                health_check_interval: Duration::from_secs(30),
                metrics_collection_interval: Duration::from_secs(10),
                enable_detailed_monitoring: true,
                enable_performance_monitoring: true,
                enable_resource_monitoring: true,
                enable_network_monitoring: true,
                enable_filesystem_monitoring: true,
                enable_process_monitoring: true,
                enable_interrupt_monitoring: true,
                enable_timer_monitoring: true,
                enable_chaos_engineering: true,
                max_data_retention: Duration::from_secs(86400 * 7), // 7天
                enable_data_compression: true,
            },
        }
    }
}

#[async_trait]
impl MonitoringStrategy for OperatingSystemMonitoringStrategy {
    fn name(&self) -> &str {
        "OperatingSystem"
    }

    fn monitoring_interval(&self) -> Duration {
        self.config.monitoring_interval
    }

    fn health_check_interval(&self) -> Duration {
        self.config.health_check_interval
    }

    fn metrics_collection_interval(&self) -> Duration {
        self.config.metrics_collection_interval
    }

    fn enable_detailed_monitoring(&self) -> bool {
        self.config.enable_detailed_monitoring
    }

    fn enable_performance_monitoring(&self) -> bool {
        self.config.enable_performance_monitoring
    }

    fn enable_resource_monitoring(&self) -> bool {
        self.config.enable_resource_monitoring
    }
    
    fn enable_chaos_engineering(&self) -> bool {
        self.config.enable_chaos_engineering
    }

    fn get_monitoring_config(&self) -> MonitoringConfig {
        self.config.clone()
    }
}

/// 嵌入式裸机环境监控策略
pub struct EmbeddedBareMetalMonitoringStrategy {
    config: MonitoringConfig,
}

impl EmbeddedBareMetalMonitoringStrategy {
    pub fn new() -> Self {
        Self {
            config: MonitoringConfig {
                monitoring_interval: Duration::from_secs(60),
                health_check_interval: Duration::from_secs(300),
                metrics_collection_interval: Duration::from_secs(120),
                enable_detailed_monitoring: false,
                enable_performance_monitoring: false,
                enable_resource_monitoring: true,
                enable_network_monitoring: false,
                enable_filesystem_monitoring: false,
                enable_process_monitoring: false,
                enable_interrupt_monitoring: true,
                enable_timer_monitoring: true,
                enable_chaos_engineering: false,
                max_data_retention: Duration::from_secs(86400), // 1天
                enable_data_compression: true,
            },
        }
    }
}

#[async_trait]
impl MonitoringStrategy for EmbeddedBareMetalMonitoringStrategy {
    fn name(&self) -> &str {
        "EmbeddedBareMetal"
    }

    fn monitoring_interval(&self) -> Duration {
        self.config.monitoring_interval
    }

    fn health_check_interval(&self) -> Duration {
        self.config.health_check_interval
    }

    fn metrics_collection_interval(&self) -> Duration {
        self.config.metrics_collection_interval
    }

    fn enable_detailed_monitoring(&self) -> bool {
        self.config.enable_detailed_monitoring
    }

    fn enable_performance_monitoring(&self) -> bool {
        self.config.enable_performance_monitoring
    }

    fn enable_resource_monitoring(&self) -> bool {
        self.config.enable_resource_monitoring
    }
    
    fn enable_chaos_engineering(&self) -> bool {
        self.config.enable_chaos_engineering
    }

    fn get_monitoring_config(&self) -> MonitoringConfig {
        self.config.clone()
    }
}

/// 容器环境监控策略
pub struct ContainerMonitoringStrategy {
    config: MonitoringConfig,
}

impl ContainerMonitoringStrategy {
    pub fn new() -> Self {
        Self {
            config: MonitoringConfig {
                monitoring_interval: Duration::from_secs(10),
                health_check_interval: Duration::from_secs(60),
                metrics_collection_interval: Duration::from_secs(15),
                enable_detailed_monitoring: true,
                enable_performance_monitoring: true,
                enable_resource_monitoring: true,
                enable_network_monitoring: true,
                enable_filesystem_monitoring: true,
                enable_process_monitoring: true,
                enable_interrupt_monitoring: false,
                enable_timer_monitoring: true,
                enable_chaos_engineering: true,
                max_data_retention: Duration::from_secs(86400 * 3), // 3天
                enable_data_compression: true,
            },
        }
    }
}

#[async_trait]
impl MonitoringStrategy for ContainerMonitoringStrategy {
    fn name(&self) -> &str {
        "Container"
    }

    fn monitoring_interval(&self) -> Duration {
        self.config.monitoring_interval
    }

    fn health_check_interval(&self) -> Duration {
        self.config.health_check_interval
    }

    fn metrics_collection_interval(&self) -> Duration {
        self.config.metrics_collection_interval
    }

    fn enable_detailed_monitoring(&self) -> bool {
        self.config.enable_detailed_monitoring
    }

    fn enable_performance_monitoring(&self) -> bool {
        self.config.enable_performance_monitoring
    }

    fn enable_resource_monitoring(&self) -> bool {
        self.config.enable_resource_monitoring
    }
    
    fn enable_chaos_engineering(&self) -> bool {
        self.config.enable_chaos_engineering
    }

    fn get_monitoring_config(&self) -> MonitoringConfig {
        self.config.clone()
    }
}

/// WebAssembly环境监控策略
pub struct WebAssemblyMonitoringStrategy {
    config: MonitoringConfig,
}

impl WebAssemblyMonitoringStrategy {
    pub fn new() -> Self {
        Self {
            config: MonitoringConfig {
                monitoring_interval: Duration::from_secs(30),
                health_check_interval: Duration::from_secs(120),
                metrics_collection_interval: Duration::from_secs(60),
                enable_detailed_monitoring: false,
                enable_performance_monitoring: true,
                enable_resource_monitoring: true,
                enable_network_monitoring: false,
                enable_filesystem_monitoring: false,
                enable_process_monitoring: false,
                enable_interrupt_monitoring: false,
                enable_timer_monitoring: true,
                enable_chaos_engineering: false,
                max_data_retention: Duration::from_secs(86400 * 2), // 2天
                enable_data_compression: true,
            },
        }
    }
}

#[async_trait]
impl MonitoringStrategy for WebAssemblyMonitoringStrategy {
    fn name(&self) -> &str {
        "WebAssembly"
    }

    fn monitoring_interval(&self) -> Duration {
        self.config.monitoring_interval
    }

    fn health_check_interval(&self) -> Duration {
        self.config.health_check_interval
    }

    fn metrics_collection_interval(&self) -> Duration {
        self.config.metrics_collection_interval
    }

    fn enable_detailed_monitoring(&self) -> bool {
        self.config.enable_detailed_monitoring
    }

    fn enable_performance_monitoring(&self) -> bool {
        self.config.enable_performance_monitoring
    }

    fn enable_resource_monitoring(&self) -> bool {
        self.config.enable_resource_monitoring
    }
    
    fn enable_chaos_engineering(&self) -> bool {
        self.config.enable_chaos_engineering
    }

    fn get_monitoring_config(&self) -> MonitoringConfig {
        self.config.clone()
    }
}

/// 函数即服务环境监控策略
pub struct FaaSMonitoringStrategy {
    config: MonitoringConfig,
}

impl FaaSMonitoringStrategy {
    pub fn new() -> Self {
        Self {
            config: MonitoringConfig {
                monitoring_interval: Duration::from_secs(5),
                health_check_interval: Duration::from_secs(30),
                metrics_collection_interval: Duration::from_secs(10),
                enable_detailed_monitoring: true,
                enable_performance_monitoring: true,
                enable_resource_monitoring: true,
                enable_network_monitoring: false,
                enable_filesystem_monitoring: false,
                enable_process_monitoring: false,
                enable_interrupt_monitoring: false,
                enable_timer_monitoring: true,
                enable_chaos_engineering: false,
                max_data_retention: Duration::from_secs(86400), // 1天
                enable_data_compression: true,
            },
        }
    }
}

#[async_trait]
impl MonitoringStrategy for FaaSMonitoringStrategy {
    fn name(&self) -> &str {
        "FunctionAsAService"
    }

    fn monitoring_interval(&self) -> Duration {
        self.config.monitoring_interval
    }

    fn health_check_interval(&self) -> Duration {
        self.config.health_check_interval
    }

    fn metrics_collection_interval(&self) -> Duration {
        self.config.metrics_collection_interval
    }

    fn enable_detailed_monitoring(&self) -> bool {
        self.config.enable_detailed_monitoring
    }

    fn enable_performance_monitoring(&self) -> bool {
        self.config.enable_performance_monitoring
    }

    fn enable_resource_monitoring(&self) -> bool {
        self.config.enable_resource_monitoring
    }
    
    fn enable_chaos_engineering(&self) -> bool {
        self.config.enable_chaos_engineering
    }

    fn get_monitoring_config(&self) -> MonitoringConfig {
        self.config.clone()
    }
}

/// 监控策略工厂
pub struct MonitoringStrategyFactory;

impl MonitoringStrategyFactory {
    /// 根据环境类型创建监控策略
    pub fn create_strategy(environment: RuntimeEnvironment) -> Box<dyn MonitoringStrategy> {
        match environment {
            RuntimeEnvironment::OperatingSystem => {
                Box::new(OperatingSystemMonitoringStrategy::new())
            },
            RuntimeEnvironment::EmbeddedBareMetal => {
                Box::new(EmbeddedBareMetalMonitoringStrategy::new())
            },
            RuntimeEnvironment::Container => {
                Box::new(ContainerMonitoringStrategy::new())
            },
            RuntimeEnvironment::WebAssembly => {
                Box::new(WebAssemblyMonitoringStrategy::new())
            },
            RuntimeEnvironment::FunctionAsAService => {
                Box::new(FaaSMonitoringStrategy::new())
            },
            _ => {
                // 默认使用操作系统策略
                Box::new(OperatingSystemMonitoringStrategy::new())
            },
        }
    }

    /// 根据环境能力创建自定义监控策略
    pub fn create_custom_strategy(capabilities: &EnvironmentCapabilities) -> Box<dyn MonitoringStrategy> {
        // 根据环境能力调整监控策略
        if !capabilities.supports_multiprocessing && !capabilities.supports_network {
            // 嵌入式环境
            Box::new(EmbeddedBareMetalMonitoringStrategy::new())
        } else if !capabilities.supports_system_calls {
            // 沙箱环境
            Box::new(WebAssemblyMonitoringStrategy::new())
        } else if capabilities.supports_chaos_engineering {
            // 完整功能环境
            Box::new(OperatingSystemMonitoringStrategy::new())
        } else {
            // 容器环境
            Box::new(ContainerMonitoringStrategy::new())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_monitoring_strategy_factory() {
        let strategy = MonitoringStrategyFactory::create_strategy(RuntimeEnvironment::OperatingSystem);
        assert_eq!(strategy.name(), "OperatingSystem");
        assert_eq!(strategy.monitoring_interval(), Duration::from_secs(5));
    }

    #[test]
    fn test_embedded_monitoring_strategy() {
        let strategy = EmbeddedBareMetalMonitoringStrategy::new();
        assert_eq!(strategy.name(), "EmbeddedBareMetal");
        assert_eq!(strategy.monitoring_interval(), Duration::from_secs(60));
        assert!(!strategy.enable_detailed_monitoring());
        assert!(!strategy.enable_chaos_engineering());
    }

    #[test]
    fn test_container_monitoring_strategy() {
        let strategy = ContainerMonitoringStrategy::new();
        assert_eq!(strategy.name(), "Container");
        assert_eq!(strategy.monitoring_interval(), Duration::from_secs(10));
        assert!(strategy.enable_detailed_monitoring());
        assert!(strategy.enable_chaos_engineering());
    }

    #[test]
    fn test_wasm_monitoring_strategy() {
        let strategy = WebAssemblyMonitoringStrategy::new();
        assert_eq!(strategy.name(), "WebAssembly");
        assert_eq!(strategy.monitoring_interval(), Duration::from_secs(30));
        assert!(!strategy.enable_detailed_monitoring());
        assert!(!strategy.enable_chaos_engineering());
    }

    #[test]
    fn test_faas_monitoring_strategy() {
        let strategy = FaaSMonitoringStrategy::new();
        assert_eq!(strategy.name(), "FunctionAsAService");
        assert_eq!(strategy.monitoring_interval(), Duration::from_secs(5));
        assert!(strategy.enable_detailed_monitoring());
        assert!(!strategy.enable_chaos_engineering());
    }
}
