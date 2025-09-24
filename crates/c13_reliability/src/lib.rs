//! # Rust 统一可靠性框架
//!
//! 本库提供了全面的可靠性解决方案，包括：
//! - 统一错误处理系统
//! - 容错机制（断路器、重试、降级）
//! - 运行时监控和自愈
//! - 混沌工程测试工具
//!
//! ## 核心特性
//!
//! - **统一错误处理**：提供类型安全、上下文丰富的错误处理
//! - **容错机制**：断路器、重试、超时、降级等企业级容错模式
//! - **运行时监控**：健康检查、性能监控、异常检测
//! - **自动恢复**：内存泄漏检测、连接池重建、死锁恢复
//! - **混沌工程**：故障注入、弹性测试、恢复验证
//!
//! ## 快速开始
//!
//! ```rust
//! use c13_reliability::prelude::*;
//! use c13_reliability::error_handling::UnifiedError;
//! use c13_reliability::fault_tolerance::{CircuitBreaker, RetryPolicy};
//! use c13_reliability::runtime_monitoring::HealthChecker;
//!
//! #[tokio::main]
//! async fn main() -> Result<(), UnifiedError> {
//!     // 初始化监控
//!     let health_checker = HealthChecker::new();
//!     
//!     // 创建断路器
//!     let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(60));
//!     
//!     // 创建重试策略
//!     let retry_policy = RetryPolicy::exponential_backoff(3, Duration::from_millis(100));
//!     
//!     // 执行带容错的操作
//!     let result = circuit_breaker
//!         .with_retry(retry_policy)
//!         .execute(|| async {
//!             // 你的业务逻辑
//!             Ok::<String, UnifiedError>("success".to_string())
//!         })
//!         .await?;
//!     
//!     println!("操作结果: {}", result);
//!     Ok(())
//! }
//! ```

// 核心模块
pub mod error_handling;
pub mod fault_tolerance;
pub mod runtime_monitoring;
pub mod chaos_engineering;
pub mod config;
pub mod metrics;
pub mod utils;

// 运行时环境支持
pub mod runtime_environments;

// 重新导出常用类型和函数
pub mod prelude {
    pub use crate::error_handling::{
        UnifiedError, ErrorContext, ErrorSeverity, ResultExt, 
        ErrorRecovery, ErrorMonitor, GlobalErrorMonitor
    };
    pub use crate::fault_tolerance::{
        CircuitBreaker, RetryPolicy, Bulkhead, Timeout, Fallback,
        FaultToleranceConfig, ResilienceBuilder
    };
    pub use crate::runtime_monitoring::{
        HealthChecker, ResourceMonitor, PerformanceMonitor, 
        AnomalyDetector, AutoRecovery, MonitoringDashboard, MonitoringConfig
    };
    pub use crate::chaos_engineering::{
        FaultInjector, ChaosScenarios, ResilienceTester, RecoveryTester
    };
    pub use crate::config::ReliabilityConfig;
    pub use crate::metrics::ReliabilityMetrics;
    pub use crate::utils::{DurationExt, ResultExt as UtilsResultExt};
    pub use crate::runtime_environments::{
        RuntimeEnvironment, RuntimeEnvironmentManager, RuntimeEnvironmentAdapter,
        EnvironmentCapabilities, SystemInfo, ResourceUsage, HealthStatus, HealthLevel,
        RecoveryType, OSEnvironmentAdapter, EmbeddedEnvironmentAdapter, ContainerEnvironmentAdapter
    };
    
    // 常用标准库类型
    pub use std::time::Duration;
    pub use std::sync::Arc;
    pub use anyhow::Result;
    pub use tracing::{info, warn, error, debug, trace};
}

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const NAME: &str = env!("CARGO_PKG_NAME");

/// 获取库版本信息
pub fn version() -> &'static str {
    VERSION
}

/// 获取库名称
pub fn name() -> &'static str {
    NAME
}

/// 初始化可靠性框架
/// 
/// 这个函数会初始化全局错误监控、指标收集和健康检查系统
pub async fn init() -> Result<(), crate::error_handling::UnifiedError> {
    // 初始化全局错误监控
    crate::error_handling::GlobalErrorMonitor::init().await?;
    
    // 初始化指标收集
    // crate::metrics::ReliabilityMetrics::init().await?;
    
    // 初始化健康检查
    crate::runtime_monitoring::GlobalHealthChecker::init_global().await?;
    
    tracing::info!("可靠性框架初始化完成");
    Ok(())
}

/// 优雅关闭可靠性框架
/// 
/// 这个函数会清理资源、保存指标数据并关闭监控系统
pub async fn shutdown() -> Result<(), crate::error_handling::UnifiedError> {
    tracing::info!("开始关闭可靠性框架");
    
    // 保存指标数据
    // crate::metrics::ReliabilityMetrics::shutdown().await?;
    
    // 关闭健康检查
    crate::runtime_monitoring::GlobalHealthChecker::shutdown_global().await?;
    
    // 关闭全局错误监控
    crate::error_handling::GlobalErrorMonitor::shutdown().await?;
    
    tracing::info!("可靠性框架关闭完成");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_init_and_shutdown() {
        // 测试初始化和关闭
        assert!(init().await.is_ok());
        assert!(shutdown().await.is_ok());
    }

    #[test]
    fn test_version_info() {
        assert!(!version().is_empty());
        assert!(!name().is_empty());
        assert_eq!(name(), "c13_reliability");
    }
}
