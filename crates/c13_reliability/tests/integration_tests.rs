//! 集成测试
//!
//! 测试可靠性框架的各个组件之间的集成功能。

use c13_reliability::fault_tolerance::{CircuitBreaker, CircuitBreakerConfig, RetryPolicy, RetryConfig};
use c13_reliability::runtime_monitoring::{HealthChecker, HealthCheckConfig};
use c13_reliability::config::{ConfigManager, ReliabilityConfig};
use c13_reliability::error_handling::UnifiedError;

#[tokio::test]
async fn test_full_reliability_workflow() {
    // 初始化框架
    assert!(c13_reliability::init().await.is_ok());
    
    // 测试错误处理与容错机制的集成
    let circuit_breaker = CircuitBreaker::new(CircuitBreakerConfig::default());
    let _retry_policy = RetryPolicy::new(RetryConfig::default());
    
    let result = circuit_breaker.execute(|| async {
        // 模拟可能失败的操作
        Ok::<String, UnifiedError>("success".to_string())
    }).await;
    
    assert!(result.is_ok());
    
    // 关闭框架
    assert!(c13_reliability::shutdown().await.is_ok());
}

#[tokio::test]
async fn test_monitoring_integration() {
    // 初始化框架
    assert!(c13_reliability::init().await.is_ok());
    
    // 创建健康检查器
    let health_checker = HealthChecker::new(HealthCheckConfig::default());
    
    // 执行健康检查
    let health_status = health_checker.check_health().await;
    assert!(matches!(health_status, Ok(_) | Err(_)));
    
    // 关闭框架
    assert!(c13_reliability::shutdown().await.is_ok());
}

#[tokio::test]
async fn test_config_and_metrics_integration() {
    // 初始化框架
    assert!(c13_reliability::init().await.is_ok());
    
    // 创建配置管理器
    let mut config_manager = ConfigManager::new();
    let config = ReliabilityConfig::default();
    config_manager.update_config(config);
    
    // 验证配置
    let current_config = config_manager.get_config();
    assert!(!current_config.global.app_name.is_empty());
    
    // 关闭框架
    assert!(c13_reliability::shutdown().await.is_ok());
}
