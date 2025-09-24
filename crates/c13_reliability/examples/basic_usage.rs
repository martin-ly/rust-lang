//! 基本使用示例
//!
//! 展示如何使用可靠性框架的基本功能。

use c13_reliability::prelude::*;
use c13_reliability::{
    //log_error,
    error_handling::{RecoveryStrategy, ErrorHandler},
    fault_tolerance::{CircuitBreakerConfig, Retrier, RetryPolicy, RetryConfig, TimeoutConfig, FallbackConfig},
    runtime_monitoring::{HealthCheckConfig, AnomalyDetectionConfig, ResourceUsage, HealthCheck, HealthStatus, ResourceMonitorConfig, PerformanceMonitorConfig},
    chaos_engineering::{ChaosEngineeringManager, ChaosEngineeringConfig},
    config::ConfigManager,
    metrics::{MetricsCollector, MetricValue},
    //utils::{PerformanceUtils, ConfigUtils}
};
use std::time::Duration;
use tokio::time::sleep;
use async_trait::async_trait;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 初始化日志
    env_logger::init();
    
    // 初始化可靠性框架
    c13_reliability::init().await?;
    
    println!("=== 可靠性框架基本使用示例 ===");
    
    // 1. 错误处理示例
    println!("\n1. 错误处理示例");
    error_handling_example().await?;
    
    // 2. 容错机制示例
    println!("\n2. 容错机制示例");
    fault_tolerance_example().await?;
    
    // 3. 运行时监控示例
    println!("\n3. 运行时监控示例");
    runtime_monitoring_example().await?;
    
    // 4. 混沌工程示例
    println!("\n4. 混沌工程示例");
    chaos_engineering_example().await?;
    
    // 5. 配置管理示例
    println!("\n5. 配置管理示例");
    config_management_example().await?;
    
    // 6. 指标收集示例
    println!("\n6. 指标收集示例");
    metrics_collection_example().await?;
    
    // 7. 工具函数示例
    println!("\n7. 工具函数示例");
    utility_functions_example().await?;
    
    // 关闭可靠性框架
    c13_reliability::shutdown().await?;
    
    println!("\n=== 示例完成 ===");
    Ok(())
}

/// 错误处理示例
#[allow(unused_variables)]
async fn error_handling_example() -> Result<(), UnifiedError> {
    // 创建统一错误
    let error = UnifiedError::new(
        "这是一个示例错误",
        ErrorSeverity::Medium,
        "example",
        ErrorContext::new("example", "error_handling_example", file!(), line!(), ErrorSeverity::Medium, "example")
    );
    
    // 记录错误
    // log_error!(error); // 需要GlobalErrorMonitor实例
    
    // 使用错误恢复策略
    let recovery_strategy = RecoveryStrategy::Retry {
        max_attempts: 3,
        delay: Duration::from_millis(1000),
    };
    
    let error_handler = ErrorHandler::new(recovery_strategy);
    
    // 模拟可能失败的操作
    let result = if rand::random::<bool>() {
        Ok("操作成功".to_string())
    } else {
        Err(UnifiedError::new(
            "操作失败",
            ErrorSeverity::Low,
            "example",
            ErrorContext::new("example", "simulated_operation", file!(), line!(), ErrorSeverity::Low, "example")
        ))
    };
    
    match result {
        Ok(value) => println!("操作成功: {}", value),
        Err(error) => println!("操作失败: {}", error),
    }
    
    Ok(())
}

/// 容错机制示例
#[allow(unused_variables)]
async fn fault_tolerance_example() -> Result<(), UnifiedError> {
    // 创建断路器
    let circuit_breaker_config = CircuitBreakerConfig {
        failure_threshold: 5,
        recovery_timeout: Duration::from_secs(60),
        ..Default::default()
    };
    let circuit_breaker = CircuitBreaker::new(circuit_breaker_config);
    
    // 创建重试策略
    let retry_policy = RetryPolicy::new(RetryConfig::default());
    
    let retrier = Retrier::new(RetryConfig::default());
    
    // 创建超时机制
    let timeout = Timeout::new(TimeoutConfig {
        duration: Duration::from_secs(5),
        ..Default::default()
    });
    
    // 创建降级机制
    let fallback = Fallback::new(FallbackConfig::default());
    
    // 执行带容错的操作
    let result = circuit_breaker.execute(|| async {
            // 模拟可能失败的操作
            sleep(Duration::from_millis(100)).await;
            
            if rand::random::<bool>() {
                Ok("操作成功".to_string())
            } else {
                Err(UnifiedError::new(
                    "操作失败",
                    ErrorSeverity::Medium,
                    "example",
                    ErrorContext::new("example", "fault_tolerant_operation", file!(), line!(), ErrorSeverity::Medium, "example")
                ))
            }
        })
        .await;
    
    match result {
        Ok(value) => println!("容错操作成功: {}", value),
        Err(error) => println!("容错操作失败: {}", error),
    }
    
    Ok(())
}

/// 运行时监控示例
async fn runtime_monitoring_example() -> Result<(), UnifiedError> {
    // 创建健康检查器
    let health_checker = HealthChecker::new(HealthCheckConfig::default());
    
    // 添加健康检查项目
    // health_checker.add_check(Box::new(DatabaseHealthCheck)); // 方法不存在
    // health_checker.add_check(Box::new(CacheHealthCheck)); // 方法不存在
    // health_checker.add_check(Box::new(ExternalServiceHealthCheck)); // 方法不存在
    
    // 执行健康检查
    let health_status = health_checker.check_health().await;
    println!("健康状态: {:?}", health_status);
    
    // 创建资源监控器
    let _resource_monitor = ResourceMonitor::new(ResourceMonitorConfig::default());
    
    // 启动资源监控
    // let monitor_handle = tokio::spawn(async move {
    //     resource_monitor.start_monitoring(|usage| { // 方法不存在
    //         println!("资源使用情况: CPU: {:.1}%, 内存: {}MB, 磁盘: {}MB", 
    //                  usage.cpu_usage, 
    //                  usage.memory_usage / 1024 / 1024,
    //                  usage.disk_usage / 1024 / 1024);
    //     }).await;
    // });
    
    // 等待一段时间
    sleep(Duration::from_secs(5)).await;
    
    // 停止监控
    // monitor_handle.abort(); // monitor_handle未定义
    
    // 创建性能监控器
    let _performance_monitor = PerformanceMonitor::new(PerformanceMonitorConfig::default());
    
    // 记录一些性能指标
    for _i in 0..10 {
        let start = std::time::Instant::now();
        sleep(Duration::from_millis(100)).await;
        let _latency = start.elapsed();
        
        // performance_monitor.record_request(latency, true); // 方法不存在
    }
    
    // 创建异常检测器
    let anomaly_detector_config = AnomalyDetectionConfig::default();
    let _anomaly_detector = AnomalyDetector::new(anomaly_detector_config);
    
    // 模拟资源使用情况
    let _resource_usage = ResourceUsage {
        cpu_usage: 85.0,
        memory_usage: 512.0 * 1024.0 * 1024.0,
        disk_usage: 100.0 * 1024.0 * 1024.0,
        network_usage: 1024.0 * 1024.0,
    };
    
    // 检测异常
    // if let Some(anomaly) = anomaly_detector.detect_resource_anomaly(&resource_usage) { // 方法不存在
    //     println!("检测到异常: {:?}", anomaly);
    // }
    
    Ok(())
}

/// 混沌工程示例
async fn chaos_engineering_example() -> Result<(), UnifiedError> {
    // 创建混沌工程管理器
    let chaos_manager = ChaosEngineeringManager::new(ChaosEngineeringConfig::default());
    
    // 启动混沌工程测试
    chaos_manager.start().await?;
    
    // 执行混沌工程测试
    let test_result = chaos_manager.run_tests().await?;
    
    println!("混沌工程测试结果:");
    println!("  总体评分: {:.2}", test_result.overall_assessment.overall_score);
    println!("  弹性评分: {:.2}", test_result.overall_assessment.resilience_score);
    println!("  恢复评分: {:.2}", test_result.overall_assessment.recovery_score);
    println!("  建议: {:?}", test_result.overall_assessment.recommendations);
    
    // 停止混沌工程测试
    chaos_manager.stop().await?;
    
    Ok(())
}

/// 配置管理示例
async fn config_management_example() -> Result<(), UnifiedError> {
    // 创建配置管理器
    let mut config_manager = ConfigManager::new();
    
    // 创建配置
    let config = ReliabilityConfig::default();
    
    // 更新配置
    config_manager.update_config(config);
    
    // 获取配置
    let current_config = config_manager.get_config();
    println!("当前配置: 应用名称: {}, 环境: {}", 
             current_config.global.app_name, 
             current_config.global.environment);
    
    // 设置配置值
    config_manager.set_value("custom_key", "custom_value")?;
    
    // 获取配置值
    if let Some(value) = config_manager.get_value::<String>("custom_key") {
        println!("自定义配置值: {}", value);
    }
    
    Ok(())
}

/// 指标收集示例
async fn metrics_collection_example() -> Result<(), UnifiedError> {
    // 创建指标收集器
    let metrics_collector = MetricsCollector::new(Duration::from_secs(5));
    
    // 启动指标收集
    metrics_collector.start().await?;
    
    // 设置自定义指标
    metrics_collector.set_custom_metric("custom_counter".to_string(), MetricValue::Integer(42));
    metrics_collector.set_custom_metric("custom_gauge".to_string(), MetricValue::Float(3.14));
    metrics_collector.set_custom_metric("custom_label".to_string(), MetricValue::String("test".to_string()));
    
    // 等待一段时间让指标收集
    sleep(Duration::from_secs(10)).await;
    
    // 获取当前指标
    let current_metrics = metrics_collector.get_current_metrics();
    println!("当前指标:");
    println!("  总错误数: {}", current_metrics.error_metrics.total_errors);
    println!("  错误率: {:.2}%", current_metrics.error_metrics.error_rate * 100.0);
    println!("  总请求数: {}", current_metrics.performance_metrics.total_requests);
    println!("  平均响应时间: {:?}", current_metrics.performance_metrics.average_response_time);
    println!("  CPU使用率: {:.1}%", current_metrics.resource_metrics.cpu_usage);
    println!("  内存使用率: {:.1}%", current_metrics.resource_metrics.memory_usage);
    println!("  整体健康状态: {}", current_metrics.health_metrics.overall_health);
    
    // 获取自定义指标
    let custom_metrics = metrics_collector.get_all_custom_metrics();
    println!("自定义指标: {:?}", custom_metrics);
    
    // 停止指标收集
    metrics_collector.stop().await?;
    
    Ok(())
}

/// 工具函数示例
async fn utility_functions_example() -> Result<(), UnifiedError> {
    // 持续时间扩展
    let duration = Duration::from_secs(3661);
    println!("持续时间: {}", duration.human_readable());
    
    // 字符串扩展
    let _s = "hello world".to_string();
    // println!("标题格式: {}", s.to_title_case()); // 方法不存在
    // println!("蛇形命名: {}", s.to_snake_case()); // 方法不存在
    // println!("驼峰命名: {}", s.to_camel_case()); // 方法不存在
    
    // 数字扩展
    let _number = 1000000u64;
    // println!("数字: {}", number.human_readable()); // 方法不存在
    // println!("百分比: {:.1}%", number.percentage(2000000)); // 方法不存在
    
    // 性能工具
    // let (result, duration) = PerformanceUtils::measure_time(|| { // 方法不存在
    //     // 模拟一些计算
    //     let mut sum = 0;
    //     for i in 0..1000000 {
    //         sum += i;
    //     }
    //     sum
    // });
    // println!("计算结果: {}, 耗时: {:?}", result, duration);
    
    // 配置工具
    unsafe {
        std::env::set_var("TEST_CONFIG", "test_value");
    }
    // if let Some(value) = ConfigUtils::get_env_var("TEST_CONFIG") { // 方法不存在
    //     println!("环境变量: {}", value);
    // }
    unsafe {
        std::env::remove_var("TEST_CONFIG");
    }
    
    // 错误处理工具
    let _error = UnifiedError::new(
        "测试错误",
        ErrorSeverity::Low,
        "example",
        ErrorContext::new("example", "utility_functions_example", file!(), line!(), ErrorSeverity::Low, "example")
    );
    
    // ErrorHandler::handle_error(&error, "工具函数示例"); // 方法不存在
    
    Ok(())
}

// 健康检查实现示例
#[allow(dead_code)]
struct DatabaseHealthCheck;

#[async_trait]
impl HealthCheck for DatabaseHealthCheck {
    async fn check(&self) -> HealthStatus {
        // 模拟数据库健康检查
        sleep(Duration::from_millis(100)).await;
        
        if rand::random::<bool>() {
            HealthStatus::Healthy
        } else {
            HealthStatus::Degraded("数据库连接缓慢".to_string())
        }
    }
}

#[allow(dead_code)]
struct CacheHealthCheck;

#[async_trait]
impl HealthCheck for CacheHealthCheck {
    async fn check(&self) -> HealthStatus {
        // 模拟缓存健康检查
        sleep(Duration::from_millis(50)).await;
        
        if rand::random::<bool>() {
            HealthStatus::Healthy
        } else {
            HealthStatus::Unhealthy("缓存服务不可用".to_string())
        }
    }
}

#[allow(dead_code)]
struct ExternalServiceHealthCheck;

#[async_trait]
impl HealthCheck for ExternalServiceHealthCheck {
    async fn check(&self) -> HealthStatus {
        // 模拟外部服务健康检查
        sleep(Duration::from_millis(200)).await;
        
        if rand::random::<bool>() {
            HealthStatus::Healthy
        } else {
            HealthStatus::Degraded("外部服务响应缓慢".to_string())
        }
    }
}
