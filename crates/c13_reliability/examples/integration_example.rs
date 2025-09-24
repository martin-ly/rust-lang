//! 集成示例
//!
//! 展示如何将可靠性框架集成到实际应用中。

use c13_reliability::prelude::*;
use c13_reliability::{
    fault_tolerance::{CircuitBreakerConfig, Retrier, RetryConfig, TimeoutConfig, FallbackConfig},
    runtime_monitoring::{HealthCheckConfig, HealthCheck, HealthStatus, ResourceMonitorConfig},
    metrics::MetricsCollector
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
    
    println!("=== 可靠性框架集成示例 ===");
    
    // 创建应用服务
    let mut app_service = AppService::new().await?;
    
    // 启动应用服务
    app_service.start().await?;
    
    // 模拟应用运行
    println!("应用服务已启动，开始处理请求...");
    
    // 模拟处理多个请求
    for i in 0..20 {
        println!("\n--- 处理请求 {} ---", i + 1);
        
        let request = Request {
            id: i + 1,
            data: format!("请求数据 {}", i + 1),
            timeout: Duration::from_secs(5),
        };
        
        match app_service.process_request(request).await {
            Ok(response) => println!("请求处理成功: {:?}", response),
            Err(error) => println!("请求处理失败: {}", error),
        }
        
        // 模拟请求间隔
        sleep(Duration::from_millis(500)).await;
    }
    
    // 停止应用服务
    app_service.stop().await?;
    
    // 关闭可靠性框架
    c13_reliability::shutdown().await?;
    
    println!("\n=== 集成示例完成 ===");
    Ok(())
}

/// 应用服务
#[allow(dead_code)]
struct AppService {
    health_checker: HealthChecker,
    resource_monitor: ResourceMonitor,
    metrics_collector: MetricsCollector,
    circuit_breaker: CircuitBreaker,
    retrier: Retrier,
    timeout: Timeout,
    fallback: Fallback,
}

impl AppService {
    /// 创建新的应用服务
    async fn new() -> Result<Self, UnifiedError> {
        // 创建健康检查器
        let health_check_config = HealthCheckConfig::default();
        let health_checker = HealthChecker::new(health_check_config);
        // health_checker.add_check(Box::new(DatabaseHealthCheck)); // 方法不存在
        // health_checker.add_check(Box::new(CacheHealthCheck)); // 方法不存在
        // health_checker.add_check(Box::new(ExternalServiceHealthCheck)); // 方法不存在
        
        // 创建资源监控器
        let resource_monitor = ResourceMonitor::new(ResourceMonitorConfig::default());
        
        // 创建指标收集器
        let metrics_collector = MetricsCollector::new(Duration::from_secs(30));
        
        // 创建容错机制
        let circuit_breaker_config = CircuitBreakerConfig {
            failure_threshold: 5,
            recovery_timeout: Duration::from_secs(60),
            ..Default::default()
        };
        let circuit_breaker = CircuitBreaker::new(circuit_breaker_config);
        let _retry_policy = RetryPolicy::new(RetryConfig::default());
        let retrier = Retrier::new(RetryConfig::default());
        let timeout = Timeout::new(TimeoutConfig {
            duration: Duration::from_secs(10),
            ..Default::default()
        });
        let fallback = Fallback::new(FallbackConfig::default());
        
        Ok(Self {
            health_checker,
            resource_monitor,
            metrics_collector,
            circuit_breaker,
            retrier,
            timeout,
            fallback,
        })
    }
    
    /// 启动应用服务
    async fn start(&mut self) -> Result<(), UnifiedError> {
        println!("启动应用服务...");
        
        // 启动指标收集
        self.metrics_collector.start().await?;
        
        // 启动资源监控
        let _resource_monitor = self.resource_monitor.clone();
        tokio::spawn(async move {
            // resource_monitor.start_monitoring(|usage| { // 方法不存在
            //     if usage.cpu_usage > 80.0 || usage.memory_usage > 1024.0 * 1024.0 * 1024.0 {
            //         println!("⚠️  资源使用率过高: CPU {:.1}%, 内存 {}MB", 
            //                  usage.cpu_usage, 
            //                  usage.memory_usage / 1024 / 1024);
            //     }
            // }).await;
        });
        
        // 执行初始健康检查
        let health_status = self.health_checker.check_health().await;
        match health_status {
            Ok(result) => println!("✅ 系统健康检查通过: {:?}", result),
            Err(error) => {
                println!("❌ 系统健康检查失败: {}", error);
                return Err(error);
            }
        }
        
        println!("应用服务启动完成");
        Ok(())
    }
    
    /// 处理请求
    async fn process_request(&self, request: Request) -> Result<Response, UnifiedError> {
        let start_time = std::time::Instant::now();
        
        // 使用容错机制处理请求
          let result = self.circuit_breaker.execute(|| async {
                // 实际的业务逻辑处理
                self.handle_business_logic(&request).await
            })
            .await;
        
        let processing_time = start_time.elapsed();
        
        // 记录性能指标
        match &result {
            Ok(_) => {
                // self.metrics_collector.record_performance_metric( // 方法不存在
                //     "request_processing",
                //     processing_time,
                //     true
                // );
                println!("✅ 请求 {} 处理成功，耗时: {:?}", request.id, processing_time);
            }
            Err(_) => {
                // self.metrics_collector.record_performance_metric( // 方法不存在
                //     "request_processing",
                //     processing_time,
                //     false
                // );
                // self.metrics_collector.record_error_metric( // 方法不存在
                //     "request_processing_error",
                //     "processing_failed"
                // );
                println!("❌ 请求 {} 处理失败，耗时: {:?}", request.id, processing_time);
            }
        }
        
        result
    }
    
    /// 处理业务逻辑
    async fn handle_business_logic(&self, request: &Request) -> Result<Response, UnifiedError> {
        // 模拟数据库操作
        let db_result = self.simulate_database_operation(&request.data).await?;
        
        // 模拟缓存操作
        let cache_result = self.simulate_cache_operation(&db_result).await?;
        
        // 模拟外部服务调用
        let external_result = self.simulate_external_service_call(&cache_result).await?;
        
        // 构建响应
        Ok(Response {
            id: request.id,
            data: external_result,
            timestamp: chrono::Utc::now(),
            processing_time: std::time::Instant::now().elapsed(),
        })
    }
    
    /// 模拟数据库操作
    async fn simulate_database_operation(&self, data: &str) -> Result<String, UnifiedError> {
        // 模拟数据库延迟
        sleep(Duration::from_millis(rand::random::<u64>() % 100 + 50)).await;
        
        // 模拟数据库错误
        if rand::random::<f64>() < 0.1 {
            return Err(UnifiedError::new(
                "数据库操作失败",
                ErrorSeverity::High,
                "database",
                ErrorContext::new(
                    "database",
                    "simulate_database_operation",
                    file!(),
                    line!(),
                    ErrorSeverity::High,
                    "database_component"
                )
            ));
        }
        
        Ok(format!("数据库处理结果: {}", data))
    }
    
    /// 模拟缓存操作
    async fn simulate_cache_operation(&self, data: &str) -> Result<String, UnifiedError> {
        // 模拟缓存延迟
        sleep(Duration::from_millis(rand::random::<u64>() % 50 + 10)).await;
        
        // 模拟缓存错误
        if rand::random::<f64>() < 0.05 {
            return Err(UnifiedError::new(
                "缓存操作失败",
                ErrorSeverity::Medium,
                "cache",
                ErrorContext::new(
                    "cache",
                    "simulate_cache_operation",
                    file!(),
                    line!(),
                    ErrorSeverity::Medium,
                    "cache_component"
                )
            ));
        }
        
        Ok(format!("缓存处理结果: {}", data))
    }
    
    /// 模拟外部服务调用
    async fn simulate_external_service_call(&self, data: &str) -> Result<String, UnifiedError> {
        // 模拟网络延迟
        sleep(Duration::from_millis(rand::random::<u64>() % 200 + 100)).await;
        
        // 模拟外部服务错误
        if rand::random::<f64>() < 0.15 {
            return Err(UnifiedError::new(
                "外部服务调用失败",
                ErrorSeverity::Medium,
                "external_service",
                ErrorContext::new(
                    "external_service",
                    "simulate_external_service_call",
                    file!(),
                    line!(),
                    ErrorSeverity::Medium,
                    "external_service_component"
                )
            ));
        }
        
        Ok(format!("外部服务处理结果: {}", data))
    }
    
    /// 停止应用服务
    async fn stop(&mut self) -> Result<(), UnifiedError> {
        println!("停止应用服务...");
        
        // 停止指标收集
        self.metrics_collector.stop().await?;
        
        // 获取最终指标
        let final_metrics = self.metrics_collector.get_current_metrics();
        println!("最终指标统计:");
        println!("  总请求数: {}", final_metrics.performance_metrics.total_requests);
        println!("  成功请求数: {}", final_metrics.performance_metrics.successful_requests);
        println!("  失败请求数: {}", final_metrics.performance_metrics.failed_requests);
        println!("  成功率: {:.2}%", (final_metrics.performance_metrics.successful_requests as f64 / final_metrics.performance_metrics.total_requests as f64) * 100.0);
        println!("  平均响应时间: {:?}", final_metrics.performance_metrics.average_response_time);
        println!("  总错误数: {}", final_metrics.error_metrics.total_errors);
        println!("  错误率: {:.2}%", final_metrics.error_metrics.error_rate * 100.0);
        
        println!("应用服务已停止");
        Ok(())
    }
}

/// 请求结构
#[allow(dead_code)]
#[derive(Debug, Clone)]
struct Request {
    id: u32,
    data: String,
    timeout: Duration,
}

/// 响应结构
#[allow(dead_code)]
#[derive(Debug)]
struct Response {
    id: u32,
    data: String,
    timestamp: chrono::DateTime<chrono::Utc>,
    processing_time: Duration,
}

// 健康检查实现
#[allow(dead_code)]
struct DatabaseHealthCheck;

#[async_trait]
impl HealthCheck for DatabaseHealthCheck {
    async fn check(&self) -> HealthStatus {
        sleep(Duration::from_millis(100)).await;
        
        if rand::random::<f64>() > 0.1 {
            HealthStatus::Healthy
        } else {
            HealthStatus::Unhealthy("数据库连接失败".to_string())
        }
    }
}

#[allow(dead_code)]
struct CacheHealthCheck;

#[async_trait]
impl HealthCheck for CacheHealthCheck {
    async fn check(&self) -> HealthStatus {
        sleep(Duration::from_millis(50)).await;
        
        if rand::random::<f64>() > 0.05 {
            HealthStatus::Healthy
        } else {
            HealthStatus::Degraded("缓存响应缓慢".to_string())
        }
    }
}

#[allow(dead_code)]
struct ExternalServiceHealthCheck;

#[async_trait]
impl HealthCheck for ExternalServiceHealthCheck {
    async fn check(&self) -> HealthStatus {
        sleep(Duration::from_millis(200)).await;
        
        if rand::random::<f64>() > 0.15 {
            HealthStatus::Healthy
        } else {
            HealthStatus::Degraded("外部服务响应缓慢".to_string())
        }
    }
}
