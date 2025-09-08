//! 中间件演示
//! 
//! 展示如何使用实用的中间件功能

use c13_microservice::{
    middleware::practical_middleware::{
        MiddlewareManager, RequestTracingMiddleware, RateLimitMiddleware,
        HealthCheckMiddleware, ErrorHandlingMiddleware,
    },
    error::Result,
};
use tracing::info;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    info!("🚀 启动中间件演示");
    
    // 创建中间件管理器
    let middleware_manager = MiddlewareManager::new();
    
    // 演示请求追踪
    demo_request_tracing(&middleware_manager).await?;
    
    // 演示限流功能
    demo_rate_limiting(&middleware_manager).await?;
    
    // 演示健康检查
    demo_health_check(&middleware_manager).await?;
    
    // 演示错误处理
    demo_error_handling(&middleware_manager).await?;
    
    // 演示综合使用
    demo_comprehensive_usage(&middleware_manager).await?;
    
    info!("✅ 中间件演示完成");
    Ok(())
}

/// 演示请求追踪
async fn demo_request_tracing(middleware_manager: &MiddlewareManager) -> Result<()> {
    info!("📊 演示请求追踪");
    
    // 模拟不同类型的请求
    let requests = vec![
        ("GET", "/api/users", "client1"),
        ("POST", "/api/users", "client1"),
        ("GET", "/api/products", "client2"),
        ("PUT", "/api/users/123", "client1"),
        ("DELETE", "/api/users/456", "client2"),
    ];
    
    for (method, path, client_id) in requests {
        let result = middleware_manager.process_request(method, path, client_id).await;
        
        match result {
            c13_microservice::middleware::practical_middleware::RequestResult::Success { 
                request_id: _, 
                status_code, 
                duration 
            } => {
                info!(
                    "请求处理成功: {} {} -> {} ({}ms)",
                    method, path, status_code, duration.as_millis()
                );
            }
            _ => {
                info!("请求处理结果: {:?}", result);
            }
        }
        
        // 模拟请求间隔
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }
    
    Ok(())
}

/// 演示限流功能
async fn demo_rate_limiting(middleware_manager: &MiddlewareManager) -> Result<()> {
    info!("🚦 演示限流功能");
    
    let client_id = "test_client";
    
    // 快速发送多个请求来触发限流
    for i in 0..15 {
        let result = middleware_manager.process_request("GET", "/api/test", client_id).await;
        
        match result {
            c13_microservice::middleware::practical_middleware::RequestResult::Success { 
                request_id: _, 
                status_code, 
                duration 
            } => {
                info!(
                    "请求 {} 成功: {} ({}ms)",
                    i + 1, status_code, duration.as_millis()
                );
            }
            c13_microservice::middleware::practical_middleware::RequestResult::RateLimited => {
                info!("请求 {} 被限流", i + 1);
                break;
            }
            _ => {
                info!("请求 {} 结果: {:?}", i + 1, result);
            }
        }
        
        // 快速发送请求
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    }
    
    // 等待一段时间后恢复
    info!("等待限流恢复...");
    tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
    
    // 测试恢复后的请求
    let result = middleware_manager.process_request("GET", "/api/test", client_id).await;
    match result {
        c13_microservice::middleware::practical_middleware::RequestResult::Success { 
            status_code, 
            .. 
        } => {
            info!("限流恢复后请求成功: {}", status_code);
        }
        _ => {
            info!("限流恢复后请求结果: {:?}", result);
        }
    }
    
    Ok(())
}

/// 演示健康检查
async fn demo_health_check(middleware_manager: &MiddlewareManager) -> Result<()> {
    info!("🏥 演示健康检查");
    
    let health_endpoints = vec!["/health", "/healthz", "/status"];
    
    for endpoint in health_endpoints {
        let result = middleware_manager.process_request("GET", endpoint, "health_checker").await;
        
        match result {
            c13_microservice::middleware::practical_middleware::RequestResult::HealthCheck(health_result) => {
                info!("健康检查结果: {:?}", health_result);
            }
            _ => {
                info!("健康检查端点 {} 结果: {:?}", endpoint, result);
            }
        }
    }
    
    Ok(())
}

/// 演示错误处理
async fn demo_error_handling(middleware_manager: &MiddlewareManager) -> Result<()> {
    info!("⚠️  演示错误处理");
    
    // 模拟不同类型的错误
    let errors = vec![
        Box::new(std::io::Error::new(std::io::ErrorKind::NotFound, "文件未找到")) as Box<dyn std::error::Error>,
        Box::new(std::io::Error::new(std::io::ErrorKind::PermissionDenied, "权限不足")) as Box<dyn std::error::Error>,
        Box::new(std::io::Error::new(std::io::ErrorKind::ConnectionRefused, "连接被拒绝")) as Box<dyn std::error::Error>,
    ];
    
    for (i, error) in errors.iter().enumerate() {
        let request_id = format!("error_test_{}", i + 1);
        let error_response = middleware_manager.handle_error(error.as_ref(), &request_id);
        
        info!("错误处理结果 {}: {:?}", i + 1, error_response);
    }
    
    Ok(())
}

/// 演示综合使用
async fn demo_comprehensive_usage(middleware_manager: &MiddlewareManager) -> Result<()> {
    info!("🔄 演示综合使用");
    
    // 模拟真实的API请求场景
    let api_requests = vec![
        ("GET", "/api/users", "user_client"),
        ("POST", "/api/users", "user_client"),
        ("GET", "/api/products", "product_client"),
        ("GET", "/health", "monitoring_client"),
        ("GET", "/api/orders", "order_client"),
        ("PUT", "/api/users/123", "user_client"),
        ("DELETE", "/api/users/456", "admin_client"),
    ];
    
    for (method, path, client_id) in api_requests {
        info!("处理请求: {} {} (客户端: {})", method, path, client_id);
        
        let result = middleware_manager.process_request(method, path, client_id).await;
        
        match result {
            c13_microservice::middleware::practical_middleware::RequestResult::Success { 
                request_id: _, 
                status_code, 
                duration 
            } => {
                info!(
                    "✅ 请求成功: {} {} -> {} ({}ms)",
                    method, path, status_code, duration.as_millis()
                );
            }
            c13_microservice::middleware::practical_middleware::RequestResult::RateLimited => {
                info!("🚦 请求被限流: {} {}", method, path);
            }
            c13_microservice::middleware::practical_middleware::RequestResult::HealthCheck(health_result) => {
                info!("🏥 健康检查: {} -> {:?}", path, health_result);
            }
        }
        
        // 模拟请求间隔
        tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
    }
    
    Ok(())
}

/// 演示中间件配置
#[allow(dead_code)]
async fn demo_middleware_configuration() -> Result<()> {
    info!("⚙️  演示中间件配置");
    
    // 创建自定义配置的中间件
    let custom_tracing = RequestTracingMiddleware::new()
        .with_headers(true)
        .with_body(false);
    
    let custom_rate_limit = RateLimitMiddleware {
        requests_per_minute: 120,
        requests_per_hour: 2000,
        burst_size: 20,
        enabled: true,
    };
    
    let custom_health_check = HealthCheckMiddleware::new()
        .with_endpoints(vec!["/health".to_string(), "/status".to_string(), "/ping".to_string()])
        .with_detailed_health(true)
        .with_dependency_check(true);
    
    let custom_error_handling = ErrorHandlingMiddleware::new()
        .with_detailed_errors(true)
        .with_error_threshold(5);
    
    info!("自定义中间件配置完成:");
    info!("  - 请求追踪: 记录请求头={}, 记录请求体={}", 
          custom_tracing.log_headers, custom_tracing.log_body);
    info!("  - 限流: {}/分钟, {}/小时, 突发={}", 
          custom_rate_limit.requests_per_minute, 
          custom_rate_limit.requests_per_hour, 
          custom_rate_limit.burst_size);
    info!("  - 健康检查: 端点={:?}, 详细检查={}, 依赖检查={}", 
          custom_health_check.health_endpoints,
          custom_health_check.detailed_health,
          custom_health_check.check_dependencies);
    info!("  - 错误处理: 详细错误={}, 阈值={}", 
          custom_error_handling.return_detailed_errors,
          custom_error_handling.error_threshold);
    
    Ok(())
}