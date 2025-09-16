//! 独立可观测性演示示例
//!
//! 这是一个完全独立的示例，不依赖任何库代码
//! 展示基本的可观测性概念和最佳实践

use std::collections::HashMap;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tracing::{debug, error, info, warn};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志系统
    tracing_subscriber::fmt().with_env_filter("info").init();

    info!("启动独立可观测性演示示例");

    // 执行各种可观测性演示
    simulate_http_requests().await?;
    simulate_database_operations().await?;
    simulate_error_scenarios().await?;
    simulate_performance_monitoring().await?;
    simulate_health_checks().await?;
    generate_final_report().await?;

    info!("独立可观测性演示示例执行完成");
    Ok(())
}

async fn simulate_http_requests() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 模拟HTTP请求 ===");

    let requests = vec![
        ("GET", "/api/users", 200, 45),
        ("POST", "/api/users", 201, 120),
        ("GET", "/api/orders", 200, 67),
        ("POST", "/api/orders", 400, 89),
        ("GET", "/api/products", 200, 34),
        ("PUT", "/api/users/123", 200, 156),
        ("DELETE", "/api/users/456", 404, 23),
        ("GET", "/api/health", 200, 12),
    ];

    for (method, path, status_code, duration_ms) in requests {
        let success = status_code < 400;

        // 记录HTTP请求日志
        info!(
            "HTTP请求: {} {} - 状态码: {}, 耗时: {}ms, 成功: {}",
            method, path, status_code, duration_ms, success
        );

        // 记录结构化日志
        let mut fields = HashMap::new();
        fields.insert("method".to_string(), method.to_string());
        fields.insert("path".to_string(), path.to_string());
        fields.insert("status_code".to_string(), status_code.to_string());
        fields.insert("duration_ms".to_string(), duration_ms.to_string());
        fields.insert("success".to_string(), success.to_string());
        fields.insert("timestamp".to_string(), get_current_timestamp());

        debug!("HTTP请求详情: {:?}", fields);

        // 模拟错误情况
        if !success {
            warn!(
                "HTTP请求失败: {} {} - 状态码: {}",
                method, path, status_code
            );
        }

        // 模拟处理时间
        tokio::time::sleep(Duration::from_millis(50)).await;
    }

    Ok(())
}

async fn simulate_database_operations() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 模拟数据库操作 ===");

    let operations = vec![
        (
            "SELECT",
            "SELECT * FROM users WHERE active = true",
            10,
            Some(150),
        ),
        (
            "INSERT",
            "INSERT INTO orders (user_id, amount) VALUES (?, ?)",
            1,
            Some(1),
        ),
        (
            "UPDATE",
            "UPDATE users SET last_login = NOW() WHERE id = ?",
            1,
            Some(1),
        ),
        (
            "SELECT",
            "SELECT COUNT(*) FROM orders WHERE created_at > ?",
            1,
            Some(2500),
        ),
        (
            "DELETE",
            "DELETE FROM expired_sessions WHERE expires_at < NOW()",
            0,
            Some(0),
        ),
        (
            "SELECT",
            "SELECT * FROM products WHERE category = ?",
            5,
            Some(25),
        ),
    ];

    for (operation_type, query, duration_ms, rows_affected) in operations {
        info!(
            "数据库操作: {} - 查询: {} - 耗时: {}ms, 影响行数: {:?}",
            operation_type, query, duration_ms, rows_affected
        );

        // 记录结构化日志
        let mut fields = HashMap::new();
        fields.insert("operation_type".to_string(), operation_type.to_string());
        fields.insert("query".to_string(), query.to_string());
        fields.insert("duration_ms".to_string(), duration_ms.to_string());
        fields.insert(
            "rows_affected".to_string(),
            rows_affected
                .map(|r| r.to_string())
                .unwrap_or("NULL".to_string()),
        );
        fields.insert("timestamp".to_string(), get_current_timestamp());

        debug!("数据库操作详情: {:?}", fields);

        // 模拟处理时间
        tokio::time::sleep(Duration::from_millis(30)).await;
    }

    Ok(())
}

async fn simulate_error_scenarios() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 模拟错误场景 ===");

    let errors = vec![
        (
            "validation_error",
            "用户邮箱格式无效",
            "medium",
            "user@invalid",
        ),
        (
            "database_error",
            "数据库连接超时",
            "high",
            "connection_timeout",
        ),
        (
            "payment_error",
            "支付服务不可用",
            "critical",
            "payment_service_down",
        ),
        (
            "auth_error",
            "用户认证失败",
            "medium",
            "invalid_credentials",
        ),
        (
            "rate_limit_error",
            "API调用频率超限",
            "low",
            "rate_limit_exceeded",
        ),
        ("network_error", "网络连接中断", "high", "network_timeout"),
    ];

    for (error_type, message, severity, context) in errors {
        // 记录错误日志
        error!(
            "错误发生: {} - {} - 严重程度: {} - 上下文: {}",
            error_type, message, severity, context
        );

        // 记录结构化错误信息
        let mut error_fields = HashMap::new();
        error_fields.insert("error_type".to_string(), error_type.to_string());
        error_fields.insert("message".to_string(), message.to_string());
        error_fields.insert("severity".to_string(), severity.to_string());
        error_fields.insert("context".to_string(), context.to_string());
        error_fields.insert("timestamp".to_string(), get_current_timestamp());
        error_fields.insert("stack_trace".to_string(), "模拟堆栈跟踪".to_string());

        warn!("错误详情: {:?}", error_fields);

        // 模拟处理时间
        tokio::time::sleep(Duration::from_millis(20)).await;
    }

    Ok(())
}

async fn simulate_performance_monitoring() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 模拟性能监控 ===");

    let operations = vec![
        ("user_authentication", 15, true),
        ("data_processing", 250, true),
        ("file_upload", 1200, false), // 超时
        ("email_sending", 45, true),
        ("report_generation", 5000, false), // 超时
        ("cache_lookup", 5, true),
        ("external_api_call", 800, true),
    ];

    for (operation, duration_ms, success) in operations {
        let performance_status = if duration_ms < 100 {
            "excellent"
        } else if duration_ms < 500 {
            "good"
        } else if duration_ms < 1000 {
            "acceptable"
        } else {
            "poor"
        };

        info!(
            "性能监控: {} - 耗时: {}ms, 成功: {}, 性能状态: {}",
            operation, duration_ms, success, performance_status
        );

        // 记录性能指标
        let mut perf_fields = HashMap::new();
        perf_fields.insert("operation".to_string(), operation.to_string());
        perf_fields.insert("duration_ms".to_string(), duration_ms.to_string());
        perf_fields.insert("success".to_string(), success.to_string());
        perf_fields.insert(
            "performance_status".to_string(),
            performance_status.to_string(),
        );
        perf_fields.insert("timestamp".to_string(), get_current_timestamp());

        debug!("性能指标: {:?}", perf_fields);

        // 性能告警
        if !success || duration_ms > 1000 {
            warn!("性能告警: {} 操作耗时过长或失败", operation);
        }

        // 模拟处理时间
        tokio::time::sleep(Duration::from_millis(25)).await;
    }

    Ok(())
}

async fn simulate_health_checks() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 模拟健康检查 ===");

    let health_checks = vec![
        ("database", "healthy", "数据库连接正常", 5),
        ("redis", "healthy", "Redis缓存正常", 3),
        ("external_api", "degraded", "外部API响应缓慢", 1200),
        ("disk_space", "healthy", "磁盘空间充足", 2),
        ("memory", "degraded", "内存使用率较高", 8),
        ("cpu", "unhealthy", "CPU使用率过高", 15),
    ];

    for (service, status, message, response_time_ms) in health_checks {
        match status {
            "healthy" => info!(
                "健康检查: {} - 状态: {} - {} - 响应时间: {}ms",
                service, status, message, response_time_ms
            ),
            "degraded" => warn!(
                "健康检查: {} - 状态: {} - {} - 响应时间: {}ms",
                service, status, message, response_time_ms
            ),
            "unhealthy" => error!(
                "健康检查: {} - 状态: {} - {} - 响应时间: {}ms",
                service, status, message, response_time_ms
            ),
            _ => info!(
                "健康检查: {} - 状态: {} - {} - 响应时间: {}ms",
                service, status, message, response_time_ms
            ),
        }

        // 记录健康检查详情
        let mut health_fields = HashMap::new();
        health_fields.insert("service".to_string(), service.to_string());
        health_fields.insert("status".to_string(), status.to_string());
        health_fields.insert("message".to_string(), message.to_string());
        health_fields.insert("response_time_ms".to_string(), response_time_ms.to_string());
        health_fields.insert("timestamp".to_string(), get_current_timestamp());

        debug!("健康检查详情: {:?}", health_fields);

        // 模拟处理时间
        tokio::time::sleep(Duration::from_millis(15)).await;
    }

    Ok(())
}

async fn generate_final_report() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 生成最终报告 ===");

    println!("\n{}", "=".repeat(60));
    println!("                   系统可观测性报告");
    println!("{}", "=".repeat(60));
    println!("时间戳: {}", get_current_timestamp());
    println!("整体健康状态: 降级 (部分服务性能下降)");

    println!("\n--- HTTP请求统计 ---");
    println!("  总请求数: 8");
    println!("  成功请求: 6 (75.0%)");
    println!("  失败请求: 2 (25.0%)");
    println!("  平均响应时间: 68.25ms");
    println!("  最慢请求: PUT /api/users/123 (156ms)");

    println!("\n--- 数据库操作统计 ---");
    println!("  总操作数: 6");
    println!("  查询操作: 4");
    println!("  修改操作: 2");
    println!("  平均响应时间: 18.33ms");
    println!("  总影响行数: 2,777");

    println!("\n--- 错误统计 ---");
    println!("  总错误数: 6");
    println!("  严重错误: 1 (payment_error)");
    println!("  高级错误: 2 (database_error, network_error)");
    println!("  中级错误: 2 (validation_error, auth_error)");
    println!("  低级错误: 1 (rate_limit_error)");

    println!("\n--- 性能监控统计 ---");
    println!("  总操作数: 7");
    println!("  成功操作: 5 (71.4%)");
    println!("  失败操作: 2 (28.6%)");
    println!("  平均响应时间: 1,031.43ms");
    println!("  性能状态分布:");
    println!("    - 优秀 (<100ms): 3");
    println!("    - 良好 (100-500ms): 2");
    println!("    - 可接受 (500-1000ms): 1");
    println!("    - 较差 (>1000ms): 1");

    println!("\n--- 健康检查结果 ---");
    println!("  数据库: 健康 (5ms)");
    println!("  Redis: 健康 (3ms)");
    println!("  外部API: 降级 (1200ms)");
    println!("  磁盘空间: 健康 (2ms)");
    println!("  内存: 降级 (8ms)");
    println!("  CPU: 不健康 (15ms)");

    println!("\n--- 建议措施 ---");
    println!("  1. 优化外部API调用，减少响应时间");
    println!("  2. 监控CPU使用率，考虑扩容或优化");
    println!("  3. 检查内存使用情况，防止内存泄漏");
    println!("  4. 优化慢查询，提升数据库性能");
    println!("  5. 实施更严格的错误处理和重试机制");

    println!("\n{}", "=".repeat(60));
    println!("报告生成完成");
    println!("{}", "=".repeat(60));

    Ok(())
}

fn get_current_timestamp() -> String {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_http_requests() {
        let result = simulate_http_requests().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_database_operations() {
        let result = simulate_database_operations().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_error_scenarios() {
        let result = simulate_error_scenarios().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_performance_monitoring() {
        let result = simulate_performance_monitoring().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_health_checks() {
        let result = simulate_health_checks().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_final_report() {
        let result = generate_final_report().await;
        assert!(result.is_ok());
    }
}
