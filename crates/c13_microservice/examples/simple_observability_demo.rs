//! 简化的可观测性演示示例
//!
//! 这是一个独立的示例，展示基本的OpenTelemetry可观测性功能
//! 不依赖其他可能有问题的模块

use std::collections::HashMap;
use std::thread;
use std::time::Duration;
use tracing::{error, info, warn};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志系统
    tracing_subscriber::fmt().with_env_filter("info").init();

    info!("启动简化可观测性演示示例");

    // 模拟基本的可观测性功能
    simulate_basic_observability().await?;

    info!("简化可观测性演示示例执行完成");
    Ok(())
}

async fn simulate_basic_observability() -> Result<(), Box<dyn std::error::Error>> {
    info!("开始模拟基本可观测性功能");

    // 模拟HTTP请求记录
    for i in 0..5 {
        let method = if i % 2 == 0 { "GET" } else { "POST" };
        let path = if i % 3 == 0 {
            "/api/users"
        } else {
            "/api/orders"
        };
        let status_code = if i % 4 == 0 { 500 } else { 200 };
        let duration = Duration::from_millis(50 + (i * 10) as u64);

        info!(
            "HTTP请求: {} {} - 状态码: {}, 耗时: {}ms",
            method,
            path,
            status_code,
            duration.as_millis()
        );

        // 记录结构化日志
        let mut fields = HashMap::new();
        fields.insert("request_id".to_string(), format!("req_{}", i));
        fields.insert("user_id".to_string(), format!("user_{}", i % 100));

        info!(
            "处理请求: {} {} - 请求ID: {}, 用户ID: {}",
            method, path, fields["request_id"], fields["user_id"]
        );

        thread::sleep(Duration::from_millis(100));
    }

    // 模拟数据库查询记录
    for i in 0..3 {
        let query = if i % 2 == 0 {
            "SELECT * FROM users WHERE active = true"
        } else {
            "INSERT INTO orders (user_id, amount) VALUES (?, ?)"
        };
        let duration = Duration::from_millis(20 + (i * 5) as u64);
        let rows_affected = if i % 2 == 0 { Some(10) } else { Some(1) };

        info!(
            "数据库查询: {} - 耗时: {}ms, 影响行数: {:?}",
            query,
            duration.as_millis(),
            rows_affected
        );

        thread::sleep(Duration::from_millis(50));
    }

    // 模拟错误记录
    let errors = vec![
        ("validation_error", "用户邮箱格式无效", "medium"),
        ("database_error", "数据库连接超时", "high"),
        ("payment_error", "支付服务不可用", "critical"),
    ];

    for (error_type, message, severity) in errors {
        warn!(
            "错误记录: {} - {} - 严重程度: {}",
            error_type, message, severity
        );

        let mut context = HashMap::new();
        context.insert("error_type".to_string(), error_type.to_string());
        context.insert("severity".to_string(), severity.to_string());
        context.insert("timestamp".to_string(), chrono::Utc::now().to_rfc3339());

        error!("错误详情: {} - 上下文: {:?}", message, context);
    }

    // 模拟性能监控
    let operations = vec![
        ("fast_operation", Duration::from_millis(10)),
        ("normal_operation", Duration::from_millis(100)),
        ("slow_operation", Duration::from_millis(2000)),
    ];

    for (operation, duration) in operations {
        let success = duration.as_millis() < 1000;

        info!(
            "性能监控: {} - 耗时: {}ms, 成功: {}",
            operation,
            duration.as_millis(),
            success
        );

        if !success {
            warn!("性能告警: {} 操作耗时过长", operation);
        }

        thread::sleep(Duration::from_millis(50));
    }

    // 模拟健康检查
    let health_checks = vec![
        ("database", "healthy", "数据库连接正常"),
        ("redis", "healthy", "Redis缓存正常"),
        ("system_resources", "degraded", "CPU使用率较高"),
    ];

    for (service, status, message) in health_checks {
        match status {
            "healthy" => info!("健康检查: {} - 状态: {} - {}", service, status, message),
            "degraded" => warn!("健康检查: {} - 状态: {} - {}", service, status, message),
            "unhealthy" => error!("健康检查: {} - 状态: {} - {}", service, status, message),
            _ => info!("健康检查: {} - 状态: {} - {}", service, status, message),
        }
    }

    // 生成系统报告
    generate_system_report().await?;

    info!("基本可观测性功能模拟完成");
    Ok(())
}

async fn generate_system_report() -> Result<(), Box<dyn std::error::Error>> {
    info!("生成系统报告");

    println!("\n=== 系统报告 ===");
    println!("时间戳: {}", chrono::Utc::now().to_rfc3339());
    println!("整体健康状态: 健康");

    println!("\n--- 健康检查结果 ---");
    println!("  数据库: 健康 - 连接正常");
    println!("  Redis: 健康 - 缓存正常");
    println!("  系统资源: 降级 - CPU使用率较高");

    println!("\n--- 性能摘要 ---");
    println!("  总操作数: 8");
    println!("  总错误数: 3");
    println!("  错误率: 37.50%");
    println!("  平均响应时间: 275.00ms");
    println!("  最慢操作: slow_operation");

    println!("\n--- 错误统计 ---");
    println!("  总错误数: 3");
    println!("  严重错误: 1");
    println!("  高级错误: 1");
    println!("  中级错误: 1");

    println!("\n--- 日志统计 ---");
    println!("  总日志数: 15");
    println!("  错误日志: 3");
    println!("  警告日志: 4");
    println!("  信息日志: 8");

    println!("\n=== 报告完成 ===");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_observability() {
        let result = simulate_basic_observability().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_system_report() {
        let result = generate_system_report().await;
        assert!(result.is_ok());
    }
}
