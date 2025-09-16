//! 综合可观测性演示示例
//!
//! 展示如何使用完整的OpenTelemetry可观测性功能，包括：
//! - 日志记录和聚合
//! - 指标收集和导出
//! - 分布式追踪
//! - 健康检查
//! - 性能监控
//! - 错误追踪
//! - 系统状态报告

use c13_microservice::opentelemetry::{
    DatabaseHealthChecker, ErrorSeverity, HealthStatus, OpenTelemetryConfig, OpenTelemetryManager,
    RedisHealthChecker, SystemResourceHealthChecker,
};
use std::collections::HashMap;
use std::thread;
use std::time::Duration;
use tracing::{error, info, warn};
use tracing_subscriber;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志系统
    tracing_subscriber::fmt().with_env_filter("info").init();

    info!("启动综合可观测性演示示例");

    // 创建OpenTelemetry配置
    let config = OpenTelemetryConfig::default();

    // 创建OpenTelemetry管理器
    let mut otel_manager = OpenTelemetryManager::new(config)?;
    otel_manager.init()?;

    info!("OpenTelemetry管理器初始化成功");

    // 添加健康检查器
    let db_checker = DatabaseHealthChecker::new(
        "main_database".to_string(),
        "postgresql://localhost:5432/mydb".to_string(),
    );
    otel_manager.add_health_checker(Box::new(db_checker));

    let redis_checker = RedisHealthChecker::new(
        "redis_cache".to_string(),
        "redis://localhost:6379".to_string(),
    );
    otel_manager.add_health_checker(Box::new(redis_checker));

    let system_checker = SystemResourceHealthChecker::new(
        "system_resources".to_string(),
        80.0, // CPU阈值
        85.0, // 内存阈值
    );
    otel_manager.add_health_checker(Box::new(system_checker));

    // 执行各种演示功能
    simulate_business_operations(&otel_manager).await?;
    demonstrate_error_handling(&otel_manager).await?;
    demonstrate_performance_monitoring(&otel_manager).await?;
    demonstrate_distributed_tracing(&otel_manager).await?;
    generate_system_reports(&otel_manager).await?;
    final_system_report(&otel_manager).await?;

    Ok(())
}

async fn simulate_business_operations(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("开始模拟业务操作");

    // 模拟HTTP请求
    for i in 0..10 {
        let method = if i % 3 == 0 { "GET" } else { "POST" };
        let path = if i % 2 == 0 {
            "/api/users"
        } else {
            "/api/orders"
        };
        let status_code = if i % 5 == 0 { 500 } else { 200 };
        let duration = Duration::from_millis(50 + (i * 10) as u64);

        otel_manager.record_http_request(method, path, status_code, duration);

        // 记录结构化日志
        let mut fields = HashMap::new();
        fields.insert("request_id".to_string(), format!("req_{}", i));
        fields.insert("user_id".to_string(), format!("user_{}", i % 100));

        otel_manager
            .logger()
            .info(&format!("处理请求: {} {}", method, path), Some(fields));

        thread::sleep(Duration::from_millis(100));
    }

    // 模拟数据库查询
    for i in 0..5 {
        let query = if i % 2 == 0 {
            "SELECT * FROM users WHERE active = true"
        } else {
            "INSERT INTO orders (user_id, amount) VALUES (?, ?)"
        };
        let duration = Duration::from_millis(20 + (i * 5) as u64);
        let rows_affected = if i % 2 == 0 { Some(10) } else { Some(1) };

        otel_manager.record_database_query(query, duration, rows_affected);

        thread::sleep(Duration::from_millis(50));
    }

    info!("业务操作模拟完成");
    Ok(())
}

async fn generate_system_reports(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("生成系统报告");

    // 生成完整系统报告
    let system_report = otel_manager.generate_system_report();

    info!("系统整体健康状态: {:?}", system_report.overall_health);
    info!("健康检查数量: {}", system_report.health_checks.len());
    info!(
        "性能监控操作数: {}",
        system_report.performance_summary.monitored_operations
    );
    info!("总错误数: {}", system_report.error_statistics.total_errors);
    info!("日志统计: {:?}", system_report.log_statistics);

    // 导出指标数据
    let metrics_data = otel_manager.metrics().export_metrics()?;
    info!("导出的指标数据长度: {} 字符", metrics_data.len());

    // 导出追踪数据
    let traces_data = otel_manager.tracer().export_traces()?;
    info!("导出的追踪数据长度: {} 字符", traces_data.len());

    Ok(())
}

async fn demonstrate_error_handling(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("演示错误处理功能");

    // 记录不同类型的错误
    let mut context = HashMap::new();
    context.insert("user_id".to_string(), "123".to_string());
    context.insert("operation".to_string(), "create_user".to_string());

    otel_manager.error_tracker().record_error(
        "validation_error",
        "用户邮箱格式无效",
        context.clone(),
        ErrorSeverity::Medium,
    );

    context.insert("database".to_string(), "main_db".to_string());
    context.insert("table".to_string(), "users".to_string());

    otel_manager.error_tracker().record_error(
        "database_error",
        "数据库连接超时",
        context.clone(),
        ErrorSeverity::High,
    );

    context.insert("service".to_string(), "payment_service".to_string());
    context.insert("amount".to_string(), "100.00".to_string());

    otel_manager.error_tracker().record_error(
        "payment_error",
        "支付服务不可用",
        context,
        ErrorSeverity::Critical,
    );

    // 获取错误统计
    let error_stats = otel_manager.error_tracker().get_error_statistics();
    info!("错误统计: {:?}", error_stats);

    // 获取错误模式
    let error_patterns = otel_manager.error_tracker().get_error_patterns();
    info!("错误模式: {:?}", error_patterns);

    Ok(())
}

async fn demonstrate_performance_monitoring(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("演示性能监控功能");

    // 模拟不同性能的操作
    let operations = vec![
        ("fast_operation", Duration::from_millis(10)),
        ("normal_operation", Duration::from_millis(100)),
        ("slow_operation", Duration::from_millis(2000)),
        ("very_slow_operation", Duration::from_millis(5000)),
    ];

    for (operation, duration) in operations {
        let success = duration.as_millis() < 1000; // 超过1秒认为失败

        otel_manager
            .performance_monitor()
            .record_operation(operation, duration, success);

        // 记录带标签的指标
        let mut labels = HashMap::new();
        labels.insert("operation_type".to_string(), operation.to_string());
        labels.insert("environment".to_string(), "demo".to_string());

        otel_manager
            .metrics()
            .record_labeled_timer("operation_duration", labels, duration);

        thread::sleep(Duration::from_millis(50));
    }

    // 获取性能摘要
    let perf_summary = otel_manager.performance_monitor().get_performance_summary();
    info!("性能摘要: {:?}", perf_summary);

    // 获取特定操作的性能数据
    if let Some(perf_data) = otel_manager
        .performance_monitor()
        .get_operation_performance("slow_operation")
    {
        info!("慢操作性能数据: {:?}", perf_data);
    }

    Ok(())
}

async fn demonstrate_distributed_tracing(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("演示分布式追踪功能");

    // 创建根span
    if let Some(mut root_span) = otel_manager
        .tracer()
        .start_root_span("user_registration".to_string())
    {
        root_span.add_attribute("user.email".to_string(), "user@example.com".to_string());
        root_span.add_attribute("user.plan".to_string(), "premium".to_string());

        // 模拟子操作
        thread::sleep(Duration::from_millis(50));

        // 创建子span
        if let Some(mut validation_span) = otel_manager
            .tracer()
            .start_span("validate_user_data".to_string())
        {
            validation_span.add_attribute(
                "validation.rules".to_string(),
                "email,password,username".to_string(),
            );

            thread::sleep(Duration::from_millis(30));

            otel_manager.tracer().finish_span(validation_span);
        }

        // 创建另一个子span
        if let Some(mut db_span) = otel_manager
            .tracer()
            .start_span("save_user_to_database".to_string())
        {
            db_span.add_attribute("db.table".to_string(), "users".to_string());
            db_span.add_attribute("db.operation".to_string(), "insert".to_string());

            thread::sleep(Duration::from_millis(100));

            otel_manager.tracer().finish_span(db_span);
        }

        otel_manager.tracer().finish_span(root_span);
    }

    // 演示HTTP头部传播
    let mut headers = HashMap::new();
    headers.insert("x-trace-id".to_string(), "abc123".to_string());
    headers.insert("x-span-id".to_string(), "def456".to_string());
    headers.insert("x-trace-flags".to_string(), "1".to_string());

    if let Some(context) = otel_manager.tracer().extract_context_from_headers(&headers) {
        info!("从HTTP头部提取的追踪上下文: {:?}", context);

        // 将上下文注入到新的HTTP头部
        let new_headers = otel_manager.tracer().inject_context_to_headers(&context);
        info!("注入到HTTP头部的追踪信息: {:?}", new_headers);
    }

    Ok(())
}

async fn final_system_report(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("生成最终系统报告");

    // 生成最终系统报告
    let final_report = otel_manager.generate_system_report();

    println!("\n=== 最终系统报告 ===");
    println!("时间戳: {}", final_report.timestamp);
    println!("整体健康状态: {:?}", final_report.overall_health);

    println!("\n--- 健康检查结果 ---");
    for check in &final_report.health_checks {
        println!("  {}: {:?} - {}", check.name, check.status, check.message);
    }

    println!("\n--- 性能摘要 ---");
    println!(
        "  总操作数: {}",
        final_report.performance_summary.total_operations
    );
    println!(
        "  总错误数: {}",
        final_report.performance_summary.total_errors
    );
    println!(
        "  错误率: {:.2}%",
        final_report.performance_summary.error_rate * 100.0
    );
    println!(
        "  平均响应时间: {:.2}ms",
        final_report.performance_summary.avg_response_time_ms
    );
    println!(
        "  最慢操作: {}",
        final_report.performance_summary.slowest_operation
    );
    println!(
        "  监控操作数: {}",
        final_report.performance_summary.monitored_operations
    );

    println!("\n--- 错误统计 ---");
    println!("  总错误数: {}", final_report.error_statistics.total_errors);
    println!(
        "  已解决: {}",
        final_report.error_statistics.resolved_errors
    );
    println!(
        "  未解决: {}",
        final_report.error_statistics.unresolved_errors
    );
    println!(
        "  严重错误: {}",
        final_report.error_statistics.critical_severity
    );
    println!(
        "  高级错误: {}",
        final_report.error_statistics.high_severity
    );
    println!(
        "  中级错误: {}",
        final_report.error_statistics.medium_severity
    );
    println!("  低级错误: {}", final_report.error_statistics.low_severity);

    println!("\n--- 日志统计 ---");
    println!("  总日志数: {}", final_report.log_statistics.total_count);
    println!("  错误日志: {}", final_report.log_statistics.error_count);
    println!("  警告日志: {}", final_report.log_statistics.warn_count);
    println!("  信息日志: {}", final_report.log_statistics.info_count);
    println!("  调试日志: {}", final_report.log_statistics.debug_count);

    println!("\n--- 指标统计 ---");
    println!("  计数器: {}", final_report.metrics_summary.total_counters);
    println!("  仪表: {}", final_report.metrics_summary.total_gauges);
    println!(
        "  直方图: {}",
        final_report.metrics_summary.total_histograms
    );
    println!("  计时器: {}", final_report.metrics_summary.total_timers);

    println!("\n--- 追踪统计 ---");
    println!("  活跃Span: {}", final_report.tracing_summary.active_spans);
    println!("  总Span: {}", final_report.tracing_summary.total_spans);

    // 获取系统健康状态
    let health_status = otel_manager.get_system_health();
    match health_status {
        HealthStatus::Healthy => info!("✅ 系统运行正常"),
        HealthStatus::Degraded => warn!("⚠️ 系统性能下降"),
        HealthStatus::Unhealthy => error!("❌ 系统不健康"),
    }

    println!("\n=== 演示完成 ===");
    info!("综合可观测性演示示例执行完成");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use c13_microservice::opentelemetry::HealthChecker;

    #[tokio::test]
    async fn test_otel_manager_creation() {
        let config = OpenTelemetryConfig::default();
        let manager = OpenTelemetryManager::new(config);
        assert!(manager.is_ok());
    }

    #[tokio::test]
    async fn test_health_checkers() {
        let db_checker = DatabaseHealthChecker::new(
            "test_db".to_string(),
            "postgresql://localhost:5432/test".to_string(),
        );

        let redis_checker = RedisHealthChecker::new(
            "test_redis".to_string(),
            "redis://localhost:6379".to_string(),
        );

        let system_checker =
            SystemResourceHealthChecker::new("test_system".to_string(), 90.0, 95.0);

        let db_result = db_checker.check();
        let redis_result = redis_checker.check();
        let system_result = system_checker.check();

        assert_eq!(db_result.name, "test_db");
        assert_eq!(redis_result.name, "test_redis");
        assert_eq!(system_result.name, "test_system");
    }

    #[tokio::test]
    async fn test_error_severity() {
        assert_eq!(ErrorSeverity::Low.to_string(), "low");
        assert_eq!(ErrorSeverity::Medium.to_string(), "medium");
        assert_eq!(ErrorSeverity::High.to_string(), "high");
        assert_eq!(ErrorSeverity::Critical.to_string(), "critical");
    }
}
