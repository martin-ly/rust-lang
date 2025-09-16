//! 集成日志功能演示示例
//!
//! 展示如何将本地日志功能与OpenTelemetry可观测性系统结合使用：
//! - 本地日志与OpenTelemetry日志的协同工作
//! - 统一的日志管理接口
//! - 性能监控与本地日志记录
//! - 错误追踪与本地日志存储
//! - 分布式追踪与本地日志关联

use c13_microservice::opentelemetry::{
    CompressionStrategy, DatabaseHealthChecker, ErrorSeverity, HealthStatus, LocalLogConfig,
    LocalLogLevel, LogFormat, OpenTelemetryConfig, OpenTelemetryManager, RedisHealthChecker,
    RotationStrategy, SystemResourceHealthChecker,
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

    info!("启动集成日志功能演示示例");

    // 创建OpenTelemetry配置
    let config = OpenTelemetryConfig::default();

    // 创建OpenTelemetry管理器
    let mut otel_manager = OpenTelemetryManager::new(config)?;
    otel_manager.init()?;

    // 配置本地日志
    let local_log_config = LocalLogConfig {
        log_dir: std::path::PathBuf::from("logs/integrated"),
        file_prefix: "integrated".to_string(),
        level: LocalLogLevel::Debug,
        rotation_strategy: RotationStrategy::SizeAndTime {
            max_size_bytes: 5 * 1024 * 1024, // 5MB
            interval_hours: 24,              // 24小时
        },
        compression_strategy: CompressionStrategy::Delayed { days: 1 },
        max_files: 10,
        cache_size_bytes: 2 * 1024 * 1024, // 2MB
        async_write: true,
        enable_console: true,
        enable_file: true,
        format: LogFormat::Json,
        include_timestamp: true,
        include_thread_id: true,
    };

    // 启用本地日志
    otel_manager.enable_local_logging(local_log_config)?;

    info!("OpenTelemetry管理器和本地日志初始化成功");

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
    demonstrate_integrated_logging(&otel_manager).await?;
    demonstrate_performance_with_local_logs(&otel_manager).await?;
    demonstrate_error_tracking_with_local_logs(&otel_manager).await?;
    demonstrate_health_monitoring_with_local_logs(&otel_manager).await?;
    demonstrate_distributed_tracing_with_local_logs(&otel_manager).await?;
    generate_comprehensive_reports(&otel_manager).await?;

    info!("集成日志功能演示示例执行完成");
    Ok(())
}

async fn demonstrate_integrated_logging(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 演示集成日志功能 ===");

    // 记录本地日志
    let mut fields = HashMap::new();
    fields.insert("service".to_string(), "demo_service".to_string());
    fields.insert("version".to_string(), "1.0.0".to_string());
    fields.insert("environment".to_string(), "development".to_string());

    otel_manager.log_local(LocalLogLevel::Info, "服务启动", Some(fields.clone()));

    // 模拟业务操作并记录日志
    for i in 0..10 {
        let mut request_fields = HashMap::new();
        request_fields.insert("request_id".to_string(), format!("req_{}", i));
        request_fields.insert("user_id".to_string(), format!("user_{}", i % 100));
        request_fields.insert("endpoint".to_string(), "/api/users".to_string());

        // 记录本地日志
        otel_manager.log_local(
            LocalLogLevel::Info,
            &format!("处理用户请求 {}", i),
            Some(request_fields.clone()),
        );

        // 模拟HTTP请求（这会同时记录到OpenTelemetry和本地日志）
        let method = if i % 3 == 0 { "GET" } else { "POST" };
        let path = if i % 2 == 0 {
            "/api/users"
        } else {
            "/api/orders"
        };
        let status_code = if i % 5 == 0 { 500 } else { 200 };
        let duration = Duration::from_millis(50 + (i * 10) as u64);

        otel_manager.record_http_request(method, path, status_code, duration);

        thread::sleep(Duration::from_millis(100));
    }

    // 记录服务状态
    otel_manager.log_local(LocalLogLevel::Info, "服务运行正常", Some(fields));

    info!("集成日志功能演示完成");
    Ok(())
}

async fn demonstrate_performance_with_local_logs(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 演示性能监控与本地日志 ===");

    let start_time = std::time::Instant::now();
    let operation_count = 1000;

    // 记录性能测试开始
    let mut perf_fields = HashMap::new();
    perf_fields.insert("test_type".to_string(), "performance".to_string());
    perf_fields.insert("operation_count".to_string(), operation_count.to_string());
    otel_manager.log_local(LocalLogLevel::Info, "开始性能测试", Some(perf_fields));

    // 执行性能测试
    for i in 0..operation_count {
        let _operation_start = std::time::Instant::now();

        // 模拟数据库查询
        let query = if i % 2 == 0 {
            "SELECT * FROM users WHERE active = true"
        } else {
            "INSERT INTO orders (user_id, amount) VALUES (?, ?)"
        };
        let duration = Duration::from_millis(20 + (i % 50) as u64);
        let rows_affected = if i % 2 == 0 { Some(10) } else { Some(1) };

        otel_manager.record_database_query(query, duration, rows_affected);

        // 记录性能数据到本地日志
        if i % 100 == 0 {
            let elapsed = start_time.elapsed();
            let rate = i as f64 / elapsed.as_secs_f64();

            let mut rate_fields = HashMap::new();
            rate_fields.insert("operations_completed".to_string(), i.to_string());
            rate_fields.insert("rate_ops_per_sec".to_string(), format!("{:.2}", rate));
            rate_fields.insert(
                "elapsed_time_ms".to_string(),
                elapsed.as_millis().to_string(),
            );

            otel_manager.log_local(
                LocalLogLevel::Info,
                &format!("性能测试进度: {}/{}", i, operation_count),
                Some(rate_fields),
            );
        }

        thread::sleep(Duration::from_millis(1));
    }

    let total_time = start_time.elapsed();
    let rate = operation_count as f64 / total_time.as_secs_f64();

    // 记录性能测试结果
    let mut result_fields = HashMap::new();
    result_fields.insert("total_operations".to_string(), operation_count.to_string());
    result_fields.insert(
        "total_time_ms".to_string(),
        total_time.as_millis().to_string(),
    );
    result_fields.insert("avg_rate_ops_per_sec".to_string(), format!("{:.2}", rate));

    otel_manager.log_local(LocalLogLevel::Info, "性能测试完成", Some(result_fields));

    info!("性能监控与本地日志演示完成");
    Ok(())
}

async fn demonstrate_error_tracking_with_local_logs(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 演示错误追踪与本地日志 ===");

    // 记录不同类型的错误
    let error_scenarios = vec![
        (
            "validation_error",
            "用户邮箱格式无效",
            ErrorSeverity::Medium,
        ),
        ("database_error", "数据库连接超时", ErrorSeverity::High),
        ("payment_error", "支付服务不可用", ErrorSeverity::Critical),
        ("network_error", "网络连接失败", ErrorSeverity::High),
        ("auth_error", "用户认证失败", ErrorSeverity::Medium),
    ];

    for (i, (error_type, error_message, severity)) in error_scenarios.iter().enumerate() {
        let mut context = HashMap::new();
        context.insert("error_id".to_string(), format!("err_{}", i));
        context.insert("error_type".to_string(), error_type.to_string());
        context.insert("severity".to_string(), format!("{:?}", severity));
        context.insert("timestamp".to_string(), chrono::Local::now().to_rfc3339());

        // 记录错误到OpenTelemetry
        otel_manager.error_tracker().record_error(
            error_type,
            error_message,
            context.clone(),
            *severity,
        );

        // 记录错误到本地日志
        let log_level = match severity {
            ErrorSeverity::Critical | ErrorSeverity::High => LocalLogLevel::Error,
            ErrorSeverity::Medium => LocalLogLevel::Warn,
            ErrorSeverity::Low => LocalLogLevel::Info,
        };

        otel_manager.log_local(
            log_level,
            &format!("错误发生: {} - {}", error_type, error_message),
            Some(context),
        );

        thread::sleep(Duration::from_millis(200));
    }

    // 获取错误统计并记录到本地日志
    let error_stats = otel_manager.error_tracker().get_error_statistics();
    let mut stats_fields = HashMap::new();
    stats_fields.insert(
        "total_errors".to_string(),
        error_stats.total_errors.to_string(),
    );
    stats_fields.insert(
        "critical_errors".to_string(),
        error_stats.critical_severity.to_string(),
    );
    stats_fields.insert(
        "high_errors".to_string(),
        error_stats.high_severity.to_string(),
    );
    stats_fields.insert(
        "medium_errors".to_string(),
        error_stats.medium_severity.to_string(),
    );
    stats_fields.insert(
        "low_errors".to_string(),
        error_stats.low_severity.to_string(),
    );

    otel_manager.log_local(LocalLogLevel::Info, "错误统计汇总", Some(stats_fields));

    info!("错误追踪与本地日志演示完成");
    Ok(())
}

async fn demonstrate_health_monitoring_with_local_logs(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 演示健康监控与本地日志 ===");

    // 生成系统报告
    let system_report = otel_manager.generate_system_report();

    // 记录健康状态到本地日志
    let mut health_fields = HashMap::new();
    health_fields.insert(
        "overall_health".to_string(),
        format!("{:?}", system_report.overall_health),
    );
    health_fields.insert(
        "health_checks_count".to_string(),
        system_report.health_checks.len().to_string(),
    );
    health_fields.insert("timestamp".to_string(), system_report.timestamp.to_string());

    otel_manager.log_local(LocalLogLevel::Info, "系统健康状态检查", Some(health_fields));

    // 记录每个健康检查的详细结果
    for check in &system_report.health_checks {
        let mut check_fields = HashMap::new();
        check_fields.insert("check_name".to_string(), check.name.clone());
        check_fields.insert("status".to_string(), format!("{:?}", check.status));
        check_fields.insert("message".to_string(), check.message.clone());
        check_fields.insert("duration_ms".to_string(), check.duration_ms.to_string());

        let log_level = match check.status {
            HealthStatus::Healthy => LocalLogLevel::Info,
            HealthStatus::Degraded => LocalLogLevel::Warn,
            HealthStatus::Unhealthy => LocalLogLevel::Error,
        };

        otel_manager.log_local(
            log_level,
            &format!("健康检查: {}", check.name),
            Some(check_fields),
        );
    }

    // 记录性能摘要
    let perf_summary = &system_report.performance_summary;
    let mut perf_fields = HashMap::new();
    perf_fields.insert(
        "total_operations".to_string(),
        perf_summary.total_operations.to_string(),
    );
    perf_fields.insert(
        "total_errors".to_string(),
        perf_summary.total_errors.to_string(),
    );
    perf_fields.insert(
        "error_rate".to_string(),
        format!("{:.2}%", perf_summary.error_rate * 100.0),
    );
    perf_fields.insert(
        "avg_response_time_ms".to_string(),
        format!("{:.2}", perf_summary.avg_response_time_ms),
    );
    perf_fields.insert(
        "slowest_operation".to_string(),
        perf_summary.slowest_operation.clone(),
    );

    otel_manager.log_local(LocalLogLevel::Info, "性能摘要", Some(perf_fields));

    info!("健康监控与本地日志演示完成");
    Ok(())
}

async fn demonstrate_distributed_tracing_with_local_logs(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 演示分布式追踪与本地日志 ===");

    // 创建根span
    if let Some(mut root_span) = otel_manager
        .tracer()
        .start_root_span("user_registration_flow".to_string())
    {
        root_span.add_attribute("user.email".to_string(), "user@example.com".to_string());
        root_span.add_attribute("user.plan".to_string(), "premium".to_string());

        // 记录追踪开始到本地日志
        let mut trace_fields = HashMap::new();
        trace_fields.insert("trace_id".to_string(), "user_registration_flow".to_string());
        trace_fields.insert("operation".to_string(), "user_registration".to_string());
        trace_fields.insert("user_email".to_string(), "user@example.com".to_string());

        otel_manager.log_local(
            LocalLogLevel::Info,
            "开始用户注册流程追踪",
            Some(trace_fields),
        );

        // 模拟子操作
        thread::sleep(Duration::from_millis(50));

        // 创建子span - 数据验证
        if let Some(mut validation_span) = otel_manager
            .tracer()
            .start_span("validate_user_data".to_string())
        {
            validation_span.add_attribute(
                "validation.rules".to_string(),
                "email,password,username".to_string(),
            );

            // 记录验证步骤到本地日志
            let mut validation_fields = HashMap::new();
            validation_fields.insert("step".to_string(), "data_validation".to_string());
            validation_fields.insert("rules".to_string(), "email,password,username".to_string());

            otel_manager.log_local(
                LocalLogLevel::Debug,
                "执行用户数据验证",
                Some(validation_fields),
            );

            thread::sleep(Duration::from_millis(30));

            otel_manager.tracer().finish_span(validation_span);
        }

        // 创建子span - 数据库操作
        if let Some(mut db_span) = otel_manager
            .tracer()
            .start_span("save_user_to_database".to_string())
        {
            db_span.add_attribute("db.table".to_string(), "users".to_string());
            db_span.add_attribute("db.operation".to_string(), "insert".to_string());

            // 记录数据库操作到本地日志
            let mut db_fields = HashMap::new();
            db_fields.insert("step".to_string(), "database_operation".to_string());
            db_fields.insert("table".to_string(), "users".to_string());
            db_fields.insert("operation".to_string(), "insert".to_string());

            otel_manager.log_local(LocalLogLevel::Info, "保存用户数据到数据库", Some(db_fields));

            thread::sleep(Duration::from_millis(100));

            otel_manager.tracer().finish_span(db_span);
        }

        // 记录追踪完成到本地日志
        let mut completion_fields = HashMap::new();
        completion_fields.insert("trace_id".to_string(), "user_registration_flow".to_string());
        completion_fields.insert("status".to_string(), "completed".to_string());

        otel_manager.log_local(
            LocalLogLevel::Info,
            "用户注册流程追踪完成",
            Some(completion_fields),
        );

        otel_manager.tracer().finish_span(root_span);
    }

    info!("分布式追踪与本地日志演示完成");
    Ok(())
}

async fn generate_comprehensive_reports(
    otel_manager: &OpenTelemetryManager,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 生成综合报告 ===");

    // 生成最终系统报告
    let final_report = otel_manager.generate_system_report();

    // 记录系统报告到本地日志
    let mut report_fields = HashMap::new();
    report_fields.insert(
        "report_type".to_string(),
        "comprehensive_system_report".to_string(),
    );
    report_fields.insert("timestamp".to_string(), final_report.timestamp.to_string());
    report_fields.insert(
        "overall_health".to_string(),
        format!("{:?}", final_report.overall_health),
    );
    report_fields.insert(
        "health_checks_count".to_string(),
        final_report.health_checks.len().to_string(),
    );
    report_fields.insert(
        "total_operations".to_string(),
        final_report
            .performance_summary
            .total_operations
            .to_string(),
    );
    report_fields.insert(
        "total_errors".to_string(),
        final_report.error_statistics.total_errors.to_string(),
    );

    otel_manager.log_local(LocalLogLevel::Info, "生成综合系统报告", Some(report_fields));

    // 打印详细报告到控制台
    println!("\n=== 综合系统报告 ===");
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

    println!("\n--- 错误统计 ---");
    println!("  总错误数: {}", final_report.error_statistics.total_errors);
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

    // 获取本地日志统计
    if let Some(local_log_manager) = otel_manager.local_log_manager() {
        let log_stats = local_log_manager.get_stats();

        let mut log_stats_fields = HashMap::new();
        log_stats_fields.insert(
            "cache_entries".to_string(),
            log_stats.cache_entries.to_string(),
        );
        log_stats_fields.insert(
            "cache_size_bytes".to_string(),
            log_stats.cache_size_bytes.to_string(),
        );
        log_stats_fields.insert(
            "current_file_size_bytes".to_string(),
            log_stats.current_file_size_bytes.to_string(),
        );
        log_stats_fields.insert(
            "current_file_path".to_string(),
            log_stats.current_file_path.to_string_lossy().to_string(),
        );

        otel_manager.log_local(LocalLogLevel::Info, "本地日志统计", Some(log_stats_fields));

        println!("\n--- 本地日志统计 ---");
        println!("  缓存条目: {}", log_stats.cache_entries);
        println!("  缓存大小: {} 字节", log_stats.cache_size_bytes);
        println!("  当前文件大小: {} 字节", log_stats.current_file_size_bytes);
        println!("  当前文件路径: {:?}", log_stats.current_file_path);
    }

    // 获取系统健康状态
    let health_status = otel_manager.get_system_health();
    match health_status {
        HealthStatus::Healthy => {
            otel_manager.log_local(LocalLogLevel::Info, "系统运行正常", None);
            info!("✅ 系统运行正常");
        }
        HealthStatus::Degraded => {
            otel_manager.log_local(LocalLogLevel::Warn, "系统性能下降", None);
            warn!("⚠️ 系统性能下降");
        }
        HealthStatus::Unhealthy => {
            otel_manager.log_local(LocalLogLevel::Error, "系统不健康", None);
            error!("❌ 系统不健康");
        }
    }

    println!("\n=== 演示完成 ===");
    info!("综合报告生成完成");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[tokio::test]
    async fn test_integrated_logging() {
        let temp_dir = tempdir().unwrap();
        let config = OpenTelemetryConfig::default();
        let mut manager = OpenTelemetryManager::new(config).unwrap();
        manager.init().unwrap();

        let local_log_config = LocalLogConfig {
            log_dir: temp_dir.path().to_path_buf(),
            ..Default::default()
        };

        manager.enable_local_logging(local_log_config).unwrap();

        // 测试集成日志记录
        let mut fields = HashMap::new();
        fields.insert("test".to_string(), "integration".to_string());

        manager.log_local(LocalLogLevel::Info, "Test message", Some(fields));
        manager.record_http_request("GET", "/test", 200, Duration::from_millis(100));

        // 验证本地日志管理器存在
        assert!(manager.local_log_manager().is_some());
    }

    #[tokio::test]
    async fn test_error_tracking_with_local_logs() {
        let temp_dir = tempdir().unwrap();
        let config = OpenTelemetryConfig::default();
        let mut manager = OpenTelemetryManager::new(config).unwrap();
        manager.init().unwrap();

        let local_log_config = LocalLogConfig {
            log_dir: temp_dir.path().to_path_buf(),
            ..Default::default()
        };

        manager.enable_local_logging(local_log_config).unwrap();

        // 记录错误
        let mut context = HashMap::new();
        context.insert("error_type".to_string(), "test_error".to_string());

        manager.error_tracker().record_error(
            "test_error",
            "Test error message",
            context.clone(),
            ErrorSeverity::Medium,
        );

        // 记录到本地日志
        manager.log_local(LocalLogLevel::Error, "Test error occurred", Some(context));

        // 验证错误统计
        let error_stats = manager.error_tracker().get_error_statistics();
        assert!(error_stats.total_errors > 0);
    }
}
