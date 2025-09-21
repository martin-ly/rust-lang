//! 错误处理演示示例
//! 
//! 展示如何使用c17_iot的错误处理功能来管理IoT设备中的各种错误

use c17_iot::error_handling::{
    ErrorHandler, ErrorType, ErrorSeverity, RecoveryStrategy, RecoveryConfig
};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动错误处理演示...");

    // 创建错误处理配置
    let config = RecoveryConfig {
        max_retries: 3,
        initial_retry_interval: Duration::from_secs(1),
        max_retry_interval: Duration::from_secs(30),
        backoff_multiplier: 2.0,
        strategy: RecoveryStrategy::ExponentialBackoff,
        auto_recovery_enabled: true,
        recovery_timeout: Duration::from_secs(60),
    };

    // 创建错误处理器
    let error_handler = ErrorHandler::new(config);

    println!("📊 开始模拟IoT设备错误场景...");

    // 1. 网络错误模拟
    println!("\n1️⃣ 网络错误处理演示");
    simulate_network_errors(&error_handler).await?;

    // 2. 设备错误模拟
    println!("\n2️⃣ 设备错误处理演示");
    simulate_device_errors(&error_handler).await?;

    // 3. 数据错误模拟
    println!("\n3️⃣ 数据错误处理演示");
    simulate_data_errors(&error_handler).await?;

    // 4. 配置错误模拟
    println!("\n4️⃣ 配置错误处理演示");
    simulate_configuration_errors(&error_handler).await?;

    // 5. 认证错误模拟
    println!("\n5️⃣ 认证错误处理演示");
    simulate_authentication_errors(&error_handler).await?;

    // 6. 资源错误模拟
    println!("\n6️⃣ 资源错误处理演示");
    simulate_resource_errors(&error_handler).await?;

    // 7. 系统错误模拟
    println!("\n7️⃣ 系统错误处理演示");
    simulate_system_errors(&error_handler).await?;

    // 等待一段时间让自动恢复完成
    println!("\n⏳ 等待自动恢复完成...");
    sleep(Duration::from_secs(10)).await;

    // 8. 错误统计和分析
    println!("\n8️⃣ 错误统计和分析");
    let stats = error_handler.get_stats().await;
    println!("总错误数: {}", stats.total_errors);
    println!("按严重程度统计:");
    for (severity, count) in &stats.errors_by_severity {
        println!("  {:?}: {} 个", severity, count);
    }
    println!("按类型统计:");
    for (error_type, count) in &stats.errors_by_type {
        println!("  {:?}: {} 个", error_type, count);
    }
    println!("按组件统计:");
    for (component, count) in &stats.errors_by_component {
        println!("  {}: {} 个", component, count);
    }

    // 9. 生成错误报告
    println!("\n9️⃣ 生成错误报告");
    let report = error_handler.generate_error_report().await;
    println!("错误报告已生成 ({} 字符)", report.len());
    
    // 显示报告的前几行
    let lines: Vec<&str> = report.lines().take(20).collect();
    for line in lines {
        println!("{}", line);
    }

    // 10. 错误恢复演示
    println!("\n🔟 错误恢复演示");
    let all_errors = error_handler.get_all_errors().await;
    let recovered_errors: Vec<_> = all_errors.iter().filter(|e| e.recovered).collect();
    let unrecovered_errors: Vec<_> = all_errors.iter().filter(|e| !e.recovered).collect();
    
    println!("已恢复错误: {} 个", recovered_errors.len());
    println!("未恢复错误: {} 个", unrecovered_errors.len());
    
    if !unrecovered_errors.is_empty() {
        println!("未恢复的错误:");
        for error in &unrecovered_errors {
            println!("  - {}: {} (重试次数: {}/{})", 
                error.component, 
                error.message, 
                error.retry_count, 
                error.max_retries
            );
        }
    }

    println!("\n✅ 错误处理演示完成!");
    println!("🎯 演示展示了以下功能:");
    println!("  - 多种错误类型处理");
    println!("  - 自动恢复策略");
    println!("  - 错误统计和分析");
    println!("  - 错误报告生成");
    println!("  - 恢复状态跟踪");

    Ok(())
}

/// 模拟网络错误
async fn simulate_network_errors(error_handler: &ErrorHandler) -> Result<(), Box<dyn std::error::Error>> {
    println!("  模拟网络连接失败...");
    error_handler.record_error(
        ErrorType::Network,
        ErrorSeverity::High,
        "网络连接超时".to_string(),
        "network_manager".to_string(),
        Some("connect".to_string()),
        Some("连接服务器超时，可能是网络不稳定".to_string()),
    ).await;

    println!("  模拟网络数据传输错误...");
    error_handler.record_error(
        ErrorType::Network,
        ErrorSeverity::Medium,
        "数据传输失败".to_string(),
        "data_transmitter".to_string(),
        Some("send_data".to_string()),
        Some("数据包丢失，需要重传".to_string()),
    ).await;

    println!("  模拟网络断开连接...");
    error_handler.record_error(
        ErrorType::Network,
        ErrorSeverity::Critical,
        "网络连接断开".to_string(),
        "network_manager".to_string(),
        Some("maintain_connection".to_string()),
        Some("与服务器的连接意外断开".to_string()),
    ).await;

    Ok(())
}

/// 模拟设备错误
async fn simulate_device_errors(error_handler: &ErrorHandler) -> Result<(), Box<dyn std::error::Error>> {
    println!("  模拟传感器读取错误...");
    error_handler.record_error(
        ErrorType::Device,
        ErrorSeverity::Medium,
        "传感器读取失败".to_string(),
        "temperature_sensor".to_string(),
        Some("read_temperature".to_string()),
        Some("I2C通信失败，传感器无响应".to_string()),
    ).await;

    println!("  模拟设备初始化错误...");
    error_handler.record_error(
        ErrorType::Device,
        ErrorSeverity::High,
        "设备初始化失败".to_string(),
        "device_manager".to_string(),
        Some("initialize_device".to_string()),
        Some("设备固件版本不兼容".to_string()),
    ).await;

    println!("  模拟设备硬件故障...");
    error_handler.record_error(
        ErrorType::Device,
        ErrorSeverity::Critical,
        "硬件故障检测".to_string(),
        "hardware_monitor".to_string(),
        Some("health_check".to_string()),
        Some("检测到硬件异常，需要维护".to_string()),
    ).await;

    Ok(())
}

/// 模拟数据错误
async fn simulate_data_errors(error_handler: &ErrorHandler) -> Result<(), Box<dyn std::error::Error>> {
    println!("  模拟数据验证错误...");
    error_handler.record_error(
        ErrorType::Data,
        ErrorSeverity::Low,
        "数据格式错误".to_string(),
        "data_validator".to_string(),
        Some("validate_data".to_string()),
        Some("接收到的数据格式不符合预期".to_string()),
    ).await;

    println!("  模拟数据完整性错误...");
    error_handler.record_error(
        ErrorType::Data,
        ErrorSeverity::Medium,
        "数据完整性检查失败".to_string(),
        "data_processor".to_string(),
        Some("process_data".to_string()),
        Some("数据校验和不匹配".to_string()),
    ).await;

    println!("  模拟数据解析错误...");
    error_handler.record_error(
        ErrorType::Data,
        ErrorSeverity::Medium,
        "JSON解析失败".to_string(),
        "json_parser".to_string(),
        Some("parse_json".to_string()),
        Some("无效的JSON格式".to_string()),
    ).await;

    Ok(())
}

/// 模拟配置错误
async fn simulate_configuration_errors(error_handler: &ErrorHandler) -> Result<(), Box<dyn std::error::Error>> {
    println!("  模拟配置文件错误...");
    error_handler.record_error(
        ErrorType::Configuration,
        ErrorSeverity::High,
        "配置文件加载失败".to_string(),
        "config_manager".to_string(),
        Some("load_config".to_string()),
        Some("配置文件不存在或格式错误".to_string()),
    ).await;

    println!("  模拟配置参数错误...");
    error_handler.record_error(
        ErrorType::Configuration,
        ErrorSeverity::Medium,
        "无效的配置参数".to_string(),
        "config_validator".to_string(),
        Some("validate_config".to_string()),
        Some("MQTT端口号超出有效范围".to_string()),
    ).await;

    Ok(())
}

/// 模拟认证错误
async fn simulate_authentication_errors(error_handler: &ErrorHandler) -> Result<(), Box<dyn std::error::Error>> {
    println!("  模拟认证失败...");
    error_handler.record_error(
        ErrorType::Authentication,
        ErrorSeverity::High,
        "设备认证失败".to_string(),
        "auth_manager".to_string(),
        Some("authenticate_device".to_string()),
        Some("设备证书已过期".to_string()),
    ).await;

    println!("  模拟令牌刷新失败...");
    error_handler.record_error(
        ErrorType::Authentication,
        ErrorSeverity::Medium,
        "访问令牌刷新失败".to_string(),
        "token_manager".to_string(),
        Some("refresh_token".to_string()),
        Some("刷新令牌无效".to_string()),
    ).await;

    Ok(())
}

/// 模拟资源错误
async fn simulate_resource_errors(error_handler: &ErrorHandler) -> Result<(), Box<dyn std::error::Error>> {
    println!("  模拟内存不足...");
    error_handler.record_error(
        ErrorType::Resource,
        ErrorSeverity::High,
        "内存分配失败".to_string(),
        "memory_manager".to_string(),
        Some("allocate_memory".to_string()),
        Some("系统内存不足，无法分配新内存".to_string()),
    ).await;

    println!("  模拟磁盘空间不足...");
    error_handler.record_error(
        ErrorType::Resource,
        ErrorSeverity::Medium,
        "磁盘空间不足".to_string(),
        "storage_manager".to_string(),
        Some("write_file".to_string()),
        Some("磁盘空间不足，无法写入文件".to_string()),
    ).await;

    println!("  模拟文件句柄耗尽...");
    error_handler.record_error(
        ErrorType::Resource,
        ErrorSeverity::High,
        "文件句柄耗尽".to_string(),
        "file_manager".to_string(),
        Some("open_file".to_string()),
        Some("系统文件句柄已用完".to_string()),
    ).await;

    Ok(())
}

/// 模拟系统错误
async fn simulate_system_errors(error_handler: &ErrorHandler) -> Result<(), Box<dyn std::error::Error>> {
    println!("  模拟系统服务错误...");
    error_handler.record_error(
        ErrorType::System,
        ErrorSeverity::Critical,
        "系统服务崩溃".to_string(),
        "system_service".to_string(),
        Some("run_service".to_string()),
        Some("关键系统服务意外终止".to_string()),
    ).await;

    println!("  模拟系统资源耗尽...");
    error_handler.record_error(
        ErrorType::System,
        ErrorSeverity::High,
        "系统资源耗尽".to_string(),
        "resource_monitor".to_string(),
        Some("monitor_resources".to_string()),
        Some("CPU使用率持续过高".to_string()),
    ).await;

    println!("  模拟系统调用失败...");
    error_handler.record_error(
        ErrorType::System,
        ErrorSeverity::Medium,
        "系统调用失败".to_string(),
        "system_interface".to_string(),
        Some("system_call".to_string()),
        Some("底层系统调用返回错误".to_string()),
    ).await;

    Ok(())
}
