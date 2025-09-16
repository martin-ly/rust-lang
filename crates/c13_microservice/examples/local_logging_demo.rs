//! 本地日志功能演示示例
//!
//! 展示如何使用完整的本地日志功能，包括：
//! - 日志滚动（按大小和时间）
//! - 日志压缩
//! - 固定缓存大小管理
//! - 按日期文件命名
//! - 异步写入
//! - 性能监控

use c13_microservice::opentelemetry::{
    CompressionStrategy, LocalLogConfig, LocalLogLevel, LocalLogManager, LogFormat,
    RotationStrategy,
};
use std::collections::HashMap;
use std::thread;
use std::time::Duration;
use tracing::{
    info,
    //    warn,
    //    error,
};
use tracing_subscriber;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志系统
    tracing_subscriber::fmt().with_env_filter("info").init();

    info!("启动本地日志功能演示示例");

    // 演示不同的日志配置
    demonstrate_basic_logging().await?;
    demonstrate_size_rotation().await?;
    demonstrate_time_rotation().await?;
    demonstrate_compression().await?;
    demonstrate_performance().await?;
    demonstrate_different_formats().await?;

    info!("本地日志功能演示示例执行完成");
    Ok(())
}

async fn demonstrate_basic_logging() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 演示基本日志功能 ===");

    // 创建基本配置
    let config = LocalLogConfig {
        log_dir: std::path::PathBuf::from("logs/basic"),
        file_prefix: "basic".to_string(),
        level: LocalLogLevel::Debug,
        rotation_strategy: RotationStrategy::Size {
            max_size_bytes: 1024 * 1024,
        }, // 1MB
        compression_strategy: CompressionStrategy::None,
        max_files: 5,
        cache_size_bytes: 512 * 1024, // 512KB
        async_write: true,
        enable_console: true,
        enable_file: true,
        format: LogFormat::Text,
        include_timestamp: true,
        include_thread_id: true,
    };

    let manager = LocalLogManager::new(config)?;

    // 记录不同级别的日志
    manager.log(LocalLogLevel::Debug, "这是一条调试日志", None);
    manager.log(LocalLogLevel::Info, "这是一条信息日志", None);
    manager.log(LocalLogLevel::Warn, "这是一条警告日志", None);
    manager.log(LocalLogLevel::Error, "这是一条错误日志", None);

    // 记录带字段的日志
    let mut fields = HashMap::new();
    fields.insert("user_id".to_string(), "12345".to_string());
    fields.insert("action".to_string(), "login".to_string());
    fields.insert("ip".to_string(), "192.168.1.1".to_string());

    manager.log(LocalLogLevel::Info, "用户登录成功", Some(fields));

    // 获取统计信息
    let stats = manager.get_stats();
    info!(
        "日志统计: 缓存条目={}, 缓存大小={}字节, 当前文件大小={}字节",
        stats.cache_entries, stats.cache_size_bytes, stats.current_file_size_bytes
    );

    // 强制刷新
    manager.flush()?;

    // 关闭管理器
    manager.shutdown()?;

    info!("基本日志功能演示完成");
    Ok(())
}

async fn demonstrate_size_rotation() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 演示按大小轮转日志 ===");

    let config = LocalLogConfig {
        log_dir: std::path::PathBuf::from("logs/size_rotation"),
        file_prefix: "size_rotation".to_string(),
        level: LocalLogLevel::Info,
        rotation_strategy: RotationStrategy::Size {
            max_size_bytes: 1024,
        }, // 1KB，便于演示
        compression_strategy: CompressionStrategy::None,
        max_files: 3,
        cache_size_bytes: 1024 * 1024, // 1MB
        async_write: true,
        enable_console: false, // 关闭控制台输出以便观察文件
        enable_file: true,
        format: LogFormat::Text,
        include_timestamp: true,
        include_thread_id: false,
    };

    let manager = LocalLogManager::new(config)?;

    // 写入大量日志以触发轮转
    for i in 0..100 {
        let message = format!("这是第{}条日志消息，内容比较长以便快速达到文件大小限制", i);
        manager.log(LocalLogLevel::Info, &message, None);

        // 每10条日志检查一次统计
        if i % 10 == 0 {
            let stats = manager.get_stats();
            info!(
                "已写入{}条日志，当前文件大小: {}字节",
                i + 1,
                stats.current_file_size_bytes
            );
        }

        thread::sleep(Duration::from_millis(10));
    }

    // 强制刷新并获取最终统计
    manager.flush()?;
    let final_stats = manager.get_stats();
    info!(
        "最终统计: 缓存条目={}, 当前文件大小={}字节",
        final_stats.cache_entries, final_stats.current_file_size_bytes
    );

    manager.shutdown()?;

    info!("按大小轮转日志演示完成");
    Ok(())
}

async fn demonstrate_time_rotation() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 演示按时间轮转日志 ===");

    let config = LocalLogConfig {
        log_dir: std::path::PathBuf::from("logs/time_rotation"),
        file_prefix: "time_rotation".to_string(),
        level: LocalLogLevel::Info,
        rotation_strategy: RotationStrategy::Time { interval_hours: 1 }, // 1小时轮转
        compression_strategy: CompressionStrategy::None,
        max_files: 5,
        cache_size_bytes: 1024 * 1024,
        async_write: true,
        enable_console: false,
        enable_file: true,
        format: LogFormat::Json,
        include_timestamp: true,
        include_thread_id: true,
    };

    let manager = LocalLogManager::new(config)?;

    // 记录一些日志
    for i in 0..20 {
        let mut fields = HashMap::new();
        fields.insert("iteration".to_string(), i.to_string());
        fields.insert("timestamp".to_string(), chrono::Local::now().to_rfc3339());

        manager.log(
            LocalLogLevel::Info,
            &format!("时间轮转测试消息 {}", i),
            Some(fields),
        );
        thread::sleep(Duration::from_millis(100));
    }

    manager.flush()?;
    let stats = manager.get_stats();
    info!("时间轮转测试完成，当前文件: {:?}", stats.current_file_path);

    manager.shutdown()?;

    info!("按时间轮转日志演示完成");
    Ok(())
}

async fn demonstrate_compression() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 演示日志压缩功能 ===");

    let config = LocalLogConfig {
        log_dir: std::path::PathBuf::from("logs/compression"),
        file_prefix: "compression".to_string(),
        level: LocalLogLevel::Info,
        rotation_strategy: RotationStrategy::Size {
            max_size_bytes: 2 * 1024,
        }, // 2KB
        compression_strategy: CompressionStrategy::Immediate, // 立即压缩
        max_files: 5,
        cache_size_bytes: 1024 * 1024,
        async_write: true,
        enable_console: false,
        enable_file: true,
        format: LogFormat::Text,
        include_timestamp: true,
        include_thread_id: false,
    };

    let manager = LocalLogManager::new(config)?;

    // 写入大量日志以触发轮转和压缩
    for i in 0..200 {
        let message = format!(
            "压缩测试消息 {} - 这是一条比较长的日志消息，用于测试压缩功能的效果",
            i
        );
        manager.log(LocalLogLevel::Info, &message, None);

        if i % 50 == 0 {
            let stats = manager.get_stats();
            info!(
                "已写入{}条日志，当前文件大小: {}字节",
                i + 1,
                stats.current_file_size_bytes
            );
        }

        thread::sleep(Duration::from_millis(5));
    }

    manager.flush()?;
    manager.shutdown()?;

    // 等待压缩完成
    thread::sleep(Duration::from_secs(2));

    info!("日志压缩功能演示完成");
    Ok(())
}

async fn demonstrate_performance() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 演示性能测试 ===");

    let config = LocalLogConfig {
        log_dir: std::path::PathBuf::from("logs/performance"),
        file_prefix: "performance".to_string(),
        level: LocalLogLevel::Info,
        rotation_strategy: RotationStrategy::Size {
            max_size_bytes: 10 * 1024 * 1024,
        }, // 10MB
        compression_strategy: CompressionStrategy::Delayed { days: 1 },
        max_files: 10,
        cache_size_bytes: 2 * 1024 * 1024, // 2MB缓存
        async_write: true,
        enable_console: false,
        enable_file: true,
        format: LogFormat::Compact,
        include_timestamp: true,
        include_thread_id: false,
    };

    let manager = LocalLogManager::new(config)?;

    let start_time = std::time::Instant::now();
    let log_count = 10000;

    // 性能测试：写入大量日志
    for i in 0..log_count {
        let mut fields = HashMap::new();
        fields.insert("request_id".to_string(), format!("req_{}", i));
        fields.insert("user_id".to_string(), format!("user_{}", i % 1000));
        fields.insert("action".to_string(), "api_call".to_string());

        manager.log(
            LocalLogLevel::Info,
            &format!("性能测试消息 {}", i),
            Some(fields),
        );

        // 每1000条日志报告一次进度
        if i % 1000 == 0 && i > 0 {
            let elapsed = start_time.elapsed();
            let rate = i as f64 / elapsed.as_secs_f64();
            info!("已写入{}条日志，速率: {:.2} 条/秒", i, rate);
        }
    }

    let total_time = start_time.elapsed();
    let rate = log_count as f64 / total_time.as_secs_f64();

    info!(
        "性能测试完成: 写入{}条日志，耗时{:?}，平均速率: {:.2} 条/秒",
        log_count, total_time, rate
    );

    // 获取最终统计
    manager.flush()?;
    let stats = manager.get_stats();
    info!(
        "最终统计: 缓存条目={}, 缓存大小={}字节, 文件大小={}字节",
        stats.cache_entries, stats.cache_size_bytes, stats.current_file_size_bytes
    );

    manager.shutdown()?;

    info!("性能测试演示完成");
    Ok(())
}

async fn demonstrate_different_formats() -> Result<(), Box<dyn std::error::Error>> {
    info!("=== 演示不同日志格式 ===");

    let formats = vec![
        (LogFormat::Text, "text"),
        (LogFormat::Json, "json"),
        (LogFormat::Compact, "compact"),
    ];

    for (format, format_name) in formats {
        info!("演示{}格式", format_name);

        let config = LocalLogConfig {
            log_dir: std::path::PathBuf::from(format!("logs/format_{}", format_name)),
            file_prefix: format_name.to_string(),
            level: LocalLogLevel::Info,
            rotation_strategy: RotationStrategy::Size {
                max_size_bytes: 1024 * 1024,
            },
            compression_strategy: CompressionStrategy::None,
            max_files: 3,
            cache_size_bytes: 1024 * 1024,
            async_write: true,
            enable_console: false,
            enable_file: true,
            format,
            include_timestamp: true,
            include_thread_id: true,
        };

        let manager = LocalLogManager::new(config)?;

        // 记录不同类型的日志
        let mut fields = HashMap::new();
        fields.insert("service".to_string(), "demo_service".to_string());
        fields.insert("version".to_string(), "1.0.0".to_string());
        fields.insert("environment".to_string(), "development".to_string());

        manager.log(
            LocalLogLevel::Info,
            "这是一条信息日志",
            Some(fields.clone()),
        );

        fields.insert("error_code".to_string(), "E001".to_string());
        fields.insert("error_message".to_string(), "示例错误".to_string());
        manager.log(LocalLogLevel::Error, "这是一条错误日志", Some(fields));

        manager.flush()?;
        manager.shutdown()?;

        info!("{}格式演示完成", format_name);
    }

    info!("不同日志格式演示完成");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[tokio::test]
    async fn test_local_log_manager_creation() {
        let temp_dir = tempdir().unwrap();
        let config = LocalLogConfig {
            log_dir: temp_dir.path().to_path_buf(),
            ..Default::default()
        };

        let manager = LocalLogManager::new(config);
        assert!(manager.is_ok());
    }

    #[tokio::test]
    async fn test_log_levels() {
        let temp_dir = tempdir().unwrap();
        let config = LocalLogConfig {
            log_dir: temp_dir.path().to_path_buf(),
            level: LocalLogLevel::Warn,
            enable_console: false,
            ..Default::default()
        };

        let manager = LocalLogManager::new(config).unwrap();

        manager.log(LocalLogLevel::Debug, "Debug message", None);
        manager.log(LocalLogLevel::Info, "Info message", None);
        manager.log(LocalLogLevel::Warn, "Warn message", None);
        manager.log(LocalLogLevel::Error, "Error message", None);

        manager.flush().unwrap();

        // 只有Warn和Error级别的日志应该被记录
        let stats = manager.get_stats();
        assert!(stats.cache_entries >= 2);
    }

    #[tokio::test]
    async fn test_log_rotation() {
        let temp_dir = tempdir().unwrap();
        let config = LocalLogConfig {
            log_dir: temp_dir.path().to_path_buf(),
            rotation_strategy: RotationStrategy::Size {
                max_size_bytes: 100,
            },
            enable_console: false,
            ..Default::default()
        };

        let manager = LocalLogManager::new(config).unwrap();

        // 写入大量日志以触发轮转
        for i in 0..100 {
            manager.log(LocalLogLevel::Info, &format!("Test message {}", i), None);
        }

        manager.flush().unwrap();

        // 检查是否创建了多个日志文件
        let entries: Vec<_> = std::fs::read_dir(temp_dir.path()).unwrap().collect();
        assert!(entries.len() > 1);
    }

    #[tokio::test]
    async fn test_log_compression() {
        let temp_dir = tempdir().unwrap();
        let config = LocalLogConfig {
            log_dir: temp_dir.path().to_path_buf(),
            compression_strategy: CompressionStrategy::Immediate,
            enable_console: false,
            ..Default::default()
        };

        let manager = LocalLogManager::new(config).unwrap();
        manager.log(LocalLogLevel::Info, "Test message", None);
        manager.flush().unwrap();
        manager.shutdown().unwrap();

        // 检查是否创建了压缩文件
        let entries: Vec<_> = std::fs::read_dir(temp_dir.path()).unwrap().collect();
        let has_gz_file = entries.iter().any(|entry| {
            entry
                .as_ref()
                .unwrap()
                .path()
                .extension()
                .and_then(|s| s.to_str())
                == Some("gz")
        });
        assert!(has_gz_file);
    }
}
