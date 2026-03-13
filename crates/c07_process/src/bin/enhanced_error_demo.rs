//! 增强的错误处理演示程序
//! 
//! 这个程序展示了增强的错误处理功能，包括错误恢复、
//! 错误链追踪、错误分类等 Rust 1.90 新特性
#[cfg(feature = "async")]
use c07_process::prelude::*;
#[cfg(feature = "async")]
use c07_process::{
    EnhancedErrorManager, EnhancedErrorEntry, ErrorSeverity,
    RecoveryStrategy, RecoveryResult, ErrorManagerConfig,
};
#[cfg(feature = "async")]
use c07_process::error::{ProcessError, IpcError, SyncError, ResourceError, PlatformError, ConfigError};
#[cfg(feature = "async")]
use std::collections::HashMap;
#[cfg(feature = "async")]
use std::time::Duration;

#[cfg(feature = "async")]
#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 增强的错误处理演示程序");
    println!("========================\n");

    // 创建增强的错误管理器
    println!("🔧 创建增强的错误管理器...");
    let config = ErrorManagerConfig {
        max_history_size: 1000,
        retention_duration: Duration::from_secs(3600),
        auto_recovery: true,
        auto_classification: true,
        auto_notification: true,
        chain_tracking: true,
        performance_monitoring: true,
    };
    let manager = EnhancedErrorManager::new(config).await;
    println!("✅ 增强的错误管理器创建成功！\n");

    // 演示基础错误处理功能
    println!("1️⃣ 基础错误处理功能演示");
    println!("------------------------");
    demonstrate_basic_error_handling(&manager).await?;
    println!();

    // 演示错误恢复功能
    println!("2️⃣ 错误恢复功能演示");
    println!("-------------------");
    demonstrate_error_recovery(&manager).await?;
    println!();

    // 演示错误分类功能
    println!("3️⃣ 错误分类功能演示");
    println!("-------------------");
    demonstrate_error_classification(&manager).await?;
    println!();

    // 演示错误链追踪功能
    println!("4️⃣ 错误链追踪功能演示");
    println!("---------------------");
    demonstrate_error_chain_tracking(&manager).await?;
    println!();

    // 演示高级错误处理功能
    println!("5️⃣ 高级错误处理功能演示");
    println!("-----------------------");
    demonstrate_advanced_error_handling(&manager).await?;
    println!();

    println!("\n🎉 增强的错误处理演示完成！");
    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_basic_error_handling(manager: &EnhancedErrorManager) -> Result<()> {
    // 创建不同类型的错误
    println!("  创建不同类型的错误...");
    
    // 进程错误
    let process_error = ProcessError::StartFailed("Failed to start process".to_string());
    let mut context = HashMap::new();
    context.insert("process_name".to_string(), "test_process".to_string());
    context.insert("pid".to_string(), "1234".to_string());
    
    let error_id1 = manager.record_error(&process_error, "process_manager", context.clone()).await;
    println!("    ✅ 进程错误记录成功，ID: {}", error_id1);
    
    // IPC错误
    let ipc_error = IpcError::ConnectionFailed("IPC connection failed".to_string());
    context.clear();
    context.insert("channel_name".to_string(), "test_channel".to_string());
    context.insert("protocol".to_string(), "tcp".to_string());
    
    let error_id2 = manager.record_error(&ipc_error, "ipc_manager", context.clone()).await;
    println!("    ✅ IPC错误记录成功，ID: {}", error_id2);
    
    // 同步错误
    let sync_error = SyncError::DeadlockDetected("Deadlock detected".to_string());
    context.clear();
    context.insert("mutex_name".to_string(), "test_mutex".to_string());
    context.insert("thread_id".to_string(), "thread_1".to_string());
    
    let error_id3 = manager.record_error(&sync_error, "sync_manager", context.clone()).await;
    println!("    ✅ 同步错误记录成功，ID: {}", error_id3);
    
    // 获取错误历史
    println!("  获取错误历史...");
    let history = manager.get_error_history(Some(10)).await;
    println!("    ✅ 错误历史获取成功，共 {} 条记录", history.len());
    
    for entry in &history {
        println!("      错误ID: {}, 类型: {:?}, 严重程度: {:?}, 消息: {}", 
                entry.id, entry.error_type, entry.severity, entry.message);
    }
    
    // 获取错误统计
    println!("  获取错误统计...");
    let stats = manager.get_error_statistics().await;
    println!("    ✅ 错误统计获取成功");
    println!("      总错误数: {}", stats.total_errors);
    println!("      成功恢复数: {}", stats.successful_recoveries);
    println!("      失败恢复数: {}", stats.failed_recoveries);
    
    for (error_type, count) in &stats.error_type_counts {
        println!("      {:?}: {} 次", error_type, count);
    }
    
    for (severity, count) in &stats.severity_counts {
        println!("      {:?}: {} 次", severity, count);
    }

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_error_recovery(manager: &EnhancedErrorManager) -> Result<()> {
    // 创建可恢复的错误
    println!("  创建可恢复的错误...");
    
    let recoverable_error = ProcessError::StartFailed("Temporary process start failure".to_string());
    let mut context = HashMap::new();
    context.insert("retry_count".to_string(), "0".to_string());
    context.insert("max_retries".to_string(), "3".to_string());
    
    let error_id = manager.record_error(&recoverable_error, "process_manager", context.clone()).await;
    println!("    ✅ 可恢复错误记录成功，ID: {}", error_id);
    
    // 获取错误历史中的错误条目
    let history = manager.get_error_history(Some(1)).await;
    if let Some(error_entry) = history.first() {
        println!("  尝试错误恢复...");
        
        // 尝试恢复
        let recovery_result = manager.attempt_recovery(error_entry).await;
        match recovery_result {
            RecoveryResult::Success { message, duration } => {
                println!("    ✅ 错误恢复成功: {}", message);
                println!("      恢复耗时: {:?}", duration);
            }
            RecoveryResult::Failure { error, duration } => {
                println!("    ❌ 错误恢复失败: {}", error);
                println!("      失败耗时: {:?}", duration);
            }
            RecoveryResult::Retry { delay, reason } => {
                println!("    🔄 错误恢复重试: {}", reason);
                println!("      重试延迟: {:?}", delay);
            }
            RecoveryResult::Escalate { level, reason } => {
                println!("    ⬆️ 错误恢复升级: {}", reason);
                println!("      升级级别: {:?}", level);
            }
        }
    }
    
    // 演示不同类型的恢复策略
    println!("  演示不同类型的恢复策略...");
    
    // 重试策略
    let _retry_strategy = RecoveryStrategy::Retry {
        max_attempts: 3,
        backoff_duration: Duration::from_millis(100),
        backoff_multiplier: 2.0,
    };
    println!("    ✅ 重试策略创建成功");
    
    // 重启策略
    let _restart_strategy = RecoveryStrategy::Restart {
        component: "process_manager".to_string(),
        timeout: Duration::from_secs(30),
    };
    println!("    ✅ 重启策略创建成功");
    
    // 回退策略
    let _fallback_strategy = RecoveryStrategy::Fallback {
        alternative: "backup_process_manager".to_string(),
        timeout: Duration::from_secs(10),
    };
    println!("    ✅ 回退策略创建成功");
    
    // 跳过策略
    let _skip_strategy = RecoveryStrategy::Skip {
        reason: "Non-critical error".to_string(),
    };
    println!("    ✅ 跳过策略创建成功");
    
    // 升级策略
    let _escalate_strategy = RecoveryStrategy::Escalate {
        level: ErrorSeverity::Critical,
        target: "system_administrator".to_string(),
    };
    println!("    ✅ 升级策略创建成功");

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_error_classification(manager: &EnhancedErrorManager) -> Result<()> {
    // 创建不同类型的错误进行分类
    println!("  创建不同类型的错误进行分类...");
    
    // 逐个创建不同类别错误并记录，避免类型不匹配
    let context = HashMap::new();
    let e1 = ProcessError::StartFailed("Process start failed".to_string());
    let id1 = manager.record_error(&e1, "test_source", context.clone()).await;
    println!("    ✅ Process Error 记录成功，ID: {}", id1);

    let e2 = IpcError::ConnectionFailed("IPC connection failed".to_string());
    let id2 = manager.record_error(&e2, "test_source", context.clone()).await;
    println!("    ✅ IPC Error 记录成功，ID: {}", id2);

    let e3 = SyncError::DeadlockDetected("Deadlock detected".to_string());
    let id3 = manager.record_error(&e3, "test_source", context.clone()).await;
    println!("    ✅ Sync Error 记录成功，ID: {}", id3);

    let e4 = ResourceError::InsufficientMemory(1024, 256);
    let id4 = manager.record_error(&e4, "test_source", context.clone()).await;
    println!("    ✅ Resource Error 记录成功，ID: {}", id4);

    let e5 = PlatformError::NotSupported("Unsupported platform".to_string());
    let id5 = manager.record_error(&e5, "test_source", context.clone()).await;
    println!("    ✅ Platform Error 记录成功，ID: {}", id5);

    let e6 = ConfigError::InvalidItem("Invalid configuration value".to_string());
    let id6 = manager.record_error(&e6, "test_source", context).await;
    println!("    ✅ Config Error 记录成功，ID: {}", id6);
    
    // 获取错误历史并分析分类
    println!("  分析错误分类...");
    let history = manager.get_error_history(Some(10)).await;
    
    for entry in &history {
        println!("    错误ID: {}", entry.id);
        println!("      类型: {:?}", entry.error_type);
        println!("      严重程度: {:?}", entry.severity);
        println!("      消息: {}", entry.message);
        println!("      来源: {}", entry.source);
        println!("      时间戳: {:?}", entry.timestamp);
        
        if !entry.context.is_empty() {
            println!("      上下文:");
            for (key, value) in &entry.context {
                println!("        {}: {}", key, value);
            }
        }
        
        if let Some(chain_id) = &entry.chain_id {
            println!("      错误链ID: {}", chain_id);
        }
        
        println!("      恢复尝试次数: {}", entry.recovery_attempts);
        println!("      恢复成功: {}", entry.recovery_success);
        println!();
    }
    
    // 演示错误类型统计
    println!("  错误类型统计:");
    let stats = manager.get_error_statistics().await;
    for (error_type, count) in &stats.error_type_counts {
        println!("    {:?}: {} 次", error_type, count);
    }
    
    // 演示严重程度统计
    println!("  严重程度统计:");
    for (severity, count) in &stats.severity_counts {
        println!("    {:?}: {} 次", severity, count);
    }
    
    // 演示来源统计
    println!("  来源统计:");
    for (source, count) in &stats.source_counts {
        println!("    {}: {} 次", source, count);
    }

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_error_chain_tracking(manager: &EnhancedErrorManager) -> Result<()> {
    // 创建错误链
    println!("  创建错误链...");
    
    // 创建一系列相关的错误
    let mut context = HashMap::new();
    context.insert("chain_id".to_string(), "test_chain_1".to_string());
    
    let error1 = ProcessError::StartFailed("Initial process start failed".to_string());
    let error_id1 = manager.record_error(&error1, "process_manager", context.clone()).await;
    println!("    ✅ 错误1记录成功，ID: {}", error_id1);
    
    // 等待一小段时间
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    let error2 = IpcError::ConnectionFailed("IPC connection failed due to process failure".to_string());
    let error_id2 = manager.record_error(&error2, "ipc_manager", context.clone()).await;
    println!("    ✅ 错误2记录成功，ID: {}", error_id2);
    
    // 等待一小段时间
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    let error3 = SyncError::DeadlockDetected("Deadlock detected due to IPC failure".to_string());
    let error_id3 = manager.record_error(&error3, "sync_manager", context.clone()).await;
    println!("    ✅ 错误3记录成功，ID: {}", error_id3);
    
    // 分析错误链
    println!("  分析错误链...");
    let history = manager.get_error_history(Some(10)).await;
    
    let mut chain_errors: HashMap<String, Vec<&EnhancedErrorEntry>> = HashMap::new();
    for entry in &history {
        if let Some(chain_id) = &entry.chain_id {
            chain_errors.entry(chain_id.clone()).or_default().push(entry);
        }
    }
    
    for (chain_id, errors) in chain_errors {
        println!("    错误链ID: {}", chain_id);
        println!("      链中错误数量: {}", errors.len());
        
        for (i, error) in errors.iter().enumerate() {
            println!("        错误{}: ID={}, 类型={:?}, 严重程度={:?}", 
                    i + 1, error.id, error.error_type, error.severity);
            println!("          消息: {}", error.message);
            println!("          时间戳: {:?}", error.timestamp);
        }
    }
    
    // 演示错误链的时序分析
    println!("  错误链时序分析...");
    let mut sorted_history = history.clone();
    sorted_history.sort_by(|a, b| a.timestamp.cmp(&b.timestamp));
    
    for (i, entry) in sorted_history.iter().enumerate() {
        println!("    时序{}: {} - {:?} - {}", 
                i + 1, entry.id, entry.error_type, entry.message);
    }

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_advanced_error_handling(manager: &EnhancedErrorManager) -> Result<()> {
    // 演示高级错误处理功能
    println!("  演示高级错误处理功能...");
    
    // 创建复杂的错误场景
    println!("    创建复杂的错误场景...");
    
    // 模拟系统级错误
    let system_error = ProcessError::StartFailed("System resource exhausted".to_string());
    let mut context = HashMap::new();
    context.insert("system_load".to_string(), "95%".to_string());
    context.insert("memory_usage".to_string(), "98%".to_string());
    context.insert("cpu_usage".to_string(), "90%".to_string());
    context.insert("disk_usage".to_string(), "85%".to_string());
    
    let error_id = manager.record_error(&system_error, "system_monitor", context.clone()).await;
    println!("      ✅ 系统级错误记录成功，ID: {}", error_id);
    
    // 模拟网络错误
    let network_error = IpcError::ConnectionFailed("Network timeout".to_string());
    context.clear();
    context.insert("network_latency".to_string(), "5000ms".to_string());
    context.insert("packet_loss".to_string(), "5%".to_string());
    context.insert("connection_attempts".to_string(), "3".to_string());
    
    let error_id2 = manager.record_error(&network_error, "network_manager", context.clone()).await;
    println!("      ✅ 网络错误记录成功，ID: {}", error_id2);
    
    // 模拟并发错误
    let concurrency_error = SyncError::DeadlockDetected("High contention detected".to_string());
    context.clear();
    context.insert("contention_rate".to_string(), "85%".to_string());
    context.insert("waiting_threads".to_string(), "10".to_string());
    context.insert("lock_hold_time".to_string(), "5s".to_string());
    
    let error_id3 = manager.record_error(&concurrency_error, "concurrency_manager", context.clone()).await;
    println!("      ✅ 并发错误记录成功，ID: {}", error_id3);
    
    // 获取详细的错误统计
    println!("    获取详细的错误统计...");
    let stats = manager.get_error_statistics().await;
    
    println!("      总错误数: {}", stats.total_errors);
    println!("      成功恢复数: {}", stats.successful_recoveries);
    println!("      失败恢复数: {}", stats.failed_recoveries);
    
    // 错误类型分布
    println!("      错误类型分布:");
    for (error_type, count) in &stats.error_type_counts {
        let percentage = (*count as f64 / stats.total_errors as f64) * 100.0;
        println!("        {:?}: {} 次 ({:.1}%)", error_type, count, percentage);
    }
    
    // 严重程度分布
    println!("      严重程度分布:");
    for (severity, count) in &stats.severity_counts {
        let percentage = (*count as f64 / stats.total_errors as f64) * 100.0;
        println!("        {:?}: {} 次 ({:.1}%)", severity, count, percentage);
    }
    
    // 来源分布
    println!("      来源分布:");
    for (source, count) in &stats.source_counts {
        let percentage = (*count as f64 / stats.total_errors as f64) * 100.0;
        println!("        {}: {} 次 ({:.1}%)", source, count, percentage);
    }
    
    // 演示错误趋势分析
    println!("    错误趋势分析...");
    let history = manager.get_error_history(None).await;
    
    if history.len() > 1 {
        let mut error_times: Vec<std::time::SystemTime> = history.iter()
            .map(|entry| entry.timestamp)
            .collect();
        error_times.sort();
        
        let first_error = error_times.first().unwrap();
        let last_error = error_times.last().unwrap();
        let duration = last_error.duration_since(*first_error).unwrap();
        
        println!("      错误时间范围: {:?}", duration);
        println!("      错误频率: {:.2} 错误/秒", 
                history.len() as f64 / duration.as_secs_f64());
        
        // 分析错误间隔
        let mut intervals = Vec::new();
        for i in 1..error_times.len() {
            let interval = error_times[i].duration_since(error_times[i-1]).unwrap();
            intervals.push(interval);
        }
        
        if !intervals.is_empty() {
            let avg_interval = intervals.iter().sum::<Duration>() / intervals.len() as u32;
            println!("      平均错误间隔: {:?}", avg_interval);
        }
    }
    
    // 演示错误恢复效果分析
    println!("    错误恢复效果分析...");
    let recovery_success_rate = if stats.total_errors > 0 {
        (stats.successful_recoveries as f64 / stats.total_errors as f64) * 100.0
    } else {
        0.0
    };
    
    println!("      恢复成功率: {:.1}%", recovery_success_rate);
    
    if recovery_success_rate > 80.0 {
        println!("      ✅ 错误恢复效果优秀");
    } else if recovery_success_rate > 60.0 {
        println!("      🟡 错误恢复效果良好");
    } else if recovery_success_rate > 40.0 {
        println!("      🟠 错误恢复效果一般");
    } else {
        println!("      ❌ 错误恢复效果需要改进");
    }

    Ok(())
}

#[cfg(not(feature = "async"))]
fn main() {
    println!("❌ 异步功能未启用");
    println!("请使用 --features async 重新编译以启用异步功能");
}
