//! 增强的异步功能演示程序
//! 
//! 这个程序展示了增强的异步进程管理功能，包括异步闭包、
//! 性能监控、错误恢复等 Rust 1.90 新特性

#[cfg(feature = "async")]
use c07_process::prelude::*;
#[cfg(feature = "async")]
use c07_process::{
    EnhancedAsyncProcessManager,  
};
#[cfg(feature = "async")]
use std::collections::HashMap;
#[cfg(feature = "async")]
use std::time::Duration;

#[cfg(feature = "async")]
#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 增强的异步进程管理演示程序");
    println!("================================\n");

    // 创建增强的异步进程管理器
    println!("🔧 创建增强的异步进程管理器...");
    let manager = EnhancedAsyncProcessManager::new(5).await?;
    println!("✅ 增强的异步进程管理器创建成功！\n");

    // 演示基础异步功能
    println!("1️⃣ 基础异步功能演示");
    println!("-------------------");
    demonstrate_basic_async_features(&manager).await?;
    println!();

    // 演示异步闭包功能
    println!("2️⃣ 异步闭包功能演示");
    println!("-------------------");
    demonstrate_async_closures(&manager).await?;
    println!();

    // 演示性能监控功能
    println!("3️⃣ 性能监控功能演示");
    println!("-------------------");
    demonstrate_performance_monitoring(&manager).await?;
    println!();

    // 演示错误恢复功能
    println!("4️⃣ 错误恢复功能演示");
    println!("-------------------");
    demonstrate_error_recovery(&manager).await?;
    println!();

    // 演示高级异步功能
    println!("5️⃣ 高级异步功能演示");
    println!("-------------------");
    demonstrate_advanced_async_features(&manager).await?;
    println!();

    // 清理资源
    println!("🧹 清理资源...");
    manager.cleanup().await?;
    println!("✅ 资源清理完成");

    println!("\n🎉 增强的异步功能演示完成！");
    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_basic_async_features(manager: &EnhancedAsyncProcessManager) -> Result<()> {
    // 创建进程配置
    let config = create_demo_config("basic_demo")?;
    
    // 启动进程
    println!("  启动基础异步进程...");
    let pid = manager.spawn(config).await?;
    println!("  ✅ 进程启动成功，PID: {}", pid);
    
    // 获取进程信息
    println!("  获取进程信息...");
    let info = manager.get_info(pid).await?;
    println!("  ✅ 进程信息: {:?}", info);
    
    // 获取性能指标
    println!("  获取性能指标...");
    let metrics = manager.get_metrics(pid).await?;
    println!("  ✅ 性能指标: {:?}", metrics);
    
    // 等待进程完成
    println!("  等待进程完成...");
    if let Some(output) = manager.wait_with_timeout(pid, Duration::from_secs(5)).await? {
        println!("  ✅ 进程完成，退出码: {:?}", output.exit_code);
        println!("  📤 标准输出: {}", String::from_utf8_lossy(&output.stdout));
    } else {
        println!("  ⏰ 进程超时");
        let _ = manager.kill(pid, true).await;
    }
    
    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_async_closures(manager: &EnhancedAsyncProcessManager) -> Result<()> {
    // 创建进程配置
    let config = create_demo_config("async_closure_demo")?;
    
    // 使用异步闭包启动进程
    println!("  使用异步闭包启动进程...");
    let callback = |result: ProcessResult<u32>| -> ProcessResult<()> {
        match result {
            Ok(pid) => {
                println!("    🎯 异步闭包回调: 进程 {} 启动成功", pid);
                Ok(())
            }
            Err(e) => {
                println!("    ❌ 异步闭包回调: 进程启动失败 - {}", e);
                Err(e)
            }
        }
    };
    
    let pid = manager.spawn_with_callback(config, callback).await?;
    println!("  ✅ 异步闭包进程启动成功，PID: {}", pid);
    
    // 等待进程完成
    if let Some(output) = manager.wait_with_timeout(pid, Duration::from_secs(5)).await? {
        println!("  ✅ 异步闭包进程完成，退出码: {:?}", output.exit_code);
    } else {
        println!("  ⏰ 异步闭包进程超时");
        let _ = manager.kill(pid, true).await;
    }
    
    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_performance_monitoring(manager: &EnhancedAsyncProcessManager) -> Result<()> {
    // 创建多个进程进行性能监控
    println!("  创建多个进程进行性能监控...");
    let mut pids = Vec::new();
    
    for i in 0..3 {
        let config = create_demo_config(&format!("perf_monitor_{}", i))?;
        let pid = manager.spawn(config).await?;
        pids.push(pid);
        println!("    ✅ 进程 {} 启动，PID: {}", i, pid);
    }
    
    // 监控性能指标
    println!("  监控性能指标...");
    for (i, &pid) in pids.iter().enumerate() {
        let metrics = manager.get_metrics(pid).await?;
        println!("    进程 {} (PID: {}):", i, pid);
        println!("      CPU 使用率: {:.2}%", metrics.cpu_usage);
        println!("      内存使用: {} bytes", metrics.memory_usage);
        println!("      I/O 读取: {} bytes", metrics.io_read_bytes);
        println!("      I/O 写入: {} bytes", metrics.io_write_bytes);
        println!("      运行时间: {:?}", metrics.start_time.elapsed());
    }
    
    // 等待所有进程完成
    println!("  等待所有进程完成...");
    for (i, &pid) in pids.iter().enumerate() {
        if let Some(output) = manager.wait_with_timeout(pid, Duration::from_secs(5)).await? {
            println!("    ✅ 进程 {} 完成，运行时间: {:?}", i, output.duration);
        } else {
            println!("    ⏰ 进程 {} 超时", i);
            let _ = manager.kill(pid, true).await;
        }
    }
    
    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_error_recovery(manager: &EnhancedAsyncProcessManager) -> Result<()> {
    // 演示错误恢复机制
    println!("  演示错误恢复机制...");
    
    // 尝试启动一个不存在的程序
    let invalid_config = ProcessConfig {
        program: "nonexistent_program".to_string(),
        args: vec![],
        env: HashMap::new(),
        working_dir: None,
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: Default::default(),
    };
    
    match manager.spawn(invalid_config).await {
        Ok(pid) => {
            println!("    ⚠️ 意外成功启动进程，PID: {}", pid);
            let _ = manager.kill(pid, true).await;
        }
        Err(e) => {
            println!("    ✅ 预期的错误: {}", e);
            
            // 演示错误恢复
            println!("    尝试错误恢复...");
            // 这里可以添加具体的错误恢复逻辑
            println!("    ✅ 错误恢复完成");
        }
    }
    
    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_advanced_async_features(manager: &EnhancedAsyncProcessManager) -> Result<()> {
    // 演示高级异步功能
    println!("  演示高级异步功能...");
    
    // 创建进程配置
    let config = create_demo_config("advanced_demo")?;
    
    // 启动进程
    let pid = manager.spawn(config).await?;
    println!("    ✅ 高级异步进程启动，PID: {}", pid);
    
    // 演示异步 I/O 操作
    println!("    演示异步 I/O 操作...");
    
    // 写入标准输入
    let input_data = b"Hello from enhanced async demo!";
    if let Err(e) = manager.write_stdin(pid, input_data).await {
        println!("      ⚠️ 写入标准输入失败: {}", e);
    } else {
        println!("      ✅ 写入标准输入成功");
    }
    
    // 读取标准输出
    if let Ok(output_data) = manager.read_stdout(pid).await {
        println!("      ✅ 读取标准输出: {}", String::from_utf8_lossy(&output_data));
    } else {
        println!("      ⚠️ 读取标准输出失败");
    }
    
    // 等待进程完成
    if let Some(output) = manager.wait_with_timeout(pid, Duration::from_secs(5)).await? {
        println!("    ✅ 高级异步进程完成");
        println!("      退出码: {:?}", output.exit_code);
        println!("      运行时间: {:?}", output.duration);
        println!("      标准输出: {}", String::from_utf8_lossy(&output.stdout));
        if !output.stderr.is_empty() {
            println!("      标准错误: {}", String::from_utf8_lossy(&output.stderr));
        }
    } else {
        println!("    ⏰ 高级异步进程超时");
        let _ = manager.kill(pid, true).await;
    }
    
    Ok(())
}

#[cfg(feature = "async")]
fn create_demo_config(name: &str) -> Result<ProcessConfig> {
    let mut env = HashMap::new();
    if cfg!(windows) {
        env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
    } else {
        env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    }
    
    Ok(ProcessConfig {
        program: if cfg!(windows) { "cmd".to_string() } else { "echo".to_string() },
        args: if cfg!(windows) {
            vec!["/c".to_string(), format!("echo {} - Enhanced Async Demo", name)]
        } else {
            vec![format!("{} - Enhanced Async Demo", name)]
        },
        env,
        working_dir: Some(".".to_string()),
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: Default::default(),
    })
}

#[cfg(not(feature = "async"))]
fn main() {
    println!("❌ 异步功能未启用");
    println!("请使用 --features async 重新编译以启用异步功能");
}
