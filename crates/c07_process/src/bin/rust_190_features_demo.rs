//! Rust 1.90 Edition 2024 新特性演示程序
//! 
//! 这个程序展示了如何在 c07_process 项目中使用最新的 Rust 1.90 特性

use c07_process::prelude::*;
use c07_process::prelude::{Rust190Features, AsyncTaskDemo, TaskStatus, ProcessConfig, ProcessManager, IpcManager, IpcConfig, Message, SyncManager, SyncConfig};
use c07_process::error::ProcessError;
use std::collections::HashMap;
// 移除未使用的导入

#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 Rust 1.90 Edition 2024 新特性演示");
    println!("=====================================\n");

    // 创建特性演示实例
    let features = Rust190Features::new();

    // 1. 演示异步闭包
    println!("1️⃣ 异步闭包演示");
    println!("----------------");
    if let Err(e) = features.demonstrate_async_closures().await {
        println!("❌ 异步闭包演示失败: {}", e);
    }
    println!();

    // 2. 演示改进的模式匹配
    println!("2️⃣ 改进的模式匹配演示");
    println!("----------------------");
    features.demonstrate_improved_pattern_matching(Ok(1234));
    features.demonstrate_improved_pattern_matching(Err(ProcessError::NotFound(5678)));
    features.demonstrate_improved_pattern_matching(Err(ProcessError::PermissionDenied("测试权限错误".to_string())));
    println!();

    // 3. 演示改进的迭代器
    println!("3️⃣ 改进的迭代器演示");
    println!("-------------------");
    let configs = vec![
        ProcessConfig {
            program: "echo".to_string(),
            args: vec!["Hello".to_string()],
            env: HashMap::new(),
            working_dir: None,
            user_id: None,
            group_id: None,
            priority: None,
            resource_limits: Default::default(),
        },
        ProcessConfig {
            program: "ls".to_string(),
            args: vec!["-la".to_string()],
            env: HashMap::new(),
            working_dir: None,
            user_id: None,
            group_id: None,
            priority: None,
            resource_limits: Default::default(),
        },
    ];
    features.demonstrate_improved_iterators(configs);
    println!();

    // 4. 演示改进的错误处理
    println!("4️⃣ 改进的错误处理演示");
    println!("---------------------");
    if let Err(e) = features.demonstrate_improved_error_handling() {
        println!("❌ 错误处理演示失败: {}", e);
    }
    println!();

    // 5. 演示改进的类型推断
    println!("5️⃣ 改进的类型推断演示");
    println!("---------------------");
    features.demonstrate_improved_type_inference();
    println!();

    // 6. 演示改进的宏系统
    println!("6️⃣ 改进的宏系统演示");
    println!("-------------------");
    features.demonstrate_improved_macros();
    println!();

    // 7. 演示标准库新特性
    println!("7️⃣ 标准库新特性演示");
    println!("-------------------");
    features.demonstrate_std_library_features();
    println!();

    // 8. 演示改进的并发特性
    println!("8️⃣ 改进的并发特性演示");
    println!("---------------------");
    if let Err(e) = features.demonstrate_improved_concurrency().await {
        println!("❌ 并发特性演示失败: {}", e);
    }
    println!();

    // 9. 演示异步任务
    println!("9️⃣ 异步任务演示");
    println!("---------------");
    let tasks = vec![
        AsyncTaskDemo::new(1, "任务 1".to_string()),
        AsyncTaskDemo::new(2, "任务 2".to_string()),
        AsyncTaskDemo::new(3, "任务 3".to_string()),
    ];

    // 并发执行任务
    let mut handles = Vec::new();
    for mut task in tasks {
        let handle = tokio::spawn(async move {
            if let Err(e) = task.execute().await {
                println!("❌ 任务执行失败: {}", e);
            }
            task
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    let mut completed_tasks = Vec::new();
    for handle in handles {
        if let Ok(task) = handle.await {
            completed_tasks.push(task);
        }
    }

    // 显示任务状态
    for task in completed_tasks {
        match task.get_status() {
            TaskStatus::Completed => println!("✅ 任务已完成"),
            TaskStatus::Failed(msg) => println!("❌ 任务失败: {}", msg),
            _ => println!("⚠️ 任务状态未知"),
        }
    }
    println!();

    // 10. 演示与现有功能的集成
    println!("🔟 与现有功能集成演示");
    println!("---------------------");
    demonstrate_integration_with_existing_features().await?;
    println!();

    println!("🎉 Rust 1.90 新特性演示完成！");
    println!("=============================");
    
    Ok(())
}

/// 演示新特性与现有功能的集成
async fn demonstrate_integration_with_existing_features() -> Result<()> {
    // 创建进程管理器
    let mut pm = ProcessManager::new();
    
    // 使用新特性创建进程配置
    let config = create_config_with_new_features()?;
    
    // 启动进程
    let pid = pm.spawn(config)?;
    println!("✅ 使用新特性启动进程，PID: {}", pid);
    
    // 获取进程信息
    if let Ok(info) = pm.get_process_info(pid) {
        println!("📋 进程信息: {:?}", info);
    }
    
    // 等待进程完成
    if let Ok(output) = pm.get_output(pid) {
        println!("📤 进程输出: {:?}", output);
    }
    
    // 创建IPC管理器
    let mut ipc = IpcManager::new(IpcConfig::default());
    
    // 使用新特性创建IPC通道
    ipc.create_named_pipe("rust_190_demo_pipe")?;
    println!("✅ 创建IPC通道: rust_190_demo_pipe");
    
    // 发送消息
    let message = Message::new(1, "rust_190_demo", "Hello from Rust 1.90!".as_bytes().to_vec(), 1234);
    ipc.send_message("rust_190_demo_pipe", &message)?;
    println!("📤 发送消息到 IPC 通道");
    
    // 接收消息
    if let Ok(received) = ipc.receive_message("rust_190_demo_pipe") {
        println!("📥 从 IPC 通道接收消息: {:?}", received);
    }
    
    // 创建同步管理器
    let mut sync = SyncManager::new(SyncConfig::default());
    
    // 使用新特性创建同步原语
    let mutex = sync.create_mutex("rust_190_demo_mutex")?;
    println!("✅ 创建互斥锁: rust_190_demo_mutex");
    
    // 测试锁
    if let Ok(guard) = mutex.lock() {
        println!("🔒 获取互斥锁成功");
        drop(guard);
        println!("🔓 释放互斥锁");
    }
    
    // 清理资源
    ipc.cleanup()?;
    println!("🧹 清理完成");
    
    Ok(())
}

/// 使用新特性创建进程配置
fn create_config_with_new_features() -> Result<ProcessConfig> {
    // 使用改进的迭代器和模式匹配
    let args = vec!["Hello", "Rust", "1.90"]
        .into_iter()
        .map(|s| s.to_string())
        .collect();
    
    let mut env = HashMap::new();
    env.insert("RUST_VERSION".to_string(), "1.90".to_string());
    env.insert("EDITION".to_string(), "2024".to_string());
    
    Ok(ProcessConfig {
        program: if cfg!(windows) { "cmd".to_string() } else { "echo".to_string() },
        args: if cfg!(windows) {
            vec!["/c".to_string(), "echo Hello from Rust 1.90!".to_string()]
        } else {
            args
        },
        env,
        working_dir: Some(".".to_string()),
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: Default::default(),
    })
}
