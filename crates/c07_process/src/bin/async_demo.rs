#[cfg(feature = "async")]
use c07_process::prelude::*;
#[cfg(feature = "async")]
use c07_process::{AsyncProcessManager, AsyncProcessPool, AsyncTaskScheduler, AsyncTask};
#[cfg(feature = "async")]
use std::collections::HashMap;
#[cfg(feature = "async")]
use std::time::Duration;

#[cfg(feature = "async")]
#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 异步进程管理演示程序");
    println!("======================\n");
    
    // 创建异步进程管理器
    println!("🔧 创建异步进程管理器...");
    let async_manager = AsyncProcessManager::new().await;
    println!("✅ 异步进程管理器创建成功！\n");
    
    // 创建异步进程池
    println!("🔧 创建异步进程池...");
    let async_pool = AsyncProcessPool::new(3).await?;
    println!("✅ 异步进程池创建成功！\n");
    
    // 创建异步任务调度器
    println!("🔧 创建异步任务调度器...");
    let scheduler = AsyncTaskScheduler::new(2);
    scheduler.start().await;
    println!("✅ 异步任务调度器启动成功！\n");
    
    // 演示异步进程管理
    println!("🔄 演示异步进程管理...");
    
    // 创建进程配置
    let mut env = HashMap::new();
    env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    
    let config = ProcessConfig {
        program: "echo".to_string(),
        args: vec!["Hello from async process".to_string()],
        env,
        working_dir: Some("/tmp".to_string()),
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: ResourceLimits::default(),
    };
    
    // 异步启动进程
    println!("  异步启动进程...");
    let pid = async_manager.spawn(config).await?;
    println!("  ✅ 进程启动成功，PID: {}", pid);
    
    // 获取进程信息
    println!("  获取进程信息...");
    let info = async_manager.get_info(pid).await?;
    println!("  ✅ 进程信息: {:?}", info);
    
    // 列出所有进程
    println!("  列出所有进程...");
    let all_processes = async_manager.list_all().await;
    println!("  ✅ 总进程数: {}", all_processes.len());
    
    // 演示异步进程池
    println!("\n🔄 演示异步进程池...");
    
    // 获取进程
    println!("  从进程池获取进程...");
    let pool_pid1 = async_pool.get_process().await?;
    println!("  ✅ 获取进程成功，PID: {}", pool_pid1);
    
    let pool_pid2 = async_pool.get_process().await?;
    println!("  ✅ 获取进程成功，PID: {}", pool_pid2);
    
    // 显示进程池状态
    let pool_stats = async_pool.get_stats().await;
    println!("  📊 进程池状态:");
    println!("    总进程数: {}", pool_stats.total_processes);
    println!("    可用进程数: {}", pool_stats.available_processes);
    println!("    忙碌进程数: {}", pool_stats.busy_processes);
    
    // 释放进程
    println!("  释放进程回池...");
    async_pool.release_process(pool_pid1).await?;
    println!("  ✅ 进程 {} 释放成功", pool_pid1);
    
    async_pool.release_process(pool_pid2).await?;
    println!("  ✅ 进程 {} 释放成功", pool_pid2);
    
    // 演示异步任务调度
    println!("\n🔄 演示异步任务调度...");
    
    // 创建任务
    let task1 = AsyncTask {
        id: 1,
        name: "Task 1".to_string(),
        priority: 5,
        payload: "Hello Task 1".as_bytes().to_vec(),
    };
    
    let task2 = AsyncTask {
        id: 2,
        name: "Task 2".to_string(),
        priority: 3,
        payload: "Hello Task 2".as_bytes().to_vec(),
    };
    
    let task3 = AsyncTask {
        id: 3,
        name: "Task 3".to_string(),
        priority: 7,
        payload: "Hello Task 3".as_bytes().to_vec(),
    };
    
    // 添加任务到调度器
    println!("  添加任务到调度器...");
    scheduler.add_task(task1).await;
    scheduler.add_task(task2).await;
    scheduler.add_task(task3).await;
    println!("  ✅ 3个任务添加成功");
    
    // 等待一段时间让任务处理
    println!("  等待任务处理...");
    tokio::time::sleep(Duration::from_millis(200)).await;
    
    // 终止进程
    println!("\n🔄 终止进程...");
    async_manager.kill(pid).await?;
    println!("  ✅ 进程 {} 终止成功", pid);
    
    // 最终状态
    println!("\n📊 最终状态:");
    let final_processes = async_manager.list_all().await;
    println!("  总进程数: {}", final_processes.len());
    
    let final_pool_stats = async_pool.get_stats().await;
    println!("  进程池状态:");
    println!("    总进程数: {}", final_pool_stats.total_processes);
    println!("    可用进程数: {}", final_pool_stats.available_processes);
    println!("    忙碌进程数: {}", final_pool_stats.busy_processes);
    
    println!("\n🎉 异步演示完成！");
    Ok(())
}

#[cfg(not(feature = "async"))]
fn main() {
    println!("❌ 异步功能未启用");
    println!("请使用 --features async 重新编译以启用异步功能");
}
