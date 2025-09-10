use c07_process::prelude::*;
use std::collections::HashMap;
use std::time::Duration;

fn main() -> Result<()> {
    println!("🚀 进程池管理演示程序");
    println!("====================\n");
    
    // 创建基础进程配置（跨平台）
    let mut env = HashMap::new();
    if cfg!(windows) {
        env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
    } else {
        env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    }

    let base_config = if cfg!(windows) {
        ProcessConfig {
            program: "cmd".to_string(),
            args: vec!["/c".to_string(), "echo Hello from process pool".to_string()],
            env,
            working_dir: Some(".".to_string()),
            user_id: None,
            group_id: None,
            priority: None,
            resource_limits: ResourceLimits::default(),
        }
    } else {
        ProcessConfig {
            program: "echo".to_string(),
            args: vec!["Hello from process pool".to_string()],
            env,
            working_dir: Some("/tmp".to_string()),
            user_id: None,
            group_id: None,
            priority: None,
            resource_limits: ResourceLimits::default(),
        }
    };
    
    // 创建进程池配置
    let pool_config = ProcessPoolConfig {
        min_processes: 2,
        max_processes: 5,
        initial_processes: 3,
        idle_timeout: Duration::from_secs(60),
        health_check_interval: Duration::from_secs(30),
        load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
        auto_scaling: AutoScalingConfig::default(),
    };
    
    println!("📋 进程池配置:");
    println!("  最小进程数: {}", pool_config.min_processes);
    println!("  最大进程数: {}", pool_config.max_processes);
    println!("  初始进程数: {}", pool_config.initial_processes);
    println!("  空闲超时: {:?}", pool_config.idle_timeout);
    println!("  健康检查间隔: {:?}", pool_config.health_check_interval);
    println!();
    
    // 创建进程池
    println!("🔧 创建进程池...");
    let pool = ProcessPool::new(pool_config, base_config)?;
    println!("✅ 进程池创建成功！\n");
    
    // 显示初始状态
    let stats = pool.get_stats();
    println!("📊 初始状态:");
    println!("  总进程数: {}", stats.total_processes);
    println!("  可用进程数: {}", stats.available_processes);
    println!("  忙碌进程数: {}", stats.busy_processes);
    println!("  平均CPU使用率: {:.2}%", stats.average_cpu_usage);
    println!("  平均内存使用率: {:.2}%", stats.average_memory_usage);
    println!();
    
    // 模拟使用进程池
    println!("🔄 模拟使用进程池...");
    
    // 获取进程1
    println!("  获取进程1...");
    let pid1 = pool.get_process()?;
    println!("  ✅ 获取进程成功，PID: {}", pid1);
    
    // 获取进程2
    println!("  获取进程2...");
    let pid2 = pool.get_process()?;
    println!("  ✅ 获取进程成功，PID: {}", pid2);
    
    // 获取进程3
    println!("  获取进程3...");
    let pid3 = pool.get_process()?;
    println!("  ✅ 获取进程成功，PID: {}", pid3);
    
    // 显示使用后状态
    let stats = pool.get_stats();
    println!("\n📊 使用后状态:");
    println!("  总进程数: {}", stats.total_processes);
    println!("  可用进程数: {}", stats.available_processes);
    println!("  忙碌进程数: {}", stats.busy_processes);
    println!();
    
    // 释放进程
    println!("🔄 释放进程...");
    println!("  释放进程 {}...", pid1);
    pool.release_process(pid1)?;
    println!("  ✅ 进程 {} 释放成功", pid1);
    
    println!("  释放进程 {}...", pid2);
    pool.release_process(pid2)?;
    println!("  ✅ 进程 {} 释放成功", pid2);
    
    println!("  释放进程 {}...", pid3);
    pool.release_process(pid3)?;
    println!("  ✅ 进程 {} 释放成功", pid3);
    
    // 显示最终状态
    let stats = pool.get_stats();
    println!("\n📊 最终状态:");
    println!("  总进程数: {}", stats.total_processes);
    println!("  可用进程数: {}", stats.available_processes);
    println!("  忙碌进程数: {}", stats.busy_processes);
    println!();
    
    // 演示自动扩展
    println!("🚀 演示自动扩展...");
    println!("  获取多个进程以触发扩展...");
    
    let mut pids = Vec::new();
    for i in 0..4 {
        let pid = pool.get_process()?;
        pids.push(pid);
        println!("  ✅ 获取进程 {}，PID: {}", i + 1, pid);
    }
    
    let stats = pool.get_stats();
    println!("\n📊 扩展后状态:");
    println!("  总进程数: {}", stats.total_processes);
    println!("  可用进程数: {}", stats.available_processes);
    println!("  忙碌进程数: {}", stats.busy_processes);
    println!();
    
    // 释放所有进程
    println!("🔄 释放所有进程...");
    for pid in &pids {
        pool.release_process(*pid)?;
        println!("  ✅ 进程 {} 释放成功", pid);
    }
    
    // 清理不健康的进程
    println!("\n🧹 清理不健康的进程...");
    let removed_count = pool.cleanup_unhealthy_processes()?;
    println!("  ✅ 清理了 {} 个不健康的进程", removed_count);
    
    // 显示最终统计
    let final_stats = pool.get_stats();
    println!("\n📊 最终统计:");
    println!("  总进程数: {}", final_stats.total_processes);
    println!("  可用进程数: {}", final_stats.available_processes);
    println!("  忙碌进程数: {}", final_stats.busy_processes);
    println!("  平均CPU使用率: {:.2}%", final_stats.average_cpu_usage);
    println!("  平均内存使用率: {:.2}%", final_stats.average_memory_usage);
    
    println!("\n🎉 进程池演示完成！");
    Ok(())
}
