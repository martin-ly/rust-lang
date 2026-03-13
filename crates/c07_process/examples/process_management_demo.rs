//! 进程管理演示程序
//!
//! 本示例展示如何使用 C07 进程管理模块进行：
//! - 进程创建和管理
//! - 进程配置
//! - 进程状态监控
//! - 进程组管理
use c07_process::prelude::*;
use c07_process::{ProcessGroupManager, SystemResources};
use std::collections::HashMap;

fn main() -> Result<()> {
    println!("🚀 C07 进程管理演示程序");
    println!("========================\n");

    // 1. 创建进程管理器
    println!("📦 创建进程管理器...");
    let _pm = ProcessManager::new();
    println!("✅ 进程管理器创建成功\n");

    // 2. 创建进程配置
    println!("⚙️  创建进程配置...");
    let mut env = HashMap::new();
    env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    env.insert("RUST_LOG".to_string(), "info".to_string());

    let config = ProcessConfig {
        program: "echo".to_string(),
        args: vec!["Hello, World!".to_string()],
        env,
        working_dir: Some("/tmp".to_string()),
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: ResourceLimits::default(),
    };
    println!("✅ 进程配置创建成功:");
    println!("  程序: {}", config.program);
    println!("  参数: {:?}", config.args);
    println!("  工作目录: {:?}\n", config.working_dir);

    // 3. 使用 ProcessBuilder 创建进程
    println!("🔨 使用 ProcessBuilder 创建进程...");
    let _builder = ProcessBuilder::new("echo")
        .args(vec!["ProcessBuilder", "Demo"])
        .env("DEMO_VAR", "demo_value");

    println!("✅ ProcessBuilder 配置完成:");
    println!("  程序: echo");
    println!("  参数数量: 2\n");

    // 4. 进程组管理示例
    println!("👥 进程组管理示例...");
    let _pgm = ProcessGroupManager::new();

    let _group_config = ProcessConfig {
        program: "echo".to_string(),
        args: vec!["Group".to_string(), "Demo".to_string()],
        env: HashMap::new(),
        working_dir: None,
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: ResourceLimits::default(),
    };

    println!("✅ 进程组管理器创建成功");
    println!("  进程组配置已准备\n");

    // 5. 资源限制示例
    println!("📊 资源限制示例...");
    let limits = ResourceLimits {
        max_memory: Some(1024 * 1024 * 100), // 100MB
        max_cpu_time: Some(60), // 60 seconds
        max_file_size: Some(1024 * 1024 * 10), // 10MB
        max_file_descriptors: Some(100),
    };
    println!("✅ 资源限制配置:");
    println!("  最大内存: {:?} bytes", limits.max_memory);
    println!("  最大CPU时间: {:?} seconds", limits.max_cpu_time);
    println!("  最大文件大小: {:?} bytes", limits.max_file_size);
    println!("  最大文件描述符数: {:?}\n", limits.max_file_descriptors);

    // 6. 进程状态示例
    println!("📈 进程状态示例...");
    let statuses = vec![
        ProcessStatus::Running,
        ProcessStatus::Stopped,
        ProcessStatus::Zombie,
        ProcessStatus::Unknown,
    ];

    for status in statuses {
        println!("  状态: {:?}", status);
    }
    println!();

    // 7. 系统资源示例
    println!("💻 系统资源示例...");
    let resources = SystemResources {
        total_memory: 8 * 1024 * 1024 * 1024, // 8GB
        available_memory: 4 * 1024 * 1024 * 1024, // 4GB
        cpu_cores: 4,
        cpu_usage: 0.5,
        total_disk: 500 * 1024 * 1024 * 1024, // 500GB
        available_disk: 250 * 1024 * 1024 * 1024, // 250GB
        timestamp: std::time::SystemTime::now(),
    };
    println!("✅ 系统资源信息:");
    println!("  总内存: {} bytes", resources.total_memory);
    println!("  可用内存: {} bytes", resources.available_memory);
    println!("  CPU核心数: {}", resources.cpu_cores);
    println!("  CPU使用率: {:.1}%\n", resources.cpu_usage * 100.0);

    println!("✅ 进程管理演示完成！");
    println!("\n💡 提示:");
    println!("  - 在实际使用中，需要确保程序存在");
    println!("  - 可以使用 ProcessBuilder 进行链式配置");
    println!("  - 进程组管理可以同时管理多个进程");
    println!("  - 资源限制可以防止进程消耗过多资源");

    Ok(())
}
