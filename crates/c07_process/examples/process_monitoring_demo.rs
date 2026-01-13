//! 进程监控示例
//!
//! 本示例展示如何使用C07进程管理模块进行进程监控：
//! - 进程状态监控
//! - 资源使用监控
//! - 进程信息查询
//!
//! 运行方式:
//! ```bash
//! cargo run --example process_monitoring_demo
//! ```

use c07_process::prelude::*;
use c07_process::SystemResources;

fn main() -> Result<()> {
    println!("🚀 进程监控示例\n");
    println!("{}", "=".repeat(60));

    // 1. 创建进程管理器
    println!("\n📊 创建进程管理器:");
    println!("{}", "-".repeat(60));
    let _pm = ProcessManager::new();
    println!("✅ ProcessManager创建成功");

    // 2. 进程状态监控
    println!("\n📊 进程状态说明:");
    println!("{}", "-".repeat(60));
    let statuses = vec![
        ProcessStatus::Running,
        ProcessStatus::Sleeping,
        ProcessStatus::Stopped,
        ProcessStatus::Zombie,
        ProcessStatus::Unknown,
    ];

    for status in statuses {
        println!("  状态: {:?}", status);
    }

    // 3. 进程信息结构说明
    println!("\n📊 进程信息结构:");
    println!("{}", "-".repeat(60));
    let process_info = ProcessInfo {
        pid: 1234,
        name: "example_process".to_string(),
        status: ProcessStatus::Running,
        memory_usage: 1024 * 1024, // 1MB
        cpu_usage: 0.5,             // 50%
        created_at: std::time::SystemTime::now(),
        parent_pid: Some(1),
        children_pids: vec![5678, 5679],
    };

    println!("  进程ID: {}", process_info.pid);
    println!("  进程名称: {}", process_info.name);
    println!("  状态: {:?}", process_info.status);
    println!("  内存使用: {} bytes", process_info.memory_usage);
    println!("  CPU使用率: {:.1}%", process_info.cpu_usage * 100.0);
    println!("  父进程ID: {:?}", process_info.parent_pid);
    println!("  子进程ID: {:?}", process_info.children_pids);

    // 4. 资源监控说明
    println!("\n📊 资源监控说明:");
    println!("{}", "-".repeat(60));
    println!("  1. 使用ProcessManager的get_process_info()获取进程信息");
    println!("  2. 监控内存使用防止内存泄漏");
    println!("  3. 监控CPU使用率识别性能瓶颈");
    println!("  4. 定期检查进程状态");

    // 5. 系统资源说明
    println!("\n📊 系统资源说明:");
    println!("{}", "-".repeat(60));
    let resources = SystemResources {
        total_memory: 8 * 1024 * 1024 * 1024,      // 8GB
        available_memory: 4 * 1024 * 1024 * 1024,  // 4GB
        cpu_cores: 4,
        cpu_usage: 0.3, // 30%
        total_disk: 500 * 1024 * 1024 * 1024,      // 500GB
        available_disk: 250 * 1024 * 1024 * 1024,  // 250GB
        timestamp: std::time::SystemTime::now(),
    };

    println!("  总内存: {} GB", resources.total_memory / (1024 * 1024 * 1024));
    println!("  可用内存: {} GB", resources.available_memory / (1024 * 1024 * 1024));
    println!("  CPU核心数: {}", resources.cpu_cores);
    println!("  CPU使用率: {:.1}%", resources.cpu_usage * 100.0);

    println!("\n💡 监控最佳实践:");
    println!("{}", "-".repeat(60));
    println!("  1. 定期轮询进程状态（避免过于频繁）");
    println!("  2. 设置资源使用阈值和告警");
    println!("  3. 记录历史数据用于分析");
    println!("  4. 使用异步监控避免阻塞主线程");

    println!("\n✅ 进程监控演示完成！");

    Ok(())
}
