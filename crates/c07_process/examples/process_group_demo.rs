//! 进程组管理示例
//!
//! 本示例展示如何使用C07进程管理模块进行进程组管理：
//! - 进程组创建
//! - 进程组配置
//! - 进程组操作
//!
//! 运行方式:
//! ```bash
//! cargo run --example process_group_demo
//! ```

use c07_process::prelude::*;
use c07_process::ProcessGroupManager;
use std::collections::HashMap;

fn main() -> Result<()> {
    println!("🚀 进程组管理示例\n");
    println!("{}", "=".repeat(60));

    // 1. 创建进程组管理器
    println!("\n📊 创建进程组管理器:");
    println!("{}", "-".repeat(60));
    let _pgm = ProcessGroupManager::new();
    println!("✅ ProcessGroupManager创建成功");

    // 2. 进程组配置示例
    println!("\n📊 进程组配置示例:");
    println!("{}", "-".repeat(60));
    let mut env = HashMap::new();
    env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    env.insert("RUST_LOG".to_string(), "info".to_string());

    let group_config = ProcessConfig {
        program: "echo".to_string(),
        args: vec!["Group".to_string(), "Demo".to_string()],
        env,
        working_dir: Some("/tmp".to_string()),
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: ResourceLimits::default(),
    };

    println!("  程序: {}", group_config.program);
    println!("  参数: {:?}", group_config.args);
    println!("  工作目录: {:?}", group_config.working_dir);
    println!("  环境变量数量: {}", group_config.env.len());

    // 3. 进程组功能说明
    println!("\n📊 进程组功能说明:");
    println!("{}", "-".repeat(60));
    println!("  ✅ 同时管理多个相关进程");
    println!("  ✅ 统一的进程配置");
    println!("  ✅ 批量操作（启动/停止/监控）");
    println!("  ✅ 进程间依赖管理");

    // 4. 使用场景
    println!("\n💡 进程组使用场景:");
    println!("{}", "-".repeat(60));
    println!("  1. 微服务架构 - 管理多个服务进程");
    println!("  2. 并行计算 - 管理worker进程池");
    println!("  3. 测试环境 - 管理测试进程组");
    println!("  4. 开发环境 - 管理开发工具链");

    // 5. 最佳实践
    println!("\n💡 进程组管理最佳实践:");
    println!("{}", "-".repeat(60));
    println!("  1. 使用进程组管理相关进程");
    println!("  2. 设置统一的资源限制");
    println!("  3. 实现优雅关闭机制");
    println!("  4. 监控进程组整体状态");

    println!("\n✅ 进程组管理演示完成！");

    Ok(())
}
