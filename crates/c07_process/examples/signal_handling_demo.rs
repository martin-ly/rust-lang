//! 信号处理示例
//!
//! 本示例展示进程信号处理的概念和最佳实践：
//! - 信号类型说明
//! - 信号处理策略
//! - 跨平台注意事项
//!
//! 注意：Windows不支持Unix信号，本示例主要展示概念
//!
//! 运行方式:
//! ```bash
//! cargo run --example signal_handling_demo
//! ```
use c07_process::prelude::*;

fn main() -> Result<()> {
    println!("🚀 信号处理示例\n");
    println!("{}", "=".repeat(60));

    // 1. 信号类型说明
    println!("\n📊 信号类型说明:");
    println!("{}", "-".repeat(60));
    println!("  SIGTERM - 终止信号（可捕获）");
    println!("  SIGKILL - 强制终止（不可捕获）");
    println!("  SIGINT  - 中断信号（Ctrl+C）");
    println!("  SIGCHLD - 子进程状态改变");
    println!("  SIGHUP  - 挂起信号");

    // 2. 信号处理策略
    println!("\n📊 信号处理策略:");
    println!("{}", "-".repeat(60));
    println!("  1. 使用ProcessManager的kill()方法发送信号");
    println!("  2. 在实际应用中，使用signal-hook或ctrlc库处理信号");
    println!("  3. 确保信号处理函数是async-signal-safe的");

    // 3. 进程终止示例
    println!("\n📊 进程终止示例:");
    println!("{}", "-".repeat(60));
    let _pm = ProcessManager::new();

    // 注意：这里只是演示API，实际使用需要先创建进程
    println!("✅ ProcessManager创建成功");
    println!("  使用 pm.kill(pid) 可以发送终止信号");

    // 4. 跨平台注意事项
    println!("\n💡 跨平台注意事项:");
    println!("{}", "-".repeat(60));
    println!("  ⚠️  Windows不支持Unix信号");
    println!("  ✅ Unix/Linux: 使用kill系统调用");
    println!("  ✅ Windows: 使用TerminateProcess API");
    println!("  ✅ C07库提供了跨平台抽象");

    // 5. 最佳实践
    println!("\n💡 最佳实践:");
    println!("{}", "-".repeat(60));
    println!("  1. 优先使用SIGTERM而不是SIGKILL");
    println!("  2. 给进程时间进行清理工作");
    println!("  3. 使用超时机制防止进程无法终止");
    println!("  4. 记录信号处理日志便于调试");

    println!("\n✅ 信号处理演示完成！");

    Ok(())
}
