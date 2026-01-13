//! 跨平台进程管理示例
//!
//! 本示例展示C07进程管理模块的跨平台特性：
//! - Windows/Linux/macOS兼容性
//! - 平台特定API抽象
//! - 跨平台最佳实践
//!
//! 运行方式:
//! ```bash
//! cargo run --example cross_platform_demo
//! ```

use c07_process::prelude::*;

fn main() -> Result<()> {
    println!("🚀 跨平台进程管理示例\n");
    println!("{}", "=".repeat(60));

    // 1. 平台检测
    println!("\n📊 当前平台:");
    println!("{}", "-".repeat(60));
    #[cfg(target_os = "windows")]
    {
        println!("  操作系统: Windows");
        println!("  使用Win32 API进行进程管理");
    }
    #[cfg(target_os = "linux")]
    {
        println!("  操作系统: Linux");
        println!("  使用POSIX API进行进程管理");
    }
    #[cfg(target_os = "macos")]
    {
        println!("  操作系统: macOS");
        println!("  使用POSIX API进行进程管理");
    }
    #[cfg(not(any(target_os = "windows", target_os = "linux", target_os = "macos")))]
    {
        println!("  操作系统: 其他");
        println!("  使用通用API进行进程管理");
    }

    // 2. 跨平台API
    println!("\n📊 跨平台API:");
    println!("{}", "-".repeat(60));
    println!("  ✅ ProcessManager - 统一的进程管理API");
    println!("  ✅ ProcessConfig - 统一的配置结构");
    println!("  ✅ IpcManager - 统一的IPC管理API");
    println!("  ✅ 自动适配不同平台的实现");

    // 3. 平台差异说明
    println!("\n📊 平台差异说明:");
    println!("{}", "-".repeat(60));
    println!("  Windows:");
    println!("    - 使用cmd.exe作为shell");
    println!("    - 不支持Unix信号");
    println!("    - 使用命名管道和TCP套接字");
    println!("\n  Unix/Linux/macOS:");
    println!("    - 使用sh作为shell");
    println!("    - 支持Unix信号");
    println!("    - 支持Unix域套接字");

    // 4. 跨平台最佳实践
    println!("\n💡 跨平台最佳实践:");
    println!("{}", "-".repeat(60));
    println!("  1. 使用C07库提供的统一API");
    println!("  2. 避免使用平台特定的代码");
    println!("  3. 测试所有目标平台");
    println!("  4. 使用条件编译处理平台差异");

    // 5. 进程配置示例
    println!("\n📊 跨平台进程配置示例:");
    println!("{}", "-".repeat(60));

    #[cfg(target_os = "windows")]
    let program = "cmd";
    #[cfg(not(target_os = "windows"))]
    let program = "echo";

    println!("  程序: {} (自动适配平台)", program);
    println!("  配置结构相同，底层实现自动适配");

    println!("\n✅ 跨平台进程管理演示完成！");

    Ok(())
}
