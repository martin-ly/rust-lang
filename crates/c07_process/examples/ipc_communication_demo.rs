//! IPC通信完整示例
//!
//! 本示例展示如何使用C07进程管理模块进行IPC通信：
//! - 命名管道通信
//! - TCP套接字通信
//! - 共享内存通信
//! - 消息队列通信
//!
//! 运行方式:
//! ```bash
//! cargo run --example ipc_communication_demo
//! ```
use c07_process::prelude::*;
use std::time::Duration;

fn main() -> Result<()> {
    println!("🚀 IPC通信完整示例\n");
    println!("{}", "=".repeat(60));

    // 1. 创建IPC管理器
    println!("\n📊 创建IPC管理器:");
    println!("{}", "-".repeat(60));
    let config = IpcConfig {
        protocol: IpcProtocol::Pipe,
        timeout: Duration::from_secs(5),
        retry_count: 3,
        buffer_size: 4096,
        encrypted: false,
    };
    let mut ipc = IpcManager::new(config.clone());
    println!("✅ IPC管理器创建成功");

    // 2. 命名管道示例
    println!("\n📊 命名管道示例:");
    println!("{}", "-".repeat(60));
    match ipc.create_named_pipe("demo_pipe") {
        Ok(_) => println!("✅ 命名管道创建成功: demo_pipe"),
        Err(e) => println!("⚠️  命名管道创建失败: {}", e),
    }

    // 3. TCP套接字示例
    println!("\n📊 TCP套接字示例:");
    println!("{}", "-".repeat(60));
    match ipc.create_tcp_socket("127.0.0.1", 8080) {
        Ok(_) => println!("✅ TCP套接字创建成功: 127.0.0.1:8080"),
        Err(e) => println!("⚠️  TCP套接字创建失败: {}", e),
    }

    // 4. 共享内存示例
    println!("\n📊 共享内存示例:");
    println!("{}", "-".repeat(60));
    match ipc.create_shared_memory("demo_memory", 1024) {
        Ok(_) => println!("✅ 共享内存创建成功: demo_memory (1024 bytes)"),
        Err(e) => println!("⚠️  共享内存创建失败: {}", e),
    }

    // 5. 消息队列示例
    println!("\n📊 消息队列示例:");
    println!("{}", "-".repeat(60));
    match ipc.create_message_queue("demo_queue", 100) {
        Ok(_) => println!("✅ 消息队列创建成功: demo_queue (容量: 100)"),
        Err(e) => println!("⚠️  消息队列创建失败: {}", e),
    }

    // 6. IPC配置说明
    println!("\n💡 IPC配置说明:");
    println!("{}", "-".repeat(60));
    println!("  协议: {:?}", config.protocol);
    println!("  超时: {:?}", config.timeout);
    println!("  重试次数: {}", config.retry_count);
    println!("  缓冲区大小: {} bytes", config.buffer_size);
    println!("  加密: {}", config.encrypted);

    println!("\n✅ IPC通信演示完成！");

    Ok(())
}
