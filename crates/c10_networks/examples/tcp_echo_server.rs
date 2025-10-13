//! TCP Echo 服务器示例
//!
//! 这个示例展示了如何使用 c10_networks 库创建一个简单的 TCP Echo 服务器
//!
//! ## 功能特性
//!
//! - ✅ 异步 TCP 服务器
//! - ✅ 多客户端并发处理
//! - ✅ 连接管理和错误处理
//! - ✅ 可配置的套接字选项
//! - ✅ 完整的日志记录
//!
//! ## 运行方式
//!
//! ```bash
//! # 启动服务器
//! cargo run --example tcp_echo_server
//!
//! # 在另一个终端测试连接
//! telnet 127.0.0.1 8080
//! ```
//!
//! ## 配置选项
//!
//! 可以通过环境变量配置服务器：
//! - `C10_TCP_ADDRESS`: 监听地址 (默认: 127.0.0.1:8080)
//! - `C10_TCP_TIMEOUT`: 连接超时 (默认: 30秒)
//! - `C10_TCP_BUFFER_SIZE`: 缓冲区大小 (默认: 8192字节)
//! - `C10_TCP_KEEP_ALIVE`: 启用TCP Keep-Alive (默认: true)
//! - `C10_TCP_NODELAY`: 启用TCP_NODELAY (默认: true)

use c10_networks::{
    error::NetworkResult,
    socket::{TcpConfig, TcpListenerWrapper, TcpSocket},
    //protocol::tcp::{TcpConnection, TcpConnectionConfig},
};
use std::time::Duration;
//use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 启动 TCP Echo 服务器...");

    // 从环境变量读取配置，提供默认值
    let address = std::env::var("C10_TCP_ADDRESS")
        .unwrap_or_else(|_| "127.0.0.1:8080".to_string());
    let timeout_secs = std::env::var("C10_TCP_TIMEOUT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(30);
    let buffer_size = std::env::var("C10_TCP_BUFFER_SIZE")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(8192);
    let keep_alive = std::env::var("C10_TCP_KEEP_ALIVE")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(true);
    let tcp_nodelay = std::env::var("C10_TCP_NODELAY")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(true);

    // 创建服务器配置
    let config = TcpConfig {
        address: address.parse().unwrap(),
        timeout: Some(Duration::from_secs(timeout_secs)),
        buffer_size,
        keep_alive,
        tcp_nodelay,
    };

    // 创建监听器
    let listener = TcpListenerWrapper::new(config).await?;
    let local_addr = listener.local_addr()?;

    println!("📡 服务器监听地址: {}", local_addr);

    // 接受连接循环
    loop {
        match listener.accept().await {
            Ok((socket, peer_addr)) => {
                println!("🔗 新连接来自: {}", peer_addr);

                // 为每个连接创建一个异步任务
                tokio::spawn(async move {
                    if let Err(e) = handle_connection(socket, peer_addr).await {
                        eprintln!("❌ 处理连接时出错: {}", e);
                    }
                });
            }
            Err(e) => {
                eprintln!("❌ 接受连接时出错: {}", e);
            }
        }
    }
}

/// 处理单个连接
async fn handle_connection(
    mut socket: TcpSocket,
    peer_addr: std::net::SocketAddr,
) -> NetworkResult<()> {
    let mut buffer = [0; 1024];

    loop {
        // 读取数据
        match socket.read(&mut buffer).await {
            Ok(0) => {
                println!("📤 客户端 {} 断开连接", peer_addr);
                break;
            }
            Ok(n) => {
                let data = &buffer[..n];
                println!(
                    "📥 从 {} 接收到 {} 字节: {}",
                    peer_addr,
                    n,
                    String::from_utf8_lossy(data)
                );

                // Echo 回数据
                if let Err(e) = socket.write(data).await {
                    eprintln!("❌ 发送数据时出错: {}", e);
                    break;
                }

                println!("📤 向 {} 发送 {} 字节", peer_addr, n);
            }
            Err(e) => {
                eprintln!("❌ 读取数据时出错: {}", e);
                break;
            }
        }
    }

    Ok(())
}
