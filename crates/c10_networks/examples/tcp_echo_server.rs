//! TCP Echo 服务器示例
//!
//! 这个示例展示了如何使用 c10_networks 库创建一个简单的 TCP Echo 服务器

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

    // 创建服务器配置
    let config = TcpConfig {
        address: "127.0.0.1:8080".parse().unwrap(),
        timeout: Some(Duration::from_secs(30)),
        buffer_size: 8192,
        keep_alive: true,
        tcp_nodelay: true,
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
