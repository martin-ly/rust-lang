//! TCP 客户端示例
//!
//! 这个示例展示了如何使用 c10_networks 库创建一个 TCP 客户端

use c10_networks::{
    error::NetworkResult,
    socket::{TcpConfig, TcpSocket},
    //protocol::tcp::{TcpConnection, TcpConnectionConfig},
};
use std::time::Duration;
//use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 启动 TCP 客户端...");

    // 创建客户端配置
    let config = TcpConfig {
        address: "127.0.0.1:8080".parse().unwrap(),
        timeout: Some(Duration::from_secs(30)),
        buffer_size: 8192,
        keep_alive: true,
        tcp_nodelay: true,
    };

    // 创建套接字并连接
    let mut socket = TcpSocket::new(config);
    socket.connect().await?;

    println!("🔗 已连接到服务器: {}", socket.peer_addr().unwrap());

    // 发送一些测试消息
    let messages = vec![
        "Hello, Server!",
        "This is a test message",
        "Rust 1.89 is awesome!",
        "Goodbye!",
    ];

    for message in messages {
        println!("📤 发送消息: {}", message);

        // 发送消息
        socket.write(message.as_bytes()).await?;

        // 读取响应
        let mut buffer = [0; 1024];
        let n = socket.read(&mut buffer).await?;
        let response = String::from_utf8_lossy(&buffer[..n]);

        println!("📥 收到响应: {}", response);

        // 等待一秒
        tokio::time::sleep(Duration::from_secs(1)).await;
    }

    println!("✅ 客户端完成");
    Ok(())
}
