//! TCP 客户端示例
//!
//! 这个示例展示了如何使用 c10_networks 库创建一个 TCP 客户端
//!
//! ## 📖 理论基础
//!
//! TCP (传输控制协议) 是一种面向连接的、可靠的传输层协议。它提供：
//!
//! - **连接导向**: 建立连接、数据传输、连接释放
//! - **可靠性**: 数据包确认、重传、排序
//! - **流量控制**: 滑动窗口机制
//! - **拥塞控制**: 慢启动、拥塞避免、快速重传
//!
//! ## 🔬 实现原理
//!
//! ### TCP 连接建立过程
//!
//! 1. **SYN**: 客户端发送 SYN 包，请求建立连接
//! 2. **SYN-ACK**: 服务器响应 SYN-ACK 包，确认连接请求
//! 3. **ACK**: 客户端发送 ACK 包，完成三次握手
//!
//! ### 配置参数说明
//!
//! - `address`: 目标服务器的 IP 地址和端口号
//! - `timeout`: 连接建立的最大等待时间，防止无限等待
//! - `buffer_size`: 读写缓冲区大小，影响内存使用和性能
//! - `keep_alive`: 启用 TCP Keep-Alive，检测连接状态
//! - `tcp_nodelay`: 禁用 Nagle 算法，减少延迟
//!
//! ## 🚀 使用场景
//!
//! - **客户端应用**: 连接到服务器获取服务
//! - **微服务通信**: 服务间通信
//! - **数据同步**: 定期数据同步
//! - **实时通信**: 聊天、游戏等实时应用
//!
//! ## ⚠️ 注意事项
//!
//! - **错误处理**: 网络连接可能失败，需要适当的错误处理
//! - **资源管理**: 及时关闭连接，避免资源泄漏
//! - **超时设置**: 合理设置超时时间，避免长时间等待
//! - **缓冲区大小**: 根据应用需求调整缓冲区大小
//!
//! ## 🔧 运行方式
//!
//! ```bash
//! # 运行客户端示例
//! cargo run --example tcp_client
//! 
//! # 需要先启动对应的服务器
//! cargo run --example tcp_echo_server
//! ```

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
