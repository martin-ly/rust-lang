//! WebSocket 演示示例
//!
//! 这个示例展示了如何使用 c10_networks 库创建 WebSocket 帧和握手
//!
//! ## 功能特性
//!
//! - ✅ WebSocket 帧创建和解析
//! - ✅ 握手请求和响应
//! - ✅ 密钥生成和验证
//! - ✅ 操作码特性演示
//! - ✅ 完整的协议支持
//!
//! ## 运行方式
//!
//! ```bash
//! # 运行演示
//! cargo run --example websocket_demo
//! ```
//!
//! ## WebSocket 协议支持
//!
//! 本示例演示了以下 WebSocket 特性：
//! - **文本帧**: 用于传输 UTF-8 文本数据
//! - **二进制帧**: 用于传输二进制数据
//! - **控制帧**: Ping、Pong、Close 帧
//! - **握手**: HTTP 升级到 WebSocket 协议
//! - **密钥验证**: WebSocket 安全握手机制
//!
//! ## 配置选项
//!
//! 可以通过环境变量配置演示：
//! - `C10_WS_DEMO_HOST`: 演示主机名 (默认: example.com)
//! - `C10_WS_DEMO_PATH`: 演示路径 (默认: /chat)
//! - `C10_WS_DEMO_KEY`: 自定义密钥 (可选)
use c10_networks::{
    error::NetworkResult,
    protocol::websocket::{
        WebSocketClient, WebSocketFrame, WebSocketHandshakeRequest, WebSocketHandshakeResponse,
        WebSocketOpcode,
    },
};

#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 启动 WebSocket 演示示例...");

    // 演示 WebSocket 帧创建
    println!("\n📡 演示 WebSocket 帧创建:");

    // 创建文本帧
    let text_frame = WebSocketFrame::text("Hello, WebSocket!");
    println!("📤 文本帧:");
    println!("   操作码: {:?}", text_frame.opcode);
    println!("   载荷长度: {}", text_frame.payload_length);
    println!(
        "   载荷内容: {}",
        String::from_utf8_lossy(&text_frame.payload)
    );

    // 创建二进制帧
    let binary_frame = WebSocketFrame::binary(&[1, 2, 3, 4, 5]);
    println!("📤 二进制帧:");
    println!("   操作码: {:?}", binary_frame.opcode);
    println!("   载荷长度: {}", binary_frame.payload_length);
    println!("   载荷内容: {:?}", binary_frame.payload.as_ref());

    // 创建关闭帧
    let close_frame = WebSocketFrame::close(Some(1000), Some("Normal closure"));
    println!("📤 关闭帧:");
    println!("   操作码: {:?}", close_frame.opcode);
    println!("   载荷长度: {}", close_frame.payload_length);

    // 创建 Ping 帧
    let ping_frame = WebSocketFrame::ping(Some(b"ping data"));
    println!("📤 Ping 帧:");
    println!("   操作码: {:?}", ping_frame.opcode);
    println!("   载荷长度: {}", ping_frame.payload_length);

    // 创建 Pong 帧
    let pong_frame = WebSocketFrame::pong(Some(b"pong data"));
    println!("📤 Pong 帧:");
    println!("   操作码: {:?}", pong_frame.opcode);
    println!("   载荷长度: {}", pong_frame.payload_length);

    // 演示 WebSocket 握手
    println!("\n🤝 演示 WebSocket 握手:");

    // 从环境变量读取配置
    let host = std::env::var("C10_WS_DEMO_HOST")
        .unwrap_or_else(|_| "example.com".to_string());
    let path = std::env::var("C10_WS_DEMO_PATH")
        .unwrap_or_else(|_| "/chat".to_string());
    let custom_key = std::env::var("C10_WS_DEMO_KEY").ok();

    // 创建握手请求
    let mut request = WebSocketHandshakeRequest::new(&path);
    request.set_host(&host);
    request.set_websocket_key(&custom_key.unwrap_or_else(|| "dGhlIHNhbXBsZSBub25jZQ==".to_string()));
    request.set_websocket_version("13");
    request.set_upgrade();

    println!("📤 WebSocket 握手请求:");
    println!("{}", request.encode());

    // 创建握手响应
    let mut response = WebSocketHandshakeResponse::new(101, "Switching Protocols");
    response.set_websocket_accept("s3pPLMBiTxaQ9kYGzzhZRbK+xOo=");
    response.set_upgrade();

    println!("📥 WebSocket 握手响应:");
    println!("{}", response.encode());

    // 演示 WebSocket 客户端工具
    println!("\n🔧 演示 WebSocket 客户端工具:");

    let key = WebSocketClient::generate_key();
    println!("🔑 生成的 WebSocket 密钥: {}", key);

    let accept = WebSocketClient::calculate_accept(&key);
    println!("✅ 计算的接受密钥: {}", accept);

    // 演示操作码特性
    println!("\n🎯 演示操作码特性:");

    let opcodes = vec![
        WebSocketOpcode::Text,
        WebSocketOpcode::Binary,
        WebSocketOpcode::Close,
        WebSocketOpcode::Ping,
        WebSocketOpcode::Pong,
    ];

    for opcode in opcodes {
        println!("🔍 操作码: {:?}", opcode);
        println!("   是否为控制帧: {}", opcode.is_control_frame());
        println!("   是否为数据帧: {}", opcode.is_data_frame());
    }

    println!("\n✅ WebSocket 演示示例完成！");
    Ok(())
}
