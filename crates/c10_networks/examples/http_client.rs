//! HTTP 客户端示例
//!
//! 这个示例展示了如何使用 c10_networks 库创建一个 HTTP 客户端
//!
//! ## 📐 知识结构
//!
//! ### 核心概念
//!
//! - **HTTP 客户端**: 用于发送 HTTP 请求并接收响应的客户端程序
//!   - **属性**: 请求构建、响应处理、错误处理、重试机制
//!   - **关系**: 与 HTTP 协议、网络编程相关
//!
//! ### 思维导图
//!
//! ```text
//! HTTP 客户端演示
//! │
//! ├── 请求构建
//! │   ├── 请求方法
//! │   ├── 请求头
//! │   └── 请求体
//! ├── 响应处理
//! │   ├── 状态码
//! │   └── 响应体
//! └── 错误处理
//!     ├── 网络错误
//!     └── 重试机制
//! ```
//!
//! ## 📖 理论基础
//!
//! HTTP (超文本传输协议) 是应用层协议，用于 Web 通信：
//!
//! - **请求-响应模型**: 客户端发送请求，服务器返回响应
//! - **无状态**: 每个请求独立处理
//! - **可扩展**: 支持各种扩展和功能
//! - **文本协议**: 人类可读的协议格式
//!
//! ## 🔬 实现原理
//!
//! ### HTTP 请求结构
//!
//! ```rust
//! pub struct HttpRequest {
//!     pub method: HttpMethod,      // GET, POST, PUT, DELETE 等
//!     pub uri: String,            // 请求路径
//!     pub version: HttpVersion,   // HTTP/1.1, HTTP/2 等
//!     pub headers: HashMap<String, String>, // 请求头
//!     pub body: Vec<u8>,          // 请求体
//! }
//! ```
//!
//! ### HTTP 响应结构
//!
//! ```rust
//! pub struct HttpResponse {
//!     pub version: HttpVersion,   // HTTP 版本
//!     pub status: HttpStatusCode,  // 状态码
//!     pub headers: HashMap<String, String>, // 响应头
//!     pub body: Vec<u8>,          // 响应体
//! }
//! ```
//!
//! ## 🚀 使用场景
//!
//! - **Web 应用**: 构建 Web 应用和 API
//! - **数据获取**: 从服务器获取数据
//! - **文件传输**: 上传和下载文件
//! - **API 调用**: 调用 RESTful API
//!
//! ## ⚠️ 注意事项
//!
//! - **错误处理**: 处理各种 HTTP 错误状态码
//! - **超时设置**: 设置合理的请求超时时间
//! - **重试机制**: 实现适当的重试逻辑
//! - **安全考虑**: 注意 HTTPS 和安全头
//!
//! ## 🔧 运行方式
//!
//! ```bash
//! # 运行 HTTP 客户端示例
//! cargo run --example http_client
//! ```
use c10_networks::{
    error::NetworkResult,
    protocol::http::{HttpMethod, HttpStatusCode, HttpVersion},
};
use common::RustLangError;
use std::time::Duration;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 启动 HTTP 客户端示例...");

    // 创建 HTTP 客户端
    // let client = HttpClient::new(); // HttpClient 暂未实现

    // 创建 HTTP 请求
    let mut request =
        c10_networks::protocol::http::HttpRequest::new(HttpMethod::GET, "/", HttpVersion::Http1_1);

    request.add_header("Host", "httpbin.org");
    request.add_header("User-Agent", "c10_networks/0.1.0");
    request.add_header("Accept", "application/json");

    println!("📤 创建 HTTP 请求:");
    println!("   方法: {}", request.method);
    println!("   URI: {}", request.uri);
    println!("   版本: {}", request.version);
    println!("   请求头数量: {}", request.headers.len());

    // 创建 HTTP 响应
    let mut response =
        c10_networks::protocol::http::HttpResponse::new(HttpVersion::Http1_1, HttpStatusCode::ok());

    response.add_header("Content-Type", "application/json");
    response.add_header("Server", "c10_networks/0.1.0");
    response.set_body(r#"{"message": "Hello from Rust 1.92.0!", "status": "success"}"#);

    println!("📥 创建 HTTP 响应:");
    println!("   状态码: {}", response.status);
    println!("   版本: {}", response.version);
    println!("   响应头数量: {}", response.headers.len());
    println!("   响应体长度: {} 字节", response.body.len());
    println!("   响应体内容: {}", String::from_utf8_lossy(&response.body));

    // 演示错误处理
    println!("\n⚠️  演示错误处理:");

    let errors = vec![
        c10_networks::error::NetworkError::Protocol("测试协议错误".to_string()),
        c10_networks::error::NetworkError::Connection("连接失败".to_string()),
        c10_networks::error::NetworkError::Timeout(Duration::from_secs(5)),
    ];

    for error in errors {
        println!("🔍 错误类型: {}", error);
        println!("   可重试: {}", RustLangError::is_retryable(&error));
        if let Some(delay) = RustLangError::retry_delay(&error) {
            println!("   重试延迟: {:?}", delay);
        }
        if let Some(max_retries) = RustLangError::max_retries(&error) {
            println!("   最大重试次数: {}", max_retries);
        }
        println!();
    }

    println!("✅ HTTP 客户端示例完成！");
    Ok(())
}
