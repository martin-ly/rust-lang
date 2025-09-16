//! HTTP 客户端示例
//!
//! 这个示例展示了如何使用 c10_networks 库创建一个 HTTP 客户端

use c10_networks::{
    error::{ErrorRecovery, NetworkResult},
    protocol::http::{HttpMethod, HttpStatusCode, HttpVersion},
};
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
    response.set_body(r#"{"message": "Hello from Rust 1.89!", "status": "success"}"#);

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
        println!("   可重试: {}", error.is_retryable());
        if let Some(delay) = error.retry_delay() {
            println!("   重试延迟: {:?}", delay);
        }
        if let Some(max_retries) = error.max_retries() {
            println!("   最大重试次数: {}", max_retries);
        }
        println!();
    }

    println!("✅ HTTP 客户端示例完成！");
    Ok(())
}
