//! C10 Networks 示例程序
//!
//! 展示基于 Rust 1.89 的网络编程功能

use c10_networks::{
    NAME, VERSION,
    error::{ErrorRecovery, NetworkError, NetworkResult},
    protocol::http::{HttpMethod, HttpStatusCode, HttpVersion},
};

#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 {} v{} - Rust 1.89 网络编程示例", NAME, VERSION);

    // 演示 HTTP 客户端
    demo_http_client().await?;

    // 演示错误处理
    demo_error_handling().await?;

    println!("✅ 所有示例运行完成！");
    Ok(())
}

/// 演示 HTTP 客户端功能
async fn demo_http_client() -> NetworkResult<()> {
    println!("\n📡 演示 HTTP 客户端功能");

    // let client = HttpClient::new(); // HttpClient 暂未实现

    // 创建 HTTP 请求
    let mut request = c10_networks::protocol::http::HttpRequest::new(
        HttpMethod::GET,
        "/api/test",
        HttpVersion::Http1_1,
    );

    request.add_header("User-Agent", format!("{}/{}", NAME, VERSION));
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
    response.add_header("Server", format!("{}/{}", NAME, VERSION));
    response.set_body(r#"{"message": "Hello from Rust 1.89!"}"#);

    println!("📥 创建 HTTP 响应:");
    println!("   状态码: {}", response.status);
    println!("   版本: {}", response.version);
    println!("   响应头数量: {}", response.headers.len());
    println!("   响应体长度: {} 字节", response.body.len());

    Ok(())
}

/// 演示错误处理功能
async fn demo_error_handling() -> NetworkResult<()> {
    println!("\n⚠️  演示错误处理功能");

    // 演示不同类型的错误
    let errors = vec![
        NetworkError::Protocol("测试协议错误".to_string()),
        NetworkError::Connection("连接失败".to_string()),
        NetworkError::Timeout(std::time::Duration::from_secs(5)),
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

    Ok(())
}
