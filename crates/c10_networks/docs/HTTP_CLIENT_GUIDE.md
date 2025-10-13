# HTTP客户端指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](STYLE.md)。

## 📋 目录

- [HTTP客户端指南](#http客户端指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [主要特性](#主要特性)
  - [⚡ 快速开始](#-快速开始)
    - [基础HTTP请求](#基础http请求)
    - [运行示例](#运行示例)
  - [🔧 基础用法](#-基础用法)
    - [创建客户端](#创建客户端)
    - [HTTP方法支持](#http方法支持)
    - [请求头管理](#请求头管理)
    - [查询参数](#查询参数)
  - [🌐 HTTP/1.1 支持](#-http11-支持)
    - [基础HTTP/1.1请求](#基础http11请求)
    - [持久连接](#持久连接)
    - [分块传输编码](#分块传输编码)
  - [🚀 HTTP/2 支持](#-http2-支持)
    - [启用HTTP/2](#启用http2)
    - [多路复用](#多路复用)
    - [服务器推送](#服务器推送)
  - [🔒 HTTPS/TLS 支持](#-httpstls-支持)
    - [基础HTTPS请求](#基础https请求)
    - [客户端证书认证](#客户端证书认证)
    - [自定义CA证书](#自定义ca证书)
    - [证书固定](#证书固定)
  - [📊 高级特性](#-高级特性)
    - [请求重试](#请求重试)
    - [请求超时](#请求超时)
    - [代理支持](#代理支持)
    - [请求/响应拦截器](#请求响应拦截器)
  - [⚙️ 配置选项](#️-配置选项)
    - [HttpConfig 完整配置](#httpconfig-完整配置)
    - [环境变量配置](#环境变量配置)
  - [🔍 错误处理](#-错误处理)
    - [错误类型](#错误类型)
    - [错误重试](#错误重试)
  - [📈 性能优化](#-性能优化)
    - [连接池优化](#连接池优化)
    - [并发请求](#并发请求)
    - [流式处理](#流式处理)
  - [🧪 测试示例](#-测试示例)
    - [单元测试](#单元测试)
    - [集成测试](#集成测试)
    - [性能测试](#性能测试)
  - [❓ 常见问题](#-常见问题)
    - [Q: 如何设置自定义User-Agent？](#q-如何设置自定义user-agent)
    - [Q: 如何处理重定向？](#q-如何处理重定向)
    - [Q: 如何设置请求超时？](#q-如何设置请求超时)
    - [Q: 如何启用HTTP/2？](#q-如何启用http2)
    - [Q: 如何处理HTTPS证书验证？](#q-如何处理https证书验证)
    - [Q: 如何设置代理？](#q-如何设置代理)
    - [Q: 如何实现请求重试？](#q-如何实现请求重试)
    - [Q: 如何优化性能？](#q-如何优化性能)

## 🎯 概述

C10 Networks 提供了完整的HTTP客户端实现，支持HTTP/1.1、HTTP/2和HTTPS协议。本指南将详细介绍如何使用HTTP客户端进行网络请求。

### 主要特性

- **HTTP/1.1**: 完整的请求/响应处理
- **HTTP/2**: 多路复用和头部压缩
- **HTTPS**: TLS加密传输
- **连接池**: 高效的连接复用
- **异步I/O**: 基于Tokio的高性能实现
- **错误处理**: 详细的错误信息和重试机制

## ⚡ 快速开始

### 基础HTTP请求

```rust
use c10_networks::protocol::http::{HttpClient, HttpMethod};
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 创建HTTP客户端
    let client = HttpClient::new();
    
    // 发送GET请求
    let response = client.get("https://httpbin.org/get").await?;
    
    println!("状态码: {}", response.status);
    println!("响应体: {}", String::from_utf8_lossy(&response.body));
    
    Ok(())
}
```

### 运行示例

```bash
cargo run --example http_client
```

## 🔧 基础用法

### 创建客户端

```rust
use c10_networks::protocol::http::{HttpClient, HttpConfig};

// 使用默认配置
let client = HttpClient::new();

// 使用自定义配置
let config = HttpConfig::new()
    .with_timeout(Duration::from_secs(30))
    .with_max_redirects(5)
    .with_user_agent("MyApp/1.0");
let client = HttpClient::with_config(config);
```

### HTTP方法支持

```rust
use c10_networks::protocol::http::{HttpClient, HttpMethod};

let client = HttpClient::new();

// GET请求
let get_response = client.get("https://httpbin.org/get").await?;

// POST请求
let post_data = b"{\"name\": \"C10 Networks\"}";
let post_response = client.post("https://httpbin.org/post", post_data).await?;

// PUT请求
let put_data = b"{\"id\": 1, \"name\": \"Updated\"}";
let put_response = client.put("https://httpbin.org/put", put_data).await?;

// DELETE请求
let delete_response = client.delete("https://httpbin.org/delete").await?;

// PATCH请求
let patch_data = b"{\"status\": \"active\"}";
let patch_response = client.patch("https://httpbin.org/patch", patch_data).await?;
```

### 请求头管理

```rust
use c10_networks::protocol::http::{HttpClient, HttpRequest, HttpMethod};
use std::collections::HashMap;

let client = HttpClient::new();

// 创建自定义请求
let mut request = HttpRequest::new(HttpMethod::GET, "https://httpbin.org/headers");

// 添加请求头
request.add_header("User-Agent", "C10-Networks/1.0");
request.add_header("Accept", "application/json");
request.add_header("Authorization", "Bearer token123");

// 发送请求
let response = client.send_request(request).await?;
```

### 查询参数

```rust
use c10_networks::protocol::http::{HttpClient, HttpRequest, HttpMethod};

let client = HttpClient::new();

// 方法1: 直接在URL中添加查询参数
let response = client.get("https://httpbin.org/get?param1=value1&param2=value2").await?;

// 方法2: 使用HttpRequest构建器
let mut request = HttpRequest::new(HttpMethod::GET, "https://httpbin.org/get");
request.add_query_param("param1", "value1");
request.add_query_param("param2", "value2");

let response = client.send_request(request).await?;
```

## 🌐 HTTP/1.1 支持

### 基础HTTP/1.1请求

```rust
use c10_networks::protocol::http::{HttpClient, HttpVersion};

let client = HttpClient::new();

// 明确指定HTTP/1.1
let response = client.get("https://httpbin.org/get")
    .with_version(HttpVersion::Http1_1)
    .await?;
```

### 持久连接

```rust
use c10_networks::protocol::http::{HttpClient, HttpConfig};

let config = HttpConfig::new()
    .with_keep_alive(true)
    .with_connection_timeout(Duration::from_secs(60));

let client = HttpClient::with_config(config);

// 多个请求将复用同一个连接
let response1 = client.get("https://httpbin.org/get").await?;
let response2 = client.get("https://httpbin.org/get").await?;
```

### 分块传输编码

```rust
use c10_networks::protocol::http::{HttpClient, HttpRequest, HttpMethod};

let client = HttpClient::new();

let mut request = HttpRequest::new(HttpMethod::POST, "https://httpbin.org/post");
request.add_header("Transfer-Encoding", "chunked");

// 发送分块数据
let chunk1 = b"Hello";
let chunk2 = b" World";
let chunk3 = b"!";

request.add_chunk(chunk1);
request.add_chunk(chunk2);
request.add_chunk(chunk3);

let response = client.send_request(request).await?;
```

## 🚀 HTTP/2 支持

### 启用HTTP/2

```rust
use c10_networks::protocol::http::{HttpClient, HttpConfig, HttpVersion};

let config = HttpConfig::new()
    .with_version(HttpVersion::Http2)
    .with_max_concurrent_streams(100);

let client = HttpClient::with_config(config);

// HTTP/2请求
let response = client.get("https://httpbin.org/get").await?;
```

### 多路复用

```rust
use c10_networks::protocol::http::HttpClient;
use futures::future::join_all;

let client = HttpClient::new();

// 并发发送多个请求，HTTP/2会自动多路复用
let futures = vec![
    client.get("https://httpbin.org/get"),
    client.get("https://httpbin.org/get"),
    client.get("https://httpbin.org/get"),
];

let responses = join_all(futures).await;
for response in responses {
    let response = response?;
    println!("响应状态: {}", response.status);
}
```

### 服务器推送

```rust
use c10_networks::protocol::http::{HttpClient, HttpConfig, HttpVersion};

let config = HttpConfig::new()
    .with_version(HttpVersion::Http2)
    .with_server_push_enabled(true);

let client = HttpClient::with_config(config);

// 处理服务器推送
let response = client.get("https://httpbin.org/get").await?;

// 检查是否有推送的资源
if let Some(pushed_resources) = response.pushed_resources {
    for resource in pushed_resources {
        println!("推送资源: {}", resource.path);
    }
}
```

## 🔒 HTTPS/TLS 支持

### 基础HTTPS请求

```rust
use c10_networks::protocol::http::{HttpClient, HttpConfig};
use c10_networks::security::tls_reload::TlsConfig;

let tls_config = TlsConfig::default()
    .with_verify_certificates(true)
    .with_verify_hostname(true);

let http_config = HttpConfig::new()
    .with_tls_config(tls_config);

let client = HttpClient::with_config(http_config);

// HTTPS请求
let response = client.get("https://httpbin.org/get").await?;
println!("安全连接: {}", response.is_secure());
```

### 客户端证书认证

```rust
use c10_networks::security::tls_reload::TlsConfig;
use c10_networks::protocol::http::{HttpClient, HttpConfig};

let tls_config = TlsConfig::default()
    .with_client_certificate("client.crt", "client.key")
    .with_ca_certificate("ca.crt");

let http_config = HttpConfig::new()
    .with_tls_config(tls_config);

let client = HttpClient::with_config(http_config);

// 使用客户端证书进行认证
let response = client.get("https://secure.example.com/api").await?;
```

### 自定义CA证书

```rust
use c10_networks::security::tls_reload::TlsConfig;

let tls_config = TlsConfig::default()
    .with_ca_certificate("custom-ca.crt")
    .with_verify_certificates(true);

let http_config = HttpConfig::new()
    .with_tls_config(tls_config);

let client = HttpClient::with_config(http_config);
```

### 证书固定

```rust
use c10_networks::security::tls_reload::TlsConfig;

let tls_config = TlsConfig::default()
    .with_certificate_pinning("sha256/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=")
    .with_verify_certificates(true);

let http_config = HttpConfig::new()
    .with_tls_config(tls_config);

let client = HttpClient::with_config(http_config);
```

## 📊 高级特性

### 请求重试

```rust
use c10_networks::protocol::http::{HttpClient, HttpConfig, RetryConfig};

let retry_config = RetryConfig::new()
    .with_max_attempts(3)
    .with_backoff_strategy(BackoffStrategy::Exponential)
    .with_retryable_status_codes(vec![500, 502, 503, 504]);

let http_config = HttpConfig::new()
    .with_retry_config(retry_config);

let client = HttpClient::with_config(http_config);

// 自动重试的请求
let response = client.get("https://unstable-api.example.com/data").await?;
```

### 请求超时

```rust
use c10_networks::protocol::http::{HttpClient, HttpConfig};
use std::time::Duration;

let config = HttpConfig::new()
    .with_timeout(Duration::from_secs(30))
    .with_connection_timeout(Duration::from_secs(10))
    .with_read_timeout(Duration::from_secs(20));

let client = HttpClient::with_config(config);
```

### 代理支持

```rust
use c10_networks::protocol::http::{HttpClient, HttpConfig, ProxyConfig};

let proxy_config = ProxyConfig::new()
    .with_http_proxy("http://proxy.example.com:8080")
    .with_https_proxy("http://proxy.example.com:8080")
    .with_no_proxy(vec!["localhost".to_string(), "127.0.0.1".to_string()]);

let http_config = HttpConfig::new()
    .with_proxy_config(proxy_config);

let client = HttpClient::with_config(http_config);
```

### 请求/响应拦截器

```rust
use c10_networks::protocol::http::{HttpClient, HttpConfig, Interceptor};

struct LoggingInterceptor;

impl Interceptor for LoggingInterceptor {
    fn on_request(&self, request: &mut HttpRequest) -> NetworkResult<()> {
        println!("发送请求: {} {}", request.method(), request.url());
        Ok(())
    }
    
    fn on_response(&self, response: &HttpResponse) -> NetworkResult<()> {
        println!("收到响应: {}", response.status());
        Ok(())
    }
}

let config = HttpConfig::new()
    .with_interceptor(Box::new(LoggingInterceptor));

let client = HttpClient::with_config(config);
```

## ⚙️ 配置选项

### HttpConfig 完整配置

```rust
use c10_networks::protocol::http::{HttpConfig, HttpVersion, RetryConfig, ProxyConfig};
use c10_networks::security::tls_reload::TlsConfig;
use std::time::Duration;

let config = HttpConfig::new()
    // 基础配置
    .with_version(HttpVersion::Http2)
    .with_timeout(Duration::from_secs(30))
    .with_connection_timeout(Duration::from_secs(10))
    .with_read_timeout(Duration::from_secs(20))
    
    // 连接配置
    .with_keep_alive(true)
    .with_max_connections(100)
    .with_max_connections_per_host(10)
    
    // 重试配置
    .with_retry_config(RetryConfig::new()
        .with_max_attempts(3)
        .with_backoff_strategy(BackoffStrategy::Exponential))
    
    // 代理配置
    .with_proxy_config(ProxyConfig::new()
        .with_http_proxy("http://proxy.example.com:8080"))
    
    // TLS配置
    .with_tls_config(TlsConfig::default()
        .with_verify_certificates(true)
        .with_verify_hostname(true))
    
    // 其他配置
    .with_max_redirects(5)
    .with_user_agent("MyApp/1.0")
    .with_accept_gzip(true)
    .with_follow_redirects(true);
```

### 环境变量配置

```bash
# HTTP客户端配置
export C10_HTTP_TIMEOUT=30000
export C10_HTTP_MAX_REDIRECTS=5
export C10_HTTP_USER_AGENT="MyApp/1.0"
export C10_HTTP_VERIFY_CERTIFICATES=true
export C10_HTTP_VERIFY_HOSTNAME=true

# 代理配置
export C10_HTTP_PROXY=http://proxy.example.com:8080
export C10_HTTPS_PROXY=http://proxy.example.com:8080
export C10_NO_PROXY=localhost,127.0.0.1
```

## 🔍 错误处理

### 错误类型

```rust
use c10_networks::error::{NetworkError, NetworkResult};

async fn handle_http_request() -> NetworkResult<()> {
    let client = HttpClient::new();
    
    match client.get("https://httpbin.org/get").await {
        Ok(response) => {
            println!("请求成功: {}", response.status);
            Ok(())
        }
        Err(NetworkError::Timeout) => {
            eprintln!("请求超时");
            Err(NetworkError::Timeout)
        }
        Err(NetworkError::ConnectionError(e)) => {
            eprintln!("连接错误: {}", e);
            Err(NetworkError::ConnectionError(e))
        }
        Err(NetworkError::HttpError(status)) => {
            eprintln!("HTTP错误: {}", status);
            Err(NetworkError::HttpError(status))
        }
        Err(e) => {
            eprintln!("其他错误: {}", e);
            Err(e)
        }
    }
}
```

### 错误重试

```rust
use c10_networks::protocol::http::{HttpClient, HttpConfig, RetryConfig};
use c10_networks::error::NetworkResult;

async fn resilient_request() -> NetworkResult<()> {
    let retry_config = RetryConfig::new()
        .with_max_attempts(5)
        .with_backoff_strategy(BackoffStrategy::Exponential)
        .with_retryable_errors(vec![
            NetworkError::Timeout,
            NetworkError::ConnectionError("".to_string()),
        ]);

    let config = HttpConfig::new()
        .with_retry_config(retry_config);

    let client = HttpClient::with_config(config);
    
    let response = client.get("https://unstable-api.example.com/data").await?;
    println!("最终响应: {}", response.status);
    
    Ok(())
}
```

## 📈 性能优化

### 连接池优化

```rust
use c10_networks::protocol::http::{HttpClient, HttpConfig};

let config = HttpConfig::new()
    .with_max_connections(200)
    .with_max_connections_per_host(20)
    .with_connection_timeout(Duration::from_secs(30))
    .with_keep_alive(true);

let client = HttpClient::with_config(config);
```

### 并发请求

```rust
use c10_networks::protocol::http::HttpClient;
use futures::future::join_all;

async fn concurrent_requests() -> NetworkResult<()> {
    let client = HttpClient::new();
    
    // 创建多个并发请求
    let urls = vec![
        "https://httpbin.org/get",
        "https://httpbin.org/get",
        "https://httpbin.org/get",
    ];
    
    let futures: Vec<_> = urls.into_iter()
        .map(|url| client.get(url))
        .collect();
    
    let responses = join_all(futures).await;
    
    for response in responses {
        let response = response?;
        println!("响应状态: {}", response.status);
    }
    
    Ok(())
}
```

### 流式处理

```rust
use c10_networks::protocol::http::{HttpClient, HttpRequest, HttpMethod};
use tokio::io::AsyncReadExt;

async fn stream_response() -> NetworkResult<()> {
    let client = HttpClient::new();
    
    let mut request = HttpRequest::new(HttpMethod::GET, "https://httpbin.org/stream/10");
    let mut response = client.send_request_stream(request).await?;
    
    let mut buffer = [0; 1024];
    while let Ok(n) = response.read(&mut buffer).await {
        if n == 0 {
            break;
        }
        print!("{}", String::from_utf8_lossy(&buffer[..n]));
    }
    
    Ok(())
}
```

## 🧪 测试示例

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use c10_networks::protocol::http::HttpClient;
    use tokio_test;

    #[tokio::test]
    async fn test_http_get() {
        let client = HttpClient::new();
        let response = client.get("https://httpbin.org/get").await.unwrap();
        
        assert_eq!(response.status, 200);
        assert!(!response.body.is_empty());
    }

    #[tokio::test]
    async fn test_http_post() {
        let client = HttpClient::new();
        let data = b"{\"test\": \"data\"}";
        let response = client.post("https://httpbin.org/post", data).await.unwrap();
        
        assert_eq!(response.status, 200);
    }

    #[tokio::test]
    async fn test_https_request() {
        let client = HttpClient::new();
        let response = client.get("https://httpbin.org/get").await.unwrap();
        
        assert_eq!(response.status, 200);
        assert!(response.is_secure());
    }
}
```

### 集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use c10_networks::protocol::http::HttpClient;

    #[tokio::test]
    async fn test_http_client_integration() {
        let client = HttpClient::new();
        
        // 测试GET请求
        let get_response = client.get("https://httpbin.org/get").await.unwrap();
        assert_eq!(get_response.status, 200);
        
        // 测试POST请求
        let post_data = b"{\"integration\": \"test\"}";
        let post_response = client.post("https://httpbin.org/post", post_data).await.unwrap();
        assert_eq!(post_response.status, 200);
        
        // 测试PUT请求
        let put_data = b"{\"id\": 1, \"name\": \"test\"}";
        let put_response = client.put("https://httpbin.org/put", put_data).await.unwrap();
        assert_eq!(put_response.status, 200);
    }
}
```

### 性能测试

```rust
#[cfg(test)]
mod performance_tests {
    use super::*;
    use c10_networks::protocol::http::HttpClient;
    use std::time::Instant;

    #[tokio::test]
    async fn test_http_performance() {
        let client = HttpClient::new();
        let start = Instant::now();
        
        // 发送100个并发请求
        let futures: Vec<_> = (0..100)
            .map(|_| client.get("https://httpbin.org/get"))
            .collect();
        
        let responses = futures::future::join_all(futures).await;
        let duration = start.elapsed();
        
        // 验证所有请求都成功
        for response in responses {
            assert!(response.is_ok());
        }
        
        println!("100个并发请求耗时: {:?}", duration);
        assert!(duration.as_secs() < 10); // 应该在10秒内完成
    }
}
```

## ❓ 常见问题

### Q: 如何设置自定义User-Agent？

A: 使用 `HttpConfig::with_user_agent()` 方法或直接在请求头中添加。

### Q: 如何处理重定向？

A: 默认情况下会自动跟随重定向，可以通过 `HttpConfig::with_follow_redirects(false)` 禁用。

### Q: 如何设置请求超时？

A: 使用 `HttpConfig::with_timeout()` 方法设置请求超时时间。

### Q: 如何启用HTTP/2？

A: 使用 `HttpConfig::with_version(HttpVersion::Http2)` 启用HTTP/2支持。

### Q: 如何处理HTTPS证书验证？

A: 使用 `TlsConfig::with_verify_certificates(false)` 禁用证书验证（不推荐），或配置正确的CA证书。

### Q: 如何设置代理？

A: 使用 `HttpConfig::with_proxy_config()` 方法配置HTTP/HTTPS代理。

### Q: 如何实现请求重试？

A: 使用 `HttpConfig::with_retry_config()` 方法配置重试策略。

### Q: 如何优化性能？

A: 启用连接池、使用HTTP/2、合理设置超时时间、使用并发请求。

---

**HTTP客户端指南完成！** 🎉

现在您已经掌握了C10 Networks HTTP客户端的完整用法，可以构建高性能的网络应用程序了。

*最后更新: 2025年1月*  
*文档版本: v1.0*  
*维护者: C10 Networks 开发团队*
