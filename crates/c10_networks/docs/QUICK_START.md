# C10 Networks 快速开始指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](STYLE.md)。

## 📋 目录

- [C10 Networks 快速开始指南](#c10-networks-快速开始指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [⚡ 5分钟快速体验](#-5分钟快速体验)
    - [1. 克隆项目](#1-克隆项目)
    - [2. 运行示例](#2-运行示例)
    - [3. 查看结果](#3-查看结果)
  - [🔧 环境准备](#-环境准备)
    - [系统要求](#系统要求)
    - [Rust环境安装](#rust环境安装)
    - [开发工具推荐](#开发工具推荐)
  - [📦 安装依赖](#-安装依赖)
    - [在您的项目中添加依赖](#在您的项目中添加依赖)
    - [安装项目依赖](#安装项目依赖)
  - [🚀 第一个网络程序](#-第一个网络程序)
  - [🌐 HTTP客户端示例](#-http客户端示例)
    - [基础HTTP请求](#基础http请求)
    - [自定义请求头](#自定义请求头)
  - [🔌 WebSocket通信示例](#-websocket通信示例)
    - [WebSocket服务器](#websocket服务器)
    - [WebSocket客户端](#websocket客户端)
  - [📡 TCP服务器示例](#-tcp服务器示例)
    - [TCP回显服务器](#tcp回显服务器)
    - [TCP客户端](#tcp客户端)
  - [🔍 DNS解析示例](#-dns解析示例)
    - [基础DNS查询](#基础dns查询)
    - [高级DNS查询](#高级dns查询)
  - [📊 性能监控示例](#-性能监控示例)
    - [网络性能监控](#网络性能监控)
  - [🔒 安全通信示例](#-安全通信示例)
    - [HTTPS客户端](#https客户端)
    - [客户端证书认证](#客户端证书认证)
  - [🧪 运行测试](#-运行测试)
    - [运行所有测试](#运行所有测试)
    - [测试覆盖率](#测试覆盖率)
  - [📚 下一步学习](#-下一步学习)
    - [深入学习](#深入学习)
    - [高级特性](#高级特性)
    - [最佳实践](#最佳实践)
  - [❓ 常见问题](#-常见问题)
    - [Q: 如何解决编译错误？](#q-如何解决编译错误)
    - [Q: 网络请求超时怎么办？](#q-网络请求超时怎么办)
    - [Q: 如何启用TLS支持？](#q-如何启用tls支持)
    - [Q: 抓包功能需要什么权限？](#q-抓包功能需要什么权限)
    - [Q: 如何自定义DNS服务器？](#q-如何自定义dns服务器)
    - [Q: 性能基准测试如何运行？](#q-性能基准测试如何运行)

## 🎯 概述

C10 Networks 是一个基于 Rust 1.90 的现代网络编程库，提供了完整的网络编程解决方案。本指南将帮助您在5分钟内快速上手，体验核心功能。

## ⚡ 5分钟快速体验

### 1. 克隆项目

```bash
git clone https://github.com/your-org/rust-lang.git
cd rust-lang/crates/c10_networks
```

### 2. 运行示例

```bash
# HTTP客户端示例
cargo run --example http_client

# WebSocket通信示例（需要两个终端）
cargo run --example ws_echo_server
cargo run --example ws_echo_client

# DNS解析示例
cargo run --example dns_lookup -- example.com
```

### 3. 查看结果

您将看到网络请求的响应、WebSocket消息的传输和DNS解析的结果。

## 🔧 环境准备

### 系统要求

- **Rust**: 1.90+ (推荐使用最新稳定版)
- **操作系统**: Windows 10+, macOS 10.15+, Ubuntu 18.04+
- **内存**: 至少 4GB RAM
- **网络**: 互联网连接（用于下载依赖和测试）

### Rust环境安装

```bash
# 安装Rust（如果尚未安装）
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 验证安装
rustc --version
cargo --version
```

### 开发工具推荐

```bash
# 安装有用的Rust工具
rustup component add rustfmt clippy
cargo install cargo-watch cargo-expand
```

## 📦 安装依赖

### 在您的项目中添加依赖

```toml
# Cargo.toml
[dependencies]
c10_networks = "0.1.0"
tokio = { version = "1.35", features = ["full"] }
```

### 安装项目依赖

```bash
# 在c10_networks目录下
cargo build

# 或者直接运行示例
cargo run --example http_client
```

## 🚀 第一个网络程序

创建一个简单的HTTP客户端：

```rust
// examples/my_first_client.rs
use c10_networks::protocol::http::{HttpClient, HttpMethod, HttpVersion};
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    println!("🚀 启动C10 Networks HTTP客户端...");
    
    // 创建HTTP客户端
    let client = HttpClient::new();
    
    // 发送GET请求
    let response = client.get("https://httpbin.org/get").await?;
    
    println!("✅ 请求成功!");
    println!("状态码: {}", response.status);
    println!("响应头: {:?}", response.headers);
    println!("响应体长度: {} 字节", response.body.len());
    
    Ok(())
}
```

运行示例：

```bash
cargo run --example my_first_client
```

## 🌐 HTTP客户端示例

### 基础HTTP请求

```rust
use c10_networks::protocol::http::{HttpClient, HttpMethod};
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    let client = HttpClient::new();
    
    // GET请求
    let get_response = client.get("https://httpbin.org/get").await?;
    println!("GET响应: {}", String::from_utf8_lossy(&get_response.body));
    
    // POST请求
    let post_data = b"{\"name\": \"C10 Networks\"}";
    let post_response = client.post("https://httpbin.org/post", post_data).await?;
    println!("POST响应: {}", String::from_utf8_lossy(&post_response.body));
    
    Ok(())
}
```

### 自定义请求头

```rust
use c10_networks::protocol::http::{HttpClient, HttpRequest};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    let client = HttpClient::new();
    
    // 创建自定义请求
    let mut request = HttpRequest::new(HttpMethod::GET, "https://httpbin.org/headers");
    request.add_header("User-Agent", "C10-Networks/1.0");
    request.add_header("Accept", "application/json");
    
    let response = client.send_request(request).await?;
    println!("自定义请求响应: {}", String::from_utf8_lossy(&response.body));
    
    Ok(())
}
```

## 🔌 WebSocket通信示例

### WebSocket服务器

```rust
// examples/websocket_server.rs
use c10_networks::protocol::websocket::{WebSocketServer, WebSocketMessage};
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    println!("🔌 启动WebSocket服务器...");
    
    let server = WebSocketServer::new("127.0.0.1:8080").await?;
    println!("✅ 服务器启动在 ws://127.0.0.1:8080");
    
    loop {
        let (mut connection, addr) = server.accept().await?;
        println!("📡 新连接来自: {}", addr);
        
        tokio::spawn(async move {
            while let Some(message) = connection.receive().await? {
                match message {
                    WebSocketMessage::Text(text) => {
                        println!("📨 收到文本消息: {}", text);
                        // 回显消息
                        connection.send_text(format!("Echo: {}", text)).await?;
                    }
                    WebSocketMessage::Binary(data) => {
                        println!("📦 收到二进制消息: {} 字节", data.len());
                        // 回显二进制数据
                        connection.send_binary(data).await?;
                    }
                    WebSocketMessage::Close => {
                        println!("🔚 连接关闭");
                        break;
                    }
                    _ => {}
                }
            }
            Ok::<(), NetworkError>(())
        });
    }
}
```

### WebSocket客户端

```rust
// examples/websocket_client.rs
use c10_networks::protocol::websocket::{WebSocketClient, WebSocketMessage};
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    println!("🔌 连接WebSocket服务器...");
    
    let mut client = WebSocketClient::connect("ws://127.0.0.1:8080").await?;
    println!("✅ 连接成功!");
    
    // 发送文本消息
    client.send_text("Hello, C10 Networks!").await?;
    
    // 发送二进制消息
    let binary_data = b"Binary message from C10 Networks";
    client.send_binary(binary_data.to_vec()).await?;
    
    // 接收响应
    for _ in 0..2 {
        if let Some(message) = client.receive().await? {
            match message {
                WebSocketMessage::Text(text) => {
                    println!("📨 收到响应: {}", text);
                }
                WebSocketMessage::Binary(data) => {
                    println!("📦 收到二进制响应: {} 字节", data.len());
                }
                _ => {}
            }
        }
    }
    
    // 关闭连接
    client.close().await?;
    println!("🔚 连接已关闭");
    
    Ok(())
}
```

运行WebSocket示例：

```bash
# 终端1: 启动服务器
cargo run --example websocket_server

# 终端2: 启动客户端
cargo run --example websocket_client
```

## 📡 TCP服务器示例

### TCP回显服务器

```rust
// examples/tcp_echo_server.rs
use c10_networks::socket::tcp::TcpServer;
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    println!("📡 启动TCP回显服务器...");
    
    let server = TcpServer::bind("127.0.0.1:8080").await?;
    println!("✅ 服务器启动在 tcp://127.0.0.1:8080");
    
    loop {
        let (mut stream, addr) = server.accept().await?;
        println!("📡 新连接来自: {}", addr);
        
        tokio::spawn(async move {
            let mut buffer = [0; 1024];
            
            loop {
                match stream.read(&mut buffer).await {
                    Ok(0) => {
                        println!("🔚 连接关闭: {}", addr);
                        break;
                    }
                    Ok(n) => {
                        let data = &buffer[..n];
                        println!("📨 收到数据: {} 字节", n);
                        
                        // 回显数据
                        if let Err(e) = stream.write_all(data).await {
                            eprintln!("❌ 写入错误: {}", e);
                            break;
                        }
                    }
                    Err(e) => {
                        eprintln!("❌ 读取错误: {}", e);
                        break;
                    }
                }
            }
        });
    }
}
```

### TCP客户端

```rust
// examples/tcp_client.rs
use c10_networks::socket::tcp::TcpClient;
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    println!("📡 连接TCP服务器...");
    
    let mut client = TcpClient::connect("127.0.0.1:8080").await?;
    println!("✅ 连接成功!");
    
    // 发送测试数据
    let test_data = b"Hello, C10 Networks TCP!";
    client.write_all(test_data).await?;
    println!("📤 发送数据: {} 字节", test_data.len());
    
    // 接收回显数据
    let mut buffer = [0; 1024];
    let n = client.read(&mut buffer).await?;
    let response = &buffer[..n];
    
    println!("📨 收到回显: {}", String::from_utf8_lossy(response));
    
    Ok(())
}
```

运行TCP示例：

```bash
# 终端1: 启动服务器
cargo run --example tcp_echo_server

# 终端2: 启动客户端
cargo run --example tcp_client
```

## 🔍 DNS解析示例

### 基础DNS查询

```rust
// examples/dns_basic.rs
use c10_networks::protocol::dns::{DnsResolver, presets};
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    println!("🔍 开始DNS解析...");
    
    // 使用系统DNS配置
    let resolver = DnsResolver::from_system().await?;
    
    // 查询A记录
    let ips = resolver.lookup_ips("example.com").await?;
    println!("✅ example.com 的IP地址: {:?}", ips);
    
    // 查询TXT记录
    let txt_records = resolver.lookup_txt("example.com").await?;
    println!("📝 TXT记录: {:?}", txt_records);
    
    // 使用Cloudflare DoH
    let (cfg, opts) = presets::cloudflare_doh();
    let doh_resolver = DnsResolver::from_config(cfg, opts).await?;
    
    let doh_ips = doh_resolver.lookup_ips("google.com").await?;
    println!("🌐 Google.com (DoH): {:?}", doh_ips);
    
    Ok(())
}
```

### 高级DNS查询

```rust
// examples/dns_advanced.rs
use c10_networks::protocol::dns::DnsResolver;
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    let resolver = DnsResolver::from_system().await?;
    
    // 查询MX记录
    let mx_records = resolver.lookup_mx("example.com").await?;
    println!("📧 MX记录: {:?}", mx_records);
    
    // 查询SRV记录
    let srv_records = resolver.lookup_srv("_http._tcp.example.com").await?;
    println!("🔗 SRV记录: {:?}", srv_records);
    
    // 反向DNS查询
    let ptr_records = resolver.reverse_lookup("8.8.8.8".parse()?).await?;
    println!("🔄 反向DNS: {:?}", ptr_records);
    
    Ok(())
}
```

运行DNS示例：

```bash
cargo run --example dns_basic
cargo run --example dns_advanced
```

## 📊 性能监控示例

### 网络性能监控

```rust
// examples/performance_monitor.rs
use c10_networks::performance::metrics::NetworkMetrics;
use c10_networks::diagnostics::NetDiagnostics;
use c10_networks::error::NetworkResult;
use std::time::Duration;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    println!("📊 启动网络性能监控...");
    
    let mut metrics = NetworkMetrics::new();
    let diagnostics = NetDiagnostics::new();
    
    // 监控HTTP请求性能
    let start = std::time::Instant::now();
    let client = c10_networks::protocol::http::HttpClient::new();
    let response = client.get("https://httpbin.org/get").await?;
    let duration = start.elapsed();
    
    // 记录指标
    metrics.record_http_request(duration, response.status);
    metrics.record_bandwidth(response.body.len() as u64, duration);
    
    // 显示性能指标
    println!("✅ 请求完成:");
    println!("   响应时间: {:?}", duration);
    println!("   状态码: {}", response.status);
    println!("   数据大小: {} 字节", response.body.len());
    println!("   吞吐量: {:.2} KB/s", 
        (response.body.len() as f64 / 1024.0) / duration.as_secs_f64());
    
    // 网络诊断
    println!("\n🔍 网络诊断:");
    let dns_ok = diagnostics.check_dns("example.com");
    println!("   DNS解析: {}", if dns_ok { "✅ 正常" } else { "❌ 异常" });
    
    let tcp_ok = diagnostics.check_tcp_connect("127.0.0.1:80", 1000);
    println!("   TCP连接: {:?}", tcp_ok);
    
    Ok(())
}
```

运行性能监控示例：

```bash
cargo run --example performance_monitor
```

## 🔒 安全通信示例

### HTTPS客户端

```rust
// examples/https_client.rs
use c10_networks::protocol::http::{HttpClient, HttpConfig};
use c10_networks::security::tls_reload::TlsConfig;
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    println!("🔒 启动HTTPS客户端...");
    
    // 配置TLS
    let tls_config = TlsConfig::default()
        .with_verify_certificates(true)
        .with_verify_hostname(true);
    
    // 创建安全的HTTP客户端
    let http_config = HttpConfig::new()
        .with_tls_config(tls_config)
        .with_timeout(Duration::from_secs(30));
    
    let client = HttpClient::with_config(http_config);
    
    // 发送HTTPS请求
    let response = client.get("https://httpbin.org/get").await?;
    
    println!("✅ HTTPS请求成功!");
    println!("   状态码: {}", response.status);
    println!("   安全连接: {}", response.is_secure());
    
    Ok(())
}
```

### 客户端证书认证

```rust
// examples/client_cert_auth.rs
use c10_networks::security::tls_reload::TlsConfig;
use c10_networks::protocol::http::{HttpClient, HttpConfig};
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    println!("🔐 配置客户端证书认证...");
    
    // 加载客户端证书
    let tls_config = TlsConfig::default()
        .with_client_certificate("client.crt", "client.key")
        .with_ca_certificate("ca.crt");
    
    let http_config = HttpConfig::new()
        .with_tls_config(tls_config);
    
    let client = HttpClient::with_config(http_config);
    
    // 使用客户端证书进行认证
    let response = client.get("https://secure.example.com/api").await?;
    
    println!("✅ 客户端证书认证成功!");
    println!("   状态码: {}", response.status);
    
    Ok(())
}
```

运行安全通信示例：

```bash
cargo run --example https_client
cargo run --example client_cert_auth
```

## 🧪 运行测试

### 运行所有测试

```bash
# 运行单元测试
cargo test

# 运行集成测试
cargo test --test integration

# 运行性能测试
cargo bench

# 运行特定测试
cargo test http_client
cargo test websocket
cargo test dns_resolver
```

### 测试覆盖率

```bash
# 安装tarpaulin
cargo install cargo-tarpaulin

# 运行覆盖率测试
cargo tarpaulin --out html

# 查看覆盖率报告
open tarpaulin-report.html
```

## 📚 下一步学习

### 深入学习

1. [HTTP客户端指南](HTTP_CLIENT_GUIDE.md) - 深入了解HTTP协议实现
2. [WebSocket通信指南](WEBSOCKET_GUIDE.md) - 掌握实时通信技术
3. [TCP/UDP套接字指南](SOCKET_GUIDE.md) - 学习底层网络编程
4. [DNS解析指南](DNS_RESOLVER_GUIDE.md) - 掌握域名解析技术

### 高级特性

1. [P2P网络指南](P2P_GUIDE.md) - 构建P2P应用程序
2. [抓包分析指南](PACKET_CAPTURE_GUIDE.md) - 网络流量分析
3. [性能优化指南](PERFORMANCE_OPTIMIZATION.md) - 提升应用性能
4. [安全实践指南](SECURITY_GUIDE.md) - 保障通信安全

### 最佳实践

1. [代码规范](CODE_STYLE.md) - 编写高质量代码
2. [测试策略](TESTING_STRATEGY.md) - 全面的测试方法
3. [部署指南](DEPLOYMENT_GUIDE.md) - 生产环境部署
4. [故障排查](TROUBLESHOOTING.md) - 问题诊断和解决

## ❓ 常见问题

### Q: 如何解决编译错误？

A: 确保使用Rust 1.90+版本，并运行 `cargo update` 更新依赖。

### Q: 网络请求超时怎么办？

A: 检查网络连接，或增加超时时间配置。

### Q: 如何启用TLS支持？

A: 在Cargo.toml中添加 `tls` 特性：`c10_networks = { version = "0.1.0", features = ["tls"] }`

### Q: 抓包功能需要什么权限？

A: Windows需要管理员权限，Linux需要root权限或CAP_NET_RAW能力。

### Q: 如何自定义DNS服务器？

A: 使用 `DnsResolver::from_config()` 方法配置自定义DNS服务器。

### Q: 性能基准测试如何运行？

A: 运行 `cargo bench` 或查看 [基准测试指南](benchmark_minimal_guide.md)。

---

**快速开始完成！** 🎉

现在您已经掌握了C10 Networks的基本用法，可以开始构建您的网络应用程序了。

*最后更新: 2025年1月*  
*文档版本: v1.0*  
*维护者: C10 Networks 开发团队*
