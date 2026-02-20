# 网络编程快速参考卡片

**模块**: C10 Networks
**创建日期**: 2026-01-27
**最后更新**: 2026-01-27
**Rust 版本**: 1.93.0+ (Edition 2024)
**状态**: ✅ 已完成

---

## 📋 目录

- [网络编程快速参考卡片](#网络编程快速参考卡片)
  - [📋 目录](#-目录)
  - [🚀 快速开始](#-快速开始)
    - [HTTP 客户端](#http-客户端)
    - [TCP 服务器](#tcp-服务器)
  - [📋 常用 API](#-常用-api)
    - [HTTP 客户端](#http-客户端-1)
    - [TCP/UDP](#tcpudp)
    - [WebSocket](#websocket)
    - [DNS 解析](#dns-解析)
  - [🔧 配置选项](#-配置选项)
    - [HTTP 客户端配置](#http-客户端配置)
    - [TCP 服务器配置](#tcp-服务器配置)
  - [⚡ 异步模式](#-异步模式)
    - [并发处理多个请求](#并发处理多个请求)
    - [流式处理](#流式处理)
  - [🐛 错误处理](#-错误处理)
  - [🔒 安全特性](#-安全特性)
    - [HTTPS/TLS](#httpstls)
    - [认证](#认证)
  - [📊 性能优化](#-性能优化)
    - [连接池](#连接池)
    - [压缩](#压缩)
  - [🚫 反例速查](#-反例速查)
    - [反例 1: 忽略连接错误](#反例-1-忽略连接错误)
    - [反例 2: 未设置超时导致无限阻塞](#反例-2-未设置超时导致无限阻塞)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码](#-相关示例代码)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [相关速查卡](#相关速查卡)

---

## 🚀 快速开始

### HTTP 客户端

```rust
use c10_networks::prelude::*;

// 创建 HTTP 客户端
let client = HttpClient::new()?;

// GET 请求
let response = client.get("https://api.example.com/data").await?;
println!("Status: {}", response.status());
println!("Body: {}", response.text().await?);

// POST 请求
let response = client
    .post("https://api.example.com/data")
    .json(&json!({"key": "value"}))
    .send()
    .await?;
```

### TCP 服务器

```rust
use c10_networks::tcp::TcpListener;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

let listener = TcpListener::bind("127.0.0.1:8080").await?;

loop {
    let (mut socket, _) = listener.accept().await?;

    tokio::spawn(async move {
        let mut buf = [0; 1024];
        match socket.read(&mut buf).await {
            Ok(n) => {
                if n == 0 {
                    return;
                }
                socket.write_all(&buf[0..n]).await.unwrap();
            }
            Err(e) => eprintln!("Error: {}", e),
        }
    });
}
```

---

## 📋 常用 API

### HTTP 客户端

| 操作      | 方法                  | 说明             |
| :--- | :--- | :--- || GET       | `get(url)`            | 发送 GET 请求    |
| POST      | `post(url)`           | 发送 POST 请求   |
| PUT       | `put(url)`            | 发送 PUT 请求    |
| DELETE    | `delete(url)`         | 发送 DELETE 请求 |
| 设置头部  | `.header(key, value)` | 设置请求头       |
| JSON 数据 | `.json(data)`         | 发送 JSON 数据   |
| 表单数据  | `.form(data)`         | 发送表单数据     |

### TCP/UDP

| 操作 | TCP                    | UDP                    |
| :--- | :--- | :--- || 监听 | `TcpListener::bind()`  | `UdpSocket::bind()`    |
| 连接 | `TcpStream::connect()` | `UdpSocket::connect()` |
| 接收 | `recv()`               | `recv_from()`          |
| 发送 | `send()`               | `send_to()`            |

### WebSocket

```rust
use c10_networks::websocket::WebSocket;

// 客户端连接
let mut ws = WebSocket::connect("ws://localhost:8080").await?;

// 发送消息
ws.send(Message::Text("Hello".to_string())).await?;

// 接收消息
if let Some(msg) = ws.recv().await? {
    match msg {
        Message::Text(text) => println!("Received: {}", text),
        Message::Binary(data) => println!("Received {} bytes", data.len()),
        _ => {}
    }
}
```

### DNS 解析

```rust
use c10_networks::dns::DnsResolver;

let resolver = DnsResolver::from_system().await?;

// A 记录查询
let ips = resolver.lookup_ipv4("example.com").await?;
for ip in ips {
    println!("IPv4: {}", ip);
}

// AAAA 记录查询
let ips = resolver.lookup_ipv6("example.com").await?;
for ip in ips {
    println!("IPv6: {}", ip);
}
```

---

## 🔧 配置选项

### HTTP 客户端配置

```rust
let client = HttpClient::builder()
    .timeout(Duration::from_secs(30))
    .connect_timeout(Duration::from_secs(10))
    .user_agent("MyApp/1.0")
    .build()?;
```

### TCP 服务器配置

```rust
let listener = TcpListener::bind("127.0.0.1:8080")
    .with_nodelay(true)  // 禁用 Nagle 算法
    .with_keepalive(Duration::from_secs(60))
    .await?;
```

---

## ⚡ 异步模式

### 并发处理多个请求

```rust
use futures::future;

let urls = vec![
    "https://api1.example.com",
    "https://api2.example.com",
    "https://api3.example.com",
];

let futures = urls.into_iter().map(|url| {
    client.get(url)
});

let results = future::join_all(futures).await;
```

### 流式处理

```rust
use futures::StreamExt;

let mut stream = client.get_stream("https://api.example.com/stream").await?;

while let Some(chunk) = stream.next().await {
    let chunk = chunk?;
    println!("Received chunk: {} bytes", chunk.len());
}
```

---

## 🐛 错误处理

```rust
use c10_networks::error::NetworkError;

match client.get(url).await {
    Ok(response) => {
        if response.status().is_success() {
            println!("Success: {}", response.text().await?);
        } else {
            println!("Error status: {}", response.status());
        }
    }
    Err(NetworkError::Timeout) => println!("Request timeout"),
    Err(NetworkError::ConnectionError(e)) => println!("Connection error: {}", e),
    Err(e) => println!("Other error: {}", e),
}
```

---

## 🔒 安全特性

### HTTPS/TLS

```rust
let client = HttpClient::builder()
    .tls_config(TlsConfig::default())
    .danger_accept_invalid_certs(false)  // 生产环境设为 false
    .build()?;
```

### 认证

```rust
// Basic 认证
let response = client
    .get(url)
    .basic_auth("username", Some("password"))
    .send()
    .await?;

// Bearer Token
let response = client
    .get(url)
    .bearer_auth("token")
    .send()
    .await?;
```

---

## 📊 性能优化

### 连接池

```rust
let client = HttpClient::builder()
    .pool_max_idle_per_host(10)
    .pool_idle_timeout(Duration::from_secs(90))
    .build()?;
```

### 压缩

```rust
let response = client
    .get(url)
    .header("Accept-Encoding", "gzip, deflate")
    .send()
    .await?;
```

---

## 🚫 反例速查

### 反例 1: 忽略连接错误

**错误示例**:

```rust
let stream = TcpStream::connect("127.0.0.1:8080").unwrap();  // ❌ 失败即 panic
```

**原因**: 网络不可靠，应处理连接失败。

**修正**:

```rust
let stream = TcpStream::connect("127.0.0.1:8080")?;
```

---

### 反例 2: 未设置超时导致无限阻塞

**错误示例**:

```rust
let mut buf = [0u8; 1024];
stream.read(&mut buf);  // ❌ 可能永久阻塞
```

**原因**: 对方不响应时 read 会一直等待。

**修正**: 使用 `set_read_timeout` 或 `tokio::time::timeout`。

---

## 📚 相关文档

- [网络模块完整文档](../../../crates/c10_networks/docs/)
- [网络模块 README](../../../crates/c10_networks/README.md)

## 🧩 相关示例代码

以下示例位于 `crates/c10_networks/examples/`，可直接运行（例如：`cargo run -p c10_networks --example tcp_echo_server`）。

- [TCP 回显服务/客户端](../../../crates/c10_networks/examples/tcp_echo_server.rs)、[tcp_client.rs](../../../crates/c10_networks/examples/tcp_client.rs)
- [UDP 回显与自定义](../../../crates/c10_networks/examples/udp_echo.rs)、[udp_custom_demo.rs](../../../crates/c10_networks/examples/udp_custom_demo.rs)
- [HTTP 客户端](../../../crates/c10_networks/examples/http_client.rs)
- [WebSocket 演示与回显](../../../crates/c10_networks/examples/websocket_demo.rs)、[ws_echo_server.rs](../../../crates/c10_networks/examples/ws_echo_server.rs)、[ws_echo_client.rs](../../../crates/c10_networks/examples/ws_echo_client.rs)
- [DNS 解析与记录](../../../crates/c10_networks/examples/dns_lookup.rs)、[dns_records.rs](../../../crates/c10_networks/examples/dns_records.rs)、[unified_dns.rs](../../../crates/c10_networks/examples/unified_dns.rs)
- [gRPC 客户端/服务端](../../../crates/c10_networks/examples/grpc_client.rs)、[grpc_server.rs](../../../crates/c10_networks/examples/grpc_server.rs)

---

## 📚 相关资源

### 官方文档

- [std::net 文档](https://doc.rust-lang.org/std/net/)
- [Tokio 网络文档](https://tokio.rs/)

### 项目内部文档

- [完整文档](../../../crates/c10_networks/README.md)
- [HTTP 指南](../../../crates/c10_networks/docs/tier_02_guides/02_HTTP客户端开发.md)
- [TCP/UDP 指南](../../../crates/c10_networks/docs/tier_02_guides/04_TCP_UDP编程.md)
- [WebSocket 指南](../../../crates/c10_networks/docs/tier_02_guides/03_WebSocket实时通信.md)

### 相关速查卡

- [异步编程速查卡](./async_patterns.md) - 异步网络编程
- [错误处理速查卡](./error_handling_cheatsheet.md) - 网络错误处理
- [线程与并发速查卡](./threads_concurrency_cheatsheet.md) - 并发网络编程

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.0+ (Edition 2024)
**提示**: 使用 `cargo doc --open` 查看完整 API 文档
