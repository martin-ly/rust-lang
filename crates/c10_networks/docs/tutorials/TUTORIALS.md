# c10_networks 教程和最佳实践指南

## 目录

- [c10\_networks 教程和最佳实践指南](#c10_networks-教程和最佳实践指南)
  - [目录](#目录)
  - [快速开始](#快速开始)
    - [安装依赖](#安装依赖)
    - [第一个网络程序](#第一个网络程序)
  - [基础教程](#基础教程)
    - [TCP 客户端/服务器](#tcp-客户端服务器)
      - [创建 TCP 服务器](#创建-tcp-服务器)
      - [创建 TCP 客户端](#创建-tcp-客户端)
    - [UDP 通信](#udp-通信)
      - [UDP 服务器](#udp-服务器)
      - [UDP 客户端](#udp-客户端)
    - [HTTP 客户端](#http-客户端)
      - [基本 HTTP 请求](#基本-http-请求)
      - [带认证的 HTTP 请求](#带认证的-http-请求)
    - [WebSocket 连接](#websocket-连接)
      - [WebSocket 客户端](#websocket-客户端)
  - [高级教程](#高级教程)
    - [异步网络编程](#异步网络编程)
      - [使用 Tokio 运行时](#使用-tokio-运行时)
      - [连接池管理](#连接池管理)
    - [错误处理](#错误处理)
      - [自定义错误类型](#自定义错误类型)
      - [错误恢复策略](#错误恢复策略)
    - [性能优化](#性能优化)
      - [零拷贝优化](#零拷贝优化)
      - [内存池使用](#内存池使用)
    - [安全配置](#安全配置)
      - [TLS 配置](#tls-配置)
      - [认证和授权](#认证和授权)
  - [最佳实践](#最佳实践)
    - [代码组织](#代码组织)
      - [模块化设计](#模块化设计)
      - [配置管理](#配置管理)
    - [资源管理](#资源管理)
      - [连接生命周期管理](#连接生命周期管理)
      - [内存管理](#内存管理)
    - [测试策略](#测试策略)
      - [单元测试](#单元测试)
      - [集成测试](#集成测试)
    - [部署指南](#部署指南)
      - [Docker 部署](#docker-部署)
      - [Kubernetes 部署](#kubernetes-部署)
  - [常见问题](#常见问题)
    - [Q: 如何处理网络连接超时？](#q-如何处理网络连接超时)
    - [Q: 如何优化大量并发连接的性能？](#q-如何优化大量并发连接的性能)
    - [Q: 如何实现自定义协议？](#q-如何实现自定义协议)
  - [进阶主题](#进阶主题)
    - [自定义协议](#自定义协议)
      - [实现自定义协议栈](#实现自定义协议栈)
    - [网络监控](#网络监控)
      - [实现网络监控](#实现网络监控)
    - [负载均衡](#负载均衡)
      - [实现简单的负载均衡](#实现简单的负载均衡)
    - [故障恢复](#故障恢复)
      - [实现故障恢复机制](#实现故障恢复机制)

## 快速开始

### 安装依赖

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
c10_networks = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
bytes = "1.0"
```

### 第一个网络程序

```rust
use c10_networks::protocol::tcp::TcpClient;
use std::io::{self, Write};

#[tokio::main]
async fn main() -> io::Result<()> {
    // 连接到服务器
    let mut client = TcpClient::new("127.0.0.1:8080").await?;

    // 发送数据
    client.write_all(b"Hello, Server!").await?;

    // 读取响应
    let mut buffer = [0; 1024];
    let n = client.read(&mut buffer).await?;

    println!("收到响应: {}", String::from_utf8_lossy(&buffer[..n]));

    Ok(())
}
```

## 基础教程

### TCP 客户端/服务器

#### 创建 TCP 服务器

```rust
use c10_networks::protocol::tcp::TcpServer;
use std::io;

#[tokio::main]
async fn main() -> io::Result<()> {
    let server = TcpServer::new("127.0.0.1:8080").await?;

    println!("服务器启动在 127.0.0.1:8080");

    loop {
        let mut client = server.accept().await?;

        tokio::spawn(async move {
            let mut buffer = [0; 1024];

            loop {
                match client.read(&mut buffer).await {
                    Ok(0) => break, // 连接关闭
                    Ok(n) => {
                        // 回显数据
                        if let Err(e) = client.write_all(&buffer[..n]).await {
                            eprintln!("写入错误: {}", e);
                            break;
                        }
                    }
                    Err(e) => {
                        eprintln!("读取错误: {}", e);
                        break;
                    }
                }
            }
        });
    }
}
```

#### 创建 TCP 客户端

```rust
use c10_networks::protocol::tcp::TcpClient;
use std::io::{self, Write};

#[tokio::main]
async fn main() -> io::Result<()> {
    let mut client = TcpClient::new("127.0.0.1:8080").await?;

    // 发送多条消息
    for i in 0..5 {
        let message = format!("消息 {}: Hello, Server!", i);
        client.write_all(message.as_bytes()).await?;

        // 读取响应
        let mut buffer = [0; 1024];
        let n = client.read(&mut buffer).await?;
        println!("响应: {}", String::from_utf8_lossy(&buffer[..n]));

        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    }

    Ok(())
}
```

### UDP 通信

#### UDP 服务器

```rust
use c10_networks::protocol::udp::UdpSocket;
use std::net::SocketAddr;

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let socket = UdpSocket::bind("127.0.0.1:8080").await?;
    println!("UDP 服务器启动在 127.0.0.1:8080");

    let mut buffer = [0; 1024];

    loop {
        let (n, addr) = socket.recv_from(&mut buffer).await?;
        let message = String::from_utf8_lossy(&buffer[..n]);
        println!("收到来自 {} 的消息: {}", addr, message);

        // 发送响应
        let response = format!("收到: {}", message);
        socket.send_to(response.as_bytes(), addr).await?;
    }
}
```

#### UDP 客户端

```rust
use c10_networks::protocol::udp::UdpSocket;
use std::net::SocketAddr;

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let socket = UdpSocket::bind("127.0.0.1:0").await?; // 任意端口
    let server_addr: SocketAddr = "127.0.0.1:8080".parse().unwrap();

    // 发送消息
    let message = "Hello, UDP Server!";
    socket.send_to(message.as_bytes(), server_addr).await?;

    // 接收响应
    let mut buffer = [0; 1024];
    let (n, _) = socket.recv_from(&mut buffer).await?;
    println!("响应: {}", String::from_utf8_lossy(&buffer[..n]));

    Ok(())
}
```

### HTTP 客户端

#### 基本 HTTP 请求

```rust
use c10_networks::protocol::http::{HttpClient, HttpMethod, HttpVersion};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = HttpClient::new();

    // GET 请求
    let response = client
        .request(HttpMethod::GET, "https://httpbin.org/get")
        .version(HttpVersion::Http1_1)
        .send()
        .await?;

    println!("状态码: {}", response.status_code());
    println!("响应头: {:?}", response.headers());
    println!("响应体: {}", response.body());

    // POST 请求
    let mut headers = HashMap::new();
    headers.insert("Content-Type".to_string(), "application/json".to_string());

    let response = client
        .request(HttpMethod::POST, "https://httpbin.org/post")
        .version(HttpVersion::Http1_1)
        .headers(headers)
        .body(r#"{"message": "Hello, World!"}"#)
        .send()
        .await?;

    println!("POST 响应: {}", response.body());

    Ok(())
}
```

#### 带认证的 HTTP 请求

```rust
use c10_networks::protocol::http::{HttpClient, HttpMethod, HttpVersion};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = HttpClient::new();

    let mut headers = HashMap::new();
    headers.insert("Authorization".to_string(), "Bearer your-token-here".to_string());
    headers.insert("Content-Type".to_string(), "application/json".to_string());

    let response = client
        .request(HttpMethod::GET, "https://api.example.com/protected")
        .version(HttpVersion::Http1_1)
        .headers(headers)
        .send()
        .await?;

    println!("受保护资源响应: {}", response.body());

    Ok(())
}
```

### WebSocket 连接

#### WebSocket 客户端

```rust
use c10_networks::protocol::websocket::{WebSocketClient, WebSocketFrame, WebSocketOpcode};
use bytes::Bytes;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = WebSocketClient::connect("ws://127.0.0.1:8080").await?;

    println!("WebSocket 连接已建立");

    // 发送文本消息
    let text_frame = WebSocketFrame {
        fin: true,
        opcode: WebSocketOpcode::Text,
        mask: true,
        payload_length: 13,
        masking_key: Some([0x12, 0x34, 0x56, 0x78]),
        payload: Bytes::from("Hello, WebSocket!"),
    };

    client.send_frame(text_frame).await?;

    // 发送二进制消息
    let binary_frame = WebSocketFrame {
        fin: true,
        opcode: WebSocketOpcode::Binary,
        mask: true,
        payload_length: 4,
        masking_key: Some([0x12, 0x34, 0x56, 0x78]),
        payload: Bytes::from(vec![0x01, 0x02, 0x03, 0x04]),
    };

    client.send_frame(binary_frame).await?;

    // 接收消息
    loop {
        match client.receive_frame().await? {
            Some(frame) => {
                match frame.opcode {
                    WebSocketOpcode::Text => {
                        println!("收到文本消息: {}", String::from_utf8_lossy(&frame.payload));
                    }
                    WebSocketOpcode::Binary => {
                        println!("收到二进制消息: {:?}", frame.payload);
                    }
                    WebSocketOpcode::Close => {
                        println!("连接关闭");
                        break;
                    }
                    WebSocketOpcode::Ping => {
                        // 自动回复 Pong
                        let pong_frame = WebSocketFrame {
                            fin: true,
                            opcode: WebSocketOpcode::Pong,
                            mask: true,
                            payload_length: frame.payload_length,
                            masking_key: frame.masking_key,
                            payload: frame.payload,
                        };
                        client.send_frame(pong_frame).await?;
                    }
                    _ => {}
                }
            }
            None => break,
        }
    }

    Ok(())
}
```

## 高级教程

### 异步网络编程

#### 使用 Tokio 运行时

```rust
use c10_networks::protocol::tcp::TcpServer;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::sync::Arc;

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let server = Arc::new(TcpServer::new("127.0.0.1:8080").await?);

    println!("服务器启动在 127.0.0.1:8080");

    loop {
        let server_clone = Arc::clone(&server);
        let mut client = server_clone.accept().await?;

        tokio::spawn(async move {
            let mut buffer = [0; 1024];

            loop {
                match client.read(&mut buffer).await {
                    Ok(0) => break,
                    Ok(n) => {
                        // 处理请求
                        let request = String::from_utf8_lossy(&buffer[..n]);
                        let response = process_request(&request);

                        if let Err(e) = client.write_all(response.as_bytes()).await {
                            eprintln!("写入错误: {}", e);
                            break;
                        }
                    }
                    Err(e) => {
                        eprintln!("读取错误: {}", e);
                        break;
                    }
                }
            }
        });
    }
}

fn process_request(request: &str) -> String {
    // 简单的请求处理逻辑
    match request.trim() {
        "ping" => "pong".to_string(),
        "time" => format!("当前时间: {}", chrono::Utc::now()),
        _ => "未知命令".to_string(),
    }
}
```

#### 连接池管理

```rust
use c10_networks::protocol::tcp::TcpClient;
use std::sync::Arc;
use tokio::sync::Semaphore;

struct ConnectionPool {
    clients: Vec<Arc<TcpClient>>,
    semaphore: Arc<Semaphore>,
}

impl ConnectionPool {
    async fn new(addr: &str, max_connections: usize) -> std::io::Result<Self> {
        let mut clients = Vec::new();

        for _ in 0..max_connections {
            let client = Arc::new(TcpClient::new(addr).await?);
            clients.push(client);
        }

        Ok(Self {
            clients,
            semaphore: Arc::new(Semaphore::new(max_connections)),
        })
    }

    async fn get_connection(&self) -> Arc<TcpClient> {
        let _permit = self.semaphore.acquire().await.unwrap();
        // 简单的轮询选择连接
        self.clients[0].clone()
    }
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let pool = ConnectionPool::new("127.0.0.1:8080", 10).await?;

    // 使用连接池
    let client = pool.get_connection().await;
    client.write_all(b"Hello from pool!").await?;

    Ok(())
}
```

### 错误处理

#### 自定义错误类型

```rust
use c10_networks::error::{NetworkError, ErrorRecovery};
use std::time::Duration;

#[derive(Debug)]
enum CustomError {
    Network(NetworkError),
    Validation(String),
    Timeout,
}

impl From<NetworkError> for CustomError {
    fn from(error: NetworkError) -> Self {
        CustomError::Network(error)
    }
}

impl std::fmt::Display for CustomError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CustomError::Network(e) => write!(f, "网络错误: {}", e),
            CustomError::Validation(msg) => write!(f, "验证错误: {}", msg),
            CustomError::Timeout => write!(f, "超时错误"),
        }
    }
}

impl std::error::Error for CustomError {}

async fn handle_network_operation() -> Result<(), CustomError> {
    // 模拟网络操作
    let result: Result<(), NetworkError> = Err(NetworkError::Timeout(Duration::from_secs(5)));

    match result {
        Ok(_) => Ok(()),
        Err(e) => {
            if e.is_retryable() {
                println!("错误可重试，延迟: {:?}", e.retry_delay());
                // 实现重试逻辑
                Err(CustomError::Network(e))
            } else {
                Err(CustomError::Network(e))
            }
        }
    }
}
```

#### 错误恢复策略

```rust
use c10_networks::error::{NetworkError, ErrorRecovery};
use std::time::Duration;
use tokio::time::sleep;

async fn retry_with_backoff<F, T>(mut operation: F, max_retries: u32) -> Result<T, NetworkError>
where
    F: FnMut() -> Result<T, NetworkError>,
{
    let mut retries = 0;

    loop {
        match operation() {
            Ok(result) => return Ok(result),
            Err(e) => {
                if !e.is_retryable() || retries >= max_retries {
                    return Err(e);
                }

                retries += 1;
                let delay = e.retry_delay();
                println!("重试 {} 次，延迟: {:?}", retries, delay);
                sleep(delay).await;
            }
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let result = retry_with_backoff(|| {
        // 模拟可能失败的操作
        if rand::random::<f32>() < 0.7 {
            Err(NetworkError::Timeout(Duration::from_secs(1)))
        } else {
            Ok("成功!".to_string())
        }
    }, 3).await;

    match result {
        Ok(msg) => println!("操作成功: {}", msg),
        Err(e) => println!("操作失败: {}", e),
    }

    Ok(())
}
```

### 性能优化

#### 零拷贝优化

```rust
use c10_networks::packet::{Packet, PacketBuilder, PacketType};
use bytes::Bytes;

fn create_packet_zero_copy() -> Packet {
    // 使用 Bytes 避免数据拷贝
    let data = Bytes::from_static(b"Hello, World!");

    Packet::new(PacketType::Raw, data)
}

fn build_packet_efficiently() -> Packet {
    let mut builder = PacketBuilder::new(PacketType::Custom("test".to_string()));

    // 链式调用减少中间分配
    builder
        .add_data(b"header")
        .add_data(b"body")
        .sequence_number(1)
        .flags(0x01)
        .build()
}
```

#### 内存池使用

```rust
use c10_networks::performance::memory_pool::MemoryPool;
use std::sync::Arc;

struct OptimizedServer {
    memory_pool: Arc<MemoryPool>,
}

impl OptimizedServer {
    fn new() -> Self {
        Self {
            memory_pool: Arc::new(MemoryPool::new(1024 * 1024, 1000)),
        }
    }

    async fn handle_request(&self, data: &[u8]) -> Vec<u8> {
        // 从内存池分配缓冲区
        let buffer = self.memory_pool.allocate(data.len());

        // 处理数据
        let processed_data = process_data(data);

        // 返回处理结果
        processed_data
    }
}

fn process_data(data: &[u8]) -> Vec<u8> {
    // 简单的数据处理
    data.iter().map(|&b| b.wrapping_add(1)).collect()
}
```

### 安全配置

#### TLS 配置

```rust
use c10_networks::security::tls::{TlsConfig, TlsServer};
use std::path::Path;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = TlsConfig::new()
        .certificate_file(Path::new("cert.pem"))
        .private_key_file(Path::new("key.pem"))
        .build()?;

    let server = TlsServer::new("127.0.0.1:8443", config).await?;

    println!("TLS 服务器启动在 127.0.0.1:8443");

    loop {
        let mut client = server.accept().await?;

        tokio::spawn(async move {
            let mut buffer = [0; 1024];

            loop {
                match client.read(&mut buffer).await {
                    Ok(0) => break,
                    Ok(n) => {
                        let message = String::from_utf8_lossy(&buffer[..n]);
                        println!("收到加密消息: {}", message);

                        let response = format!("收到: {}", message);
                        if let Err(e) = client.write_all(response.as_bytes()).await {
                            eprintln!("写入错误: {}", e);
                            break;
                        }
                    }
                    Err(e) => {
                        eprintln!("读取错误: {}", e);
                        break;
                    }
                }
            }
        });
    }
}
```

#### 认证和授权

```rust
use c10_networks::security::auth::{AuthManager, JwtToken};
use std::collections::HashMap;

struct SecureServer {
    auth_manager: AuthManager,
}

impl SecureServer {
    fn new() -> Self {
        Self {
            auth_manager: AuthManager::new(),
        }
    }

    async fn handle_authenticated_request(&self, token: &str, request: &str) -> Result<String, String> {
        // 验证 JWT token
        let claims = self.auth_manager.verify_token(token)?;

        // 检查权限
        if !self.auth_manager.has_permission(&claims, "read") {
            return Err("权限不足".to_string());
        }

        // 处理请求
        Ok(format!("处理请求: {}", request))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let server = SecureServer::new();

    // 模拟认证请求
    let token = "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...";
    let request = "GET /api/data";

    match server.handle_authenticated_request(token, request).await {
        Ok(response) => println!("响应: {}", response),
        Err(e) => println!("错误: {}", e),
    }

    Ok(())
}
```

## 最佳实践

### 代码组织

#### 模块化设计

```rust
// src/lib.rs
pub mod protocol;
pub mod error;
pub mod security;
pub mod performance;

// src/protocol/mod.rs
pub mod tcp;
pub mod udp;
pub mod http;
pub mod websocket;

// src/protocol/tcp/mod.rs
pub mod client;
pub mod server;
pub mod connection;

pub use client::TcpClient;
pub use server::TcpServer;
pub use connection::TcpConnection;
```

#### 配置管理

```rust
use serde::{Deserialize, Serialize};
use std::path::Path;

#[derive(Debug, Serialize, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub max_connections: usize,
    pub timeout: u64,
    pub tls: Option<TlsConfig>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TlsConfig {
    pub cert_file: String,
    pub key_file: String,
    pub ca_file: Option<String>,
}

impl ServerConfig {
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn std::error::Error>> {
        let content = std::fs::read_to_string(path)?;
        let config: ServerConfig = toml::from_str(&content)?;
        Ok(config)
    }

    pub fn default() -> Self {
        Self {
            host: "127.0.0.1".to_string(),
            port: 8080,
            max_connections: 1000,
            timeout: 30,
            tls: None,
        }
    }
}
```

### 资源管理

#### 连接生命周期管理

```rust
use c10_networks::protocol::tcp::TcpConnection;
use std::sync::Arc;
use tokio::sync::RwLock;

struct ConnectionManager {
    connections: Arc<RwLock<Vec<Arc<TcpConnection>>>>,
    max_connections: usize,
}

impl ConnectionManager {
    fn new(max_connections: usize) -> Self {
        Self {
            connections: Arc::new(RwLock::new(Vec::new())),
            max_connections,
        }
    }

    async fn add_connection(&self, connection: Arc<TcpConnection>) -> Result<(), String> {
        let mut connections = self.connections.write().await;

        if connections.len() >= self.max_connections {
            return Err("连接数已达上限".to_string());
        }

        connections.push(connection);
        Ok(())
    }

    async fn remove_connection(&self, connection_id: u64) -> bool {
        let mut connections = self.connections.write().await;

        if let Some(pos) = connections.iter().position(|c| c.id == connection_id) {
            connections.remove(pos);
            true
        } else {
            false
        }
    }

    async fn get_connection_count(&self) -> usize {
        let connections = self.connections.read().await;
        connections.len()
    }
}
```

#### 内存管理

```rust
use c10_networks::performance::memory_pool::MemoryPool;
use std::sync::Arc;

struct ResourceManager {
    memory_pool: Arc<MemoryPool>,
    buffer_pool: Arc<Vec<Vec<u8>>>,
}

impl ResourceManager {
    fn new() -> Self {
        Self {
            memory_pool: Arc::new(MemoryPool::new(1024 * 1024, 1000)),
            buffer_pool: Arc::new(Vec::new()),
        }
    }

    fn get_buffer(&self, size: usize) -> Vec<u8> {
        // 尝试从池中获取合适大小的缓冲区
        if let Some(mut buffer) = self.buffer_pool.pop() {
            if buffer.capacity() >= size {
                buffer.clear();
                buffer
            } else {
                vec![0; size]
            }
        } else {
            vec![0; size]
        }
    }

    fn return_buffer(&self, buffer: Vec<u8>) {
        // 将缓冲区返回到池中
        if buffer.capacity() <= 1024 * 1024 { // 限制池大小
            // 注意：这里需要实现线程安全的缓冲区池
        }
    }
}
```

### 测试策略

#### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use c10_networks::protocol::tcp::TcpClient;
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    #[tokio::test]
    async fn test_tcp_client_connection() {
        let mut client = TcpClient::new("127.0.0.1:8080").await.unwrap();

        // 测试连接
        assert!(client.is_connected());

        // 测试数据传输
        let test_data = b"test message";
        client.write_all(test_data).await.unwrap();

        let mut buffer = [0; 1024];
        let n = client.read(&mut buffer).await.unwrap();
        assert_eq!(&buffer[..n], test_data);
    }

    #[test]
    fn test_packet_creation() {
        let packet = Packet::new(
            PacketType::Raw,
            Bytes::from(b"test data"),
        );

        assert_eq!(packet.packet_type, PacketType::Raw);
        assert_eq!(packet.data, Bytes::from(b"test data"));
    }
}
```

#### 集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use c10_networks::protocol::tcp::{TcpServer, TcpClient};
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    #[tokio::test]
    async fn test_tcp_server_client_integration() {
        // 启动服务器
        let server = TcpServer::new("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();

        // 启动客户端
        let mut client = TcpClient::new(&server_addr.to_string()).await.unwrap();

        // 测试通信
        let test_message = b"Hello, Server!";
        client.write_all(test_message).await.unwrap();

        let mut server_client = server.accept().await.unwrap();
        let mut buffer = [0; 1024];
        let n = server_client.read(&mut buffer).await.unwrap();

        assert_eq!(&buffer[..n], test_message);

        // 发送响应
        let response = b"Hello, Client!";
        server_client.write_all(response).await.unwrap();

        let mut client_buffer = [0; 1024];
        let n = client.read(&mut client_buffer).await.unwrap();
        assert_eq!(&client_buffer[..n], response);
    }
}
```

### 部署指南

#### Docker 部署

```dockerfile
# Dockerfile
FROM rust:1.70-slim as builder

WORKDIR /app
COPY . .
RUN cargo build --release

FROM debian:bullseye-slim
RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/c10_networks /usr/local/bin/c10_networks
EXPOSE 8080
CMD ["c10_networks"]
```

#### Kubernetes 部署

```yaml
# k8s-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: c10-networks
spec:
  replicas: 3
  selector:
    matchLabels:
      app: c10-networks
  template:
    metadata:
      labels:
        app: c10-networks
    spec:
      containers:
      - name: c10-networks
        image: c10-networks:latest
        ports:
        - containerPort: 8080
        env:
        - name: RUST_LOG
          value: "info"
        resources:
          requests:
            memory: "64Mi"
            cpu: "100m"
          limits:
            memory: "128Mi"
            cpu: "200m"
---
apiVersion: v1
kind: Service
metadata:
  name: c10-networks-service
spec:
  selector:
    app: c10-networks
  ports:
  - port: 80
    targetPort: 8080
  type: LoadBalancer
```

## 常见问题

### Q: 如何处理网络连接超时？

A: 使用 `ErrorRecovery` trait 提供的重试机制：

```rust
use c10_networks::error::{NetworkError, ErrorRecovery};
use std::time::Duration;

async fn handle_timeout() -> Result<(), NetworkError> {
    let result = some_network_operation().await;

    match result {
        Ok(data) => Ok(data),
        Err(e) => {
            if e.is_retryable() {
                println!("操作超时，将在 {:?} 后重试", e.retry_delay());
                // 实现重试逻辑
                Err(e)
            } else {
                Err(e)
            }
        }
    }
}
```

### Q: 如何优化大量并发连接的性能？

A: 使用连接池和异步处理：

```rust
use c10_networks::protocol::tcp::TcpServer;
use tokio::sync::Semaphore;

struct HighPerformanceServer {
    semaphore: Arc<Semaphore>,
}

impl HighPerformanceServer {
    fn new(max_connections: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_connections)),
        }
    }

    async fn handle_connection(&self, mut client: TcpClient) {
        let _permit = self.semaphore.acquire().await.unwrap();

        // 处理连接
        let mut buffer = [0; 1024];
        loop {
            match client.read(&mut buffer).await {
                Ok(0) => break,
                Ok(n) => {
                    // 快速处理
                    if let Err(_) = client.write_all(&buffer[..n]).await {
                        break;
                    }
                }
                Err(_) => break,
            }
        }
    }
}
```

### Q: 如何实现自定义协议？

A: 实现 `Packet` trait 和相关的序列化/反序列化逻辑：

```rust
use c10_networks::packet::{Packet, PacketType};
use bytes::Bytes;

#[derive(Debug, Clone)]
pub struct CustomPacket {
    pub header: CustomHeader,
    pub payload: Bytes,
}

#[derive(Debug, Clone)]
pub struct CustomHeader {
    pub version: u8,
    pub message_type: u8,
    pub length: u16,
}

impl Packet for CustomPacket {
    fn packet_type(&self) -> PacketType {
        PacketType::Custom("custom".to_string())
    }

    fn serialize(&self) -> Bytes {
        let mut data = Vec::new();
        data.push(self.header.version);
        data.push(self.header.message_type);
        data.extend_from_slice(&self.header.length.to_be_bytes());
        data.extend_from_slice(&self.payload);
        Bytes::from(data)
    }

    fn deserialize(data: Bytes) -> Result<Self, String> {
        if data.len() < 4 {
            return Err("数据太短".to_string());
        }

        let version = data[0];
        let message_type = data[1];
        let length = u16::from_be_bytes([data[2], data[3]]);

        if data.len() < 4 + length as usize {
            return Err("数据长度不匹配".to_string());
        }

        let payload = data.slice(4..4 + length as usize);

        Ok(CustomPacket {
            header: CustomHeader {
                version,
                message_type,
                length,
            },
            payload,
        })
    }
}
```

## 进阶主题

### 自定义协议

#### 实现自定义协议栈

```rust
use c10_networks::protocol::Protocol;
use bytes::Bytes;

pub struct CustomProtocol {
    name: String,
    version: String,
}

impl CustomProtocol {
    pub fn new(name: String, version: String) -> Self {
        Self { name, version }
    }
}

impl Protocol for CustomProtocol {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }

    fn encode(&self, data: &[u8]) -> Result<Bytes, String> {
        // 实现编码逻辑
        let mut encoded = Vec::new();
        encoded.extend_from_slice(&self.name.as_bytes());
        encoded.extend_from_slice(&self.version.as_bytes());
        encoded.extend_from_slice(data);
        Ok(Bytes::from(encoded))
    }

    fn decode(&self, data: Bytes) -> Result<Bytes, String> {
        // 实现解码逻辑
        let header_size = self.name.len() + self.version.len();
        if data.len() < header_size {
            return Err("数据太短".to_string());
        }

        Ok(data.slice(header_size..))
    }
}
```

### 网络监控

#### 实现网络监控

```rust
use c10_networks::performance::metrics::NetworkMetrics;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};

pub struct NetworkMonitor {
    metrics: Arc<RwLock<NetworkMetrics>>,
    start_time: Instant,
}

impl NetworkMonitor {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(RwLock::new(NetworkMetrics::new())),
            start_time: Instant::now(),
        }
    }

    pub async fn record_connection(&self) {
        let mut metrics = self.metrics.write().await;
        metrics.increment_connections();
    }

    pub async fn record_bytes_sent(&self, bytes: usize) {
        let mut metrics = self.metrics.write().await;
        metrics.add_bytes_sent(bytes);
    }

    pub async fn record_bytes_received(&self, bytes: usize) {
        let mut metrics = self.metrics.write().await;
        metrics.add_bytes_received(bytes);
    }

    pub async fn get_metrics(&self) -> NetworkMetrics {
        let metrics = self.metrics.read().await;
        metrics.clone()
    }

    pub fn uptime(&self) -> Duration {
        self.start_time.elapsed()
    }
}
```

### 负载均衡

#### 实现简单的负载均衡

```rust
use c10_networks::protocol::tcp::TcpClient;
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct LoadBalancer {
    servers: Arc<RwLock<Vec<String>>>,
    current_index: Arc<RwLock<usize>>,
}

impl LoadBalancer {
    pub fn new(servers: Vec<String>) -> Self {
        Self {
            servers: Arc::new(RwLock::new(servers)),
            current_index: Arc::new(RwLock::new(0)),
        }
    }

    pub async fn get_next_server(&self) -> Option<String> {
        let servers = self.servers.read().await;
        let mut index = self.current_index.write().await;

        if servers.is_empty() {
            return None;
        }

        let server = servers[*index].clone();
        *index = (*index + 1) % servers.len();
        Some(server)
    }

    pub async fn add_server(&self, server: String) {
        let mut servers = self.servers.write().await;
        servers.push(server);
    }

    pub async fn remove_server(&self, server: &str) {
        let mut servers = self.servers.write().await;
        servers.retain(|s| s != server);
    }
}

pub struct BalancedClient {
    load_balancer: Arc<LoadBalancer>,
}

impl BalancedClient {
    pub fn new(servers: Vec<String>) -> Self {
        Self {
            load_balancer: Arc::new(LoadBalancer::new(servers)),
        }
    }

    pub async fn connect(&self) -> Result<TcpClient, String> {
        if let Some(server) = self.load_balancer.get_next_server().await {
            TcpClient::new(&server).await.map_err(|e| e.to_string())
        } else {
            Err("没有可用的服务器".to_string())
        }
    }
}
```

### 故障恢复

#### 实现故障恢复机制

```rust
use c10_networks::error::{NetworkError, ErrorRecovery};
use std::time::Duration;
use tokio::time::sleep;

pub struct FaultTolerantClient {
    primary_server: String,
    backup_servers: Vec<String>,
    max_retries: u32,
}

impl FaultTolerantClient {
    pub fn new(primary_server: String, backup_servers: Vec<String>) -> Self {
        Self {
            primary_server,
            backup_servers,
            max_retries: 3,
        }
    }

    pub async fn execute_with_failover<F, T>(&self, operation: F) -> Result<T, String>
    where
        F: Fn(&str) -> Result<T, NetworkError>,
    {
        let mut servers = vec![self.primary_server.clone()];
        servers.extend(self.backup_servers.clone());

        for (attempt, server) in servers.iter().enumerate() {
            match operation(server) {
                Ok(result) => return Ok(result),
                Err(e) => {
                    if attempt < servers.len() - 1 {
                        println!("服务器 {} 失败，尝试下一个: {}", server, e);
                        if e.is_retryable() {
                            sleep(e.retry_delay()).await;
                        }
                    } else {
                        return Err(format!("所有服务器都失败了: {}", e));
                    }
                }
            }
        }

        Err("没有可用的服务器".to_string())
    }
}
```

这个教程涵盖了 c10_networks 库的主要功能和使用方法，从基础的网络编程到高级的性能优化和安全配置。通过遵循这些最佳实践，您可以构建高效、可靠和安全的网络应用程序。
