# C10 Networks 综合教程指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`DOCUMENTATION_STANDARDS.md`](DOCUMENTATION_STANDARDS.md)。

[![Rust](https://img.shields.io/badge/rust-1.90+-orange.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](../../LICENSE)
[![Crates.io](https://img.shields.io/crates/v/c10_networks.svg)](https://crates.io/crates/c10_networks)

## 📋 目录

- [C10 Networks 综合教程指南](#c10-networks-综合教程指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [1. 教程目标](#1-教程目标)
    - [2. 学习路径](#2-学习路径)
    - [3. 前置要求](#3-前置要求)
    - [4. 学习资源](#4-学习资源)
  - [🚀 第一阶段：基础入门](#-第一阶段基础入门)
    - [1. 环境准备](#1-环境准备)
      - [1.1 Rust环境安装](#11-rust环境安装)
      - [1.2 项目创建](#12-项目创建)
      - [1.3 依赖配置](#13-依赖配置)
      - [1.4 开发工具](#14-开发工具)
    - [2. 网络编程基础](#2-网络编程基础)
      - [2.1 网络概念](#21-网络概念)
      - [2.2 协议栈理解](#22-协议栈理解)
      - [2.3 异步编程基础](#23-异步编程基础)
      - [2.4 错误处理](#24-错误处理)
    - [3. 第一个网络程序](#3-第一个网络程序)
      - [3.1 TCP回显服务器](#31-tcp回显服务器)
      - [3.2 TCP客户端](#32-tcp客户端)
      - [3.3 测试连接](#33-测试连接)
      - [3.4 错误处理实践](#34-错误处理实践)
  - [🔧 第二阶段：协议实现](#-第二阶段协议实现)
    - [1. HTTP协议](#1-http协议)
      - [1.1 HTTP基础](#11-http基础)
  - [🔗 相关文档](#-相关文档)

## 🎯 概述

本教程指南为C10 Networks项目提供了完整的学习路径，从基础网络编程到高级分布式系统，从理论到实践，帮助开发者系统性地掌握现代网络编程技术。

### 1. 教程目标

通过本教程，您将能够：

- **掌握基础**：理解网络编程的基本概念和原理
- **实现协议**：能够实现TCP、HTTP、WebSocket等网络协议
- **应用高级特性**：掌握异步编程、连接池、负载均衡等高级技术
- **构建实际应用**：开发微服务、分布式系统等实际应用
- **确保安全**：实现安全的网络通信和身份认证
- **进行测试**：编写全面的测试和验证代码

### 2. 学习路径

教程分为六个阶段，每个阶段都有明确的学习目标和实践项目：

1. **第一阶段：基础入门**（1-2周）
2. **第二阶段：协议实现**（2-3周）
3. **第三阶段：高级特性**（2-3周）
4. **第四阶段：实际应用**（3-4周）
5. **第五阶段：安全实践**（2-3周）
6. **第六阶段：测试与验证**（1-2周）

### 3. 前置要求

开始学习前，请确保您具备以下基础知识：

- **Rust语言基础**：熟悉Rust语法、所有权、生命周期等概念
- **异步编程概念**：了解async/await、Future、Stream等概念
- **网络基础知识**：理解TCP/IP协议栈、HTTP协议等
- **系统编程经验**：有基本的系统编程和并发编程经验

### 4. 学习资源

- **理论文档**：[NETWORK_COMMUNICATION_THEORY_ENHANCED.md](NETWORK_COMMUNICATION_THEORY_ENHANCED.md)
- **概念定义**：[CONCEPT_DEFINITIONS_ENHANCED.md](CONCEPT_DEFINITIONS_ENHANCED.md)
- **示例代码**：[EXAMPLES_AND_APPLICATIONS_ENHANCED.md](EXAMPLES_AND_APPLICATIONS_ENHANCED.md)
- **API文档**：[API_DOCUMENTATION.md](API_DOCUMENTATION.md)

## 🚀 第一阶段：基础入门

### 1. 环境准备

#### 1.1 Rust环境安装

**安装Rust工具链**：

```bash
# 安装Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 配置环境变量
source ~/.cargo/env

# 验证安装
rustc --version
cargo --version
```

**安装必要工具**：

```bash
# 安装rustfmt（代码格式化）
rustup component add rustfmt

# 安装clippy（代码检查）
rustup component add clippy

# 安装rust-analyzer（IDE支持）
rustup component add rust-analyzer
```

#### 1.2 项目创建

**创建新项目**：

```bash
# 创建新的Rust项目
cargo new c10_networks_tutorial
cd c10_networks_tutorial

# 添加C10 Networks依赖
cargo add c10_networks
cargo add tokio --features full
cargo add anyhow
cargo add thiserror
```

**项目结构**：

```text
c10_networks_tutorial/
├── Cargo.toml
├── src/
│   ├── main.rs
│   ├── lib.rs
│   ├── error.rs
│   ├── tcp/
│   ├── http/
│   ├── websocket/
│   └── udp/
├── examples/
├── tests/
└── benches/
```

#### 1.3 依赖配置

**Cargo.toml配置**：

```toml
[package]
name = "c10_networks_tutorial"
version = "0.1.0"
edition = "2021"

[dependencies]
c10_networks = "0.1.0"
tokio = { version = "1.35", features = ["full"] }
anyhow = "1.0"
thiserror = "1.0"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tracing = "0.1"
tracing-subscriber = "0.3"

[dev-dependencies]
tokio-test = "0.4"
criterion = { version = "0.5", features = ["html_reports"] }
```

#### 1.4 开发工具

**VS Code配置**：

```json
{
    "rust-analyzer.checkOnSave.command": "clippy",
    "rust-analyzer.cargo.features": "all",
    "editor.formatOnSave": true,
    "editor.defaultFormatter": "rust-lang.rust-analyzer"
}
```

**常用命令**：

```bash
# 代码格式化
cargo fmt

# 代码检查
cargo clippy

# 运行测试
cargo test

# 运行示例
cargo run --example tcp_server

# 性能测试
cargo bench
```

### 2. 网络编程基础

#### 2.1 网络概念

**OSI七层模型**：

```text
应用层 (Application Layer)
├── HTTP, HTTPS, WebSocket, gRPC
├── 数据格式：JSON, XML, Protobuf
└── 应用协议：REST, GraphQL

表示层 (Presentation Layer)
├── 数据编码：UTF-8, Base64
├── 数据压缩：Gzip, Brotli
└── 数据加密：TLS, SSL

会话层 (Session Layer)
├── 会话管理：Cookie, Session
├── 连接管理：Keep-Alive
└── 同步控制：Checkpoint

传输层 (Transport Layer)
├── TCP：可靠传输，面向连接
├── UDP：不可靠传输，无连接
└── QUIC：基于UDP的可靠传输

网络层 (Network Layer)
├── IP协议：IPv4, IPv6
├── 路由协议：OSPF, BGP
└── 地址解析：ARP, NDP

数据链路层 (Data Link Layer)
├── 以太网：Ethernet
├── 无线网络：WiFi, Bluetooth
└── 错误检测：CRC, Checksum

物理层 (Physical Layer)
├── 传输介质：双绞线, 光纤, 无线电
├── 信号编码：NRZ, Manchester
└── 物理接口：RJ45, USB, HDMI
```

**TCP/IP协议栈**：

```text
应用层
├── HTTP/HTTPS (80/443)
├── FTP (21)
├── SSH (22)
├── SMTP (25)
├── DNS (53)
└── DHCP (67/68)

传输层
├── TCP (可靠传输)
└── UDP (不可靠传输)

网络层
├── IP (IPv4/IPv6)
├── ICMP (控制消息)
└── IGMP (组播管理)

网络接口层
├── 以太网
├── WiFi
└── 其他物理网络
```

#### 2.2 协议栈理解

**协议分层原理**：

```rust
// 协议栈抽象
pub trait ProtocolLayer {
    type Input;
    type Output;
    
    async fn process(&self, input: Self::Input) -> Result<Self::Output, NetworkError>;
}

// 应用层协议
pub struct ApplicationLayer {
    handlers: HashMap<String, Box<dyn Fn(Request) -> Response + Send + Sync>>,
}

impl ProtocolLayer for ApplicationLayer {
    type Input = Request;
    type Output = Response;
    
    async fn process(&self, input: Self::Input) -> Result<Self::Output, NetworkError> {
        // 处理应用层请求
        if let Some(handler) = self.handlers.get(&input.path) {
            Ok(handler(input))
        } else {
            Err(NetworkError::NotFound)
        }
    }
}

// 传输层协议
pub struct TransportLayer {
    protocol: TransportProtocol,
}

impl ProtocolLayer for TransportLayer {
    type Input = Segment;
    type Output = Segment;
    
    async fn process(&self, input: Self::Input) -> Result<Self::Output, NetworkError> {
        match self.protocol {
            TransportProtocol::Tcp => {
                // TCP处理逻辑
                self.process_tcp(input).await
            }
            TransportProtocol::Udp => {
                // UDP处理逻辑
                self.process_udp(input).await
            }
        }
    }
}
```

#### 2.3 异步编程基础

**异步编程概念**：

```rust
use tokio::time::{sleep, Duration};

// 异步函数
async fn async_function() -> Result<String, Box<dyn std::error::Error>> {
    // 模拟异步操作
    sleep(Duration::from_millis(100)).await;
    Ok("Hello, Async!".to_string())
}

// Future trait
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub struct MyFuture {
    state: FutureState,
}

enum FutureState {
    Pending,
    Ready(String),
}

impl Future for MyFuture {
    type Output = String;
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.state {
            FutureState::Pending => {
                // 设置waker，当数据准备好时唤醒
                self.state = FutureState::Ready("Data ready".to_string());
                Poll::Ready("Data ready".to_string())
            }
            FutureState::Ready(ref data) => Poll::Ready(data.clone()),
        }
    }
}

// Stream trait
use tokio_stream::Stream;
use tokio_stream::StreamExt;

pub struct MyStream {
    items: Vec<String>,
    index: usize,
}

impl Stream for MyStream {
    type Item = String;
    
    fn poll_next(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        if self.index < self.items.len() {
            let item = self.items[self.index].clone();
            self.index += 1;
            Poll::Ready(Some(item))
        } else {
            Poll::Ready(None)
        }
    }
}

// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 调用异步函数
    let result = async_function().await?;
    println!("{}", result);
    
    // 使用Future
    let future = MyFuture { state: FutureState::Pending };
    let result = future.await;
    println!("{}", result);
    
    // 使用Stream
    let mut stream = MyStream {
        items: vec!["item1".to_string(), "item2".to_string(), "item3".to_string()],
        index: 0,
    };
    
    while let Some(item) = stream.next().await {
        println!("Stream item: {}", item);
    }
    
    Ok(())
}
```

#### 2.4 错误处理

**错误类型定义**：

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum NetworkError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Connection error: {0}")]
    Connection(String),
    
    #[error("Protocol error: {0}")]
    Protocol(String),
    
    #[error("Timeout error")]
    Timeout,
    
    #[error("Authentication failed")]
    Authentication,
    
    #[error("Authorization denied")]
    Authorization,
    
    #[error("Resource not found")]
    NotFound,
    
    #[error("Internal server error: {0}")]
    Internal(String),
}

// 错误处理宏
macro_rules! network_error {
    ($($arg:tt)*) => {
        NetworkError::Internal(format!($($arg)*))
    };
}

// 结果类型别名
pub type NetworkResult<T> = Result<T, NetworkError>;

// 错误处理示例
pub async fn handle_network_operation() -> NetworkResult<()> {
    // 模拟网络操作
    let result = simulate_network_call().await;
    
    match result {
        Ok(data) => {
            println!("操作成功: {:?}", data);
            Ok(())
        }
        Err(e) => {
            // 错误分类处理
            match e {
                NetworkError::Timeout => {
                    println!("操作超时，正在重试...");
                    // 重试逻辑
                    retry_operation().await
                }
                NetworkError::Connection(_) => {
                    println!("连接错误，检查网络状态");
                    Err(e)
                }
                NetworkError::Authentication => {
                    println!("认证失败，请检查凭据");
                    Err(e)
                }
                _ => {
                    println!("未知错误: {}", e);
                    Err(e)
                }
            }
        }
    }
}

async fn simulate_network_call() -> NetworkResult<String> {
    // 模拟网络调用
    tokio::time::sleep(Duration::from_millis(100)).await;
    Ok("Network data".to_string())
}

async fn retry_operation() -> NetworkResult<()> {
    // 重试逻辑
    for attempt in 1..=3 {
        println!("重试第 {} 次", attempt);
        tokio::time::sleep(Duration::from_millis(1000)).await;
        
        if let Ok(_) = simulate_network_call().await {
            return Ok(());
        }
    }
    
    Err(NetworkError::Timeout)
}
```

### 3. 第一个网络程序

#### 3.1 TCP回显服务器

**基础TCP服务器**：

```rust
use c10_networks::error::NetworkResult;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use std::sync::Arc;

/// TCP回显服务器
pub struct EchoServer {
    listener: TcpListener,
}

impl EchoServer {
    /// 创建新的回显服务器
    pub async fn new(addr: &str) -> NetworkResult<Self> {
        let listener = TcpListener::bind(addr).await?;
        Ok(Self { listener })
    }
    
    /// 启动服务器
    pub async fn run(&self) -> NetworkResult<()> {
        println!("TCP回显服务器启动在: {}", self.listener.local_addr()?);
        
        loop {
            let (stream, addr) = self.listener.accept().await?;
            println!("新连接来自: {}", addr);
            
            // 为每个连接创建异步任务
            tokio::spawn(async move {
                if let Err(e) = Self::handle_connection(stream).await {
                    eprintln!("处理连接错误: {}", e);
                }
            });
        }
    }
    
    /// 处理单个连接
    async fn handle_connection(mut stream: TcpStream) -> NetworkResult<()> {
        let mut buffer = [0; 1024];
        
        loop {
            // 读取数据
            let n = stream.read(&mut buffer).await?;
            if n == 0 {
                println!("连接关闭");
                break;
            }
            
            // 回显数据
            stream.write_all(&buffer[..n]).await?;
            println!("回显 {} 字节数据", n);
        }
        
        Ok(())
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let server = EchoServer::new("127.0.0.1:8080").await?;
    server.run().await
}
```

#### 3.2 TCP客户端

**基础TCP客户端**：

```rust
use c10_networks::error::NetworkResult;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use std::time::Duration;

/// TCP客户端
pub struct EchoClient {
    stream: Option<TcpStream>,
    addr: String,
}

impl EchoClient {
    /// 创建新的客户端
    pub fn new(addr: &str) -> Self {
        Self {
            stream: None,
            addr: addr.to_string(),
        }
    }
    
    /// 连接到服务器
    pub async fn connect(&mut self) -> NetworkResult<()> {
        let stream = TcpStream::connect(&self.addr).await?;
        self.stream = Some(stream);
        println!("连接到服务器: {}", self.addr);
        Ok(())
    }
    
    /// 发送消息并接收回显
    pub async fn send_message(&mut self, message: &str) -> NetworkResult<String> {
        if let Some(stream) = &mut self.stream {
            // 发送消息
            stream.write_all(message.as_bytes()).await?;
            println!("发送消息: {}", message);
            
            // 接收回显
            let mut buffer = [0; 1024];
            let n = stream.read(&mut buffer).await?;
            let response = String::from_utf8_lossy(&buffer[..n]).to_string();
            println!("接收回显: {}", response);
            
            Ok(response)
        } else {
            Err(NetworkError::Connection("未连接到服务器".to_string()))
        }
    }
    
    /// 断开连接
    pub async fn disconnect(&mut self) -> NetworkResult<()> {
        if let Some(_) = self.stream.take() {
            println!("断开连接");
        }
        Ok(())
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let mut client = EchoClient::new("127.0.0.1:8080");
    
    // 连接服务器
    client.connect().await?;
    
    // 发送多条消息
    let messages = vec![
        "Hello, Server!",
        "How are you?",
        "This is a test message.",
    ];
    
    for message in messages {
        let response = client.send_message(message).await?;
        println!("服务器响应: {}", response);
        
        // 等待一段时间
        tokio::time::sleep(Duration::from_millis(1000)).await;
    }
    
    // 断开连接
    client.disconnect().await?;
    
    Ok(())
}
```

#### 3.3 测试连接

**测试脚本**：

```rust
use c10_networks::error::NetworkResult;
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::time::Duration;

/// 连接测试工具
pub struct ConnectionTester {
    addr: String,
}

impl ConnectionTester {
    pub fn new(addr: &str) -> Self {
        Self {
            addr: addr.to_string(),
        }
    }
    
    /// 测试连接
    pub async fn test_connection(&self) -> NetworkResult<()> {
        println!("测试连接到: {}", self.addr);
        
        let start = std::time::Instant::now();
        let stream = TcpStream::connect(&self.addr).await?;
        let duration = start.elapsed();
        
        println!("连接成功，耗时: {:?}", duration);
        
        // 测试数据传输
        self.test_data_transfer(stream).await?;
        
        Ok(())
    }
    
    /// 测试数据传输
    async fn test_data_transfer(&self, mut stream: TcpStream) -> NetworkResult<()> {
        let test_data = "Test message for data transfer";
        
        // 发送数据
        let start = std::time::Instant::now();
        stream.write_all(test_data.as_bytes()).await?;
        let send_duration = start.elapsed();
        
        // 接收数据
        let mut buffer = [0; 1024];
        let n = stream.read(&mut buffer).await?;
        let receive_duration = start.elapsed();
        
        let response = String::from_utf8_lossy(&buffer[..n]);
        println!("发送数据: {}", test_data);
        println!("接收数据: {}", response);
        println!("发送耗时: {:?}", send_duration);
        println!("接收耗时: {:?}", receive_duration);
        
        // 验证数据
        if response == test_data {
            println!("✅ 数据传输测试通过");
        } else {
            println!("❌ 数据传输测试失败");
            return Err(NetworkError::Protocol("数据不匹配".to_string()));
        }
        
        Ok(())
    }
    
    /// 压力测试
    pub async fn stress_test(&self, num_connections: usize) -> NetworkResult<()> {
        println!("开始压力测试，连接数: {}", num_connections);
        
        let mut handles = vec![];
        
        for i in 0..num_connections {
            let addr = self.addr.clone();
            let handle = tokio::spawn(async move {
                let mut stream = TcpStream::connect(&addr).await?;
                let message = format!("Stress test message {}", i);
                stream.write_all(message.as_bytes()).await?;
                
                let mut buffer = [0; 1024];
                let n = stream.read(&mut buffer).await?;
                let response = String::from_utf8_lossy(&buffer[..n]);
                
                Ok::<String, NetworkError>(response)
            });
            
            handles.push(handle);
        }
        
        // 等待所有连接完成
        let mut success_count = 0;
        for handle in handles {
            match handle.await {
                Ok(Ok(response)) => {
                    println!("连接成功: {}", response);
                    success_count += 1;
                }
                Ok(Err(e)) => {
                    println!("连接失败: {}", e);
                }
                Err(e) => {
                    println!("任务失败: {}", e);
                }
            }
        }
        
        println!("压力测试完成，成功连接数: {}/{}", success_count, num_connections);
        
        if success_count == num_connections {
            Ok(())
        } else {
            Err(NetworkError::Internal("部分连接失败".to_string()))
        }
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let tester = ConnectionTester::new("127.0.0.1:8080");
    
    // 基本连接测试
    tester.test_connection().await?;
    
    // 压力测试
    tester.stress_test(10).await?;
    
    Ok(())
}
```

#### 3.4 错误处理实践

**错误处理示例**：

```rust
use c10_networks::error::{NetworkError, NetworkResult};
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::time::Duration;

/// 带错误处理的客户端
pub struct RobustClient {
    stream: Option<TcpStream>,
    addr: String,
    max_retries: usize,
    retry_delay: Duration,
}

impl RobustClient {
    pub fn new(addr: &str) -> Self {
        Self {
            stream: None,
            addr: addr.to_string(),
            max_retries: 3,
            retry_delay: Duration::from_millis(1000),
        }
    }
    
    /// 带重试的连接
    pub async fn connect_with_retry(&mut self) -> NetworkResult<()> {
        for attempt in 1..=self.max_retries {
            match TcpStream::connect(&self.addr).await {
                Ok(stream) => {
                    self.stream = Some(stream);
                    println!("连接成功 (尝试 {})", attempt);
                    return Ok(());
                }
                Err(e) => {
                    println!("连接失败 (尝试 {}): {}", attempt, e);
                    if attempt < self.max_retries {
                        println!("等待 {}ms 后重试...", self.retry_delay.as_millis());
                        tokio::time::sleep(self.retry_delay).await;
                    }
                }
            }
        }
        
        Err(NetworkError::Connection("连接失败，已达到最大重试次数".to_string()))
    }
    
    /// 带超时的操作
    pub async fn send_with_timeout(&mut self, message: &str, timeout: Duration) -> NetworkResult<String> {
        if let Some(stream) = &mut self.stream {
            // 使用tokio::time::timeout包装操作
            let result = tokio::time::timeout(timeout, async {
                // 发送消息
                stream.write_all(message.as_bytes()).await?;
                
                // 接收响应
                let mut buffer = [0; 1024];
                let n = stream.read(&mut buffer).await?;
                let response = String::from_utf8_lossy(&buffer[..n]).to_string();
                
                Ok::<String, NetworkError>(response)
            }).await;
            
            match result {
                Ok(Ok(response)) => Ok(response),
                Ok(Err(e)) => Err(e),
                Err(_) => Err(NetworkError::Timeout),
            }
        } else {
            Err(NetworkError::Connection("未连接到服务器".to_string()))
        }
    }
    
    /// 健康检查
    pub async fn health_check(&mut self) -> NetworkResult<bool> {
        match self.send_with_timeout("ping", Duration::from_secs(5)).await {
            Ok(response) => {
                if response == "pong" {
                    println!("健康检查通过");
                    Ok(true)
                } else {
                    println!("健康检查失败: 响应不匹配");
                    Ok(false)
                }
            }
            Err(e) => {
                println!("健康检查失败: {}", e);
                Ok(false)
            }
        }
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let mut client = RobustClient::new("127.0.0.1:8080");
    
    // 带重试的连接
    client.connect_with_retry().await?;
    
    // 健康检查
    if client.health_check().await? {
        println!("服务器健康");
    } else {
        println!("服务器不健康");
    }
    
    // 带超时的消息发送
    let response = client.send_with_timeout("Hello, Server!", Duration::from_secs(10)).await?;
    println!("服务器响应: {}", response);
    
    Ok(())
}
```

## 🔧 第二阶段：协议实现

### 1. HTTP协议

#### 1.1 HTTP基础

**HTTP请求结构**：

```rust
use std::collections::HashMap;

/// HTTP方法
#[derive(Debug, Clone, PartialEq)]
pub enum HttpMethod {
    GET,
    POST,
    PUT,
    DELETE,
    PATCH,
    HEAD,
    OPTIONS,
}

/// HTTP版本
#[derive(Debug, Clone, PartialEq)]
pub enum HttpVersion {
    Http1_0,
    Http1_1,
    Http2,
}

/// HTTP状态码
#[derive(Debug, Clone, PartialEq)]
pub enum HttpStatusCode {
    Ok = 200,
    Created = 201,
    BadRequest = 400,
    NotFound = 404,
    InternalServerError = 500,
}

/// HTTP请求
#[derive(Debug, Clone)]
pub struct HttpRequest {
    pub method: HttpMethod,
    pub path: String,
    pub version: HttpVersion,
    pub headers: HashMap<String, String>,
    pub body: Vec<u8>,
}

/// HTTP响应
#[derive(Debug, Clone)]
pub struct HttpResponse {
    pub version: HttpVersion,
    pub status: HttpStatusCode,
    pub headers: HashMap<String, String>,
    pub body: Vec<u8>,
}

impl HttpRequest {
    /// 解析HTTP请求
    pub fn parse(request_str: &str) -> NetworkResult<Self> {
        let lines: Vec<&str> = request_str.lines().collect();
        if lines.is_empty() {
            return Err(NetworkError::Protocol("空请求".to_string()));
        }
        
        // 解析请求行
        let request_line = lines[0];
        let parts: Vec<&str> = request_line.split_whitespace().collect();
        if parts.len() != 3 {
            return Err(NetworkError::Protocol("无效的请求行".to_string()));
        }
        
        let method = match parts[0] {
            "GET" => HttpMethod::GET,
            "POST" => HttpMethod::POST,
            "PUT" => HttpMethod::PUT,
            "DELETE" => HttpMethod::DELETE,
            "PATCH" => HttpMethod::PATCH,
            "HEAD" => HttpMethod::HEAD,
            "OPTIONS" => HttpMethod::OPTIONS,
            _ => return Err(NetworkError::Protocol("不支持的方法".to_string())),
        };
        
        let path = parts[1].to_string();
        
        let version = match parts[2] {
            "HTTP/1.0" => HttpVersion::Http1_0,
            "HTTP/1.1" => HttpVersion::Http1_1,
            "HTTP/2" => HttpVersion::Http2,
            _ => return Err(NetworkError::Protocol("不支持的版本".to_string())),
        };
        
        // 解析头部
        let mut headers = HashMap::new();
        let mut body_start = 0;
        
        for (i, line) in lines.iter().enumerate().skip(1) {
            if line.is_empty() {
                body_start = i + 1;
                break;
            }
            
            if let Some(colon_pos) = line.find(':') {
                let key = line[..colon_pos].trim().to_string();
                let value = line[colon_pos + 1..].trim().to_string();
                headers.insert(key, value);
            }
        }
        
        // 解析主体
        let body = if body_start < lines.len() {
            lines[body_start..].join("\n").into_bytes()
        } else {
            Vec::new()
        };
        
        Ok(HttpRequest {
            method,
            path,
            version,
            headers,
            body,
        })
    }
    
    /// 转换为字符串
    pub fn to_string(&self) -> String {
        let method_str = match self.method {
            HttpMethod::GET => "GET",
            HttpMethod::POST => "POST",
            HttpMethod::PUT => "PUT",
            HttpMethod::DELETE => "DELETE",
            HttpMethod::PATCH => "PATCH",
            HttpMethod::HEAD => "HEAD",
            HttpMethod::OPTIONS => "OPTIONS",
        };
        
        let version_str = match self.version {
            HttpVersion::Http1_0 => "HTTP/1.0",
            HttpVersion::Http1_1 => "HTTP/1.1",
            HttpVersion::Http2 => "HTTP/2",
        };
        
        let mut request = format!("{} {} {}\r\n", method_str, self.path, version_str);
        
        for (key, value) in &self.headers {
            request.push_str(&format!("{}: {}\r\n", key, value));
        }
        
        request.push_str("\r\n");
        
        if !self.body.is_empty() {
            request.push_str(&String::from_utf8_lossy(&self.body));
        }
        
        request
    }
}

impl HttpResponse {
    /// 创建新的响应
    pub fn new(version: HttpVersion, status: HttpStatusCode) -> Self {
        Self {
            version,
            status,
            headers: HashMap::new(),
            body: Vec::new(),
        }
    }
    
    /// 设置响应体
    pub fn with_body(mut self, body: Vec<u8>) -> Self {
        self.body = body;
        self.headers.insert("Content-Length".to_string(), self.body.len().to_string());
        self
    }
    
    /// 转换为字符串
    pub fn to_string(&self) -> String {
        let version_str = match self.version {
            HttpVersion::Http1_0 => "HTTP/1.0",
            HttpVersion::Http1_1 => "HTTP/1.1",
            HttpVersion::Http2 => "HTTP/2",
        };
        
        let status_code = self.status.clone() as u16;
        let status_text = match self.status {
            HttpStatusCode::Ok => "OK",
            HttpStatusCode::Created => "Created",
            HttpStatusCode::BadRequest => "Bad Request",
            HttpStatusCode::NotFound => "Not Found",
            HttpStatusCode::InternalServerError => "Internal Server Error",
        };
        
        let mut response = format!("{} {} {}\r\n", version_str, status_code, status_text);
        
        for (key, value) in &self.headers {
            response.push_str(&format!("{}: {}\r\n", key, value));
        }
        
        response.push_str("\r\n");
        
        if !self.body.is_empty() {
            response.push_str(&String::from_utf8_lossy(&self.body));
        }
        
        response
    }
}
```

## 🔗 相关文档

- [NETWORK_COMMUNICATION_THEORY_ENHANCED.md](NETWORK_COMMUNICATION_THEORY_ENHANCED.md) - 网络通信理论增强版
- [CONCEPT_DEFINITIONS_ENHANCED.md](CONCEPT_DEFINITIONS_ENHANCED.md) - 概念定义增强版
- [EXAMPLES_AND_APPLICATIONS_ENHANCED.md](EXAMPLES_AND_APPLICATIONS_ENHANCED.md) - 示例代码增强版
- [API_DOCUMENTATION.md](API_DOCUMENTATION.md) - API参考文档
- [PERFORMANCE_ANALYSIS_GUIDE.md](PERFORMANCE_ANALYSIS_GUIDE.md) - 性能分析指南
- [BEST_PRACTICES.md](BEST_PRACTICES.md) - 最佳实践指南

---

**C10 Networks 综合教程指南** - 为网络编程提供完整的学习路径！

*最后更新: 2025年1月*  
*文档版本: v2.0*  
*维护者: C10 Networks 开发团队*
