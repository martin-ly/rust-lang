# Rust 1.90 网络编程实战示例大全

> **文档版本**: v1.0  
> **适用版本**: Rust 1.90+, Tokio 1.35+  
> **最后更新**: 2025-10-19  
> **文档类型**: 💻 代码示例集

---


## 📊 目录

- [Rust 1.90 网络编程实战示例大全](#rust-190-网络编程实战示例大全)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [Rust 1.90 核心特性](#rust-190-核心特性)
    - [1. async trait 特性详解](#1-async-trait-特性详解)
    - [2. async closure 特性详解](#2-async-closure-特性详解)
    - [3. const 泛型推断](#3-const-泛型推断)
  - [TCP编程完整示例](#tcp编程完整示例)
    - [1. 高性能TCP服务器](#1-高性能tcp服务器)
    - [2. 功能完整的TCP客户端](#2-功能完整的tcp客户端)
  - [UDP编程完整示例](#udp编程完整示例)
    - [1. UDP服务器与客户端](#1-udp服务器与客户端)


## 📋 目录

- [Rust 1.90 网络编程实战示例大全](#rust-190-网络编程实战示例大全)
  - [� 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [Rust 1.90 核心特性](#rust-190-核心特性)
    - [1. async trait 特性详解](#1-async-trait-特性详解)
    - [2. async closure 特性详解](#2-async-closure-特性详解)
    - [3. const 泛型推断](#3-const-泛型推断)
  - [TCP编程完整示例](#tcp编程完整示例)
    - [1. 高性能TCP服务器](#1-高性能tcp服务器)
    - [2. 功能完整的TCP客户端](#2-功能完整的tcp客户端)
  - [UDP编程完整示例](#udp编程完整示例)
    - [1. UDP服务器与客户端](#1-udp服务器与客户端)

---

## Rust 1.90 核心特性

### 1. async trait 特性详解

```rust
//! Rust 1.90: async trait 特性
//! 允许在 trait 中直接使用 async 方法

use std::future::Future;
use std::pin::Pin;
use tokio::io::{AsyncRead, AsyncWrite};
use tokio::net::TcpStream;

/// 网络协议抽象 trait
pub trait NetworkProtocol: Send + Sync {
    /// 连接到服务器
    async fn connect(&mut self, addr: &str) -> Result<(), Box<dyn std::error::Error>>;
    
    /// 发送数据
    async fn send(&mut self, data: &[u8]) -> Result<usize, Box<dyn std::error::Error>>;
    
    /// 接收数据
    async fn receive(&mut self, buf: &mut [u8]) -> Result<usize, Box<dyn std::error::Error>>;
    
    /// 关闭连接
    async fn close(&mut self) -> Result<(), Box<dyn std::error::Error>>;
}

/// TCP 协议实现
pub struct TcpProtocol {
    stream: Option<TcpStream>,
}

impl TcpProtocol {
    pub fn new() -> Self {
        Self { stream: None }
    }
}

impl NetworkProtocol for TcpProtocol {
    async fn connect(&mut self, addr: &str) -> Result<(), Box<dyn std::error::Error>> {
        let stream = TcpStream::connect(addr).await?;
        println!("✅ TCP连接成功: {}", addr);
        self.stream = Some(stream);
        Ok(())
    }
    
    async fn send(&mut self, data: &[u8]) -> Result<usize, Box<dyn std::error::Error>> {
        use tokio::io::AsyncWriteExt;
        
        if let Some(stream) = &mut self.stream {
            let n = stream.write(data).await?;
            stream.flush().await?;
            println!("📤 TCP发送 {} 字节", n);
            Ok(n)
        } else {
            Err("未连接".into())
        }
    }
    
    async fn receive(&mut self, buf: &mut [u8]) -> Result<usize, Box<dyn std::error::Error>> {
        use tokio::io::AsyncReadExt;
        
        if let Some(stream) = &mut self.stream {
            let n = stream.read(buf).await?;
            println!("📥 TCP接收 {} 字节", n);
            Ok(n)
        } else {
            Err("未连接".into())
        }
    }
    
    async fn close(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(mut stream) = self.stream.take() {
            use tokio::io::AsyncWriteExt;
            stream.shutdown().await?;
            println!("🔌 TCP连接已关闭");
        }
        Ok(())
    }
}

/// 使用 async trait 的示例函数
pub async fn demo_async_trait() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== Rust 1.90: async trait 示例 ===\n");
    
    // 创建协议实例
    let mut protocol: Box<dyn NetworkProtocol> = Box::new(TcpProtocol::new());
    
    // 连接
    protocol.connect("httpbin.org:80").await?;
    
    // 发送HTTP请求
    let request = b"GET / HTTP/1.1\r\nHost: httpbin.org\r\nConnection: close\r\n\r\n";
    protocol.send(request).await?;
    
    // 接收响应
    let mut buffer = vec![0u8; 1024];
    let n = protocol.receive(&mut buffer).await?;
    let response = String::from_utf8_lossy(&buffer[..n]);
    println!("📄 响应头:\n{}", response.lines().take(10).collect::<Vec<_>>().join("\n"));
    
    // 关闭连接
    protocol.close().await?;
    
    Ok(())
}
```

### 2. async closure 特性详解

```rust
//! Rust 1.90: async closure 特性
//! 允许创建异步闭包,简化异步编程

use futures::stream::{Stream, StreamExt};
use std::time::Duration;
use tokio::time::sleep;

/// async closure 示例: 处理数据流
pub async fn demo_async_closure() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== Rust 1.90: async closure 示例 ===\n");
    
    // 示例1: 简单的异步闭包
    let async_add = |a: i32, b: i32| async move {
        sleep(Duration::from_millis(100)).await;
        a + b
    };
    
    let result = async_add(10, 20).await;
    println!("✅ 异步加法: 10 + 20 = {}", result);
    
    // 示例2: 在 map 中使用异步闭包
    let numbers = vec![1, 2, 3, 4, 5];
    let results: Vec<_> = futures::future::join_all(
        numbers.into_iter().map(|n| async move {
            sleep(Duration::from_millis(50)).await;
            n * 2
        })
    ).await;
    
    println!("✅ 异步map结果: {:?}", results);
    
    // 示例3: 流处理with异步闭包
    let stream = futures::stream::iter(1..=5);
    let mut processed = stream.then(|n| async move {
        sleep(Duration::from_millis(100)).await;
        println!("  处理数字: {}", n);
        n * n
    });
    
    println!("✅ 异步流处理:");
    while let Some(result) = processed.next().await {
        println!("  结果: {}", result);
    }
    
    Ok(())
}

/// 高阶函数with异步闭包
pub async fn process_with_async_fn<F, Fut>(items: Vec<i32>, f: F) -> Vec<i32>
where
    F: Fn(i32) -> Fut,
    Fut: Future<Output = i32>,
{
    let mut results = Vec::new();
    for item in items {
        results.push(f(item).await);
    }
    results
}

/// 示例: 使用高阶异步函数
pub async fn demo_higher_order_async() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 高阶异步函数示例 ===\n");
    
    let items = vec![1, 2, 3, 4, 5];
    
    // 使用异步闭包处理
    let results = process_with_async_fn(items, |n| async move {
        sleep(Duration::from_millis(50)).await;
        n * n
    }).await;
    
    println!("✅ 处理结果: {:?}", results);
    
    Ok(())
}
```

### 3. const 泛型推断

```rust
//! Rust 1.90: const 泛型推断
//! 编译器可以自动推断常量泛型参数

use std::fmt;

/// 固定大小的网络数据包
#[derive(Debug, Clone)]
pub struct Packet<const N: usize> {
    data: [u8; N],
    len: usize,
}

impl<const N: usize> Packet<N> {
    /// 创建新数据包
    pub fn new() -> Self {
        Self {
            data: [0u8; N],
            len: 0,
        }
    }
    
    /// 从字节切片创建 (Rust 1.90: 编译器推断N)
    pub fn from_slice(slice: &[u8]) -> Option<Self> {
        if slice.len() > N {
            return None;
        }
        
        let mut packet = Self::new();
        packet.data[..slice.len()].copy_from_slice(slice);
        packet.len = slice.len();
        Some(packet)
    }
    
    /// 获取数据
    pub fn as_slice(&self) -> &[u8] {
        &self.data[..self.len]
    }
    
    /// 计算校验和
    pub fn checksum(&self) -> u32 {
        self.data[..self.len]
            .iter()
            .fold(0u32, |acc, &byte| acc.wrapping_add(byte as u32))
    }
}

/// Rust 1.90: 函数可以使用 _ 让编译器推断数组大小
pub fn process_packet<const N: usize>(data: [u8; N]) -> u32 {
    data.iter()
        .fold(0u32, |acc, &byte| acc.wrapping_add(byte as u32))
}

/// const 泛型示例
pub async fn demo_const_generics() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== Rust 1.90: const 泛型推断示例 ===\n");
    
    // 创建不同大小的数据包
    let small_packet: Packet<64> = Packet::from_slice(b"Hello").unwrap();
    let large_packet: Packet<1024> = Packet::from_slice(b"Large packet data").unwrap();
    
    println!("✅ 小数据包 (64字节): {:?}", small_packet.as_slice());
    println!("   校验和: {}", small_packet.checksum());
    
    println!("✅ 大数据包 (1024字节): {:?}", large_packet.as_slice());
    println!("   校验和: {}", large_packet.checksum());
    
    // Rust 1.90: 使用 _ 让编译器推断数组大小
    let checksum = process_packet([1, 2, 3, 4, 5]);
    println!("✅ 数组校验和: {}", checksum);
    
    Ok(())
}
```

---

## TCP编程完整示例

### 1. 高性能TCP服务器

```rust
//! 高性能TCP回显服务器
//! 特性: 并发处理、连接统计、优雅关闭

use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::sync::broadcast;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

/// 服务器统计信息
#[derive(Debug, Clone)]
pub struct ServerStats {
    total_connections: Arc<AtomicU64>,
    active_connections: Arc<AtomicU64>,
    bytes_received: Arc<AtomicU64>,
    bytes_sent: Arc<AtomicU64>,
}

impl ServerStats {
    pub fn new() -> Self {
        Self {
            total_connections: Arc::new(AtomicU64::new(0)),
            active_connections: Arc::new(AtomicU64::new(0)),
            bytes_received: Arc::new(AtomicU64::new(0)),
            bytes_sent: Arc::new(AtomicU64::new(0)),
        }
    }
    
    pub fn print(&self) {
        println!("\n📊 服务器统计:");
        println!("  总连接数: {}", self.total_connections.load(Ordering::Relaxed));
        println!("  活跃连接: {}", self.active_connections.load(Ordering::Relaxed));
        println!("  接收字节: {}", self.bytes_received.load(Ordering::Relaxed));
        println!("  发送字节: {}", self.bytes_sent.load(Ordering::Relaxed));
    }
}

/// TCP回显服务器
pub struct TcpEchoServer {
    listener: TcpListener,
    stats: ServerStats,
    shutdown_tx: broadcast::Sender<()>,
}

impl TcpEchoServer {
    /// 创建服务器
    pub async fn new(addr: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let listener = TcpListener::bind(addr).await?;
        let (shutdown_tx, _) = broadcast::channel(1);
        
        println!("🚀 TCP回显服务器启动于: {}", addr);
        
        Ok(Self {
            listener,
            stats: ServerStats::new(),
            shutdown_tx,
        })
    }
    
    /// 运行服务器
    pub async fn run(self) -> Result<(), Box<dyn std::error::Error>> {
        let stats = self.stats.clone();
        let shutdown_tx = self.shutdown_tx.clone();
        
        // 统计任务
        let stats_clone = stats.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(10));
            loop {
                interval.tick().await;
                stats_clone.print();
            }
        });
        
        // 接受连接
        loop {
            tokio::select! {
                result = self.listener.accept() => {
                    match result {
                        Ok((socket, addr)) => {
                            println!("✅ 新连接: {}", addr);
                            
                            stats.total_connections.fetch_add(1, Ordering::Relaxed);
                            stats.active_connections.fetch_add(1, Ordering::Relaxed);
                            
                            let stats_clone = stats.clone();
                            let mut shutdown_rx = shutdown_tx.subscribe();
                            
                            tokio::spawn(async move {
                                tokio::select! {
                                    result = Self::handle_connection(socket, stats_clone.clone()) => {
                                        if let Err(e) = result {
                                            eprintln!("❌ 处理连接错误: {}", e);
                                        }
                                    }
                                    _ = shutdown_rx.recv() => {
                                        println!("🔌 关闭连接: {}", addr);
                                    }
                                }
                                
                                stats_clone.active_connections.fetch_sub(1, Ordering::Relaxed);
                            });
                        }
                        Err(e) => {
                            eprintln!("❌ 接受连接错误: {}", e);
                        }
                    }
                }
                _ = tokio::signal::ctrl_c() => {
                    println!("\n🛑 收到关闭信号，正在优雅关闭...");
                    let _ = shutdown_tx.send(());
                    break;
                }
            }
        }
        
        // 等待所有连接关闭
        tokio::time::sleep(Duration::from_secs(1)).await;
        stats.print();
        
        Ok(())
    }
    
    /// 处理单个连接
    async fn handle_connection(
        mut socket: TcpStream,
        stats: ServerStats,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut buffer = vec![0u8; 8192];
        
        loop {
            // 读取数据
            let n = socket.read(&mut buffer).await?;
            
            if n == 0 {
                // 连接关闭
                break;
            }
            
            stats.bytes_received.fetch_add(n as u64, Ordering::Relaxed);
            
            // 回显数据
            socket.write_all(&buffer[..n]).await?;
            stats.bytes_sent.fetch_add(n as u64, Ordering::Relaxed);
        }
        
        Ok(())
    }
}

/// 示例: 运行TCP服务器
pub async fn demo_tcp_server() -> Result<(), Box<dyn std::error::Error>> {
    let server = TcpEchoServer::new("127.0.0.1:8080").await?;
    server.run().await
}
```

### 2. 功能完整的TCP客户端

```rust
//! 功能完整的TCP客户端
//! 特性: 重连机制、超时控制、连接池

use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::time::{timeout, Duration};
use std::sync::Arc;

/// TCP客户端配置
#[derive(Debug, Clone)]
pub struct TcpClientConfig {
    pub connect_timeout: Duration,
    pub read_timeout: Duration,
    pub write_timeout: Duration,
    pub max_retries: usize,
    pub retry_delay: Duration,
}

impl Default for TcpClientConfig {
    fn default() -> Self {
        Self {
            connect_timeout: Duration::from_secs(5),
            read_timeout: Duration::from_secs(10),
            write_timeout: Duration::from_secs(5),
            max_retries: 3,
            retry_delay: Duration::from_secs(1),
        }
    }
}

/// TCP客户端
pub struct TcpClient {
    addr: String,
    config: TcpClientConfig,
    stream: Option<TcpStream>,
}

impl TcpClient {
    /// 创建客户端
    pub fn new(addr: impl Into<String>) -> Self {
        Self {
            addr: addr.into(),
            config: TcpClientConfig::default(),
            stream: None,
        }
    }
    
    /// 使用自定义配置创建
    pub fn with_config(addr: impl Into<String>, config: TcpClientConfig) -> Self {
        Self {
            addr: addr.into(),
            config,
            stream: None,
        }
    }
    
    /// 连接到服务器 (带重试)
    pub async fn connect(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let mut attempts = 0;
        
        loop {
            match timeout(
                self.config.connect_timeout,
                TcpStream::connect(&self.addr)
            ).await {
                Ok(Ok(stream)) => {
                    println!("✅ 连接成功: {}", self.addr);
                    self.stream = Some(stream);
                    return Ok(());
                }
                Ok(Err(e)) => {
                    attempts += 1;
                    if attempts >= self.config.max_retries {
                        return Err(format!("连接失败 ({}次尝试): {}", attempts, e).into());
                    }
                    println!("⚠️  连接失败,重试 {}/{}: {}", attempts, self.config.max_retries, e);
                    tokio::time::sleep(self.config.retry_delay).await;
                }
                Err(_) => {
                    attempts += 1;
                    if attempts >= self.config.max_retries {
                        return Err(format!("连接超时 ({}次尝试)", attempts).into());
                    }
                    println!("⚠️  连接超时,重试 {}/{}", attempts, self.config.max_retries);
                    tokio::time::sleep(self.config.retry_delay).await;
                }
            }
        }
    }
    
    /// 发送数据
    pub async fn send(&mut self, data: &[u8]) -> Result<usize, Box<dyn std::error::Error>> {
        if let Some(stream) = &mut self.stream {
            let n = timeout(
                self.config.write_timeout,
                async {
                    stream.write_all(data).await?;
                    stream.flush().await?;
                    Ok::<_, std::io::Error>(data.len())
                }
            ).await??;
            
            println!("📤 发送 {} 字节", n);
            Ok(n)
        } else {
            Err("未连接".into())
        }
    }
    
    /// 接收数据
    pub async fn receive(&mut self, buffer: &mut [u8]) -> Result<usize, Box<dyn std::error::Error>> {
        if let Some(stream) = &mut self.stream {
            let n = timeout(
                self.config.read_timeout,
                stream.read(buffer)
            ).await??;
            
            println!("📥 接收 {} 字节", n);
            Ok(n)
        } else {
            Err("未连接".into())
        }
    }
    
    /// 发送并接收
    pub async fn send_and_receive(
        &mut self,
        data: &[u8],
        buffer: &mut [u8]
    ) -> Result<usize, Box<dyn std::error::Error>> {
        self.send(data).await?;
        self.receive(buffer).await
    }
    
    /// 关闭连接
    pub async fn close(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(mut stream) = self.stream.take() {
            stream.shutdown().await?;
            println!("🔌 连接已关闭");
        }
        Ok(())
    }
}

/// 示例: 使用TCP客户端
pub async fn demo_tcp_client() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== TCP客户端示例 ===\n");
    
    // 创建客户端
    let mut client = TcpClient::new("127.0.0.1:8080");
    
    // 连接
    client.connect().await?;
    
    // 发送并接收数据
    let message = b"Hello, TCP Server!";
    let mut buffer = vec![0u8; 1024];
    let n = client.send_and_receive(message, &mut buffer).await?;
    
    println!("📄 回显: {}", String::from_utf8_lossy(&buffer[..n]));
    
    // 关闭连接
    client.close().await?;
    
    Ok(())
}
```

---

## UDP编程完整示例

### 1. UDP服务器与客户端

```rust
//! UDP服务器和客户端完整实现
//! 特性: 多播、广播、超时控制

use tokio::net::UdpSocket;
use std::net::{SocketAddr, Ipv4Addr};
use std::sync::Arc;
use tokio::time::{timeout, Duration};

/// UDP服务器
pub struct UdpServer {
    socket: Arc<UdpSocket>,
}

impl UdpServer {
    /// 创建UDP服务器
    pub async fn new(addr: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let socket = UdpSocket::bind(addr).await?;
        println!("🚀 UDP服务器启动于: {}", addr);
        
        Ok(Self {
            socket: Arc::new(socket),
        })
    }
    
    /// 运行服务器 (回显模式)
    pub async fn run_echo(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut buffer = vec![0u8; 65507]; // UDP最大包大小
        
        loop {
            // 接收数据
            let (n, peer_addr) = self.socket.recv_from(&mut buffer).await?;
            println!("📥 收到来自 {} 的 {} 字节", peer_addr, n);
            
            // 回显数据
            let sent = self.socket.send_to(&buffer[..n], peer_addr).await?;
            println!("📤 回显 {} 字节到 {}", sent, peer_addr);
        }
    }
    
    /// 运行服务器 (自定义处理)
    pub async fn run_with_handler<F>(&self, handler: F) -> Result<(), Box<dyn std::error::Error>>
    where
        F: Fn(&[u8], SocketAddr) -> Vec<u8> + Send + Sync + 'static,
    {
        let mut buffer = vec![0u8; 65507];
        let handler = Arc::new(handler);
        
        loop {
            let (n, peer_addr) = self.socket.recv_from(&mut buffer).await?;
            println!("📥 收到来自 {} 的 {} 字节", peer_addr, n);
            
            // 处理数据
            let response = handler(&buffer[..n], peer_addr);
            
            // 发送响应
            let sent = self.socket.send_to(&response, peer_addr).await?;
            println!("📤 发送 {} 字节到 {}", sent, peer_addr);
        }
    }
}

/// UDP客户端
pub struct UdpClient {
    socket: UdpSocket,
    server_addr: SocketAddr,
    timeout_duration: Duration,
}

impl UdpClient {
    /// 创建UDP客户端
    pub async fn new(server_addr: &str) -> Result<Self, Box<dyn std::error::Error>> {
        // 绑定到任意端口
        let socket = UdpSocket::bind("0.0.0.0:0").await?;
        let server_addr: SocketAddr = server_addr.parse()?;
        
        println!("✅ UDP客户端创建,目标服务器: {}", server_addr);
        
        Ok(Self {
            socket,
            server_addr,
            timeout_duration: Duration::from_secs(5),
        })
    }
    
    /// 设置超时时间
    pub fn set_timeout(&mut self, duration: Duration) {
        self.timeout_duration = duration;
    }
    
    /// 发送数据
    pub async fn send(&self, data: &[u8]) -> Result<usize, Box<dyn std::error::Error>> {
        let n = self.socket.send_to(data, self.server_addr).await?;
        println!("📤 发送 {} 字节", n);
        Ok(n)
    }
    
    /// 接收数据
    pub async fn receive(&self, buffer: &mut [u8]) -> Result<(usize, SocketAddr), Box<dyn std::error::Error>> {
        let result = timeout(
            self.timeout_duration,
            self.socket.recv_from(buffer)
        ).await?;
        
        let (n, addr) = result?;
        println!("📥 接收 {} 字节来自 {}", n, addr);
        Ok((n, addr))
    }
    
    /// 发送并接收
    pub async fn send_and_receive(
        &self,
        data: &[u8],
        buffer: &mut [u8]
    ) -> Result<(usize, SocketAddr), Box<dyn std::error::Error>> {
        self.send(data).await?;
        self.receive(buffer).await
    }
}

/// UDP多播示例
pub struct UdpMulticast {
    socket: UdpSocket,
    multicast_addr: SocketAddr,
}

impl UdpMulticast {
    /// 创建多播发送者
    pub async fn new_sender(multicast_addr: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let socket = UdpSocket::bind("0.0.0.0:0").await?;
        let multicast_addr: SocketAddr = multicast_addr.parse()?;
        
        println!("✅ UDP多播发送者创建: {}", multicast_addr);
        
        Ok(Self {
            socket,
            multicast_addr,
        })
    }
    
    /// 创建多播接收者
    pub async fn new_receiver(
        multicast_addr: &str,
        interface: Ipv4Addr,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let multicast_addr: SocketAddr = multicast_addr.parse()?;
        let socket = UdpSocket::bind(multicast_addr).await?;
        
        // 加入多播组
        if let SocketAddr::V4(addr) = multicast_addr {
            socket.join_multicast_v4(*addr.ip(), interface)?;
            println!("✅ UDP多播接收者加入组: {}", multicast_addr);
        }
        
        Ok(Self {
            socket,
            multicast_addr,
        })
    }
    
    /// 发送多播消息
    pub async fn send(&self, data: &[u8]) -> Result<usize, Box<dyn std::error::Error>> {
        let n = self.socket.send_to(data, self.multicast_addr).await?;
        println!("📤 多播发送 {} 字节", n);
        Ok(n)
    }
    
    /// 接收多播消息
    pub async fn receive(&self, buffer: &mut [u8]) -> Result<(usize, SocketAddr), Box<dyn std::error::Error>> {
        let (n, addr) = self.socket.recv_from(buffer).await?;
        println!("📥 多播接收 {} 字节来自 {}", n, addr);
        Ok((n, addr))
    }
}

/// 示例: UDP回显客户端
pub async fn demo_udp_client() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== UDP客户端示例 ===\n");
    
    let client = UdpClient::new("127.0.0.1:9000").await?;
    
    let message = b"Hello, UDP Server!";
    let mut buffer = vec![0u8; 1024];
    
    let (n, addr) = client.send_and_receive(message, &mut buffer).await?;
    println!("📄 回显: {} (来自 {})", String::from_utf8_lossy(&buffer[..n]), addr);
    
    Ok(())
}
```

---

由于篇幅限制，文档的其余部分将在下一个文件中继续...

---

**待续**: HTTP客户端、WebSocket、DNS、gRPC等完整示例

---

**文档维护**: C10 Networks 团队  
**最后更新**: 2025-10-19  
**文档版本**: v1.0 (Part 1)
