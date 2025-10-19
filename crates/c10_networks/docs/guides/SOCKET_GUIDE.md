# TCP/UDP 套接字指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](STYLE.md)。

## 📋 目录

- [TCP/UDP 套接字指南](#tcpudp-套接字指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [主要特性](#主要特性)
  - [⚡ 快速开始](#-快速开始)
    - [TCP客户端/服务器](#tcp客户端服务器)
    - [UDP客户端/服务器](#udp客户端服务器)
  - [🔧 TCP 套接字](#-tcp-套接字)
    - [TCP服务器](#tcp服务器)
    - [TCP客户端](#tcp客户端)
    - [TCP连接池](#tcp连接池)
  - [📡 UDP 套接字](#-udp-套接字)
    - [UDP服务器](#udp服务器)
    - [UDP客户端](#udp客户端)
    - [UDP广播](#udp广播)
    - [UDP多播](#udp多播)
  - [🌐 网络地址处理](#-网络地址处理)
    - [地址解析](#地址解析)
    - [地址过滤](#地址过滤)
  - [📊 高级特性](#-高级特性)
    - [套接字选项](#套接字选项)
    - [套接字监控](#套接字监控)
    - [套接字池管理](#套接字池管理)
  - [⚙️ 配置选项](#️-配置选项)
    - [TcpConfig 完整配置](#tcpconfig-完整配置)
    - [UdpConfig 完整配置](#udpconfig-完整配置)
    - [环境变量配置](#环境变量配置)
  - [🔍 错误处理](#-错误处理)
    - [错误类型](#错误类型)
    - [重连机制](#重连机制)
  - [📈 性能优化](#-性能优化)
    - [连接复用](#连接复用)
    - [批量操作](#批量操作)
  - [🧪 测试示例](#-测试示例)
    - [单元测试](#单元测试)
    - [集成测试](#集成测试)
    - [性能测试](#性能测试)
  - [❓ 常见问题](#-常见问题)
    - [Q: 如何设置TCP套接字选项？](#q-如何设置tcp套接字选项)
    - [Q: 如何处理UDP丢包？](#q-如何处理udp丢包)
    - [Q: 如何优化TCP性能？](#q-如何优化tcp性能)
    - [Q: 如何实现UDP广播？](#q-如何实现udp广播)
    - [Q: 如何处理网络超时？](#q-如何处理网络超时)
    - [Q: 如何实现连接池？](#q-如何实现连接池)
    - [Q: 如何监控套接字状态？](#q-如何监控套接字状态)
    - [Q: 如何优化UDP性能？](#q-如何优化udp性能)

## 🎯 概述

C10 Networks 提供了完整的TCP和UDP套接字实现，支持异步I/O、连接池管理和高性能网络通信。

### 主要特性

- **TCP套接字**: 可靠的面向连接协议
- **UDP套接字**: 无连接的数据报协议
- **异步I/O**: 基于Tokio的高性能实现
- **连接池**: 高效的连接复用
- **地址解析**: 支持IPv4和IPv6
- **超时控制**: 灵活的超时配置

## ⚡ 快速开始

### TCP客户端/服务器

```rust
use c10_networks::socket::tcp::{TcpServer, TcpClient};
use c10_networks::error::NetworkResult;

// 服务器端
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let server = TcpServer::bind("127.0.0.1:8080").await?;
    println!("TCP服务器启动在 127.0.0.1:8080");
    
    loop {
        let (mut stream, addr) = server.accept().await?;
        println!("新连接来自: {}", addr);
        
        tokio::spawn(async move {
            let mut buffer = [0; 1024];
            
            loop {
                match stream.read(&mut buffer).await {
                    Ok(0) => break,
                    Ok(n) => {
                        let data = &buffer[..n];
                        println!("收到数据: {} 字节", n);
                        
                        // 回显数据
                        stream.write_all(data).await?;
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

// 客户端
async fn tcp_client() -> NetworkResult<()> {
    let mut client = TcpClient::connect("127.0.0.1:8080").await?;
    
    // 发送数据
    let data = b"Hello, TCP!";
    client.write_all(data).await?;
    
    // 接收响应
    let mut buffer = [0; 1024];
    let n = client.read(&mut buffer).await?;
    let response = &buffer[..n];
    
    println!("收到响应: {}", String::from_utf8_lossy(response));
    
    Ok(())
}
```

### UDP客户端/服务器

```rust
use c10_networks::socket::udp::{UdpSocket, UdpServer};
use c10_networks::error::NetworkResult;

// 服务器端
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let server = UdpServer::bind("127.0.0.1:8080").await?;
    println!("UDP服务器启动在 127.0.0.1:8080");
    
    let mut buffer = [0; 1024];
    
    loop {
        let (n, addr) = server.recv_from(&mut buffer).await?;
        let data = &buffer[..n];
        println!("收到来自 {} 的数据: {} 字节", addr, n);
        
        // 回显数据
        server.send_to(data, addr).await?;
    }
}

// 客户端
async fn udp_client() -> NetworkResult<()> {
    let client = UdpSocket::bind("127.0.0.1:0").await?;
    
    // 发送数据
    let data = b"Hello, UDP!";
    client.send_to(data, "127.0.0.1:8080").await?;
    
    // 接收响应
    let mut buffer = [0; 1024];
    let (n, addr) = client.recv_from(&mut buffer).await?;
    let response = &buffer[..n];
    
    println!("收到来自 {} 的响应: {}", addr, String::from_utf8_lossy(response));
    
    Ok(())
}
```

## 🔧 TCP 套接字

### TCP服务器

```rust
use c10_networks::socket::tcp::{TcpServer, TcpConfig};
use c10_networks::error::NetworkResult;
use std::time::Duration;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 使用默认配置
    let server = TcpServer::bind("127.0.0.1:8080").await?;
    
    // 使用自定义配置
    let config = TcpConfig::new()
        .with_keep_alive(true)
        .with_nodelay(true)
        .with_read_timeout(Duration::from_secs(30))
        .with_write_timeout(Duration::from_secs(30))
        .with_connection_timeout(Duration::from_secs(10));
    
    let server = TcpServer::with_config("127.0.0.1:8080", config).await?;
    
    println!("TCP服务器启动在 127.0.0.1:8080");
    
    loop {
        let (stream, addr) = server.accept().await?;
        println!("新连接来自: {}", addr);
        
        tokio::spawn(handle_tcp_connection(stream, addr));
    }
}

async fn handle_tcp_connection(
    mut stream: TcpStream,
    addr: std::net::SocketAddr,
) -> NetworkResult<()> {
    println!("处理TCP连接: {}", addr);
    
    let mut buffer = [0; 1024];
    
    loop {
        match stream.read(&mut buffer).await {
            Ok(0) => {
                println!("连接 {} 正常关闭", addr);
                break;
            }
            Ok(n) => {
                let data = &buffer[..n];
                println!("收到数据: {} 字节", n);
                
                // 处理数据
                let response = process_tcp_data(data);
                
                // 发送响应
                stream.write_all(&response).await?;
            }
            Err(e) => {
                eprintln!("读取错误: {}", e);
                break;
            }
        }
    }
    
    Ok(())
}

fn process_tcp_data(data: &[u8]) -> Vec<u8> {
    // 简单的数据处理：转换为大写
    data.iter().map(|&b| b.to_ascii_uppercase()).collect()
}
```

### TCP客户端

```rust
use c10_networks::socket::tcp::{TcpClient, TcpConfig};
use c10_networks::error::NetworkResult;
use std::time::Duration;

async fn tcp_client_example() -> NetworkResult<()> {
    // 使用默认配置
    let mut client = TcpClient::connect("127.0.0.1:8080").await?;
    
    // 使用自定义配置
    let config = TcpConfig::new()
        .with_keep_alive(true)
        .with_nodelay(true)
        .with_read_timeout(Duration::from_secs(30))
        .with_write_timeout(Duration::from_secs(30))
        .with_connection_timeout(Duration::from_secs(10));
    
    let mut client = TcpClient::connect_with_config("127.0.0.1:8080", config).await?;
    
    // 发送数据
    let data = b"Hello, TCP Server!";
    client.write_all(data).await?;
    println!("发送数据: {} 字节", data.len());
    
    // 接收响应
    let mut buffer = [0; 1024];
    let n = client.read(&mut buffer).await?;
    let response = &buffer[..n];
    
    println!("收到响应: {}", String::from_utf8_lossy(response));
    
    Ok(())
}
```

### TCP连接池

```rust
use c10_networks::socket::tcp::{TcpClient, TcpConfig};
use std::collections::VecDeque;
use std::sync::Arc;
use tokio::sync::Mutex;

struct TcpConnectionPool {
    connections: Arc<Mutex<VecDeque<TcpClient>>>,
    max_size: usize,
    address: String,
    config: TcpConfig,
}

impl TcpConnectionPool {
    fn new(address: String, max_size: usize, config: TcpConfig) -> Self {
        Self {
            connections: Arc::new(Mutex::new(VecDeque::new())),
            max_size,
            address,
            config,
        }
    }
    
    async fn get_connection(&self) -> NetworkResult<TcpClient> {
        // 尝试从池中获取连接
        {
            let mut connections = self.connections.lock().await;
            if let Some(connection) = connections.pop_front() {
                return Ok(connection);
            }
        }
        
        // 池中没有可用连接，创建新连接
        TcpClient::connect_with_config(&self.address, self.config.clone()).await
    }
    
    async fn return_connection(&self, connection: TcpClient) {
        let mut connections = self.connections.lock().await;
        
        if connections.len() < self.max_size {
            connections.push_back(connection);
        }
        // 如果池已满，丢弃连接
    }
    
    async fn close_all(&self) -> NetworkResult<()> {
        let mut connections = self.connections.lock().await;
        
        while let Some(mut connection) = connections.pop_front() {
            connection.close().await?;
        }
        
        Ok(())
    }
}

// 使用示例
async fn use_tcp_pool() -> NetworkResult<()> {
    let config = TcpConfig::new()
        .with_keep_alive(true)
        .with_nodelay(true);
    
    let pool = TcpConnectionPool::new(
        "127.0.0.1:8080".to_string(),
        10,
        config
    );
    
    // 获取连接
    let mut connection = pool.get_connection().await?;
    
    // 使用连接
    connection.write_all(b"Hello").await?;
    
    // 归还连接
    pool.return_connection(connection).await;
    
    Ok(())
}
```

## 📡 UDP 套接字

### UDP服务器

```rust
use c10_networks::socket::udp::{UdpServer, UdpConfig};
use c10_networks::error::NetworkResult;
use std::time::Duration;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 使用默认配置
    let server = UdpServer::bind("127.0.0.1:8080").await?;
    
    // 使用自定义配置
    let config = UdpConfig::new()
        .with_read_timeout(Duration::from_secs(30))
        .with_write_timeout(Duration::from_secs(30))
        .with_buffer_size(8192);
    
    let server = UdpServer::with_config("127.0.0.1:8080", config).await?;
    
    println!("UDP服务器启动在 127.0.0.1:8080");
    
    let mut buffer = [0; 1024];
    
    loop {
        match server.recv_from(&mut buffer).await {
            Ok((n, addr)) => {
                let data = &buffer[..n];
                println!("收到来自 {} 的数据: {} 字节", addr, n);
                
                // 处理数据
                let response = process_udp_data(data);
                
                // 发送响应
                server.send_to(&response, addr).await?;
            }
            Err(e) => {
                eprintln!("接收错误: {}", e);
            }
        }
    }
}

fn process_udp_data(data: &[u8]) -> Vec<u8> {
    // 简单的数据处理：反转数据
    data.iter().rev().cloned().collect()
}
```

### UDP客户端

```rust
use c10_networks::socket::udp::{UdpSocket, UdpConfig};
use c10_networks::error::NetworkResult;
use std::time::Duration;

async fn udp_client_example() -> NetworkResult<()> {
    // 使用默认配置
    let client = UdpSocket::bind("127.0.0.1:0").await?;
    
    // 使用自定义配置
    let config = UdpConfig::new()
        .with_read_timeout(Duration::from_secs(30))
        .with_write_timeout(Duration::from_secs(30))
        .with_buffer_size(8192);
    
    let client = UdpSocket::with_config("127.0.0.1:0", config).await?;
    
    // 发送数据
    let data = b"Hello, UDP Server!";
    client.send_to(data, "127.0.0.1:8080").await?;
    println!("发送数据: {} 字节", data.len());
    
    // 接收响应
    let mut buffer = [0; 1024];
    let (n, addr) = client.recv_from(&mut buffer).await?;
    let response = &buffer[..n];
    
    println!("收到来自 {} 的响应: {}", addr, String::from_utf8_lossy(response));
    
    Ok(())
}
```

### UDP广播

```rust
use c10_networks::socket::udp::UdpSocket;
use c10_networks::error::NetworkResult;

async fn udp_broadcast_example() -> NetworkResult<()> {
    let socket = UdpSocket::bind("0.0.0.0:0").await?;
    
    // 启用广播
    socket.set_broadcast(true)?;
    
    // 发送广播消息
    let data = b"Broadcast message";
    socket.send_to(data, "255.255.255.255:8080").await?;
    
    println!("广播消息已发送");
    
    // 接收响应
    let mut buffer = [0; 1024];
    let (n, addr) = socket.recv_from(&mut buffer).await?;
    let response = &buffer[..n];
    
    println!("收到来自 {} 的响应: {}", addr, String::from_utf8_lossy(response));
    
    Ok(())
}
```

### UDP多播

```rust
use c10_networks::socket::udp::UdpSocket;
use c10_networks::error::NetworkResult;

async fn udp_multicast_example() -> NetworkResult<()> {
    let socket = UdpSocket::bind("0.0.0.0:8080").await?;
    
    // 加入多播组
    let multicast_addr = "224.0.0.1:8080".parse()?;
    socket.join_multicast_group("224.0.0.1".parse()?)?;
    
    println!("已加入多播组 224.0.0.1");
    
    // 接收多播消息
    let mut buffer = [0; 1024];
    loop {
        let (n, addr) = socket.recv_from(&mut buffer).await?;
        let data = &buffer[..n];
        
        println!("收到来自 {} 的多播消息: {}", addr, String::from_utf8_lossy(data));
    }
}

async fn udp_multicast_sender() -> NetworkResult<()> {
    let socket = UdpSocket::bind("0.0.0.0:0").await?;
    
    // 发送多播消息
    let data = b"Multicast message";
    socket.send_to(data, "224.0.0.1:8080").await?;
    
    println!("多播消息已发送");
    
    Ok(())
}
```

## 🌐 网络地址处理

### 地址解析

```rust
use c10_networks::socket::address::{AddressResolver, SocketAddr};
use c10_networks::error::NetworkResult;

async fn address_resolution_example() -> NetworkResult<()> {
    let resolver = AddressResolver::new();
    
    // 解析域名
    let addresses = resolver.resolve("example.com").await?;
    println!("example.com 解析结果: {:?}", addresses);
    
    // 解析端口
    let socket_addrs = resolver.resolve_socket_addrs("example.com", 80).await?;
    println!("example.com:80 解析结果: {:?}", socket_addrs);
    
    // 解析IPv6地址
    let ipv6_addr = "2001:db8::1".parse()?;
    let socket_addr = SocketAddr::new(ipv6_addr, 8080);
    println!("IPv6地址: {}", socket_addr);
    
    Ok(())
}
```

### 地址过滤

```rust
use c10_networks::socket::address::{AddressFilter, SocketAddr};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

async fn address_filtering_example() -> NetworkResult<()> {
    let filter = AddressFilter::new();
    
    // 只允许IPv4地址
    filter.allow_ipv4(true);
    filter.allow_ipv6(false);
    
    // 只允许特定网段
    filter.allow_subnet("192.168.0.0/16".parse()?);
    filter.allow_subnet("10.0.0.0/8".parse()?);
    
    // 检查地址是否被允许
    let addr1 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 1)), 8080);
    let addr2 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(8, 8, 8, 8)), 53);
    
    println!("192.168.1.1:8080 是否允许: {}", filter.is_allowed(addr1));
    println!("8.8.8.8:53 是否允许: {}", filter.is_allowed(addr2));
    
    Ok(())
}
```

## 📊 高级特性

### 套接字选项

```rust
use c10_networks::socket::tcp::{TcpClient, TcpConfig};
use c10_networks::socket::udp::{UdpSocket, UdpConfig};
use std::time::Duration;

async fn socket_options_example() -> NetworkResult<()> {
    // TCP套接字选项
    let tcp_config = TcpConfig::new()
        .with_keep_alive(true)
        .with_nodelay(true)
        .with_linger(Duration::from_secs(5))
        .with_reuse_addr(true)
        .with_reuse_port(true)
        .with_recv_buffer_size(8192)
        .with_send_buffer_size(8192);
    
    let tcp_client = TcpClient::connect_with_config("127.0.0.1:8080", tcp_config).await?;
    
    // UDP套接字选项
    let udp_config = UdpConfig::new()
        .with_reuse_addr(true)
        .with_reuse_port(true)
        .with_recv_buffer_size(8192)
        .with_send_buffer_size(8192)
        .with_broadcast(true)
        .with_multicast_loop(true);
    
    let udp_socket = UdpSocket::with_config("127.0.0.1:0", udp_config).await?;
    
    Ok(())
}
```

### 套接字监控

```rust
use c10_networks::socket::monitor::{SocketMonitor, SocketStats};
use c10_networks::socket::tcp::TcpClient;
use std::time::Duration;

async fn socket_monitoring_example() -> NetworkResult<()> {
    let monitor = SocketMonitor::new();
    
    // 创建TCP客户端
    let mut client = TcpClient::connect("127.0.0.1:8080").await?;
    
    // 注册监控
    let socket_id = monitor.register_socket(&client).await?;
    
    // 发送数据
    client.write_all(b"Hello, World!").await?;
    
    // 获取统计信息
    let stats = monitor.get_stats(socket_id).await?;
    println!("套接字统计: {:?}", stats);
    
    // 监控连接状态
    let is_connected = monitor.is_connected(socket_id).await?;
    println!("连接状态: {}", is_connected);
    
    // 获取网络延迟
    let latency = monitor.measure_latency(socket_id).await?;
    println!("网络延迟: {:?}", latency);
    
    Ok(())
}
```

### 套接字池管理

```rust
use c10_networks::socket::pool::{SocketPool, PoolConfig};
use c10_networks::socket::tcp::TcpClient;
use std::time::Duration;

async fn socket_pool_example() -> NetworkResult<()> {
    let config = PoolConfig::new()
        .with_max_connections(100)
        .with_max_connections_per_host(10)
        .with_connection_timeout(Duration::from_secs(30))
        .with_idle_timeout(Duration::from_secs(300))
        .with_keep_alive(true);
    
    let pool = SocketPool::new(config);
    
    // 获取连接
    let mut connection = pool.get_connection("127.0.0.1:8080").await?;
    
    // 使用连接
    connection.write_all(b"Hello").await?;
    
    // 归还连接
    pool.return_connection(connection).await;
    
    // 获取池统计信息
    let stats = pool.get_stats().await?;
    println!("连接池统计: {:?}", stats);
    
    Ok(())
}
```

## ⚙️ 配置选项

### TcpConfig 完整配置

```rust
use c10_networks::socket::tcp::{TcpClient, TcpConfig};
use std::time::Duration;

let config = TcpConfig::new()
    // 连接选项
    .with_keep_alive(true)
    .with_nodelay(true)
    .with_linger(Duration::from_secs(5))
    
    // 地址重用
    .with_reuse_addr(true)
    .with_reuse_port(true)
    
    // 缓冲区大小
    .with_recv_buffer_size(8192)
    .with_send_buffer_size(8192)
    
    // 超时设置
    .with_connection_timeout(Duration::from_secs(30))
    .with_read_timeout(Duration::from_secs(30))
    .with_write_timeout(Duration::from_secs(30))
    
    // 其他选项
    .with_tcp_keepalive(Duration::from_secs(60))
    .with_tcp_keepalive_interval(Duration::from_secs(30))
    .with_tcp_keepalive_retries(3);

let client = TcpClient::connect_with_config("127.0.0.1:8080", config).await?;
```

### UdpConfig 完整配置

```rust
use c10_networks::socket::udp::{UdpSocket, UdpConfig};
use std::time::Duration;

let config = UdpConfig::new()
    // 地址重用
    .with_reuse_addr(true)
    .with_reuse_port(true)
    
    // 缓冲区大小
    .with_recv_buffer_size(8192)
    .with_send_buffer_size(8192)
    
    // 超时设置
    .with_read_timeout(Duration::from_secs(30))
    .with_write_timeout(Duration::from_secs(30))
    
    // 广播和多播
    .with_broadcast(true)
    .with_multicast_loop(true)
    .with_multicast_ttl(1)
    
    // 其他选项
    .with_ipv6_only(false)
    .with_freebind(true);

let socket = UdpSocket::with_config("127.0.0.1:0", config).await?;
```

### 环境变量配置

```bash
# TCP配置
export C10_TCP_KEEP_ALIVE=true
export C10_TCP_NODELAY=true
export C10_TCP_CONNECTION_TIMEOUT=30000
export C10_TCP_READ_TIMEOUT=30000
export C10_TCP_WRITE_TIMEOUT=30000
export C10_TCP_RECV_BUFFER_SIZE=8192
export C10_TCP_SEND_BUFFER_SIZE=8192

# UDP配置
export C10_UDP_READ_TIMEOUT=30000
export C10_UDP_WRITE_TIMEOUT=30000
export C10_UDP_RECV_BUFFER_SIZE=8192
export C10_UDP_SEND_BUFFER_SIZE=8192
export C10_UDP_BROADCAST=true
export C10_UDP_MULTICAST_LOOP=true
```

## 🔍 错误处理

### 错误类型

```rust
use c10_networks::error::{NetworkError, NetworkResult};

async fn handle_socket_errors() -> NetworkResult<()> {
    let mut client = TcpClient::connect("127.0.0.1:8080").await?;
    
    loop {
        match client.read(&mut [0; 1024]).await {
            Ok(0) => {
                println!("连接正常关闭");
                break;
            }
            Ok(n) => {
                println!("收到数据: {} 字节", n);
            }
            Err(NetworkError::ConnectionClosed) => {
                println!("连接被关闭");
                break;
            }
            Err(NetworkError::Timeout) => {
                println!("读取超时");
                break;
            }
            Err(NetworkError::ConnectionRefused) => {
                println!("连接被拒绝");
                break;
            }
            Err(NetworkError::NetworkUnreachable) => {
                println!("网络不可达");
                break;
            }
            Err(e) => {
                eprintln!("其他错误: {}", e);
                break;
            }
        }
    }
    
    Ok(())
}
```

### 重连机制

```rust
use c10_networks::socket::tcp::TcpClient;
use std::time::Duration;

struct ReconnectingTcpClient {
    address: String,
    max_retries: usize,
    retry_delay: Duration,
    backoff_multiplier: f64,
}

impl ReconnectingTcpClient {
    fn new(address: String) -> Self {
        Self {
            address,
            max_retries: 5,
            retry_delay: Duration::from_secs(1),
            backoff_multiplier: 2.0,
        }
    }
    
    async fn connect_with_retry(&self) -> NetworkResult<TcpClient> {
        let mut delay = self.retry_delay;
        
        for attempt in 1..=self.max_retries {
            match TcpClient::connect(&self.address).await {
                Ok(client) => {
                    println!("连接成功 (尝试 {})", attempt);
                    return Ok(client);
                }
                Err(e) => {
                    eprintln!("连接失败 (尝试 {}): {}", attempt, e);
                    
                    if attempt < self.max_retries {
                        println!("{}秒后重试...", delay.as_secs());
                        tokio::time::sleep(delay).await;
                        delay = Duration::from_secs_f64(
                            delay.as_secs_f64() * self.backoff_multiplier
                        );
                    } else {
                        return Err(e);
                    }
                }
            }
        }
        
        Err(NetworkError::ConnectionFailed)
    }
}

// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let reconnecting_client = ReconnectingTcpClient::new(
        "127.0.0.1:8080".to_string()
    );
    
    let mut client = reconnecting_client.connect_with_retry().await?;
    
    // 使用客户端...
    
    Ok(())
}
```

## 📈 性能优化

### 连接复用

```rust
use c10_networks::socket::tcp::{TcpClient, TcpConfig};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

struct ConnectionManager {
    connections: Arc<Mutex<HashMap<String, Vec<TcpClient>>>>,
    max_connections_per_host: usize,
    config: TcpConfig,
}

impl ConnectionManager {
    fn new(max_connections_per_host: usize, config: TcpConfig) -> Self {
        Self {
            connections: Arc::new(Mutex::new(HashMap::new())),
            max_connections_per_host,
            config,
        }
    }
    
    async fn get_connection(&self, address: &str) -> NetworkResult<TcpClient> {
        let mut connections = self.connections.lock().await;
        
        // 尝试从现有连接中获取
        if let Some(host_connections) = connections.get_mut(address) {
            if let Some(connection) = host_connections.pop() {
                return Ok(connection);
            }
        }
        
        // 创建新连接
        TcpClient::connect_with_config(address, self.config.clone()).await
    }
    
    async fn return_connection(&self, address: String, connection: TcpClient) {
        let mut connections = self.connections.lock().await;
        
        let host_connections = connections.entry(address).or_insert_with(Vec::new);
        
        if host_connections.len() < self.max_connections_per_host {
            host_connections.push(connection);
        }
        // 如果已达到最大连接数，丢弃连接
    }
}

// 使用示例
async fn use_connection_manager() -> NetworkResult<()> {
    let config = TcpConfig::new()
        .with_keep_alive(true)
        .with_nodelay(true);
    
    let manager = ConnectionManager::new(10, config);
    
    // 获取连接
    let mut connection = manager.get_connection("127.0.0.1:8080").await?;
    
    // 使用连接
    connection.write_all(b"Hello").await?;
    
    // 归还连接
    manager.return_connection("127.0.0.1:8080".to_string(), connection).await;
    
    Ok(())
}
```

### 批量操作

```rust
use c10_networks::socket::tcp::TcpClient;
use futures::future::join_all;

async fn batch_operations() -> NetworkResult<()> {
    let addresses = vec![
        "127.0.0.1:8080",
        "127.0.0.1:8081",
        "127.0.0.1:8082",
    ];
    
    // 并发连接
    let connection_futures: Vec<_> = addresses
        .into_iter()
        .map(|addr| TcpClient::connect(addr))
        .collect();
    
    let connections = join_all(connection_futures).await;
    
    // 并发发送数据
    let send_futures: Vec<_> = connections
        .into_iter()
        .map(|mut conn| async move {
            conn.write_all(b"Hello").await
        })
        .collect();
    
    let results = join_all(send_futures).await;
    
    // 处理结果
    for result in results {
        match result {
            Ok(_) => println!("发送成功"),
            Err(e) => eprintln!("发送失败: {}", e),
        }
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
    use c10_networks::socket::tcp::{TcpServer, TcpClient};
    use c10_networks::socket::udp::{UdpServer, UdpSocket};

    #[tokio::test]
    async fn test_tcp_server_creation() {
        let server = TcpServer::bind("127.0.0.1:0").await.unwrap();
        assert!(server.is_bound());
    }

    #[tokio::test]
    async fn test_tcp_client_connection() {
        // 启动测试服务器
        let server = TcpServer::bind("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        // 启动服务器任务
        let server_task = tokio::spawn(async move {
            let (mut stream, _) = server.accept().await.unwrap();
            
            // 回显数据
            let mut buffer = [0; 1024];
            let n = stream.read(&mut buffer).await.unwrap();
            stream.write_all(&buffer[..n]).await.unwrap();
        });
        
        // 连接客户端
        let mut client = TcpClient::connect(&format!("127.0.0.1:{}", server_addr.port())).await.unwrap();
        
        // 发送数据
        client.write_all(b"Hello").await.unwrap();
        
        // 接收响应
        let mut buffer = [0; 1024];
        let n = client.read(&mut buffer).await.unwrap();
        assert_eq!(&buffer[..n], b"Hello");
        
        // 等待服务器任务完成
        server_task.await.unwrap();
    }

    #[tokio::test]
    async fn test_udp_server_creation() {
        let server = UdpServer::bind("127.0.0.1:0").await.unwrap();
        assert!(server.is_bound());
    }

    #[tokio::test]
    async fn test_udp_message_exchange() {
        // 启动测试服务器
        let server = UdpServer::bind("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        // 启动服务器任务
        let server_task = tokio::spawn(async move {
            let mut buffer = [0; 1024];
            let (n, addr) = server.recv_from(&mut buffer).await.unwrap();
            server.send_to(&buffer[..n], addr).await.unwrap();
        });
        
        // 创建客户端
        let client = UdpSocket::bind("127.0.0.1:0").await.unwrap();
        
        // 发送数据
        client.send_to(b"Hello", &format!("127.0.0.1:{}", server_addr.port())).await.unwrap();
        
        // 接收响应
        let mut buffer = [0; 1024];
        let (n, _) = client.recv_from(&mut buffer).await.unwrap();
        assert_eq!(&buffer[..n], b"Hello");
        
        // 等待服务器任务完成
        server_task.await.unwrap();
    }
}
```

### 集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use c10_networks::socket::tcp::{TcpServer, TcpClient};

    #[tokio::test]
    async fn test_tcp_echo_server() {
        // 启动回显服务器
        let server = TcpServer::bind("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        let server_task = tokio::spawn(async move {
            loop {
                let (mut stream, _) = server.accept().await.unwrap();
                
                tokio::spawn(async move {
                    let mut buffer = [0; 1024];
                    
                    loop {
                        match stream.read(&mut buffer).await {
                            Ok(0) => break,
                            Ok(n) => {
                                stream.write_all(&buffer[..n]).await.unwrap();
                            }
                            Err(_) => break,
                        }
                    }
                });
            }
        });
        
        // 测试多个客户端
        let client_count = 5;
        let mut client_tasks = Vec::new();
        
        for i in 0..client_count {
            let server_addr = server_addr;
            let task = tokio::spawn(async move {
                let mut client = TcpClient::connect(&format!("127.0.0.1:{}", server_addr.port())).await.unwrap();
                
                let message = format!("Message from client {}", i);
                client.write_all(message.as_bytes()).await.unwrap();
                
                let mut buffer = [0; 1024];
                let n = client.read(&mut buffer).await.unwrap();
                let response = String::from_utf8_lossy(&buffer[..n]);
                
                assert_eq!(response, message);
            });
            
            client_tasks.push(task);
        }
        
        // 等待所有客户端完成
        for task in client_tasks {
            task.await.unwrap();
        }
        
        // 停止服务器
        server_task.abort();
    }

    #[tokio::test]
    async fn test_tcp_connection_pool() {
        // 启动测试服务器
        let server = TcpServer::bind("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        let server_task = tokio::spawn(async move {
            let mut connection_count = 0;
            
            loop {
                let (mut stream, _) = server.accept().await.unwrap();
                connection_count += 1;
                
                tokio::spawn(async move {
                    let mut buffer = [0; 1024];
                    let n = stream.read(&mut buffer).await.unwrap();
                    stream.write_all(&buffer[..n]).await.unwrap();
                });
                
                if connection_count >= 10 {
                    break;
                }
            }
        });
        
        // 测试连接池
        let config = TcpConfig::new().with_keep_alive(true);
        let pool = TcpConnectionPool::new(
            format!("127.0.0.1:{}", server_addr.port()),
            5,
            config
        );
        
        // 获取多个连接
        let mut connections = Vec::new();
        for _ in 0..5 {
            let connection = pool.get_connection().await.unwrap();
            connections.push(connection);
        }
        
        // 使用连接
        for (i, mut connection) in connections.into_iter().enumerate() {
            let message = format!("Message {}", i);
            connection.write_all(message.as_bytes()).await.unwrap();
            
            let mut buffer = [0; 1024];
            let n = connection.read(&mut buffer).await.unwrap();
            let response = String::from_utf8_lossy(&buffer[..n]);
            
            assert_eq!(response, message);
            
            // 归还连接
            pool.return_connection(connection).await;
        }
        
        // 等待服务器任务完成
        server_task.await.unwrap();
    }
}
```

### 性能测试

```rust
#[cfg(test)]
mod performance_tests {
    use super::*;
    use c10_networks::socket::tcp::{TcpServer, TcpClient};
    use std::time::Instant;

    #[tokio::test]
    async fn test_tcp_throughput() {
        // 启动服务器
        let server = TcpServer::bind("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        let server_task = tokio::spawn(async move {
            let (mut stream, _) = server.accept().await.unwrap();
            
            // 回显所有数据
            let mut buffer = [0; 1024];
            loop {
                match stream.read(&mut buffer).await {
                    Ok(0) => break,
                    Ok(n) => {
                        stream.write_all(&buffer[..n]).await.unwrap();
                    }
                    Err(_) => break,
                }
            }
        });
        
        // 连接客户端
        let mut client = TcpClient::connect(&format!("127.0.0.1:{}", server_addr.port())).await.unwrap();
        
        // 性能测试
        let message_count = 1000;
        let start = Instant::now();
        
        for i in 0..message_count {
            let message = format!("Message {}", i);
            client.write_all(message.as_bytes()).await.unwrap();
            
            let mut buffer = [0; 1024];
            let n = client.read(&mut buffer).await.unwrap();
            let response = String::from_utf8_lossy(&buffer[..n]);
            
            assert_eq!(response, message);
        }
        
        let duration = start.elapsed();
        let throughput = message_count as f64 / duration.as_secs_f64();
        
        println!("发送 {} 条消息耗时: {:?}", message_count, duration);
        println!("吞吐量: {:.2} 消息/秒", throughput);
        
        // 断言性能要求
        assert!(throughput > 100.0); // 至少100消息/秒
        
        // 等待服务器任务完成
        server_task.await.unwrap();
    }

    #[tokio::test]
    async fn test_tcp_concurrent_connections() {
        // 启动服务器
        let server = TcpServer::bind("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        let server_task = tokio::spawn(async move {
            let mut connection_count = 0;
            
            loop {
                let (mut stream, _) = server.accept().await.unwrap();
                connection_count += 1;
                
                tokio::spawn(async move {
                    let mut buffer = [0; 1024];
                    let n = stream.read(&mut buffer).await.unwrap();
                    stream.write_all(&buffer[..n]).await.unwrap();
                });
                
                if connection_count >= 20 {
                    break;
                }
            }
        });
        
        // 创建多个并发连接
        let connection_count = 20;
        let mut client_tasks = Vec::new();
        
        for i in 0..connection_count {
            let server_addr = server_addr;
            let task = tokio::spawn(async move {
                let mut client = TcpClient::connect(&format!("127.0.0.1:{}", server_addr.port())).await.unwrap();
                
                let message = format!("Message from client {}", i);
                client.write_all(message.as_bytes()).await.unwrap();
                
                let mut buffer = [0; 1024];
                let n = client.read(&mut buffer).await.unwrap();
                let response = String::from_utf8_lossy(&buffer[..n]);
                
                assert_eq!(response, message);
            });
            
            client_tasks.push(task);
        }
        
        // 等待所有客户端完成
        let start = Instant::now();
        for task in client_tasks {
            task.await.unwrap();
        }
        let duration = start.elapsed();
        
        println!("{} 个并发连接测试耗时: {:?}", connection_count, duration);
        
        // 等待服务器任务完成
        server_task.await.unwrap();
    }
}
```

## ❓ 常见问题

### Q: 如何设置TCP套接字选项？

A: 使用 `TcpConfig` 配置各种TCP选项，如 `with_keep_alive()`、`with_nodelay()` 等。

### Q: 如何处理UDP丢包？

A: 实现应用层重传机制，或使用可靠的UDP协议如QUIC。

### Q: 如何优化TCP性能？

A: 启用 `TCP_NODELAY`、调整缓冲区大小、使用连接池。

### Q: 如何实现UDP广播？

A: 使用 `UdpConfig::with_broadcast(true)` 启用广播功能。

### Q: 如何处理网络超时？

A: 使用 `with_read_timeout()` 和 `with_write_timeout()` 设置超时时间。

### Q: 如何实现连接池？

A: 使用 `TcpConnectionPool` 或自定义连接管理器。

### Q: 如何监控套接字状态？

A: 使用 `SocketMonitor` 监控连接状态和统计信息。

### Q: 如何优化UDP性能？

A: 调整缓冲区大小、启用广播/多播、使用批量操作。

---

**TCP/UDP套接字指南完成！** 🎉

现在您已经掌握了C10 Networks套接字的完整用法，可以构建高性能的网络应用程序了。

*最后更新: 2025年1月*  
*文档版本: v1.0*  
*维护者: C10 Networks 开发团队*
