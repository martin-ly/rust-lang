# C10 Networks 示例代码与应用场景增强版

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`DOCUMENTATION_STANDARDS.md`](DOCUMENTATION_STANDARDS.md)。

## 📊 目录

- [C10 Networks 示例代码与应用场景增强版](#c10-networks-示例代码与应用场景增强版)
  - [📊 目录](#-目录)
  - [🎯 概述](#-概述)
    - [1. 示例分类](#1-示例分类)
    - [2. 学习路径](#2-学习路径)
    - [3. 最佳实践](#3-最佳实践)
  - [🚀 基础示例](#-基础示例)
    - [1. TCP客户端-服务器](#1-tcp客户端-服务器)
      - [1.1 基础TCP服务器](#11-基础tcp服务器)
      - [1.2 异步TCP服务器](#12-异步tcp服务器)
      - [1.3 TCP客户端](#13-tcp客户端)
      - [1.4 连接池管理](#14-连接池管理)
    - [2. HTTP客户端-服务器](#2-http客户端-服务器)
      - [2.1 HTTP服务器](#21-http服务器)
      - [2.2 HTTP客户端](#22-http客户端)
    - [3. WebSocket通信](#3-websocket通信)
      - [3.1 WebSocket服务器](#31-websocket服务器)
    - [4. UDP通信](#4-udp通信)
      - [4.1 UDP服务器](#41-udp服务器)
  - [🔧 高级示例](#-高级示例)
    - [1. 异步网络编程](#1-异步网络编程)
      - [1.1 异步任务调度](#11-异步任务调度)
  - [🔗 相关文档](#-相关文档)

[![Rust](https://img.shields.io/badge/rust-1.90+-orange.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](../../LICENSE)
[![Crates.io](https://img.shields.io/crates/v/c10_networks.svg)](https://crates.io/crates/c10_networks)

## 🎯 概述

本文档提供了C10 Networks项目的全面示例代码和实际应用场景，从基础网络编程到高级分布式系统，从性能优化到安全实践，为开发者提供完整的学习和实践指南。

### 1. 示例分类

示例代码按照以下分类组织：

- **基础示例**：TCP、HTTP、WebSocket、UDP等基础网络编程
- **高级示例**：异步编程、连接池、负载均衡、故障恢复等高级特性
- **实际应用**：微服务、实时数据流、分布式系统、云原生应用
- **性能优化**：内存、并发、网络、协议等性能优化技术
- **安全示例**：TLS、认证、访问控制、安全监控等安全实践
- **测试示例**：单元测试、集成测试、性能测试、压力测试

### 2. 学习路径

建议的学习路径：

1. **基础阶段**：从TCP客户端-服务器开始，掌握基本网络编程
2. **进阶阶段**：学习异步编程和高级网络特性
3. **应用阶段**：实践微服务和分布式系统开发
4. **优化阶段**：掌握性能优化和安全实践
5. **测试阶段**：学习各种测试方法和工具

### 3. 最佳实践

所有示例都遵循以下最佳实践：

- **错误处理**：完整的错误处理和恢复机制
- **资源管理**：正确的资源分配和释放
- **性能考虑**：高效的算法和数据结构
- **安全实践**：安全的编程模式和配置
- **可维护性**：清晰的代码结构和文档

## 🚀 基础示例

### 1. TCP客户端-服务器

#### 1.1 基础TCP服务器

```rust
use c10_networks::protocol::tcp::TcpServer;
use c10_networks::error::NetworkResult;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use std::sync::Arc;

/// 基础TCP服务器实现
pub struct BasicTcpServer {
    listener: TcpListener,
    handler: Arc<dyn Fn(TcpStream) -> NetworkResult<()> + Send + Sync>,
}

impl BasicTcpServer {
    /// 创建新的TCP服务器
    pub async fn new<F>(addr: &str, handler: F) -> NetworkResult<Self>
    where
        F: Fn(TcpStream) -> NetworkResult<()> + Send + Sync + 'static,
    {
        let listener = TcpListener::bind(addr).await?;
        Ok(Self {
            listener,
            handler: Arc::new(handler),
        })
    }

    /// 启动服务器
    pub async fn run(&self) -> NetworkResult<()> {
        println!("TCP服务器启动在: {}", self.listener.local_addr()?);
        
        loop {
            let (stream, addr) = self.listener.accept().await?;
            println!("新连接来自: {}", addr);
            
            let handler = self.handler.clone();
            tokio::spawn(async move {
                if let Err(e) = handler(stream) {
                    eprintln!("处理连接时出错: {}", e);
                }
            });
        }
    }
}

/// 回显处理器
pub async fn echo_handler(mut stream: TcpStream) -> NetworkResult<()> {
    let mut buffer = [0; 1024];
    
    loop {
        let n = stream.read(&mut buffer).await?;
        if n == 0 {
            break; // 连接关闭
        }
        
        // 回显数据
        stream.write_all(&buffer[..n]).await?;
    }
    
    Ok(())
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let server = BasicTcpServer::new("127.0.0.1:8080", |stream| {
        Box::pin(echo_handler(stream))
    }).await?;
    
    server.run().await
}
```

#### 1.2 异步TCP服务器

```rust
use c10_networks::protocol::tcp::AsyncTcpServer;
use c10_networks::error::NetworkResult;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use tokio::sync::mpsc;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 异步TCP服务器
pub struct AsyncTcpServer {
    connections: Arc<RwLock<HashMap<String, mpsc::UnboundedSender<Vec<u8>>>>>,
}

impl AsyncTcpServer {
    pub fn new() -> Self {
        Self {
            connections: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 处理新连接
    pub async fn handle_connection(&self, mut stream: TcpStream) -> NetworkResult<()> {
        let addr = stream.peer_addr()?.to_string();
        let (tx, mut rx) = mpsc::unbounded_channel();
        
        // 注册连接
        {
            let mut connections = self.connections.write().await;
            connections.insert(addr.clone(), tx);
        }
        
        // 启动读取任务
        let connections = self.connections.clone();
        let addr_clone = addr.clone();
        let read_task = tokio::spawn(async move {
            let mut buffer = [0; 1024];
            loop {
                match stream.read(&mut buffer).await {
                    Ok(0) => break, // 连接关闭
                    Ok(n) => {
                        // 广播消息给所有连接
                        let connections = connections.read().await;
                        for (other_addr, sender) in connections.iter() {
                            if *other_addr != addr_clone {
                                let _ = sender.send(buffer[..n].to_vec());
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("读取错误: {}", e);
                        break;
                    }
                }
            }
            
            // 移除连接
            let mut connections = connections.write().await;
            connections.remove(&addr_clone);
        });
        
        // 启动写入任务
        let write_task = tokio::spawn(async move {
            while let Some(data) = rx.recv().await {
                if stream.write_all(&data).await.is_err() {
                    break;
                }
            }
        });
        
        // 等待任务完成
        tokio::select! {
            _ = read_task => {},
            _ = write_task => {},
        }
        
        Ok(())
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    use tokio::net::TcpListener;
    
    let server = AsyncTcpServer::new();
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    
    println!("异步TCP服务器启动在: {}", listener.local_addr()?);
    
    loop {
        let (stream, addr) = listener.accept().await?;
        println!("新连接: {}", addr);
        
        let server = server.clone();
        tokio::spawn(async move {
            if let Err(e) = server.handle_connection(stream).await {
                eprintln!("处理连接错误: {}", e);
            }
        });
    }
}
```

#### 1.3 TCP客户端

```rust
use c10_networks::protocol::tcp::TcpClient;
use c10_networks::error::NetworkResult;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use std::time::Duration;

/// TCP客户端
pub struct TcpClient {
    stream: Option<TcpStream>,
    addr: String,
}

impl TcpClient {
    /// 创建新的TCP客户端
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

    /// 发送数据
    pub async fn send(&mut self, data: &[u8]) -> NetworkResult<()> {
        if let Some(stream) = &mut self.stream {
            stream.write_all(data).await?;
            Ok(())
        } else {
            Err(c10_networks::error::NetworkError::NotConnected)
        }
    }

    /// 接收数据
    pub async fn receive(&mut self) -> NetworkResult<Vec<u8>> {
        if let Some(stream) = &mut self.stream {
            let mut buffer = vec![0; 1024];
            let n = stream.read(&mut buffer).await?;
            Ok(buffer[..n].to_vec())
        } else {
            Err(c10_networks::error::NetworkError::NotConnected)
        }
    }

    /// 发送并接收数据
    pub async fn send_and_receive(&mut self, data: &[u8]) -> NetworkResult<Vec<u8>> {
        self.send(data).await?;
        self.receive().await
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
    let mut client = TcpClient::new("127.0.0.1:8080");
    
    // 连接服务器
    client.connect().await?;
    
    // 发送数据
    let message = b"Hello, Server!";
    client.send(message).await?;
    
    // 接收响应
    let response = client.receive().await?;
    println!("服务器响应: {}", String::from_utf8_lossy(&response));
    
    // 断开连接
    client.disconnect().await?;
    
    Ok(())
}
```

#### 1.4 连接池管理

```rust
use c10_networks::protocol::tcp::ConnectionPool;
use c10_networks::error::NetworkResult;
use tokio::net::TcpStream;
use std::sync::Arc;
use tokio::sync::{Semaphore, Mutex};
use std::collections::VecDeque;
use std::time::{Duration, Instant};

/// 连接池配置
#[derive(Debug, Clone)]
pub struct PoolConfig {
    pub max_connections: usize,
    pub min_connections: usize,
    pub idle_timeout: Duration,
    pub connection_timeout: Duration,
}

impl Default for PoolConfig {
    fn default() -> Self {
        Self {
            max_connections: 10,
            min_connections: 2,
            idle_timeout: Duration::from_secs(300),
            connection_timeout: Duration::from_secs(30),
        }
    }
}

/// 连接信息
#[derive(Debug)]
struct ConnectionInfo {
    stream: TcpStream,
    created_at: Instant,
    last_used: Instant,
}

/// TCP连接池
pub struct TcpConnectionPool {
    config: PoolConfig,
    addr: String,
    connections: Arc<Mutex<VecDeque<ConnectionInfo>>>,
    semaphore: Arc<Semaphore>,
}

impl TcpConnectionPool {
    /// 创建新的连接池
    pub fn new(addr: &str, config: PoolConfig) -> Self {
        let semaphore = Arc::new(Semaphore::new(config.max_connections));
        
        Self {
            config,
            addr: addr.to_string(),
            connections: Arc::new(Mutex::new(VecDeque::new())),
            semaphore,
        }
    }

    /// 获取连接
    pub async fn get_connection(&self) -> NetworkResult<PooledConnection> {
        // 获取信号量
        let _permit = self.semaphore.acquire().await
            .map_err(|_| c10_networks::error::NetworkError::PoolExhausted)?;

        // 尝试从池中获取连接
        {
            let mut connections = self.connections.lock().await;
            
            // 清理过期连接
            self.cleanup_expired_connections(&mut connections).await;
            
            // 查找可用连接
            while let Some(mut conn_info) = connections.pop_front() {
                if self.is_connection_healthy(&conn_info).await {
                    conn_info.last_used = Instant::now();
                    return Ok(PooledConnection {
                        stream: Some(conn_info.stream),
                        pool: self.clone(),
                    });
                }
            }
        }

        // 创建新连接
        let stream = tokio::time::timeout(
            self.config.connection_timeout,
            TcpStream::connect(&self.addr)
        ).await??;

        Ok(PooledConnection {
            stream: Some(stream),
            pool: self.clone(),
        })
    }

    /// 检查连接健康状态
    async fn is_connection_healthy(&self, conn_info: &ConnectionInfo) -> bool {
        // 检查连接是否过期
        if conn_info.last_used.elapsed() > self.config.idle_timeout {
            return false;
        }

        // 这里可以添加更多的健康检查逻辑
        // 例如：发送ping消息、检查连接状态等
        
        true
    }

    /// 清理过期连接
    async fn cleanup_expired_connections(&self, connections: &mut VecDeque<ConnectionInfo>) {
        let now = Instant::now();
        connections.retain(|conn| {
            now.duration_since(conn.last_used) <= self.config.idle_timeout
        });
    }

    /// 归还连接到池中
    async fn return_connection(&self, mut conn_info: ConnectionInfo) {
        conn_info.last_used = Instant::now();
        
        let mut connections = self.connections.lock().await;
        connections.push_back(conn_info);
    }
}

impl Clone for TcpConnectionPool {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            addr: self.addr.clone(),
            connections: self.connections.clone(),
            semaphore: self.semaphore.clone(),
        }
    }
}

/// 池化连接
pub struct PooledConnection {
    stream: Option<TcpStream>,
    pool: TcpConnectionPool,
}

impl PooledConnection {
    /// 获取底层流
    pub fn stream(&mut self) -> Option<&mut TcpStream> {
        self.stream.as_mut()
    }
}

impl Drop for PooledConnection {
    fn drop(&mut self) {
        if let Some(stream) = self.stream.take() {
            let conn_info = ConnectionInfo {
                stream,
                created_at: Instant::now(),
                last_used: Instant::now(),
            };
            
            let pool = self.pool.clone();
            tokio::spawn(async move {
                pool.return_connection(conn_info).await;
            });
        }
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let config = PoolConfig {
        max_connections: 5,
        min_connections: 1,
        idle_timeout: Duration::from_secs(60),
        connection_timeout: Duration::from_secs(10),
    };
    
    let pool = TcpConnectionPool::new("127.0.0.1:8080", config);
    
    // 并发使用连接池
    let mut handles = vec![];
    for i in 0..10 {
        let pool = pool.clone();
        let handle = tokio::spawn(async move {
            let mut conn = pool.get_connection().await?;
            if let Some(stream) = conn.stream() {
                use tokio::io::AsyncWriteExt;
                let message = format!("Message {}", i);
                stream.write_all(message.as_bytes()).await?;
            }
            Ok::<(), NetworkResult<()>>(())
        });
        handles.push(handle);
    }
    
    // 等待所有任务完成
    for handle in handles {
        handle.await??;
    }
    
    Ok(())
}
```

### 2. HTTP客户端-服务器

#### 2.1 HTTP服务器

```rust
use c10_networks::protocol::http::{HttpServer, HttpRequest, HttpResponse, HttpMethod, HttpStatusCode};
use c10_networks::error::NetworkResult;
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::collections::HashMap;
use std::sync::Arc;

/// HTTP服务器
pub struct HttpServer {
    routes: Arc<HashMap<String, Box<dyn Fn(HttpRequest) -> HttpResponse + Send + Sync>>>,
}

impl HttpServer {
    /// 创建新的HTTP服务器
    pub fn new() -> Self {
        Self {
            routes: Arc::new(HashMap::new()),
        }
    }

    /// 添加路由
    pub fn add_route<F>(&mut self, path: &str, handler: F)
    where
        F: Fn(HttpRequest) -> HttpResponse + Send + Sync + 'static,
    {
        let mut routes = Arc::get_mut(&mut self.routes).unwrap();
        routes.insert(path.to_string(), Box::new(handler));
    }

    /// 启动服务器
    pub async fn run(&self, addr: &str) -> NetworkResult<()> {
        let listener = TcpListener::bind(addr).await?;
        println!("HTTP服务器启动在: {}", addr);

        loop {
            let (stream, _) = listener.accept().await?;
            let routes = self.routes.clone();
            
            tokio::spawn(async move {
                if let Err(e) = Self::handle_connection(stream, routes).await {
                    eprintln!("处理HTTP连接错误: {}", e);
                }
            });
        }
    }

    /// 处理HTTP连接
    async fn handle_connection(
        mut stream: TcpStream,
        routes: Arc<HashMap<String, Box<dyn Fn(HttpRequest) -> HttpResponse + Send + Sync>>>,
    ) -> NetworkResult<()> {
        let mut buffer = [0; 8192];
        let n = stream.read(&mut buffer).await?;
        
        // 解析HTTP请求
        let request_str = String::from_utf8_lossy(&buffer[..n]);
        let request = HttpRequest::parse(&request_str)?;
        
        // 查找路由处理器
        let response = if let Some(handler) = routes.get(&request.path) {
            handler(request)
        } else {
            // 404 Not Found
            HttpResponse::new(HttpStatusCode::NotFound)
                .with_body("404 Not Found".as_bytes().to_vec())
        };

        // 发送HTTP响应
        let response_str = response.to_string();
        stream.write_all(response_str.as_bytes()).await?;
        
        Ok(())
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let mut server = HttpServer::new();
    
    // 添加路由
    server.add_route("/", |_| {
        HttpResponse::new(HttpStatusCode::OK)
            .with_body("Hello, World!".as_bytes().to_vec())
    });
    
    server.add_route("/api/users", |request| {
        match request.method {
            HttpMethod::GET => {
                HttpResponse::new(HttpStatusCode::OK)
                    .with_body(r#"{"users": ["Alice", "Bob", "Charlie"]}"#.as_bytes().to_vec())
            }
            HttpMethod::POST => {
                HttpResponse::new(HttpStatusCode::Created)
                    .with_body(r#"{"message": "User created"}"#.as_bytes().to_vec())
            }
            _ => {
                HttpResponse::new(HttpStatusCode::MethodNotAllowed)
                    .with_body("Method Not Allowed".as_bytes().to_vec())
            }
        }
    });
    
    // 启动服务器
    server.run("127.0.0.1:8080").await
}
```

#### 2.2 HTTP客户端

```rust
use c10_networks::protocol::http::{HttpClient, HttpRequest, HttpResponse, HttpMethod};
use c10_networks::error::NetworkResult;
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::collections::HashMap;

/// HTTP客户端
pub struct HttpClient {
    base_url: String,
    default_headers: HashMap<String, String>,
}

impl HttpClient {
    /// 创建新的HTTP客户端
    pub fn new(base_url: &str) -> Self {
        Self {
            base_url: base_url.to_string(),
            default_headers: HashMap::new(),
        }
    }

    /// 设置默认头部
    pub fn set_default_header(&mut self, name: &str, value: &str) {
        self.default_headers.insert(name.to_string(), value.to_string());
    }

    /// 发送HTTP请求
    pub async fn send_request(&self, request: HttpRequest) -> NetworkResult<HttpResponse> {
        let url = format!("{}{}", self.base_url, request.path);
        let host = self.extract_host(&url)?;
        let port = self.extract_port(&url)?;

        // 连接到服务器
        let mut stream = TcpStream::connect(format!("{}:{}", host, port)).await?;

        // 构建HTTP请求
        let mut http_request = request;
        http_request.headers.extend(self.default_headers.clone());
        http_request.headers.insert("Host".to_string(), host);

        // 发送请求
        let request_str = http_request.to_string();
        stream.write_all(request_str.as_bytes()).await?;

        // 读取响应
        let mut buffer = Vec::new();
        stream.read_to_end(&mut buffer).await?;

        // 解析响应
        let response_str = String::from_utf8_lossy(&buffer);
        HttpResponse::parse(&response_str)
    }

    /// GET请求
    pub async fn get(&self, path: &str) -> NetworkResult<HttpResponse> {
        let request = HttpRequest {
            method: HttpMethod::GET,
            path: path.to_string(),
            headers: HashMap::new(),
            body: Vec::new(),
        };
        self.send_request(request).await
    }

    /// POST请求
    pub async fn post(&self, path: &str, body: &[u8]) -> NetworkResult<HttpResponse> {
        let mut request = HttpRequest {
            method: HttpMethod::POST,
            path: path.to_string(),
            headers: HashMap::new(),
            body: body.to_vec(),
        };
        request.headers.insert("Content-Length".to_string(), body.len().to_string());
        self.send_request(request).await
    }

    /// 提取主机名
    fn extract_host(&self, url: &str) -> NetworkResult<String> {
        if let Some(start) = url.find("://") {
            let url = &url[start + 3..];
            if let Some(end) = url.find('/') {
                let host = &url[..end];
                if let Some(colon) = host.find(':') {
                    Ok(host[..colon].to_string())
                } else {
                    Ok(host.to_string())
                }
            } else {
                Ok(url.to_string())
            }
        } else {
            Err(c10_networks::error::NetworkError::InvalidUrl)
        }
    }

    /// 提取端口号
    fn extract_port(&self, url: &str) -> NetworkResult<u16> {
        if let Some(start) = url.find("://") {
            let url = &url[start + 3..];
            if let Some(end) = url.find('/') {
                let host = &url[..end];
                if let Some(colon) = host.find(':') {
                    let port_str = &host[colon + 1..];
                    port_str.parse().map_err(|_| c10_networks::error::NetworkError::InvalidUrl)
                } else {
                    Ok(80) // 默认HTTP端口
                }
            } else {
                Ok(80)
            }
        } else {
            Ok(80)
        }
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let mut client = HttpClient::new("http://127.0.0.1:8080");
    client.set_default_header("User-Agent", "C10-Networks-Client/1.0");

    // GET请求
    let response = client.get("/").await?;
    println!("GET响应: {}", response.status);
    println!("响应体: {}", String::from_utf8_lossy(&response.body));

    // POST请求
    let data = r#"{"name": "Alice", "email": "alice@example.com"}"#;
    let response = client.post("/api/users", data.as_bytes()).await?;
    println!("POST响应: {}", response.status);
    println!("响应体: {}", String::from_utf8_lossy(&response.body));

    Ok(())
}
```

### 3. WebSocket通信

#### 3.1 WebSocket服务器

```rust
use c10_networks::protocol::websocket::{WebSocketServer, WebSocketFrame, WebSocketOpcode};
use c10_networks::error::NetworkResult;
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{Mutex, mpsc};

/// WebSocket服务器
pub struct WebSocketServer {
    clients: Arc<Mutex<HashMap<String, mpsc::UnboundedSender<WebSocketFrame>>>>,
}

impl WebSocketServer {
    /// 创建新的WebSocket服务器
    pub fn new() -> Self {
        Self {
            clients: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// 启动服务器
    pub async fn run(&self, addr: &str) -> NetworkResult<()> {
        let listener = TcpListener::bind(addr).await?;
        println!("WebSocket服务器启动在: {}", addr);

        loop {
            let (stream, addr) = listener.accept().await?;
            let clients = self.clients.clone();
            
            tokio::spawn(async move {
                if let Err(e) = Self::handle_connection(stream, addr.to_string(), clients).await {
                    eprintln!("处理WebSocket连接错误: {}", e);
                }
            });
        }
    }

    /// 处理WebSocket连接
    async fn handle_connection(
        mut stream: TcpStream,
        client_id: String,
        clients: Arc<Mutex<HashMap<String, mpsc::UnboundedSender<WebSocketFrame>>>>,
    ) -> NetworkResult<()> {
        // WebSocket握手
        let mut buffer = [0; 1024];
        let n = stream.read(&mut buffer).await?;
        let request = String::from_utf8_lossy(&buffer[..n]);
        
        if let Some(response) = Self::handle_handshake(&request) {
            stream.write_all(response.as_bytes()).await?;
        } else {
            return Err(c10_networks::error::NetworkError::WebSocketHandshakeFailed);
        }

        // 创建客户端通道
        let (tx, mut rx) = mpsc::unbounded_channel();
        {
            let mut clients = clients.lock().await;
            clients.insert(client_id.clone(), tx);
        }

        // 启动读取任务
        let clients_clone = clients.clone();
        let client_id_clone = client_id.clone();
        let read_task = tokio::spawn(async move {
            let mut buffer = [0; 1024];
            loop {
                match stream.read(&mut buffer).await {
                    Ok(0) => break, // 连接关闭
                    Ok(n) => {
                        if let Ok(frame) = WebSocketFrame::parse(&buffer[..n]) {
                            // 处理不同类型的帧
                            match frame.opcode {
                                WebSocketOpcode::Text | WebSocketOpcode::Binary => {
                                    // 广播消息给其他客户端
                                    let clients = clients_clone.lock().await;
                                    for (id, sender) in clients.iter() {
                                        if *id != client_id_clone {
                                            let _ = sender.send(frame.clone());
                                        }
                                    }
                                }
                                WebSocketOpcode::Close => {
                                    break; // 关闭连接
                                }
                                WebSocketOpcode::Ping => {
                                    // 发送Pong响应
                                    let pong_frame = WebSocketFrame {
                                        fin: true,
                                        opcode: WebSocketOpcode::Pong,
                                        mask: false,
                                        payload: frame.payload,
                                    };
                                    let clients = clients_clone.lock().await;
                                    if let Some(sender) = clients.get(&client_id_clone) {
                                        let _ = sender.send(pong_frame);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("读取WebSocket帧错误: {}", e);
                        break;
                    }
                }
            }
            
            // 移除客户端
            let mut clients = clients_clone.lock().await;
            clients.remove(&client_id_clone);
        });

        // 启动写入任务
        let write_task = tokio::spawn(async move {
            while let Some(frame) = rx.recv().await {
                let frame_data = frame.to_bytes();
                if stream.write_all(&frame_data).await.is_err() {
                    break;
                }
            }
        });

        // 等待任务完成
        tokio::select! {
            _ = read_task => {},
            _ = write_task => {},
        }

        Ok(())
    }

    /// 处理WebSocket握手
    fn handle_handshake(request: &str) -> Option<String> {
        // 查找WebSocket-Key
        if let Some(key_start) = request.find("Sec-WebSocket-Key: ") {
            let key_line = &request[key_start..];
            if let Some(key_end) = key_line.find("\r\n") {
                let key = &key_line[19..key_end];
                
                // 生成响应密钥
                let response_key = Self::generate_response_key(key);
                
                // 构建握手响应
                let response = format!(
                    "HTTP/1.1 101 Switching Protocols\r\n\
                     Upgrade: websocket\r\n\
                     Connection: Upgrade\r\n\
                     Sec-WebSocket-Accept: {}\r\n\r\n",
                    response_key
                );
                
                return Some(response);
            }
        }
        None
    }

    /// 生成响应密钥
    fn generate_response_key(key: &str) -> String {
        use sha1::{Digest, Sha1};
        use base64;
        
        const WEBSOCKET_MAGIC: &str = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
        let combined = format!("{}{}", key, WEBSOCKET_MAGIC);
        
        let mut hasher = Sha1::new();
        hasher.update(combined.as_bytes());
        let hash = hasher.finalize();
        
        base64::encode(&hash)
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let server = WebSocketServer::new();
    server.run("127.0.0.1:8080").await
}
```

### 4. UDP通信

#### 4.1 UDP服务器

```rust
use c10_networks::protocol::udp::UdpServer;
use c10_networks::error::NetworkResult;
use tokio::net::UdpSocket;
use std::net::SocketAddr;

/// UDP服务器
pub struct UdpServer {
    socket: UdpSocket,
}

impl UdpServer {
    /// 创建新的UDP服务器
    pub async fn new(addr: &str) -> NetworkResult<Self> {
        let socket = UdpSocket::bind(addr).await?;
        Ok(Self { socket })
    }

    /// 启动服务器
    pub async fn run(&self) -> NetworkResult<()> {
        println!("UDP服务器启动在: {}", self.socket.local_addr()?);
        
        let mut buffer = [0; 1024];
        
        loop {
            let (n, addr) = self.socket.recv_from(&mut buffer).await?;
            println!("收到来自 {} 的数据: {} 字节", addr, n);
            
            // 回显数据
            self.socket.send_to(&buffer[..n], addr).await?;
        }
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let server = UdpServer::new("127.0.0.1:8080").await?;
    server.run().await
}
```

## 🔧 高级示例

### 1. 异步网络编程

#### 1.1 异步任务调度

```rust
use c10_networks::protocol::async_traits::AsyncTaskScheduler;
use c10_networks::error::NetworkResult;
use tokio::sync::mpsc;
use tokio::time::{Duration, Instant};
use std::collections::BinaryHeap;
use std::cmp::Ordering;

/// 任务优先级
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TaskPriority {
    Low,
    Normal,
    High,
    Critical,
}

impl Ord for TaskPriority {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (TaskPriority::Critical, _) => Ordering::Greater,
            (_, TaskPriority::Critical) => Ordering::Less,
            (TaskPriority::High, _) => Ordering::Greater,
            (_, TaskPriority::High) => Ordering::Less,
            (TaskPriority::Normal, _) => Ordering::Greater,
            (_, TaskPriority::Normal) => Ordering::Less,
            (TaskPriority::Low, TaskPriority::Low) => Ordering::Equal,
        }
    }
}

impl PartialOrd for TaskPriority {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// 调度任务
#[derive(Debug)]
pub struct ScheduledTask {
    pub id: u64,
    pub priority: TaskPriority,
    pub scheduled_time: Instant,
    pub task: Box<dyn Fn() -> NetworkResult<()> + Send + Sync>,
}

impl Ord for ScheduledTask {
    fn cmp(&self, other: &Self) -> Ordering {
        // 首先按优先级排序，然后按调度时间排序
        match self.priority.cmp(&other.priority) {
            Ordering::Equal => other.scheduled_time.cmp(&self.scheduled_time),
            other => other,
        }
    }
}

impl PartialOrd for ScheduledTask {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for ScheduledTask {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for ScheduledTask {}

/// 异步任务调度器
pub struct AsyncTaskScheduler {
    task_queue: BinaryHeap<ScheduledTask>,
    task_id_counter: u64,
    sender: mpsc::UnboundedSender<ScheduledTask>,
    receiver: mpsc::UnboundedReceiver<ScheduledTask>,
}

impl AsyncTaskScheduler {
    /// 创建新的任务调度器
    pub fn new() -> Self {
        let (sender, receiver) = mpsc::unbounded_channel();
        
        Self {
            task_queue: BinaryHeap::new(),
            task_id_counter: 0,
            sender,
            receiver,
        }
    }

    /// 调度任务
    pub fn schedule_task<F>(
        &mut self,
        priority: TaskPriority,
        delay: Duration,
        task: F,
    ) -> u64
    where
        F: Fn() -> NetworkResult<()> + Send + Sync + 'static,
    {
        let task_id = self.task_id_counter;
        self.task_id_counter += 1;

        let scheduled_task = ScheduledTask {
            id: task_id,
            priority,
            scheduled_time: Instant::now() + delay,
            task: Box::new(task),
        };

        let _ = self.sender.send(scheduled_task);
        task_id
    }

    /// 启动调度器
    pub async fn run(&mut self) -> NetworkResult<()> {
        let mut interval = tokio::time::interval(Duration::from_millis(100));
        
        loop {
            tokio::select! {
                // 接收新任务
                task = self.receiver.recv() => {
                    if let Some(task) = task {
                        self.task_queue.push(task);
                    }
                }
                
                // 处理到期的任务
                _ = interval.tick() => {
                    self.process_due_tasks().await?;
                }
            }
        }
    }

    /// 处理到期的任务
    async fn process_due_tasks(&mut self) -> NetworkResult<()> {
        let now = Instant::now();
        let mut tasks_to_execute = Vec::new();

        // 收集到期的任务
        while let Some(task) = self.task_queue.peek() {
            if task.scheduled_time <= now {
                if let Some(task) = self.task_queue.pop() {
                    tasks_to_execute.push(task);
                }
            } else {
                break;
            }
        }

        // 执行任务
        for task in tasks_to_execute {
            tokio::spawn(async move {
                if let Err(e) = (task.task)() {
                    eprintln!("任务执行错误: {}", e);
                }
            });
        }

        Ok(())
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> NetworkResult<()> {
    let mut scheduler = AsyncTaskScheduler::new();

    // 调度一些任务
    scheduler.schedule_task(
        TaskPriority::High,
        Duration::from_secs(1),
        || {
            println!("高优先级任务执行");
            Ok(())
        },
    );

    scheduler.schedule_task(
        TaskPriority::Normal,
        Duration::from_secs(2),
        || {
            println!("普通优先级任务执行");
            Ok(())
        },
    );

    scheduler.schedule_task(
        TaskPriority::Low,
        Duration::from_secs(3),
        || {
            println!("低优先级任务执行");
            Ok(())
        },
    );

    // 启动调度器
    scheduler.run().await
}
```

## 🔗 相关文档

- [NETWORK_COMMUNICATION_THEORY_ENHANCED.md](NETWORK_COMMUNICATION_THEORY_ENHANCED.md) - 网络通信理论增强版
- [CONCEPT_DEFINITIONS_ENHANCED.md](CONCEPT_DEFINITIONS_ENHANCED.md) - 概念定义增强版
- [API_DOCUMENTATION.md](API_DOCUMENTATION.md) - API参考文档
- [PERFORMANCE_ANALYSIS_GUIDE.md](PERFORMANCE_ANALYSIS_GUIDE.md) - 性能分析指南
- [BEST_PRACTICES.md](BEST_PRACTICES.md) - 最佳实践指南

---

**C10 Networks 示例代码与应用场景增强版** - 为网络编程提供完整的实践指南！

*最后更新: 2025年1月*  
*文档版本: v2.0*  
*维护者: C10 Networks 开发团队*
