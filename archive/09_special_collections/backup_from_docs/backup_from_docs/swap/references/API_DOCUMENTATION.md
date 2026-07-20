# C10 Networks API 文档

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`DOCUMENTATION_STYLE_GUIDE.md`](DOCUMENTATION_STYLE_GUIDE.md)。

## 📊 目录

- [C10 Networks API 文档](#c10-networks-api-文档)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [🎯 概述](#-概述)
    - [1. API设计原则](#1-api设计原则)
      - [1.1 设计理念](#11-设计理念)
      - [1.2 命名规范](#12-命名规范)
    - [2. 模块结构](#2-模块结构)
      - [2.1 模块组织](#21-模块组织)
    - [3. 使用指南](#3-使用指南)
      - [3.1 快速开始](#31-快速开始)
  - [🔧 核心API](#-核心api)
    - [1. 网络连接](#1-网络连接)
      - [1.1 连接管理](#11-连接管理)
      - [1.2 连接池](#12-连接池)
    - [2. 协议处理](#2-协议处理)
      - [2.1 协议处理器](#21-协议处理器)
    - [3. 异步操作](#3-异步操作)
      - [3.1 异步流](#31-异步流)
    - [4. 错误处理](#4-错误处理)
      - [4.1 错误类型](#41-错误类型)
  - [🌐 协议API](#-协议api)
    - [1. TCP API](#1-tcp-api)
      - [1.1 TCP客户端](#11-tcp客户端)
    - [2. HTTP API](#2-http-api)
      - [2.1 HTTP客户端](#21-http客户端)
  - [🔗 相关文档](#-相关文档)

## 📋 目录

- [C10 Networks API 文档](#c10-networks-api-文档)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [🎯 概述](#-概述)
    - [1. API设计原则](#1-api设计原则)
      - [1.1 设计理念](#11-设计理念)
      - [1.2 命名规范](#12-命名规范)
    - [2. 模块结构](#2-模块结构)
      - [2.1 模块组织](#21-模块组织)
    - [3. 使用指南](#3-使用指南)
      - [3.1 快速开始](#31-快速开始)
  - [🔧 核心API](#-核心api)
    - [1. 网络连接](#1-网络连接)
      - [1.1 连接管理](#11-连接管理)
      - [1.2 连接池](#12-连接池)
    - [2. 协议处理](#2-协议处理)
      - [2.1 协议处理器](#21-协议处理器)
    - [3. 异步操作](#3-异步操作)
      - [3.1 异步流](#31-异步流)
    - [4. 错误处理](#4-错误处理)
      - [4.1 错误类型](#41-错误类型)
  - [🌐 协议API](#-协议api)
    - [1. TCP API](#1-tcp-api)
      - [1.1 TCP客户端](#11-tcp客户端)
    - [2. HTTP API](#2-http-api)
      - [2.1 HTTP客户端](#21-http客户端)
  - [🔗 相关文档](#-相关文档)

## 🎯 概述

本文档提供了C10 Networks项目的完整API参考，包括所有公共接口、类型定义、错误处理和示例代码。

### 1. API设计原则

#### 1.1 设计理念

1. **简洁性**: API设计简洁明了，易于理解和使用
2. **一致性**: 保持API风格和命名的一致性
3. **类型安全**: 充分利用Rust的类型系统保证安全性
4. **异步优先**: 所有I/O操作都是异步的
5. **错误友好**: 提供详细的错误信息和处理建议

#### 1.2 命名规范

```rust
// 命名规范示例
pub struct TcpClient;           // 结构体使用PascalCase
pub enum ConnectionState;       // 枚举使用PascalCase
pub trait AsyncRead;           // trait使用PascalCase

pub fn connect_async() -> Result<()>;  // 函数使用snake_case
pub const MAX_CONNECTIONS: usize = 100; // 常量使用SCREAMING_SNAKE_CASE
pub static GLOBAL_CONFIG: Config = Config::new(); // 静态变量使用SCREAMING_SNAKE_CASE
```

### 2. 模块结构

#### 2.1 模块组织

```rust
// 模块结构
pub mod tcp {
    pub mod client;
    pub mod server;
    pub mod connection;
    pub mod state_machine;
}

pub mod http {
    pub mod client;
    pub mod server;
    pub mod request;
    pub mod response;
    pub mod headers;
}

pub mod websocket {
    pub mod client;
    pub mod server;
    pub mod frame;
    pub mod handshake;
}

pub mod udp {
    pub mod socket;
    pub mod datagram;
}

pub mod security {
    pub mod tls;
    pub mod auth;
    pub mod crypto;
}

pub mod performance {
    pub mod pool;
    pub mod cache;
    pub mod metrics;
}

pub mod utils {
    pub mod error;
    pub mod config;
    pub mod logging;
}
```

### 3. 使用指南

#### 3.1 快速开始

```rust
use c10_networks::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建TCP客户端
    let mut client = TcpClient::new("127.0.0.1:8080").await?;
    
    // 发送数据
    client.write_all(b"Hello, Server!").await?;
    
    // 接收响应
    let mut buffer = vec![0; 1024];
    let n = client.read(&mut buffer).await?;
    let response = String::from_utf8_lossy(&buffer[..n]);
    
    println!("服务器响应: {}", response);
    
    Ok(())
}
```

## 🔧 核心API

### 1. 网络连接

#### 1.1 连接管理

```rust
// 网络连接API
pub struct NetworkConnection {
    id: ConnectionId,
    state: ConnectionState,
    local_addr: SocketAddr,
    remote_addr: SocketAddr,
    metrics: ConnectionMetrics,
}

impl NetworkConnection {
    /// 创建新的网络连接
    /// 
    /// # 参数
    /// * `remote_addr` - 远程地址
    /// 
    /// # 返回值
    /// 返回网络连接实例
    /// 
    /// # 示例
    /// ```rust
    /// let connection = NetworkConnection::new("127.0.0.1:8080".parse()?).await?;
    /// ```
    pub async fn new(remote_addr: SocketAddr) -> Result<Self, ConnectionError> {
        let stream = TcpStream::connect(remote_addr).await?;
        let local_addr = stream.local_addr()?;
        
        Ok(Self {
            id: ConnectionId::new(),
            state: ConnectionState::Connected,
            local_addr,
            remote_addr,
            metrics: ConnectionMetrics::new(),
        })
    }
    
    /// 获取连接ID
    pub fn id(&self) -> &ConnectionId {
        &self.id
    }
    
    /// 获取连接状态
    pub fn state(&self) -> &ConnectionState {
        &self.state
    }
    
    /// 获取本地地址
    pub fn local_addr(&self) -> &SocketAddr {
        &self.local_addr
    }
    
    /// 获取远程地址
    pub fn remote_addr(&self) -> &SocketAddr {
        &self.remote_addr
    }
    
    /// 获取连接指标
    pub fn metrics(&self) -> &ConnectionMetrics {
        &self.metrics
    }
    
    /// 关闭连接
    pub async fn close(&mut self) -> Result<(), ConnectionError> {
        self.state = ConnectionState::Closed;
        self.metrics.record_close();
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConnectionState {
    Connecting,
    Connected,
    Disconnecting,
    Disconnected,
    Closed,
    Error,
}

#[derive(Debug, Clone)]
pub struct ConnectionId(String);

impl ConnectionId {
    pub fn new() -> Self {
        Self(uuid::Uuid::new_v4().to_string())
    }
}

impl std::fmt::Display for ConnectionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
```

#### 1.2 连接池

```rust
// 连接池API
pub struct ConnectionPool {
    connections: HashMap<SocketAddr, Vec<PooledConnection>>,
    config: PoolConfig,
    metrics: PoolMetrics,
}

pub struct PooledConnection {
    connection: NetworkConnection,
    created_at: Instant,
    last_used: Instant,
    is_idle: bool,
}

impl ConnectionPool {
    /// 创建连接池
    /// 
    /// # 参数
    /// * `config` - 连接池配置
    /// 
    /// # 返回值
    /// 返回连接池实例
    pub fn new(config: PoolConfig) -> Self {
        Self {
            connections: HashMap::new(),
            config,
            metrics: PoolMetrics::new(),
        }
    }
    
    /// 获取连接
    /// 
    /// # 参数
    /// * `addr` - 目标地址
    /// 
    /// # 返回值
    /// 返回连接实例
    pub async fn get_connection(&mut self, addr: SocketAddr) -> Result<PooledConnection, PoolError> {
        // 查找空闲连接
        if let Some(connections) = self.connections.get_mut(&addr) {
            for (i, conn) in connections.iter_mut().enumerate() {
                if conn.is_idle && conn.last_used.elapsed() < self.config.max_idle_time {
                    conn.is_idle = false;
                    conn.last_used = Instant::now();
                    self.metrics.increment_hit();
                    return Ok(connections.remove(i));
                }
            }
        }
        
        // 创建新连接
        let connection = NetworkConnection::new(addr).await?;
        let pooled_connection = PooledConnection {
            connection,
            created_at: Instant::now(),
            last_used: Instant::now(),
            is_idle: false,
        };
        
        self.metrics.increment_miss();
        Ok(pooled_connection)
    }
    
    /// 归还连接
    /// 
    /// # 参数
    /// * `connection` - 要归还的连接
    pub fn return_connection(&mut self, mut connection: PooledConnection) {
        let addr = connection.connection.remote_addr().clone();
        
        connection.is_idle = true;
        connection.last_used = Instant::now();
        
        self.connections.entry(addr)
            .or_insert_with(Vec::new)
            .push(connection);
        
        self.metrics.increment_returned();
    }
    
    /// 清理空闲连接
    pub fn cleanup_idle_connections(&mut self) {
        let now = Instant::now();
        
        for connections in self.connections.values_mut() {
            connections.retain(|conn| {
                !conn.is_idle || now.duration_since(conn.last_used) < self.config.max_idle_time
            });
        }
        
        self.metrics.record_cleanup();
    }
    
    /// 获取连接池指标
    pub fn metrics(&self) -> &PoolMetrics {
        &self.metrics
    }
}

#[derive(Debug, Clone)]
pub struct PoolConfig {
    pub max_connections_per_host: usize,
    pub max_idle_time: Duration,
    pub connection_timeout: Duration,
    pub keep_alive: bool,
}

impl Default for PoolConfig {
    fn default() -> Self {
        Self {
            max_connections_per_host: 10,
            max_idle_time: Duration::from_secs(30),
            connection_timeout: Duration::from_secs(5),
            keep_alive: true,
        }
    }
}
```

### 2. 协议处理

#### 2.1 协议处理器

```rust
// 协议处理器API
pub trait ProtocolHandler {
    type Request;
    type Response;
    type Error;
    
    /// 处理协议请求
    /// 
    /// # 参数
    /// * `request` - 协议请求
    /// 
    /// # 返回值
    /// 返回协议响应
    async fn handle(&self, request: Self::Request) -> Result<Self::Response, Self::Error>;
    
    /// 验证请求
    /// 
    /// # 参数
    /// * `request` - 要验证的请求
    /// 
    /// # 返回值
    /// 验证结果
    fn validate(&self, request: &Self::Request) -> Result<(), ValidationError>;
    
    /// 获取协议版本
    fn version(&self) -> ProtocolVersion;
    
    /// 获取协议名称
    fn name(&self) -> &str;
}

pub struct ProtocolProcessor {
    handlers: HashMap<String, Box<dyn ProtocolHandler>>,
    metrics: ProcessorMetrics,
}

impl ProtocolProcessor {
    /// 创建协议处理器
    pub fn new() -> Self {
        Self {
            handlers: HashMap::new(),
            metrics: ProcessorMetrics::new(),
        }
    }
    
    /// 注册协议处理器
    /// 
    /// # 参数
    /// * `name` - 协议名称
    /// * `handler` - 协议处理器
    pub fn register_handler<H>(&mut self, name: String, handler: H)
    where
        H: ProtocolHandler + 'static,
    {
        self.handlers.insert(name, Box::new(handler));
    }
    
    /// 处理协议请求
    /// 
    /// # 参数
    /// * `protocol` - 协议名称
    /// * `request` - 请求数据
    /// 
    /// # 返回值
    /// 返回响应数据
    pub async fn process_request(
        &self,
        protocol: &str,
        request: &[u8],
    ) -> Result<Vec<u8>, ProcessorError> {
        let handler = self.handlers.get(protocol)
            .ok_or(ProcessorError::UnknownProtocol)?;
        
        let start_time = Instant::now();
        let result = handler.handle(request).await;
        let duration = start_time.elapsed();
        
        self.metrics.record_request(duration, result.is_ok());
        
        result
    }
    
    /// 获取支持的协议列表
    pub fn supported_protocols(&self) -> Vec<String> {
        self.handlers.keys().cloned().collect()
    }
    
    /// 获取处理器指标
    pub fn metrics(&self) -> &ProcessorMetrics {
        &self.metrics
    }
}

#[derive(Debug, Clone)]
pub struct ProtocolVersion {
    major: u8,
    minor: u8,
    patch: u8,
}

impl ProtocolVersion {
    pub fn new(major: u8, minor: u8, patch: u8) -> Self {
        Self { major, minor, patch }
    }
    
    pub fn major(&self) -> u8 {
        self.major
    }
    
    pub fn minor(&self) -> u8 {
        self.minor
    }
    
    pub fn patch(&self) -> u8 {
        self.patch
    }
}

impl std::fmt::Display for ProtocolVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}
```

### 3. 异步操作

#### 3.1 异步流

```rust
// 异步流API
pub struct AsyncStream<T> {
    inner: Pin<Box<dyn Stream<Item = T> + Send>>,
    buffer: VecDeque<T>,
    buffer_size: usize,
}

impl<T> AsyncStream<T> {
    /// 创建异步流
    /// 
    /// # 参数
    /// * `stream` - 底层流
    /// * `buffer_size` - 缓冲区大小
    /// 
    /// # 返回值
    /// 返回异步流实例
    pub fn new(stream: impl Stream<Item = T> + Send + 'static, buffer_size: usize) -> Self {
        Self {
            inner: Box::pin(stream),
            buffer: VecDeque::with_capacity(buffer_size),
            buffer_size,
        }
    }
    
    /// 获取下一个元素
    /// 
    /// # 返回值
    /// 返回下一个元素，如果没有则返回None
    pub async fn next(&mut self) -> Option<T> {
        if let Some(item) = self.buffer.pop_front() {
            return Some(item);
        }
        
        self.fill_buffer().await;
        self.buffer.pop_front()
    }
    
    /// 批量获取元素
    /// 
    /// # 参数
    /// * `count` - 要获取的元素数量
    /// 
    /// # 返回值
    /// 返回元素向量
    pub async fn next_batch(&mut self, count: usize) -> Vec<T> {
        let mut batch = Vec::with_capacity(count);
        
        for _ in 0..count {
            if let Some(item) = self.next().await {
                batch.push(item);
            } else {
                break;
            }
        }
        
        batch
    }
    
    /// 处理流中的每个元素
    /// 
    /// # 参数
    /// * `processor` - 处理函数
    /// 
    /// # 返回值
    /// 处理结果
    pub async fn for_each<F>(&mut self, mut processor: F) -> Result<(), StreamError>
    where
        F: FnMut(T) -> BoxFuture<'static, Result<(), StreamError>>,
    {
        while let Some(item) = self.next().await {
            processor(item).await?;
        }
        
        Ok(())
    }
    
    /// 映射流中的元素
    /// 
    /// # 参数
    /// * `mapper` - 映射函数
    /// 
    /// # 返回值
    /// 返回新的流
    pub fn map<U, F>(self, mapper: F) -> AsyncStream<U>
    where
        F: Fn(T) -> U + Send + 'static,
        U: Send + 'static,
    {
        let mapped_stream = self.inner.map(mapper);
        AsyncStream::new(mapped_stream, self.buffer_size)
    }
    
    /// 过滤流中的元素
    /// 
    /// # 参数
    /// * `predicate` - 过滤函数
    /// 
    /// # 返回值
    /// 返回新的流
    pub fn filter<F>(self, predicate: F) -> AsyncStream<T>
    where
        F: Fn(&T) -> bool + Send + 'static,
    {
        let filtered_stream = self.inner.filter(predicate);
        AsyncStream::new(filtered_stream, self.buffer_size)
    }
    
    async fn fill_buffer(&mut self) {
        let mut batch = Vec::with_capacity(self.buffer_size);
        
        for _ in 0..self.buffer_size {
            if let Some(item) = self.inner.next().await {
                batch.push(item);
            } else {
                break;
            }
        }
        
        self.buffer.extend(batch);
    }
}

impl<T> Stream for AsyncStream<T> {
    type Item = T;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        if let Some(item) = self.buffer.pop_front() {
            return Poll::Ready(Some(item));
        }
        
        self.inner.as_mut().poll_next(cx)
    }
}
```

### 4. 错误处理

#### 4.1 错误类型

```rust
// 错误处理API
#[derive(Debug, thiserror::Error)]
pub enum NetworkError {
    #[error("连接错误: {0}")]
    ConnectionError(#[from] ConnectionError),
    
    #[error("协议错误: {0}")]
    ProtocolError(#[from] ProtocolError),
    
    #[error("IO错误: {0}")]
    IoError(#[from] std::io::Error),
    
    #[error("超时错误: {timeout:?}")]
    TimeoutError { timeout: Duration },
    
    #[error("配置错误: {0}")]
    ConfigError(String),
    
    #[error("验证错误: {0}")]
    ValidationError(#[from] ValidationError),
    
    #[error("安全错误: {0}")]
    SecurityError(#[from] SecurityError),
}

#[derive(Debug, thiserror::Error)]
pub enum ConnectionError {
    #[error("连接失败: {address}")]
    ConnectionFailed { address: SocketAddr },
    
    #[error("连接超时: {timeout:?}")]
    ConnectionTimeout { timeout: Duration },
    
    #[error("连接已关闭")]
    ConnectionClosed,
    
    #[error("连接被拒绝: {reason}")]
    ConnectionRefused { reason: String },
    
    #[error("网络不可达: {address}")]
    NetworkUnreachable { address: SocketAddr },
    
    #[error("地址已在使用: {address}")]
    AddressInUse { address: SocketAddr },
}

#[derive(Debug, thiserror::Error)]
pub enum ProtocolError {
    #[error("无效的协议版本: {version}")]
    InvalidVersion { version: String },
    
    #[error("协议不匹配: 期望 {expected}, 实际 {actual}")]
    ProtocolMismatch { expected: String, actual: String },
    
    #[error("数据包格式错误: {reason}")]
    InvalidPacketFormat { reason: String },
    
    #[error("校验和错误: 期望 {expected}, 实际 {actual}")]
    ChecksumError { expected: u32, actual: u32 },
    
    #[error("序列号错误: 期望 {expected}, 实际 {actual}")]
    SequenceError { expected: u32, actual: u32 },
}

#[derive(Debug, thiserror::Error)]
pub enum ValidationError {
    #[error("字段验证失败: {field} - {reason}")]
    FieldValidation { field: String, reason: String },
    
    #[error("长度验证失败: 期望 {expected}, 实际 {actual}")]
    LengthValidation { expected: usize, actual: usize },
    
    #[error("范围验证失败: 值 {value} 超出范围 [{min}, {max}]")]
    RangeValidation { value: i64, min: i64, max: i64 },
    
    #[error("格式验证失败: {value} 不符合格式 {pattern}")]
    FormatValidation { value: String, pattern: String },
}

impl NetworkError {
    /// 检查错误是否可恢复
    pub fn is_recoverable(&self) -> bool {
        match self {
            NetworkError::TimeoutError { .. } => true,
            NetworkError::IoError(_) => true,
            NetworkError::ConnectionError(ConnectionError::ConnectionTimeout { .. }) => true,
            _ => false,
        }
    }
    
    /// 检查错误是否应该重试
    pub fn should_retry(&self) -> bool {
        match self {
            NetworkError::TimeoutError { .. } => true,
            NetworkError::IoError(_) => true,
            NetworkError::ConnectionError(ConnectionError::ConnectionTimeout { .. }) => true,
            _ => false,
        }
    }
    
    /// 获取错误严重程度
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            NetworkError::SecurityError(_) => ErrorSeverity::Critical,
            NetworkError::ConnectionError(ConnectionError::ConnectionClosed) => ErrorSeverity::High,
            NetworkError::TimeoutError { .. } => ErrorSeverity::Medium,
            NetworkError::ValidationError(_) => ErrorSeverity::Low,
            _ => ErrorSeverity::Medium,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ErrorSeverity {
    Low,
    Medium,
    High,
    Critical,
}

// 错误处理工具
pub struct ErrorHandler {
    error_counts: HashMap<String, AtomicUsize>,
    error_thresholds: HashMap<String, usize>,
    alert_callbacks: Vec<Box<dyn Fn(&NetworkError) + Send + Sync>>,
}

impl ErrorHandler {
    pub fn new() -> Self {
        Self {
            error_counts: HashMap::new(),
            error_thresholds: HashMap::new(),
            alert_callbacks: Vec::new(),
        }
    }
    
    pub fn handle_error(&self, error: &NetworkError) {
        let error_type = format!("{:?}", error);
        let count = self.error_counts
            .entry(error_type.clone())
            .or_insert_with(|| AtomicUsize::new(0))
            .fetch_add(1, Ordering::Relaxed);
        
        if let Some(threshold) = self.error_thresholds.get(&error_type) {
            if count >= *threshold {
                for callback in &self.alert_callbacks {
                    callback(error);
                }
            }
        }
    }
    
    pub fn set_threshold(&mut self, error_type: String, threshold: usize) {
        self.error_thresholds.insert(error_type, threshold);
    }
    
    pub fn add_alert_callback<F>(&mut self, callback: F)
    where
        F: Fn(&NetworkError) + Send + Sync + 'static,
    {
        self.alert_callbacks.push(Box::new(callback));
    }
    
    pub fn get_error_count(&self, error_type: &str) -> usize {
        self.error_counts
            .get(error_type)
            .map(|count| count.load(Ordering::Relaxed))
            .unwrap_or(0)
    }
    
    pub fn reset_counts(&self) {
        for count in self.error_counts.values() {
            count.store(0, Ordering::Relaxed);
        }
    }
}
```

## 🌐 协议API

### 1. TCP API

#### 1.1 TCP客户端

```rust
// TCP客户端API
pub struct TcpClient {
    stream: TcpStream,
    connection_info: ConnectionInfo,
    metrics: ClientMetrics,
}

impl TcpClient {
    /// 创建TCP客户端
    /// 
    /// # 参数
    /// * `addr` - 服务器地址
    /// 
    /// # 返回值
    /// 返回TCP客户端实例
    /// 
    /// # 示例
    /// ```rust
    /// let client = TcpClient::new("127.0.0.1:8080").await?;
    /// ```
    pub async fn new(addr: impl ToSocketAddrs) -> Result<Self, ClientError> {
        let addr = addr.to_socket_addrs()?
            .next()
            .ok_or(ClientError::InvalidAddress)?;
        
        let stream = TcpStream::connect(addr).await?;
        let local_addr = stream.local_addr()?;
        
        Ok(Self {
            stream,
            connection_info: ConnectionInfo::new(local_addr, addr),
            metrics: ClientMetrics::new(),
        })
    }
    
    /// 发送数据
    /// 
    /// # 参数
    /// * `data` - 要发送的数据
    /// 
    /// # 返回值
    /// 返回发送的字节数
    pub async fn send(&mut self, data: &[u8]) -> Result<usize, ClientError> {
        let start_time = Instant::now();
        let result = self.stream.write(data).await;
        let duration = start_time.elapsed();
        
        match result {
            Ok(bytes_written) => {
                self.metrics.record_send(bytes_written, duration);
                Ok(bytes_written)
            }
            Err(e) => {
                self.metrics.record_error();
                Err(ClientError::IoError(e))
            }
        }
    }
    
    /// 接收数据
    /// 
    /// # 参数
    /// * `buffer` - 接收缓冲区
    /// 
    /// # 返回值
    /// 返回接收的字节数
    pub async fn receive(&mut self, buffer: &mut [u8]) -> Result<usize, ClientError> {
        let start_time = Instant::now();
        let result = self.stream.read(buffer).await;
        let duration = start_time.elapsed();
        
        match result {
            Ok(bytes_read) => {
                self.metrics.record_receive(bytes_read, duration);
                Ok(bytes_read)
            }
            Err(e) => {
                self.metrics.record_error();
                Err(ClientError::IoError(e))
            }
        }
    }
    
    /// 发送所有数据
    /// 
    /// # 参数
    /// * `data` - 要发送的数据
    /// 
    /// # 返回值
    /// 发送结果
    pub async fn send_all(&mut self, data: &[u8]) -> Result<(), ClientError> {
        let start_time = Instant::now();
        let result = self.stream.write_all(data).await;
        let duration = start_time.elapsed();
        
        match result {
            Ok(_) => {
                self.metrics.record_send(data.len(), duration);
                Ok(())
            }
            Err(e) => {
                self.metrics.record_error();
                Err(ClientError::IoError(e))
            }
        }
    }
    
    /// 获取连接信息
    pub fn connection_info(&self) -> &ConnectionInfo {
        &self.connection_info
    }
    
    /// 获取客户端指标
    pub fn metrics(&self) -> &ClientMetrics {
        &self.metrics
    }
    
    /// 关闭连接
    pub async fn close(self) -> Result<(), ClientError> {
        drop(self.stream);
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct ConnectionInfo {
    local_addr: SocketAddr,
    remote_addr: SocketAddr,
    established_at: Instant,
}

impl ConnectionInfo {
    pub fn new(local_addr: SocketAddr, remote_addr: SocketAddr) -> Self {
        Self {
            local_addr,
            remote_addr,
            established_at: Instant::now(),
        }
    }
    
    pub fn local_addr(&self) -> &SocketAddr {
        &self.local_addr
    }
    
    pub fn remote_addr(&self) -> &SocketAddr {
        &self.remote_addr
    }
    
    pub fn duration(&self) -> Duration {
        self.established_at.elapsed()
    }
}

pub struct ClientMetrics {
    bytes_sent: AtomicUsize,
    bytes_received: AtomicUsize,
    send_count: AtomicUsize,
    receive_count: AtomicUsize,
    error_count: AtomicUsize,
    total_send_time: AtomicU64,
    total_receive_time: AtomicU64,
}

impl ClientMetrics {
    pub fn new() -> Self {
        Self {
            bytes_sent: AtomicUsize::new(0),
            bytes_received: AtomicUsize::new(0),
            send_count: AtomicUsize::new(0),
            receive_count: AtomicUsize::new(0),
            error_count: AtomicUsize::new(0),
            total_send_time: AtomicU64::new(0),
            total_receive_time: AtomicU64::new(0),
        }
    }
    
    pub fn record_send(&self, bytes: usize, duration: Duration) {
        self.bytes_sent.fetch_add(bytes, Ordering::Relaxed);
        self.send_count.fetch_add(1, Ordering::Relaxed);
        self.total_send_time.fetch_add(duration.as_nanos() as u64, Ordering::Relaxed);
    }
    
    pub fn record_receive(&self, bytes: usize, duration: Duration) {
        self.bytes_received.fetch_add(bytes, Ordering::Relaxed);
        self.receive_count.fetch_add(1, Ordering::Relaxed);
        self.total_receive_time.fetch_add(duration.as_nanos() as u64, Ordering::Relaxed);
    }
    
    pub fn record_error(&self) {
        self.error_count.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn bytes_sent(&self) -> usize {
        self.bytes_sent.load(Ordering::Relaxed)
    }
    
    pub fn bytes_received(&self) -> usize {
        self.bytes_received.load(Ordering::Relaxed)
    }
    
    pub fn send_count(&self) -> usize {
        self.send_count.load(Ordering::Relaxed)
    }
    
    pub fn receive_count(&self) -> usize {
        self.receive_count.load(Ordering::Relaxed)
    }
    
    pub fn error_count(&self) -> usize {
        self.error_count.load(Ordering::Relaxed)
    }
    
    pub fn average_send_time(&self) -> Duration {
        let count = self.send_count.load(Ordering::Relaxed);
        let total_time = self.total_send_time.load(Ordering::Relaxed);
        
        if count > 0 {
            Duration::from_nanos(total_time / count as u64)
        } else {
            Duration::ZERO
        }
    }
    
    pub fn average_receive_time(&self) -> Duration {
        let count = self.receive_count.load(Ordering::Relaxed);
        let total_time = self.total_receive_time.load(Ordering::Relaxed);
        
        if count > 0 {
            Duration::from_nanos(total_time / count as u64)
        } else {
            Duration::ZERO
        }
    }
}
```

### 2. HTTP API

#### 2.1 HTTP客户端

```rust
// HTTP客户端API
pub struct HttpClient {
    client: reqwest::Client,
    base_url: Option<Url>,
    default_headers: HeaderMap,
    timeout: Duration,
    metrics: HttpMetrics,
}

impl HttpClient {
    /// 创建HTTP客户端
    /// 
    /// # 返回值
    /// 返回HTTP客户端实例
    pub fn new() -> Self {
        Self {
            client: reqwest::Client::new(),
            base_url: None,
            default_headers: HeaderMap::new(),
            timeout: Duration::from_secs(30),
            metrics: HttpMetrics::new(),
        }
    }
    
    /// 设置基础URL
    /// 
    /// # 参数
    /// * `url` - 基础URL
    /// 
    /// # 返回值
    /// 返回客户端实例
    pub fn with_base_url(mut self, url: Url) -> Self {
        self.base_url = Some(url);
        self
    }
    
    /// 设置默认头部
    /// 
    /// # 参数
    /// * `headers` - 头部映射
    /// 
    /// # 返回值
    /// 返回客户端实例
    pub fn with_default_headers(mut self, headers: HeaderMap) -> Self {
        self.default_headers = headers;
        self
    }
    
    /// 设置超时时间
    /// 
    /// # 参数
    /// * `timeout` - 超时时间
    /// 
    /// # 返回值
    /// 返回客户端实例
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
    
    /// 发送GET请求
    /// 
    /// # 参数
    /// * `url` - 请求URL
    /// 
    /// # 返回值
    /// 返回HTTP响应
    pub async fn get(&self, url: &str) -> Result<HttpResponse, HttpError> {
        let start_time = Instant::now();
        
        let mut request = self.client.get(url);
        request = request.timeout(self.timeout);
        
        // 添加默认头部
        for (name, value) in &self.default_headers {
            request = request.header(name, value);
        }
        
        let response = request.send().await?;
        let duration = start_time.elapsed();
        
        let http_response = HttpResponse::from_reqwest(response).await?;
        self.metrics.record_request(Method::GET, duration, http_response.status());
        
        Ok(http_response)
    }
    
    /// 发送POST请求
    /// 
    /// # 参数
    /// * `url` - 请求URL
    /// * `body` - 请求体
    /// 
    /// # 返回值
    /// 返回HTTP响应
    pub async fn post(&self, url: &str, body: impl Into<Body>) -> Result<HttpResponse, HttpError> {
        let start_time = Instant::now();
        
        let mut request = self.client.post(url);
        request = request.timeout(self.timeout);
        request = request.body(body);
        
        // 添加默认头部
        for (name, value) in &self.default_headers {
            request = request.header(name, value);
        }
        
        let response = request.send().await?;
        let duration = start_time.elapsed();
        
        let http_response = HttpResponse::from_reqwest(response).await?;
        self.metrics.record_request(Method::POST, duration, http_response.status());
        
        Ok(http_response)
    }
    
    /// 发送PUT请求
    /// 
    /// # 参数
    /// * `url` - 请求URL
    /// * `body` - 请求体
    /// 
    /// # 返回值
    /// 返回HTTP响应
    pub async fn put(&self, url: &str, body: impl Into<Body>) -> Result<HttpResponse, HttpError> {
        let start_time = Instant::now();
        
        let mut request = self.client.put(url);
        request = request.timeout(self.timeout);
        request = request.body(body);
        
        // 添加默认头部
        for (name, value) in &self.default_headers {
            request = request.header(name, value);
        }
        
        let response = request.send().await?;
        let duration = start_time.elapsed();
        
        let http_response = HttpResponse::from_reqwest(response).await?;
        self.metrics.record_request(Method::PUT, duration, http_response.status());
        
        Ok(http_response)
    }
    
    /// 发送DELETE请求
    /// 
    /// # 参数
    /// * `url` - 请求URL
    /// 
    /// # 返回值
    /// 返回HTTP响应
    pub async fn delete(&self, url: &str) -> Result<HttpResponse, HttpError> {
        let start_time = Instant::now();
        
        let mut request = self.client.delete(url);
        request = request.timeout(self.timeout);
        
        // 添加默认头部
        for (name, value) in &self.default_headers {
            request = request.header(name, value);
        }
        
        let response = request.send().await?;
        let duration = start_time.elapsed();
        
        let http_response = HttpResponse::from_reqwest(response).await?;
        self.metrics.record_request(Method::DELETE, duration, http_response.status());
        
        Ok(http_response)
    }
    
    /// 获取客户端指标
    pub fn metrics(&self) -> &HttpMetrics {
        &self.metrics
    }
}

#[derive(Debug, Clone)]
pub struct HttpResponse {
    status: u16,
    headers: HeaderMap,
    body: Vec<u8>,
    version: HttpVersion,
}

impl HttpResponse {
    pub fn new(status: u16, headers: HeaderMap, body: Vec<u8>) -> Self {
        Self {
            status,
            headers,
            body,
            version: HttpVersion::Http11,
        }
    }
    
    pub async fn from_reqwest(response: reqwest::Response) -> Result<Self, HttpError> {
        let status = response.status().as_u16();
        let headers = response.headers().clone();
        let body = response.bytes().await?.to_vec();
        
        Ok(Self {
            status,
            headers,
            body,
            version: HttpVersion::Http11,
        })
    }
    
    pub fn status(&self) -> u16 {
        self.status
    }
    
    pub fn headers(&self) -> &HeaderMap {
        &self.headers
    }
    
    pub fn body(&self) -> &[u8] {
        &self.body
    }
    
    pub fn text(&self) -> Result<String, HttpError> {
        String::from_utf8(self.body.clone())
            .map_err(|_| HttpError::InvalidUtf8)
    }
    
    pub fn json<T>(&self) -> Result<T, HttpError>
    where
        T: serde::de::DeserializeOwned,
    {
        serde_json::from_slice(&self.body)
            .map_err(|_| HttpError::InvalidJson)
    }
    
    pub fn get_header(&self, name: &str) -> Option<&HeaderValue> {
        self.headers.get(name)
    }
    
    pub fn is_success(&self) -> bool {
        self.status >= 200 && self.status < 300
    }
    
    pub fn is_redirect(&self) -> bool {
        self.status >= 300 && self.status < 400
    }
    
    pub fn is_client_error(&self) -> bool {
        self.status >= 400 && self.status < 500
    }
    
    pub fn is_server_error(&self) -> bool {
        self.status >= 500 && self.status < 600
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum HttpVersion {
    Http10,
    Http11,
    Http2,
}

pub struct HttpMetrics {
    request_count: AtomicUsize,
    success_count: AtomicUsize,
    error_count: AtomicUsize,
    total_time: AtomicU64,
    method_counts: HashMap<Method, AtomicUsize>,
}

impl HttpMetrics {
    pub fn new() -> Self {
        Self {
            request_count: AtomicUsize::new(0),
            success_count: AtomicUsize::new(0),
            error_count: AtomicUsize::new(0),
            total_time: AtomicU64::new(0),
            method_counts: HashMap::new(),
        }
    }
    
    pub fn record_request(&self, method: Method, duration: Duration, status: u16) {
        self.request_count.fetch_add(1, Ordering::Relaxed);
        self.total_time.fetch_add(duration.as_nanos() as u64, Ordering::Relaxed);
        
        if status >= 200 && status < 400 {
            self.success_count.fetch_add(1, Ordering::Relaxed);
        } else {
            self.error_count.fetch_add(1, Ordering::Relaxed);
        }
        
        self.method_counts
            .entry(method)
            .or_insert_with(|| AtomicUsize::new(0))
            .fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn request_count(&self) -> usize {
        self.request_count.load(Ordering::Relaxed)
    }
    
    pub fn success_rate(&self) -> f64 {
        let total = self.request_count.load(Ordering::Relaxed);
        let success = self.success_count.load(Ordering::Relaxed);
        
        if total > 0 {
            success as f64 / total as f64
        } else {
            0.0
        }
    }
    
    pub fn average_response_time(&self) -> Duration {
        let count = self.request_count.load(Ordering::Relaxed);
        let total_time = self.total_time.load(Ordering::Relaxed);
        
        if count > 0 {
            Duration::from_nanos(total_time / count as u64)
        } else {
            Duration::ZERO
        }
    }
}
```

## 🔗 相关文档

- [网络通信理论](NETWORK_COMMUNICATION_THEORY.md) - 网络通信的理论基础
- [数学基础](MATHEMATICAL_FOUNDATIONS.md) - 网络编程的数学基础
- [网络通信概念](NETWORK_COMMUNICATION_CONCEPTS.md) - 网络通信概念详解
- [形式化证明](FORMAL_PROOFS_AND_MATHEMATICAL_ARGUMENTS.md) - 形式化证明和数学论证
- [示例与应用场景](EXAMPLES_AND_APPLICATION_SCENARIOS.md) - 实际应用示例
- [网络理论与通信机制](NETWORK_THEORY_AND_COMMUNICATION_MECHANISMS.md) - 网络理论和通信机制
- [协议实现指南](PROTOCOL_IMPLEMENTATION_GUIDE.md) - 协议实现的具体指导
- [性能优化指南](PERFORMANCE_OPTIMIZATION_GUIDE.md) - 性能优化的详细指导

---

**C10 Networks API 文档** - 完整的API参考和使用指南！

*最后更新: 2025年1月*  
*文档版本: v1.0*  
