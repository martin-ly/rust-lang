# C07-13. IPC 通信高级示例 (Rust 1.90 增强版)

## 目录

- [C07-13. IPC 通信高级示例 (Rust 1.90 增强版)](#c07-13-ipc-通信高级示例-rust-190-增强版)
  - [目录](#目录)
  - [1. 命名管道 (Named Pipes)](#1-命名管道-named-pipes)
    - [1.1 命名管道服务器](#11-命名管道服务器)
    - [1.2 命名管道客户端](#12-命名管道客户端)
  - [2. Unix Domain Sockets](#2-unix-domain-sockets)
    - [2.1 Unix Domain Socket 服务器](#21-unix-domain-socket-服务器)
    - [2.2 Unix Domain Socket 客户端](#22-unix-domain-socket-客户端)
  - [3. 共享内存通信](#3-共享内存通信)
    - [3.1 共享内存管理器](#31-共享内存管理器)
  - [4. 消息队列](#4-消息队列)
    - [4.1 消息队列实现](#41-消息队列实现)
  - [5. 信号量同步](#5-信号量同步)
    - [5.1 信号量实现](#51-信号量实现)
  - [6. 内存映射文件](#6-内存映射文件)
    - [6.1 内存映射文件管理器](#61-内存映射文件管理器)
  - [总结](#总结)

本章提供高级 IPC 通信示例，涵盖命名管道、Unix Domain Sockets、共享内存、消息队列、信号量和内存映射文件等通信机制。

## 1. 命名管道 (Named Pipes)

### 1.1 命名管道服务器

```rust
use std::io::{self, Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;
use tokio::sync::mpsc;

// 命名管道服务器
pub struct NamedPipeServer {
    pipe_path: String,
    clients: Arc<Mutex<Vec<ClientConnection>>>,
    message_handler: Arc<dyn Fn(String) -> String + Send + Sync>,
}

#[derive(Debug)]
pub struct ClientConnection {
    pub id: String,
    pub stream: UnixStream,
    pub last_activity: std::time::Instant,
}

impl NamedPipeServer {
    pub fn new(pipe_path: String, message_handler: Arc<dyn Fn(String) -> String + Send + Sync>) -> Self {
        Self {
            pipe_path,
            clients: Arc::new(Mutex::new(Vec::new())),
            message_handler,
        }
    }

    // 启动服务器
    pub async fn start(&self) -> Result<(), PipeError> {
        // 删除已存在的管道文件
        if Path::new(&self.pipe_path).exists() {
            std::fs::remove_file(&self.pipe_path)?;
        }

        // 创建 Unix Domain Socket
        let listener = UnixListener::bind(&self.pipe_path)
            .map_err(|e| PipeError::BindFailed(e.to_string()))?;

        println!("命名管道服务器启动，监听: {}", self.pipe_path);

        // 异步接受连接
        let clients = self.clients.clone();
        let message_handler = self.message_handler.clone();
        let pipe_path = self.pipe_path.clone();

        tokio::spawn(async move {
            for stream in listener.incoming() {
                match stream {
                    Ok(stream) => {
                        let client_id = uuid::Uuid::new_v4().to_string();
                        let client = ClientConnection {
                            id: client_id.clone(),
                            stream,
                            last_activity: std::time::Instant::now(),
                        };

                        {
                            let mut clients = clients.lock().unwrap();
                            clients.push(client);
                        }

                        println!("新客户端连接: {}", client_id);

                        // 处理客户端消息
                        let clients_clone = clients.clone();
                        let handler_clone = message_handler.clone();
                        tokio::spawn(async move {
                            Self::handle_client(client_id, clients_clone, handler_clone).await;
                        });
                    }
                    Err(e) => {
                        eprintln!("接受连接失败: {}", e);
                    }
                }
            }
        });

        Ok(())
    }

    // 处理客户端消息
    async fn handle_client(
        client_id: String,
        clients: Arc<Mutex<Vec<ClientConnection>>>,
        message_handler: Arc<dyn Fn(String) -> String + Send + Sync>,
    ) {
        let mut buffer = [0; 1024];
        
        loop {
            // 查找客户端连接
            let mut stream = {
                let mut clients = clients.lock().unwrap();
                if let Some(client) = clients.iter_mut().find(|c| c.id == client_id) {
                    client.last_activity = std::time::Instant::now();
                    client.stream.try_clone().ok()
                } else {
                    break;
                }
            };

            if let Some(ref mut stream) = stream {
                match stream.read(&mut buffer) {
                    Ok(0) => {
                        // 客户端断开连接
                        break;
                    }
                    Ok(n) => {
                        let message = String::from_utf8_lossy(&buffer[..n]);
                        println!("收到消息: {}", message);

                        // 处理消息
                        let response = message_handler(message.to_string());
                        
                        // 发送响应
                        if let Err(e) = stream.write_all(response.as_bytes()) {
                            eprintln!("发送响应失败: {}", e);
                            break;
                        }
                    }
                    Err(e) => {
                        eprintln!("读取消息失败: {}", e);
                        break;
                    }
                }
            }
        }

        // 移除客户端
        {
            let mut clients = clients.lock().unwrap();
            clients.retain(|c| c.id != client_id);
        }

        println!("客户端断开连接: {}", client_id);
    }

    // 广播消息
    pub async fn broadcast(&self, message: &str) -> Result<(), PipeError> {
        let mut clients = self.clients.lock().unwrap();
        let mut failed_clients = Vec::new();

        for client in clients.iter_mut() {
            if let Err(_) = client.stream.write_all(message.as_bytes()) {
                failed_clients.push(client.id.clone());
            }
        }

        // 移除失败的客户端
        clients.retain(|c| !failed_clients.contains(&c.id));

        Ok(())
    }

    // 获取客户端数量
    pub fn get_client_count(&self) -> usize {
        self.clients.lock().unwrap().len()
    }

    // 停止服务器
    pub fn stop(&self) -> Result<(), PipeError> {
        if Path::new(&self.pipe_path).exists() {
            std::fs::remove_file(&self.pipe_path)?;
        }
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum PipeError {
    #[error("绑定失败: {0}")]
    BindFailed(String),
    
    #[error("IO错误: {0}")]
    IoError(#[from] io::Error),
    
    #[error("连接失败: {0}")]
    ConnectionFailed(String),
    
    #[error("消息发送失败: {0}")]
    MessageSendFailed(String),
}
```

### 1.2 命名管道客户端

```rust
use std::io::{self, Read, Write};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::time::Duration;

// 命名管道客户端
pub struct NamedPipeClient {
    pipe_path: String,
    stream: Option<UnixStream>,
}

impl NamedPipeClient {
    pub fn new(pipe_path: String) -> Self {
        Self {
            pipe_path,
            stream: None,
        }
    }

    // 连接到服务器
    pub async fn connect(&mut self) -> Result<(), PipeError> {
        // 等待服务器启动
        while !Path::new(&self.pipe_path).exists() {
            tokio::time::sleep(Duration::from_millis(100)).await;
        }

        let stream = UnixStream::connect(&self.pipe_path)
            .map_err(|e| PipeError::ConnectionFailed(e.to_string()))?;

        self.stream = Some(stream);
        println!("连接到命名管道服务器: {}", self.pipe_path);

        Ok(())
    }

    // 发送消息
    pub async fn send_message(&mut self, message: &str) -> Result<String, PipeError> {
        if let Some(ref mut stream) = self.stream {
            // 发送消息
            stream.write_all(message.as_bytes())
                .map_err(|e| PipeError::MessageSendFailed(e.to_string()))?;

            // 读取响应
            let mut buffer = [0; 1024];
            let n = stream.read(&mut buffer)
                .map_err(|e| PipeError::IoError(e))?;

            let response = String::from_utf8_lossy(&buffer[..n]).to_string();
            Ok(response)
        } else {
            Err(PipeError::ConnectionFailed("未连接到服务器".to_string()))
        }
    }

    // 断开连接
    pub fn disconnect(&mut self) {
        self.stream = None;
    }
}

// 使用示例
pub async fn named_pipe_example() -> Result<(), Box<dyn std::error::Error>> {
    let pipe_path = "/tmp/named_pipe_example".to_string();
    
    // 创建消息处理器
    let message_handler = Arc::new(|message: String| -> String {
        format!("服务器响应: {}", message)
    });

    // 启动服务器
    let server = NamedPipeServer::new(pipe_path.clone(), message_handler);
    server.start().await?;

    // 等待服务器启动
    tokio::time::sleep(Duration::from_millis(100)).await;

    // 创建客户端
    let mut client = NamedPipeClient::new(pipe_path.clone());
    client.connect().await?;

    // 发送消息
    let response = client.send_message("Hello, Named Pipe!").await?;
    println!("收到响应: {}", response);

    // 断开连接
    client.disconnect();

    // 停止服务器
    server.stop()?;

    Ok(())
}
```

## 2. Unix Domain Sockets

### 2.1 Unix Domain Socket 服务器

```rust
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use tokio::sync::mpsc;
use serde::{Deserialize, Serialize};

// Unix Domain Socket 服务器
pub struct UnixSocketServer {
    socket_path: String,
    clients: Arc<Mutex<HashMap<String, UnixStream>>>,
    message_handlers: Arc<Mutex<HashMap<String, Box<dyn Fn(SocketMessage) -> SocketMessage + Send + Sync>>>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SocketMessage {
    pub id: String,
    pub message_type: String,
    pub payload: String,
    pub timestamp: u64,
}

impl UnixSocketServer {
    pub fn new(socket_path: String) -> Self {
        Self {
            socket_path,
            clients: Arc::new(Mutex::new(HashMap::new())),
            message_handlers: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    // 注册消息处理器
    pub fn register_handler(
        &self,
        message_type: String,
        handler: Box<dyn Fn(SocketMessage) -> SocketMessage + Send + Sync>,
    ) {
        let mut handlers = self.message_handlers.lock().unwrap();
        handlers.insert(message_type, handler);
    }

    // 启动服务器
    pub async fn start(&self) -> Result<(), SocketError> {
        // 删除已存在的套接字文件
        if Path::new(&self.socket_path).exists() {
            std::fs::remove_file(&self.socket_path)?;
        }

        // 创建 Unix Domain Socket
        let listener = UnixListener::bind(&self.socket_path)
            .map_err(|e| SocketError::BindFailed(e.to_string()))?;

        println!("Unix Domain Socket 服务器启动，监听: {}", self.socket_path);

        // 异步接受连接
        let clients = self.clients.clone();
        let handlers = self.message_handlers.clone();

        tokio::spawn(async move {
            for stream in listener.incoming() {
                match stream {
                    Ok(stream) => {
                        let client_id = uuid::Uuid::new_v4().to_string();
                        
                        {
                            let mut clients = clients.lock().unwrap();
                            clients.insert(client_id.clone(), stream);
                        }

                        println!("新客户端连接: {}", client_id);

                        // 处理客户端消息
                        let clients_clone = clients.clone();
                        let handlers_clone = handlers.clone();
                        tokio::spawn(async move {
                            Self::handle_client(client_id, clients_clone, handlers_clone).await;
                        });
                    }
                    Err(e) => {
                        eprintln!("接受连接失败: {}", e);
                    }
                }
            }
        });

        Ok(())
    }

    // 处理客户端消息
    async fn handle_client(
        client_id: String,
        clients: Arc<Mutex<HashMap<String, UnixStream>>>,
        handlers: Arc<Mutex<HashMap<String, Box<dyn Fn(SocketMessage) -> SocketMessage + Send + Sync>>>>,
    ) {
        let mut buffer = [0; 4096];
        
        loop {
            // 查找客户端连接
            let mut stream = {
                let mut clients = clients.lock().unwrap();
                if let Some(client_stream) = clients.get_mut(&client_id) {
                    client_stream.try_clone().ok()
                } else {
                    break;
                }
            };

            if let Some(ref mut stream) = stream {
                match stream.read(&mut buffer) {
                    Ok(0) => {
                        // 客户端断开连接
                        break;
                    }
                    Ok(n) => {
                        // 解析消息
                        if let Ok(message_str) = String::from_utf8(buffer[..n].to_vec()) {
                            if let Ok(message) = serde_json::from_str::<SocketMessage>(&message_str) {
                                println!("收到消息: {:?}", message);

                                // 处理消息
                                let response = {
                                    let handlers = handlers.lock().unwrap();
                                    if let Some(handler) = handlers.get(&message.message_type) {
                                        handler(message.clone())
                                    } else {
                                        SocketMessage {
                                            id: uuid::Uuid::new_v4().to_string(),
                                            message_type: "error".to_string(),
                                            payload: "未知消息类型".to_string(),
                                            timestamp: std::time::SystemTime::now()
                                                .duration_since(std::time::UNIX_EPOCH)
                                                .unwrap()
                                                .as_secs(),
                                        }
                                    }
                                };

                                // 发送响应
                                if let Ok(response_str) = serde_json::to_string(&response) {
                                    if let Err(e) = stream.write_all(response_str.as_bytes()) {
                                        eprintln!("发送响应失败: {}", e);
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("读取消息失败: {}", e);
                        break;
                    }
                }
            }
        }

        // 移除客户端
        {
            let mut clients = clients.lock().unwrap();
            clients.remove(&client_id);
        }

        println!("客户端断开连接: {}", client_id);
    }

    // 发送消息到指定客户端
    pub async fn send_to_client(&self, client_id: &str, message: SocketMessage) -> Result<(), SocketError> {
        let mut clients = self.clients.lock().unwrap();
        
        if let Some(client) = clients.get_mut(client_id) {
            let message_str = serde_json::to_string(&message)
                .map_err(|e| SocketError::SerializationFailed(e.to_string()))?;
            
            client.write_all(message_str.as_bytes())
                .map_err(|e| SocketError::SendFailed(e.to_string()))?;
        }

        Ok(())
    }

    // 广播消息
    pub async fn broadcast(&self, message: SocketMessage) -> Result<(), SocketError> {
        let mut clients = self.clients.lock().unwrap();
        let message_str = serde_json::to_string(&message)
            .map_err(|e| SocketError::SerializationFailed(e.to_string()))?;

        let mut failed_clients = Vec::new();

        for (client_id, client) in clients.iter_mut() {
            if let Err(_) = client.write_all(message_str.as_bytes()) {
                failed_clients.push(client_id.clone());
            }
        }

        // 移除失败的客户端
        for client_id in failed_clients {
            clients.remove(&client_id);
        }

        Ok(())
    }

    // 获取客户端数量
    pub fn get_client_count(&self) -> usize {
        self.clients.lock().unwrap().len()
    }

    // 停止服务器
    pub fn stop(&self) -> Result<(), SocketError> {
        if Path::new(&self.socket_path).exists() {
            std::fs::remove_file(&self.socket_path)?;
        }
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum SocketError {
    #[error("绑定失败: {0}")]
    BindFailed(String),
    
    #[error("IO错误: {0}")]
    IoError(#[from] std::io::Error),
    
    #[error("连接失败: {0}")]
    ConnectionFailed(String),
    
    #[error("发送失败: {0}")]
    SendFailed(String),
    
    #[error("序列化失败: {0}")]
    SerializationFailed(String),
}
```

### 2.2 Unix Domain Socket 客户端

```rust
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::time::Duration;
use serde::{Deserialize, Serialize};

// Unix Domain Socket 客户端
pub struct UnixSocketClient {
    socket_path: String,
    stream: Option<UnixStream>,
}

impl UnixSocketClient {
    pub fn new(socket_path: String) -> Self {
        Self {
            socket_path,
            stream: None,
        }
    }

    // 连接到服务器
    pub async fn connect(&mut self) -> Result<(), SocketError> {
        // 等待服务器启动
        while !Path::new(&self.socket_path).exists() {
            tokio::time::sleep(Duration::from_millis(100)).await;
        }

        let stream = UnixStream::connect(&self.socket_path)
            .map_err(|e| SocketError::ConnectionFailed(e.to_string()))?;

        self.stream = Some(stream);
        println!("连接到 Unix Domain Socket 服务器: {}", self.socket_path);

        Ok(())
    }

    // 发送消息
    pub async fn send_message(&mut self, message: SocketMessage) -> Result<SocketMessage, SocketError> {
        if let Some(ref mut stream) = self.stream {
            // 序列化消息
            let message_str = serde_json::to_string(&message)
                .map_err(|e| SocketError::SerializationFailed(e.to_string()))?;

            // 发送消息
            stream.write_all(message_str.as_bytes())
                .map_err(|e| SocketError::SendFailed(e.to_string()))?;

            // 读取响应
            let mut buffer = [0; 4096];
            let n = stream.read(&mut buffer)
                .map_err(|e| SocketError::IoError(e))?;

            // 反序列化响应
            let response_str = String::from_utf8_lossy(&buffer[..n]);
            let response = serde_json::from_str::<SocketMessage>(&response_str)
                .map_err(|e| SocketError::SerializationFailed(e.to_string()))?;

            Ok(response)
        } else {
            Err(SocketError::ConnectionFailed("未连接到服务器".to_string()))
        }
    }

    // 断开连接
    pub fn disconnect(&mut self) {
        self.stream = None;
    }
}

// 使用示例
pub async fn unix_socket_example() -> Result<(), Box<dyn std::error::Error>> {
    let socket_path = "/tmp/unix_socket_example".to_string();
    
    // 启动服务器
    let server = UnixSocketServer::new(socket_path.clone());
    
    // 注册消息处理器
    server.register_handler("echo".to_string(), Box::new(|message| {
        SocketMessage {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: "echo_response".to_string(),
            payload: format!("Echo: {}", message.payload),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        }
    }));

    server.start().await?;

    // 等待服务器启动
    tokio::time::sleep(Duration::from_millis(100)).await;

    // 创建客户端
    let mut client = UnixSocketClient::new(socket_path.clone());
    client.connect().await?;

    // 发送消息
    let message = SocketMessage {
        id: uuid::Uuid::new_v4().to_string(),
        message_type: "echo".to_string(),
        payload: "Hello, Unix Socket!".to_string(),
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs(),
    };

    let response = client.send_message(message).await?;
    println!("收到响应: {:?}", response);

    // 断开连接
    client.disconnect();

    // 停止服务器
    server.stop()?;

    Ok(())
}
```

## 3. 共享内存通信

### 3.1 共享内存管理器

```rust
use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 共享内存管理器
pub struct SharedMemoryManager {
    segments: Arc<RwLock<HashMap<String, SharedMemorySegment>>>,
    config: SharedMemoryConfig,
}

#[derive(Debug, Clone)]
pub struct SharedMemoryConfig {
    pub max_segments: usize,
    pub default_segment_size: usize,
    pub cleanup_interval: Duration,
    pub auto_cleanup: bool,
}

#[derive(Debug)]
pub struct SharedMemorySegment {
    pub id: String,
    pub name: String,
    pub size: usize,
    pub data: Arc<Mutex<Vec<u8>>>,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub access_count: u64,
    pub permissions: SegmentPermissions,
}

#[derive(Debug, Clone)]
pub struct SegmentPermissions {
    pub readable: bool,
    pub writable: bool,
    pub executable: bool,
}

impl SharedMemoryManager {
    pub fn new(config: SharedMemoryConfig) -> Self {
        let manager = Self {
            segments: Arc::new(RwLock::new(HashMap::new())),
            config,
        };

        // 启动自动清理
        if config.auto_cleanup {
            manager.start_cleanup_task();
        }

        manager
    }

    // 创建共享内存段
    pub async fn create_segment(
        &self,
        name: String,
        size: Option<usize>,
        permissions: SegmentPermissions,
    ) -> Result<String, SharedMemoryError> {
        let segment_id = uuid::Uuid::new_v4().to_string();
        let segment_size = size.unwrap_or(self.config.default_segment_size);

        let segment = SharedMemorySegment {
            id: segment_id.clone(),
            name: name.clone(),
            size: segment_size,
            data: Arc::new(Mutex::new(vec![0; segment_size])),
            created_at: Instant::now(),
            last_accessed: Instant::now(),
            access_count: 0,
            permissions,
        };

        {
            let mut segments = self.segments.write().await;
            if segments.len() >= self.config.max_segments {
                return Err(SharedMemoryError::MaxSegmentsExceeded);
            }
            segments.insert(segment_id.clone(), segment);
        }

        println!("创建共享内存段: {} (大小: {} bytes)", name, segment_size);
        Ok(segment_id)
    }

    // 删除共享内存段
    pub async fn delete_segment(&self, segment_id: &str) -> Result<(), SharedMemoryError> {
        let mut segments = self.segments.write().await;
        
        if let Some(segment) = segments.remove(segment_id) {
            println!("删除共享内存段: {}", segment.name);
            Ok(())
        } else {
            Err(SharedMemoryError::SegmentNotFound(segment_id.to_string()))
        }
    }

    // 读取共享内存段
    pub async fn read_segment(
        &self,
        segment_id: &str,
        offset: usize,
        length: usize,
    ) -> Result<Vec<u8>, SharedMemoryError> {
        let mut segments = self.segments.write().await;
        
        if let Some(segment) = segments.get_mut(segment_id) {
            if !segment.permissions.readable {
                return Err(SharedMemoryError::PermissionDenied);
            }

            if offset + length > segment.size {
                return Err(SharedMemoryError::OutOfBounds);
            }

            segment.last_accessed = Instant::now();
            segment.access_count += 1;

            let data = segment.data.lock().unwrap();
            Ok(data[offset..offset + length].to_vec())
        } else {
            Err(SharedMemoryError::SegmentNotFound(segment_id.to_string()))
        }
    }

    // 写入共享内存段
    pub async fn write_segment(
        &self,
        segment_id: &str,
        offset: usize,
        data: &[u8],
    ) -> Result<(), SharedMemoryError> {
        let mut segments = self.segments.write().await;
        
        if let Some(segment) = segments.get_mut(segment_id) {
            if !segment.permissions.writable {
                return Err(SharedMemoryError::PermissionDenied);
            }

            if offset + data.len() > segment.size {
                return Err(SharedMemoryError::OutOfBounds);
            }

            segment.last_accessed = Instant::now();
            segment.access_count += 1;

            let mut segment_data = segment.data.lock().unwrap();
            segment_data[offset..offset + data.len()].copy_from_slice(data);
        } else {
            return Err(SharedMemoryError::SegmentNotFound(segment_id.to_string()));
        }

        Ok(())
    }

    // 获取段信息
    pub async fn get_segment_info(&self, segment_id: &str) -> Result<SegmentInfo, SharedMemoryError> {
        let segments = self.segments.read().await;
        
        if let Some(segment) = segments.get(segment_id) {
            Ok(SegmentInfo {
                id: segment.id.clone(),
                name: segment.name.clone(),
                size: segment.size,
                created_at: segment.created_at,
                last_accessed: segment.last_accessed,
                access_count: segment.access_count,
                permissions: segment.permissions.clone(),
            })
        } else {
            Err(SharedMemoryError::SegmentNotFound(segment_id.to_string()))
        }
    }

    // 列出所有段
    pub async fn list_segments(&self) -> Vec<SegmentInfo> {
        let segments = self.segments.read().await;
        segments.values().map(|segment| SegmentInfo {
            id: segment.id.clone(),
            name: segment.name.clone(),
            size: segment.size,
            created_at: segment.created_at,
            last_accessed: segment.last_accessed,
            access_count: segment.access_count,
            permissions: segment.permissions.clone(),
        }).collect()
    }

    // 启动清理任务
    fn start_cleanup_task(&self) {
        let segments = self.segments.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.cleanup_interval);
            
            loop {
                interval.tick().await;
                
                let mut segments_guard = segments.write().await;
                let now = Instant::now();
                
                // 清理长时间未访问的段
                segments_guard.retain(|_, segment| {
                    now.duration_since(segment.last_accessed) < Duration::from_secs(3600)
                });
            }
        });
    }

    // 获取统计信息
    pub async fn get_statistics(&self) -> SharedMemoryStats {
        let segments = self.segments.read().await;
        
        let total_segments = segments.len();
        let total_size: usize = segments.values().map(|s| s.size).sum();
        let total_access_count: u64 = segments.values().map(|s| s.access_count).sum();
        
        SharedMemoryStats {
            total_segments,
            total_size,
            total_access_count,
            average_segment_size: if total_segments > 0 {
                total_size / total_segments
            } else {
                0
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct SegmentInfo {
    pub id: String,
    pub name: String,
    pub size: usize,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub access_count: u64,
    pub permissions: SegmentPermissions,
}

#[derive(Debug)]
pub struct SharedMemoryStats {
    pub total_segments: usize,
    pub total_size: usize,
    pub total_access_count: u64,
    pub average_segment_size: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum SharedMemoryError {
    #[error("段未找到: {0}")]
    SegmentNotFound(String),
    
    #[error("权限不足")]
    PermissionDenied,
    
    #[error("超出边界")]
    OutOfBounds,
    
    #[error("超过最大段数")]
    MaxSegmentsExceeded,
    
    #[error("操作失败: {0}")]
    OperationFailed(String),
}

// 使用示例
pub async fn shared_memory_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = SharedMemoryConfig {
        max_segments: 100,
        default_segment_size: 1024,
        cleanup_interval: Duration::from_secs(60),
        auto_cleanup: true,
    };

    let manager = SharedMemoryManager::new(config);

    // 创建共享内存段
    let permissions = SegmentPermissions {
        readable: true,
        writable: true,
        executable: false,
    };

    let segment_id = manager.create_segment(
        "test_segment".to_string(),
        Some(512),
        permissions,
    ).await?;

    // 写入数据
    let test_data = b"Hello, Shared Memory!";
    manager.write_segment(&segment_id, 0, test_data).await?;

    // 读取数据
    let read_data = manager.read_segment(&segment_id, 0, test_data.len()).await?;
    println!("读取的数据: {}", String::from_utf8_lossy(&read_data));

    // 获取段信息
    let info = manager.get_segment_info(&segment_id).await?;
    println!("段信息: {:?}", info);

    // 获取统计信息
    let stats = manager.get_statistics().await;
    println!("统计信息: {:?}", stats);

    // 删除段
    manager.delete_segment(&segment_id).await?;

    Ok(())
}
```

## 4. 消息队列

### 4.1 消息队列实现

```rust
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, mpsc};
use serde::{Deserialize, Serialize};

// 消息队列
pub struct MessageQueue {
    queues: Arc<RwLock<HashMap<String, Queue>>>,
    subscribers: Arc<RwLock<HashMap<String, Vec<Subscriber>>>>,
    config: QueueConfig,
}

#[derive(Debug, Clone)]
pub struct QueueConfig {
    pub max_queue_size: usize,
    pub message_ttl: Duration,
    pub max_retries: u32,
    pub cleanup_interval: Duration,
    pub auto_cleanup: bool,
}

#[derive(Debug)]
pub struct Queue {
    pub name: String,
    pub messages: VecDeque<Message>,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub message_count: u64,
    pub total_messages: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub id: String,
    pub queue_name: String,
    pub payload: String,
    pub priority: MessagePriority,
    pub created_at: Instant,
    pub expires_at: Option<Instant>,
    pub retry_count: u32,
    pub max_retries: u32,
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum MessagePriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

#[derive(Debug)]
pub struct Subscriber {
    pub id: String,
    pub queue_name: String,
    pub callback: Arc<dyn Fn(Message) -> Result<(), String> + Send + Sync>,
    pub created_at: Instant,
    pub last_message: Option<Instant>,
    pub message_count: u64,
}

impl MessageQueue {
    pub fn new(config: QueueConfig) -> Self {
        let queue = Self {
            queues: Arc::new(RwLock::new(HashMap::new())),
            subscribers: Arc::new(RwLock::new(HashMap::new())),
            config,
        };

        // 启动自动清理
        if config.auto_cleanup {
            queue.start_cleanup_task();
        }

        queue
    }

    // 创建队列
    pub async fn create_queue(&self, name: String) -> Result<(), QueueError> {
        let queue = Queue {
            name: name.clone(),
            messages: VecDeque::new(),
            created_at: Instant::now(),
            last_accessed: Instant::now(),
            message_count: 0,
            total_messages: 0,
        };

        {
            let mut queues = self.queues.write().await;
            queues.insert(name, queue);
        }

        Ok(())
    }

    // 发布消息
    pub async fn publish_message(
        &self,
        queue_name: &str,
        payload: String,
        priority: MessagePriority,
        ttl: Option<Duration>,
    ) -> Result<String, QueueError> {
        let message_id = uuid::Uuid::new_v4().to_string();
        let expires_at = ttl.map(|ttl| Instant::now() + ttl);

        let message = Message {
            id: message_id.clone(),
            queue_name: queue_name.to_string(),
            payload,
            priority,
            created_at: Instant::now(),
            expires_at,
            retry_count: 0,
            max_retries: self.config.max_retries,
            metadata: HashMap::new(),
        };

        {
            let mut queues = self.queues.write().await;
            if let Some(queue) = queues.get_mut(queue_name) {
                if queue.messages.len() >= self.config.max_queue_size {
                    return Err(QueueError::QueueFull);
                }

                queue.messages.push_back(message);
                queue.message_count += 1;
                queue.total_messages += 1;
                queue.last_accessed = Instant::now();
            } else {
                return Err(QueueError::QueueNotFound(queue_name.to_string()));
            }
        }

        // 通知订阅者
        self.notify_subscribers(queue_name, message).await;

        Ok(message_id)
    }

    // 消费消息
    pub async fn consume_message(&self, queue_name: &str) -> Result<Option<Message>, QueueError> {
        let mut queues = self.queues.write().await;
        
        if let Some(queue) = queues.get_mut(queue_name) {
            // 按优先级排序消息
            let mut messages: Vec<_> = queue.messages.drain(..).collect();
            messages.sort_by(|a, b| b.priority.cmp(&a.priority));
            
            // 查找未过期的消息
            let now = Instant::now();
            for (i, message) in messages.iter().enumerate() {
                if let Some(expires_at) = message.expires_at {
                    if now > expires_at {
                        continue;
                    }
                }
                
                // 找到有效消息
                let message = messages.remove(i);
                queue.messages.extend(messages);
                queue.last_accessed = Instant::now();
                
                return Ok(Some(message));
            }
            
            // 没有有效消息
            queue.messages.extend(messages);
            Ok(None)
        } else {
            Err(QueueError::QueueNotFound(queue_name.to_string()))
        }
    }

    // 确认消息
    pub async fn acknowledge_message(&self, queue_name: &str, message_id: &str) -> Result<(), QueueError> {
        let mut queues = self.queues.write().await;
        
        if let Some(queue) = queues.get_mut(queue_name) {
            queue.messages.retain(|msg| msg.id != message_id);
            queue.message_count = queue.messages.len() as u64;
        }

        Ok(())
    }

    // 订阅队列
    pub async fn subscribe(
        &self,
        queue_name: &str,
        callback: Arc<dyn Fn(Message) -> Result<(), String> + Send + Sync>,
    ) -> Result<String, QueueError> {
        let subscriber_id = uuid::Uuid::new_v4().to_string();
        
        let subscriber = Subscriber {
            id: subscriber_id.clone(),
            queue_name: queue_name.to_string(),
            callback,
            created_at: Instant::now(),
            last_message: None,
            message_count: 0,
        };

        {
            let mut subscribers = self.subscribers.write().await;
            subscribers.entry(queue_name.to_string())
                .or_insert_with(Vec::new)
                .push(subscriber);
        }

        Ok(subscriber_id)
    }

    // 通知订阅者
    async fn notify_subscribers(&self, queue_name: &str, message: Message) {
        let subscribers = self.subscribers.read().await;
        
        if let Some(queue_subscribers) = subscribers.get(queue_name) {
            for subscriber in queue_subscribers {
                let callback = subscriber.callback.clone();
                let message_clone = message.clone();
                
                tokio::spawn(async move {
                    if let Err(e) = callback(message_clone) {
                        eprintln!("订阅者处理消息失败: {}", e);
                    }
                });
            }
        }
    }

    // 获取队列统计
    pub async fn get_queue_stats(&self, queue_name: &str) -> Result<QueueStats, QueueError> {
        let queues = self.queues.read().await;
        
        if let Some(queue) = queues.get(queue_name) {
            Ok(QueueStats {
                name: queue.name.clone(),
                message_count: queue.message_count,
                total_messages: queue.total_messages,
                created_at: queue.created_at,
                last_accessed: queue.last_accessed,
            })
        } else {
            Err(QueueError::QueueNotFound(queue_name.to_string()))
        }
    }

    // 启动清理任务
    fn start_cleanup_task(&self) {
        let queues = self.queues.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.cleanup_interval);
            
            loop {
                interval.tick().await;
                
                let mut queues_guard = queues.write().await;
                let now = Instant::now();
                
                // 清理过期消息
                for queue in queues_guard.values_mut() {
                    queue.messages.retain(|msg| {
                        if let Some(expires_at) = msg.expires_at {
                            now < expires_at
                        } else {
                            true
                        }
                    });
                    queue.message_count = queue.messages.len() as u64;
                }
            }
        });
    }
}

#[derive(Debug)]
pub struct QueueStats {
    pub name: String,
    pub message_count: u64,
    pub total_messages: u64,
    pub created_at: Instant,
    pub last_accessed: Instant,
}

#[derive(Debug, thiserror::Error)]
pub enum QueueError {
    #[error("队列未找到: {0}")]
    QueueNotFound(String),
    
    #[error("队列已满")]
    QueueFull,
    
    #[error("消息未找到: {0}")]
    MessageNotFound(String),
    
    #[error("订阅失败: {0}")]
    SubscriptionFailed(String),
    
    #[error("操作失败: {0}")]
    OperationFailed(String),
}

// 使用示例
pub async fn message_queue_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = QueueConfig {
        max_queue_size: 1000,
        message_ttl: Duration::from_secs(300),
        max_retries: 3,
        cleanup_interval: Duration::from_secs(60),
        auto_cleanup: true,
    };

    let queue = MessageQueue::new(config);

    // 创建队列
    queue.create_queue("test_queue".to_string()).await?;

    // 订阅队列
    let callback = Arc::new(|message: Message| -> Result<(), String> {
        println!("收到消息: {}", message.payload);
        Ok(())
    });

    queue.subscribe("test_queue", callback).await?;

    // 发布消息
    let message_id = queue.publish_message(
        "test_queue",
        "Hello, Message Queue!".to_string(),
        MessagePriority::Normal,
        Some(Duration::from_secs(60)),
    ).await?;

    println!("发布消息: {}", message_id);

    // 消费消息
    if let Some(message) = queue.consume_message("test_queue").await? {
        println!("消费消息: {}", message.payload);
        
        // 确认消息
        queue.acknowledge_message("test_queue", &message.id).await?;
    }

    // 获取队列统计
    let stats = queue.get_queue_stats("test_queue").await?;
    println!("队列统计: {:?}", stats);

    Ok(())
}
```

## 5. 信号量同步

### 5.1 信号量实现

```rust
use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};

// 信号量管理器
pub struct SemaphoreManager {
    semaphores: Arc<RwLock<HashMap<String, ManagedSemaphore>>>,
    config: SemaphoreConfig,
}

#[derive(Debug, Clone)]
pub struct SemaphoreConfig {
    pub max_semaphores: usize,
    pub default_permits: usize,
    pub timeout: Duration,
    pub auto_cleanup: bool,
    pub cleanup_interval: Duration,
}

#[derive(Debug)]
pub struct ManagedSemaphore {
    pub name: String,
    pub semaphore: Arc<Semaphore>,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub total_permits: usize,
    pub available_permits: usize,
    pub waiters: u32,
    pub acquired_count: u64,
    pub released_count: u64,
}

impl SemaphoreManager {
    pub fn new(config: SemaphoreConfig) -> Self {
        let manager = Self {
            semaphores: Arc::new(RwLock::new(HashMap::new())),
            config,
        };

        // 启动自动清理
        if config.auto_cleanup {
            manager.start_cleanup_task();
        }

        manager
    }

    // 创建信号量
    pub async fn create_semaphore(
        &self,
        name: String,
        permits: Option<usize>,
    ) -> Result<(), SemaphoreError> {
        let total_permits = permits.unwrap_or(self.config.default_permits);
        let semaphore = Arc::new(Semaphore::new(total_permits));

        let managed_semaphore = ManagedSemaphore {
            name: name.clone(),
            semaphore,
            created_at: Instant::now(),
            last_accessed: Instant::now(),
            total_permits,
            available_permits: total_permits,
            waiters: 0,
            acquired_count: 0,
            released_count: 0,
        };

        {
            let mut semaphores = self.semaphores.write().await;
            if semaphores.len() >= self.config.max_semaphores {
                return Err(SemaphoreError::MaxSemaphoresExceeded);
            }
            semaphores.insert(name, managed_semaphore);
        }

        Ok(())
    }

    // 获取信号量许可
    pub async fn acquire(&self, name: &str) -> Result<SemaphorePermit, SemaphoreError> {
        let semaphore = {
            let mut semaphores = self.semaphores.write().await;
            if let Some(managed_semaphore) = semaphores.get_mut(name) {
                managed_semaphore.last_accessed = Instant::now();
                managed_semaphore.waiters += 1;
                managed_semaphore.semaphore.clone()
            } else {
                return Err(SemaphoreError::SemaphoreNotFound(name.to_string()));
            }
        };

        // 尝试获取许可
        let permit = semaphore.acquire().await
            .map_err(|_| SemaphoreError::AcquireFailed)?;

        // 更新统计信息
        {
            let mut semaphores = self.semaphores.write().await;
            if let Some(managed_semaphore) = semaphores.get_mut(name) {
                managed_semaphore.waiters -= 1;
                managed_semaphore.acquired_count += 1;
                managed_semaphore.available_permits -= 1;
            }
        }

        Ok(SemaphorePermit {
            name: name.to_string(),
            permit,
            manager: self.clone(),
        })
    }

    // 释放信号量许可
    pub async fn release(&self, name: &str) -> Result<(), SemaphoreError> {
        {
            let mut semaphores = self.semaphores.write().await;
            if let Some(managed_semaphore) = semaphores.get_mut(name) {
                managed_semaphore.last_accessed = Instant::now();
                managed_semaphore.released_count += 1;
                managed_semaphore.available_permits += 1;
            } else {
                return Err(SemaphoreError::SemaphoreNotFound(name.to_string()));
            }
        }

        Ok(())
    }

    // 尝试获取信号量许可（非阻塞）
    pub async fn try_acquire(&self, name: &str) -> Result<Option<SemaphorePermit>, SemaphoreError> {
        let semaphore = {
            let mut semaphores = self.semaphores.write().await;
            if let Some(managed_semaphore) = semaphores.get_mut(name) {
                managed_semaphore.last_accessed = Instant::now();
                managed_semaphore.semaphore.clone()
            } else {
                return Err(SemaphoreError::SemaphoreNotFound(name.to_string()));
            }
        };

        // 尝试获取许可
        if let Ok(permit) = semaphore.try_acquire() {
            // 更新统计信息
            {
                let mut semaphores = self.semaphores.write().await;
                if let Some(managed_semaphore) = semaphores.get_mut(name) {
                    managed_semaphore.acquired_count += 1;
                    managed_semaphore.available_permits -= 1;
                }
            }

            Ok(Some(SemaphorePermit {
                name: name.to_string(),
                permit,
                manager: self.clone(),
            }))
        } else {
            Ok(None)
        }
    }

    // 获取信号量信息
    pub async fn get_semaphore_info(&self, name: &str) -> Result<SemaphoreInfo, SemaphoreError> {
        let semaphores = self.semaphores.read().await;
        
        if let Some(managed_semaphore) = semaphores.get(name) {
            Ok(SemaphoreInfo {
                name: managed_semaphore.name.clone(),
                total_permits: managed_semaphore.total_permits,
                available_permits: managed_semaphore.available_permits,
                waiters: managed_semaphore.waiters,
                acquired_count: managed_semaphore.acquired_count,
                released_count: managed_semaphore.released_count,
                created_at: managed_semaphore.created_at,
                last_accessed: managed_semaphore.last_accessed,
            })
        } else {
            Err(SemaphoreError::SemaphoreNotFound(name.to_string()))
        }
    }

    // 列出所有信号量
    pub async fn list_semaphores(&self) -> Vec<SemaphoreInfo> {
        let semaphores = self.semaphores.read().await;
        semaphores.values().map(|managed_semaphore| SemaphoreInfo {
            name: managed_semaphore.name.clone(),
            total_permits: managed_semaphore.total_permits,
            available_permits: managed_semaphore.available_permits,
            waiters: managed_semaphore.waiters,
            acquired_count: managed_semaphore.acquired_count,
            released_count: managed_semaphore.released_count,
            created_at: managed_semaphore.created_at,
            last_accessed: managed_semaphore.last_accessed,
        }).collect()
    }

    // 启动清理任务
    fn start_cleanup_task(&self) {
        let semaphores = self.semaphores.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.cleanup_interval);
            
            loop {
                interval.tick().await;
                
                let mut semaphores_guard = semaphores.write().await;
                let now = Instant::now();
                
                // 清理长时间未访问的信号量
                semaphores_guard.retain(|_, semaphore| {
                    now.duration_since(semaphore.last_accessed) < Duration::from_secs(3600)
                });
            }
        });
    }

    // 获取统计信息
    pub async fn get_statistics(&self) -> SemaphoreStats {
        let semaphores = self.semaphores.read().await;
        
        let total_semaphores = semaphores.len();
        let total_permits: usize = semaphores.values().map(|s| s.total_permits).sum();
        let available_permits: usize = semaphores.values().map(|s| s.available_permits).sum();
        let total_waiters: u32 = semaphores.values().map(|s| s.waiters).sum();
        
        SemaphoreStats {
            total_semaphores,
            total_permits,
            available_permits,
            total_waiters,
            utilization_rate: if total_permits > 0 {
                (total_permits - available_permits) as f64 / total_permits as f64
            } else {
                0.0
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct SemaphoreInfo {
    pub name: String,
    pub total_permits: usize,
    pub available_permits: usize,
    pub waiters: u32,
    pub acquired_count: u64,
    pub released_count: u64,
    pub created_at: Instant,
    pub last_accessed: Instant,
}

#[derive(Debug)]
pub struct SemaphoreStats {
    pub total_semaphores: usize,
    pub total_permits: usize,
    pub available_permits: usize,
    pub total_waiters: u32,
    pub utilization_rate: f64,
}

// 信号量许可
pub struct SemaphorePermit {
    name: String,
    permit: tokio::sync::SemaphorePermit<'static>,
    manager: SemaphoreManager,
}

impl Drop for SemaphorePermit {
    fn drop(&mut self) {
        let manager = self.manager.clone();
        let name = self.name.clone();
        
        tokio::spawn(async move {
            let _ = manager.release(&name).await;
        });
    }
}

#[derive(Debug, thiserror::Error)]
pub enum SemaphoreError {
    #[error("信号量未找到: {0}")]
    SemaphoreNotFound(String),
    
    #[error("获取许可失败")]
    AcquireFailed,
    
    #[error("超过最大信号量数")]
    MaxSemaphoresExceeded,
    
    #[error("操作失败: {0}")]
    OperationFailed(String),
}

// 使用示例
pub async fn semaphore_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = SemaphoreConfig {
        max_semaphores: 100,
        default_permits: 5,
        timeout: Duration::from_secs(30),
        auto_cleanup: true,
        cleanup_interval: Duration::from_secs(60),
    };

    let manager = SemaphoreManager::new(config);

    // 创建信号量
    manager.create_semaphore("test_semaphore".to_string(), Some(3)).await?;

    // 获取许可
    let permit1 = manager.acquire("test_semaphore").await?;
    println!("获取许可 1");

    let permit2 = manager.acquire("test_semaphore").await?;
    println!("获取许可 2");

    // 尝试获取许可（非阻塞）
    if let Some(permit3) = manager.try_acquire("test_semaphore").await? {
        println!("获取许可 3");
        drop(permit3);
    } else {
        println!("无法获取许可 3");
    }

    // 获取信号量信息
    let info = manager.get_semaphore_info("test_semaphore").await?;
    println!("信号量信息: {:?}", info);

    // 获取统计信息
    let stats = manager.get_statistics().await;
    println!("统计信息: {:?}", stats);

    // 释放许可
    drop(permit1);
    drop(permit2);

    Ok(())
}
```

## 6. 内存映射文件

### 6.1 内存映射文件管理器

```rust
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::Path;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 内存映射文件管理器
pub struct MemoryMappedFileManager {
    mapped_files: Arc<RwLock<HashMap<String, MappedFile>>>,
    config: MmapConfig,
}

#[derive(Debug, Clone)]
pub struct MmapConfig {
    pub max_mapped_files: usize,
    pub default_file_size: usize,
    pub sync_interval: Duration,
    pub auto_sync: bool,
    pub cleanup_interval: Duration,
    pub auto_cleanup: bool,
}

#[derive(Debug)]
pub struct MappedFile {
    pub id: String,
    pub path: String,
    pub size: usize,
    pub data: Arc<Mutex<Vec<u8>>>,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub last_modified: Instant,
    pub access_count: u64,
    pub is_dirty: bool,
    pub permissions: FilePermissions,
}

#[derive(Debug, Clone)]
pub struct FilePermissions {
    pub readable: bool,
    pub writable: bool,
    pub executable: bool,
}

impl MemoryMappedFileManager {
    pub fn new(config: MmapConfig) -> Self {
        let manager = Self {
            mapped_files: Arc::new(RwLock::new(HashMap::new())),
            config,
        };

        // 启动自动同步
        if config.auto_sync {
            manager.start_sync_task();
        }

        // 启动自动清理
        if config.auto_cleanup {
            manager.start_cleanup_task();
        }

        manager
    }

    // 映射文件
    pub async fn map_file(
        &self,
        path: String,
        size: Option<usize>,
        permissions: FilePermissions,
    ) -> Result<String, MmapError> {
        let file_id = uuid::Uuid::new_v4().to_string();
        let file_size = size.unwrap_or(self.config.default_file_size);

        // 创建或打开文件
        let file = if Path::new(&path).exists() {
            File::open(&path)?
        } else {
            File::create(&path)?
        };

        // 设置文件大小
        file.set_len(file_size as u64)?;

        // 读取文件内容
        let mut data = vec![0; file_size];
        file.read_exact(&mut data)?;

        let mapped_file = MappedFile {
            id: file_id.clone(),
            path: path.clone(),
            size: file_size,
            data: Arc::new(Mutex::new(data)),
            created_at: Instant::now(),
            last_accessed: Instant::now(),
            last_modified: Instant::now(),
            access_count: 0,
            is_dirty: false,
            permissions,
        };

        {
            let mut mapped_files = self.mapped_files.write().await;
            if mapped_files.len() >= self.config.max_mapped_files {
                return Err(MmapError::MaxFilesExceeded);
            }
            mapped_files.insert(file_id.clone(), mapped_file);
        }

        println!("映射文件: {} (大小: {} bytes)", path, file_size);
        Ok(file_id)
    }

    // 取消映射文件
    pub async fn unmap_file(&self, file_id: &str) -> Result<(), MmapError> {
        let mapped_file = {
            let mut mapped_files = self.mapped_files.write().await;
            mapped_files.remove(file_id)
        };

        if let Some(mapped_file) = mapped_file {
            // 同步文件
            if mapped_file.is_dirty {
                self.sync_file(&mapped_file).await?;
            }

            println!("取消映射文件: {}", mapped_file.path);
            Ok(())
        } else {
            Err(MmapError::FileNotFound(file_id.to_string()))
        }
    }

    // 读取文件
    pub async fn read_file(
        &self,
        file_id: &str,
        offset: usize,
        length: usize,
    ) -> Result<Vec<u8>, MmapError> {
        let mut mapped_files = self.mapped_files.write().await;
        
        if let Some(mapped_file) = mapped_files.get_mut(file_id) {
            if !mapped_file.permissions.readable {
                return Err(MmapError::PermissionDenied);
            }

            if offset + length > mapped_file.size {
                return Err(MmapError::OutOfBounds);
            }

            mapped_file.last_accessed = Instant::now();
            mapped_file.access_count += 1;

            let data = mapped_file.data.lock().unwrap();
            Ok(data[offset..offset + length].to_vec())
        } else {
            Err(MmapError::FileNotFound(file_id.to_string()))
        }
    }

    // 写入文件
    pub async fn write_file(
        &self,
        file_id: &str,
        offset: usize,
        data: &[u8],
    ) -> Result<(), MmapError> {
        let mut mapped_files = self.mapped_files.write().await;
        
        if let Some(mapped_file) = mapped_files.get_mut(file_id) {
            if !mapped_file.permissions.writable {
                return Err(MmapError::PermissionDenied);
            }

            if offset + data.len() > mapped_file.size {
                return Err(MmapError::OutOfBounds);
            }

            mapped_file.last_accessed = Instant::now();
            mapped_file.last_modified = Instant::now();
            mapped_file.access_count += 1;
            mapped_file.is_dirty = true;

            let mut file_data = mapped_file.data.lock().unwrap();
            file_data[offset..offset + data.len()].copy_from_slice(data);
        } else {
            return Err(MmapError::FileNotFound(file_id.to_string()));
        }

        Ok(())
    }

    // 同步文件
    pub async fn sync_file(&self, mapped_file: &MappedFile) -> Result<(), MmapError> {
        let mut file = File::create(&mapped_file.path)?;
        let data = mapped_file.data.lock().unwrap();
        file.write_all(&data)?;
        file.sync_all()?;
        Ok(())
    }

    // 强制同步所有文件
    pub async fn sync_all(&self) -> Result<(), MmapError> {
        let mapped_files = self.mapped_files.read().await;
        
        for mapped_file in mapped_files.values() {
            if mapped_file.is_dirty {
                self.sync_file(mapped_file).await?;
            }
        }

        Ok(())
    }

    // 获取文件信息
    pub async fn get_file_info(&self, file_id: &str) -> Result<FileInfo, MmapError> {
        let mapped_files = self.mapped_files.read().await;
        
        if let Some(mapped_file) = mapped_files.get(file_id) {
            Ok(FileInfo {
                id: mapped_file.id.clone(),
                path: mapped_file.path.clone(),
                size: mapped_file.size,
                created_at: mapped_file.created_at,
                last_accessed: mapped_file.last_accessed,
                last_modified: mapped_file.last_modified,
                access_count: mapped_file.access_count,
                is_dirty: mapped_file.is_dirty,
                permissions: mapped_file.permissions.clone(),
            })
        } else {
            Err(MmapError::FileNotFound(file_id.to_string()))
        }
    }

    // 列出所有文件
    pub async fn list_files(&self) -> Vec<FileInfo> {
        let mapped_files = self.mapped_files.read().await;
        mapped_files.values().map(|mapped_file| FileInfo {
            id: mapped_file.id.clone(),
            path: mapped_file.path.clone(),
            size: mapped_file.size,
            created_at: mapped_file.created_at,
            last_accessed: mapped_file.last_accessed,
            last_modified: mapped_file.last_modified,
            access_count: mapped_file.access_count,
            is_dirty: mapped_file.is_dirty,
            permissions: mapped_file.permissions.clone(),
        }).collect()
    }

    // 启动同步任务
    fn start_sync_task(&self) {
        let mapped_files = self.mapped_files.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.sync_interval);
            
            loop {
                interval.tick().await;
                
                let mapped_files_guard = mapped_files.read().await;
                for mapped_file in mapped_files_guard.values() {
                    if mapped_file.is_dirty {
                        // 异步同步文件
                        let manager = Self {
                            mapped_files: mapped_files.clone(),
                            config: config.clone(),
                        };
                        
                        if let Err(e) = manager.sync_file(mapped_file).await {
                            eprintln!("同步文件失败: {}", e);
                        }
                    }
                }
            }
        });
    }

    // 启动清理任务
    fn start_cleanup_task(&self) {
        let mapped_files = self.mapped_files.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.cleanup_interval);
            
            loop {
                interval.tick().await;
                
                let mut mapped_files_guard = mapped_files.write().await;
                let now = Instant::now();
                
                // 清理长时间未访问的文件
                mapped_files_guard.retain(|_, mapped_file| {
                    now.duration_since(mapped_file.last_accessed) < Duration::from_secs(3600)
                });
            }
        });
    }

    // 获取统计信息
    pub async fn get_statistics(&self) -> MmapStats {
        let mapped_files = self.mapped_files.read().await;
        
        let total_files = mapped_files.len();
        let total_size: usize = mapped_files.values().map(|f| f.size).sum();
        let dirty_files = mapped_files.values().filter(|f| f.is_dirty).count();
        let total_access_count: u64 = mapped_files.values().map(|f| f.access_count).sum();
        
        MmapStats {
            total_files,
            total_size,
            dirty_files,
            total_access_count,
            average_file_size: if total_files > 0 {
                total_size / total_files
            } else {
                0
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct FileInfo {
    pub id: String,
    pub path: String,
    pub size: usize,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub last_modified: Instant,
    pub access_count: u64,
    pub is_dirty: bool,
    pub permissions: FilePermissions,
}

#[derive(Debug)]
pub struct MmapStats {
    pub total_files: usize,
    pub total_size: usize,
    pub dirty_files: usize,
    pub total_access_count: u64,
    pub average_file_size: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum MmapError {
    #[error("文件未找到: {0}")]
    FileNotFound(String),
    
    #[error("权限不足")]
    PermissionDenied,
    
    #[error("超出边界")]
    OutOfBounds,
    
    #[error("超过最大文件数")]
    MaxFilesExceeded,
    
    #[error("IO错误: {0}")]
    IoError(#[from] io::Error),
    
    #[error("操作失败: {0}")]
    OperationFailed(String),
}

// 使用示例
pub async fn memory_mapped_file_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = MmapConfig {
        max_mapped_files: 100,
        default_file_size: 1024,
        sync_interval: Duration::from_secs(30),
        auto_sync: true,
        cleanup_interval: Duration::from_secs(60),
        auto_cleanup: true,
    };

    let manager = MemoryMappedFileManager::new(config);

    // 映射文件
    let permissions = FilePermissions {
        readable: true,
        writable: true,
        executable: false,
    };

    let file_id = manager.map_file(
        "/tmp/test_mmap".to_string(),
        Some(512),
        permissions,
    ).await?;

    // 写入数据
    let test_data = b"Hello, Memory Mapped File!";
    manager.write_file(&file_id, 0, test_data).await?;

    // 读取数据
    let read_data = manager.read_file(&file_id, 0, test_data.len()).await?;
    println!("读取的数据: {}", String::from_utf8_lossy(&read_data));

    // 获取文件信息
    let info = manager.get_file_info(&file_id).await?;
    println!("文件信息: {:?}", info);

    // 同步文件
    manager.sync_all().await?;

    // 获取统计信息
    let stats = manager.get_statistics().await;
    println!("统计信息: {:?}", stats);

    // 取消映射文件
    manager.unmap_file(&file_id).await?;

    Ok(())
}
```

## 总结

本章提供了高级 IPC 通信的完整示例，包括：

1. **命名管道** - 基于 Unix Domain Socket 的进程间通信
2. **Unix Domain Sockets** - 高性能的本地套接字通信
3. **共享内存** - 高效的内存共享机制
4. **消息队列** - 异步消息传递系统
5. **信号量** - 进程同步和资源控制
6. **内存映射文件** - 文件内存映射技术

这些示例展示了如何在 Rust 1.90 中实现各种 IPC 通信机制，提供了完整的错误处理、资源管理和监控功能。
