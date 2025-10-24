# WebSocket 通信指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](STYLE.md)。


## 📊 目录

- [📋 目录](#目录)
- [🎯 概述](#概述)
  - [主要特性](#主要特性)
- [⚡ 快速开始](#快速开始)
  - [基础WebSocket通信](#基础websocket通信)
  - [运行示例](#运行示例)
- [🔧 基础用法](#基础用法)
  - [创建WebSocket服务器](#创建websocket服务器)
  - [创建WebSocket客户端](#创建websocket客户端)
- [🔌 WebSocket 服务器](#websocket-服务器)
  - [基础服务器实现](#基础服务器实现)
  - [多客户端管理](#多客户端管理)
  - [房间管理](#房间管理)
- [📱 WebSocket 客户端](#websocket-客户端)
  - [基础客户端实现](#基础客户端实现)
  - [自动重连客户端](#自动重连客户端)
  - [订阅-发布客户端](#订阅-发布客户端)
- [📨 消息处理](#消息处理)
  - [消息类型](#消息类型)
  - [消息序列化](#消息序列化)
  - [消息路由](#消息路由)
- [🔒 安全 WebSocket](#安全-websocket)
  - [WSS (WebSocket Secure) 服务器](#wss-websocket-secure-服务器)
  - [WSS 客户端](#wss-客户端)
  - [身份验证](#身份验证)
- [📊 高级特性](#高级特性)
  - [心跳机制](#心跳机制)
  - [消息压缩](#消息压缩)
  - [消息队列](#消息队列)
- [⚙️ 配置选项](#️-配置选项)
  - [WebSocketConfig 完整配置](#websocketconfig-完整配置)
  - [环境变量配置](#环境变量配置)
- [🔍 错误处理](#错误处理)
  - [错误类型](#错误类型)
  - [重连机制](#重连机制)
- [📈 性能优化](#性能优化)
  - [连接池](#连接池)
  - [消息批处理](#消息批处理)
- [🧪 测试示例](#测试示例)
  - [单元测试](#单元测试)
  - [集成测试](#集成测试)
  - [性能测试](#性能测试)
- [❓ 常见问题](#常见问题)
  - [Q: 如何设置WebSocket超时？](#q-如何设置websocket超时)
  - [Q: 如何处理连接断开？](#q-如何处理连接断开)
  - [Q: 如何启用消息压缩？](#q-如何启用消息压缩)
  - [Q: 如何实现心跳机制？](#q-如何实现心跳机制)
  - [Q: 如何设置最大消息大小？](#q-如何设置最大消息大小)
  - [Q: 如何启用TLS支持？](#q-如何启用tls支持)
  - [Q: 如何处理大量并发连接？](#q-如何处理大量并发连接)
  - [Q: 如何实现消息路由？](#q-如何实现消息路由)


## 📋 目录

- [WebSocket 通信指南](#websocket-通信指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [主要特性](#主要特性)
  - [⚡ 快速开始](#-快速开始)
    - [基础WebSocket通信](#基础websocket通信)
    - [运行示例](#运行示例)
  - [🔧 基础用法](#-基础用法)
    - [创建WebSocket服务器](#创建websocket服务器)
    - [创建WebSocket客户端](#创建websocket客户端)
  - [🔌 WebSocket 服务器](#-websocket-服务器)
    - [基础服务器实现](#基础服务器实现)
    - [多客户端管理](#多客户端管理)
    - [房间管理](#房间管理)
  - [📱 WebSocket 客户端](#-websocket-客户端)
    - [基础客户端实现](#基础客户端实现)
    - [自动重连客户端](#自动重连客户端)
    - [订阅-发布客户端](#订阅-发布客户端)
  - [📨 消息处理](#-消息处理)
    - [消息类型](#消息类型)
    - [消息序列化](#消息序列化)
    - [消息路由](#消息路由)
  - [🔒 安全 WebSocket](#-安全-websocket)
    - [WSS (WebSocket Secure) 服务器](#wss-websocket-secure-服务器)
    - [WSS 客户端](#wss-客户端)
    - [身份验证](#身份验证)
  - [📊 高级特性](#-高级特性)
    - [心跳机制](#心跳机制)
    - [消息压缩](#消息压缩)
    - [消息队列](#消息队列)
  - [⚙️ 配置选项](#️-配置选项)
    - [WebSocketConfig 完整配置](#websocketconfig-完整配置)
    - [环境变量配置](#环境变量配置)
  - [🔍 错误处理](#-错误处理)
    - [错误类型](#错误类型)
    - [重连机制](#重连机制)
  - [📈 性能优化](#-性能优化)
    - [连接池](#连接池)
    - [消息批处理](#消息批处理)
  - [🧪 测试示例](#-测试示例)
    - [单元测试](#单元测试)
    - [集成测试](#集成测试)
    - [性能测试](#性能测试)
  - [❓ 常见问题](#-常见问题)
    - [Q: 如何设置WebSocket超时？](#q-如何设置websocket超时)
    - [Q: 如何处理连接断开？](#q-如何处理连接断开)
    - [Q: 如何启用消息压缩？](#q-如何启用消息压缩)
    - [Q: 如何实现心跳机制？](#q-如何实现心跳机制)
    - [Q: 如何设置最大消息大小？](#q-如何设置最大消息大小)
    - [Q: 如何启用TLS支持？](#q-如何启用tls支持)
    - [Q: 如何处理大量并发连接？](#q-如何处理大量并发连接)
    - [Q: 如何实现消息路由？](#q-如何实现消息路由)

## 🎯 概述

WebSocket 是一种在单个TCP连接上进行全双工通信的协议。C10 Networks 提供了完整的WebSocket实现，支持客户端和服务器端功能。

### 主要特性

- **全双工通信**: 客户端和服务器可以同时发送和接收数据
- **低延迟**: 相比HTTP轮询，延迟更低
- **协议支持**: 支持WebSocket协议的所有帧类型
- **安全连接**: 支持WSS（WebSocket Secure）
- **心跳机制**: 连接保活和健康检查
- **扩展支持**: 自定义扩展协议

## ⚡ 快速开始

### 基础WebSocket通信

```rust
use c10_networks::protocol::websocket::{WebSocketServer, WebSocketClient, WebSocketMessage};
use c10_networks::error::NetworkResult;

// 服务器端
#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 启动WebSocket服务器
    let server = WebSocketServer::new("127.0.0.1:8080").await?;
    println!("WebSocket服务器启动在 ws://127.0.0.1:8080");
    
    loop {
        let (mut connection, addr) = server.accept().await?;
        println!("新连接来自: {}", addr);
        
        tokio::spawn(async move {
            while let Some(message) = connection.receive().await? {
                match message {
                    WebSocketMessage::Text(text) => {
                        println!("收到文本消息: {}", text);
                        // 回显消息
                        connection.send_text(format!("Echo: {}", text)).await?;
                    }
                    WebSocketMessage::Binary(data) => {
                        println!("收到二进制消息: {} 字节", data.len());
                        // 回显二进制数据
                        connection.send_binary(data).await?;
                    }
                    WebSocketMessage::Close => {
                        println!("连接关闭");
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

### 运行示例

```bash
# 终端1: 启动服务器
cargo run --example ws_echo_server

# 终端2: 启动客户端
cargo run --example ws_echo_client
```

## 🔧 基础用法

### 创建WebSocket服务器

```rust
use c10_networks::protocol::websocket::{WebSocketServer, WebSocketConfig};

// 使用默认配置
let server = WebSocketServer::new("127.0.0.1:8080").await?;

// 使用自定义配置
let config = WebSocketConfig::new()
    .with_max_connections(1000)
    .with_max_message_size(1024 * 1024) // 1MB
    .with_heartbeat_interval(Duration::from_secs(30))
    .with_heartbeat_timeout(Duration::from_secs(60));

let server = WebSocketServer::with_config("127.0.0.1:8080", config).await?;
```

### 创建WebSocket客户端

```rust
use c10_networks::protocol::websocket::{WebSocketClient, WebSocketConfig};

// 使用默认配置
let mut client = WebSocketClient::connect("ws://127.0.0.1:8080").await?;

// 使用自定义配置
let config = WebSocketConfig::new()
    .with_max_message_size(1024 * 1024)
    .with_heartbeat_interval(Duration::from_secs(30))
    .with_heartbeat_timeout(Duration::from_secs(60));

let mut client = WebSocketClient::connect_with_config("ws://127.0.0.1:8080", config).await?;
```

## 🔌 WebSocket 服务器

### 基础服务器实现

```rust
use c10_networks::protocol::websocket::{WebSocketServer, WebSocketConnection, WebSocketMessage};
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    let server = WebSocketServer::new("127.0.0.1:8080").await?;
    println!("WebSocket服务器启动在 ws://127.0.0.1:8080");
    
    loop {
        let (connection, addr) = server.accept().await?;
        println!("新连接来自: {}", addr);
        
        // 为每个连接创建一个任务
        tokio::spawn(handle_connection(connection, addr));
    }
}

async fn handle_connection(
    mut connection: WebSocketConnection,
    addr: std::net::SocketAddr,
) -> NetworkResult<()> {
    println!("处理连接: {}", addr);
    
    while let Some(message) = connection.receive().await? {
        match message {
            WebSocketMessage::Text(text) => {
                println!("收到文本消息: {}", text);
                // 处理文本消息
                let response = process_text_message(&text);
                connection.send_text(response).await?;
            }
            WebSocketMessage::Binary(data) => {
                println!("收到二进制消息: {} 字节", data.len());
                // 处理二进制消息
                let response = process_binary_message(&data);
                connection.send_binary(response).await?;
            }
            WebSocketMessage::Ping(data) => {
                println!("收到Ping: {:?}", data);
                // 自动回复Pong
                connection.send_pong(data).await?;
            }
            WebSocketMessage::Pong(data) => {
                println!("收到Pong: {:?}", data);
            }
            WebSocketMessage::Close(close_frame) => {
                println!("连接关闭: {:?}", close_frame);
                break;
            }
        }
    }
    
    println!("连接 {} 已断开", addr);
    Ok(())
}

fn process_text_message(text: &str) -> String {
    format!("服务器响应: {}", text)
}

fn process_binary_message(data: &[u8]) -> Vec<u8> {
    // 简单的二进制处理：反转数据
    data.iter().rev().cloned().collect()
}
```

### 多客户端管理

```rust
use c10_networks::protocol::websocket::{WebSocketServer, WebSocketConnection, WebSocketMessage};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

type ClientMap = Arc<Mutex<HashMap<String, WebSocketConnection>>>;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    let server = WebSocketServer::new("127.0.0.1:8080").await?;
    let clients: ClientMap = Arc::new(Mutex::new(HashMap::new()));
    
    println!("WebSocket服务器启动在 ws://127.0.0.1:8080");
    
    loop {
        let (connection, addr) = server.accept().await?;
        let clients = clients.clone();
        
        tokio::spawn(async move {
            let client_id = format!("client_{}", addr);
            println!("新客户端连接: {}", client_id);
            
            // 注册客户端
            {
                let mut clients = clients.lock().await;
                clients.insert(client_id.clone(), connection.clone());
            }
            
            // 处理客户端消息
            while let Some(message) = connection.receive().await? {
                match message {
                    WebSocketMessage::Text(text) => {
                        println!("客户端 {} 发送: {}", client_id, text);
                        
                        // 广播消息给所有客户端
                        broadcast_message(&clients, &client_id, &text).await;
                    }
                    WebSocketMessage::Close(_) => {
                        println!("客户端 {} 断开连接", client_id);
                        break;
                    }
                    _ => {}
                }
            }
            
            // 移除客户端
            {
                let mut clients = clients.lock().await;
                clients.remove(&client_id);
            }
            
            Ok::<(), NetworkError>(())
        });
    }
}

async fn broadcast_message(
    clients: &ClientMap,
    sender_id: &str,
    message: &str,
) {
    let clients = clients.lock().await;
    let broadcast_message = format!("{}: {}", sender_id, message);
    
    for (client_id, connection) in clients.iter() {
        if client_id != sender_id {
            if let Err(e) = connection.send_text(broadcast_message.clone()).await {
                eprintln!("发送消息到客户端 {} 失败: {}", client_id, e);
            }
        }
    }
}
```

### 房间管理

```rust
use c10_networks::protocol::websocket::{WebSocketServer, WebSocketConnection, WebSocketMessage};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

type RoomMap = Arc<Mutex<HashMap<String, Vec<WebSocketConnection>>>>;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    let server = WebSocketServer::new("127.0.0.1:8080").await?;
    let rooms: RoomMap = Arc::new(Mutex::new(HashMap::new()));
    
    println!("WebSocket服务器启动在 ws://127.0.0.1:8080");
    
    loop {
        let (connection, addr) = server.accept().await?;
        let rooms = rooms.clone();
        
        tokio::spawn(async move {
            let client_id = format!("client_{}", addr);
            println!("新客户端连接: {}", client_id);
            
            // 处理客户端消息
            while let Some(message) = connection.receive().await? {
                match message {
                    WebSocketMessage::Text(text) => {
                        if let Ok(command) = parse_command(&text) {
                            match command {
                                Command::JoinRoom(room_name) => {
                                    join_room(&rooms, &client_id, room_name, connection.clone()).await;
                                }
                                Command::LeaveRoom(room_name) => {
                                    leave_room(&rooms, &client_id, room_name).await;
                                }
                                Command::SendToRoom(room_name, message) => {
                                    send_to_room(&rooms, &client_id, room_name, message).await;
                                }
                                Command::Broadcast(message) => {
                                    broadcast_to_all(&rooms, &client_id, message).await;
                                }
                            }
                        }
                    }
                    WebSocketMessage::Close(_) => {
                        println!("客户端 {} 断开连接", client_id);
                        break;
                    }
                    _ => {}
                }
            }
            
            Ok::<(), NetworkError>(())
        });
    }
}

#[derive(Debug)]
enum Command {
    JoinRoom(String),
    LeaveRoom(String),
    SendToRoom(String, String),
    Broadcast(String),
}

fn parse_command(text: &str) -> Result<Command, String> {
    let parts: Vec<&str> = text.splitn(2, ' ').collect();
    match parts[0] {
        "JOIN" => {
            if parts.len() > 1 {
                Ok(Command::JoinRoom(parts[1].to_string()))
            } else {
                Err("JOIN命令需要房间名".to_string())
            }
        }
        "LEAVE" => {
            if parts.len() > 1 {
                Ok(Command::LeaveRoom(parts[1].to_string()))
            } else {
                Err("LEAVE命令需要房间名".to_string())
            }
        }
        "SEND" => {
            if parts.len() > 1 {
                let room_parts: Vec<&str> = parts[1].splitn(2, ' ').collect();
                if room_parts.len() > 1 {
                    Ok(Command::SendToRoom(room_parts[0].to_string(), room_parts[1].to_string()))
                } else {
                    Err("SEND命令需要房间名和消息".to_string())
                }
            } else {
                Err("SEND命令需要房间名和消息".to_string())
            }
        }
        "BROADCAST" => {
            if parts.len() > 1 {
                Ok(Command::Broadcast(parts[1].to_string()))
            } else {
                Err("BROADCAST命令需要消息".to_string())
            }
        }
        _ => Err("未知命令".to_string()),
    }
}

async fn join_room(
    rooms: &RoomMap,
    client_id: &str,
    room_name: String,
    connection: WebSocketConnection,
) {
    let mut rooms = rooms.lock().await;
    rooms.entry(room_name.clone()).or_insert_with(Vec::new).push(connection);
    println!("客户端 {} 加入房间 {}", client_id, room_name);
}

async fn leave_room(rooms: &RoomMap, client_id: &str, room_name: String) {
    let mut rooms = rooms.lock().await;
    if let Some(room_clients) = rooms.get_mut(&room_name) {
        room_clients.retain(|conn| {
            // 这里需要根据连接标识来移除特定客户端
            // 简化实现，实际应用中需要更复杂的逻辑
            true
        });
    }
    println!("客户端 {} 离开房间 {}", client_id, room_name);
}

async fn send_to_room(
    rooms: &RoomMap,
    sender_id: &str,
    room_name: String,
    message: String,
) {
    let rooms = rooms.lock().await;
    if let Some(room_clients) = rooms.get(&room_name) {
        let broadcast_message = format!("{}: {}", sender_id, message);
        for connection in room_clients {
            if let Err(e) = connection.send_text(broadcast_message.clone()).await {
                eprintln!("发送消息失败: {}", e);
            }
        }
    }
}

async fn broadcast_to_all(rooms: &RoomMap, sender_id: &str, message: String) {
    let rooms = rooms.lock().await;
    let broadcast_message = format!("{}: {}", sender_id, message);
    
    for room_clients in rooms.values() {
        for connection in room_clients {
            if let Err(e) = connection.send_text(broadcast_message.clone()).await {
                eprintln!("广播消息失败: {}", e);
            }
        }
    }
}
```

## 📱 WebSocket 客户端

### 基础客户端实现

```rust
use c10_networks::protocol::websocket::{WebSocketClient, WebSocketMessage};
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    println!("连接WebSocket服务器...");
    
    let mut client = WebSocketClient::connect("ws://127.0.0.1:8080").await?;
    println!("连接成功!");
    
    // 发送文本消息
    client.send_text("Hello, WebSocket!").await?;
    
    // 发送二进制消息
    let binary_data = b"Binary message from client";
    client.send_binary(binary_data.to_vec()).await?;
    
    // 接收响应
    for _ in 0..2 {
        if let Some(message) = client.receive().await? {
            match message {
                WebSocketMessage::Text(text) => {
                    println!("收到文本响应: {}", text);
                }
                WebSocketMessage::Binary(data) => {
                    println!("收到二进制响应: {} 字节", data.len());
                }
                _ => {}
            }
        }
    }
    
    // 关闭连接
    client.close().await?;
    println!("连接已关闭");
    
    Ok(())
}
```

### 自动重连客户端

```rust
use c10_networks::protocol::websocket::{WebSocketClient, WebSocketMessage};
use c10_networks::error::NetworkResult;
use std::time::Duration;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    let url = "ws://127.0.0.1:8080";
    let max_retries = 5;
    let retry_delay = Duration::from_secs(5);
    
    for attempt in 1..=max_retries {
        match WebSocketClient::connect(url).await {
            Ok(mut client) => {
                println!("连接成功 (尝试 {})", attempt);
                
                // 处理连接
                if let Err(e) = handle_connection(&mut client).await {
                    eprintln!("连接处理错误: {}", e);
                }
                
                break;
            }
            Err(e) => {
                eprintln!("连接失败 (尝试 {}): {}", attempt, e);
                
                if attempt < max_retries {
                    println!("{}秒后重试...", retry_delay.as_secs());
                    tokio::time::sleep(retry_delay).await;
                } else {
                    eprintln!("达到最大重试次数，连接失败");
                    return Err(e);
                }
            }
        }
    }
    
    Ok(())
}

async fn handle_connection(client: &mut WebSocketClient) -> NetworkResult<()> {
    // 发送心跳消息
    let heartbeat_task = tokio::spawn({
        let mut client = client.clone();
        async move {
            loop {
                tokio::time::sleep(Duration::from_secs(30)).await;
                if let Err(e) = client.send_text("ping".to_string()).await {
                    eprintln!("发送心跳失败: {}", e);
                    break;
                }
            }
        }
    });
    
    // 接收消息
    let receive_task = tokio::spawn({
        let mut client = client.clone();
        async move {
            while let Some(message) = client.receive().await? {
                match message {
                    WebSocketMessage::Text(text) => {
                        if text == "pong" {
                            println!("收到心跳响应");
                        } else {
                            println!("收到消息: {}", text);
                        }
                    }
                    WebSocketMessage::Binary(data) => {
                        println!("收到二进制消息: {} 字节", data.len());
                    }
                    WebSocketMessage::Close(_) => {
                        println!("服务器关闭连接");
                        break;
                    }
                    _ => {}
                }
            }
            Ok::<(), NetworkError>(())
        }
    });
    
    // 等待任务完成
    tokio::select! {
        _ = heartbeat_task => {
            println!("心跳任务结束");
        }
        result = receive_task => {
            result??;
        }
    }
    
    Ok(())
}
```

### 订阅-发布客户端

```rust
use c10_networks::protocol::websocket::{WebSocketClient, WebSocketMessage};
use c10_networks::error::NetworkResult;
use serde_json::json;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    let mut client = WebSocketClient::connect("ws://127.0.0.1:8080").await?;
    
    // 订阅主题
    let subscribe_message = json!({
        "type": "subscribe",
        "topic": "news"
    });
    client.send_text(subscribe_message.to_string()).await?;
    
    // 发布消息
    let publish_message = json!({
        "type": "publish",
        "topic": "news",
        "message": "Hello, subscribers!"
    });
    client.send_text(publish_message.to_string()).await?;
    
    // 接收消息
    while let Some(message) = client.receive().await? {
        match message {
            WebSocketMessage::Text(text) => {
                if let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) {
                    if let Some(msg_type) = json.get("type") {
                        match msg_type.as_str() {
                            Some("message") => {
                                if let Some(topic) = json.get("topic") {
                                    if let Some(content) = json.get("message") {
                                        println!("收到主题 {} 的消息: {}", topic, content);
                                    }
                                }
                            }
                            Some("error") => {
                                if let Some(error) = json.get("error") {
                                    eprintln!("服务器错误: {}", error);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            WebSocketMessage::Close(_) => {
                println!("连接关闭");
                break;
            }
            _ => {}
        }
    }
    
    Ok(())
}
```

## 📨 消息处理

### 消息类型

```rust
use c10_networks::protocol::websocket::WebSocketMessage;

fn handle_message(message: WebSocketMessage) {
    match message {
        WebSocketMessage::Text(text) => {
            println!("文本消息: {}", text);
            // 处理文本消息
        }
        WebSocketMessage::Binary(data) => {
            println!("二进制消息: {} 字节", data.len());
            // 处理二进制消息
        }
        WebSocketMessage::Ping(data) => {
            println!("Ping: {:?}", data);
            // 通常自动回复Pong
        }
        WebSocketMessage::Pong(data) => {
            println!("Pong: {:?}", data);
            // 处理Pong响应
        }
        WebSocketMessage::Close(close_frame) => {
            println!("关闭帧: {:?}", close_frame);
            // 处理连接关闭
        }
    }
}
```

### 消息序列化

```rust
use c10_networks::protocol::websocket::{WebSocketClient, WebSocketMessage};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct ChatMessage {
    user: String,
    message: String,
    timestamp: u64,
}

#[derive(Serialize, Deserialize)]
enum MessageType {
    Chat(ChatMessage),
    Join(String),
    Leave(String),
    Error(String),
}

async fn send_chat_message(
    client: &mut WebSocketClient,
    user: &str,
    message: &str,
) -> NetworkResult<()> {
    let chat_message = ChatMessage {
        user: user.to_string(),
        message: message.to_string(),
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs(),
    };
    
    let message_type = MessageType::Chat(chat_message);
    let json = serde_json::to_string(&message_type)?;
    
    client.send_text(json).await?;
    Ok(())
}

async fn handle_received_message(message: WebSocketMessage) -> NetworkResult<()> {
    if let WebSocketMessage::Text(text) = message {
        if let Ok(message_type) = serde_json::from_str::<MessageType>(&text) {
            match message_type {
                MessageType::Chat(chat) => {
                    println!("[{}] {}: {}", 
                        chrono::DateTime::from_timestamp(chat.timestamp as i64, 0)
                            .unwrap()
                            .format("%H:%M:%S"),
                        chat.user,
                        chat.message
                    );
                }
                MessageType::Join(user) => {
                    println!("用户 {} 加入聊天", user);
                }
                MessageType::Leave(user) => {
                    println!("用户 {} 离开聊天", user);
                }
                MessageType::Error(error) => {
                    eprintln!("错误: {}", error);
                }
            }
        }
    }
    Ok(())
}
```

### 消息路由

```rust
use c10_networks::protocol::websocket::{WebSocketConnection, WebSocketMessage};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

type MessageHandler = Box<dyn Fn(WebSocketMessage) -> NetworkResult<()> + Send + Sync>;
type HandlerMap = Arc<Mutex<HashMap<String, MessageHandler>>>;

struct MessageRouter {
    handlers: HandlerMap,
}

impl MessageRouter {
    fn new() -> Self {
        Self {
            handlers: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    async fn register_handler(&self, message_type: &str, handler: MessageHandler) {
        let mut handlers = self.handlers.lock().await;
        handlers.insert(message_type.to_string(), handler);
    }
    
    async fn route_message(&self, message: WebSocketMessage) -> NetworkResult<()> {
        if let WebSocketMessage::Text(text) = message {
            if let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) {
                if let Some(message_type) = json.get("type").and_then(|v| v.as_str()) {
                    let handlers = self.handlers.lock().await;
                    if let Some(handler) = handlers.get(message_type) {
                        let message = WebSocketMessage::Text(text);
                        handler(message)?;
                    }
                }
            }
        }
        Ok(())
    }
}

// 使用示例
async fn setup_router() -> MessageRouter {
    let router = MessageRouter::new();
    
    // 注册聊天消息处理器
    router.register_handler("chat", Box::new(|message| {
        if let WebSocketMessage::Text(text) = message {
            println!("处理聊天消息: {}", text);
        }
        Ok(())
    })).await;
    
    // 注册系统消息处理器
    router.register_handler("system", Box::new(|message| {
        if let WebSocketMessage::Text(text) = message {
            println!("处理系统消息: {}", text);
        }
        Ok(())
    })).await;
    
    router
}
```

## 🔒 安全 WebSocket

### WSS (WebSocket Secure) 服务器

```rust
use c10_networks::protocol::websocket::{WebSocketServer, WebSocketConfig};
use c10_networks::security::tls_reload::TlsConfig;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 配置TLS
    let tls_config = TlsConfig::default()
        .with_certificate("server.crt", "server.key")
        .with_verify_certificates(false); // 自签名证书
    
    let ws_config = WebSocketConfig::new()
        .with_tls_config(tls_config)
        .with_max_connections(1000);
    
    // 启动WSS服务器
    let server = WebSocketServer::with_config("0.0.0.0:8443", ws_config).await?;
    println!("WSS服务器启动在 wss://0.0.0.0:8443");
    
    loop {
        let (connection, addr) = server.accept().await?;
        println!("安全连接来自: {}", addr);
        
        tokio::spawn(handle_secure_connection(connection, addr));
    }
}

async fn handle_secure_connection(
    mut connection: WebSocketConnection,
    addr: std::net::SocketAddr,
) -> NetworkResult<()> {
    println!("处理安全连接: {}", addr);
    
    while let Some(message) = connection.receive().await? {
        match message {
            WebSocketMessage::Text(text) => {
                println!("收到安全消息: {}", text);
                connection.send_text(format!("Secure echo: {}", text)).await?;
            }
            WebSocketMessage::Close(_) => {
                println!("安全连接关闭: {}", addr);
                break;
            }
            _ => {}
        }
    }
    
    Ok(())
}
```

### WSS 客户端

```rust
use c10_networks::protocol::websocket::{WebSocketClient, WebSocketConfig};
use c10_networks::security::tls_reload::TlsConfig;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 配置TLS
    let tls_config = TlsConfig::default()
        .with_verify_certificates(false) // 自签名证书
        .with_verify_hostname(false);
    
    let ws_config = WebSocketConfig::new()
        .with_tls_config(tls_config);
    
    // 连接WSS服务器
    let mut client = WebSocketClient::connect_with_config(
        "wss://127.0.0.1:8443",
        ws_config
    ).await?;
    
    println!("WSS连接成功!");
    
    // 发送安全消息
    client.send_text("Hello, secure WebSocket!".to_string()).await?;
    
    // 接收响应
    if let Some(message) = client.receive().await? {
        if let WebSocketMessage::Text(text) = message {
            println!("收到安全响应: {}", text);
        }
    }
    
    client.close().await?;
    Ok(())
}
```

### 身份验证

```rust
use c10_networks::protocol::websocket::{WebSocketServer, WebSocketConnection, WebSocketMessage};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

type AuthToken = String;
type UserId = String;
type AuthenticatedClients = Arc<Mutex<HashMap<AuthToken, UserId>>>;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    let server = WebSocketServer::new("127.0.0.1:8080").await?;
    let authenticated_clients: AuthenticatedClients = Arc::new(Mutex::new(HashMap::new()));
    
    println!("WebSocket服务器启动在 ws://127.0.0.1:8080");
    
    loop {
        let (connection, addr) = server.accept().await?;
        let authenticated_clients = authenticated_clients.clone();
        
        tokio::spawn(async move {
            if let Ok(user_id) = authenticate_connection(&mut connection).await {
                println!("用户 {} 认证成功", user_id);
                
                // 存储认证信息
                let token = generate_token();
                {
                    let mut clients = authenticated_clients.lock().await;
                    clients.insert(token.clone(), user_id.clone());
                }
                
                // 处理认证后的连接
                handle_authenticated_connection(connection, user_id, token, authenticated_clients).await;
            } else {
                println!("认证失败，关闭连接: {}", addr);
                connection.close().await?;
            }
            
            Ok::<(), NetworkError>(())
        });
    }
}

async fn authenticate_connection(
    connection: &mut WebSocketConnection,
) -> NetworkResult<UserId> {
    // 等待认证消息
    if let Some(message) = connection.receive().await? {
        if let WebSocketMessage::Text(text) = message {
            if let Ok(auth_data) = serde_json::from_str::<serde_json::Value>(&text) {
                if let (Some(username), Some(password)) = (
                    auth_data.get("username").and_then(|v| v.as_str()),
                    auth_data.get("password").and_then(|v| v.as_str()),
                ) {
                    // 简单的认证逻辑（实际应用中应该使用更安全的方法）
                    if username == "admin" && password == "password" {
                        connection.send_text(r#"{"status": "authenticated"}"#.to_string()).await?;
                        return Ok(username.to_string());
                    }
                }
            }
        }
    }
    
    connection.send_text(r#"{"status": "authentication_failed"}"#.to_string()).await?;
    Err(NetworkError::AuthenticationFailed)
}

async fn handle_authenticated_connection(
    mut connection: WebSocketConnection,
    user_id: UserId,
    token: AuthToken,
    authenticated_clients: AuthenticatedClients,
) -> NetworkResult<()> {
    println!("处理认证用户 {} 的连接", user_id);
    
    while let Some(message) = connection.receive().await? {
        match message {
            WebSocketMessage::Text(text) => {
                println!("用户 {} 发送: {}", user_id, text);
                
                // 处理用户消息
                let response = format!("用户 {} 的消息: {}", user_id, text);
                connection.send_text(response).await?;
            }
            WebSocketMessage::Close(_) => {
                println!("用户 {} 断开连接", user_id);
                
                // 移除认证信息
                {
                    let mut clients = authenticated_clients.lock().await;
                    clients.remove(&token);
                }
                
                break;
            }
            _ => {}
        }
    }
    
    Ok(())
}

fn generate_token() -> AuthToken {
    use std::time::{SystemTime, UNIX_EPOCH};
    let timestamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
    format!("token_{}", timestamp)
}
```

## 📊 高级特性

### 心跳机制

```rust
use c10_networks::protocol::websocket::{WebSocketConnection, WebSocketMessage};
use std::time::Duration;

async fn setup_heartbeat(connection: &mut WebSocketConnection) -> NetworkResult<()> {
    let heartbeat_interval = Duration::from_secs(30);
    let heartbeat_timeout = Duration::from_secs(60);
    
    let mut last_pong = std::time::Instant::now();
    
    loop {
        tokio::select! {
            // 发送心跳
            _ = tokio::time::sleep(heartbeat_interval) => {
                if let Err(e) = connection.send_ping(vec![]).await {
                    eprintln!("发送心跳失败: {}", e);
                    break;
                }
            }
            
            // 接收消息
            message = connection.receive() => {
                if let Some(message) = message? {
                    match message {
                        WebSocketMessage::Pong(_) => {
                            last_pong = std::time::Instant::now();
                        }
                        WebSocketMessage::Close(_) => {
                            println!("连接关闭");
                            break;
                        }
                        _ => {}
                    }
                } else {
                    println!("连接断开");
                    break;
                }
            }
            
            // 检查心跳超时
            _ = tokio::time::sleep(heartbeat_timeout) => {
                if last_pong.elapsed() > heartbeat_timeout {
                    eprintln!("心跳超时，关闭连接");
                    connection.close().await?;
                    break;
                }
            }
        }
    }
    
    Ok(())
}
```

### 消息压缩

```rust
use c10_networks::protocol::websocket::{WebSocketClient, WebSocketConfig};
use flate2::write::GzEncoder;
use flate2::read::GzDecoder;
use flate2::Compression;
use std::io::{Read, Write};

async fn send_compressed_message(
    client: &mut WebSocketClient,
    message: &str,
) -> NetworkResult<()> {
    // 压缩消息
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(message.as_bytes())?;
    let compressed_data = encoder.finish()?;
    
    // 发送压缩后的二进制数据
    client.send_binary(compressed_data).await?;
    Ok(())
}

async fn receive_compressed_message(
    client: &mut WebSocketClient,
) -> NetworkResult<String> {
    if let Some(message) = client.receive().await? {
        if let WebSocketMessage::Binary(data) = message {
            // 解压缩消息
            let mut decoder = GzDecoder::new(&data[..]);
            let mut decompressed = String::new();
            decoder.read_to_string(&mut decompressed)?;
            return Ok(decompressed);
        }
    }
    
    Err(NetworkError::InvalidMessage)
}
```

### 消息队列

```rust
use c10_networks::protocol::websocket::{WebSocketConnection, WebSocketMessage};
use std::collections::VecDeque;
use std::sync::Arc;
use tokio::sync::Mutex;

type MessageQueue = Arc<Mutex<VecDeque<WebSocketMessage>>>;

struct WebSocketMessageQueue {
    queue: MessageQueue,
    max_size: usize,
}

impl WebSocketMessageQueue {
    fn new(max_size: usize) -> Self {
        Self {
            queue: Arc::new(Mutex::new(VecDeque::new())),
            max_size,
        }
    }
    
    async fn push(&self, message: WebSocketMessage) -> NetworkResult<()> {
        let mut queue = self.queue.lock().await;
        
        if queue.len() >= self.max_size {
            // 队列已满，移除最旧的消息
            queue.pop_front();
        }
        
        queue.push_back(message);
        Ok(())
    }
    
    async fn pop(&self) -> Option<WebSocketMessage> {
        let mut queue = self.queue.lock().await;
        queue.pop_front()
    }
    
    async fn len(&self) -> usize {
        let queue = self.queue.lock().await;
        queue.len()
    }
    
    async fn is_empty(&self) -> bool {
        let queue = self.queue.lock().await;
        queue.is_empty()
    }
}

// 使用示例
async fn handle_connection_with_queue(
    mut connection: WebSocketConnection,
) -> NetworkResult<()> {
    let message_queue = WebSocketMessageQueue::new(1000);
    
    // 接收消息并加入队列
    let queue_clone = message_queue.clone();
    let receive_task = tokio::spawn(async move {
        while let Some(message) = connection.receive().await? {
            queue_clone.push(message).await?;
        }
        Ok::<(), NetworkError>(())
    });
    
    // 处理队列中的消息
    let process_task = tokio::spawn(async move {
        while let Some(message) = message_queue.pop().await {
            match message {
                WebSocketMessage::Text(text) => {
                    println!("处理文本消息: {}", text);
                }
                WebSocketMessage::Binary(data) => {
                    println!("处理二进制消息: {} 字节", data.len());
                }
                _ => {}
            }
        }
        Ok::<(), NetworkError>(())
    });
    
    // 等待任务完成
    tokio::select! {
        result = receive_task => result??,
        result = process_task => result??,
    }
    
    Ok(())
}
```

## ⚙️ 配置选项

### WebSocketConfig 完整配置

```rust
use c10_networks::protocol::websocket::{WebSocketConfig, WebSocketServer, WebSocketClient};
use c10_networks::security::tls_reload::TlsConfig;
use std::time::Duration;

// 服务器配置
let server_config = WebSocketConfig::new()
    .with_max_connections(1000)
    .with_max_message_size(1024 * 1024) // 1MB
    .with_heartbeat_interval(Duration::from_secs(30))
    .with_heartbeat_timeout(Duration::from_secs(60))
    .with_connection_timeout(Duration::from_secs(30))
    .with_read_timeout(Duration::from_secs(20))
    .with_write_timeout(Duration::from_secs(20))
    .with_keep_alive(true)
    .with_tcp_nodelay(true)
    .with_tcp_keepalive(Duration::from_secs(60))
    .with_tls_config(TlsConfig::default())
    .with_compression_enabled(true)
    .with_subprotocols(vec!["chat".to_string(), "binary".to_string()]);

let server = WebSocketServer::with_config("127.0.0.1:8080", server_config).await?;

// 客户端配置
let client_config = WebSocketConfig::new()
    .with_max_message_size(1024 * 1024)
    .with_heartbeat_interval(Duration::from_secs(30))
    .with_heartbeat_timeout(Duration::from_secs(60))
    .with_connection_timeout(Duration::from_secs(30))
    .with_read_timeout(Duration::from_secs(20))
    .with_write_timeout(Duration::from_secs(20))
    .with_keep_alive(true)
    .with_tcp_nodelay(true)
    .with_tls_config(TlsConfig::default())
    .with_compression_enabled(true)
    .with_subprotocols(vec!["chat".to_string()]);

let client = WebSocketClient::connect_with_config("ws://127.0.0.1:8080", client_config).await?;
```

### 环境变量配置

```bash
# WebSocket配置
export C10_WS_MAX_CONNECTIONS=1000
export C10_WS_MAX_MESSAGE_SIZE=1048576
export C10_WS_HEARTBEAT_INTERVAL=30
export C10_WS_HEARTBEAT_TIMEOUT=60
export C10_WS_CONNECTION_TIMEOUT=30
export C10_WS_READ_TIMEOUT=20
export C10_WS_WRITE_TIMEOUT=20
export C10_WS_KEEP_ALIVE=true
export C10_WS_TCP_NODELAY=true
export C10_WS_COMPRESSION_ENABLED=true
```

## 🔍 错误处理

### 错误类型

```rust
use c10_networks::error::{NetworkError, NetworkResult};

async fn handle_websocket_errors() -> NetworkResult<()> {
    let mut client = WebSocketClient::connect("ws://127.0.0.1:8080").await?;
    
    loop {
        match client.receive().await {
            Ok(Some(message)) => {
                // 处理消息
                handle_message(message).await?;
            }
            Ok(None) => {
                println!("连接正常关闭");
                break;
            }
            Err(NetworkError::ConnectionClosed) => {
                println!("连接被关闭");
                break;
            }
            Err(NetworkError::Timeout) => {
                println!("接收超时");
                // 可以尝试重连
                break;
            }
            Err(NetworkError::ProtocolError(e)) => {
                eprintln!("协议错误: {}", e);
                break;
            }
            Err(NetworkError::TlsError(e)) => {
                eprintln!("TLS错误: {}", e);
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

async fn handle_message(message: WebSocketMessage) -> NetworkResult<()> {
    match message {
        WebSocketMessage::Text(text) => {
            println!("收到文本消息: {}", text);
        }
        WebSocketMessage::Binary(data) => {
            println!("收到二进制消息: {} 字节", data.len());
        }
        WebSocketMessage::Close(close_frame) => {
            if let Some(code) = close_frame.code {
                println!("连接关闭，代码: {}, 原因: {:?}", code, close_frame.reason);
            }
        }
        _ => {}
    }
    Ok(())
}
```

### 重连机制

```rust
use c10_networks::protocol::websocket::WebSocketClient;
use std::time::Duration;

struct ReconnectingWebSocketClient {
    url: String,
    max_retries: usize,
    retry_delay: Duration,
    backoff_multiplier: f64,
}

impl ReconnectingWebSocketClient {
    fn new(url: String) -> Self {
        Self {
            url,
            max_retries: 5,
            retry_delay: Duration::from_secs(1),
            backoff_multiplier: 2.0,
        }
    }
    
    async fn connect_with_retry(&self) -> NetworkResult<WebSocketClient> {
        let mut delay = self.retry_delay;
        
        for attempt in 1..=self.max_retries {
            match WebSocketClient::connect(&self.url).await {
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
    let reconnecting_client = ReconnectingWebSocketClient::new(
        "ws://127.0.0.1:8080".to_string()
    );
    
    let mut client = reconnecting_client.connect_with_retry().await?;
    
    // 使用客户端...
    
    Ok(())
}
```

## 📈 性能优化

### 连接池

```rust
use c10_networks::protocol::websocket::{WebSocketClient, WebSocketConfig};
use std::collections::VecDeque;
use std::sync::Arc;
use tokio::sync::Mutex;

struct WebSocketConnectionPool {
    connections: Arc<Mutex<VecDeque<WebSocketClient>>>,
    max_size: usize,
    url: String,
    config: WebSocketConfig,
}

impl WebSocketConnectionPool {
    fn new(url: String, max_size: usize, config: WebSocketConfig) -> Self {
        Self {
            connections: Arc::new(Mutex::new(VecDeque::new())),
            max_size,
            url,
            config,
        }
    }
    
    async fn get_connection(&self) -> NetworkResult<WebSocketClient> {
        // 尝试从池中获取连接
        {
            let mut connections = self.connections.lock().await;
            if let Some(connection) = connections.pop_front() {
                return Ok(connection);
            }
        }
        
        // 池中没有可用连接，创建新连接
        WebSocketClient::connect_with_config(&self.url, self.config.clone()).await
    }
    
    async fn return_connection(&self, connection: WebSocketClient) {
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
async fn use_connection_pool() -> NetworkResult<()> {
    let config = WebSocketConfig::new()
        .with_max_message_size(1024 * 1024)
        .with_heartbeat_interval(Duration::from_secs(30));
    
    let pool = WebSocketConnectionPool::new(
        "ws://127.0.0.1:8080".to_string(),
        10,
        config
    );
    
    // 获取连接
    let mut connection = pool.get_connection().await?;
    
    // 使用连接
    connection.send_text("Hello".to_string()).await?;
    
    // 归还连接
    pool.return_connection(connection).await;
    
    Ok(())
}
```

### 消息批处理

```rust
use c10_networks::protocol::websocket::{WebSocketClient, WebSocketMessage};
use std::collections::VecDeque;
use std::time::Duration;

struct MessageBatcher {
    batch_size: usize,
    batch_timeout: Duration,
    messages: VecDeque<WebSocketMessage>,
    last_flush: std::time::Instant,
}

impl MessageBatcher {
    fn new(batch_size: usize, batch_timeout: Duration) -> Self {
        Self {
            batch_size,
            batch_timeout,
            messages: VecDeque::new(),
            last_flush: std::time::Instant::now(),
        }
    }
    
    fn add_message(&mut self, message: WebSocketMessage) -> bool {
        self.messages.push_back(message);
        
        // 检查是否需要刷新
        self.messages.len() >= self.batch_size || 
        self.last_flush.elapsed() >= self.batch_timeout
    }
    
    fn flush(&mut self) -> Vec<WebSocketMessage> {
        let messages: Vec<_> = self.messages.drain(..).collect();
        self.last_flush = std::time::Instant::now();
        messages
    }
    
    fn is_empty(&self) -> bool {
        self.messages.is_empty()
    }
}

async fn batch_send_messages(
    client: &mut WebSocketClient,
    messages: Vec<WebSocketMessage>,
) -> NetworkResult<()> {
    for message in messages {
        match message {
            WebSocketMessage::Text(text) => {
                client.send_text(text).await?;
            }
            WebSocketMessage::Binary(data) => {
                client.send_binary(data).await?;
            }
            _ => {}
        }
    }
    Ok(())
}

// 使用示例
async fn use_message_batcher() -> NetworkResult<()> {
    let mut client = WebSocketClient::connect("ws://127.0.0.1:8080").await?;
    let mut batcher = MessageBatcher::new(10, Duration::from_millis(100));
    
    // 添加消息到批处理器
    for i in 0..25 {
        let message = WebSocketMessage::Text(format!("Message {}", i));
        
        if batcher.add_message(message) {
            // 批处理已满或超时，发送消息
            let messages = batcher.flush();
            batch_send_messages(&mut client, messages).await?;
        }
    }
    
    // 发送剩余消息
    if !batcher.is_empty() {
        let messages = batcher.flush();
        batch_send_messages(&mut client, messages).await?;
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
    use c10_networks::protocol::websocket::{WebSocketServer, WebSocketClient, WebSocketMessage};
    use tokio_test;

    #[tokio::test]
    async fn test_websocket_server_creation() {
        let server = WebSocketServer::new("127.0.0.1:0").await.unwrap();
        assert!(server.is_bound());
    }

    #[tokio::test]
    async fn test_websocket_client_connection() {
        // 启动测试服务器
        let server = WebSocketServer::new("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        // 连接客户端
        let client = WebSocketClient::connect(&format!("ws://{}", server_addr)).await.unwrap();
        assert!(client.is_connected());
    }

    #[tokio::test]
    async fn test_websocket_message_exchange() {
        // 启动测试服务器
        let server = WebSocketServer::new("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        // 启动服务器任务
        let server_task = tokio::spawn(async move {
            let (mut connection, _) = server.accept().await.unwrap();
            
            // 接收消息
            if let Some(message) = connection.receive().await.unwrap() {
                if let WebSocketMessage::Text(text) = message {
                    // 回显消息
                    connection.send_text(format!("Echo: {}", text)).await.unwrap();
                }
            }
        });
        
        // 连接客户端
        let mut client = WebSocketClient::connect(&format!("ws://{}", server_addr)).await.unwrap();
        
        // 发送消息
        client.send_text("Hello, WebSocket!".to_string()).await.unwrap();
        
        // 接收响应
        if let Some(message) = client.receive().await.unwrap() {
            if let WebSocketMessage::Text(text) = message {
                assert_eq!(text, "Echo: Hello, WebSocket!");
            }
        }
        
        // 等待服务器任务完成
        server_task.await.unwrap();
    }

    #[tokio::test]
    async fn test_websocket_binary_message() {
        // 启动测试服务器
        let server = WebSocketServer::new("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        // 启动服务器任务
        let server_task = tokio::spawn(async move {
            let (mut connection, _) = server.accept().await.unwrap();
            
            // 接收二进制消息
            if let Some(message) = connection.receive().await.unwrap() {
                if let WebSocketMessage::Binary(data) = message {
                    // 回显二进制数据
                    connection.send_binary(data).await.unwrap();
                }
            }
        });
        
        // 连接客户端
        let mut client = WebSocketClient::connect(&format!("ws://{}", server_addr)).await.unwrap();
        
        // 发送二进制消息
        let test_data = b"Binary test data";
        client.send_binary(test_data.to_vec()).await.unwrap();
        
        // 接收响应
        if let Some(message) = client.receive().await.unwrap() {
            if let WebSocketMessage::Binary(data) = message {
                assert_eq!(data, test_data);
            }
        }
        
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
    use c10_networks::protocol::websocket::{WebSocketServer, WebSocketClient, WebSocketMessage};

    #[tokio::test]
    async fn test_websocket_chat_room() {
        // 启动聊天室服务器
        let server = WebSocketServer::new("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        let server_task = tokio::spawn(async move {
            let (mut connection, _) = server.accept().await.unwrap();
            
            // 模拟聊天室逻辑
            while let Some(message) = connection.receive().await.unwrap() {
                match message {
                    WebSocketMessage::Text(text) => {
                        if text.starts_with("JOIN ") {
                            let room = &text[5..];
                            connection.send_text(format!("Joined room: {}", room)).await.unwrap();
                        } else if text.starts_with("SEND ") {
                            let message = &text[5..];
                            connection.send_text(format!("Message: {}", message)).await.unwrap();
                        }
                    }
                    WebSocketMessage::Close(_) => {
                        break;
                    }
                    _ => {}
                }
            }
        });
        
        // 连接客户端
        let mut client = WebSocketClient::connect(&format!("ws://{}", server_addr)).await.unwrap();
        
        // 加入房间
        client.send_text("JOIN general".to_string()).await.unwrap();
        if let Some(message) = client.receive().await.unwrap() {
            if let WebSocketMessage::Text(text) = message {
                assert_eq!(text, "Joined room: general");
            }
        }
        
        // 发送消息
        client.send_text("SEND Hello, everyone!".to_string()).await.unwrap();
        if let Some(message) = client.receive().await.unwrap() {
            if let WebSocketMessage::Text(text) = message {
                assert_eq!(text, "Message: Hello, everyone!");
            }
        }
        
        // 关闭连接
        client.close().await.unwrap();
        
        // 等待服务器任务完成
        server_task.await.unwrap();
    }

    #[tokio::test]
    async fn test_websocket_heartbeat() {
        // 启动服务器
        let server = WebSocketServer::new("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        let server_task = tokio::spawn(async move {
            let (mut connection, _) = server.accept().await.unwrap();
            
            // 处理心跳
            while let Some(message) = connection.receive().await.unwrap() {
                match message {
                    WebSocketMessage::Ping(data) => {
                        connection.send_pong(data).await.unwrap();
                    }
                    WebSocketMessage::Close(_) => {
                        break;
                    }
                    _ => {}
                }
            }
        });
        
        // 连接客户端
        let mut client = WebSocketClient::connect(&format!("ws://{}", server_addr)).await.unwrap();
        
        // 发送心跳
        client.send_ping(vec![1, 2, 3, 4]).await.unwrap();
        
        // 接收心跳响应
        if let Some(message) = client.receive().await.unwrap() {
            if let WebSocketMessage::Pong(data) = message {
                assert_eq!(data, vec![1, 2, 3, 4]);
            }
        }
        
        // 关闭连接
        client.close().await.unwrap();
        
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
    use c10_networks::protocol::websocket::{WebSocketServer, WebSocketClient, WebSocketMessage};
    use std::time::Instant;

    #[tokio::test]
    async fn test_websocket_throughput() {
        // 启动服务器
        let server = WebSocketServer::new("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        let server_task = tokio::spawn(async move {
            let (mut connection, _) = server.accept().await.unwrap();
            
            // 回显所有消息
            while let Some(message) = connection.receive().await.unwrap() {
                match message {
                    WebSocketMessage::Text(text) => {
                        connection.send_text(text).await.unwrap();
                    }
                    WebSocketMessage::Binary(data) => {
                        connection.send_binary(data).await.unwrap();
                    }
                    WebSocketMessage::Close(_) => {
                        break;
                    }
                    _ => {}
                }
            }
        });
        
        // 连接客户端
        let mut client = WebSocketClient::connect(&format!("ws://{}", server_addr)).await.unwrap();
        
        // 性能测试
        let message_count = 1000;
        let start = Instant::now();
        
        for i in 0..message_count {
            let message = format!("Message {}", i);
            client.send_text(message).await.unwrap();
            
            if let Some(response) = client.receive().await.unwrap() {
                if let WebSocketMessage::Text(text) = response {
                    assert_eq!(text, format!("Message {}", i));
                }
            }
        }
        
        let duration = start.elapsed();
        let throughput = message_count as f64 / duration.as_secs_f64();
        
        println!("发送 {} 条消息耗时: {:?}", message_count, duration);
        println!("吞吐量: {:.2} 消息/秒", throughput);
        
        // 断言性能要求
        assert!(throughput > 100.0); // 至少100消息/秒
        
        // 关闭连接
        client.close().await.unwrap();
        
        // 等待服务器任务完成
        server_task.await.unwrap();
    }

    #[tokio::test]
    async fn test_websocket_concurrent_connections() {
        // 启动服务器
        let server = WebSocketServer::new("127.0.0.1:0").await.unwrap();
        let server_addr = server.local_addr().unwrap();
        
        let server_task = tokio::spawn(async move {
            let mut connection_count = 0;
            
            loop {
                let (mut connection, _) = server.accept().await.unwrap();
                connection_count += 1;
                
                tokio::spawn(async move {
                    // 处理连接
                    while let Some(message) = connection.receive().await.unwrap() {
                        match message {
                            WebSocketMessage::Text(text) => {
                                connection.send_text(format!("Echo: {}", text)).await.unwrap();
                            }
                            WebSocketMessage::Close(_) => {
                                break;
                            }
                            _ => {}
                        }
                    }
                });
                
                if connection_count >= 10 {
                    break;
                }
            }
        });
        
        // 创建多个并发连接
        let connection_count = 10;
        let mut clients = Vec::new();
        
        for i in 0..connection_count {
            let client = WebSocketClient::connect(&format!("ws://{}", server_addr)).await.unwrap();
            clients.push(client);
        }
        
        // 测试并发消息发送
        let start = Instant::now();
        
        let futures: Vec<_> = clients.into_iter().enumerate().map(|(i, mut client)| {
            tokio::spawn(async move {
                let message = format!("Message from client {}", i);
                client.send_text(message.clone()).await.unwrap();
                
                if let Some(response) = client.receive().await.unwrap() {
                    if let WebSocketMessage::Text(text) = response {
                        assert_eq!(text, format!("Echo: {}", message));
                    }
                }
                
                client.close().await.unwrap();
            })
        }).collect();
        
        // 等待所有任务完成
        for future in futures {
            future.await.unwrap();
        }
        
        let duration = start.elapsed();
        println!("{} 个并发连接测试耗时: {:?}", connection_count, duration);
        
        // 等待服务器任务完成
        server_task.await.unwrap();
    }
}
```

## ❓ 常见问题

### Q: 如何设置WebSocket超时？

A: 使用 `WebSocketConfig::with_connection_timeout()` 方法设置连接超时。

### Q: 如何处理连接断开？

A: 监听 `WebSocketMessage::Close` 消息，并实现重连机制。

### Q: 如何启用消息压缩？

A: 使用 `WebSocketConfig::with_compression_enabled(true)` 启用压缩。

### Q: 如何实现心跳机制？

A: 定期发送 `Ping` 消息，并监听 `Pong` 响应。

### Q: 如何设置最大消息大小？

A: 使用 `WebSocketConfig::with_max_message_size()` 方法设置。

### Q: 如何启用TLS支持？

A: 使用 `WebSocketConfig::with_tls_config()` 方法配置TLS。

### Q: 如何处理大量并发连接？

A: 使用连接池、消息队列和适当的超时配置。

### Q: 如何实现消息路由？

A: 根据消息类型或内容实现自定义路由逻辑。

---

**WebSocket通信指南完成！** 🎉

现在您已经掌握了C10 Networks WebSocket的完整用法，可以构建实时通信应用程序了。

*最后更新: 2025年1月*  
*文档版本: v1.0*  
*维护者: C10 Networks 开发团队*
