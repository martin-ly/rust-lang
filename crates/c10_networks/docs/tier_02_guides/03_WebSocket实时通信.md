# C10 Networks - Tier 2: WebSocket 实时通信

> **文档版本**: v1.0.0  
> **最后更新**: 2025-10-23  
> **Rust 版本**: 1.90+  
> **预计阅读**: 35 分钟

---

## 📋 目录

- [C10 Networks - Tier 2: WebSocket 实时通信](#c10-networks---tier-2-websocket-实时通信)
  - [📋 目录](#-目录)
  - [1. WebSocket 基础](#1-websocket-基础)
    - [1.1 WebSocket vs HTTP](#11-websocket-vs-http)
    - [1.2 WebSocket 握手](#12-websocket-握手)
  - [2. 使用 tokio-tungstenite](#2-使用-tokio-tungstenite)
    - [2.1 基础客户端](#21-基础客户端)
    - [2.2 基础服务器](#22-基础服务器)
  - [3. 客户端开发](#3-客户端开发)
    - [3.1 完整客户端](#31-完整客户端)
    - [3.2 自动重连](#32-自动重连)
  - [4. 服务器开发](#4-服务器开发)
    - [4.1 广播服务器](#41-广播服务器)
    - [4.2 房间管理](#42-房间管理)
  - [5. 消息格式与编解码](#5-消息格式与编解码)
    - [5.1 JSON 消息](#51-json-消息)
    - [5.2 二进制消息](#52-二进制消息)
  - [6. 实战案例](#6-实战案例)
    - [6.1 聊天室](#61-聊天室)
    - [6.2 实时数据推送](#62-实时数据推送)
  - [7. 总结](#7-总结)
    - [核心要点](#核心要点)
    - [最佳实践](#最佳实践)
  - [📚 参考资源](#-参考资源)

---

## 1. WebSocket 基础

### 1.1 WebSocket vs HTTP

| 特性 | HTTP | WebSocket |
|-----|------|-----------|
| **连接方式** | 短连接 | 长连接 |
| **通信方向** | 单向（请求/响应） | 双向 |
| **开销** | 每次请求都有头部 | 握手后低开销 |
| **适用场景** | 普通数据获取 | 实时通信 |

### 1.2 WebSocket 握手

**HTTP 升级请求**：

```http
GET /chat HTTP/1.1
Host: server.example.com
Upgrade: websocket
Connection: Upgrade
Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==
Sec-WebSocket-Version: 13
```

**服务器响应**：

```http
HTTP/1.1 101 Switching Protocols
Upgrade: websocket
Connection: Upgrade
Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=
```

---

## 2. 使用 tokio-tungstenite

### 2.1 基础客户端

```rust
use tokio_tungstenite::{connect_async, tungstenite::Message};
use futures_util::{StreamExt, SinkExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 连接 WebSocket 服务器
    let (ws_stream, _) = connect_async("ws://echo.websocket.org").await?;
    println!("WebSocket 已连接");
    
    let (mut write, mut read) = ws_stream.split();
    
    // 发送消息
    write.send(Message::Text("Hello WebSocket".to_string())).await?;
    
    // 接收消息
    if let Some(msg) = read.next().await {
        let msg = msg?;
        println!("收到: {}", msg);
    }
    
    Ok(())
}
```

### 2.2 基础服务器

```rust
use tokio::net::TcpListener;
use tokio_tungstenite::accept_async;
use futures_util::{StreamExt, SinkExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:9001").await?;
    println!("WebSocket 服务器运行在 ws://127.0.0.1:9001");
    
    while let Ok((stream, addr)) = listener.accept().await {
        tokio::spawn(async move {
            println!("新连接: {}", addr);
            
            let ws_stream = accept_async(stream).await.expect("握手失败");
            let (mut write, mut read) = ws_stream.split();
            
            while let Some(msg) = read.next().await {
                let msg = msg.expect("读取消息失败");
                
                if msg.is_text() || msg.is_binary() {
                    // 回显消息
                    write.send(msg).await.expect("发送消息失败");
                }
            }
        });
    }
    
    Ok(())
}
```

---

## 3. 客户端开发

### 3.1 完整客户端

```rust
use tokio_tungstenite::{connect_async, tungstenite::Message};
use futures_util::{StreamExt, SinkExt, stream::SplitSink};
use tokio::sync::mpsc;
use tokio::net::TcpStream;
use tokio_tungstenite::WebSocketStream;

type WsWrite = SplitSink<WebSocketStream<tokio_tungstenite::MaybeTlsStream<TcpStream>>, Message>;

struct WebSocketClient {
    sender: mpsc::UnboundedSender<Message>,
}

impl WebSocketClient {
    async fn new(url: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let (ws_stream, _) = connect_async(url).await?;
        let (write, mut read) = ws_stream.split();
        
        let (tx, mut rx) = mpsc::unbounded_channel::<Message>();
        
        // 发送任务
        tokio::spawn(async move {
            Self::send_task(write, &mut rx).await;
        });
        
        // 接收任务
        tokio::spawn(async move {
            Self::receive_task(&mut read).await;
        });
        
        Ok(Self { sender: tx })
    }
    
    async fn send_task(mut write: WsWrite, rx: &mut mpsc::UnboundedReceiver<Message>) {
        while let Some(msg) = rx.recv().await {
            if write.send(msg).await.is_err() {
                break;
            }
        }
    }
    
    async fn receive_task<S>(read: &mut futures_util::stream::SplitStream<S>)
    where
        S: StreamExt<Item = Result<Message, tokio_tungstenite::tungstenite::Error>> + Unpin,
    {
        while let Some(msg) = read.next().await {
            match msg {
                Ok(Message::Text(text)) => {
                    println!("收到文本: {}", text);
                }
                Ok(Message::Binary(data)) => {
                    println!("收到二进制: {} 字节", data.len());
                }
                Ok(Message::Close(_)) => {
                    println!("连接关闭");
                    break;
                }
                Err(e) => {
                    eprintln!("接收错误: {}", e);
                    break;
                }
                _ => {}
            }
        }
    }
    
    fn send(&self, msg: Message) -> Result<(), Box<dyn std::error::Error>> {
        self.sender.send(msg)?;
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = WebSocketClient::new("ws://echo.websocket.org").await?;
    
    // 发送测试消息
    client.send(Message::Text("Test 1".to_string()))?;
    client.send(Message::Text("Test 2".to_string()))?;
    
    tokio::time::sleep(tokio::time::Duration::from_secs(3)).await;
    
    Ok(())
}
```

### 3.2 自动重连

```rust
use tokio_tungstenite::connect_async;
use std::time::Duration;

async fn connect_with_retry(url: &str, max_retries: u32) -> Result<(), Box<dyn std::error::Error>> {
    let mut attempts = 0;
    
    loop {
        match connect_async(url).await {
            Ok((ws_stream, _)) => {
                println!("连接成功");
                // 处理连接...
                break;
            }
            Err(e) if attempts < max_retries => {
                attempts += 1;
                println!("连接失败（{}/{}）: {}", attempts, max_retries, e);
                tokio::time::sleep(Duration::from_secs(2_u64.pow(attempts))).await;
            }
            Err(e) => return Err(e.into()),
        }
    }
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    connect_with_retry("ws://echo.websocket.org", 3).await
}
```

---

## 4. 服务器开发

### 4.1 广播服务器

```rust
use tokio::net::TcpListener;
use tokio::sync::broadcast;
use tokio_tungstenite::{accept_async, tungstenite::Message};
use futures_util::{StreamExt, SinkExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:9001").await?;
    let (tx, _rx) = broadcast::channel::<String>(100);
    
    println!("广播服务器运行在 ws://127.0.0.1:9001");
    
    loop {
        let (stream, addr) = listener.accept().await?;
        let tx = tx.clone();
        let mut rx = tx.subscribe();
        
        tokio::spawn(async move {
            let ws_stream = accept_async(stream).await.expect("握手失败");
            let (mut write, mut read) = ws_stream.split();
            
            println!("客户端 {} 已连接", addr);
            
            // 接收并广播消息
            let tx_clone = tx.clone();
            tokio::spawn(async move {
                while let Some(msg) = read.next().await {
                    if let Ok(Message::Text(text)) = msg {
                        println!("收到消息: {}", text);
                        let _ = tx_clone.send(text);
                    }
                }
                println!("客户端 {} 断开连接", addr);
            });
            
            // 转发广播消息
            while let Ok(text) = rx.recv().await {
                if write.send(Message::Text(text)).await.is_err() {
                    break;
                }
            }
        });
    }
}
```

### 4.2 房间管理

```rust
use tokio::sync::RwLock;
use std::collections::HashMap;
use std::sync::Arc;

type ClientId = usize;
type RoomId = String;

struct Room {
    id: RoomId,
    clients: Vec<ClientId>,
}

struct RoomManager {
    rooms: Arc<RwLock<HashMap<RoomId, Room>>>,
    next_client_id: Arc<RwLock<ClientId>>,
}

impl RoomManager {
    fn new() -> Self {
        Self {
            rooms: Arc::new(RwLock::new(HashMap::new())),
            next_client_id: Arc::new(RwLock::new(0)),
        }
    }
    
    async fn create_room(&self, room_id: RoomId) {
        let mut rooms = self.rooms.write().await;
        rooms.insert(room_id.clone(), Room {
            id: room_id,
            clients: Vec::new(),
        });
    }
    
    async fn join_room(&self, room_id: &str, client_id: ClientId) -> bool {
        let mut rooms = self.rooms.write().await;
        if let Some(room) = rooms.get_mut(room_id) {
            room.clients.push(client_id);
            true
        } else {
            false
        }
    }
    
    async fn leave_room(&self, room_id: &str, client_id: ClientId) {
        let mut rooms = self.rooms.write().await;
        if let Some(room) = rooms.get_mut(room_id) {
            room.clients.retain(|&id| id != client_id);
        }
    }
    
    async fn get_next_client_id(&self) -> ClientId {
        let mut id = self.next_client_id.write().await;
        let current = *id;
        *id += 1;
        current
    }
}

fn main() {
    let manager = RoomManager::new();
    println!("房间管理器已创建");
}
```

---

## 5. 消息格式与编解码

### 5.1 JSON 消息

```rust
use serde::{Serialize, Deserialize};
use tokio_tungstenite::tungstenite::Message;

#[derive(Serialize, Deserialize, Debug)]
#[serde(tag = "type")]
enum WsMessage {
    Join { room: String, username: String },
    Leave { room: String },
    Message { room: String, content: String },
    Ping,
    Pong,
}

impl WsMessage {
    fn to_message(&self) -> Result<Message, serde_json::Error> {
        let json = serde_json::to_string(self)?;
        Ok(Message::Text(json))
    }
    
    fn from_message(msg: Message) -> Result<Self, Box<dyn std::error::Error>> {
        match msg {
            Message::Text(text) => {
                let parsed = serde_json::from_str(&text)?;
                Ok(parsed)
            }
            _ => Err("不支持的消息类型".into()),
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let msg = WsMessage::Join {
        room: "general".to_string(),
        username: "Alice".to_string(),
    };
    
    let ws_msg = msg.to_message()?;
    println!("序列化: {:?}", ws_msg);
    
    let parsed = WsMessage::from_message(ws_msg)?;
    println!("反序列化: {:?}", parsed);
    
    Ok(())
}
```

### 5.2 二进制消息

```rust
use tokio_tungstenite::tungstenite::Message;

fn encode_binary_message(msg_type: u8, data: &[u8]) -> Message {
    let mut payload = vec![msg_type];
    payload.extend_from_slice(data);
    Message::Binary(payload)
}

fn decode_binary_message(msg: Message) -> Result<(u8, Vec<u8>), String> {
    match msg {
        Message::Binary(data) if !data.is_empty() => {
            let msg_type = data[0];
            let payload = data[1..].to_vec();
            Ok((msg_type, payload))
        }
        _ => Err("无效的二进制消息".to_string()),
    }
}

fn main() {
    let msg = encode_binary_message(1, b"Hello");
    println!("编码: {:?}", msg);
    
    let (msg_type, data) = decode_binary_message(msg).unwrap();
    println!("解码: type={}, data={:?}", msg_type, String::from_utf8_lossy(&data));
}
```

---

## 6. 实战案例

### 6.1 聊天室

```rust
use tokio::net::TcpListener;
use tokio::sync::{broadcast, mpsc};
use tokio_tungstenite::{accept_async, tungstenite::Message};
use futures_util::{StreamExt, SinkExt};
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Clone, Debug)]
struct ChatMessage {
    username: String,
    content: String,
    timestamp: i64,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:9001").await?;
    let (broadcast_tx, _) = broadcast::channel::<ChatMessage>(100);
    
    println!("聊天室服务器运行在 ws://127.0.0.1:9001");
    
    loop {
        let (stream, addr) = listener.accept().await?;
        let broadcast_tx = broadcast_tx.clone();
        let mut broadcast_rx = broadcast_tx.subscribe();
        
        tokio::spawn(async move {
            let ws_stream = accept_async(stream).await.expect("握手失败");
            let (mut write, mut read) = ws_stream.split();
            
            println!("新用户加入: {}", addr);
            
            // 接收并广播消息
            let tx = broadcast_tx.clone();
            tokio::spawn(async move {
                while let Some(msg) = read.next().await {
                    if let Ok(Message::Text(text)) = msg {
                        if let Ok(chat_msg) = serde_json::from_str::<ChatMessage>(&text) {
                            println!("消息: {} - {}", chat_msg.username, chat_msg.content);
                            let _ = tx.send(chat_msg);
                        }
                    }
                }
            });
            
            // 转发消息
            while let Ok(chat_msg) = broadcast_rx.recv().await {
                let json = serde_json::to_string(&chat_msg).unwrap();
                if write.send(Message::Text(json)).await.is_err() {
                    break;
                }
            }
            
            println!("用户离开: {}", addr);
        });
    }
}
```

### 6.2 实时数据推送

```rust
use tokio::time::{interval, Duration};
use tokio_tungstenite::tungstenite::Message;
use serde_json::json;

async fn data_pusher() -> Result<(), Box<dyn std::error::Error>> {
    let mut ticker = interval(Duration::from_secs(1));
    
    loop {
        ticker.tick().await;
        
        // 模拟实时数据
        let data = json!({
            "timestamp": chrono::Utc::now().timestamp(),
            "value": rand::random::<f64>() * 100.0,
        });
        
        println!("推送数据: {}", data);
        
        // 在实际应用中，这里会发送到 WebSocket 客户端
        // write.send(Message::Text(data.to_string())).await?;
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    data_pusher().await
}
```

---

## 7. 总结

### 核心要点

| 特性 | 描述 | 适用场景 |
|-----|------|---------|
| **全双工通信** | 双向实时通信 | 聊天、游戏 |
| **低延迟** | 减少握手开销 | 实时数据 |
| **事件驱动** | 异步消息处理 | 高并发 |

### 最佳实践

1. **心跳检测**: 定期发送 Ping/Pong 维持连接
2. **错误处理**: 妥善处理断线重连
3. **消息队列**: 缓冲待发送消息
4. **状态管理**: 维护连接状态
5. **资源清理**: 连接关闭时清理资源

---

## 📚 参考资源

- [WebSocket RFC](https://tools.ietf.org/html/rfc6455)
- [tokio-tungstenite](https://docs.rs/tokio-tungstenite/)
- [WebSocket MDN](https://developer.mozilla.org/zh-CN/docs/Web/API/WebSocket)

---

**下一步**: 学习 [TCP/UDP 编程](04_TCP_UDP编程.md)，掌握底层网络协议。
