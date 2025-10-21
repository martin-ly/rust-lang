# Rust 网络编程实战指南 (2025)

> **全面掌握 Rust 网络编程，从 TCP/UDP 到高性能网络服务**
>
> **版本**: Rust 1.90+ | **更新日期**: 2025-10-20 | **难度**: ⭐⭐⭐⭐

## 📋 目录1

- [Rust 网络编程实战指南 (2025)](#rust-网络编程实战指南-2025)
  - [📋 目录1](#-目录1)
  - [1. 网络编程基础1](#1-网络编程基础1)
    - [1.1 TCP vs UDP1](#11-tcp-vs-udp1)
    - [1.2 Rust 网络模型1](#12-rust-网络模型1)
    - [1.3 标准库网络 API1](#13-标准库网络-api1)
  - [2. TCP 编程1](#2-tcp-编程1)
    - [2.1 TCP 服务器1](#21-tcp-服务器1)
    - [2.2 TCP 客户端1](#22-tcp-客户端1)
    - [2.3 并发 TCP 服务器1](#23-并发-tcp-服务器1)
  - [3. UDP 编程1](#3-udp-编程1)
    - [3.1 UDP 服务器1](#31-udp-服务器1)
    - [3.2 UDP 客户端1](#32-udp-客户端1)
    - [3.3 UDP 广播和多播1](#33-udp-广播和多播1)
  - [4. 异步网络编程1](#4-异步网络编程1)
    - [4.1 Tokio TCP1](#41-tokio-tcp1)
    - [4.2 Tokio UDP1](#42-tokio-udp1)
    - [4.3 异步 HTTP 客户端1](#43-异步-http-客户端1)
  - [5. HTTP 服务开发1](#5-http-服务开发1)
    - [5.1 Axum Web 框架1](#51-axum-web-框架1)
    - [5.2 中间件1](#52-中间件1)
    - [5.3 路由和处理器1](#53-路由和处理器1)
  - [6. WebSocket1](#6-websocket1)
    - [6.1 WebSocket 服务器1](#61-websocket-服务器1)
    - [6.2 WebSocket 客户端1](#62-websocket-客户端1)
    - [6.3 实时聊天室1](#63-实时聊天室1)
  - [7. 协议实现1](#7-协议实现1)
    - [7.1 自定义二进制协议1](#71-自定义二进制协议1)
    - [7.2 HTTP/2 和 gRPC1](#72-http2-和-grpc1)
    - [7.3 QUIC 和 HTTP/31](#73-quic-和-http31)
  - [8. 性能优化1](#8-性能优化1)
    - [8.1 零拷贝 IO1](#81-零拷贝-io1)
    - [8.2 连接池1](#82-连接池1)
    - [8.3 负载均衡1](#83-负载均衡1)
  - [9. 常见陷阱1](#9-常见陷阱1)
  - [10. 最佳实践1](#10-最佳实践1)
  - [11. 参考资源1](#11-参考资源1)
    - [官方文档](#官方文档)
    - [推荐库](#推荐库)
    - [学习资源](#学习资源)
  - [总结](#总结)

---

## 1. 网络编程基础1

### 1.1 TCP vs UDP1

```text
┌────────────────────────────────────────────────────────────┐
│                     TCP (传输控制协议)                     │
├────────────────────────────────────────────────────────────┤
│  ✅ 可靠传输 (确认、重传)                                 │
│  ✅ 有序到达 (序列号)                                     │
│  ✅ 流量控制 (滑动窗口)                                   │
│  ✅ 拥塞控制 (慢启动、拥塞避免)                           │
│  ❌ 延迟较高 (三次握手、确认机制)                         │
│  📦 适用场景: HTTP, FTP, SSH, 数据库连接                  │
└────────────────────────────────────────────────────────────┘

┌────────────────────────────────────────────────────────────┐
│                     UDP (用户数据报协议)                   │
├────────────────────────────────────────────────────────────┤
│  ✅ 低延迟 (无连接)                                       │
│  ✅ 简单高效                                              │
│  ❌ 不可靠 (可能丢包)                                     │
│  ❌ 无序到达                                              │
│  📦 适用场景: DNS, 视频流, 游戏, IoT                      │
└────────────────────────────────────────────────────────────┘
```

### 1.2 Rust 网络模型1

**核心特性**:

1. **标准库支持**
   - `std::net::TcpListener`, `std::net::TcpStream`
   - `std::net::UdpSocket`
   - 同步阻塞 IO

2. **异步生态**
   - Tokio: 生产级异步运行时
   - Hyper: 高性能 HTTP 库
   - Tonic: gRPC 实现

### 1.3 标准库网络 API1

```rust
use std::net::{IpAddr, Ipv4Addr, SocketAddr, TcpListener, TcpStream, UdpSocket};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 地址表示
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let ip = IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1));
let socket_addr = SocketAddr::new(ip, 8080);

// 或者使用字符串解析
let addr: SocketAddr = "127.0.0.1:8080".parse().unwrap();
```

---

## 2. TCP 编程1

### 2.1 TCP 服务器1

```rust
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 简单 TCP Echo 服务器
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() -> std::io::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:8080")?;
    println!("服务器启动: 127.0.0.1:8080");

    for stream in listener.incoming() {
        let stream = stream?;
        println!("新连接: {}", stream.peer_addr()?);
        
        thread::spawn(move || {
            handle_client(stream).unwrap();
        });
    }

    Ok(())
}

fn handle_client(mut stream: TcpStream) -> std::io::Result<()> {
    let mut buffer = [0; 1024];
    
    loop {
        let bytes_read = stream.read(&mut buffer)?;
        
        if bytes_read == 0 {
            println!("客户端断开连接");
            break;
        }
        
        // Echo back
        stream.write_all(&buffer[..bytes_read])?;
    }
    
    Ok(())
}
```

### 2.2 TCP 客户端1

```rust
use std::io::{Read, Write};
use std::net::TcpStream;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// TCP 客户端
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() -> std::io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:8080")?;
    println!("已连接到服务器");
    
    // 发送数据
    let message = b"Hello, server!";
    stream.write_all(message)?;
    
    // 接收响应
    let mut buffer = [0; 1024];
    let bytes_read = stream.read(&mut buffer)?;
    
    let response = String::from_utf8_lossy(&buffer[..bytes_read]);
    println!("服务器响应: {}", response);
    
    Ok(())
}
```

### 2.3 并发 TCP 服务器1

```rust
use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 多线程聊天服务器
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
type ClientList = Arc<Mutex<Vec<TcpStream>>>;

fn main() -> std::io::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:8080")?;
    let clients: ClientList = Arc::new(Mutex::new(Vec::new()));
    
    println!("聊天服务器启动: 127.0.0.1:8080");
    
    for stream in listener.incoming() {
        let stream = stream?;
        let clients = Arc::clone(&clients);
        
        // 添加新客户端
        clients.lock().unwrap().push(stream.try_clone()?);
        
        thread::spawn(move || {
            handle_chat_client(stream, clients);
        });
    }
    
    Ok(())
}

fn handle_chat_client(stream: TcpStream, clients: ClientList) {
    let mut reader = BufReader::new(stream.try_clone().unwrap());
    let mut line = String::new();
    
    while reader.read_line(&mut line).unwrap() > 0 {
        println!("收到消息: {}", line.trim());
        
        // 广播消息给所有客户端
        let mut clients = clients.lock().unwrap();
        clients.retain_mut(|client| {
            client.write_all(line.as_bytes()).is_ok()
        });
        
        line.clear();
    }
}
```

---

## 3. UDP 编程1

### 3.1 UDP 服务器1

```rust
use std::net::UdpSocket;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// UDP Echo 服务器
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() -> std::io::Result<()> {
    let socket = UdpSocket::bind("127.0.0.1:8080")?;
    println!("UDP 服务器启动: 127.0.0.1:8080");
    
    let mut buffer = [0; 1024];
    
    loop {
        let (bytes_received, src_addr) = socket.recv_from(&mut buffer)?;
        println!("收到来自 {} 的 {} 字节", src_addr, bytes_received);
        
        // Echo back
        socket.send_to(&buffer[..bytes_received], src_addr)?;
    }
}
```

### 3.2 UDP 客户端1

```rust
use std::net::UdpSocket;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// UDP 客户端
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() -> std::io::Result<()> {
    let socket = UdpSocket::bind("0.0.0.0:0")?; // 绑定任意端口
    
    // 发送数据
    let message = b"Hello, UDP server!";
    socket.send_to(message, "127.0.0.1:8080")?;
    
    // 接收响应
    let mut buffer = [0; 1024];
    let (bytes_received, src_addr) = socket.recv_from(&mut buffer)?;
    
    let response = String::from_utf8_lossy(&buffer[..bytes_received]);
    println!("收到来自 {} 的响应: {}", src_addr, response);
    
    Ok(())
}
```

### 3.3 UDP 广播和多播1

```rust
use std::net::{Ipv4Addr, SocketAddr, UdpSocket};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// UDP 广播发送
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn broadcast_sender() -> std::io::Result<()> {
    let socket = UdpSocket::bind("0.0.0.0:0")?;
    socket.set_broadcast(true)?;
    
    let broadcast_addr: SocketAddr = "255.255.255.255:8080".parse().unwrap();
    socket.send_to(b"Broadcast message", broadcast_addr)?;
    
    Ok(())
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// UDP 多播接收
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn multicast_receiver() -> std::io::Result<()> {
    let socket = UdpSocket::bind("0.0.0.0:8080")?;
    let multicast_addr = Ipv4Addr::new(239, 0, 0, 1);
    
    socket.join_multicast_v4(&multicast_addr, &Ipv4Addr::UNSPECIFIED)?;
    
    let mut buffer = [0; 1024];
    loop {
        let (bytes_received, src_addr) = socket.recv_from(&mut buffer)?;
        println!("多播消息来自 {}: {:?}", src_addr, &buffer[..bytes_received]);
    }
}
```

---

## 4. 异步网络编程1

### 4.1 Tokio TCP1

```rust
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 异步 TCP Echo 服务器
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("异步服务器启动: 127.0.0.1:8080");
    
    loop {
        let (socket, addr) = listener.accept().await?;
        println!("新连接: {}", addr);
        
        tokio::spawn(async move {
            handle_client(socket).await.unwrap();
        });
    }
}

async fn handle_client(mut socket: TcpStream) -> Result<(), Box<dyn std::error::Error>> {
    let mut buffer = vec![0; 1024];
    
    loop {
        let bytes_read = socket.read(&mut buffer).await?;
        
        if bytes_read == 0 {
            break;
        }
        
        socket.write_all(&buffer[..bytes_read]).await?;
    }
    
    Ok(())
}
```

### 4.2 Tokio UDP1

```rust
use tokio::net::UdpSocket;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 异步 UDP 服务器
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let socket = UdpSocket::bind("127.0.0.1:8080").await?;
    let mut buffer = vec![0; 1024];
    
    loop {
        let (len, addr) = socket.recv_from(&mut buffer).await?;
        println!("收到 {} 字节来自 {}", len, addr);
        
        socket.send_to(&buffer[..len], addr).await?;
    }
}
```

### 4.3 异步 HTTP 客户端1

```rust
use reqwest;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Reqwest HTTP 客户端
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // GET 请求
    let response = reqwest::get("https://httpbin.org/get").await?;
    println!("Status: {}", response.status());
    let body = response.text().await?;
    println!("Body: {}", body);
    
    // POST 请求
    let client = reqwest::Client::new();
    let response = client
        .post("https://httpbin.org/post")
        .json(&serde_json::json!({
            "name": "Rust",
            "version": "1.90"
        }))
        .send()
        .await?;
    
    println!("POST 响应: {}", response.text().await?);
    
    Ok(())
}
```

---

## 5. HTTP 服务开发1

### 5.1 Axum Web 框架1

```rust
use axum::{
    routing::{get, post},
    http::StatusCode,
    Json, Router,
};
use serde::{Deserialize, Serialize};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 基本 HTTP 服务
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(root))
        .route("/users", post(create_user));
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    println!("服务器启动: http://0.0.0.0:3000");
    axum::serve(listener, app).await.unwrap();
}

async fn root() -> &'static str {
    "Hello, World!"
}

#[derive(Deserialize)]
struct CreateUser {
    username: String,
}

#[derive(Serialize)]
struct User {
    id: u64,
    username: String,
}

async fn create_user(Json(payload): Json<CreateUser>) -> (StatusCode, Json<User>) {
    let user = User {
        id: 1,
        username: payload.username,
    };
    
    (StatusCode::CREATED, Json(user))
}
```

### 5.2 中间件1

```rust
use axum::{
    middleware::{self, Next},
    response::Response,
    Router,
};
use tower_http::{cors::CorsLayer, trace::TraceLayer};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 中间件示例
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn logging_middleware(req: axum::extract::Request, next: Next) -> Response {
    println!("请求: {} {}", req.method(), req.uri());
    let response = next.run(req).await;
    println!("响应: {}", response.status());
    response
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", axum::routing::get(|| async { "Hello" }))
        .layer(middleware::from_fn(logging_middleware))
        .layer(CorsLayer::permissive())
        .layer(TraceLayer::new_for_http());
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    axum::serve(listener, app).await.unwrap();
}
```

### 5.3 路由和处理器1

```rust
use axum::{
    extract::{Path, Query, State},
    routing::get,
    Json, Router,
};
use serde::Deserialize;
use std::sync::Arc;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 路由参数提取
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Clone)]
struct AppState {
    counter: Arc<std::sync::Mutex<i32>>,
}

#[derive(Deserialize)]
struct Pagination {
    page: Option<u32>,
    per_page: Option<u32>,
}

async fn get_user(Path(user_id): Path<u32>) -> String {
    format!("User ID: {}", user_id)
}

async fn list_users(Query(pagination): Query<Pagination>) -> String {
    format!(
        "Page: {}, Per Page: {}",
        pagination.page.unwrap_or(1),
        pagination.per_page.unwrap_or(10)
    )
}

async fn get_counter(State(state): State<AppState>) -> String {
    let count = *state.counter.lock().unwrap();
    format!("Counter: {}", count)
}

#[tokio::main]
async fn main() {
    let state = AppState {
        counter: Arc::new(std::sync::Mutex::new(0)),
    };
    
    let app = Router::new()
        .route("/users/:id", get(get_user))
        .route("/users", get(list_users))
        .route("/counter", get(get_counter))
        .with_state(state);
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    axum::serve(listener, app).await.unwrap();
}
```

---

## 6. WebSocket1

### 6.1 WebSocket 服务器1

```rust
use axum::{
    extract::ws::{Message, WebSocket, WebSocketUpgrade},
    response::Response,
    routing::get,
    Router,
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// WebSocket Echo 服务器
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn ws_handler(ws: WebSocketUpgrade) -> Response {
    ws.on_upgrade(handle_socket)
}

async fn handle_socket(mut socket: WebSocket) {
    while let Some(msg) = socket.recv().await {
        if let Ok(msg) = msg {
            match msg {
                Message::Text(text) => {
                    println!("收到文本: {}", text);
                    if socket.send(Message::Text(text)).await.is_err() {
                        break;
                    }
                }
                Message::Binary(data) => {
                    println!("收到二进制数据: {} 字节", data.len());
                    if socket.send(Message::Binary(data)).await.is_err() {
                        break;
                    }
                }
                Message::Close(_) => {
                    println!("客户端关闭连接");
                    break;
                }
                _ => {}
            }
        }
    }
}

#[tokio::main]
async fn main() {
    let app = Router::new().route("/ws", get(ws_handler));
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    println!("WebSocket 服务器启动: ws://0.0.0.0:3000/ws");
    axum::serve(listener, app).await.unwrap();
}
```

### 6.2 WebSocket 客户端1

```rust
use tokio_tungstenite::{connect_async, tungstenite::protocol::Message};
use futures_util::{SinkExt, StreamExt};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// WebSocket 客户端
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (ws_stream, _) = connect_async("ws://127.0.0.1:3000/ws").await?;
    println!("已连接到 WebSocket 服务器");
    
    let (mut write, mut read) = ws_stream.split();
    
    // 发送消息
    write.send(Message::Text("Hello".to_string())).await?;
    
    // 接收消息
    while let Some(msg) = read.next().await {
        let msg = msg?;
        println!("收到: {:?}", msg);
    }
    
    Ok(())
}
```

### 6.3 实时聊天室1

```rust
use axum::{
    extract::ws::{Message, WebSocket, WebSocketUpgrade},
    response::Response,
    routing::get,
    Router,
};
use futures_util::{SinkExt, StreamExt};
use std::sync::Arc;
use tokio::sync::{broadcast, Mutex};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 聊天室状态
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
struct ChatState {
    tx: broadcast::Sender<String>,
}

async fn ws_handler(
    ws: WebSocketUpgrade,
    axum::extract::State(state): axum::extract::State<Arc<ChatState>>,
) -> Response {
    ws.on_upgrade(move |socket| handle_chat(socket, state))
}

async fn handle_chat(socket: WebSocket, state: Arc<ChatState>) {
    let (mut sender, mut receiver) = socket.split();
    let mut rx = state.tx.subscribe();
    
    // 接收广播消息并发送给客户端
    let mut send_task = tokio::spawn(async move {
        while let Ok(msg) = rx.recv().await {
            if sender.send(Message::Text(msg)).await.is_err() {
                break;
            }
        }
    });
    
    // 接收客户端消息并广播
    let tx = state.tx.clone();
    let mut recv_task = tokio::spawn(async move {
        while let Some(Ok(Message::Text(text))) = receiver.next().await {
            let _ = tx.send(text);
        }
    });
    
    // 等待任一任务结束
    tokio::select! {
        _ = &mut send_task => recv_task.abort(),
        _ = &mut recv_task => send_task.abort(),
    };
}

#[tokio::main]
async fn main() {
    let (tx, _rx) = broadcast::channel(100);
    let state = Arc::new(ChatState { tx });
    
    let app = Router::new()
        .route("/ws", get(ws_handler))
        .with_state(state);
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    println!("聊天室服务器启动: ws://0.0.0.0:3000/ws");
    axum::serve(listener, app).await.unwrap();
}
```

---

## 7. 协议实现1

### 7.1 自定义二进制协议1

```rust
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 自定义协议格式
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [4 bytes: message length] [N bytes: message data]

async fn send_message(stream: &mut TcpStream, data: &[u8]) -> std::io::Result<()> {
    let len = data.len() as u32;
    stream.write_u32(len).await?;
    stream.write_all(data).await?;
    stream.flush().await?;
    Ok(())
}

async fn recv_message(stream: &mut TcpStream) -> std::io::Result<Vec<u8>> {
    let len = stream.read_u32().await?;
    let mut buffer = vec![0; len as usize];
    stream.read_exact(&mut buffer).await?;
    Ok(buffer)
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:8080").await?;
    
    // 发送消息
    send_message(&mut stream, b"Hello, custom protocol!").await?;
    
    // 接收响应
    let response = recv_message(&mut stream).await?;
    println!("收到响应: {:?}", String::from_utf8_lossy(&response));
    
    Ok(())
}
```

### 7.2 HTTP/2 和 gRPC1

```rust
// proto/hello.proto
syntax = "proto3";
package hello;

service Greeter {
    rpc SayHello (HelloRequest) returns (HelloReply);
}

message HelloRequest {
    string name = 1;
}

message HelloReply {
    string message = 1;
}
```

```rust
use tonic::{transport::Server, Request, Response, Status};

pub mod hello {
    tonic::include_proto!("hello");
}

use hello::greeter_server::{Greeter, GreeterServer};
use hello::{HelloReply, HelloRequest};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// gRPC 服务实现
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Default)]
pub struct MyGreeter {}

#[tonic::async_trait]
impl Greeter for MyGreeter {
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloReply>, Status> {
        let reply = HelloReply {
            message: format!("Hello, {}!", request.into_inner().name),
        };
        Ok(Response::new(reply))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let addr = "0.0.0.0:50051".parse()?;
    let greeter = MyGreeter::default();
    
    Server::builder()
        .add_service(GreeterServer::new(greeter))
        .serve(addr)
        .await?;
    
    Ok(())
}
```

### 7.3 QUIC 和 HTTP/31

```rust
use quinn::{Endpoint, ServerConfig};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// QUIC 服务器 (HTTP/3 基础)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let server_config = ServerConfig::with_single_cert(vec![], rustls::PrivateKey(vec![]))?;
    let endpoint = Endpoint::server(server_config, "127.0.0.1:4433".parse()?)?;
    
    while let Some(connecting) = endpoint.accept().await {
        tokio::spawn(async move {
            let connection = connecting.await.unwrap();
            println!("新连接: {:?}", connection.remote_address());
            
            while let Ok((mut send, mut recv)) = connection.accept_bi().await {
                let data = recv.read_to_end(1024).await.unwrap();
                send.write_all(&data).await.unwrap();
            }
        });
    }
    
    Ok(())
}
```

---

## 8. 性能优化1

### 8.1 零拷贝 IO1

```rust
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 使用 bytes 库减少内存拷贝
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
use bytes::{Buf, BytesMut};

async fn efficient_read_write(stream: &mut TcpStream) -> std::io::Result<()> {
    let mut buffer = BytesMut::with_capacity(4096);
    
    // 读取数据 (零拷贝)
    stream.read_buf(&mut buffer).await?;
    
    // 处理数据 (避免额外拷贝)
    let data = buffer.freeze();
    
    // 写入数据
    stream.write_all(&data).await?;
    
    Ok(())
}
```

### 8.2 连接池1

```rust
use sqlx::postgres::PgPoolOptions;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 数据库连接池
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    let pool = PgPoolOptions::new()
        .max_connections(20)
        .connect("postgres://user:pass@localhost/db")
        .await?;
    
    // 从池中获取连接 (自动管理)
    let row: (i64,) = sqlx::query_as("SELECT COUNT(*) FROM users")
        .fetch_one(&pool)
        .await?;
    
    println!("User count: {}", row.0);
    
    Ok(())
}
```

### 8.3 负载均衡1

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 轮询负载均衡
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
struct LoadBalancer {
    backends: Vec<String>,
    current: Arc<RwLock<usize>>,
}

impl LoadBalancer {
    fn new(backends: Vec<String>) -> Self {
        Self {
            backends,
            current: Arc::new(RwLock::new(0)),
        }
    }
    
    async fn next_backend(&self) -> String {
        let mut current = self.current.write().await;
        let backend = self.backends[*current % self.backends.len()].clone();
        *current += 1;
        backend
    }
}

#[tokio::main]
async fn main() {
    let lb = LoadBalancer::new(vec![
        "backend1:8080".to_string(),
        "backend2:8080".to_string(),
        "backend3:8080".to_string(),
    ]);
    
    for _ in 0..10 {
        let backend = lb.next_backend().await;
        println!("请求转发到: {}", backend);
    }
}
```

---

## 9. 常见陷阱1

1. **未正确处理连接关闭**
   - 检查 `read()` 返回 0 表示连接关闭
   - 使用 `shutdown()` 优雅关闭连接

2. **缓冲区溢出**
   - 使用固定大小缓冲区时检查边界
   - 对用户输入进行长度限制

3. **阻塞操作**
   - 在异步上下文中避免同步阻塞操作
   - 使用 `tokio::task::spawn_blocking` 处理 CPU 密集型任务

4. **超时未设置**
   - 为网络操作设置合理超时
   - 使用 `tokio::time::timeout`

5. **错误处理不完整**
   - 处理所有可能的网络错误
   - 区分可恢复和不可恢复错误

---

## 10. 最佳实践1

1. **使用异步 IO**
   - 生产环境优先使用 Tokio
   - 利用异步提高并发性能

2. **连接池管理**
   - 数据库、HTTP 客户端使用连接池
   - 合理设置连接池大小

3. **优雅关闭**
   - 监听 SIGTERM/SIGINT 信号
   - 等待正在处理的请求完成

4. **性能监控**
   - 使用 `tracing` 记录网络事件
   - 监控连接数、延迟、吞吐量

5. **安全性**
   - 使用 TLS/SSL 加密传输
   - 验证输入数据
   - 实现速率限制

---

## 11. 参考资源1

### 官方文档

- [std::net](https://doc.rust-lang.org/std/net/)
- [Tokio Guide](https://tokio.rs/tokio/tutorial)
- [Axum](https://docs.rs/axum)

### 推荐库

- [Tokio](https://tokio.rs) - 异步运行时
- [Hyper](https://hyper.rs) - HTTP 库
- [Tonic](https://github.com/hyperium/tonic) - gRPC
- [Quinn](https://github.com/quinn-rs/quinn) - QUIC

### 学习资源

- [Tokio Tutorial](https://tokio.rs/tokio/tutorial)
- [Rust Network Programming](https://rust-lang.github.io/async-book/)

---

## 总结

Rust 网络编程的核心优势:

1. **类型安全** - 编译时检查网络错误
2. **零成本抽象** - 高性能网络 IO
3. **异步生态** - Tokio 生产级异步运行时
4. **内存安全** - 防止缓冲区溢出

通过本指南，你已经掌握了 Rust 网络编程的核心技术和最佳实践！
