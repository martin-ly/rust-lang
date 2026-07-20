# 知识图谱

本页展示网络编程的概念关系。

---

## 📊 核心概念关系图

```text
                    [网络编程]
                         |
         +---------------+---------------+
         |               |               |
    [网络协议]       [I/O模型]       [网络库]
         |               |               |
    +----+----+     +----+----+     +----+----+
    |    |    |     |    |    |     |    |    |
  TCP  UDP HTTP   异步  同步  tokio  hyper  tonic
       WebSocket        阻塞        axum   reqwest
```

---

## 🎯 概念层次

### 1. 网络协议 (Network Protocols)

**传输层协议**:

- **TCP**: 可靠传输、面向连接、流式协议
- **UDP**: 不可靠传输、无连接、数据报协议
- **QUIC**: 基于UDP的可靠传输

**应用层协议**:

- **HTTP/1.1**: 传统HTTP协议
- **HTTP/2**: 多路复用、服务器推送
- **HTTP/3**: 基于QUIC
- **WebSocket**: 全双工通信
- **gRPC**: 基于HTTP/2的RPC框架
- **DNS**: 域名解析

**Rust实现**:

- `std::net`: 标准库网络模块
- `tokio`: 异步运行时
- `hyper`: HTTP库
- `tonic`: gRPC框架
- `quinn`: QUIC实现

---

### 2. I/O模型 (I/O Models)

**同步I/O**:

- **阻塞I/O**: 简单但低效
- **非阻塞I/O**: 需要轮询
- **多路复用** (select/poll/epoll): 监控多个连接

**异步I/O**:

- **Future模型**: 惰性计算
- **async/await**: 语法糖
- **Runtime**: tokio, async-std

**性能特点**:

- 同步I/O: 每连接一线程
- 异步I/O: 少量线程处理大量连接
- 零拷贝: 减少数据复制

---

### 3. 网络编程库 (Network Libraries)

**HTTP客户端**:

- **reqwest**: 高级HTTP客户端
- **ureq**: 同步HTTP客户端
- **surf**: 异步HTTP客户端

**HTTP服务器**:

- **axum**: 现代web框架
- **actix-web**: 高性能web框架
- **warp**: 过滤器式web框架
- **rocket**: 易用web框架

**底层网络**:

- **mio**: 底层异步I/O
- **tokio**: 异步运行时
- **async-std**: 异步标准库

**特殊协议**:

- **tonic**: gRPC框架
- **tokio-tungstenite**: WebSocket
- **quinn**: QUIC实现
- **libp2p**: P2P网络栈

---

## 🔗 概念关联

### TCP ←→ 异步I/O

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

// 异步TCP服务器
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 绑定监听地址
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("Server listening on 127.0.0.1:8080");
    
    loop {
        // 接受连接（异步）
        let (mut socket, addr) = listener.accept().await?;
        println!("New connection from: {}", addr);
        
        // 为每个连接创建任务
        tokio::spawn(async move {
            let mut buf = vec![0; 1024];
            
            loop {
                // 异步读取
                let n = match socket.read(&mut buf).await {
                    Ok(n) if n == 0 => return, // 连接关闭
                    Ok(n) => n,
                    Err(e) => {
                        eprintln!("Failed to read: {}", e);
                        return;
                    }
                };
                
                // 异步写入（回显）
                if let Err(e) = socket.write_all(&buf[0..n]).await {
                    eprintln!("Failed to write: {}", e);
                    return;
                }
            }
        });
    }
}
```

### HTTP ←→ Web框架

```rust
use axum::{
    routing::{get, post},
    Router,
    Json,
    extract::Path,
};
use serde::{Deserialize, Serialize};

// 请求/响应类型
#[derive(Deserialize)]
struct CreateUser {
    name: String,
    email: String,
}

#[derive(Serialize)]
struct User {
    id: u64,
    name: String,
    email: String,
}

// 路由处理器
async fn get_user(Path(id): Path<u64>) -> Json<User> {
    Json(User {
        id,
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
    })
}

async fn create_user(Json(payload): Json<CreateUser>) -> Json<User> {
    Json(User {
        id: 1,
        name: payload.name,
        email: payload.email,
    })
}

#[tokio::main]
async fn main() {
    // 构建路由
    let app = Router::new()
        .route("/users/:id", get(get_user))
        .route("/users", post(create_user));
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    axum::serve(listener, app)
        .await
        .unwrap();
}
```

### WebSocket ←→ 实时通信

```rust
use tokio_tungstenite::{connect_async, tungstenite::Message};
use futures_util::{SinkExt, StreamExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 连接WebSocket服务器
    let (mut ws_stream, _) = connect_async("ws://localhost:8080").await?;
    println!("WebSocket connected");
    
    // 发送消息
    ws_stream.send(Message::Text("Hello!".to_string())).await?;
    
    // 接收消息
    while let Some(msg) = ws_stream.next().await {
        match msg? {
            Message::Text(text) => println!("Received: {}", text),
            Message::Close(_) => break,
            _ => {}
        }
    }
    
    Ok(())
}
```

---

## 📚 学习路径图

```text
第一步: 理解网络协议基础
    ↓
第二步: 掌握TCP/UDP编程
    ↓
第三步: 学习异步I/O模型
    ↓
第四步: 使用HTTP客户端/服务器
    ↓
第五步: 高级协议(gRPC, WebSocket)
```

---

## 🎓 协议与库对应关系

### HTTP生态

| 层次 | 客户端 | 服务器 |
|------|--------|--------|
| **高层** | reqwest | axum, actix-web |
| **中层** | hyper | hyper |
| **底层** | tokio, mio | tokio, mio |

### 实时通信

| 协议 | 库 | 特点 |
|------|------|------|
| **WebSocket** | tokio-tungstenite | 双向通信 |
| **gRPC** | tonic | HTTP/2 RPC |
| **QUIC** | quinn | UDP可靠传输 |

### P2P网络

| 层次 | 库 | 用途 |
|------|------|------|
| **应用层** | libp2p | P2P框架 |
| **传输层** | quinn, tokio | 传输协议 |
| **发现** | mdns, kad | 节点发现 |

---

## 💡 核心原则

### 1. 异步优先

```text
异步I/O → 高并发 → 资源高效利用
```

### 2. 零拷贝优化

```text
减少拷贝 → 降低延迟 → 提高吞吐量
```

### 3. 类型安全

```text
类型系统 → 编译时检查 → 运行时安全
```

---

## 🔍 Rust 1.90 增强特性

### 1. 异步trait

```rust
// 异步trait现已稳定
trait AsyncRepository {
    async fn find(&self, id: i64) -> Result<User, Error>;
    async fn save(&self, user: User) -> Result<(), Error>;
}

struct DbRepository;

impl AsyncRepository for DbRepository {
    async fn find(&self, id: i64) -> Result<User, Error> {
        // 实现细节
        Ok(User::default())
    }
    
    async fn save(&self, user: User) -> Result<(), Error> {
        // 实现细节
        Ok(())
    }
}
```

### 2. 改进的错误处理

```rust
use std::error::Error;
use std::fmt;

// 自定义网络错误
#[derive(Debug)]
enum NetworkError {
    Timeout,
    ConnectionRefused,
    InvalidResponse,
}

impl fmt::Display for NetworkError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NetworkError::Timeout => write!(f, "Request timeout"),
            NetworkError::ConnectionRefused => write!(f, "Connection refused"),
            NetworkError::InvalidResponse => write!(f, "Invalid response"),
        }
    }
}

impl Error for NetworkError {}

// 使用Result链式处理
async fn fetch_data(url: &str) -> Result<String, Box<dyn Error>> {
    let response = reqwest::get(url)
        .await?
        .error_for_status()?;
    
    let body = response.text().await?;
    Ok(body)
}
```

### 3. 高性能HTTP/3

```rust
use quinn::{Endpoint, ServerConfig};

// HTTP/3服务器（基于QUIC）
async fn run_h3_server() -> Result<(), Box<dyn std::error::Error>> {
    let server_config = ServerConfig::with_single_cert(certs, key)?;
    let endpoint = Endpoint::server(server_config, "0.0.0.0:4433".parse()?)?;
    
    println!("HTTP/3 server listening");
    
    while let Some(conn) = endpoint.accept().await {
        tokio::spawn(async move {
            let connection = conn.await?;
            // 处理HTTP/3连接
            Ok::<(), Box<dyn std::error::Error>>(())
        });
    }
    
    Ok(())
}
```

---

## 📖 相关章节

- **[基础概念](./foundations.md)** - 网络理论
- **[实践指南](./guides.md)** - 实战技巧
- **[代码示例](./examples.md)** - 完整实现 ⭐
- **[返回模块首页](./README.md)**

---

## 🔗 扩展学习

### 深入阅读

- [完整网络编程指南](../../crates/c10_networks/README.md)
- [异步编程书](https://rust-lang.github.io/async-book/)
- [网络协议RFC](https://www.rfc-editor.org/)

### 相关模块

- **[C06: 异步编程](../c06/README.md)** - 异步基础
- **[C05: 多线程](../c05/README.md)** - 并发编程
- **[C13: 可靠性](../c13/README.md)** - 容错机制

---

## 🎯 实践项目建议

### 入门级

- TCP回显服务器
- HTTP客户端工具
- 简单聊天服务器

### 进阶级

- REST API服务
- WebSocket实时应用
- 负载均衡器

### 高级

- 分布式消息队列
- API网关
- P2P文件共享

---

## 🌐 网络栈层次

```text
应用层:  HTTP, gRPC, WebSocket
    ↓
传输层:  TCP, UDP, QUIC
    ↓
网络层:  IP
    ↓
链路层:  Ethernet, WiFi
```

**Rust提供各层抽象**:

- 应用层: axum, tonic, reqwest
- 传输层: tokio::net, quinn
- 网络层: pnet (数据包捕获)

---

**掌握网络编程是构建现代分布式系统的基础！** 🚀
