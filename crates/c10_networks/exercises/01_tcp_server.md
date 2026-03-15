# C10 网络编程练习

> 难度: 中级-高级 | 预计时间: 60 分钟

---

## 🎯 练习目标

- 掌握 TCP/UDP 网络编程
- 理解异步网络 IO
- 实现协议解析

---

## 练习 1: Echo 服务器

实现一个 TCP Echo 服务器。

```rust
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};

async fn handle_client(mut stream: TcpStream) -> Result<(), Box<dyn std::error::Error>> {
    let mut buffer = [0u8; 1024];

    loop {
        let n = stream.read(&mut buffer).await?;
        if n == 0 {
            break; // 连接关闭
        }

        // Echo 回数据
        stream.write_all(&buffer[0..n]).await?;
    }

    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("Echo server listening on 127.0.0.1:8080");

    loop {
        let (stream, addr) = listener.accept().await?;
        println!("New connection from: {}", addr);

        tokio::spawn(async move {
            if let Err(e) = handle_client(stream).await {
                eprintln!("Error handling client: {}", e);
            }
        });
    }
}
```

**任务**:

1. 添加日志记录
2. 实现连接数限制
3. 添加优雅关闭

---

## 练习 2: 简单 HTTP 服务器

实现一个极简 HTTP 服务器。

```rust
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

async fn handle_http_request(stream: &mut tokio::net::TcpStream) -> Result<(), Box<dyn std::error::Error>> {
    let mut buffer = [0u8; 1024];
    let n = stream.read(&mut buffer).await?;
    let request = String::from_utf8_lossy(&buffer[..n]);

    // 简单解析 HTTP 请求
    let first_line = request.lines().next().unwrap_or("");
    let parts: Vec<&str> = first_line.split_whitespace().collect();

    let (status, body) = if parts.len() >= 2 {
        match parts[1] {
            "/" => ("200 OK", "<h1>Welcome!</h1>"),
            "/api" => ("200 OK", r#"{"status": "ok"}"#),
            _ => ("404 Not Found", "<h1>404 Not Found</h1>"),
        }
    } else {
        ("400 Bad Request", "Bad Request")
    };

    let content_type = if body.starts_with('{') {
        "application/json"
    } else {
        "text/html"
    };

    let response = format!(
        "HTTP/1.1 {}\r\nContent-Type: {}\r\nContent-Length: {}\r\n\r\n{}",
        status,
        content_type,
        body.len(),
        body
    );

    stream.write_all(response.as_bytes()).await?;
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("HTTP server listening on http://127.0.0.1:8080");

    loop {
        let (mut stream, addr) = listener.accept().await?;
        println!("Request from: {}", addr);

        tokio::spawn(async move {
            if let Err(e) = handle_http_request(&mut stream).await {
                eprintln!("Error: {}", e);
            }
        });
    }
}
```

**任务**:

1. 支持更多 HTTP 方法
2. 添加请求头解析
3. 实现静态文件服务

---

## 练习 3: UDP 聊天室

实现一个简单的 UDP 聊天室。

```rust
use tokio::net::UdpSocket;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

type Peers = Arc<Mutex<HashMap<std::net::SocketAddr, String>>>;

async fn run_server(addr: &str) -> Result<(), Box<dyn std::error::Error>> {
    let socket = Arc::new(UdpSocket::bind(addr).await?);
    let peers: Peers = Arc::new(Mutex::new(HashMap::new()));

    println!("UDP chat server running on {}", addr);

    let mut buf = [0u8; 1024];

    loop {
        let (len, peer_addr) = socket.recv_from(&mut buf).await?;
        let msg = String::from_utf8_lossy(&buf[..len]);

        let socket = Arc::clone(&socket);
        let peers = Arc::clone(&peers);

        tokio::spawn(async move {
            let mut peers = peers.lock().await;

            if msg.starts_with("/join ") {
                let name = msg[6..].trim().to_string();
                println!("{} joined from {}", name, peer_addr);
                peers.insert(peer_addr, name.clone());

                let welcome = format!("Welcome {}! Users online: {}",
                    name, peers.len());
                socket.send_to(welcome.as_bytes(), peer_addr).await.unwrap();
            } else {
                let name = peers.get(&peer_addr).cloned().unwrap_or_else(|| "Anonymous".to_string());
                let broadcast = format!("{}: {}", name, msg);

                // 广播给所有用户
                for (addr, _) in peers.iter() {
                    if addr != &peer_addr {
                        socket.send_to(broadcast.as_bytes(), *addr).await.unwrap();
                    }
                }
            }
        });
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    run_server("127.0.0.1:8080").await
}
```

**任务**:

1. 添加用户离开通知
2. 实现私聊功能
3. 添加消息历史

---

## 📚 相关文档

- [C10 网络模块](../README.md)
- [Tokio 网络编程](https://tokio.rs/tokio/tutorial)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
