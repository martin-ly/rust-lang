# WebSocket - 实时双向通信

## 📋 目录

- [WebSocket - 实时双向通信](#websocket---实时双向通信)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [Axum WebSocket](#axum-websocket)
    - [基础示例](#基础示例)
    - [广播消息](#广播消息)
  - [Tokio-tungstenite](#tokio-tungstenite)
    - [WebSocket 客户端](#websocket-客户端)
  - [实战示例](#实战示例)
    - [聊天室](#聊天室)
  - [最佳实践](#最佳实践)
    - [1. 心跳保持连接](#1-心跳保持连接)
    - [2. 优雅关闭](#2-优雅关闭)
  - [参考资源](#参考资源)

---

## 概述

WebSocket 是一种在单个 TCP 连接上进行全双工通信的协议。

### 核心依赖

```toml
[dependencies]
# Axum WebSocket
axum = { version = "0.7", features = ["ws"] }

# Tokio-tungstenite
tokio-tungstenite = "0.21"
```

---

## Axum WebSocket

### 基础示例

```rust
use axum::{
    Router,
    routing::get,
    extract::ws::{WebSocket, WebSocketUpgrade, Message},
    response::IntoResponse,
};

async fn ws_handler(ws: WebSocketUpgrade) -> impl IntoResponse {
    ws.on_upgrade(handle_socket)
}

async fn handle_socket(mut socket: WebSocket) {
    while let Some(msg) = socket.recv().await {
        if let Ok(msg) = msg {
            match msg {
                Message::Text(text) => {
                    println!("收到: {}", text);
                    
                    // 回显消息
                    if socket
                        .send(Message::Text(format!("回显: {}", text)))
                        .await
                        .is_err()
                    {
                        break;
                    }
                }
                Message::Close(_) => break,
                _ => {}
            }
        }
    }
}

#[tokio::main]
async fn main() {
    let app = Router::new().route("/ws", get(ws_handler));
    
    println!("WebSocket 服务器运行在 ws://127.0.0.1:3000/ws");
    axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

### 广播消息

```rust
use axum::extract::ws::{WebSocket, WebSocketUpgrade, Message};
use std::sync::Arc;
use tokio::sync::broadcast;

type Tx = broadcast::Sender<String>;

async fn ws_handler(
    ws: WebSocketUpgrade,
    tx: Arc<Tx>,
) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_socket(socket, tx))
}

async fn handle_socket(socket: WebSocket, tx: Arc<Tx>) {
    let (mut sender, mut receiver) = socket.split();
    let mut rx = tx.subscribe();
    
    // 接收广播消息并发送给客户端
    let mut send_task = tokio::spawn(async move {
        while let Ok(msg) = rx.recv().await {
            if sender.send(Message::Text(msg)).await.is_err() {
                break;
            }
        }
    });
    
    // 接收客户端消息并广播
    let mut recv_task = tokio::spawn(async move {
        while let Some(Ok(Message::Text(text))) = receiver.next().await {
            let _ = tx.send(text);
        }
    });
    
    tokio::select! {
        _ = (&mut send_task) => recv_task.abort(),
        _ = (&mut recv_task) => send_task.abort(),
    };
}

#[tokio::main]
async fn main() {
    let (tx, _rx) = broadcast::channel::<String>(100);
    let tx = Arc::new(tx);
    
    let app = Router::new()
        .route("/ws", get(move |ws| ws_handler(ws, tx.clone())));
    
    println!("广播服务器运行中...");
}
```

---

## Tokio-tungstenite

### WebSocket 客户端

```rust
use tokio_tungstenite::{connect_async, tungstenite::Message};
use futures_util::{SinkExt, StreamExt};

#[tokio::main]
async fn main() {
    let (ws_stream, _) = connect_async("ws://127.0.0.1:3000/ws")
        .await
        .expect("连接失败");
    
    let (mut write, mut read) = ws_stream.split();
    
    // 发送消息
    write.send(Message::Text("Hello!".to_string())).await.unwrap();
    
    // 接收消息
    while let Some(msg) = read.next().await {
        let msg = msg.unwrap();
        if let Message::Text(text) = msg {
            println!("收到: {}", text);
            break;
        }
    }
}
```

---

## 实战示例

### 聊天室

```rust
use axum::{
    Router,
    routing::get,
    extract::{ws::{WebSocket, WebSocketUpgrade, Message}, State},
    response::IntoResponse,
};
use std::sync::Arc;
use tokio::sync::broadcast;

#[derive(Clone)]
struct AppState {
    tx: broadcast::Sender<String>,
}

async fn chat_handler(
    ws: WebSocketUpgrade,
    State(state): State<AppState>,
) -> impl IntoResponse {
    ws.on_upgrade(|socket| chat_socket(socket, state))
}

async fn chat_socket(socket: WebSocket, state: AppState) {
    let (mut sender, mut receiver) = socket.split();
    let mut rx = state.tx.subscribe();
    
    // 发送任务
    let mut send_task = tokio::spawn(async move {
        while let Ok(msg) = rx.recv().await {
            if sender.send(Message::Text(msg)).await.is_err() {
                break;
            }
        }
    });
    
    // 接收任务
    let tx = state.tx.clone();
    let mut recv_task = tokio::spawn(async move {
        while let Some(Ok(Message::Text(text))) = receiver.next().await {
            let _ = tx.send(text);
        }
    });
    
    tokio::select! {
        _ = (&mut send_task) => recv_task.abort(),
        _ = (&mut recv_task) => send_task.abort(),
    };
}

#[tokio::main]
async fn main() {
    let (tx, _) = broadcast::channel::<String>(100);
    let app_state = AppState { tx };
    
    let app = Router::new()
        .route("/chat", get(chat_handler))
        .with_state(app_state);
    
    println!("聊天服务器运行在 ws://127.0.0.1:3000/chat");
}
```

---

## 最佳实践

### 1. 心跳保持连接

```rust
async fn heartbeat(socket: &mut WebSocket) {
    let mut interval = tokio::time::interval(tokio::time::Duration::from_secs(30));
    
    loop {
        interval.tick().await;
        if socket.send(Message::Ping(vec![])).await.is_err() {
            break;
        }
    }
}
```

### 2. 优雅关闭

```rust
async fn graceful_close(mut socket: WebSocket) {
    socket.send(Message::Close(None)).await.ok();
    socket.close().await.ok();
}
```

---

## 参考资源

- [Axum WebSocket 示例](https://github.com/tokio-rs/axum/tree/main/examples/websockets)
- [tokio-tungstenite 文档](https://docs.rs/tokio-tungstenite/)
