# Actor 模型基础（Actor System Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [Actor 模型基础（Actor System Basics）](#actor-模型基础actor-system-basics)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [Actor 基础](#actor-基础)
    - [简单的 Actor 实现](#简单的-actor-实现)
  - [消息传递](#消息传递)
    - [异步消息传递](#异步消息传递)
  - [Actor 生命周期](#actor-生命周期)
    - [生命周期管理](#生命周期管理)
  - [实践示例](#实践示例)
    - [示例 1：聊天室 Actor 系统](#示例-1聊天室-actor-系统)
    - [示例 2：工作池 Actor](#示例-2工作池-actor)
  - [最佳实践](#最佳实践)
    - [1. 错误处理](#1-错误处理)
    - [2. 超时处理](#2-超时处理)
  - [参考资料](#参考资料)

---

## 概述

Actor 模型是一种并发计算模型，其中 Actor 是并发计算的基本单元。每个 Actor 通过消息传递进行通信，具有独立的状态和行为。

## Actor 基础

### 简单的 Actor 实现

```rust
use tokio::sync::mpsc;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum Message {
    Get { key: String, reply_to: mpsc::Sender<Option<String>> },
    Set { key: String, value: String },
    Delete { key: String },
}

pub struct KeyValueActor {
    receiver: mpsc::Receiver<Message>,
    data: HashMap<String, String>,
}

impl KeyValueActor {
    pub fn new(receiver: mpsc::Receiver<Message>) -> Self {
        KeyValueActor {
            receiver,
            data: HashMap::new(),
        }
    }

    pub async fn run(mut self) {
        while let Some(msg) = self.receiver.recv().await {
            self.handle_message(msg).await;
        }
    }

    async fn handle_message(&mut self, msg: Message) {
        match msg {
            Message::Get { key, reply_to } => {
                let value = self.data.get(&key).cloned();
                let _ = reply_to.send(value).await;
            }
            Message::Set { key, value } => {
                self.data.insert(key, value);
            }
            Message::Delete { key } => {
                self.data.remove(&key);
            }
        }
    }
}

pub struct ActorRef {
    sender: mpsc::Sender<Message>,
}

impl ActorRef {
    pub fn new(sender: mpsc::Sender<Message>) -> Self {
        ActorRef { sender }
    }

    pub async fn get(&self, key: String) -> Option<String> {
        let (tx, mut rx) = mpsc::channel(1);
        self.sender.send(Message::Get { key, reply_to: tx }).await.unwrap();
        rx.recv().await.unwrap()
    }

    pub async fn set(&self, key: String, value: String) {
        self.sender.send(Message::Set { key, value }).await.unwrap();
    }

    pub async fn delete(&self, key: String) {
        self.sender.send(Message::Delete { key }).await.unwrap();
    }
}

#[tokio::main]
async fn main() {
    let (tx, rx) = mpsc::channel(100);
    let actor_ref = ActorRef::new(tx);

    let actor = KeyValueActor::new(rx);
    tokio::spawn(actor.run());

    // 使用 Actor
    actor_ref.set("key1".to_string(), "value1".to_string()).await;
    let value = actor_ref.get("key1".to_string()).await;
    println!("值: {:?}", value);
}
```

## 消息传递

### 异步消息传递

```rust
use tokio::sync::mpsc;

#[derive(Debug, Clone)]
pub enum ActorMessage {
    Ping { reply_to: mpsc::Sender<String> },
    Pong { reply_to: mpsc::Sender<String> },
}

pub struct PingPongActor {
    receiver: mpsc::Receiver<ActorMessage>,
    name: String,
}

impl PingPongActor {
    pub fn new(receiver: mpsc::Receiver<ActorMessage>, name: String) -> Self {
        PingPongActor { receiver, name }
    }

    pub async fn run(mut self) {
        while let Some(msg) = self.receiver.recv().await {
            match msg {
                ActorMessage::Ping { reply_to } => {
                    println!("{} 收到 Ping", self.name);
                    reply_to.send("Pong".to_string()).await.unwrap();
                }
                ActorMessage::Pong { reply_to } => {
                    println!("{} 收到 Pong", self.name);
                    reply_to.send("Ping".to_string()).await.unwrap();
                }
            }
        }
    }
}
```

## Actor 生命周期

### 生命周期管理

```rust
use tokio::sync::mpsc;

#[derive(Debug, Clone)]
pub enum LifecycleMessage {
    Start,
    Stop,
    Restart,
    Status { reply_to: mpsc::Sender<String> },
}

pub struct ManagedActor {
    receiver: mpsc::Receiver<LifecycleMessage>,
    state: ActorState,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ActorState {
    Stopped,
    Running,
    Restarting,
}

impl ManagedActor {
    pub fn new(receiver: mpsc::Receiver<LifecycleMessage>) -> Self {
        ManagedActor {
            receiver,
            state: ActorState::Stopped,
        }
    }

    pub async fn run(mut self) {
        while let Some(msg) = self.receiver.recv().await {
            match msg {
                LifecycleMessage::Start => {
                    if self.state == ActorState::Stopped {
                        self.state = ActorState::Running;
                        println!("Actor 启动");
                    }
                }
                LifecycleMessage::Stop => {
                    if self.state == ActorState::Running {
                        self.state = ActorState::Stopped;
                        println!("Actor 停止");
                    }
                }
                LifecycleMessage::Restart => {
                    self.state = ActorState::Restarting;
                    println!("Actor 重启中");
                    self.state = ActorState::Running;
                    println!("Actor 重启完成");
                }
                LifecycleMessage::Status { reply_to } => {
                    let status = format!("状态: {:?}", self.state);
                    reply_to.send(status).await.unwrap();
                }
            }
        }
    }
}
```

## 实践示例

### 示例 1：聊天室 Actor 系统

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum ChatMessage {
    Join { user_id: u32, name: String },
    Leave { user_id: u32 },
    SendMessage { user_id: u32, message: String },
    GetUsers { reply_to: mpsc::Sender<Vec<u32>> },
}

pub struct ChatRoomActor {
    receiver: mpsc::Receiver<ChatMessage>,
    users: HashMap<u32, String>,
}

impl ChatRoomActor {
    pub fn new(receiver: mpsc::Receiver<ChatMessage>) -> Self {
        ChatRoomActor {
            receiver,
            users: HashMap::new(),
        }
    }

    pub async fn run(mut self) {
        while let Some(msg) = self.receiver.recv().await {
            match msg {
                ChatMessage::Join { user_id, name } => {
                    self.users.insert(user_id, name.clone());
                    println!("用户 {} ({}) 加入聊天室", user_id, name);
                }
                ChatMessage::Leave { user_id } => {
                    if let Some(name) = self.users.remove(&user_id) {
                        println!("用户 {} ({}) 离开聊天室", user_id, name);
                    }
                }
                ChatMessage::SendMessage { user_id, message } => {
                    if let Some(name) = self.users.get(&user_id) {
                        println!("{} ({}): {}", name, user_id, message);
                    }
                }
                ChatMessage::GetUsers { reply_to } => {
                    let user_ids: Vec<u32> = self.users.keys().copied().collect();
                    reply_to.send(user_ids).await.unwrap();
                }
            }
        }
    }
}
```

### 示例 2：工作池 Actor

```rust
#[derive(Debug, Clone)]
pub enum WorkMessage {
    Task { id: u32, data: String, reply_to: mpsc::Sender<String> },
    Shutdown,
}

pub struct WorkerPool {
    workers: Vec<mpsc::Sender<WorkMessage>>,
    next_worker: usize,
}

impl WorkerPool {
    pub fn new(worker_count: usize) -> (Self, Vec<mpsc::Receiver<WorkMessage>>) {
        let mut senders = Vec::new();
        let mut receivers = Vec::new();

        for _ in 0..worker_count {
            let (tx, rx) = mpsc::channel(100);
            senders.push(tx);
            receivers.push(rx);
        }

        (WorkerPool {
            workers: senders,
            next_worker: 0,
        }, receivers)
    }

    pub async fn dispatch(&mut self, task: WorkMessage) -> Result<(), mpsc::error::SendError<WorkMessage>> {
        let worker = &self.workers[self.next_worker];
        self.next_worker = (self.next_worker + 1) % self.workers.len();
        worker.send(task).await
    }
}
```

## 最佳实践

### 1. 错误处理

```rust
#[derive(Debug, Clone)]
pub enum ResultMessage<T, E> {
    Success(T),
    Error(E),
}

// Actor 应该优雅地处理错误
async fn handle_with_error_handling(msg: Message) -> ResultMessage<String, String> {
    match process_message(msg).await {
        Ok(result) => ResultMessage::Success(result),
        Err(e) => ResultMessage::Error(e.to_string()),
    }
}
```

### 2. 超时处理

```rust
use tokio::time::{timeout, Duration};

pub async fn send_with_timeout(
    sender: &mpsc::Sender<Message>,
    msg: Message,
) -> Result<(), String> {
    timeout(Duration::from_secs(5), sender.send(msg))
        .await
        .map_err(|_| "发送超时".to_string())?
        .map_err(|e| format!("发送失败: {}", e))
}
```

## 参考资料

- [Actor 模型索引](./00_index.md)
- [编程范式索引](../00_index.md)
- [并发编程](../05_concurrent/00_index.md)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回编程范式: [`../00_index.md`](../00_index.md)
