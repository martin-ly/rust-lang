# 事件驱动架构（Event-Driven Architecture）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [事件驱动架构（Event-Driven Architecture）](#事件驱动架构event-driven-architecture)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [事件循环](#事件循环)
    - [基本事件循环](#基本事件循环)
  - [事件总线](#事件总线)
    - [发布-订阅模式](#发布-订阅模式)
  - [事件处理](#事件处理)
    - [事件处理器](#事件处理器)
  - [实践示例](#实践示例)
    - [示例 1：Web 应用事件系统](#示例-1web-应用事件系统)
    - [示例 2：游戏事件系统](#示例-2游戏事件系统)
  - [最佳实践](#最佳实践)
    - [1. 事件序列化](#1-事件序列化)
    - [2. 事件持久化](#2-事件持久化)
  - [参考资料](#参考资料)

---

## 概述

事件驱动架构（Event-Driven Architecture）是一种软件架构模式，其中系统组件通过事件进行通信。这种架构模式特别适合需要解耦和异步处理的系统。

## 事件循环

### 基本事件循环

```rust
use tokio::sync::mpsc;
use tokio::time::{sleep, Duration};

#[derive(Debug, Clone)]
enum Event {
    UserAction { action: String },
    SystemEvent { event: String },
    TimerEvent { id: u32 },
}

#[tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel::<Event>(100);

    // 事件生产者
    let producer = tokio::spawn(async move {
        for i in 1..=5 {
            tx.send(Event::UserAction {
                action: format!("动作 {}", i),
            }).await.unwrap();
            sleep(Duration::from_millis(100)).await;
        }
    });

    // 事件循环
    while let Some(event) = rx.recv().await {
        handle_event(event).await;
    }

    producer.await.unwrap();
}

async fn handle_event(event: Event) {
    match event {
        Event::UserAction { action } => {
            println!("处理用户动作: {}", action);
        }
        Event::SystemEvent { event } => {
            println!("处理系统事件: {}", event);
        }
        Event::TimerEvent { id } => {
            println!("处理定时器事件: {}", id);
        }
    }
}
```

## 事件总线

### 发布-订阅模式

```rust
use tokio::sync::broadcast;
use std::collections::HashMap;

pub struct EventBus {
    channels: HashMap<String, broadcast::Sender<Event>>,
}

#[derive(Debug, Clone)]
pub struct Event {
    pub topic: String,
    pub data: String,
}

impl EventBus {
    pub fn new() -> Self {
        EventBus {
            channels: HashMap::new(),
        }
    }

    pub fn subscribe(&mut self, topic: &str) -> broadcast::Receiver<Event> {
        let sender = self.channels
            .entry(topic.to_string())
            .or_insert_with(|| broadcast::channel(100).0)
            .clone();
        sender.subscribe()
    }

    pub async fn publish(&self, event: Event) -> Result<usize, broadcast::error::SendError<Event>> {
        if let Some(sender) = self.channels.get(&event.topic) {
            sender.send(event)
        } else {
            Ok(0)
        }
    }
}

#[tokio::main]
async fn main() {
    let mut bus = EventBus::new();

    // 订阅者
    let mut subscriber1 = bus.subscribe("user");
    let mut subscriber2 = bus.subscribe("user");

    tokio::spawn(async move {
        while let Ok(event) = subscriber1.recv().await {
            println!("订阅者 1 收到: {:?}", event);
        }
    });

    tokio::spawn(async move {
        while let Ok(event) = subscriber2.recv().await {
            println!("订阅者 2 收到: {:?}", event);
        }
    });

    // 发布事件
    bus.publish(Event {
        topic: "user".to_string(),
        data: "用户登录".to_string(),
    }).await.unwrap();

    sleep(Duration::from_secs(1)).await;
}
```

## 事件处理

### 事件处理器

```rust
use std::collections::HashMap;

pub trait EventHandler {
    fn handle(&self, event: &Event) -> Result<(), String>;
}

pub struct EventDispatcher {
    handlers: HashMap<String, Vec<Box<dyn EventHandler + Send + Sync>>>,
}

impl EventDispatcher {
    pub fn new() -> Self {
        EventDispatcher {
            handlers: HashMap::new(),
        }
    }

    pub fn register(&mut self, event_type: String, handler: Box<dyn EventHandler + Send + Sync>) {
        self.handlers
            .entry(event_type)
            .or_insert_with(Vec::new)
            .push(handler);
    }

    pub async fn dispatch(&self, event: Event) -> Result<(), String> {
        if let Some(handlers) = self.handlers.get(&event.topic) {
            for handler in handlers {
                handler.handle(&event)?;
            }
        }
        Ok(())
    }
}

struct UserEventHandler;

impl EventHandler for UserEventHandler {
    fn handle(&self, event: &Event) -> Result<(), String> {
        println!("用户事件处理器: {}", event.data);
        Ok(())
    }
}
```

## 实践示例

### 示例 1：Web 应用事件系统

```rust
use tokio::sync::mpsc;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WebEvent {
    RequestReceived { path: String, method: String },
    ResponseSent { status: u16, duration_ms: u64 },
    ErrorOccurred { error: String },
}

pub struct WebEventSystem {
    sender: mpsc::Sender<WebEvent>,
}

impl WebEventSystem {
    pub fn new() -> (Self, mpsc::Receiver<WebEvent>) {
        let (tx, rx) = mpsc::channel(1000);
        (WebEventSystem { sender: tx }, rx)
    }

    pub async fn emit(&self, event: WebEvent) -> Result<(), mpsc::error::SendError<WebEvent>> {
        self.sender.send(event).await
    }
}

#[tokio::main]
async fn main() {
    let (event_system, mut receiver) = WebEventSystem::new();

    // 事件处理器
    tokio::spawn(async move {
        while let Some(event) = receiver.recv().await {
            match event {
                WebEvent::RequestReceived { path, method } => {
                    println!("请求: {} {}", method, path);
                }
                WebEvent::ResponseSent { status, duration_ms } => {
                    println!("响应: {} ({}ms)", status, duration_ms);
                }
                WebEvent::ErrorOccurred { error } => {
                    eprintln!("错误: {}", error);
                }
            }
        }
    });

    // 模拟事件
    event_system.emit(WebEvent::RequestReceived {
        path: "/api/users".to_string(),
        method: "GET".to_string(),
    }).await.unwrap();

    sleep(Duration::from_secs(1)).await;
}
```

### 示例 2：游戏事件系统

```rust
#[derive(Debug, Clone)]
pub enum GameEvent {
    PlayerMove { player_id: u32, x: f64, y: f64 },
    PlayerAttack { attacker_id: u32, target_id: u32 },
    ItemCollected { player_id: u32, item_id: u32 },
    LevelComplete { player_id: u32, level: u32 },
}

pub struct GameEventManager {
    events: mpsc::Sender<GameEvent>,
}

impl GameEventManager {
    pub fn new() -> (Self, mpsc::Receiver<GameEvent>) {
        let (tx, rx) = mpsc::channel(1000);
        (GameEventManager { events: tx }, rx)
    }

    pub async fn emit(&self, event: GameEvent) -> Result<(), mpsc::error::SendError<GameEvent>> {
        self.events.send(event).await
    }
}
```

## 最佳实践

### 1. 事件序列化

```rust
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SerializableEvent {
    pub event_type: String,
    pub payload: serde_json::Value,
    pub timestamp: i64,
}

impl SerializableEvent {
    pub fn new(event_type: String, payload: serde_json::Value) -> Self {
        SerializableEvent {
            event_type,
            payload,
            timestamp: chrono::Utc::now().timestamp(),
        }
    }
}
```

### 2. 事件持久化

```rust
pub struct EventStore {
    events: Vec<SerializableEvent>,
}

impl EventStore {
    pub fn new() -> Self {
        EventStore {
            events: Vec::new(),
        }
    }

    pub fn append(&mut self, event: SerializableEvent) {
        self.events.push(event);
    }

    pub fn get_events(&self, event_type: &str) -> Vec<&SerializableEvent> {
        self.events
            .iter()
            .filter(|e| e.event_type == event_type)
            .collect()
    }
}
```

## 参考资料

- [事件驱动编程索引](./00_index.md)
- [编程范式索引](../00_index.md)
- [响应式编程](../07_reactive/00_index.md)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回编程范式: [`../00_index.md`](../00_index.md)
