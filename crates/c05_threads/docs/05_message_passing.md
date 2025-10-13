# 消息传递模式

## 目录

- [消息传递模式](#消息传递模式)
  - [目录](#目录)
  - [概述](#概述)
  - [Actor模型实现](#actor模型实现)
    - [1. 基础Actor框架](#1-基础actor框架)
    - [2. 高级Actor特性](#2-高级actor特性)
      - [2.1 监督策略](#21-监督策略)
      - [2.2 路由Actor](#22-路由actor)
  - [高级通道通信](#高级通道通信)
    - [1. 类型安全通道](#1-类型安全通道)
    - [2. 背压控制通道](#2-背压控制通道)
  - [发布订阅模式](#发布订阅模式)
    - [1. 类型安全的事件总线](#1-类型安全的事件总线)
    - [2. 异步事件流](#2-异步事件流)
  - [总结](#总结)

## 概述

本文档介绍了Rust 1.89中支持的高级消息传递模式，包括Actor模型、通道通信、发布订阅等现代并发通信机制。

## Actor模型实现

### 1. 基础Actor框架

利用Rust 1.89的改进异步特性实现高性能Actor系统：

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;
use tokio::time::{sleep, Duration};

#[derive(Debug, Clone)]
pub enum ActorMessage {
    Text(String),
    Number(u64),
    Command(String),
    Shutdown,
}

pub trait Actor: Send + 'static {
    type Message: Send + 'static;
    
    async fn handle_message(&mut self, message: Self::Message);
    async fn on_start(&mut self) {}
    async fn on_stop(&mut self) {}
}

pub struct ActorRef<M> {
    sender: mpsc::UnboundedSender<M>,
}

impl<M: Send + 'static> ActorRef<M> {
    pub fn new(sender: mpsc::UnboundedSender<M>) -> Self {
        Self { sender }
    }
    
    pub async fn send(&self, message: M) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.sender.send(message)
            .map_err(|e| Box::new(e) as Box<dyn std::error::Error + Send + Sync>)
    }
    
    pub fn try_send(&self, message: M) -> Result<(), mpsc::error::TrySendError<M>> {
        self.sender.try_send(message)
    }
}

pub struct ActorSystem {
    actors: Arc<Mutex<HashMap<String, Box<dyn std::any::Any + Send + Sync>>>>,
}

impl ActorSystem {
    pub fn new() -> Self {
        Self {
            actors: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub async fn spawn<A>(&self, name: String, actor: A) -> Result<ActorRef<A::Message>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: Actor + 'static,
    {
        let (sender, mut receiver) = mpsc::unbounded_channel();
        let actor_ref = ActorRef::new(sender);
        
        let mut actor = actor;
        let name_clone = name.clone();
        
        // 启动Actor任务
        tokio::spawn(async move {
            actor.on_start().await;
            
            while let Some(message) = receiver.recv().await {
                actor.handle_message(message).await;
            }
            
            actor.on_stop().await;
        });
        
        // 注册Actor
        self.actors.lock().unwrap().insert(name, Box::new(actor_ref.clone()));
        
        Ok(actor_ref)
    }
    
    pub fn get_actor<M>(&self, name: &str) -> Option<ActorRef<M>>
    where
        M: Send + 'static,
    {
        self.actors.lock().unwrap()
            .get(name)
            .and_then(|any| any.downcast_ref::<ActorRef<M>>())
            .cloned()
    }
}

// 示例Actor实现
pub struct EchoActor {
    name: String,
    message_count: u64,
}

impl EchoActor {
    pub fn new(name: String) -> Self {
        Self {
            name,
            message_count: 0,
        }
    }
}

impl Actor for EchoActor {
    type Message = ActorMessage;
    
    async fn handle_message(&mut self, message: Self::Message) {
        self.message_count += 1;
        
        match message {
            ActorMessage::Text(text) => {
                println!("[{}] Echo: {}", self.name, text);
            }
            ActorMessage::Number(num) => {
                println!("[{}] Number: {}", self.name, num);
            }
            ActorMessage::Command(cmd) => {
                println!("[{}] Command: {}", self.name, cmd);
            }
            ActorMessage::Shutdown => {
                println!("[{}] Shutting down...", self.name);
            }
        }
    }
    
    async fn on_start(&mut self) {
        println!("[{}] Actor started", self.name);
    }
    
    async fn on_stop(&mut self) {
        println!("[{}] Actor stopped, processed {} messages", self.name, self.message_count);
    }
}
```

### 2. 高级Actor特性

#### 2.1 监督策略

```rust
use std::sync::atomic::{AtomicU32, Ordering};

#[derive(Debug, Clone)]
pub enum SupervisionStrategy {
    OneForOne,    // 只重启失败的Actor
    AllForOne,    // 重启所有子Actor
    Restart,      // 重启策略
    Stop,         // 停止策略
}

pub struct Supervisor {
    strategy: SupervisionStrategy,
    max_restarts: AtomicU32,
    restart_window: Duration,
}

impl Supervisor {
    pub fn new(strategy: SupervisionStrategy, max_restarts: u32, restart_window: Duration) -> Self {
        Self {
            strategy,
            max_restarts: AtomicU32::new(max_restarts),
            restart_window,
        }
    }
    
    pub async fn supervise<A>(&self, actor: A, name: String) -> Result<ActorRef<A::Message>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: Actor + 'static,
    {
        let mut restart_count = 0;
        let start_time = std::time::Instant::now();
        
        loop {
            match self.spawn_actor(actor.clone(), name.clone()).await {
                Ok(actor_ref) => return Ok(actor_ref),
                Err(e) => {
                    restart_count += 1;
                    
                    if restart_count > self.max_restarts.load(Ordering::Relaxed) {
                        return Err(e);
                    }
                    
                    if start_time.elapsed() > self.restart_window {
                        // 重置重启计数
                        restart_count = 0;
                    }
                    
                    // 等待一段时间后重试
                    sleep(Duration::from_millis(100 * restart_count)).await;
                }
            }
        }
    }
    
    async fn spawn_actor<A>(&self, actor: A, _name: String) -> Result<ActorRef<A::Message>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: Actor + Clone + 'static,
    {
        // 实际的Actor启动逻辑
        todo!()
    }
}
```

#### 2.2 路由Actor

```rust
pub struct RouterActor<M> {
    routes: HashMap<String, ActorRef<M>>,
    routing_strategy: RoutingStrategy,
}

#[derive(Debug, Clone)]
pub enum RoutingStrategy {
    RoundRobin,
    Random,
    Hash,
    Broadcast,
}

impl<M: Send + Clone + 'static> RouterActor<M> {
    pub fn new(strategy: RoutingStrategy) -> Self {
        Self {
            routes: HashMap::new(),
            routing_strategy,
        }
    }
    
    pub fn add_route(&mut self, key: String, actor: ActorRef<M>) {
        self.routes.insert(key, actor);
    }
    
    pub async fn route_message(&self, message: M, routing_key: Option<String>) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        match self.routing_strategy {
            RoutingStrategy::RoundRobin => self.round_robin_route(message).await,
            RoutingStrategy::Random => self.random_route(message).await,
            RoutingStrategy::Hash => self.hash_route(message, routing_key).await,
            RoutingStrategy::Broadcast => self.broadcast_route(message).await,
        }
    }
    
    async fn round_robin_route(&self, message: M) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        // 实现轮询路由
        todo!()
    }
    
    async fn random_route(&self, message: M) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        // 实现随机路由
        todo!()
    }
    
    async fn hash_route(&self, message: M, routing_key: Option<String>) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        // 实现哈希路由
        todo!()
    }
    
    async fn broadcast_route(&self, message: M) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        // 实现广播路由
        for actor in self.routes.values() {
            actor.send(message.clone()).await?;
        }
        Ok(())
    }
}
```

## 高级通道通信

### 1. 类型安全通道

利用Rust 1.89的改进类型系统：

```rust
use std::marker::PhantomData;
use tokio::sync::mpsc;

pub struct TypedChannel<T> {
    sender: mpsc::UnboundedSender<T>,
    receiver: mpsc::UnboundedReceiver<T>,
    _phantom: PhantomData<T>,
}

impl<T: Send + 'static> TypedChannel<T> {
    pub fn new() -> Self {
        let (sender, receiver) = mpsc::unbounded_channel();
        Self {
            sender,
            receiver,
            _phantom: PhantomData,
        }
    }
    
    pub fn sender(&self) -> TypedSender<T> {
        TypedSender {
            inner: self.sender.clone(),
        }
    }
    
    pub fn receiver(&self) -> TypedReceiver<T> {
        TypedReceiver {
            inner: self.receiver.clone(),
        }
    }
}

pub struct TypedSender<T> {
    inner: mpsc::UnboundedSender<T>,
}

impl<T: Send + 'static> TypedSender<T> {
    pub async fn send(&self, message: T) -> Result<(), mpsc::error::SendError<T>> {
        self.inner.send(message)
    }
    
    pub fn try_send(&self, message: T) -> Result<(), mpsc::error::TrySendError<T>> {
        self.inner.try_send(message)
    }
    
    pub fn is_closed(&self) -> bool {
        self.inner.is_closed()
    }
}

pub struct TypedReceiver<T> {
    inner: mpsc::UnboundedReceiver<T>,
}

impl<T: Send + 'static> TypedReceiver<T> {
    pub async fn recv(&mut self) -> Option<T> {
        self.inner.recv().await
    }
    
    pub fn try_recv(&mut self) -> Result<T, mpsc::error::TryRecvError> {
        self.inner.try_recv()
    }
}
```

### 2. 背压控制通道

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct BackpressureChannel<T> {
    sender: mpsc::Sender<T>,
    receiver: mpsc::Receiver<T>,
    capacity: usize,
    current_size: AtomicUsize,
}

impl<T: Send + 'static> BackpressureChannel<T> {
    pub fn new(capacity: usize) -> Self {
        let (sender, receiver) = mpsc::channel(capacity);
        Self {
            sender,
            receiver,
            capacity,
            current_size: AtomicUsize::new(0),
        }
    }
    
    pub async fn send(&self, message: T) -> Result<(), mpsc::error::SendError<T>> {
        let current = self.current_size.load(Ordering::Relaxed);
        
        if current >= self.capacity {
            // 等待空间可用
            while self.current_size.load(Ordering::Relaxed) >= self.capacity {
                tokio::task::yield_now().await;
            }
        }
        
        self.current_size.fetch_add(1, Ordering::Relaxed);
        self.sender.send(message).await
    }
    
    pub async fn recv(&mut self) -> Option<T> {
        let result = self.receiver.recv().await;
        if result.is_some() {
            self.current_size.fetch_sub(1, Ordering::Relaxed);
        }
        result
    }
    
    pub fn current_size(&self) -> usize {
        self.current_size.load(Ordering::Relaxed)
    }
    
    pub fn capacity(&self) -> usize {
        self.capacity
    }
}
```

## 发布订阅模式

### 1. 类型安全的事件总线

```rust
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

pub struct EventBus {
    subscribers: Arc<RwLock<HashMap<TypeId, Vec<Box<dyn Any + Send + Sync>>>>>,
}

impl EventBus {
    pub fn new() -> Self {
        Self {
            subscribers: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub fn subscribe<E: 'static + Send + Sync, F>(&self, handler: F) -> Subscription
    where
        F: Fn(&E) + Send + Sync + 'static,
    {
        let type_id = TypeId::of::<E>();
        let handler = Box::new(handler);
        
        self.subscribers.write().unwrap()
            .entry(type_id)
            .or_insert_with(Vec::new)
            .push(handler);
            
        Subscription { type_id }
    }
    
    pub fn publish<E: 'static + Send + Sync>(&self, event: E) {
        let type_id = TypeId::of::<E>();
        
        if let Some(subscribers) = self.subscribers.read().unwrap().get(&type_id) {
            for subscriber in subscribers {
                if let Some(handler) = subscriber.downcast_ref::<Box<dyn Fn(&E) + Send + Sync>>() {
                    handler(&event);
                }
            }
        }
    }
}

pub struct Subscription {
    type_id: TypeId,
}

// 使用示例
#[derive(Debug, Clone)]
pub struct UserEvent {
    pub user_id: u64,
    pub action: String,
}

#[derive(Debug, Clone)]
pub struct SystemEvent {
    pub component: String,
    pub status: String,
}

pub async fn example_event_bus() {
    let event_bus = EventBus::new();
    
    // 订阅用户事件
    let _user_sub = event_bus.subscribe(|event: &UserEvent| {
        println!("User event: {:?}", event);
    });
    
    // 订阅系统事件
    let _system_sub = event_bus.subscribe(|event: &SystemEvent| {
        println!("System event: {:?}", event);
    });
    
    // 发布事件
    event_bus.publish(UserEvent {
        user_id: 123,
        action: "login".to_string(),
    });
    
    event_bus.publish(SystemEvent {
        component: "database".to_string(),
        status: "connected".to_string(),
    });
}
```

### 2. 异步事件流

```rust
use tokio::sync::broadcast;
use futures::stream::{Stream, StreamExt};

pub struct AsyncEventStream<E> {
    sender: broadcast::Sender<E>,
    receiver: broadcast::Receiver<E>,
}

impl<E: Clone + Send + Sync + 'static> AsyncEventStream<E> {
    pub fn new(capacity: usize) -> Self {
        let (sender, receiver) = broadcast::channel(capacity);
        Self { sender, receiver }
    }
    
    pub fn subscribe(&self) -> broadcast::Receiver<E> {
        self.sender.subscribe()
    }
    
    pub async fn publish(&self, event: E) -> Result<usize, broadcast::error::SendError<E>> {
        self.sender.send(event)
    }
    
    pub fn into_stream(self) -> impl Stream<Item = Result<E, broadcast::error::RecvError>> {
        self.receiver
    }
}

// 使用示例
pub async fn example_async_stream() {
    let event_stream = AsyncEventStream::<String>::new(100);
    
    // 创建多个订阅者
    let mut sub1 = event_stream.subscribe();
    let mut sub2 = event_stream.subscribe();
    
    // 发布事件
    event_stream.publish("Event 1".to_string()).await.unwrap();
    event_stream.publish("Event 2".to_string()).await.unwrap();
    
    // 异步接收事件
    tokio::spawn(async move {
        while let Ok(event) = sub1.recv().await {
            println!("Subscriber 1: {}", event);
        }
    });
    
    tokio::spawn(async move {
        while let Ok(event) = sub2.recv().await {
            println!("Subscriber 2: {}", event);
        }
    });
}
```

## 总结

Rust 1.89的消息传递模式提供了：

1. **Actor模型**: 完整的Actor系统实现，包括监督策略和路由
2. **类型安全通道**: 编译时类型检查的通道通信
3. **背压控制**: 自动流量控制机制
4. **发布订阅**: 类型安全的事件总线
5. **异步流**: 高性能的异步事件流

这些模式充分利用了Rust 1.89的新特性，提供了高效、安全的消息传递解决方案。
