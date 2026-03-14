# 异步编程使用指南

**模块**: C06 Async
**创建日期**: 2025-12-11
**最后更新**: 2026-02-15
**Rust 版本**: 1.94.0+ (Edition 2024)
**状态**: ✅ 已完成

---

## 📋 目录

- [异步编程使用指南](#异步编程使用指南)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🚀 快速开始](#-快速开始)
    - [基本异步函数](#基本异步函数)
    - [并发执行](#并发执行)
  - [📊 核心功能](#-核心功能)
    - [1. Future Trait](#1-future-trait)
    - [2. 异步运行时](#2-异步运行时)
      - [Tokio 运行时](#tokio-运行时)
      - [自定义运行时配置](#自定义运行时配置)
    - [3. 异步 I/O](#3-异步-io)
      - [文件 I/O](#文件-io)
      - [网络 I/O](#网络-io)
    - [4. Reactor 模式](#4-reactor-模式)
    - [5. Actor 模式](#5-actor-模式)
  - [⚡ 性能优化](#-性能优化)
    - [1. 使用 select! 宏](#1-使用-select-宏)
    - [2. 使用 Stream](#2-使用-stream)
    - [3. 背压处理](#3-背压处理)
  - [🔧 错误处理](#-错误处理)
    - [异步错误传播](#异步错误传播)
    - [错误恢复](#错误恢复)
  - [🏗️ 异步编程模式（5+ 完整示例）](#️-异步编程模式5-完整示例)
    - [模式 1: 取消与超时处理](#模式-1-取消与超时处理)
    - [模式 2: 限流与速率控制](#模式-2-限流与速率控制)
    - [模式 3: 重试与退避策略](#模式-3-重试与退避策略)
    - [模式 4: 批处理与缓冲](#模式-4-批处理与缓冲)
    - [模式 5: 断路器模式](#模式-5-断路器模式)
  - [🌍 真实应用场景](#-真实应用场景)
    - [场景 1: Web 服务器实现](#场景-1-web-服务器实现)
    - [场景 2: 数据处理管道](#场景-2-数据处理管道)
    - [场景 3: 实时消息系统](#场景-3-实时消息系统)
  - [🐛 常见问题与解决方案](#-常见问题与解决方案)
    - [问题 1: 阻塞运行时](#问题-1-阻塞运行时)
    - [问题 2: Future 必须 Send](#问题-2-future-必须-send)
    - [问题 3: 持有锁跨越 await 点](#问题-3-持有锁跨越-await-点)
    - [问题 4: 忘记处理 Cancel Safety](#问题-4-忘记处理-cancel-safety)
    - [问题 5: 递归 async 函数](#问题-5-递归-async-函数)
  - [📚 相关文档](#-相关文档)
  - [🆕 Rust 1.94 特性](#-rust-194-特性)
    - [ControlFlow 在异步编程中的应用](#controlflow-在异步编程中的应用)
    - [Peekable 迭代器增强](#peekable-迭代器增强)
  - [🔗 形式化引用](#-形式化引用)

---

## 📋 概述

本指南介绍如何使用 C06 异步编程模块的功能，包括 async/await、Future、异步运行时、Reactor 模式、Actor 模式等。

**形式化引用**：T-ASYNC1 (Future 安全性)、
[async_state_machine](../research_notes/formal_methods/async_state_machine.md) T6.1-T6.3、
[pin_self_referential](../research_notes/formal_methods/pin_self_referential.md) T-PIN1。
详见 [THEOREM_RUST_EXAMPLE_MAPPING](../research_notes/THEOREM_RUST_EXAMPLE_MAPPING.md)。

---

## 🚀 快速开始

### 基本异步函数

```rust
use tokio::time::{sleep, Duration};

async fn fetch_data() -> String {
    sleep(Duration::from_secs(1)).await;
    "数据".to_string()
}

#[tokio::main]
async fn main() {
    let result = fetch_data().await;
    println!("结果: {}", result);
}
```

### 并发执行

```rust
use tokio::time::{sleep, Duration, Instant};

async fn task1() -> &'static str {
    sleep(Duration::from_secs(1)).await;
    "任务1完成"
}

async fn task2() -> &'static str {
    sleep(Duration::from_secs(1)).await;
    "任务2完成"
}

#[tokio::main]
async fn main() {
    let start = Instant::now();

    // 并发执行
    let (result1, result2) = tokio::join!(task1(), task2());

    println!("{}: {:?}", result1, start.elapsed());
    println!("{}: {:?}", result2, start.elapsed());
    // 总耗时约 1 秒（并发执行）
}
```

---

## 📊 核心功能

### 1. Future Trait

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct MyFuture {
    value: i32,
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(self.value)
    }
}

#[tokio::main]
async fn main() {
    let future = MyFuture { value: 42 };
    let result = future.await;
    println!("结果: {}", result);
}
```

### 2. 异步运行时

#### Tokio 运行时

```rust
use tokio::runtime::Runtime;

let rt = Runtime::new().unwrap();

rt.block_on(async {
    println!("在 Tokio 运行时中执行");
});
```

#### 自定义运行时配置

```rust
use tokio::runtime::Builder;

let rt = Builder::new_multi_thread()
    .worker_threads(4)
    .max_blocking_threads(512)
    .enable_all()
    .build()
    .unwrap();
```

### 3. 异步 I/O

#### 文件 I/O

```rust
use tokio::fs;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 异步读取文件
    let contents = fs::read_to_string("file.txt").await?;
    println!("文件内容: {}", contents);

    // 异步写入文件
    fs::write("output.txt", "Hello, World!").await?;

    Ok(())
}
```

#### 网络 I/O

```rust
use tokio::net::TcpListener;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;

    loop {
        let (mut socket, _) = listener.accept().await?;

        tokio::spawn(async move {
            let mut buf = [0; 1024];
            match socket.read(&mut buf).await {
                Ok(n) => {
                    if n == 0 {
                        return;
                    }
                    socket.write_all(&buf[0..n]).await.unwrap();
                }
                Err(e) => eprintln!("错误: {}", e),
            }
        });
    }
}
```

### 4. Reactor 模式

```rust
use c06_async::reactor::Reactor;

let mut reactor = Reactor::new();

// 注册事件处理器
reactor.register_handler(EventType::Read, |event| {
    println!("处理读事件: {:?}", event);
});

// 运行事件循环
reactor.run().await;
```

### 5. Actor 模式

```rust
use c06_async::actor::{Actor, ActorRef, Message};

struct MyActor {
    count: i32,
}

impl Actor for MyActor {
    type Message = i32;

    async fn handle(&mut self, msg: Self::Message) {
        self.count += msg;
        println!("计数: {}", self.count);
    }
}

#[tokio::main]
async fn main() {
    let actor_ref = ActorRef::spawn(MyActor { count: 0 }).await;

    actor_ref.send(1).await;
    actor_ref.send(2).await;
    actor_ref.send(3).await;
}
```

---

## ⚡ 性能优化

### 1. 使用 select! 宏

```rust
use tokio::time::{sleep, Duration, timeout};

#[tokio::main]
async fn main() {
    tokio::select! {
        result = async_task1() => {
            println!("任务1完成: {:?}", result);
        }
        result = async_task2() => {
            println!("任务2完成: {:?}", result);
        }
        _ = sleep(Duration::from_secs(5)) => {
            println!("超时");
        }
    }
}
```

### 2. 使用 Stream

```rust
use tokio_stream::{self as stream, StreamExt};

#[tokio::main]
async fn main() {
    let mut stream = stream::iter(1..=10);

    while let Some(value) = stream.next().await {
        println!("值: {}", value);
    }
}
```

### 3. 背压处理

```rust
use tokio::sync::mpsc;

let (tx, mut rx) = mpsc::channel(100); // 有界通道

tokio::spawn(async move {
    for i in 0..1000 {
        // 如果通道满了，会等待
        tx.send(i).await.unwrap();
    }
});

while let Some(value) = rx.recv().await {
    println!("接收: {}", value);
}
```

---

## 🔧 错误处理

### 异步错误传播

```rust
use std::error::Error;

async fn fetch_data() -> Result<String, Box<dyn Error>> {
    // 使用 ? 操作符传播错误
    let response = reqwest::get("https://api.example.com").await?;
    let text = response.text().await?;
    Ok(text)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let data = fetch_data().await?;
    println!("数据: {}", data);
    Ok(())
}
```

### 错误恢复

```rust
use tokio::time::{sleep, Duration};

async fn retry_operation<F, Fut, T, E>(mut f: F, max_retries: u32) -> Result<T, E>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T, E>>,
{
    for attempt in 1..=max_retries {
        match f().await {
            Ok(value) => return Ok(value),
            Err(e) => {
                if attempt < max_retries {
                    sleep(Duration::from_secs(1)).await;
                    continue;
                }
                return Err(e);
            }
        }
    }
    unreachable!()
}
```

---

## 🏗️ 异步编程模式（5+ 完整示例）

### 模式 1: 取消与超时处理

```rust
use tokio::time::{timeout, Duration};
use tokio::sync::CancellationToken;

async fn cancellable_task(token: CancellationToken) -> Result<String, &'static str> {
    tokio::select! {
        result = perform_work() => Ok(result),
        _ = token.cancelled() => Err("任务被取消"),
    }
}

async fn with_timeout() -> Result<String, &'static str> {
    match timeout(Duration::from_secs(5), fetch_data()).await {
        Ok(result) => result.map_err(|_| "获取数据失败"),
        Err(_) => Err("操作超时"),
    }
}
```

### 模式 2: 限流与速率控制

```rust
use tokio::time::{interval, Instant};
use std::sync::Arc;
use tokio::sync::Semaphore;

struct RateLimiter {
    semaphore: Arc<Semaphore>,
}

impl RateLimiter {
    fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
        }
    }

    async fn execute<F, Fut, T>(&self, f: F) -> T
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        let permit = self.semaphore.acquire().await.unwrap();
        let result = f().await;
        drop(permit);
        result
    }
}

// Token Bucket 限流器
struct TokenBucket {
    tokens: std::sync::atomic::AtomicU32,
    rate: u32,
}

impl TokenBucket {
    async fn acquire(&self) {
        loop {
            let current = self.tokens.load(std::sync::atomic::Ordering::Relaxed);
            if current > 0 {
                if self.tokens.compare_exchange(
                    current,
                    current - 1,
                    std::sync::atomic::Ordering::Relaxed,
                    std::sync::atomic::Ordering::Relaxed,
                ).is_ok() {
                    break;
                }
            }
            tokio::task::yield_now().await;
        }
    }
}
```

### 模式 3: 重试与退避策略

```rust
use tokio::time::{sleep, Duration};
use rand::Rng;

enum BackoffStrategy {
    Fixed(Duration),
    Exponential { initial: Duration, max: Duration, factor: u32 },
    Jitter { base: Duration, max_jitter: Duration },
}

async fn retry_with_backoff<F, Fut, T, E>(
    mut operation: F,
    max_attempts: u32,
    strategy: BackoffStrategy,
) -> Result<T, E>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T, E>>,
{
    let mut attempt = 1;

    loop {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) if attempt >= max_attempts => return Err(e),
            Err(_) => {
                let delay = match &strategy {
                    BackoffStrategy::Fixed(d) => *d,
                    BackoffStrategy::Exponential { initial, max, factor } => {
                        let exp = initial.saturating_mul(factor.saturating_pow(attempt - 1));
                        std::cmp::min(exp, *max)
                    }
                    BackoffStrategy::Jitter { base, max_jitter } => {
                        let jitter = rand::thread_rng().gen_range(Duration::ZERO..=*max_jitter);
                        *base + jitter
                    }
                };
                sleep(delay).await;
                attempt += 1;
            }
        }
    }
}
```

### 模式 4: 批处理与缓冲

```rust
use tokio::sync::mpsc;
use tokio::time::{interval, Duration};

struct BatchProcessor<T> {
    sender: mpsc::Sender<T>,
}

impl<T: Send + 'static> BatchProcessor<T> {
    fn new<F, Fut>(
        batch_size: usize,
        timeout: Duration,
        mut processor: F,
    ) -> Self
    where
        F: FnMut(Vec<T>) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = ()> + Send,
    {
        let (sender, mut receiver) = mpsc::channel::<T>(1000);

        tokio::spawn(async move {
            let mut batch = Vec::with_capacity(batch_size);
            let mut tick = interval(timeout);

            loop {
                tokio::select! {
                    Some(item) = receiver.recv() => {
                        batch.push(item);
                        if batch.len() >= batch_size {
                            processor(std::mem::take(&mut batch)).await;
                            batch.reserve(batch_size);
                        }
                    }
                    _ = tick.tick() => {
                        if !batch.is_empty() {
                            processor(std::mem::take(&mut batch)).await;
                            batch.reserve(batch_size);
                        }
                    }
                    else => break,
                }
            }
        });

        Self { sender }
    }

    async fn send(&self, item: T) -> Result<(), mpsc::error::SendError<T>> {
        self.sender.send(item).await
    }
}
```

### 模式 5: 断路器模式

```rust
use std::sync::Arc;
use tokio::sync::RwLock;
use tokio::time::{Duration, Instant};

enum CircuitState {
    Closed,      // 正常状态
    Open { until: Instant },  // 熔断状态
    HalfOpen,    // 半开状态，测试恢复
}

struct CircuitBreaker {
    state: Arc<RwLock<CircuitState>>,
    failure_threshold: u32,
    success_threshold: u32,
    timeout: Duration,
    consecutive_failures: Arc<RwLock<u32>>,
    consecutive_successes: Arc<RwLock<u32>>,
}

impl CircuitBreaker {
    async fn call<F, Fut, T>(&self, operation: F) -> Result<T, &'static str>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, Box<dyn std::error::Error>>>,
    {
        // 检查当前状态
        {
            let state = self.state.read().await;
            match &*state {
                CircuitState::Open { until } if Instant::now() < *until => {
                    return Err("电路已熔断");
                }
                CircuitState::Open { .. } => {
                    drop(state);
                    let mut state = self.state.write().await;
                    *state = CircuitState::HalfOpen;
                }
                _ => {}
            }
        }

        // 执行操作
        match operation().await {
            Ok(result) => {
                self.on_success().await;
                Ok(result)
            }
            Err(_) => {
                self.on_failure().await;
                Err("操作失败")
            }
        }
    }

    async fn on_success(&self) {
        let mut successes = self.consecutive_successes.write().await;
        *successes += 1;

        if *successes >= self.success_threshold {
            let mut state = self.state.write().await;
            *state = CircuitState::Closed;
            *self.consecutive_failures.write().await = 0;
            *successes = 0;
        }
    }

    async fn on_failure(&self) {
        let mut failures = self.consecutive_failures.write().await;
        *failures += 1;

        if *failures >= self.failure_threshold {
            let mut state = self.state.write().await;
            *state = CircuitState::Open {
                until: Instant::now() + self.timeout
            };
        }
    }
}
```

---

## 🌍 真实应用场景

### 场景 1: Web 服务器实现

```rust
use axum::{
    routing::{get, post},
    Router,
    extract::State,
    http::StatusCode,
    Json,
};
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};

#[derive(Clone)]
struct AppState {
    db_pool: sqlx::PgPool,
    cache: Arc<RwLock<lru::LruCache<String, String>>>,
}

async fn create_server() -> Result<(), Box<dyn std::error::Error>> {
    let state = AppState {
        db_pool: sqlx::PgPool::connect("postgres://localhost/db").await?,
        cache: Arc::new(RwLock::new(lru::LruCache::new(1000))),
    };

    let app = Router::new()
        .route("/users/:id", get(get_user))
        .route("/users", post(create_user))
        .route("/health", get(health_check))
        .with_state(state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    axum::serve(listener, app).await?;

    Ok(())
}

async fn get_user(
    State(state): State<AppState>,
    axum::extract::Path(id): axum::extract::Path<String>,
) -> Result<Json<User>, StatusCode> {
    // 先检查缓存
    {
        let cache = state.cache.read().await;
        if let Some(user_json) = cache.get(&id) {
            if let Ok(user) = serde_json::from_str(user_json) {
                return Ok(Json(user));
            }
        }
    }

    // 查询数据库
    let user: User = sqlx::query_as("SELECT * FROM users WHERE id = $1")
        .bind(&id)
        .fetch_one(&state.db_pool)
        .await
        .map_err(|_| StatusCode::NOT_FOUND)?;

    // 更新缓存
    {
        let mut cache = state.cache.write().await;
        if let Ok(json) = serde_json::to_string(&user) {
            cache.put(id, json);
        }
    }

    Ok(Json(user))
}

#[derive(Debug, Serialize, Deserialize, sqlx::FromRow)]
struct User {
    id: String,
    name: String,
    email: String,
}

async fn health_check() -> &'static str {
    "OK"
}

async fn create_user(
    State(state): State<AppState>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<User>, StatusCode> {
    let user: User = sqlx::query_as(
        "INSERT INTO users (id, name, email) VALUES ($1, $2, $3) RETURNING *"
    )
    .bind(&payload.id)
    .bind(&payload.name)
    .bind(&payload.email)
    .fetch_one(&state.db_pool)
    .await
    .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    Ok(Json(user))
}

#[derive(Deserialize)]
struct CreateUserRequest {
    id: String,
    name: String,
    email: String,
}
```

### 场景 2: 数据处理管道

```rust
use tokio::sync::mpsc;
use serde::Deserialize;

// ETL 管道：提取 -> 转换 -> 加载
async fn etl_pipeline() -> Result<(), Box<dyn std::error::Error>> {
    let (extract_tx, mut extract_rx) = mpsc::channel::<RawData>(1000);
    let (transform_tx, mut transform_rx) = mpsc::channel::<ProcessedData>(1000);
    let (load_tx, mut load_rx) = mpsc::channel::<StoredData>(100);

    // 提取阶段
    let extract_handle = tokio::spawn(async move {
        let sources = vec![
            DataSource::Api("https://api1.example.com/data".to_string()),
            DataSource::File("/data/input.csv".to_string()),
            DataSource::Database("connection_string".to_string()),
        ];

        for source in sources {
            match fetch_data(source).await {
                Ok(data) => {
                    if extract_tx.send(data).await.is_err() {
                        break;
                    }
                }
                Err(e) => eprintln!("提取失败: {:?}", e),
            }
        }
    });

    // 转换阶段
    let transform_handle = tokio::spawn(async move {
        while let Some(raw) = extract_rx.recv().await {
            let processed = transform_data(raw).await;
            if transform_tx.send(processed).await.is_err() {
                break;
            }
        }
    });

    // 加载阶段
    let load_handle = tokio::spawn(async move {
        let mut batch = Vec::with_capacity(100);

        while let Some(data) = transform_rx.recv().await {
            batch.push(data);

            if batch.len() >= 100 {
                if let Err(e) = store_batch(&batch).await {
                    eprintln!("批量存储失败: {:?}", e);
                }
                batch.clear();
            }
        }

        // 处理剩余数据
        if !batch.is_empty() {
            if let Err(e) = store_batch(&batch).await {
                eprintln!("最终批量存储失败: {:?}", e);
            }
        }
    });

    // 等待所有阶段完成
    let _ = tokio::join!(extract_handle, transform_handle, load_handle);

    Ok(())
}

enum DataSource {
    Api(String),
    File(String),
    Database(String),
}

#[derive(Deserialize)]
struct RawData {
    id: u64,
    payload: String,
}

struct ProcessedData {
    id: u64,
    normalized: String,
    checksum: u64,
}

struct StoredData {
    id: u64,
    data: ProcessedData,
    timestamp: u64,
}

async fn fetch_data(source: DataSource) -> Result<RawData, Box<dyn std::error::Error>> {
    match source {
        DataSource::Api(url) => {
            let response = reqwest::get(&url).await?;
            let data = response.json().await?;
            Ok(data)
        }
        DataSource::File(path) => {
            let content = tokio::fs::read_to_string(&path).await?;
            let data: RawData = serde_json::from_str(&content)?;
            Ok(data)
        }
        DataSource::Database(conn) => {
            // 数据库查询实现
            todo!()
        }
    }
}

async fn transform_data(raw: RawData) -> ProcessedData {
    ProcessedData {
        id: raw.id,
        normalized: raw.payload.to_lowercase().trim().to_string(),
        checksum: crc32fast::hash(raw.payload.as_bytes()),
    }
}

async fn store_batch(batch: &[ProcessedData]) -> Result<(), Box<dyn std::error::Error>> {
    // 批量存储实现
    println!("存储 {} 条记录", batch.len());
    Ok(())
}
```

### 场景 3: 实时消息系统

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{broadcast, mpsc};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::sync::Arc;

struct ChatServer {
    clients: Arc<RwLock<HashMap<u64, mpsc::Sender<Message>>>>,
    broadcast_tx: broadcast::Sender<Message>,
}

impl ChatServer {
    fn new() -> Self {
        let (broadcast_tx, _) = broadcast::channel(1000);
        Self {
            clients: Arc::new(RwLock::new(HashMap::new())),
            broadcast_tx,
        }
    }

    async fn run(&self, addr: &str) -> Result<(), Box<dyn std::error::Error>> {
        let listener = TcpListener::bind(addr).await?;
        println!("聊天服务器运行在 {}", addr);

        let mut client_id = 0u64;

        loop {
            let (socket, addr) = listener.accept().await?;
            client_id += 1;
            let id = client_id;

            let (tx, rx) = mpsc::channel(100);
            {
                let mut clients = self.clients.write().await;
                clients.insert(id, tx);
            }

            let broadcast_tx = self.broadcast_tx.clone();
            let mut broadcast_rx = self.broadcast_tx.subscribe();
            let clients = Arc::clone(&self.clients);

            tokio::spawn(async move {
                handle_client(socket, id, addr, rx, broadcast_tx, broadcast_rx, clients).await;
            });
        }
    }
}

async fn handle_client(
    mut socket: TcpStream,
    id: u64,
    addr: std::net::SocketAddr,
    mut msg_rx: mpsc::Receiver<Message>,
    broadcast_tx: broadcast::Sender<Message>,
    mut broadcast_rx: broadcast::Receiver<Message>,
    clients: Arc<RwLock<HashMap<u64, mpsc::Sender<Message>>>>,
) {
    let (mut reader, mut writer) = socket.split();
    let mut buf = [0u8; 1024];

    // 欢迎消息
    let welcome = Message::System(format!("欢迎用户 {} 加入聊天室！", id));
    let _ = broadcast_tx.send(welcome);

    loop {
        tokio::select! {
            // 从客户端读取消息
            result = reader.read(&mut buf) => {
                match result {
                    Ok(0) => {
                        // 连接关闭
                        let _ = broadcast_tx.send(Message::System(format!("用户 {} 离开了", id)));
                        break;
                    }
                    Ok(n) => {
                        let text = String::from_utf8_lossy(&buf[..n]);
                        let msg = Message::Chat {
                            from: id,
                            content: text.to_string()
                        };
                        let _ = broadcast_tx.send(msg);
                    }
                    Err(e) => {
                        eprintln!("读取错误: {:?}", e);
                        break;
                    }
                }
            }

            // 接收广播消息
            Ok(msg) = broadcast_rx.recv() => {
                let text = format!("{}\n", msg);
                if writer.write_all(text.as_bytes()).await.is_err() {
                    break;
                }
            }

            // 接收私信
            Some(msg) = msg_rx.recv() => {
                let text = format!("[私信] {}\n", msg);
                if writer.write_all(text.as_bytes()).await.is_err() {
                    break;
                }
            }
        }
    }

    // 清理
    let mut clients = clients.write().await;
    clients.remove(&id);
}

enum Message {
    System(String),
    Chat { from: u64, content: String },
    Private { from: u64, to: u64, content: String },
}

impl std::fmt::Display for Message {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Message::System(text) => write!(f, "[系统] {}", text),
            Message::Chat { from, content } => write!(f, "[用户{}] {}", from, content),
            Message::Private { from, content, .. } => write!(f, "[来自用户{}的私信] {}", from, content),
        }
    }
}

use std::collections::HashMap;
use tokio::sync::RwLock;
```

---

## 🐛 常见问题与解决方案

### 问题 1: 阻塞运行时

```rust
// ❌ 在异步上下文中阻塞 - 会导致整个线程阻塞
async fn bad_example() {
    std::thread::sleep(Duration::from_secs(1)); // 阻塞！
    let data = std::fs::read_to_string("file.txt").unwrap(); // 阻塞 I/O！
}

// ✅ 使用异步等价操作
async fn good_example() {
    tokio::time::sleep(Duration::from_secs(1)).await;
    let data = tokio::fs::read_to_string("file.txt").await.unwrap();
}

// ✅ 如果必须使用阻塞操作，使用 spawn_blocking
async fn blocking_operation() -> String {
    tokio::task::spawn_blocking(|| {
        std::thread::sleep(Duration::from_secs(1));
        "结果".to_string()
    })
    .await
    .unwrap()
}
```

### 问题 2: Future 必须 Send

```rust
// ❌ 非 Send 类型跨线程使用
use std::rc::Rc;

async fn bad_example() {
    let rc = Rc::new(42);
    // 如果在多线程运行时中使用，会编译错误
}

// ✅ 使用 Arc 代替 Rc
use std::sync::Arc;

async fn good_example() {
    let arc = Arc::new(42);
    let arc2 = Arc::clone(&arc);

    tokio::spawn(async move {
        println!("{}", arc2); // Arc 是 Send
    });
}
```

### 问题 3: 持有锁跨越 await 点

```rust
use tokio::sync::Mutex;

// ❌ 危险：持有 std::sync::MutexGuard 跨越 await
async fn bad_example(mutex: &std::sync::Mutex<String>) {
    let guard = mutex.lock().unwrap();
    some_async_operation().await; // 可能阻塞其他线程！
    // guard 在这里释放
}

// ✅ 使用 tokio::sync::Mutex
async fn good_example(mutex: &tokio::sync::Mutex<String>) {
    {
        let guard = mutex.lock().await;
        // 使用 guard
    } // 锁在这里释放

    some_async_operation().await; // 不影响其他任务
}

// ✅ 或者缩小锁的作用域
async fn better_example(mutex: &std::sync::Mutex<String>) {
    let data = {
        let guard = mutex.lock().unwrap();
        guard.clone() // 复制数据后释放锁
    };

    some_async_operation().await;
}
```

### 问题 4: 忘记处理 Cancel Safety

```rust
// ❌ 非 cancel-safe: select! 取消分支可能导致数据丢失
async fn not_cancel_safe() {
    let (tx, rx) = tokio::sync::mpsc::channel::<i32>(10);

    tokio::select! {
        _ = tx.send(1) => {},  // 如果取消，消息可能已部分发送
        _ = tokio::time::sleep(Duration::from_secs(1)) => {},
    }
}

// ✅ cancel-safe 模式
async fn cancel_safe() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<i32>(10);

    tokio::select! {
        biased; // 按顺序检查
        result = rx.recv() => {
            // recv 是 cancel-safe 的
            println!("收到: {:?}", result);
        }
        _ = tokio::time::sleep(Duration::from_secs(1)) => {
            println!("超时");
        }
    }
}
```

### 问题 5: 递归 async 函数

```rust
// ❌ 编译错误：递归 async 函数
async fn recursive_bad(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        n + recursive_bad(n - 1).await // 编译错误！
    }
}

// ✅ 使用 Box::pin 包装递归调用
use std::pin::Pin;
use std::future::Future;

fn recursive_good(n: i32) -> Pin<Box<dyn Future<Output = i32> + Send>> {
    Box::pin(async move {
        if n <= 0 {
            0
        } else {
            n + recursive_good(n - 1).await
        }
    })
}

// ✅ 或者使用 async_recursion crate
// #[async_recursion]
// async fn recursive_with_crate(n: i32) -> i32 { ... }
```

---

## 📚 相关文档

- [完整文档](../../crates/c06_async/README.md)
- [异步编程指南](../../crates/c06_async/docs/tier_02_guides/01_异步编程快速入门.md)
- [Reactor 模式](../../crates/c06_async/docs/tier_04_advanced/01_异步并发模式.md)
- [Actor 模式](../../crates/c06_async/docs/tier_02_guides/04_异步设计模式实践.md)
- [异步状态机形式化](../research_notes/formal_methods/async_state_machine.md) - Future/Poll 状态机形式化定义与证明

---

## 🆕 Rust 1.94 特性

> **适用版本**: Rust 1.94.0+

### ControlFlow 在异步编程中的应用

Rust 1.94 的 `ControlFlow` 类型可以用于异步流的提前终止：

```rust
use std::ops::ControlFlow;
use tokio::time::{sleep, Duration};

// 使用 ControlFlow 在异步流中提前终止
async fn process_items(items: &[i32]) -> ControlFlow<i32, ()> {
    for &item in items {
        if item < 0 {
            return ControlFlow::Break(item);  // 遇到负数提前终止
        }
        sleep(Duration::from_millis(10)).await;
    }
    ControlFlow::Continue(())
}

// 在 try_for_each 中使用
async fn find_negative(items: &[i32]) -> Option<i32> {
    let result = items.iter().try_for_each(|&n| async move {
        if n < 0 {
            ControlFlow::Break(n)
        } else {
            ControlFlow::Continue(())
        }
    }).await;

    result.break_value()
}
```

### Peekable 迭代器增强

Rust 1.94 为 `Peekable` 添加了 `next_if_map`，可用于异步解析器：

```rust
use std::iter::Peekable;

async fn parse_number(chars: &mut Peekable<impl Iterator<Item = char>>) -> Option<i32> {
    chars.next_if_map(|c| {
        if c.is_ascii_digit() {
            Some(c as i32 - '0' as i32)
        } else {
            None
        }
    })
}
```

**最后更新**: 2026-03-14 (添加 Rust 1.94 特性)

---

## 🔗 形式化引用

本指南中的概念与以下形式化定理/定义对应：

| 概念 | 形式化定义/定理 | 文档 |
| :--- | :--- | :--- |
| Future Trait | Def 5.1 (Future Trait) | [async_state_machine.md](../research_notes/formal_methods/async_state_machine.md) |
| Poll 类型 | Def 5.2 (Poll) | [async_state_machine.md](../research_notes/formal_methods/async_state_machine.md) |
| Waker 机制 | Def 5.3 (Waker) | [async_state_machine.md](../research_notes/formal_methods/async_state_machine.md) |
| Pin 不动性 | T-PIN1 (Pin 不动性) | [pin_self_referential.md](../research_notes/formal_methods/pin_self_referential.md) |
| Send/Sync 安全 | SEND-T1/SYNC-T1 | [send_sync_formalization.md](../research_notes/formal_methods/send_sync_formalization.md) |
| 异步状态机 | T6.1-T6.3 | [async_state_machine.md](../research_notes/formal_methods/async_state_machine.md) |

**定理引用说明**: 本指南中的异步模式实现基于上述形式化定理保证。例如，`Future` 必须实现 `Send` 才能跨线程传递 (SEND-T1)；`Pin` 保证自引用结构安全 (T-PIN1)。

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 完整实现 (Week 15 形式化引用补全)
**最后更新**: 2026-02-27
