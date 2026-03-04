# Rust分布式系统设计模式

> **Rust版本**: 1.93.1
> **覆盖范围**: 微服务、共识算法、分布式事务、消息队列
> **权威参考**: Tokio生态系统, Raft共识实现, NATS/Redis客户端

---

## 目录

- [Rust分布式系统设计模式](#rust分布式系统设计模式)
  - [目录](#目录)
  - [1. 分布式系统概述](#1-分布式系统概述)
    - [Rust在分布式系统中的优势](#rust在分布式系统中的优势)
    - [常用框架与库](#常用框架与库)
  - [2. 微服务架构模式](#2-微服务架构模式)
    - [API Gateway模式](#api-gateway模式)
    - [Sidecar模式](#sidecar模式)
  - [3. 服务发现与注册](#3-服务发现与注册)
    - [Consul集成](#consul集成)
    - [负载均衡](#负载均衡)
  - [4. 分布式一致性](#4-分布式一致性)
    - [Raft共识 (使用raft-rs)](#raft共识-使用raft-rs)
    - [分布式锁 (使用Redis)](#分布式锁-使用redis)
  - [5. 分布式事务](#5-分布式事务)
    - [Saga模式](#saga模式)
  - [6. 消息队列模式](#6-消息队列模式)
    - [发布-订阅模式](#发布-订阅模式)
    - [事件溯源](#事件溯源)
  - [7. 熔断与限流](#7-熔断与限流)
    - [熔断器模式](#熔断器模式)
    - [令牌桶限流](#令牌桶限流)
  - [8. 可观测性](#8-可观测性)
    - [分布式追踪](#分布式追踪)
    - [健康检查](#健康检查)
  - [参考文献](#参考文献)

---

## 1. 分布式系统概述

### Rust在分布式系统中的优势

```text
1. 零成本抽象：高性能网络服务
2. fearless concurrency：安全的并发处理
3. 内存安全：避免段错误和数据竞争
4. 异步生态系统：Tokio/actix-web等成熟框架
5. 类型安全：编译时捕获API错误
```

### 常用框架与库

| 用途 | 库/框架 | 特点 |
|------|--------|------|
| Web服务 | actix-web, axum | 高性能异步 |
| gRPC | tonic | 类型安全RPC |
| 序列化 | serde, prost | 零拷贝 |
| 消息队列 | lapin(AMQP), rdkafka | 异步集成 |
| 缓存 | redis, bb8 | 连接池 |
| 数据库 | sqlx, sea-orm | 编译时检查 |

---

## 2. 微服务架构模式

### API Gateway模式

```rust
use axum::{
    routing::{get, post},
    Router, Extension,
    http::StatusCode,
    response::Json,
};
use std::sync::Arc;

// 服务注册
pub struct ServiceRegistry {
    services: std::collections::HashMap<String, String>,
}

impl ServiceRegistry {
    pub fn new() -> Self {
        let mut services = std::collections::HashMap::new();
        services.insert("user".to_string(), "http://user-service:8080".to_string());
        services.insert("order".to_string(), "http://order-service:8081".to_string());
        Self { services }
    }

    pub fn get(&self, name: &str) -> Option<&String> {
        self.services.get(name)
    }
}

// API Gateway
pub fn create_gateway() -> Router {
    let registry = Arc::new(ServiceRegistry::new());

    Router::new()
        .route("/api/users/*path", get(proxy_to_user_service))
        .route("/api/orders/*path", get(proxy_to_order_service))
        .layer(Extension(registry))
}

async fn proxy_to_user_service(
    Extension(registry): Extension<Arc<ServiceRegistry>>,
) -> Result<Json<serde_json::Value>, StatusCode> {
    let client = reqwest::Client::new();
    let url = format!("{}/users", registry.get("user").unwrap());

    let response = client.get(&url)
        .send()
        .await
        .map_err(|_| StatusCode::BAD_GATEWAY)?;

    let data: serde_json::Value = response.json().await
        .map_err(|_| StatusCode::BAD_GATEWAY)?;

    Ok(Json(data))
}
```

### Sidecar模式

```rust
// 使用Envoy或自定义sidecar实现横切关注点

pub struct SidecarConfig {
    service_name: String,
    logging_enabled: bool,
    metrics_enabled: bool,
    tracing_enabled: bool,
}

pub struct SidecarMiddleware<S> {
    inner: S,
    config: SidecarConfig,
}

impl<S> SidecarMiddleware<S> {
    pub fn new(inner: S, config: SidecarConfig) -> Self {
        Self { inner, config }
    }

    pub async fn handle_request<R>(&self, request: R) -> Result<R, String>
    where
        R: std::fmt::Debug,
    {
        // 日志
        if self.config.logging_enabled {
            tracing::info!("Request: {:?}", request);
        }

        // 指标
        if self.config.metrics_enabled {
            metrics::counter!("requests_total", 1);
        }

        // 追踪
        if self.config.tracing_enabled {
            let span = tracing::info_span!("request", service = %self.config.service_name);
            let _enter = span.enter();
        }

        // 转发到实际服务
        Ok(request)
    }
}
```

---

## 3. 服务发现与注册

### Consul集成

```rust
use consul::Client;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct ServiceRegistration {
    pub id: String,
    pub name: String,
    pub address: String,
    pub port: u16,
    pub check: Option<HealthCheck>,
}

#[derive(Serialize, Deserialize)]
pub struct HealthCheck {
    pub http: String,
    pub interval: String,
}

pub struct ServiceDiscovery {
    client: Client,
    service_id: String,
}

impl ServiceDiscovery {
    pub fn new(consul_addr: &str) -> Self {
        let config = consul::Config::new(consul_addr).unwrap();
        let client = consul::Client::new(config);

        Self {
            client,
            service_id: uuid::Uuid::new_v4().to_string(),
        }
    }

    pub async fn register(&self, name: &str, address: &str, port: u16) -> Result<(), String> {
        let registration = ServiceRegistration {
            id: self.service_id.clone(),
            name: name.to_string(),
            address: address.to_string(),
            port,
            check: Some(HealthCheck {
                http: format!("http://{}:{}/health", address, port),
                interval: "10s".to_string(),
            }),
        };

        self.client.register(&registration)
            .await
            .map_err(|e| e.to_string())
    }

    pub async fn discover(&self, service_name: &str) -> Result<Vec<String>, String> {
        let services = self.client.get_service_addresses(service_name, true)
            .await
            .map_err(|e| e.to_string())?;

        Ok(services)
    }

    pub async fn deregister(&self) -> Result<(), String> {
        self.client.deregister(&self.service_id)
            .await
            .map_err(|e| e.to_string())
    }
}
```

### 负载均衡

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

pub enum LoadBalanceStrategy {
    RoundRobin,
    Random,
    LeastConnections,
    WeightedRoundRobin(Vec<usize>),
}

pub struct LoadBalancer {
    backends: Vec<String>,
    strategy: LoadBalanceStrategy,
    current_index: AtomicUsize,
}

impl LoadBalancer {
    pub fn new(backends: Vec<String>, strategy: LoadBalanceStrategy) -> Self {
        Self {
            backends,
            strategy,
            current_index: AtomicUsize::new(0),
        }
    }

    pub fn next(&self) -> Option<&String> {
        match self.strategy {
            LoadBalanceStrategy::RoundRobin => {
                let index = self.current_index.fetch_add(1, Ordering::Relaxed);
                self.backends.get(index % self.backends.len())
            }
            LoadBalanceStrategy::Random => {
                use rand::Rng;
                let index = rand::thread_rng().gen_range(0..self.backends.len());
                self.backends.get(index)
            }
            _ => unimplemented!(),
        }
    }
}
```

---

## 4. 分布式一致性

### Raft共识 (使用raft-rs)

```rust
use raft::{Config, Raft, StateRole};

pub struct RaftNode {
    raft: Raft<MemoryStorage>,
    config: Config,
}

impl RaftNode {
    pub fn new(node_id: u64, peers: Vec<u64>) -> Self {
        let config = Config {
            id: node_id,
            election_tick: 10,
            heartbeat_tick: 3,
            ..Default::default()
        };

        let storage = MemoryStorage::new();
        let raft = Raft::new(&config, storage).unwrap();

        Self { raft, config }
    }

    pub async fn propose(&mut self, data: Vec<u8>) -> Result<(), String> {
        if self.raft.state != StateRole::Leader {
            return Err("Not leader".to_string());
        }

        self.raft.propose(vec![], data)
            .map_err(|e| e.to_string())
    }

    pub async fn on_message(&mut self, msg: Message) {
        self.raft.step(msg).unwrap();
    }
}
```

### 分布式锁 (使用Redis)

```rust
use redis::AsyncCommands;
use uuid::Uuid;

pub struct DistributedLock {
    redis: redis::aio::MultiplexedConnection,
    lock_key: String,
    lock_value: String,
    ttl: usize,
}

impl DistributedLock {
    pub async fn new(redis_url: &str, lock_key: &str, ttl: usize) -> Result<Self, String> {
        let client = redis::Client::open(redis_url).map_err(|e| e.to_string())?;
        let redis = client.get_multiplexed_async_connection().await
            .map_err(|e| e.to_string())?;

        Ok(Self {
            redis,
            lock_key: lock_key.to_string(),
            lock_value: Uuid::new_v4().to_string(),
            ttl,
        })
    }

    pub async fn acquire(&mut self) -> Result<bool, String> {
        let result: Option<String> = self.redis
            .set_nx(&self.lock_key, &self.lock_value)
            .await
            .map_err(|e| e.to_string())?;

        if result.is_some() {
            let _: () = self.redis
                .expire(&self.lock_key, self.ttl as i64)
                .await
                .map_err(|e| e.to_string())?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub async fn release(&mut self) -> Result<(), String> {
        let script = redis::Script::new(r#"
            if redis.call("get", KEYS[1]) == ARGV[1] then
                return redis.call("del", KEYS[1])
            else
                return 0
            end
        "#);

        script.key(&self.lock_key)
            .arg(&self.lock_value)
            .invoke_async(&mut self.redis)
            .await
            .map_err(|e| e.to_string())
    }
}

// 使用
async fn with_distributed_lock<F, Fut, R>(redis_url: &str, lock_key: &str, f: F) -> Result<R, String>
where
    F: FnOnce() -> Fut,
    Fut: std::future::Future<Output = R>,
{
    let mut lock = DistributedLock::new(redis_url, lock_key, 30).await?;

    // 重试获取锁
    loop {
        if lock.acquire().await? {
            break;
        }
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }

    let result = f().await;
    lock.release().await?;

    Ok(result)
}
```

---

## 5. 分布式事务

### Saga模式

```rust
use std::future::Future;
use std::pin::Pin;

pub type StepResult = Result<(), String>;
pub type CompensateResult = Pin<Box<dyn Future<Output = StepResult> + Send>>;
pub type StepAction = Pin<Box<dyn Future<Output = StepResult> + Send>>;

pub struct SagaStep {
    name: String,
    action: Box<dyn Fn() -> StepAction + Send>,
    compensate: Box<dyn Fn() -> CompensateResult + Send>,
}

pub struct Saga {
    steps: Vec<SagaStep>,
    completed: Vec<String>,
}

impl Saga {
    pub fn new() -> Self {
        Self {
            steps: vec![],
            completed: vec![],
        }
    }

    pub fn add_step<F, Fut, C, Cfg>(&mut self, name: &str, action: F, compensate: C)
    where
        F: Fn() -> Fut + Send + 'static,
        Fut: Future<Output = StepResult> + Send + 'static,
        C: Fn() -> Cfg + Send + 'static,
        Cfg: Future<Output = StepResult> + Send + 'static,
    {
        self.steps.push(SagaStep {
            name: name.to_string(),
            action: Box::new(move || Box::pin(action())),
            compensate: Box::new(move || Box::pin(compensate())),
        });
    }

    pub async fn execute(mut self) -> Result<(), String> {
        for step in &self.steps {
            match (step.action)().await {
                Ok(()) => {
                    self.completed.push(step.name.clone());
                }
                Err(e) => {
                    // 补偿
                    for completed_step in self.completed.iter().rev() {
                        if let Some(s) = self.steps.iter().find(|s| &s.name == completed_step) {
                            (s.compensate)().await.ok(); // 忽略补偿错误
                        }
                    }
                    return Err(format!("Step {} failed: {}", step.name, e));
                }
            }
        }
        Ok(())
    }
}

// 使用
async fn saga_example() {
    let mut saga = Saga::new();

    saga.add_step(
        "reserve_inventory",
        || Box::pin(async { Ok(()) }),
        || Box::pin(async { Ok(()) }),
    );

    saga.add_step(
        "process_payment",
        || Box::pin(async { Ok(()) }),
        || Box::pin(async { Ok(()) }),
    );

    saga.add_step(
        "create_order",
        || Box::pin(async { Ok(()) }),
        || Box::pin(async { Ok(()) }),
    );

    if let Err(e) = saga.execute().await {
        eprintln!("Transaction failed: {}", e);
    }
}
```

---

## 6. 消息队列模式

### 发布-订阅模式

```rust
use lapin::{Connection, ConnectionProperties, Channel, options::*, types::FieldTable};

pub struct MessageBus {
    connection: Connection,
    channel: Channel,
}

impl MessageBus {
    pub async fn new(amqp_url: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let connection = Connection::connect(amqp_url, ConnectionProperties::default()).await?;
        let channel = connection.create_channel().await?;

        Ok(Self { connection, channel })
    }

    pub async fn publish(&self, exchange: &str, routing_key: &str, payload: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
        self.channel.basic_publish(
            exchange,
            routing_key,
            BasicPublishOptions::default(),
            payload,
            FieldTable::default(),
        ).await?;

        Ok(())
    }

    pub async fn subscribe<F, Fut>(&self, queue: &str, handler: F) -> Result<(), Box<dyn std::error::Error>>
    where
        F: Fn(Vec<u8>) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = ()> + Send + 'static,
    {
        let mut consumer = self.channel.basic_consume(
            queue,
            "consumer",
            BasicConsumeOptions::default(),
            FieldTable::default(),
        ).await?;

        tokio::spawn(async move {
            while let Some(delivery) = consumer.next().await {
                if let Ok(delivery) = delivery {
                    handler(delivery.data).await;
                    delivery.ack(BasicAckOptions::default()).await.ok();
                }
            }
        });

        Ok(())
    }
}
```

### 事件溯源

```rust
use serde::{Serialize, Deserialize};
use std::collections::HashMap;

#[derive(Serialize, Deserialize, Clone, Debug)]
pub enum OrderEvent {
    OrderCreated { order_id: String, user_id: String },
    OrderPaid { order_id: String, amount: f64 },
    OrderShipped { order_id: String, tracking_id: String },
    OrderCompleted { order_id: String },
}

pub struct EventStore {
    events: HashMap<String, Vec<OrderEvent>>,
}

impl EventStore {
    pub fn new() -> Self {
        Self {
            events: HashMap::new(),
        }
    }

    pub fn append(&mut self, order_id: &str, event: OrderEvent) {
        self.events
            .entry(order_id.to_string())
            .or_insert_with(Vec::new)
            .push(event);
    }

    pub fn get_events(&self, order_id: &str) -> Vec<OrderEvent> {
        self.events.get(order_id).cloned().unwrap_or_default()
    }

    pub fn rebuild_state(&self, order_id: &str) -> Option<Order> {
        let events = self.get_events(order_id);
        if events.is_empty() {
            return None;
        }

        let mut order = Order::new(order_id);
        for event in events {
            order.apply(event);
        }

        Some(order)
    }
}

pub struct Order {
    id: String,
    user_id: Option<String>,
    status: OrderStatus,
    amount: Option<f64>,
}

#[derive(Default)]
pub enum OrderStatus {
    #[default]
    Pending,
    Paid,
    Shipped,
    Completed,
}

impl Order {
    fn new(id: &str) -> Self {
        Self {
            id: id.to_string(),
            user_id: None,
            status: OrderStatus::Pending,
            amount: None,
        }
    }

    fn apply(&mut self, event: OrderEvent) {
        match event {
            OrderEvent::OrderCreated { user_id, .. } => {
                self.user_id = Some(user_id);
            }
            OrderEvent::OrderPaid { amount, .. } => {
                self.amount = Some(amount);
                self.status = OrderStatus::Paid;
            }
            OrderEvent::OrderShipped { .. } => {
                self.status = OrderStatus::Shipped;
            }
            OrderEvent::OrderCompleted { .. } => {
                self.status = OrderStatus::Completed;
            }
        }
    }
}
```

---

## 7. 熔断与限流

### 熔断器模式

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tokio::time::sleep;

#[derive(Clone, Copy, PartialEq)]
pub enum CircuitState {
    Closed,      // 正常
    Open,        // 熔断
    HalfOpen,    // 半开测试
}

pub struct CircuitBreaker {
    failure_threshold: usize,
    success_threshold: usize,
    timeout: Duration,
    state: std::sync::RwLock<CircuitState>,
    failures: AtomicUsize,
    successes: AtomicUsize,
    last_failure_time: std::sync::RwLock<Option<Instant>>,
}

impl CircuitBreaker {
    pub fn new(failure_threshold: usize, success_threshold: usize, timeout: Duration) -> Self {
        Self {
            failure_threshold,
            success_threshold,
            timeout,
            state: std::sync::RwLock::new(CircuitState::Closed),
            failures: AtomicUsize::new(0),
            successes: AtomicUsize::new(0),
            last_failure_time: std::sync::RwLock::new(None),
        }
    }

    pub async fn call<F, Fut, T>(&self, f: F) -> Result<T, String>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, String>>,
    {
        self.update_state();

        let state = *self.state.read().unwrap();
        match state {
            CircuitState::Open => {
                return Err("Circuit breaker is OPEN".to_string());
            }
            CircuitState::HalfOpen | CircuitState::Closed => {
                match f().await {
                    Ok(result) => {
                        self.on_success();
                        Ok(result)
                    }
                    Err(e) => {
                        self.on_failure();
                        Err(e)
                    }
                }
            }
        }
    }

    fn update_state(&self) {
        let mut state = self.state.write().unwrap();
        if *state == CircuitState::Open {
            let last_failure = *self.last_failure_time.read().unwrap();
            if let Some(time) = last_failure {
                if time.elapsed() > self.timeout {
                    *state = CircuitState::HalfOpen;
                    self.failures.store(0, Ordering::Relaxed);
                    self.successes.store(0, Ordering::Relaxed);
                }
            }
        }
    }

    fn on_success(&self) {
        let state = *self.state.read().unwrap();
        if state == CircuitState::HalfOpen {
            let successes = self.successes.fetch_add(1, Ordering::Relaxed) + 1;
            if successes >= self.success_threshold {
                *self.state.write().unwrap() = CircuitState::Closed;
                self.failures.store(0, Ordering::Relaxed);
                self.successes.store(0, Ordering::Relaxed);
            }
        } else {
            self.failures.store(0, Ordering::Relaxed);
        }
    }

    fn on_failure(&self) {
        let failures = self.failures.fetch_add(1, Ordering::Relaxed) + 1;
        *self.last_failure_time.write().unwrap() = Some(Instant::now());

        if failures >= self.failure_threshold {
            *self.state.write().unwrap() = CircuitState::Open;
        }
    }
}
```

### 令牌桶限流

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

pub struct TokenBucket {
    capacity: u64,
    tokens: AtomicU64,
    refill_rate: u64, // tokens per second
    last_refill: std::sync::Mutex<Instant>,
}

impl TokenBucket {
    pub fn new(capacity: u64, refill_rate: u64) -> Self {
        Self {
            capacity,
            tokens: AtomicU64::new(capacity),
            refill_rate,
            last_refill: std::sync::Mutex::new(Instant::now()),
        }
    }

    pub fn try_consume(&self, tokens: u64) -> bool {
        self.refill();

        let current = self.tokens.load(Ordering::Relaxed);
        if current >= tokens {
            self.tokens.fetch_sub(tokens, Ordering::Relaxed);
            true
        } else {
            false
        }
    }

    fn refill(&self) {
        let mut last_refill = self.last_refill.lock().unwrap();
        let now = Instant::now();
        let elapsed = now.duration_since(*last_refill).as_secs();

        if elapsed > 0 {
            let new_tokens = elapsed * self.refill_rate;
            let current = self.tokens.load(Ordering::Relaxed);
            let updated = (current + new_tokens).min(self.capacity);
            self.tokens.store(updated, Ordering::Relaxed);
            *last_refill = now;
        }
    }
}

// 使用
pub struct RateLimitedService {
    bucket: TokenBucket,
}

impl RateLimitedService {
    pub async fn handle_request(&self) -> Result<String, String> {
        if self.bucket.try_consume(1) {
            // 处理请求
            Ok("Success".to_string())
        } else {
            Err("Rate limit exceeded".to_string())
        }
    }
}
```

---

## 8. 可观测性

### 分布式追踪

```rust
use opentelemetry::trace::{Tracer, SpanKind};
use opentelemetry::Context;

pub async fn traced_operation() {
    let tracer = opentelemetry::global::tracer("my_service");

    let span = tracer
        .span_builder("process_order")
        .with_kind(SpanKind::Server)
        .start(&tracer);

    let cx = Context::current_with_span(span);

    // 嵌套span
    let inner_span = tracer
        .span_builder("validate_payment")
        .with_kind(SpanKind::Internal)
        .start(&tracer);

    // 执行操作
    validate_payment().await;

    inner_span.end();

    // 传播上下文到其他服务
    let headers = std::collections::HashMap::new();
    opentelemetry::global::get_text_map_propagator(|propagator| {
        propagator.inject_context(&cx, &mut headers);
    });
}
```

### 健康检查

```rust
use axum::{routing::get, Json, Router};
use serde_json::json;

pub fn health_routes() -> Router {
    Router::new()
        .route("/health", get(health_check))
        .route("/ready", get(readiness_check))
        .route("/live", get(liveness_check))
}

async fn health_check() -> Json<serde_json::Value> {
    // 检查所有依赖
    let checks = vec![
        ("database", check_database().await),
        ("cache", check_cache().await),
        ("external_api", check_external_api().await),
    ];

    let all_healthy = checks.iter().all(|(_, status)| *status);

    let status = if all_healthy { "healthy" } else { "unhealthy" };
    let http_status = if all_healthy { 200 } else { 503 };

    Json(json!({
        "status": status,
        "checks": checks.into_iter().collect::<std::collections::HashMap<_, _>>(),
    }))
}

async fn check_database() -> bool {
    // 检查数据库连接
    true
}

async fn check_cache() -> bool {
    // 检查缓存连接
    true
}

async fn check_external_api() -> bool {
    // 检查外部API
    true
}
```

---

## 参考文献

1. Designing Data-Intensive Applications (Martin Kleppmann)
2. Building Microservices (Sam Newman)
3. Raft Consensus Algorithm: <https://raft.github.io/>
4. NATS Documentation: <https://docs.nats.io/>
5. Redis分布式锁: <https://redis.io/docs/manual/patterns/distributed-locks/>
