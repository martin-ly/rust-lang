# Rust 微服务架构设计指南 (2025版)

> **主题**: 完整的 Rust 微服务架构设计与实现  
> **难度**: 中高级  
> **预计学习时间**: 8-12 小时  
> **更新日期**: 2025-10-20

---


## 📊 目录

- [📋 目录](#目录)
- [概述](#概述)
  - [为什么选择 Rust 构建微服务](#为什么选择-rust-构建微服务)
  - [核心技术栈](#核心技术栈)
- [架构设计](#架构设计)
  - [整体架构](#整体架构)
  - [服务划分原则](#服务划分原则)
  - [通信模式](#通信模式)
- [核心组件](#核心组件)
  - [1. API 网关](#1-api-网关)
  - [2. 服务注册与发现](#2-服务注册与发现)
  - [3. 配置中心](#3-配置中心)
  - [4. 消息队列](#4-消息队列)
- [服务实现](#服务实现)
  - [用户服务 (User Service)](#用户服务-user-service)
  - [订单服务 (Order Service)](#订单服务-order-service)
- [横切关注点](#横切关注点)
  - [1. 认证与授权](#1-认证与授权)
  - [2. 分布式追踪](#2-分布式追踪)
  - [3. 日志聚合](#3-日志聚合)
  - [4. 健康检查](#4-健康检查)
- [数据管理](#数据管理)
  - [数据库per服务](#数据库per服务)
  - [分布式事务](#分布式事务)
  - [事件溯源](#事件溯源)
- [部署架构](#部署架构)
  - [Kubernetes 部署](#kubernetes-部署)
  - [Docker Compose (开发环境)](#docker-compose-开发环境)
- [监控与告警](#监控与告警)
  - [指标收集](#指标收集)
  - [告警规则](#告警规则)
- [最佳实践](#最佳实践)
  - [1. 服务设计](#1-服务设计)
  - [2. API 设计](#2-api-设计)
  - [3. 错误处理](#3-错误处理)
  - [4. 性能优化](#4-性能优化)
  - [5. 安全性](#5-安全性)
- [常见陷阱](#常见陷阱)
  - [陷阱1: 服务粒度过细](#陷阱1-服务粒度过细)
  - [陷阱2: 忽略网络分区](#陷阱2-忽略网络分区)
  - [陷阱3: 缺少熔断机制](#陷阱3-缺少熔断机制)
- [完整示例项目](#完整示例项目)
- [参考资源](#参考资源)


## 📋 目录

- [Rust 微服务架构设计指南 (2025版)](#rust-微服务架构设计指南-2025版)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [为什么选择 Rust 构建微服务](#为什么选择-rust-构建微服务)
    - [核心技术栈](#核心技术栈)
  - [架构设计](#架构设计)
    - [整体架构](#整体架构)
    - [服务划分原则](#服务划分原则)
    - [通信模式](#通信模式)
  - [核心组件](#核心组件)
    - [1. API 网关](#1-api-网关)
    - [2. 服务注册与发现](#2-服务注册与发现)
    - [3. 配置中心](#3-配置中心)
    - [4. 消息队列](#4-消息队列)
  - [服务实现](#服务实现)
    - [用户服务 (User Service)](#用户服务-user-service)
    - [订单服务 (Order Service)](#订单服务-order-service)
  - [横切关注点](#横切关注点)
    - [1. 认证与授权](#1-认证与授权)
    - [2. 分布式追踪](#2-分布式追踪)
    - [3. 日志聚合](#3-日志聚合)
    - [4. 健康检查](#4-健康检查)
  - [数据管理](#数据管理)
    - [数据库per服务](#数据库per服务)
    - [分布式事务](#分布式事务)
    - [事件溯源](#事件溯源)
  - [部署架构](#部署架构)
    - [Kubernetes 部署](#kubernetes-部署)
    - [Docker Compose (开发环境)](#docker-compose-开发环境)
  - [监控与告警](#监控与告警)
    - [指标收集](#指标收集)
    - [告警规则](#告警规则)
  - [最佳实践](#最佳实践)
    - [1. 服务设计](#1-服务设计)
    - [2. API 设计](#2-api-设计)
    - [3. 错误处理](#3-错误处理)
    - [4. 性能优化](#4-性能优化)
    - [5. 安全性](#5-安全性)
  - [常见陷阱](#常见陷阱)
    - [陷阱1: 服务粒度过细](#陷阱1-服务粒度过细)
    - [陷阱2: 忽略网络分区](#陷阱2-忽略网络分区)
    - [陷阱3: 缺少熔断机制](#陷阱3-缺少熔断机制)
  - [完整示例项目](#完整示例项目)
  - [参考资源](#参考资源)

---

## 概述

### 为什么选择 Rust 构建微服务

**核心优势**:

1. **高性能**: 接近 C/C++ 的性能，低延迟
2. **内存安全**: 无 GC，无数据竞争
3. **并发安全**: 编译期保证线程安全
4. **小内存占用**: 降低云成本
5. **快速启动**: 适合容器化部署

**与其他语言对比**:

| 特性 | Rust | Go | Java | Node.js |
|------|------|----|----|---------|
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |
| **内存占用** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ |
| **开发速度** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **生态成熟度** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **安全性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |

### 核心技术栈

```text
┌─────────────────────────────────────────────────────────────┐
│                        API 网关                              │
│                    (Axum + Tower)                           │
└─────────────────────────────────────────────────────────────┘
                              │
        ┌─────────────────────┼─────────────────────┐
        │                     │                     │
┌───────▼────────┐   ┌────────▼─────────┐  ┌───────▼────────┐
│  用户服务       │   │   订单服务        │  │  产品服务       │
│  (Axum)        │   │   (Axum)         │  │  (Axum)        │
│  PostgreSQL    │   │   PostgreSQL     │  │  PostgreSQL    │
└────────────────┘   └──────────────────┘  └────────────────┘
        │                     │                     │
        └─────────────────────┼─────────────────────┘
                              │
                    ┌─────────▼──────────┐
                    │    消息队列         │
                    │    (Kafka/NATS)    │
                    └────────────────────┘
```

**核心依赖**:

```toml
# 共享依赖
[workspace.dependencies]
# Web 框架
axum = { version = "0.7", features = ["macros"] }
tower = { version = "0.4", features = ["full"] }
tower-http = { version = "0.5", features = ["full"] }

# 异步运行时
tokio = { version = "1", features = ["full"] }

# 数据库
sqlx = { version = "0.7", features = ["postgres", "runtime-tokio"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# 日志和追踪
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
opentelemetry = "0.21"

# gRPC (服务间通信)
tonic = "0.11"
prost = "0.12"

# 消息队列
rdkafka = "0.36"

# 认证
jsonwebtoken = "9"
```

---

## 架构设计

### 整体架构

```text
┌──────────────────────────────────────────────────────────────────┐
│                         负载均衡器                                 │
│                      (Nginx/Traefik)                             │
└───────────────────────────┬──────────────────────────────────────┘
                            │
┌───────────────────────────▼──────────────────────────────────────┐
│                        API 网关                                   │
│  • 路由转发                                                       │
│  • 认证鉴权                                                       │
│  • 限流熔断                                                       │
│  • 请求聚合                                                       │
└───────────────────────────┬──────────────────────────────────────┘
                            │
        ┌───────────────────┼───────────────────┐
        │                   │                   │
┌───────▼────────┐  ┌───────▼────────┐  ┌──────▼─────────┐
│  用户服务       │  │  订单服务       │  │  产品服务       │
│  • 注册/登录    │  │  • 创建订单     │  │  • 商品管理     │
│  • 用户信息     │  │  • 订单查询     │  │  • 库存管理     │
│  • 权限管理     │  │  • 订单状态     │  │  • 价格管理     │
└────────┬───────┘  └────────┬───────┘  └────────┬───────┘
         │                   │                   │
┌────────▼───────────────────▼───────────────────▼───────┐
│                    消息队列 (Event Bus)                 │
│              Kafka / NATS / RabbitMQ                   │
└────────────────────────────────────────────────────────┘
         │                   │                   │
┌────────▼───────┐  ┌────────▼───────┐  ┌───────▼────────┐
│  PostgreSQL    │  │  PostgreSQL    │  │  PostgreSQL    │
│  (用户数据库)   │  │  (订单数据库)   │  │  (产品数据库)   │
└────────────────┘  └────────────────┘  └────────────────┘
```

### 服务划分原则

**1. 按业务能力划分 (DDD)**:

```text
用户域 (User Domain)
├─ 用户服务 (User Service)
│  ├─ 用户注册
│  ├─ 用户认证
│  └─ 用户信息管理
│
订单域 (Order Domain)
├─ 订单服务 (Order Service)
│  ├─ 订单创建
│  ├─ 订单支付
│  └─ 订单查询
│
产品域 (Product Domain)
└─ 产品服务 (Product Service)
   ├─ 商品管理
   ├─ 库存管理
   └─ 价格管理
```

**2. 服务规模**:

- **小服务** (1-3 人维护): 单一职责
- **中等服务** (3-5 人): 相关功能聚合
- **大服务** (5+ 人): 可进一步拆分

### 通信模式

**1. 同步通信 (REST/gRPC)**:

```rust
// REST API (外部访问)
GET  /api/users/:id
POST /api/users
PUT  /api/users/:id

// gRPC (服务间通信)
service UserService {
  rpc GetUser (GetUserRequest) returns (User);
  rpc CreateUser (CreateUserRequest) returns (User);
}
```

**2. 异步通信 (消息队列)**:

```rust
// 事件发布
OrderCreatedEvent {
    order_id: "ORD-001",
    user_id: "USR-123",
    total: 99.99
}

// 事件订阅
订单服务 --发布--> OrderCreatedEvent --订阅--> 库存服务
                                    └───订阅--> 支付服务
                                    └───订阅--> 通知服务
```

---

## 核心组件

### 1. API 网关

**职责**:

- 路由转发
- 认证鉴权
- 限流熔断
- 请求聚合
- 协议转换

**实现 (Axum + Tower)**:

```rust
use axum::{Router, routing::get, middleware};
use tower::ServiceBuilder;
use tower_http::{
    trace::TraceLayer,
    cors::CorsLayer,
    compression::CompressionLayer,
};

#[tokio::main]
async fn main() {
    let app = Router::new()
        // 用户服务路由
        .nest("/api/users", user_routes())
        // 订单服务路由
        .nest("/api/orders", order_routes())
        // 产品服务路由
        .nest("/api/products", product_routes())
        // 中间件
        .layer(
            ServiceBuilder::new()
                .layer(TraceLayer::new_for_http())
                .layer(middleware::from_fn(auth_middleware))
                .layer(CompressionLayer::new())
                .layer(CorsLayer::permissive())
        );
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080")
        .await
        .unwrap();
    
    axum::serve(listener, app).await.unwrap();
}

// 认证中间件
async fn auth_middleware(
    req: axum::extract::Request,
    next: axum::middleware::Next,
) -> Result<axum::response::Response, axum::http::StatusCode> {
    // JWT 验证逻辑
    let auth_header = req.headers()
        .get("authorization")
        .and_then(|h| h.to_str().ok())
        .ok_or(axum::http::StatusCode::UNAUTHORIZED)?;
    
    // 验证 token...
    
    Ok(next.run(req).await)
}
```

**服务代理**:

```rust
use axum::response::IntoResponse;
use reqwest::Client;

async fn proxy_to_user_service(
    path: String,
) -> impl IntoResponse {
    let client = Client::new();
    let response = client
        .get(format!("http://user-service:3000{}", path))
        .send()
        .await
        .unwrap();
    
    (response.status(), response.text().await.unwrap())
}
```

### 2. 服务注册与发现

**方案选择**:

| 方案 | 优点 | 缺点 |
|------|------|------|
| **Consul** | 功能完整、健康检查 | 复杂度高 |
| **Etcd** | 高性能、强一致性 | 需要手动实现 |
| **Kubernetes Service** | 原生支持、简单 | 依赖 K8s |

**Kubernetes 原生方案**:

```yaml
# user-service.yaml
apiVersion: v1
kind: Service
metadata:
  name: user-service
spec:
  selector:
    app: user-service
  ports:
    - protocol: TCP
      port: 80
      targetPort: 3000
```

**服务发现 (通过 DNS)**:

```rust
// 服务间调用
let user_service_url = "http://user-service";
let client = reqwest::Client::new();
let response = client
    .get(format!("{}/users/{}", user_service_url, user_id))
    .send()
    .await?;
```

### 3. 配置中心

**方案**: 环境变量 + ConfigMap (Kubernetes)

```rust
use config::{Config, ConfigError, Environment, File};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct Settings {
    pub database: DatabaseSettings,
    pub redis: RedisSettings,
    pub kafka: KafkaSettings,
}

#[derive(Debug, Deserialize)]
pub struct DatabaseSettings {
    pub host: String,
    pub port: u16,
    pub username: String,
    pub password: String,
    pub database: String,
}

impl Settings {
    pub fn new() -> Result<Self, ConfigError> {
        Config::builder()
            // 默认配置
            .add_source(File::with_name("config/default"))
            // 环境特定配置
            .add_source(
                File::with_name(&format!("config/{}", 
                    std::env::var("RUN_ENV").unwrap_or_else(|_| "dev".into())
                ))
                .required(false)
            )
            // 环境变量覆盖 (APP_DATABASE__HOST=...)
            .add_source(Environment::with_prefix("APP").separator("__"))
            .build()?
            .try_deserialize()
    }
}
```

**ConfigMap (K8s)**:

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: user-service-config
data:
  DATABASE_HOST: postgres-service
  DATABASE_PORT: "5432"
  REDIS_HOST: redis-service
```

### 4. 消息队列

**Kafka 示例**:

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord};
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
pub struct OrderCreatedEvent {
    pub order_id: String,
    pub user_id: String,
    pub total: f64,
    pub timestamp: i64,
}

pub struct EventPublisher {
    producer: FutureProducer,
}

impl EventPublisher {
    pub fn new(brokers: &str) -> Self {
        let producer: FutureProducer = ClientConfig::new()
            .set("bootstrap.servers", brokers)
            .set("message.timeout.ms", "5000")
            .create()
            .expect("Producer creation error");
        
        Self { producer }
    }
    
    pub async fn publish_order_created(
        &self,
        event: OrderCreatedEvent,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let payload = serde_json::to_string(&event)?;
        
        self.producer
            .send(
                FutureRecord::to("order-events")
                    .key(&event.order_id)
                    .payload(&payload),
                std::time::Duration::from_secs(0),
            )
            .await
            .map_err(|(e, _)| e)?;
        
        Ok(())
    }
}
```

**事件消费**:

```rust
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::config::ClientConfig;
use rdkafka::Message;
use futures::StreamExt;

pub async fn consume_order_events() -> Result<(), Box<dyn std::error::Error>> {
    let consumer: StreamConsumer = ClientConfig::new()
        .set("group.id", "inventory-service")
        .set("bootstrap.servers", "localhost:9092")
        .set("enable.auto.commit", "true")
        .create()?;
    
    consumer.subscribe(&["order-events"])?;
    
    let mut message_stream = consumer.stream();
    
    while let Some(message) = message_stream.next().await {
        match message {
            Ok(m) => {
                let payload = m.payload_view::<str>().unwrap().unwrap();
                let event: OrderCreatedEvent = serde_json::from_str(payload)?;
                
                // 处理事件
                handle_order_created(event).await?;
            }
            Err(e) => eprintln!("Kafka error: {}", e),
        }
    }
    
    Ok(())
}

async fn handle_order_created(event: OrderCreatedEvent) -> Result<(), Box<dyn std::error::Error>> {
    // 业务逻辑: 扣减库存
    println!("处理订单创建事件: {:?}", event);
    Ok(())
}
```

---

## 服务实现

### 用户服务 (User Service)

**目录结构**:

```text
user-service/
├── Cargo.toml
├── src/
│   ├── main.rs
│   ├── config.rs
│   ├── models/
│   │   └── user.rs
│   ├── handlers/
│   │   └── user_handler.rs
│   ├── repositories/
│   │   └── user_repository.rs
│   └── services/
│       └── user_service.rs
└── migrations/
    └── 001_create_users_table.sql
```

**核心代码**:

```rust
// src/models/user.rs
use serde::{Serialize, Deserialize};
use sqlx::FromRow;

#[derive(Debug, Serialize, Deserialize, FromRow)]
pub struct User {
    pub id: i32,
    pub username: String,
    pub email: String,
    #[serde(skip_serializing)]
    pub password_hash: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Deserialize)]
pub struct CreateUserRequest {
    pub username: String,
    pub email: String,
    pub password: String,
}

// src/repositories/user_repository.rs
use sqlx::{PgPool, query_as, query};

pub struct UserRepository {
    pool: PgPool,
}

impl UserRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
    
    pub async fn find_by_id(&self, id: i32) -> Result<Option<User>, sqlx::Error> {
        query_as!(User, "SELECT * FROM users WHERE id = $1", id)
            .fetch_optional(&self.pool)
            .await
    }
    
    pub async fn create(&self, req: CreateUserRequest) -> Result<User, sqlx::Error> {
        let password_hash = hash_password(&req.password);
        
        query_as!(
            User,
            "INSERT INTO users (username, email, password_hash) VALUES ($1, $2, $3) RETURNING *",
            req.username,
            req.email,
            password_hash
        )
        .fetch_one(&self.pool)
        .await
    }
}

fn hash_password(password: &str) -> String {
    // 使用 argon2 或 bcrypt
    format!("hashed_{}", password)
}

// src/handlers/user_handler.rs
use axum::{Json, extract::{Path, State}};
use axum::http::StatusCode;

pub async fn get_user(
    Path(id): Path<i32>,
    State(repo): State<Arc<UserRepository>>,
) -> Result<Json<User>, StatusCode> {
    repo.find_by_id(id)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        .map(Json)
        .ok_or(StatusCode::NOT_FOUND)
}

pub async fn create_user(
    State(repo): State<Arc<UserRepository>>,
    Json(req): Json<CreateUserRequest>,
) -> Result<(StatusCode, Json<User>), StatusCode> {
    let user = repo.create(req)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    Ok((StatusCode::CREATED, Json(user)))
}

// src/main.rs
use axum::{Router, routing::{get, post}};
use sqlx::postgres::PgPoolOptions;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let pool = PgPoolOptions::new()
        .max_connections(5)
        .connect("postgres://user:password@localhost/userdb")
        .await
        .unwrap();
    
    let repo = Arc::new(UserRepository::new(pool));
    
    let app = Router::new()
        .route("/users/:id", get(get_user))
        .route("/users", post(create_user))
        .with_state(repo);
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    println!("用户服务运行在 :3000");
    axum::serve(listener, app).await.unwrap();
}
```

### 订单服务 (Order Service)

**核心逻辑**:

```rust
// src/services/order_service.rs
use crate::models::{Order, CreateOrderRequest};
use crate::repositories::OrderRepository;
use crate::events::EventPublisher;

pub struct OrderService {
    repo: Arc<OrderRepository>,
    event_publisher: Arc<EventPublisher>,
}

impl OrderService {
    pub async fn create_order(
        &self,
        req: CreateOrderRequest,
    ) -> Result<Order, Box<dyn std::error::Error>> {
        // 1. 创建订单
        let order = self.repo.create(req).await?;
        
        // 2. 发布事件
        self.event_publisher.publish_order_created(OrderCreatedEvent {
            order_id: order.id.clone(),
            user_id: order.user_id.clone(),
            total: order.total,
            timestamp: chrono::Utc::now().timestamp(),
        }).await?;
        
        Ok(order)
    }
}
```

---

## 横切关注点

### 1. 认证与授权

**JWT 实现**:

```rust
use jsonwebtoken::{encode, decode, Header, Validation, EncodingKey, DecodingKey};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String,  // 用户 ID
    pub role: String,  // 角色
    pub exp: usize,   // 过期时间
}

pub fn generate_token(user_id: &str, role: &str) -> String {
    let claims = Claims {
        sub: user_id.to_string(),
        role: role.to_string(),
        exp: (chrono::Utc::now() + chrono::Duration::hours(24)).timestamp() as usize,
    };
    
    encode(
        &Header::default(),
        &claims,
        &EncodingKey::from_secret("secret".as_ref())
    ).unwrap()
}

pub fn verify_token(token: &str) -> Result<Claims, jsonwebtoken::errors::Error> {
    decode::<Claims>(
        token,
        &DecodingKey::from_secret("secret".as_ref()),
        &Validation::default()
    ).map(|data| data.claims)
}
```

### 2. 分布式追踪

**OpenTelemetry + Jaeger**:

```rust
use opentelemetry::{global, sdk::propagation::TraceContextPropagator};
use tracing_subscriber::layer::SubscriberExt;

pub fn init_tracing() {
    global::set_text_map_propagator(TraceContextPropagator::new());
    
    let tracer = opentelemetry_jaeger::new_agent_pipeline()
        .with_service_name("user-service")
        .install_simple()
        .unwrap();
    
    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    
    let subscriber = tracing_subscriber::Registry::default()
        .with(telemetry);
    
    tracing::subscriber::set_global_default(subscriber).unwrap();
}

// 使用
#[tracing::instrument]
async fn get_user(id: i32) -> Result<User, Error> {
    // 自动追踪
    repository.find_by_id(id).await
}
```

### 3. 日志聚合

**Structured Logging**:

```rust
use tracing::{info, error, warn};

#[tracing::instrument(skip(repo))]
async fn create_order(
    repo: &OrderRepository,
    req: CreateOrderRequest,
) -> Result<Order, Error> {
    info!(user_id = %req.user_id, "Creating order");
    
    match repo.create(req).await {
        Ok(order) => {
            info!(order_id = %order.id, "Order created successfully");
            Ok(order)
        }
        Err(e) => {
            error!(error = %e, "Failed to create order");
            Err(e)
        }
    }
}
```

### 4. 健康检查

```rust
use axum::{Json, routing::get};
use serde::Serialize;

#[derive(Serialize)]
struct HealthResponse {
    status: String,
    database: String,
    redis: String,
}

async fn health_check(
    State(pool): State<PgPool>,
    State(redis): State<redis::Client>,
) -> Json<HealthResponse> {
    let db_status = match sqlx::query("SELECT 1").fetch_one(&pool).await {
        Ok(_) => "healthy",
        Err(_) => "unhealthy",
    };
    
    let redis_status = match redis.get_connection() {
        Ok(_) => "healthy",
        Err(_) => "unhealthy",
    };
    
    Json(HealthResponse {
        status: "up".to_string(),
        database: db_status.to_string(),
        redis: redis_status.to_string(),
    })
}
```

---

## 数据管理

### 数据库per服务

**原则**: 每个服务拥有独立的数据库

```text
user-service    → user_db (PostgreSQL)
order-service   → order_db (PostgreSQL)
product-service → product_db (PostgreSQL)
```

### 分布式事务

**Saga 模式 (补偿事务)**:

```rust
pub async fn create_order_saga(
    order_req: CreateOrderRequest,
) -> Result<Order, SagaError> {
    // 步骤1: 创建订单
    let order = order_service.create_order(&order_req).await?;
    
    // 步骤2: 扣减库存
    match inventory_service.reserve_items(&order.items).await {
        Ok(_) => {},
        Err(e) => {
            // 补偿: 取消订单
            order_service.cancel_order(&order.id).await?;
            return Err(e.into());
        }
    }
    
    // 步骤3: 创建支付
    match payment_service.create_payment(&order).await {
        Ok(_) => {},
        Err(e) => {
            // 补偿: 释放库存
            inventory_service.release_items(&order.items).await?;
            // 补偿: 取消订单
            order_service.cancel_order(&order.id).await?;
            return Err(e.into());
        }
    }
    
    Ok(order)
}
```

### 事件溯源

```rust
#[derive(Serialize, Deserialize)]
pub enum OrderEvent {
    Created { order_id: String, user_id: String, total: f64 },
    Paid { order_id: String, payment_id: String },
    Shipped { order_id: String, tracking_number: String },
    Delivered { order_id: String },
    Cancelled { order_id: String, reason: String },
}

pub struct OrderAggregate {
    pub id: String,
    pub status: OrderStatus,
    pub events: Vec<OrderEvent>,
}

impl OrderAggregate {
    pub fn apply_event(&mut self, event: OrderEvent) {
        match event {
            OrderEvent::Created { .. } => {
                self.status = OrderStatus::Pending;
            }
            OrderEvent::Paid { .. } => {
                self.status = OrderStatus::Paid;
            }
            OrderEvent::Shipped { .. } => {
                self.status = OrderStatus::Shipped;
            }
            OrderEvent::Delivered { .. } => {
                self.status = OrderStatus::Delivered;
            }
            OrderEvent::Cancelled { .. } => {
                self.status = OrderStatus::Cancelled;
            }
        }
        self.events.push(event);
    }
}
```

---

## 部署架构

### Kubernetes 部署

**用户服务部署配置**:

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: user-service
spec:
  replicas: 3
  selector:
    matchLabels:
      app: user-service
  template:
    metadata:
      labels:
        app: user-service
    spec:
      containers:
      - name: user-service
        image: user-service:latest
        ports:
        - containerPort: 3000
        env:
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: user-service-secret
              key: database-url
        resources:
          requests:
            memory: "64Mi"
            cpu: "100m"
          limits:
            memory: "128Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 3000
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /health
            port: 3000
          initialDelaySeconds: 5
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: user-service
spec:
  selector:
    app: user-service
  ports:
  - protocol: TCP
    port: 80
    targetPort: 3000
```

### Docker Compose (开发环境)

```yaml
version: '3.8'

services:
  postgres:
    image: postgres:16
    environment:
      POSTGRES_PASSWORD: password
    ports:
      - "5432:5432"
  
  redis:
    image: redis:7
    ports:
      - "6379:6379"
  
  kafka:
    image: confluentinc/cp-kafka:latest
    ports:
      - "9092:9092"
    environment:
      KAFKA_ADVERTISED_LISTENERS: PLAINTEXT://localhost:9092
  
  user-service:
    build: ./user-service
    ports:
      - "3001:3000"
    environment:
      DATABASE_URL: postgres://postgres:password@postgres/userdb
      REDIS_URL: redis://redis:6379
    depends_on:
      - postgres
      - redis
  
  order-service:
    build: ./order-service
    ports:
      - "3002:3000"
    environment:
      DATABASE_URL: postgres://postgres:password@postgres/orderdb
      KAFKA_BROKERS: kafka:9092
    depends_on:
      - postgres
      - kafka
```

---

## 监控与告警

### 指标收集

**Prometheus + Grafana**:

```rust
use prometheus::{Counter, Histogram, Encoder, TextEncoder};
use axum::{response::IntoResponse, routing::get};

lazy_static! {
    static ref HTTP_REQUESTS: Counter = Counter::new(
        "http_requests_total",
        "Total HTTP requests"
    ).unwrap();
    
    static ref HTTP_DURATION: Histogram = Histogram::new(
        "http_request_duration_seconds",
        "HTTP request duration"
    ).unwrap();
}

async fn metrics_handler() -> impl IntoResponse {
    let encoder = TextEncoder::new();
    let metric_families = prometheus::gather();
    let mut buffer = vec![];
    encoder.encode(&metric_families, &mut buffer).unwrap();
    String::from_utf8(buffer).unwrap()
}

// 使用
#[tracing::instrument]
async fn handle_request() {
    HTTP_REQUESTS.inc();
    let timer = HTTP_DURATION.start_timer();
    
    // 处理请求...
    
    timer.observe_duration();
}
```

### 告警规则

**Prometheus Alert Rules**:

```yaml
groups:
  - name: microservices
    rules:
      - alert: HighErrorRate
        expr: rate(http_requests_total{status=~"5.."}[5m]) > 0.05
        for: 5m
        annotations:
          summary: "High error rate detected"
      
      - alert: SlowResponseTime
        expr: http_request_duration_seconds{quantile="0.99"} > 1
        for: 5m
        annotations:
          summary: "Slow response time"
      
      - alert: ServiceDown
        expr: up{job="user-service"} == 0
        for: 1m
        annotations:
          summary: "Service is down"
```

---

## 最佳实践

### 1. 服务设计

**✅ 推荐**:

- 单一职责: 每个服务只做一件事
- 松耦合: 服务间通过API通信
- 高内聚: 相关功能在同一服务

**❌ 避免**:

- 服务过细导致网络开销
- 服务间直接数据库访问
- 循环依赖

### 2. API 设计

**✅ 推荐**:

```rust
// RESTful API
GET    /api/v1/users/:id
POST   /api/v1/users
PUT    /api/v1/users/:id
DELETE /api/v1/users/:id

// 版本控制
/api/v1/...
/api/v2/...
```

### 3. 错误处理

**✅ 推荐**:

```rust
#[derive(Debug, thiserror::Error)]
pub enum ServiceError {
    #[error("User not found: {0}")]
    NotFound(String),
    
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),
    
    #[error("Invalid input: {0}")]
    Validation(String),
}

impl IntoResponse for ServiceError {
    fn into_response(self) -> Response {
        let (status, message) = match self {
            ServiceError::NotFound(msg) => (StatusCode::NOT_FOUND, msg),
            ServiceError::Database(_) => (
                StatusCode::INTERNAL_SERVER_ERROR,
                "Internal error".to_string()
            ),
            ServiceError::Validation(msg) => (StatusCode::BAD_REQUEST, msg),
        };
        
        (status, Json(serde_json::json!({ "error": message }))).into_response()
    }
}
```

### 4. 性能优化

**✅ 推荐**:

- 连接池复用
- 缓存热点数据
- 异步非阻塞IO
- 批量操作

```rust
// 连接池
let pool = PgPoolOptions::new()
    .max_connections(10)
    .connect(&database_url)
    .await?;

// 缓存
let cached_user = redis_client
    .get::<_, Option<String>>(format!("user:{}", user_id))
    .await?;
```

### 5. 安全性

**✅ 推荐**:

- HTTPS 传输
- JWT 认证
- SQL 注入防护 (使用参数化查询)
- 限流防护

```rust
// 限流
use tower::limit::RateLimitLayer;
use std::time::Duration;

let app = Router::new()
    .route("/api/users", get(get_users))
    .layer(RateLimitLayer::new(100, Duration::from_secs(1)));
```

---

## 常见陷阱

### 陷阱1: 服务粒度过细

**错误**:

```text
用户服务 → 拆分成：
  ├─ 用户注册服务
  ├─ 用户登录服务
  ├─ 用户信息服务
  └─ 用户权限服务  ❌ 过度拆分
```

**正确**:

```text
用户服务 (统一管理用户相关功能) ✅
```

### 陷阱2: 忽略网络分区

**错误**:

```rust
// 直接调用，不处理网络故障
let user = user_service_client.get_user(user_id).await.unwrap();  // ❌
```

**正确**:

```rust
// 重试 + 熔断
let user = retry_with_backoff(|| {
    user_service_client.get_user(user_id)
}).await?;  // ✅
```

### 陷阱3: 缺少熔断机制

**正确实现**:

```rust
use tower::retry::RetryLayer;
use tower::timeout::TimeoutLayer;
use std::time::Duration;

let app = Router::new()
    .layer(TimeoutLayer::new(Duration::from_secs(5)))
    .layer(RetryLayer::new(/* retry policy */));
```

---

## 完整示例项目

**项目地址**: `https://github.com/example/rust-microservices-demo`

**目录结构**:

```text
rust-microservices/
├── api-gateway/
├── user-service/
├── order-service/
├── product-service/
├── shared/
│   ├── models/
│   ├── utils/
│   └── proto/
├── docker-compose.yml
└── k8s/
    ├── deployments/
    ├── services/
    └── ingress/
```

---

## 参考资源

**官方文档**:

- **Axum**: <https://docs.rs/axum/>
- **Tokio**: <https://tokio.rs/>
- **SQLx**: <https://docs.rs/sqlx/>

**深度文章**:

- [微服务架构设计模式](https://microservices.io/patterns/)
- [Building Microservices with Rust](https://blog.logrocket.com/building-microservices-rust/)
- [Rust 异步编程指南](https://rust-lang.github.io/async-book/)

**视频教程**:

- [Rust 微服务实战](https://www.youtube.com/watch?v=...)

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20  
**贡献者**: Rust 学习社区

**下一步**: [性能优化手册](./RUST_PERFORMANCE_OPTIMIZATION_2025.md) | [部署指南](./RUST_DEPLOYMENT_GUIDE_2025.md)
