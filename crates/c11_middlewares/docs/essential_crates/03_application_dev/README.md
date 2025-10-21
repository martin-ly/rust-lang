# 第3层：应用开发层 (Application Development Layer)

> **定位**: 构建生产级应用所需的 Web、数据库、消息队列等核心组件  
> **特点**: 完整生态、生产就绪、最佳实践  
> **版本**: Rust 1.90 (2025)

---

## 📋 目录

- [层级概述](#层级概述)
  - [核心价值](#核心价值)
  - [技术栈矩阵](#技术栈矩阵)
- [核心类别](#核心类别)
  - [1. Web 框架](#1-web-框架-web_frameworks)
  - [2. HTTP 客户端](#2-http-客户端-http_clients)
  - [3. 数据库 ORM](#3-数据库-orm-databases)
  - [4. 消息队列](#4-消息队列-message_queues)
  - [5. 缓存](#5-缓存-caching)
  - [6. gRPC](#6-grpc-grpc)
  - [7. 认证授权](#7-认证授权-auth)
  - [8. 测试](#8-测试-testing)
  - [9. CLI 工具](#9-cli-工具-cli_tools)
  - [10. 模板引擎](#10-模板引擎-template)
- [场景快速启动](#场景快速启动)
  - [REST API 服务](#rest-api-服务)
  - [微服务架构](#微服务架构)
  - [全栈 Web 应用](#全栈-web-应用)
- [技术选型指南](#技术选型指南)
  - [Web 框架选择](#web-框架选择)
  - [数据库选择](#数据库选择)
  - [消息队列选择](#消息队列选择)
- [最佳实践](#最佳实践)
- [参考资源](#参考资源)

---

## 层级概述

### 核心价值

**应用开发层** 提供构建生产级应用的完整工具链，从 Web 框架到数据库、消息队列，覆盖现代应用开发的所有核心需求。

**关键特性**:

1. **类型安全**: 编译期检查，减少运行时错误
2. **高性能**: 媲美 C/C++，超越 Java/Go
3. **完整生态**: 从 Web 到数据库到消息队列
4. **生产就绪**: 经过大规模验证（Discord, AWS, Cloudflare）

**典型应用场景**:

- 🌐 Web 应用（REST API、GraphQL、WebSocket）
- 🔧 微服务架构（gRPC、服务网格）
- 📊 实时数据处理（流式、事件驱动）
- 🎯 企业后端（ERP、CRM、金融系统）
- 🚀 SaaS 平台（多租户、高可用）

### 技术栈矩阵

**按应用类型分类**:

| 应用类型 | Web 框架 | 数据库 | 消息队列 | 其他 |
|---------|---------|-------|---------|------|
| **REST API** | axum, actix-web | sqlx, diesel | - | serde, jsonwebtoken |
| **微服务** | tonic | sqlx | rdkafka, nats | tracing, prometheus |
| **全栈 Web** | axum, rocket | sqlx | - | askama, tower-sessions |
| **实时应用** | axum + ws | sqlx | redis | tokio, tower |
| **CLI 工具** | - | - | - | clap, dialoguer |

**按团队规模分类**:

| 团队规模 | 推荐栈 | 特点 |
|---------|-------|------|
| **小团队** (1-5人) | axum + sqlx + redis | 快速开发、易维护 |
| **中团队** (5-20人) | actix-web + diesel + kafka | 成熟稳定、生态好 |
| **大团队** (20+人) | 自定义栈 + 内部工具 | 定制化、规模化 |

---

## 核心类别

### 1. Web 框架 ([`web_frameworks/`](./web_frameworks/))

**对比矩阵**:

| 框架 | 特点 | 性能 | 学习曲线 | 生态 | 推荐度 |
|------|------|------|----------|------|--------|
| **axum** | 基于 tower, 类型安全 | ⚡⚡⚡⚡⚡ | 低 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **actix-web** | 成熟稳定, Actor 模型 | ⚡⚡⚡⚡⚡ | 中 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **rocket** | 易用, 功能全 | ⚡⚡⚡⚡ | 低 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |

**快速示例** (axum):

```rust
use axum::{Router, routing::{get, post}, Json};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct User {
    id: u32,
    name: String,
}

async fn get_user() -> Json<User> {
    Json(User { id: 1, name: "Alice".to_string() })
}

async fn create_user(Json(user): Json<User>) -> Json<User> {
    // 保存到数据库...
    Json(user)
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/users/:id", get(get_user))
        .route("/users", post(create_user));
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

**性能数据**:

- **axum**: 240K-295K req/s (单核)
- **actix-web**: 250K-300K req/s (单核)
- **rocket**: 180K-220K req/s (单核)

**选择建议**:

- **选 axum**: 新项目、需要 tower 生态、追求类型安全
- **选 actix-web**: 成熟项目、需要稳定性、大规模部署
- **选 rocket**: 快速原型、学习 Rust Web、中小型项目

**详细文档**: [`web_frameworks/README.md`](./web_frameworks/)

---

### 2. HTTP 客户端 ([`http_clients/`](./http_clients/))

**对比矩阵**:

| 库名 | 层次 | 特点 | 学习曲线 | 推荐度 |
|------|------|------|----------|--------|
| **reqwest** | 高级 API | 易用、功能全 | 低 | ⭐⭐⭐⭐⭐ |
| **hyper** | 底层 | 高性能、灵活 | 高 | ⭐⭐⭐⭐⭐ |
| **ureq** | 同步 | 简单、阻塞式 | 极低 | ⭐⭐⭐⭐ |

**快速示例** (reqwest):

```rust
use reqwest;
use serde::Deserialize;

#[derive(Deserialize)]
struct ApiResponse {
    origin: String,
}

#[tokio::main]
async fn main() -> Result<(), reqwest::Error> {
    // GET 请求
    let res = reqwest::get("https://httpbin.org/ip")
        .await?
        .json::<ApiResponse>()
        .await?;
    
    println!("Your IP: {}", res.origin);
    
    // POST 请求
    let client = reqwest::Client::new();
    let response = client
        .post("https://httpbin.org/post")
        .json(&serde_json::json!({
            "name": "Alice",
            "age": 30
        }))
        .send()
        .await?;
    
    println!("Status: {}", response.status());
    
    Ok(())
}
```

**详细文档**: [`http_clients/README.md`](./http_clients/)

---

### 3. 数据库 ORM ([`databases/`](./databases/))

**对比矩阵**:

| 库名 | 类型 | 异步 | 编译期检查 | 学习曲线 | 推荐度 |
|------|------|------|-----------|----------|--------|
| **sqlx** | Query Builder | ✅ | ✅ (SQL) | 低 | ⭐⭐⭐⭐⭐ |
| **diesel** | 完整 ORM | ❌ (v2.2+) | ✅ (DSL) | 中 | ⭐⭐⭐⭐⭐ |
| **sea-orm** | 异步 ORM | ✅ | ✅ (DSL) | 中 | ⭐⭐⭐⭐ |
| **mongodb** | NoSQL | ✅ | ❌ | 低 | ⭐⭐⭐⭐ |

**快速示例** (sqlx + PostgreSQL):

```rust
use sqlx::postgres::PgPoolOptions;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, sqlx::FromRow)]
struct User {
    id: i32,
    name: String,
    email: String,
}

#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    // 连接池
    let pool = PgPoolOptions::new()
        .max_connections(5)
        .connect("postgres://user:pass@localhost/mydb").await?;
    
    // 编译期检查的查询（需要 DATABASE_URL 环境变量）
    let users = sqlx::query_as::<_, User>("SELECT id, name, email FROM users")
        .fetch_all(&pool)
        .await?;
    
    for user in users {
        println!("{}: {} ({})", user.id, user.name, user.email);
    }
    
    // 插入数据
    let result = sqlx::query(
        "INSERT INTO users (name, email) VALUES ($1, $2) RETURNING id"
    )
    .bind("Bob")
    .bind("bob@example.com")
    .fetch_one(&pool)
    .await?;
    
    println!("Inserted user with ID: {}", result.get::<i32, _>("id"));
    
    Ok(())
}
```

**性能对比** (1000 次查询):

| 操作 | sqlx | diesel | sea-orm |
|------|------|--------|---------|
| 简单查询 | 12ms | 15ms | 18ms |
| 复杂联表 | 45ms | 40ms | 50ms |
| 批量插入 | 80ms | 85ms | 90ms |

**详细文档**: [`databases/README.md`](./databases/)

---

### 4. 消息队列 ([`message_queues/`](./message_queues/))

**对比矩阵**:

| 库名 | MQ | 特点 | 学习曲线 | 推荐度 |
|------|------|------|----------|--------|
| **rdkafka** | Kafka | 高吞吐、持久化 | 中 | ⭐⭐⭐⭐⭐ |
| **lapin** | RabbitMQ | 灵活路由、可靠 | 中 | ⭐⭐⭐⭐ |
| **async-nats** | NATS | 轻量、云原生 | 低 | ⭐⭐⭐⭐ |

**使用场景**:

- **Kafka**: 大数据、日志聚合、事件溯源
- **RabbitMQ**: 任务队列、RPC、复杂路由
- **NATS**: 微服务通信、IoT、边缘计算

**详细文档**: [`message_queues/README.md`](./message_queues/)

---

### 5. 缓存 ([`caching/`](./caching/))

**对比矩阵**:

| 库名 | 类型 | 特点 | 推荐度 |
|------|------|------|--------|
| **redis** | 远程缓存 | 功能全、分布式 | ⭐⭐⭐⭐⭐ |
| **moka** | 内存缓存 | 高性能、LRU/LFU | ⭐⭐⭐⭐ |
| **cached** | 内存缓存 | 简单、宏友好 | ⭐⭐⭐⭐ |

**使用场景**:

- **Redis**: 分布式缓存、会话存储、排行榜
- **moka**: 本地缓存、高频访问、低延迟
- **cached**: 函数级缓存、简单场景

**详细文档**: [`caching/README.md`](./caching/)

---

### 6. gRPC ([`grpc/`](./grpc/))

**核心库**:

| 库名 | 用途 | 推荐度 |
|------|------|--------|
| **tonic** | gRPC 服务端/客户端 | ⭐⭐⭐⭐⭐ |
| **prost** | Protobuf 编解码 | ⭐⭐⭐⭐⭐ |
| **tonic-build** | 代码生成 | ⭐⭐⭐⭐⭐ |

**详细文档**: [`grpc/README.md`](./grpc/)

---

### 7. 认证授权 ([`auth/`](./auth/))

**核心库**:

- **jsonwebtoken**: JWT 生成和验证
- **oauth2**: OAuth 2.0 客户端
- **argon2**: 密码哈希
- **tower-sessions**: 会话管理

**详细文档**: [`auth/README.md`](./auth/)

---

### 8. 测试 ([`testing/`](./testing/))

**核心库**:

- **criterion**: 基准测试
- **proptest**: 属性测试
- **mockall**: Mock 框架
- **wiremock**: HTTP Mock
- **rstest**: 参数化测试

**详细文档**: [`testing/README.md`](./testing/)

---

### 9. CLI 工具 ([`cli_tools/`](./cli_tools/))

**核心库**:

- **clap**: 参数解析
- **dialoguer**: 交互输入
- **indicatif**: 进度条
- **console**: 终端控制

**详细文档**: [`cli_tools/README.md`](./cli_tools/)

---

### 10. 模板引擎 ([`template/`](./template/))

**核心库**:

- **askama**: 编译期模板（类 Jinja2）
- **tera**: 运行时模板（类 Jinja2）

**详细文档**: [`template/README.md`](./template/)

---

## 场景快速启动

### REST API 服务

**技术栈**: axum + sqlx + redis + serde

**依赖配置**:

```toml
[dependencies]
# Web 框架
tokio = { version = "1", features = ["full"] }
axum = "0.7"
tower = "0.4"
tower-http = { version = "0.5", features = ["fs", "trace", "cors"] }

# 数据库
sqlx = { version = "0.8", features = ["runtime-tokio-rustls", "postgres"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 缓存
redis = { version = "0.24", features = ["tokio-comp"] }

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
```

**最小示例**:

```rust
use axum::{Router, routing::get, Json};
use serde::Serialize;

#[derive(Serialize)]
struct HealthCheck {
    status: String,
}

async fn health() -> Json<HealthCheck> {
    Json(HealthCheck { status: "ok".to_string() })
}

#[tokio::main]
async fn main() {
    let app = Router::new().route("/health", get(health));
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    println!("Server running on http://0.0.0.0:3000");
    axum::serve(listener, app).await.unwrap();
}
```

---

### 微服务架构

**技术栈**: tonic + sqlx + rdkafka + tracing

**依赖配置**:

```toml
[dependencies]
# gRPC
tokio = { version = "1", features = ["full"] }
tonic = "0.12"
prost = "0.13"

# 数据库
sqlx = { version = "0.8", features = ["runtime-tokio-rustls", "postgres"] }

# 消息队列
rdkafka = { version = "0.36", features = ["tokio"] }

# 可观测性
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
opentelemetry = "0.21"

[build-dependencies]
tonic-build = "0.12"
```

---

### 全栈 Web 应用

**技术栈**: axum + sqlx + askama + tower-sessions

**依赖配置**:

```toml
[dependencies]
tokio = { version = "1", features = ["full"] }
axum = "0.7"
sqlx = { version = "0.8", features = ["runtime-tokio-rustls", "postgres"] }
askama = "0.12"
tower-sessions = "0.12"
tower-sessions-sqlx-store = "0.12"
```

---

## 技术选型指南

### Web 框架选择

**决策树**:

```text
需要 Actor 模型？
├─ 是 → actix-web
└─ 否 → 需要最新特性？
   ├─ 是 → axum
   └─ 否 → 追求易用？
      ├─ 是 → rocket
      └─ 否 → axum (推荐)
```

### 数据库选择

**关系型数据库**:

| 场景 | 推荐 | 原因 |
|------|------|------|
| **新项目** | sqlx | 编译期检查、异步 |
| **复杂 ORM** | diesel | DSL 强大、类型安全 |
| **快速开发** | sea-orm | ActiveRecord 模式 |

**NoSQL**:

| 场景 | 推荐 | 原因 |
|------|------|------|
| **文档存储** | mongodb | 官方支持好 |
| **时序数据** | InfluxDB | 专用优化 |
| **图数据库** | neo4j | 生态成熟 |

### 消息队列选择

| 场景 | 推荐 | 原因 |
|------|------|------|
| **高吞吐** | Kafka (rdkafka) | 持久化、分区 |
| **灵活路由** | RabbitMQ (lapin) | Exchange 类型多 |
| **轻量级** | NATS (async-nats) | 简单、快速 |
| **实时通信** | Redis Streams | 低延迟 |

---

## 最佳实践

### 1. 分层架构

**描述**: 清晰的分层结构。

```text
src/
├── main.rs          # 入口
├── api/             # API 层（路由、处理器）
├── service/         # 业务逻辑层
├── repository/      # 数据访问层
├── model/           # 数据模型
└── config/          # 配置
```

### 2. 错误处理

**描述**: 统一的错误类型。

```rust
use axum::{http::StatusCode, response::{IntoResponse, Response}, Json};
use serde_json::json;

pub enum AppError {
    DatabaseError(sqlx::Error),
    NotFound,
    Unauthorized,
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, message) = match self {
            AppError::DatabaseError(e) => {
                (StatusCode::INTERNAL_SERVER_ERROR, e.to_string())
            }
            AppError::NotFound => {
                (StatusCode::NOT_FOUND, "Resource not found".to_string())
            }
            AppError::Unauthorized => {
                (StatusCode::UNAUTHORIZED, "Unauthorized".to_string())
            }
        };
        
        (status, Json(json!({ "error": message }))).into_response()
    }
}
```

### 3. 配置管理

**描述**: 使用环境变量和配置文件。

```rust
use serde::Deserialize;

#[derive(Deserialize)]
pub struct Config {
    pub database_url: String,
    pub redis_url: String,
    pub jwt_secret: String,
}

impl Config {
    pub fn from_env() -> Result<Self, config::ConfigError> {
        let config = config::Config::builder()
            .add_source(config::Environment::default())
            .build()?;
        
        config.try_deserialize()
    }
}
```

### 4. 依赖注入

**描述**: 使用 State 管理依赖。

```rust
#[derive(Clone)]
struct AppState {
    db: PgPool,
    redis: redis::Client,
}

async fn handler(
    State(state): State<AppState>,
) -> Json<Value> {
    // 使用 state.db 和 state.redis
}

#[tokio::main]
async fn main() {
    let state = AppState {
        db: PgPoolOptions::new().connect(&db_url).await.unwrap(),
        redis: redis::Client::open(redis_url).unwrap(),
    };
    
    let app = Router::new()
        .route("/", get(handler))
        .with_state(state);
}
```

### 5. 优雅关闭

**描述**: 正确处理关闭信号。

```rust
use tokio::signal;

#[tokio::main]
async fn main() {
    let app = Router::new();
    
    axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await
        .unwrap();
}

async fn shutdown_signal() {
    signal::ctrl_c()
        .await
        .expect("Failed to install CTRL+C signal handler");
    
    println!("Shutting down gracefully...");
}
```

---

## 参考资源

### 官方文档

- 📚 [Axum Guide](https://docs.rs/axum/latest/axum/)
- 📚 [SQLx Documentation](https://docs.rs/sqlx/latest/sqlx/)
- 📚 [Tokio Tutorial](https://tokio.rs/tokio/tutorial)

### 深度文章

- 📖 [Rust Web Development](https://www.manning.com/books/rust-web-development)
- 📖 [Zero To Production In Rust](https://www.zero2prod.com/)
- 📖 [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)

### 实战项目

- 💻 [Realworld](https://github.com/gothinkster/realworld) - 全栈示例
- 💻 [Conduit](https://github.com/tokio-rs/axum/tree/main/examples) - Axum 示例
- 💻 [mini-redis](https://github.com/tokio-rs/mini-redis) - Redis 实现

### 相关文档

- 🔗 [系统编程层](../02_system_programming/README.md)
- 🔗 [基础设施层](../01_infrastructure/README.md)
- 🔗 [工具链](../05_toolchain/README.md)

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**维护者**: Rust 学习社区
