# Rust架构设计模式

> **Rust版本**: 1.93.1
> **覆盖范围**: 分层架构、六边形架构、CQRS、Event Sourcing、微服务架构
> **权威参考**: Clean Architecture, DDD, Rust Web开发最佳实践

---

## 目录

- [Rust架构设计模式](#rust架构设计模式)
  - [目录](#目录)
  - [1. 架构设计原则](#1-架构设计原则)
    - [Rust架构哲学](#rust架构哲学)
    - [架构模式选择矩阵](#架构模式选择矩阵)
  - [2. 分层架构](#2-分层架构)
    - [经典三层架构](#经典三层架构)
    - [Rust实现](#rust实现)
  - [3. 六边形架构/端口适配器](#3-六边形架构端口适配器)
    - [架构图](#架构图)
    - [Rust实现](#rust实现-1)
  - [4. CQRS模式](#4-cqrs模式)
    - [架构分离](#架构分离)
    - [Rust实现](#rust实现-2)
  - [5. 事件溯源](#5-事件溯源)
    - [架构](#架构)
  - [6. 微服务架构](#6-微服务架构)
    - [服务边界划分](#服务边界划分)
  - [7. 模块化设计](#7-模块化设计)
    - [Crate层次结构](#crate层次结构)
  - [8. 错误处理架构](#8-错误处理架构)
    - [分层错误类型](#分层错误类型)
  - [9. 配置管理](#9-配置管理)
    - [分层配置](#分层配置)
  - [10. 测试架构](#10-测试架构)
    - [测试金字塔](#测试金字塔)
  - [参考文献](#参考文献)

---

## 1. 架构设计原则

### Rust架构哲学

```text
1. 编译时保证 > 运行时检查
   - 类型系统编码业务规则
   - 非法状态不可表示

2. 显式依赖 > 隐式依赖
   - 依赖注入
   - trait边界明确

3. 零成本抽象
   - 架构模式不引入运行时开销
   - 泛型monomorphization

4. fearless concurrency
   - 利用所有权系统实现安全并发
   - Send/Sync边界

5. 组合优于继承
   - trait系统
   - 结构体组合
```

### 架构模式选择矩阵

| 场景 | 推荐架构 | Rust适用性 |
|------|---------|-----------|
| Web服务 | 分层 + 六边形 | ⭐⭐⭐⭐⭐ |
| 高吞吐流处理 | 事件驱动 | ⭐⭐⭐⭐⭐ |
| 复杂业务逻辑 | DDD + CQRS | ⭐⭐⭐⭐ |
| 嵌入式 | 分层 | ⭐⭐⭐⭐⭐ |
| 微服务 | 微服务 + 事件溯源 | ⭐⭐⭐⭐ |

---

## 2. 分层架构

### 经典三层架构

```text
┌─────────────────────────────────────┐
│         Presentation Layer          │
│  (axum/actix-web handlers)          │
├─────────────────────────────────────┤
│          Business Layer             │
│  (services, domain logic)           │
├─────────────────────────────────────┤
│          Data Layer                 │
│  (repositories, database)           │
└─────────────────────────────────────┘
```

### Rust实现

```rust
// domain/mod.rs - 领域层
pub mod entities;
pub mod repositories;
pub mod services;

// domain/entities.rs
#[derive(Debug, Clone)]
pub struct User {
    pub id: UserId,
    pub name: String,
    pub email: Email,
}

pub struct UserId(pub uuid::Uuid);
pub struct Email(String);

impl Email {
    pub fn new(email: &str) -> Result<Self, String> {
        if email.contains('@') {
            Ok(Self(email.to_string()))
        } else {
            Err("Invalid email".to_string())
        }
    }
}

// domain/repositories.rs
#[async_trait::async_trait]
pub trait UserRepository: Send + Sync {
    async fn find_by_id(&self, id: &UserId) -> Option<User>;
    async fn save(&self, user: &User) -> Result<(), String>;
    async fn delete(&self, id: &UserId) -> Result<(), String>;
}

// domain/services.rs
pub struct UserService<R: UserRepository> {
    repository: R,
}

impl<R: UserRepository> UserService<R> {
    pub fn new(repository: R) -> Self {
        Self { repository }
    }

    pub async fn create_user(&self, name: &str, email: &str) -> Result<User, String> {
        let email = Email::new(email)?;
        let user = User {
            id: UserId(uuid::Uuid::new_v4()),
            name: name.to_string(),
            email,
        };

        self.repository.save(&user).await?;
        Ok(user)
    }
}

// infrastructure/repository.rs - 基础设施层
use sqlx::PgPool;

pub struct PostgresUserRepository {
    pool: PgPool,
}

impl PostgresUserRepository {
    pub fn new(pool: PgPool) -> Self {
        Self { pool }
    }
}

#[async_trait::async_trait]
impl UserRepository for PostgresUserRepository {
    async fn find_by_id(&self, id: &UserId) -> Option<User> {
        // SQL查询实现
        None
    }

    async fn save(&self, user: &User) -> Result<(), String> {
        // SQL插入实现
        Ok(())
    }

    async fn delete(&self, id: &UserId) -> Result<(), String> {
        // SQL删除实现
        Ok(())
    }
}

// presentation/handlers.rs - 表现层
use axum::{extract::State, Json};

pub async fn create_user_handler<R: UserRepository>(
    State(service): State<UserService<R>>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<User>, String> {
    let user = service.create_user(&payload.name, &payload.email).await?;
    Ok(Json(user))
}

#[derive(serde::Deserialize)]
pub struct CreateUserRequest {
    name: String,
    email: String,
}
```

---

## 3. 六边形架构/端口适配器

### 架构图

```text
              ┌─────────────┐
              │    CLI      │
              └──────┬──────┘
                     │
              ┌──────┴──────┐
              │  HTTP API   │
              └──────┬──────┘
                     │
        ┌────────────┼────────────┐
        │            │            │
┌───────┴──────┐ ┌───┴────┐ ┌────┴──────┐
│Primary       │ │Domain  │ │Secondary  │
│Adapter       │ │Logic   │ │Adapter    │
│(Web/API)     │ │        │ │(DB/Cache) │
└───────┬──────┘ └───┬────┘ └────┬──────┘
        │            │           │
        └────────────┼───────────┘
                     │
            Ports (Traits)
```

### Rust实现

```rust
// ports.rs - 定义端口（trait）

// 入站端口（驱动应用）
#[async_trait::async_trait]
pub trait ForCreatingUser {
    async fn create_user(&self, name: &str, email: &str) -> Result<User, String>;
}

#[async_trait::async_trait]
pub trait ForGettingUser {
    async fn get_user(&self, id: &str) -> Option<User>;
}

// 出站端口（被应用驱动）
#[async_trait::async_trait]
pub trait ForStoringUser {
    async fn save(&self, user: &User) -> Result<(), String>;
    async fn find_by_id(&self, id: &str) -> Option<User>;
}

#[async_trait::async_trait]
pub trait ForSendingEmail {
    async fn send_welcome_email(&self, to: &str, name: &str) -> Result<(), String>;
}

// application/service.rs - 应用核心
pub struct UserApplication {
    user_store: Box<dyn ForStoringUser>,
    email_sender: Box<dyn ForSendingEmail>,
}

impl UserApplication {
    pub fn new(
        user_store: Box<dyn ForStoringUser>,
        email_sender: Box<dyn ForSendingEmail>,
    ) -> Self {
        Self {
            user_store,
            email_sender,
        }
    }
}

#[async_trait::async_trait]
impl ForCreatingUser for UserApplication {
    async fn create_user(&self, name: &str, email: &str) -> Result<User, String> {
        let user = User::new(name, email)?;

        self.user_store.save(&user).await?;
        self.email_sender.send_welcome_email(email, name).await?;

        Ok(user)
    }
}

// adapters/primary/http.rs - HTTP适配器
pub fn user_routes(app: Arc<UserApplication>) -> Router {
    Router::new()
        .route("/users", post(create_user))
        .with_state(app)
}

async fn create_user(
    State(app): State<Arc<UserApplication>>,
    Json(payload): Json<CreateUserRequest>,
) -> Result<Json<User>, String> {
    let user = app.create_user(&payload.name, &payload.email).await?;
    Ok(Json(user))
}

// adapters/secondary/postgres.rs - 数据库适配器
pub struct PostgresUserAdapter {
    pool: sqlx::PgPool,
}

#[async_trait::async_trait]
impl ForStoringUser for PostgresUserAdapter {
    async fn save(&self, user: &User) -> Result<(), String> {
        // 实现...
        Ok(())
    }

    async fn find_by_id(&self, id: &str) -> Option<User> {
        // 实现...
        None
    }
}

// adapters/secondary/smtp.rs - 邮件适配器
pub struct SmtpEmailAdapter {
    smtp_client: async_smtp::SmtpClient,
}

#[async_trait::async_trait]
impl ForSendingEmail for SmtpEmailAdapter {
    async fn send_welcome_email(&self, to: &str, name: &str) -> Result<(), String> {
        // 实现...
        Ok(())
    }
}

// main.rs - 组装
#[tokio::main]
async fn main() {
    let pool = sqlx::PgPool::connect("postgres://...").await.unwrap();
    let smtp_client = async_smtp::SmtpClient::new();

    let user_store = Box::new(PostgresUserAdapter::new(pool));
    let email_sender = Box::new(SmtpEmailAdapter::new(smtp_client));

    let app = Arc::new(UserApplication::new(user_store, email_sender));

    let routes = user_routes(app);

    axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
        .serve(routes.into_make_service())
        .await
        .unwrap();
}
```

---

## 4. CQRS模式

### 架构分离

```text
┌─────────────────────────────────────────────────────┐
│                    Command Side                     │
│  (写操作)                                           │
│  ┌──────────────┐  ┌──────────────┐                │
│  │ Command      │  │ Command      │                │
│  │ Handler      │  │ Handler      │                │
│  └──────┬───────┘  └──────┬───────┘                │
│         │                 │                         │
│         └────────┬────────┘                         │
│                  ▼                                  │
│         ┌────────────────┐                         │
│         │  Write Model   │                         │
│         │  (Domain DB)   │                         │
│         └────────┬───────┘                         │
│                  │                                  │
│                  ▼ Event Bus                        │
└─────────────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────┐
│                     Query Side                      │
│  (读操作)                                           │
│         ┌────────────────┐                         │
│         │   Read Model   │                         │
│         │  (Query DB)    │                         │
│         └────────┬───────┘                         │
│                  │                                  │
│         ┌────────┴────────┐                        │
│         ▼                 ▼                         │
│  ┌──────────────┐  ┌──────────────┐                │
│  │ Query        │  │ Query        │                │
│  │ Handler      │  │ Handler      │                │
│  └──────────────┘  └──────────────┘                │
└─────────────────────────────────────────────────────┘
```

### Rust实现

```rust
// commands.rs
pub struct CreateOrderCommand {
    pub order_id: String,
    pub user_id: String,
    pub items: Vec<OrderItem>,
}

pub struct CommandHandler {
    write_repo: Arc<dyn OrderWriteRepository>,
    event_bus: Arc<dyn EventBus>,
}

impl CommandHandler {
    pub async fn handle_create_order(&self, cmd: CreateOrderCommand) -> Result<(), String> {
        let order = Order::new(&cmd.order_id, &cmd.user_id, cmd.items)?;

        self.write_repo.save(&order).await?;

        for event in order.uncommitted_events() {
            self.event_bus.publish(event).await?;
        }

        Ok(())
    }
}

// queries.rs
pub struct OrderQuery {
    pub order_id: String,
    pub total_amount: f64,
    pub status: String,
}

pub struct QueryHandler {
    read_repo: Arc<dyn OrderReadRepository>,
}

impl QueryHandler {
    pub async fn get_order_by_id(&self, order_id: &str) -> Option<OrderQuery> {
        self.read_repo.find_query_by_id(order_id).await
    }

    pub async fn get_user_orders(&self, user_id: &str) -> Vec<OrderQuery> {
        self.read_repo.find_by_user(user_id).await
    }
}

// projection.rs - 事件投影
pub struct OrderProjection {
    read_repo: Arc<dyn OrderReadRepository>,
}

impl EventHandler for OrderProjection {
    async fn handle(&self, event: &DomainEvent) {
        match event {
            DomainEvent::OrderCreated { order_id, user_id, items } => {
                let query = OrderQuery {
                    order_id: order_id.clone(),
                    total_amount: items.iter().map(|i| i.price * i.quantity).sum(),
                    status: "created".to_string(),
                };
                self.read_repo.save_query(&query).await.ok();
            }
            DomainEvent::OrderPaid { order_id } => {
                self.read_repo.update_status(order_id, "paid").await.ok();
            }
            _ => {}
        }
    }
}

// 不同的数据库优化
// Write Model: PostgreSQL (ACID)
// Read Model: Elasticsearch (查询优化)
```

---

## 5. 事件溯源

### 架构

```rust
// events.rs
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(tag = "type")]
pub enum DomainEvent {
    OrderCreated {
        order_id: String,
        user_id: String,
        items: Vec<OrderItem>,
        timestamp: DateTime<Utc>,
    },
    OrderPaid {
        order_id: String,
        amount: f64,
        timestamp: DateTime<Utc>,
    },
    OrderShipped {
        order_id: String,
        tracking_id: String,
        timestamp: DateTime<Utc>,
    },
}

// aggregate.rs
pub struct OrderAggregate {
    order_id: String,
    version: usize,
    state: OrderState,
    uncommitted_events: Vec<DomainEvent>,
}

#[derive(Default)]
pub struct OrderState {
    user_id: Option<String>,
    items: Vec<OrderItem>,
    status: OrderStatus,
    paid_amount: Option<f64>,
}

impl OrderAggregate {
    pub fn new(order_id: &str) -> Self {
        let mut aggregate = Self {
            order_id: order_id.to_string(),
            version: 0,
            state: OrderState::default(),
            uncommitted_events: vec![],
        };

        // 初始事件
        aggregate.apply_event(&DomainEvent::OrderCreated {
            order_id: order_id.to_string(),
            user_id: String::new(),
            items: vec![],
            timestamp: Utc::now(),
        });

        aggregate
    }

    pub fn create(user_id: &str, items: Vec<OrderItem>) -> Result<Self, String> {
        if items.is_empty() {
            return Err("Order must have at least one item".to_string());
        }

        let order_id = Uuid::new_v4().to_string();
        let mut order = Self::new(&order_id);

        order.uncommitted_events.push(DomainEvent::OrderCreated {
            order_id: order_id.clone(),
            user_id: user_id.to_string(),
            items: items.clone(),
            timestamp: Utc::now(),
        });

        order.apply_changes();

        Ok(order)
    }

    pub fn pay(&mut self, amount: f64) -> Result<(), String> {
        if self.state.status != OrderStatus::Created {
            return Err("Order already paid".to_string());
        }

        let total: f64 = self.state.items.iter().map(|i| i.price * i.quantity).sum();
        if amount < total {
            return Err("Insufficient payment".to_string());
        }

        self.uncommitted_events.push(DomainEvent::OrderPaid {
            order_id: self.order_id.clone(),
            amount,
            timestamp: Utc::now(),
        });

        self.apply_changes();

        Ok(())
    }

    fn apply_changes(&mut self) {
        for event in &self.uncommitted_events {
            self.apply_event(event);
        }
        self.version += self.uncommitted_events.len();
    }

    fn apply_event(&mut self, event: &DomainEvent) {
        match event {
            DomainEvent::OrderCreated { user_id, items, .. } => {
                self.state.user_id = Some(user_id.clone());
                self.state.items = items.clone();
                self.state.status = OrderStatus::Created;
            }
            DomainEvent::OrderPaid { amount, .. } => {
                self.state.paid_amount = Some(*amount);
                self.state.status = OrderStatus::Paid;
            }
            DomainEvent::OrderShipped { .. } => {
                self.state.status = OrderStatus::Shipped;
            }
        }
    }

    pub fn rebuild_from_events(order_id: &str, events: Vec<DomainEvent>) -> Self {
        let mut order = Self::new(order_id);

        for event in events {
            order.apply_event(&event);
            order.version += 1;
        }

        order.uncommitted_events.clear();
        order
    }

    pub fn uncommitted_events(&self) -> &[DomainEvent] {
        &self.uncommitted_events
    }

    pub fn clear_uncommitted(&mut self) {
        self.uncommitted_events.clear();
    }
}

// event_store.rs
#[async_trait::async_trait]
pub trait EventStore {
    async fn append(&self, aggregate_id: &str, events: &[DomainEvent], expected_version: usize) -> Result<(), String>;
    async fn get_events(&self, aggregate_id: &str) -> Vec<DomainEvent>;
    async fn get_events_after(&self, sequence: usize) -> Vec<DomainEvent>;
}

pub struct PostgresEventStore {
    pool: sqlx::PgPool,
}

#[async_trait::async_trait]
impl EventStore for PostgresEventStore {
    async fn append(&self, aggregate_id: &str, events: &[DomainEvent], expected_version: usize) -> Result<(), String> {
        let mut tx = self.pool.begin().await.map_err(|e| e.to_string())?;

        // 乐观并发控制
        let current_version: i64 = sqlx::query_scalar(
            "SELECT COALESCE(MAX(version), 0) FROM events WHERE aggregate_id = $1"
        )
        .bind(aggregate_id)
        .fetch_one(&mut tx)
        .await
        .map_err(|e| e.to_string())?;

        if current_version as usize != expected_version {
            return Err("Concurrency conflict".to_string());
        }

        for (i, event) in events.iter().enumerate() {
            let version = expected_version + i + 1;
            let event_data = serde_json::to_value(event).map_err(|e| e.to_string())?;

            sqlx::query(
                "INSERT INTO events (aggregate_id, version, event_type, event_data) VALUES ($1, $2, $3, $4)"
            )
            .bind(aggregate_id)
            .bind(version as i64)
            .bind(event.type_name())
            .bind(event_data)
            .execute(&mut tx)
            .await
            .map_err(|e| e.to_string())?;
        }

        tx.commit().await.map_err(|e| e.to_string())
    }

    async fn get_events(&self, aggregate_id: &str) -> Vec<DomainEvent> {
        // 实现...
        vec![]
    }

    async fn get_events_after(&self, _sequence: usize) -> Vec<DomainEvent> {
        // 实现...
        vec![]
    }
}
```

---

## 6. 微服务架构

### 服务边界划分

```rust
// 使用workspace组织微服务
// Cargo.toml (workspace root)
[workspace]
members = [
    "services/user-service",
    "services/order-service",
    "services/payment-service",
    "shared/events",
    "shared/types",
]

// services/user-service/src/main.rs
#[tokio::main]
async fn main() {
    let config = load_config();

    let db_pool = create_db_pool(&config.database_url).await;
    let event_bus = connect_event_bus(&config.event_bus_url).await;
    let cache = connect_cache(&config.cache_url).await;

    let user_service = UserService::new(db_pool, event_bus, cache);

    let grpc_server = start_grpc_server(user_service.clone());
    let http_server = start_http_server(user_service);

    tokio::join!(grpc_server, http_server);
}
```

---

## 7. 模块化设计

### Crate层次结构

```text
my_project/
├── Cargo.toml          # workspace root
├── crates/
│   ├── core/           # 核心业务逻辑
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── domain/
│   │       └── ports/
│   ├── adapters/       # 适配器实现
│   │   ├── web/        # HTTP适配器
│   │   ├── grpc/       # gRPC适配器
│   │   └── db/         # 数据库适配器
│   └── app/            # 应用组装
│       └── src/
│           └── main.rs
```

---

## 8. 错误处理架构

### 分层错误类型

```rust
// domain/errors.rs
#[derive(Debug, thiserror::Error)]
pub enum DomainError {
    #[error("Invalid email: {0}")]
    InvalidEmail(String),

    #[error("User not found: {0}")]
    UserNotFound(String),

    #[error("Insufficient balance")]
    InsufficientBalance,
}

// application/errors.rs
#[derive(Debug, thiserror::Error)]
pub enum ApplicationError {
    #[error("Domain error: {0}")]
    Domain(#[from] DomainError),

    #[error("Repository error: {0}")]
    Repository(String),

    #[error("External service error: {0}")]
    ExternalService(String),
}

// infrastructure/errors.rs
#[derive(Debug, thiserror::Error)]
pub enum InfrastructureError {
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),

    #[error("Cache error: {0}")]
    Cache(String),

    #[error("HTTP client error: {0}")]
    HttpClient(#[from] reqwest::Error),
}

// presentation/errors.rs
#[derive(Debug, serde::Serialize)]
pub struct ApiError {
    pub code: String,
    pub message: String,
}

impl From<ApplicationError> for ApiError {
    fn from(err: ApplicationError) -> Self {
        match err {
            ApplicationError::Domain(d) => ApiError {
                code: "DOMAIN_ERROR".to_string(),
                message: d.to_string(),
            },
            ApplicationError::Repository(_) => ApiError {
                code: "INTERNAL_ERROR".to_string(),
                message: "Internal server error".to_string(),
            },
            _ => ApiError {
                code: "UNKNOWN_ERROR".to_string(),
                message: "Unknown error".to_string(),
            },
        }
    }
}
```

---

## 9. 配置管理

### 分层配置

```rust
use config::{Config, ConfigError, Environment, File};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct AppConfig {
    pub server: ServerConfig,
    pub database: DatabaseConfig,
    pub cache: CacheConfig,
    pub external_services: ExternalServicesConfig,
}

#[derive(Debug, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
}

#[derive(Debug, Deserialize)]
pub struct DatabaseConfig {
    pub url: String,
    pub pool_size: u32,
}

impl AppConfig {
    pub fn load() -> Result<Self, ConfigError> {
        let config = Config::builder()
            // 默认配置
            .add_source(File::with_name("config/default"))
            // 环境特定配置
            .add_source(File::with_name(&format!(
                "config/{}",
                std::env::var("RUN_ENV").unwrap_or_else(|_| "development".into())
            )))
            // 环境变量覆盖
            .add_source(Environment::with_prefix("APP").separator("__"))
            .build()?;

        config.try_deserialize()
    }
}
```

---

## 10. 测试架构

### 测试金字塔

```rust
// 单元测试 (domain)
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_email_validation() {
        assert!(Email::new("test@example.com").is_ok());
        assert!(Email::new("invalid").is_err());
    }
}

// 集成测试 (application)
#[cfg(test)]
mod integration_tests {
    use super::*;

    #[tokio::test]
    async fn test_create_user() {
        let repo = InMemoryUserRepository::new();
        let service = UserService::new(repo);

        let user = service.create_user("John", "john@example.com").await.unwrap();

        assert_eq!(user.name, "John");
    }
}

// 契约测试 (adapters)
#[cfg(test)]
mod contract_tests {
    // 测试适配器是否符合端口契约
}

// E2E测试
#[cfg(test)]
mod e2e_tests {
    // 完整流程测试
}
```

---

## 参考文献

1. Clean Architecture (Robert C. Martin)
2. Domain-Driven Design (Eric Evans)
3. Implementing Domain-Driven Design (Vaughn Vernon)
4. Patterns of Enterprise Application Architecture (Martin Fowler)
5. Building Evolutionary Architectures (Neal Ford)
