# Tokio 生态系统深度指南

> **创建日期**: 2026-03-17
> **最后更新**: 2026-03-17
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **Tokio 版本**: 1.43+
> **文档状态**: ✅ 已完成
> **目标读者**: 中高级 Rust 开发者
> **维护者**: Rust 学习项目团队

---

## 📋 目录

- [Tokio 生态系统深度指南](#tokio-生态系统深度指南)
  - [📋 目录](#-目录)
  - [1. 简介](#1-简介)
    - [1.1 Tokio 生态系统概览](#11-tokio-生态系统概览)
    - [1.2 适用场景](#12-适用场景)
  - [2. Tokio 运行时基础](#2-tokio-运行时基础)
    - [2.1 简介](#21-简介)
    - [2.2 核心概念](#22-核心概念)
      - [运行时架构](#运行时架构)
      - [调度器对比](#调度器对比)
    - [2.3 示例代码](#23-示例代码)
      - [基础运行时配置](#基础运行时配置)
      - [任务管理](#任务管理)
      - [同步原语](#同步原语)
    - [2.4 最佳实践](#24-最佳实践)
      - [DO's](#dos)
      - [DON'Ts](#donts)
  - [3. Axum Web 框架](#3-axum-web-框架)
    - [3.1 简介](#31-简介)
    - [3.2 核心概念](#32-核心概念)
    - [3.3 示例代码](#33-示例代码)
      - [基础路由和处理器](#基础路由和处理器)
      - [自定义提取器](#自定义提取器)
      - [错误处理](#错误处理)
    - [3.4 最佳实践](#34-最佳实践)
      - [项目结构](#项目结构)
      - [性能优化](#性能优化)
  - [4. Tonic gRPC 框架](#4-tonic-grpc-框架)
    - [4.1 简介](#41-简介)
    - [4.2 核心概念](#42-核心概念)
    - [4.3 示例代码](#43-示例代码)
      - [Protocol Buffers 定义](#protocol-buffers-定义)
      - [Build 配置](#build-配置)
      - [服务端实现](#服务端实现)
      - [客户端实现](#客户端实现)
    - [4.4 最佳实践](#44-最佳实践)
  - [5. Tower 中间件](#5-tower-中间件)
    - [5.1 简介](#51-简介)
    - [5.2 核心概念](#52-核心概念)
      - [Service Trait](#service-trait)
      - [Layer Trait](#layer-trait)
    - [5.3 示例代码](#53-示例代码)
      - [中间件组合](#中间件组合)
      - [自定义 Layer](#自定义-layer)
      - [熔断器](#熔断器)
    - [5.4 最佳实践](#54-最佳实践)
      - [中间件顺序建议](#中间件顺序建议)
  - [6. Tracing 可观测性](#6-tracing-可观测性)
    - [6.1 简介](#61-简介)
    - [6.2 核心概念](#62-核心概念)
    - [6.3 示例代码](#63-示例代码)
      - [基础使用](#基础使用)
      - [OpenTelemetry 集成](#opentelemetry-集成)
    - [6.4 最佳实践](#64-最佳实践)
  - [7. 生产级架构示例](#7-生产级架构示例)
    - [7.1 微服务架构](#71-微服务架构)
    - [7.2 完整项目示例](#72-完整项目示例)
      - [项目结构](#项目结构-1)
      - [主入口](#主入口)
      - [应用构建](#应用构建)
      - [优雅关闭](#优雅关闭)
  - [8. 性能调优指南](#8-性能调优指南)
    - [8.1 运行时调优](#81-运行时调优)
    - [8.2 内存优化](#82-内存优化)
    - [8.3 网络优化](#83-网络优化)
    - [8.4 性能检查清单](#84-性能检查清单)
  - [9. 常见问题排查](#9-常见问题排查)
    - [9.1 性能问题](#91-性能问题)
    - [9.2 调试技巧](#92-调试技巧)
  - [10. 附录](#10-附录)
    - [10.1 推荐依赖版本](#101-推荐依赖版本)
    - [10.2 参考资源](#102-参考资源)

---

## 1. 简介

### 1.1 Tokio 生态系统概览

Tokio 是 Rust 生态系统中最重要的异步运行时，提供了一套完整的异步编程基础设施。其生态系统包含多个核心组件：

- **Tokio Runtime**: 异步运行时，提供任务调度、异步 I/O、定时器等
- **Axum**: Web 框架，基于 Tokio 和 Tower
- **Tonic**: gRPC 框架，基于 Tokio 和 Tower
- **Tower**: 服务抽象和中间件框架
- **Tracing**: 分布式追踪和日志框架

### 1.2 适用场景

| 场景 | 推荐组件 | 说明 |
|------|----------|------|
| RESTful API 服务 | Axum + Tower | 简洁高效，中间件丰富 |
| 微服务通信 | Tonic + Tower | 高性能 gRPC |
| 实时应用 | Tokio + Axum WebSocket | 低延迟，高并发 |
| 数据处理管道 | Tokio Stream | 流式处理，背压控制 |
| 可观测性 | Tracing + OpenTelemetry | 分布式追踪，指标收集 |

---

## 2. Tokio 运行时基础

### 2.1 简介

Tokio 是 Rust 的异步运行时，提供：

- **任务调度**: 多线程工作窃取调度器
- **异步 I/O**: 基于 epoll/kqueue/IOCP 的网络和文件 I/O
- **定时器**: 高效的异步延迟和间隔执行
- **通道**: 多生产者多消费者异步消息传递
- **同步原语**: 异步 Mutex、RwLock、Semaphore 等

### 2.2 核心概念

#### 运行时架构

Tokio 使用两级队列系统：

1. **全局队列**: 所有线程可访问，需要锁
2. **本地队列**: 每个工作线程独有，无锁操作

当本地队列为空时，工作线程会尝试从其他线程"窃取"任务。

#### 调度器对比

| 特性 | `multi_thread` | `current_thread` |
|------|----------------|------------------|
| 适用场景 | CPU 密集型、高并发 | 单线程、资源受限 |
| 工作线程数 | 多线程 (默认 CPU 核心数) | 1 个线程 |
| 任务调度 | 工作窃取 | 当前线程轮询 |
| spawn_blocking | 独立线程池 | 同一线程 (阻塞!) |
| 典型应用 | Web 服务器、API 服务 | 嵌入式、测试、CLI |
| 内存占用 | 较高 | 较低 |

### 2.3 示例代码

#### 基础运行时配置

```rust
use tokio::runtime::{Builder, Runtime};
use std::time::Duration;

/// 创建生产级多线程 Runtime
fn create_production_runtime() -> Runtime {
    Builder::new_multi_thread()
        .worker_threads(8)                    // 工作线程数
        .max_blocking_threads(512)            // 阻塞线程池上限
        .thread_stack_size(2 * 1024 * 1024)   // 2MB 栈大小
        .thread_name("tokio-worker")          // 线程命名
        .enable_all()                         // 启用 IO + Time 驱动
        .event_interval(61)                   // 事件轮询间隔
        .global_queue_interval(61)            // 全局队列轮询间隔
        .max_io_events_per_tick(1024)         // 每 tick 最大 IO 事件数
        .build()
        .expect("Failed to create runtime")
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 并发执行多个任务
    let handles: Vec<_> = (0..100)
        .map(|i| {
            tokio::spawn(async move {
                println!("Task {} running on {:?}", i, std::thread::current().id());
                tokio::time::sleep(Duration::from_millis(100)).await;
                i * 2
            })
        })
        .collect();

    let results: Vec<_> = futures::future::join_all(handles).await;
    println!("Completed {} tasks", results.len());

    Ok(())
}
```

#### 任务管理

```rust
use tokio::task::{self, JoinSet};
use tokio::sync::mpsc;
use std::time::Duration;

/// 任务调度最佳实践
async fn task_management_examples() {
    // 1. 使用 JoinSet 管理动态任务集合
    let mut set = JoinSet::new();

    for i in 0..100 {
        set.spawn(async move {
            tokio::time::sleep(Duration::from_millis(i as u64 * 10)).await;
            format!("Task {} complete", i)
        });
    }

    // 按完成顺序处理结果
    while let Some(result) = set.join_next().await {
        match result {
            Ok(msg) => println!("{}", msg),
            Err(e) => eprintln!("Task panicked: {}", e),
        }
    }

    // 2. CPU 密集型任务使用 spawn_blocking
    let cpu_result = task::spawn_blocking(|| {
        let mut sum = 0u64;
        for i in 0..1_000_000 {
            sum += i;
        }
        sum
    }).await.expect("Task panicked");

    println!("CPU result: {}", cpu_result);
}
```

#### 同步原语

```rust
use tokio::sync::{Mutex, RwLock, Semaphore, broadcast, mpsc, oneshot};
use std::sync::Arc;

/// Tokio 同步原语示例
async fn synchronization_primitives() {
    // 1. 异步 Mutex
    let data = Arc::new(Mutex::new(0));

    let mut handles = vec![];
    for _ in 0..10 {
        let data = Arc::clone(&data);
        handles.push(tokio::spawn(async move {
            let mut guard = data.lock().await;
            *guard += 1;
        }));
    }

    for h in handles { h.await.unwrap(); }
    println!("Final value: {}", *data.lock().await);

    // 2. Semaphore - 限制并发数
    let semaphore = Arc::new(Semaphore::new(5));

    let mut handles = vec![];
    for i in 0..20 {
        let permit = semaphore.clone().acquire_owned().await.unwrap();
        handles.push(tokio::spawn(async move {
            let _permit = permit;
            println!("Task {} executing", i);
            tokio::time::sleep(Duration::from_millis(100)).await;
        }));
    }

    for h in handles { h.await.unwrap(); }

    // 3. oneshot - 单次通信
    let (tx, rx) = oneshot::channel::<i32>();

    tokio::spawn(async move {
        tx.send(42).unwrap();
    });

    let value = rx.await.unwrap();
    println!("Received: {}", value);
}
```

### 2.4 最佳实践

#### DO's

| 实践 | 说明 |
|------|------|
| 使用 spawn_blocking 处理 CPU 密集型任务 | 避免阻塞运行时 |
| 限制并发数 | 使用 Semaphore 防止资源耗尽 |
| 使用有界通道 | 防止内存无限增长 |
| 及时处理取消信号 | 实现 Cancel Safety |
| 配置合理的超时 | 避免无限等待 |

#### DON'Ts

```rust
// 错误：在 async 中执行阻塞操作
async fn bad_example() {
    std::thread::sleep(Duration::from_secs(1)); // 阻塞整个线程！
}

// 正确：使用 spawn_blocking
async fn good_example() {
    tokio::task::spawn_blocking(|| {
        std::thread::sleep(Duration::from_secs(1));
    }).await.unwrap();
}

// 错误：持有 MutexGuard 跨越 await
async fn bad_lock_usage(cache: &Arc<Mutex<Cache>>) {
    let mut guard = cache.lock().await;
    let data = guard.get_data();
    let result = fetch_from_network(data).await; // 危险！
    guard.update(result);
}

// 正确：缩小锁作用域
async fn good_lock_usage(cache: &Arc<Mutex<Cache>>) {
    let data = {
        let guard = cache.lock().await;
        guard.get_data()
    }; // 锁在这里释放

    let result = fetch_from_network(data).await;

    {
        let mut guard = cache.lock().await;
        guard.update(result);
    }
}
```

---

## 3. Axum Web 框架

### 3.1 简介

Axum 是一个基于 Tokio 和 Tower 的 Web 框架，设计目标是：

- **人体工程学**: 利用 Rust 类型系统提供编译时保证
- **模块化**: 基于 Tower Service trait，中间件可复用
- **高性能**: 基于 Hyper，无运行时开销
- **可测试性**: 处理器是普通函数，易于单元测试

### 3.2 核心概念

| 组件 | 说明 | 示例 |
|------|------|------|
| `Router` | 路由定义 | `.route("/users", get(list_users))` |
| `Handler` | 请求处理器 | `async fn handler() -> impl IntoResponse` |
| `Extractor` | 请求数据提取 | `Path`, `Query`, `Json`, `State` |
| `Response` | 响应类型 | `Json`, `Html`, `StatusCode` |
| `Layer` | 中间件 | `TraceLayer`, `CorsLayer` |

### 3.3 示例代码

#### 基础路由和处理器

```rust
use axum::{
    routing::{get, post, put, delete, Router},
    extract::{Path, Query, State},
    Json, http::StatusCode,
    response::IntoResponse,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;

#[derive(Clone)]
struct AppState {
    db: Arc<RwLock<HashMap<i64, User>>>,
    counter: Arc<RwLock<u64>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct User {
    id: i64,
    name: String,
    email: String,
}

#[derive(Debug, Deserialize)]
struct CreateUserRequest {
    name: String,
    email: String,
}

#[derive(Debug, Deserialize)]
struct Pagination {
    #[serde(default = "default_page")]
    page: u32,
    #[serde(default = "default_per_page")]
    per_page: u32,
}

fn default_page() -> u32 { 1 }
fn default_per_page() -> u32 { 20 }

fn create_router(state: Arc<AppState>) -> Router {
    Router::new()
        .route("/", get(root))
        .route("/health", get(health_check))
        .route("/api/v1/users", get(list_users).post(create_user))
        .route("/api/v1/users/:id", get(get_user).put(update_user).delete(delete_user))
        .with_state(state)
        .layer(tower_http::trace::TraceLayer::new_for_http())
        .layer(tower_http::cors::CorsLayer::permissive())
        .layer(tower_http::compression::CompressionLayer::new())
}

async fn root() -> &'static str {
    "Hello, Axum!"
}

async fn health_check(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    let counter = *state.counter.read().await;
    Json(serde_json::json!({
        "status": "healthy",
        "requests": counter,
    }))
}

async fn list_users(
    State(state): State<Arc<AppState>>,
    Query(pagination): Query<Pagination>,
) -> Json<Vec<User>> {
    let db = state.db.read().await;
    let users: Vec<User> = db.values()
        .skip(((pagination.page - 1) * pagination.per_page) as usize)
        .take(pagination.per_page as usize)
        .cloned()
        .collect();
    Json(users)
}

async fn get_user(
    Path(id): Path<i64>,
    State(state): State<Arc<AppState>>,
) -> Result<Json<User>, StatusCode> {
    let db = state.db.read().await;
    db.get(&id).cloned().map(Json).ok_or(StatusCode::NOT_FOUND)
}

async fn create_user(
    State(state): State<Arc<AppState>>,
    Json(req): Json<CreateUserRequest>,
) -> Result<(StatusCode, Json<User>), StatusCode> {
    let mut counter = state.counter.write().await;
    *counter += 1;
    let id = *counter as i64;

    let user = User {
        id,
        name: req.name,
        email: req.email,
    };

    let mut db = state.db.write().await;
    db.insert(id, user.clone());

    Ok((StatusCode::CREATED, Json(user)))
}

async fn update_user(
    Path(id): Path<i64>,
    State(state): State<Arc<AppState>>,
    Json(req): Json<CreateUserRequest>,
) -> Result<Json<User>, StatusCode> {
    let mut db = state.db.write().await;

    if let Some(user) = db.get_mut(&id) {
        user.name = req.name;
        user.email = req.email;
        Ok(Json(user.clone()))
    } else {
        Err(StatusCode::NOT_FOUND)
    }
}

async fn delete_user(
    Path(id): Path<i64>,
    State(state): State<Arc<AppState>>,
) -> StatusCode {
    let mut db = state.db.write().await;
    if db.remove(&id).is_some() {
        StatusCode::NO_CONTENT
    } else {
        StatusCode::NOT_FOUND
    }
}

#[tokio::main]
async fn main() {
    let state = Arc::new(AppState {
        db: Arc::new(RwLock::new(HashMap::new())),
        counter: Arc::new(RwLock::new(0)),
    });

    let app = create_router(state);
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();

    println!("Server running on http://0.0.0.0:3000");
    axum::serve(listener, app).await.unwrap();
}
```

#### 自定义提取器

```rust
use axum::{
    extract::{FromRequestParts, TypedHeader},
    headers::{authorization::Bearer, Authorization},
    async_trait,
    http::{request::Parts, StatusCode},
};

#[derive(Debug, Clone)]
struct CurrentUser {
    id: i64,
    username: String,
}

#[async_trait]
impl<S> FromRequestParts<S> for CurrentUser
where
    S: Send + Sync,
{
    type Rejection = (StatusCode, &'static str);

    async fn from_request_parts(parts: &mut Parts, _state: &S) -> Result<Self, Self::Rejection> {
        let auth_header = parts
            .headers
            .get("authorization")
            .and_then(|h| h.to_str().ok())
            .ok_or((StatusCode::UNAUTHORIZED, "Missing authorization header"))?;

        let token = auth_header.strip_prefix("Bearer ")
            .ok_or((StatusCode::UNAUTHORIZED, "Invalid authorization format"))?;

        // 实际应用中应验证 JWT
        Ok(CurrentUser {
            id: 1,
            username: "user".to_string(),
        })
    }
}

async fn protected_route(current_user: CurrentUser) -> String {
    format!("Hello, {}!", current_user.username)
}
```

#### 错误处理

```rust
use axum::{
    response::{IntoResponse, Response},
    Json,
    http::StatusCode,
};
use serde_json::json;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum AppError {
    #[error("验证错误: {0}")]
    Validation(String),
    #[error("未找到资源")]
    NotFound,
    #[error("未授权")]
    Unauthorized,
    #[error("内部服务器错误")]
    Internal,
}

#[derive(Debug, serde::Serialize)]
struct ErrorResponse {
    code: String,
    message: String,
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, code, message) = match &self {
            AppError::Validation(msg) => (StatusCode::BAD_REQUEST, "VALIDATION_ERROR", msg.clone()),
            AppError::NotFound => (StatusCode::NOT_FOUND, "NOT_FOUND", "资源不存在".to_string()),
            AppError::Unauthorized => (StatusCode::UNAUTHORIZED, "UNAUTHORIZED", "请先登录".to_string()),
            AppError::Internal => (StatusCode::INTERNAL_SERVER_ERROR, "INTERNAL_ERROR", "服务器错误".to_string()),
        };

        let body = Json(ErrorResponse { code: code.to_string(), message });
        (status, body).into_response()
    }
}

pub type Result<T> = std::result::Result<T, AppError>;
```

### 3.4 最佳实践

#### 项目结构

```
src/
├── main.rs              # 应用入口
├── config/              # 配置管理
├── routes/              # 路由定义
├── handlers/            # 请求处理器
├── models/              # 数据模型
├── services/            # 业务逻辑
├── repositories/        # 数据访问
├── middleware/          # 中间件
├── error/               # 错误处理
└── utils/               # 工具函数
```

#### 性能优化

| 优化项 | 说明 |
|--------|------|
| 使用 Arc<State> | 减少状态克隆 |
| 启用压缩 | 减少传输大小 |
| 连接池 | 复用数据库连接 |
| 缓存 | 减少重复计算 |

---

## 4. Tonic gRPC 框架

### 4.1 简介

Tonic 是一个基于 Tokio 的 gRPC 实现，提供：

- **性能**: 基于 HTTP/2，支持多路复用
- **类型安全**: 基于 Protocol Buffers 生成代码
- **流支持**: 支持双向流、客户端流、服务端流
- **互操作性**: 与其他语言 gRPC 实现兼容

### 4.2 核心概念

| 类型 | 描述 | 示例 |
|------|------|------|
| Unary | 一元调用 | `rpc GetUser(Request) returns (User)` |
| Server Streaming | 服务端流 | `rpc ListUsers(Request) returns (stream User)` |
| Client Streaming | 客户端流 | `rpc Upload(stream Chunk) returns (Status)` |
| Bidirectional | 双向流 | `rpc Chat(stream Message) returns (stream Message)` |

### 4.3 示例代码

#### Protocol Buffers 定义

```protobuf
syntax = "proto3";
package user;

service UserService {
    rpc GetUser (GetUserRequest) returns (User);
    rpc ListUsers (ListUsersRequest) returns (stream User);
    rpc CreateUser (CreateUserRequest) returns (User);
    rpc Chat (stream ChatMessage) returns (stream ChatMessage);
}

message GetUserRequest { int64 id = 1; }
message CreateUserRequest { string name = 1; string email = 2; }
message ChatMessage { string user = 1; string content = 2; }

message User {
    int64 id = 1;
    string name = 2;
    string email = 3;
}
```

#### Build 配置

```rust
// build.rs
fn main() {
    tonic_build::configure()
        .build_server(true)
        .build_client(true)
        .compile(&["proto/user.proto"], &["proto"])
        .expect("Failed to compile protos");
}
```

#### 服务端实现

```rust
use tonic::{transport::Server, Request, Response, Status};
use tokio_stream::wrappers::ReceiverStream;
use tokio::sync::mpsc;
use std::time::Duration;

pub mod pb {
    tonic::include_proto!("user");
}

use pb::{
    user_service_server::{UserService, UserServiceServer},
    *,
};

#[derive(Debug, Default)]
pub struct UserServiceImpl;

#[tonic::async_trait]
impl UserService for UserServiceImpl {
    async fn get_user(
        &self,
        request: Request<GetUserRequest>,
    ) -> Result<Response<User>, Status> {
        let user = User {
            id: request.into_inner().id,
            name: "Test".to_string(),
            email: "test@example.com".to_string(),
        };
        Ok(Response::new(user))
    }

    type ListUsersStream = ReceiverStream<Result<User, Status>>;

    async fn list_users(
        &self,
        _request: Request<ListUsersRequest>,
    ) -> Result<Response<Self::ListUsersStream>, Status> {
        let (tx, rx) = mpsc::channel(128);

        tokio::spawn(async move {
            for i in 0..10 {
                let user = User {
                    id: i,
                    name: format!("User {}", i),
                    email: format!("user{}@example.com", i),
                };
                if tx.send(Ok(user)).await.is_err() { break; }
                tokio::time::sleep(Duration::from_millis(100)).await;
            }
        });

        Ok(Response::new(ReceiverStream::new(rx)))
    }

    async fn create_user(
        &self,
        request: Request<CreateUserRequest>,
    ) -> Result<Response<User>, Status> {
        let req = request.into_inner();
        Ok(Response::new(User {
            id: 1,
            name: req.name,
            email: req.email,
        }))
    }

    type ChatStream = ReceiverStream<Result<ChatMessage, Status>>;

    async fn chat(
        &self,
        request: Request<tonic::Streaming<ChatMessage>>,
    ) -> Result<Response<Self::ChatStream>, Status> {
        let mut inbound = request.into_inner();
        let (tx, rx) = mpsc::channel(128);

        tokio::spawn(async move {
            while let Some(msg) = inbound.message().await.unwrap_or(None) {
                let reply = ChatMessage {
                    user: "Server".to_string(),
                    content: format!("Echo: {}", msg.content),
                };
                if tx.send(Ok(reply)).await.is_err() { break; }
            }
        });

        Ok(Response::new(ReceiverStream::new(rx)))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let addr = "[::1]:50051".parse()?;
    let service = UserServiceImpl::default();

    println!("gRPC Server listening on {}", addr);

    Server::builder()
        .add_service(UserServiceServer::new(service))
        .serve(addr)
        .await?;

    Ok(())
}
```

#### 客户端实现

```rust
use tonic::transport::Channel;
use tokio_stream::StreamExt;

use pb::{
    user_service_client::UserServiceClient,
    *,
};

pub struct AppClient {
    client: UserServiceClient<Channel>,
}

impl AppClient {
    pub async fn connect(endpoint: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let channel = Channel::from_shared(endpoint.to_string())?
            .connect()
            .await?;
        Ok(Self { client: UserServiceClient::new(channel) })
    }

    pub async fn get_user(&mut self, id: i64) -> Result<User, tonic::Status> {
        let request = tonic::Request::new(GetUserRequest { id });
        let response = self.client.get_user(request).await?;
        Ok(response.into_inner())
    }

    pub async fn list_users(&mut self) -> Result<Vec<User>, tonic::Status> {
        let request = tonic::Request::new(ListUsersRequest {});
        let mut stream = self.client.list_users(request).await?.into_inner();

        let mut users = Vec::new();
        while let Some(user) = stream.next().await {
            users.push(user?);
        }
        Ok(users)
    }
}
```

### 4.4 最佳实践

| 实践 | 说明 |
|------|------|
| 使用连接池 | 复用 gRPC 连接 |
| 设置超时 | 避免无限等待 |
| 流式处理大文件 | 使用流式 API |
| 健康检查 | 实现 gRPC Health Checking |

---

## 5. Tower 中间件

### 5.1 简介

Tower 是一个模块化、可重用的网络服务组件库，提供：

- **Service Trait**: 统一的异步服务抽象
- **Layer Trait**: 可组合的中间件系统
- **常用中间件**: Timeout、Retry、Rate Limit 等

### 5.2 核心概念

#### Service Trait

```rust
pub trait Service<Request> {
    type Response;
    type Error;
    type Future: Future<Output = Result<Self::Response, Self::Error>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>>;
    fn call(&mut self, req: Request) -> Self::Future;
}
```

#### Layer Trait

```rust
pub trait Layer<S> {
    type Service;
    fn layer(&self, inner: S) -> Self::Service;
}
```

### 5.3 示例代码

#### 中间件组合

```rust
use tower::{ServiceBuilder, ServiceExt};
use tower::limit::{RateLimitLayer, ConcurrencyLimitLayer};
use tower::timeout::TimeoutLayer;
use std::time::Duration;
use tower_http::{
    trace::TraceLayer,
    compression::CompressionLayer,
    cors::CorsLayer,
};

pub fn create_service_stack<S, Req>(inner: S) -> impl Service<Req>
where
    S: Service<Req> + Clone + Send + 'static,
    S::Future: Send,
    Req: Send + 'static,
{
    ServiceBuilder::new()
        .layer(TraceLayer::new_for_http())
        .layer(TimeoutLayer::new(Duration::from_secs(30)))
        .layer(RateLimitLayer::new(100, Duration::from_secs(1)))
        .layer(ConcurrencyLimitLayer::new(50))
        .layer(CompressionLayer::new())
        .layer(CorsLayer::permissive())
        .service(inner)
}
```

#### 自定义 Layer

```rust
use tower::{Layer, Service};
use std::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
    time::Instant,
};

#[derive(Clone, Debug)]
pub struct TimingLayer;

impl<S> Layer<S> for TimingLayer {
    type Service = TimingService<S>;

    fn layer(&self, inner: S) -> Self::Service {
        TimingService { inner }
    }
}

#[derive(Clone, Debug)]
pub struct TimingService<S> {
    inner: S,
}

impl<S, B> Service<Request<B>> for TimingService<S>
where
    S: Service<Request<B>, Response = Response> + Send + Clone + 'static,
    S::Future: Send + 'static,
    B: Send + 'static,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, req: Request<B>) -> Self::Future {
        let start = Instant::now();
        let method = req.method().clone();
        let uri = req.uri().clone();
        let mut inner = self.inner.clone();

        Box::pin(async move {
            let response = inner.call(req).await?;
            let duration = start.elapsed();
            println!("[TIMING] {} {} took {:?}", method, uri, duration);
            Ok(response)
        })
    }
}
```

#### 熔断器

```rust
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CircuitState {
    Closed,
    Open { until: Instant },
    HalfOpen,
}

pub struct CircuitBreaker {
    state: Arc<RwLock<CircuitState>>,
    failure_threshold: u32,
    timeout: Duration,
    consecutive_failures: Arc<RwLock<u32>>,
}

impl CircuitBreaker {
    pub fn new(failure_threshold: u32, timeout: Duration) -> Self {
        Self {
            state: Arc::new(RwLock::new(CircuitState::Closed)),
            failure_threshold,
            timeout,
            consecutive_failures: Arc::new(RwLock::new(0)),
        }
    }

    pub async fn call<F, Fut, T>(&self, operation: F) -> Result<T, &'static str>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, Box<dyn std::error::Error>>>,
    {
        {
            let state = self.state.read().await;
            match &*state {
                CircuitState::Open { until } if Instant::now() < *until => {
                    return Err("Circuit breaker is open");
                }
                CircuitState::Open { .. } => {
                    drop(state);
                    let mut state = self.state.write().await;
                    *state = CircuitState::HalfOpen;
                }
                _ => {}
            }
        }

        match operation().await {
            Ok(result) => {
                *self.consecutive_failures.write().await = 0;
                Ok(result)
            }
            Err(_) => {
                let mut failures = self.consecutive_failures.write().await;
                *failures += 1;
                if *failures >= self.failure_threshold {
                    let mut state = self.state.write().await;
                    *state = CircuitState::Open { until: Instant::now() + self.timeout };
                }
                Err("Operation failed")
            }
        }
    }
}
```

### 5.4 最佳实践

| 实践 | 说明 |
|------|------|
| 顺序很重要 | 中间件执行顺序影响行为 |
| 使用 ServiceBuilder | 类型安全的方式组合中间件 |
| 实现 Clone | Service 需要实现 Clone |
| 避免耗时操作 | 中间件中避免长时间计算 |

#### 中间件顺序建议

```rust
ServiceBuilder::new()
    .layer(TraceLayer::new_for_http())      // 1. 日志记录
    .layer(TimeoutLayer::new(Duration::from_secs(30)))  // 2. 超时
    .layer(RateLimitLayer::new(100, Duration::from_secs(1)))  // 3. 限流
    .layer(ConcurrencyLimitLayer::new(50))  // 4. 并发限制
    .layer(CompressionLayer::new())          // 5. 压缩
    .layer(CorsLayer::permissive())          // 6. CORS
    .service(inner)
```

---

## 6. Tracing 可观测性

### 6.1 简介

Tracing 是 Rust 生态的分布式追踪和日志框架，提供：

- **结构化日志**: 支持结构化字段
- **Span 追踪**: 追踪请求在系统中的完整路径
- **与 OpenTelemetry 集成**: 支持导出到 Jaeger、Zipkin
- **低开销**: 设计用于高吞吐量场景

### 6.2 核心概念

| 概念 | 说明 | 示例 |
|------|------|------|
| `Span` | 具有生命周期的上下文 | 数据库查询、HTTP 请求 |
| `Event` | 瞬间发生的事件 | 日志记录、错误 |
| `Subscriber` | 收集和处理追踪数据 | 输出到控制台 |
| `Layer` | 可组合的 Subscriber 组件 | 过滤、格式化 |

### 6.3 示例代码

#### 基础使用

```rust
use tracing::{info, debug, error, span, Level, Instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_tracing() {
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::try_from_default_env()
            .unwrap_or_else(|_| "info".into()))
        .with(tracing_subscriber::fmt::layer().json())
        .init();
}

pub fn basic_logging() {
    info!("Application started");
    info!(user_id = 42, action = "login", "User performed action");
}

#[tracing::instrument(
    name = "process_order",
    skip(db),
    fields(order_id = %order.id),
    level = "info"
)]
pub async fn process_order(order: Order, db: &Database) -> Result<Receipt, Error> {
    debug!("Validating order");
    validate_order(&order)?;

    let result = async {
        debug!("Charging payment");
        charge_payment(&order).await
    }
    .instrument(span!(Level::DEBUG, "process_payment"))
    .await?;

    info!(payment_id = %result.id, "Payment processed");
    Ok(Receipt { order_id: order.id, payment_id: result.id })
}
```

#### OpenTelemetry 集成

```rust
use opentelemetry::{
    global,
    trace::TracerProvider,
    KeyValue,
};
use opentelemetry_sdk::{
    propagation::TraceContextPropagator,
    trace::TracerProvider as SdkTracerProvider,
    Resource,
};
use tracing_opentelemetry::OpenTelemetryLayer;
use tracing_subscriber::layer::SubscriberExt;

pub fn init_otel(service_name: &str, otlp_endpoint: &str) -> SdkTracerProvider {
    global::set_text_map_propagator(TraceContextPropagator::new());

    let resource = Resource::new(vec![
        KeyValue::new("service.name", service_name.to_string()),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
    ]);

    let tracer_provider = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_endpoint(otlp_endpoint)
        .with_trace_config(
            opentelemetry_sdk::trace::Config::default()
                .with_resource(resource),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)
        .expect("Failed to install OpenTelemetry pipeline");

    let tracer = tracer_provider.tracer(service_name);

    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer())
        .with(OpenTelemetryLayer::new(tracer))
        .init();

    tracer_provider
}
```

### 6.4 最佳实践

| 实践 | 说明 |
|------|------|
| 使用 `#[instrument]` | 自动创建 span |
| 使用结构化字段 | 便于查询和分析 |
| 设置合适的级别 | DEBUG 开发，INFO 生产 |
| 传播 trace context | 实现分布式追踪 |

---

## 7. 生产级架构示例

### 7.1 微服务架构

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│ API Gateway │────▶│  Service A  │────▶│  Database   │
│   (Axum)    │     │  (Axum/gRPC)│     │(PostgreSQL) │
└─────────────┘     └─────────────┘     └─────────────┘
       │                   │
       │             ┌─────────────┐
       └────────────▶│  Service B  │────▶│    Cache    │
                     │  (Tonic)    │     │   (Redis)   │
                     └─────────────┘     └─────────────┘
```

### 7.2 完整项目示例

#### 项目结构

```
myapp/
├── Cargo.toml
├── build.rs
├── src/
│   ├── main.rs          # 应用入口
│   ├── lib.rs
│   ├── config.rs        # 配置管理
│   ├── app.rs           # 应用构建
│   ├── error.rs         # 错误处理
│   ├── telemetry.rs     # 可观测性
│   ├── shutdown.rs      # 优雅关闭
│   ├── routes/          # 路由定义
│   ├── handlers/        # 请求处理器
│   ├── services/        # 业务逻辑
│   ├── middleware/      # 中间件
│   └── proto/           # protobuf
├── proto/
└── tests/
```

#### 主入口

```rust
// src/main.rs
use myapp::{app, config, telemetry};
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = config::load_config()?;
    let _otel_guard = telemetry::init(&config.telemetry)?;

    tracing::info!("Starting application");

    let app = app::create_app(Arc::new(config)).await?;
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;

    axum::serve(listener, app)
        .with_graceful_shutdown(myapp::shutdown::signal())
        .await?;

    tracing::info!("Application stopped");
    Ok(())
}
```

#### 应用构建

```rust
// src/app.rs
use axum::Router;
use std::sync::Arc;
use tower::ServiceBuilder;
use tower_http::{
    trace::TraceLayer,
    cors::CorsLayer,
    compression::CompressionLayer,
};

pub async fn create_app(config: Arc<Config>) -> Result<Router, Box<dyn std::error::Error>> {
    let api_routes = routes::api_routes(config.clone());

    let app = Router::new()
        .nest("/api/v1", api_routes)
        .layer(
            ServiceBuilder::new()
                .layer(TraceLayer::new_for_http())
                .layer(CompressionLayer::new())
                .layer(CorsLayer::permissive()),
        );

    Ok(app)
}
```

#### 优雅关闭

```rust
// src/shutdown.rs
use tokio::signal;
use std::time::Duration;

pub async fn signal() {
    let ctrl_c = async {
        signal::ctrl_c().await.expect("Failed to install Ctrl+C handler");
    };

    #[cfg(unix)]
    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("Failed to install signal handler")
            .recv()
            .await;
    };

    #[cfg(not(unix))]
    let terminate = std::future::pending::<()>();

    tokio::select! {
        _ = ctrl_c => tracing::info!("Received Ctrl+C"),
        _ = terminate => tracing::info!("Received SIGTERM"),
    }

    tracing::info!("Starting graceful shutdown...");
    tokio::time::sleep(Duration::from_secs(5)).await;
    tracing::info!("Shutdown complete");
}
```

---

## 8. 性能调优指南

### 8.1 运行时调优

```rust
use tokio::runtime::Builder;

fn create_optimized_runtime() -> tokio::runtime::Runtime {
    Builder::new_multi_thread()
        .worker_threads(num_cpus::get())
        .max_blocking_threads(512)
        .thread_stack_size(2 * 1024 * 1024)
        .enable_all()
        .event_interval(61)
        .global_queue_interval(61)
        .max_io_events_per_tick(1024)
        .build()
        .expect("Failed to create runtime")
}
```

### 8.2 内存优化

```rust
use bytes::BytesMut;

pub struct BufferPool {
    pool: Arc<crossbeam::queue::SegQueue<BytesMut>>,
}

impl BufferPool {
    pub fn acquire(&self) -> BytesMut {
        self.pool.pop().unwrap_or_else(|| BytesMut::with_capacity(4096))
    }

    pub fn release(&self, mut buf: BytesMut) {
        buf.clear();
        self.pool.push(buf);
    }
}
```

### 8.3 网络优化

```rust
pub fn create_optimized_http_client() -> reqwest::Client {
    reqwest::Client::builder()
        .pool_max_idle_per_host(100)
        .pool_idle_timeout(Duration::from_secs(90))
        .connect_timeout(Duration::from_secs(10))
        .timeout(Duration::from_secs(30))
        .tcp_keepalive(Duration::from_secs(60))
        .tcp_nodelay(true)
        .build()
        .expect("Failed to build HTTP client")
}
```

### 8.4 性能检查清单

| 检查项 | 优先级 |
|--------|--------|
| 使用 spawn_blocking 处理 CPU 密集型任务 | P0 |
| 限制并发任务数量 | P0 |
| 配置合适的线程池大小 | P0 |
| 使用连接池 | P0 |
| 启用压缩 | P1 |
| 配置合理的超时 | P1 |
| 启用 HTTP/2 | P2 |

---

## 9. 常见问题排查

### 9.1 性能问题

```rust
// 启用 Tokio Console
#[tokio::main]
async fn main() {
    console_subscriber::init();
    // ...
}
```

### 9.2 调试技巧

```bash
# 启用详细日志
RUST_LOG=debug,tokio=trace cargo run

# 使用 jemalloc 分析内存
MALLOC_CONF=stats_print:true cargo run
```

---

## 10. 附录

### 10.1 推荐依赖版本

```toml
[dependencies]
# 异步运行时
tokio = { version = "1.43", features = ["full"] }

# Web 框架
axum = "0.8"
tower = "0.5"
tower-http = { version = "0.6", features = ["full"] }

# gRPC
tonic = "0.13"
prost = "0.13"

# 可观测性
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
opentelemetry = "0.28"

# HTTP 客户端
reqwest = { version = "0.12", features = ["json", "rustls-tls"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 其他
chrono = { version = "0.4", features = ["serde"] }
uuid = { version = "1.15", features = ["v4", "serde"] }
thiserror = "2.0"
anyhow = "1.0"
futures = "0.3"
bytes = "1.10"
```

### 10.2 参考资源

| 资源 | 链接 |
|------|------|
| Tokio 官方教程 | <https://tokio.rs/tokio/tutorial> |
| Rust Async Book | <https://rust-lang.github.io/async-book/> |
| Axum 文档 | <https://docs.rs/axum/> |
| Tonic 文档 | <https://docs.rs/tonic/> |
| Tower 文档 | <https://docs.rs/tower/> |
| Tracing 文档 | <https://docs.rs/tracing/> |

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-17
**状态**: ✅ 已完成
