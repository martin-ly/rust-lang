# Web 示例（Web Examples）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [Web 示例（Web Examples）索引](#web-示例web-examples索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心示例](#-核心示例)
    - [1. Web 框架（Web Frameworks）](#1-web-框架web-frameworks)
    - [2. HTTP 服务（HTTP Services）](#2-http-服务http-services)
    - [3. 数据库集成（Database Integration）](#3-数据库集成database-integration)
    - [4. 认证与授权（Authentication \& Authorization）](#4-认证与授权authentication--authorization)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c67_web_development/src/`](#cratesc67_web_developmentsrc)
      - [`crates/c13_microservice/src/`](#cratesc13_microservicesrc)
    - [快速开始示例](#快速开始示例)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块提供 Rust Web 开发的实用示例，涵盖 Web 框架、HTTP 服务、数据库集成和认证授权等核心主题。
所有示例均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **Web 开发**: 专注于 Rust Web 开发实践
- **最佳实践**: 基于 Rust 社区最新 Web 实践
- **完整覆盖**: 涵盖多个 Web 开发场景
- **易于理解**: 提供详细的 Web 开发说明和代码示例

## 📚 核心示例

### 1. Web 框架（Web Frameworks）

**推荐库**: `axum`, `actix-web`, `warp`, `rocket`, `tower`

- **Axum 框架**: 基于 Tower 的现代 Web 框架
- **Actix Web**: 高性能 Web 框架
- **Warp 框架**: 函数式 Web 框架
- **Rocket 框架**: 类型安全的 Web 框架

**相关资源**:

- [axum 文档](https://docs.rs/axum/)
- [actix-web 文档](https://actix.rs/)
- [warp 文档](https://docs.rs/warp/)
- [rocket 文档](https://rocket.rs/)

### 2. HTTP 服务（HTTP Services）

**推荐库**: `hyper`, `reqwest`, `ureq`, `http`

- **REST API 实现**: RESTful API 设计和实现
- **GraphQL 服务**: GraphQL 服务器实现
- **WebSocket 服务**: WebSocket 服务器实现
- **静态文件服务**: 静态文件服务、CDN 集成

**相关资源**:

- [hyper 文档](https://docs.rs/hyper/)
- [reqwest 文档](https://docs.rs/reqwest/)
- [async-graphql 文档](https://docs.rs/async-graphql/)

### 3. 数据库集成（Database Integration）

**推荐库**: `sqlx`, `diesel`, `sea-orm`, `mongodb`, `redis`

- **SQLite 集成**: SQLite 数据库操作
- **PostgreSQL 集成**: PostgreSQL 数据库操作
- **MongoDB 集成**: MongoDB 数据库操作
- **Redis 集成**: Redis 缓存和消息队列

**相关资源**:

- [sqlx 文档](https://docs.rs/sqlx/)
- [diesel 文档](https://diesel.rs/)
- [sea-orm 文档](https://www.sea-ql.org/SeaORM/)
- [mongodb 文档](https://docs.rs/mongodb/)

### 4. 认证与授权（Authentication & Authorization）

**推荐库**: `jsonwebtoken`, `oauth2`, `bcrypt`, `argon2`, `axum-login`

- **JWT 认证**: JWT token 生成和验证
- **OAuth 集成**: OAuth 2.0 集成
- **会话管理**: 会话管理、Cookie 处理
- **权限控制**: 基于角色的访问控制（RBAC）

**相关资源**:

- [jsonwebtoken 文档](https://docs.rs/jsonwebtoken/)
- [oauth2 文档](https://docs.rs/oauth2/)
- [axum-login 文档](https://docs.rs/axum-login/)

## 💻 实践与样例

### 代码示例位置

- **Web 示例**: [crates/c67_web_development](../../../crates/c67_web_development/)
- **微服务**: [crates/c13_microservice](../../../crates/c13_microservice/)
- **网络编程**: [crates/c10_networks](../../../crates/c10_networks/)

### 文件级清单（精选）

#### `crates/c67_web_development/src/`

- `web_frameworks.rs` - Web 框架示例
- `http_services.rs` - HTTP 服务示例
- `database_integration.rs` - 数据库集成示例
- `authentication.rs` - 认证授权示例

#### `crates/c13_microservice/src/`

- `web_microservice.rs` - Web 微服务示例
- `api_gateway.rs` - API 网关示例
- `service_mesh.rs` - 服务网格示例

### 快速开始示例

```rust
// Axum Web 服务器示例
use axum::{routing::get, Router};

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(handler));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    axum::serve(listener, app).await.unwrap();
}

async fn handler() -> &'static str {
    "Hello, World!"
}
```

```rust
// Actix Web 服务器示例
use actix_web::{web, App, HttpServer, Responder};

async fn index() -> impl Responder {
    "Hello, World!"
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .route("/", web::get().to(index))
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
```

---

## 🔗 相关索引

- **理论基础（并发模型）**: [`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- **编程范式（异步）**: [`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- **应用领域（云基础设施）**: [`../../04_application_domains/06_cloud_infrastructure/00_index.md`](../../04_application_domains/06_cloud_infrastructure/00_index.md)

---

## 📚 内容文档

- **[Web 服务器基础](./01_web_server_basics.md)** - Web 服务器构建实践示例 ✅

## 🧭 导航

- **返回实用示例**: [`../00_index.md`](../00_index.md)
- **异步示例**: [`../07_async_examples/00_index.md`](../07_async_examples/00_index.md)
- **系统示例**: [`../09_system_examples/00_index.md`](../09_system_examples/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-15
**维护者**: 项目维护者
**状态**: 已完善 ✅
