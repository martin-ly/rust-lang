# Actix-web vs Axum: Rust Web 框架选择指南

> **定位**: 两大主流 Rust Web 框架的深度对比
> **版本**: actix-web 4.x, axum 0.8.x
> **适用场景**: API 服务、微服务、Web 应用

---

## 📋 目录

- [Actix-web vs Axum: Rust Web 框架选择指南](#actix-web-vs-axum-rust-web-框架选择指南)
  - [📋 目录](#-目录)
  - [🎯 核心对比](#-核心对比)
  - [⚡ Actix-web](#-actix-web)
  - [🔷 Axum](#-axum)
  - [📊 性能对比](#-性能对比)
  - [🔄 中间件系统](#-中间件系统)
    - [Actix-web](#actix-web)
    - [Axum (Tower)](#axum-tower)
  - [📐 选择决策树](#-选择决策树)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 核心对比

| 维度 | Actix-web | Axum |
|------|-----------|------|
| **底层模型** | Actor (actix-rt) | Tower Service |
| **学习曲线** | 中等 | 较低 |
| **生态集成** | 自包含 | 与 Tower/Tokio 深度整合 |
| **中间件** | 内置 Transform | Tower Layer |
| **Handler 签名** | 多种类型 | 函数 + Extractor |
| **状态管理** | Data<T> | State<T> |
| **成熟程度** | 非常成熟 (2018+) | 快速成熟 (2021+) |
| **Tokio 集成** | 兼容 | 原生 |

---

## ⚡ Actix-web

基于 Actor 模型的高性能 Web 框架：

```rust
use actix_web::{web, App, HttpServer, Responder};

async fn hello(name: web::Path<String>) -> impl Responder {
    format!("Hello {name}!")
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .route("/hello/{name}", web::get().to(hello))
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
```

**特点**:

- 每个连接由独立 Actor 处理
- 内置工作线程池
- 强大的 WebSocket 支持
- 丰富的生态系统

---

## 🔷 Axum

基于 Tower Service 的模块化 Web 框架：

```rust
use axum::{Router, routing::get, extract::Path};

async fn hello(Path(name): Path<String>) -> String {
    format!("Hello {name}!")
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/hello/:name", get(hello));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

**特点**:

- 函数式 Handler 设计
- Extractor 系统类型安全
- 与 Tower 中间件无缝集成
- Tokio 原生支持

---

## 📊 性能对比

| 场景 | Actix-web | Axum | 说明 |
|------|-----------|------|------|
| 纯 JSON 序列化 | ~650k req/s | ~600k req/s | 差距 < 10% |
| 带数据库查询 | ~50k req/s | ~48k req/s | 瓶颈在 DB |
| WebSocket | 优秀 | 良好 | Actix 更成熟 |
| 内存占用 | 较低 | 较低 | 相当 |

> 基准测试数据来自 TechEmpower Framework Benchmarks (2026)

---

## 🔄 中间件系统

### Actix-web

```rust
use actix_web::{dev::Service as _, middleware};

App::new()
    .wrap(middleware::Logger::default())
    .wrap(middleware::Compress::default())
    .wrap(middleware::DefaultHeaders::new())
```

### Axum (Tower)

```rust
use tower_http::{trace::TraceLayer, compression::CompressionLayer};

Router::new()
    .layer(TraceLayer::new_for_http())
    .layer(CompressionLayer::new())
```

**Tower 生态优势**: 同一套中间件可用于 tonic (gRPC)、hyper 等

---

## 📐 选择决策树

```
需要最高性能 / 成熟生态?
├── 是 ──→ 需要 Actor 模型?
│           ├── 是 ──→ Actix-web
│           └── 否 ──→ Actix-web (生态更全)
└── 否 ──→ 偏好函数式 / Tower 生态?
            ├── 是 ──→ Axum
            └── 否 ──→ 两者皆可

已有 Tokio 生态深度使用? ──是──→ Axum (更自然)
需要快速上手? ──是──→ Axum (学习曲线更平缓)
```

---

## 🔗 参考资源

- [Actix-web 文档](https://actix.rs/)
- [Axum 文档](https://docs.rs/axum)
- [Tower 文档](https://docs.rs/tower)
- [项目 C10 网络模块](../../crates/c10_networks/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-08
**状态**: ✅ 已完善
