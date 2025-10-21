# 第3层：应用开发层 (Application Development Layer)

> **定位**: 构建生产级应用所需的 Web、数据库、消息队列等核心组件  
> **特点**: 完整生态、生产就绪、最佳实践  
> **版本**: Rust 1.90 (2025)

---

## 📋 核心类别

### 1. Web 框架 ([`web_frameworks/`](./web_frameworks/))

| 框架 | 特点 | 性能 | 学习曲线 | 推荐度 |
|------|------|------|----------|--------|
| **axum** | 基于 tokio, 类型安全 | ⚡⚡⚡⚡⚡ | 低 | ⭐⭐⭐⭐⭐ |
| **actix-web** | 高性能, 成熟 | ⚡⚡⚡⚡⚡ | 中 | ⭐⭐⭐⭐⭐ |
| **rocket** | 易用, 功能全 | ⚡⚡⚡⚡ | 低 | ⭐⭐⭐⭐ |

**快速示例** (axum):

```rust
use axum::{Router, routing::get};

#[tokio::main]
async fn main() {
    let app = Router::new().route("/", get(|| async { "Hello, World!" }));
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

**性能**: 240K-295K req/s (单核)

---

### 2. HTTP 客户端 ([`http_clients/`](./http_clients/))

| 库名 | 特点 | 推荐度 |
|------|------|--------|
| **reqwest** | 高级API, 易用 | ⭐⭐⭐⭐⭐ |
| **hyper** | 底层, 高性能 | ⭐⭐⭐⭐⭐ |

**快速示例** (reqwest):

```rust
#[tokio::main]
async fn main() -> Result<(), reqwest::Error> {
    let res = reqwest::get("https://httpbin.org/ip")
        .await?
        .json::<HashMap<String, String>>()
        .await?;
    println!("{:?}", res);
    Ok(())
}
```

---

### 3. 数据库 ORM ([`databases/`](./databases/))

| 库名 | 类型 | 异步 | 推荐度 |
|------|------|------|--------|
| **sqlx** | 编译期 SQL 检查 | ✅ | ⭐⭐⭐⭐⭐ |
| **diesel** | 类型安全 ORM | ❌ (v2.2+) | ⭐⭐⭐⭐⭐ |
| **sea-orm** | 异步 ORM | ✅ | ⭐⭐⭐⭐ |

**快速示例** (sqlx):

```rust
use sqlx::postgres::PgPoolOptions;

#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    let pool = PgPoolOptions::new()
        .max_connections(5)
        .connect("postgres://localhost/mydb").await?;
    
    let row: (i64,) = sqlx::query_as("SELECT $1")
        .bind(150_i64)
        .fetch_one(&pool).await?;
    
    println!("Result: {}", row.0);
    Ok(())
}
```

---

### 4. 消息队列 ([`message_queues/`](./message_queues/))

| 库名 | MQ | 推荐度 |
|------|------|--------|
| **rdkafka** | Kafka | ⭐⭐⭐⭐⭐ |
| **lapin** | RabbitMQ | ⭐⭐⭐⭐ |
| **async-nats** | NATS | ⭐⭐⭐⭐ |

---

### 5. 缓存 ([`caching/`](./caching/))

| 库名 | 特点 | 推荐度 |
|------|------|--------|
| **redis** | Redis 客户端 | ⭐⭐⭐⭐⭐ |
| **moka** | 内存缓存 | ⭐⭐⭐⭐ |

---

### 6. gRPC ([`grpc/`](./grpc/))

| 库名 | 特点 | 推荐度 |
|------|------|--------|
| **tonic** | 完整 gRPC | ⭐⭐⭐⭐⭐ |
| **prost** | Protobuf 编解码 | ⭐⭐⭐⭐⭐ |

---

## 🎯 场景快速启动

### 后端 API 服务

```toml
[dependencies]
tokio = { version = "1", features = ["full"] }
axum = "0.7"
sqlx = { version = "0.8", features = ["runtime-tokio-rustls", "postgres"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

### 微服务

```toml
[dependencies]
tokio = { version = "1", features = ["full"] }
tonic = "0.12"
prost = "0.13"
rdkafka = "0.36"
tracing = "0.1"
```

---

**详细文档**: [应用开发完整指南 →](./guides/)

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
