# 可观测性 (Observability)

**类别**: 横切关注点  
**重要程度**: ⭐⭐⭐⭐⭐ (生产必备)  
**更新日期**: 2025-10-20

---

## 📋 目录

- [可观测性 (Observability)](#可观测性-observability)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. tracing (结构化日志 ⭐⭐⭐⭐⭐)](#1-tracing-结构化日志-)
      - [基础用法](#基础用法)
      - [Span 和 Event](#span-和-event)
      - [异步函数支持](#异步函数支持)
      - [高级配置](#高级配置)
    - [2. metrics (指标收集 ⭐⭐⭐⭐⭐)](#2-metrics-指标收集-)
      - [基础用法2](#基础用法2)
      - [Prometheus 导出](#prometheus-导出)
      - [自定义指标](#自定义指标)
    - [3. OpenTelemetry (分布式追踪 ⭐⭐⭐⭐⭐)](#3-opentelemetry-分布式追踪-)
      - [配置 OpenTelemetry](#配置-opentelemetry)
      - [分布式追踪](#分布式追踪)
    - [4. log (传统日志 ⭐⭐⭐⭐)](#4-log-传统日志-)
    - [5. tokio-console (Tokio 调试 💡)](#5-tokio-console-tokio-调试-)
  - [💡 最佳实践](#-最佳实践)
    - [1. 三层日志策略](#1-三层日志策略)
    - [2. 结构化日志字段](#2-结构化日志字段)
    - [3. 生产环境配置](#3-生产环境配置)
    - [4. 完整可观测性栈](#4-完整可观测性栈)
  - [📊 工具对比](#-工具对比)
    - [日志库对比](#日志库对比)
    - [指标库对比](#指标库对比)
  - [🎯 实战场景](#-实战场景)
    - [场景1: Web 服务监控](#场景1-web-服务监控)
    - [场景2: 分布式追踪](#场景2-分布式追踪)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

可观测性（Observability）是理解系统运行状态的关键能力，包括**日志（Logs）**、**指标（Metrics）**和**追踪（Traces）**三大支柱。

---

## 🔧 核心工具

### 1. tracing (结构化日志 ⭐⭐⭐⭐⭐)

**添加依赖**:

```toml
[dependencies]
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
```

**用途**: 应用级结构化日志和追踪

#### 基础用法

```rust
use tracing::{info, warn, error, debug, trace, instrument};
use tracing_subscriber;

#[instrument]
fn process_order(order_id: u64, user_id: u64) {
    info!("Processing order");
    
    // 自动捕获函数参数
    debug!("Validating order");
    
    // 添加额外字段
    info!(amount = 99.99, "Order validated");
}

fn main() {
    // 初始化订阅者
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_target(false)
        .with_thread_ids(true)
        .with_line_number(true)
        .init();
    
    process_order(123, 456);
}
```

#### Span 和 Event

```rust
use tracing::{info, span, Level};

fn main() {
    tracing_subscriber::fmt::init();
    
    // 创建 span
    let span = span!(Level::INFO, "my_span", user_id = 123);
    let _enter = span.enter();
    
    info!("Inside span");
    
    // Span 嵌套
    {
        let child_span = span!(Level::DEBUG, "child_span");
        let _enter = child_span.enter();
        info!("Inside child span");
    }
}
```

#### 异步函数支持

```rust
use tracing::{info, instrument};

#[instrument]
async fn fetch_user(user_id: u64) -> User {
    info!("Fetching user from database");
    
    // 异步操作
    let user = database::get_user(user_id).await;
    
    info!(username = %user.name, "User fetched");
    
    user
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();
    
    let user = fetch_user(123).await;
}
```

#### 高级配置

```rust
use tracing_subscriber::{
    fmt,
    layer::SubscriberExt,
    util::SubscriberInitExt,
    EnvFilter,
};

fn setup_tracing() {
    tracing_subscriber::registry()
        // 环境变量控制日志级别
        .with(EnvFilter::from_default_env()
            .add_directive("my_app=debug".parse().unwrap())
            .add_directive("hyper=info".parse().unwrap()))
        // JSON 格式输出
        .with(fmt::layer().json())
        .init();
}
```

---

### 2. metrics (指标收集 ⭐⭐⭐⭐⭐)

**添加依赖**:

```toml
[dependencies]
metrics = "0.21"
metrics-exporter-prometheus = "0.13"
```

**用途**: 应用性能指标收集

#### 基础用法2

```rust
use metrics::{counter, gauge, histogram};

fn handle_request() {
    // 计数器：累加值
    counter!("requests_total", "endpoint" => "/api/users").increment(1);
    
    // 仪表盘：当前值
    gauge!("active_connections").set(42.0);
    
    // 直方图：分布统计
    histogram!("request_duration_seconds").record(0.123);
}
```

#### Prometheus 导出

```rust
use metrics_exporter_prometheus::PrometheusBuilder;
use std::net::SocketAddr;

#[tokio::main]
async fn main() {
    // 启动 Prometheus exporter
    let addr: SocketAddr = "0.0.0.0:9000".parse().unwrap();
    PrometheusBuilder::new()
        .with_http_listener(addr)
        .install()
        .expect("Failed to install Prometheus exporter");
    
    // 应用逻辑
    loop {
        handle_request();
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    }
}
```

#### 自定义指标

```rust
use metrics::{describe_counter, describe_gauge, Unit};

fn setup_metrics() {
    describe_counter!(
        "http_requests_total",
        Unit::Count,
        "Total HTTP requests"
    );
    
    describe_gauge!(
        "memory_usage_bytes",
        Unit::Bytes,
        "Current memory usage"
    );
    
    describe_histogram!(
        "response_time_seconds",
        Unit::Seconds,
        "HTTP response time"
    );
}
```

---

### 3. OpenTelemetry (分布式追踪 ⭐⭐⭐⭐⭐)

**添加依赖**:

```toml
[dependencies]
opentelemetry = { version = "0.21", features = ["trace", "metrics"] }
opentelemetry-otlp = { version = "0.14", features = ["trace", "metrics"] }
opentelemetry_sdk = { version = "0.21", features = ["rt-tokio"] }
tracing-opentelemetry = "0.22"
```

**用途**: 分布式系统追踪和遥测

#### 配置 OpenTelemetry

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    Resource,
    trace::{self, Sampler},
};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

fn init_tracer() {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", "my-service"),
                    KeyValue::new("service.version", "1.0.0"),
                ]))
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)
        .unwrap();
    
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();
}

#[tokio::main]
async fn main() {
    init_tracer();
    
    // 应用逻辑
    
    // 关闭时刷新
    global::shutdown_tracer_provider();
}
```

#### 分布式追踪

```rust
use tracing::{info, instrument};
use opentelemetry::global;

#[instrument]
async fn call_service_a() {
    info!("Calling Service A");
    
    // 自动传播 trace context
    let client = reqwest::Client::new();
    let response = client
        .get("http://service-a/api")
        .send()
        .await
        .unwrap();
    
    info!("Service A responded");
}

#[instrument]
async fn call_service_b() {
    info!("Calling Service B");
    call_service_a().await;
}
```

---

### 4. log (传统日志 ⭐⭐⭐⭐)

**添加依赖**: `cargo add log env_logger`  
**用途**: 经典日志接口（与 tracing 兼容）

```rust
use log::{info, warn, error, debug};

fn main() {
    env_logger::init();
    
    info!("Application started");
    warn!("This is a warning");
    error!("This is an error");
    debug!("Debug information");
}
```

---

### 5. tokio-console (Tokio 调试 💡)

**添加依赖**:

```toml
[dependencies]
console-subscriber = "0.2"
```

**用途**: Tokio 异步任务可视化调试

```rust
fn main() {
    console_subscriber::init();
    
    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(async {
            // 异步代码
        });
}
```

---

## 💡 最佳实践

### 1. 三层日志策略

```rust
use tracing::{info, instrument, Level};

// 应用层：业务日志
#[instrument(level = "info")]
async fn create_order(order: Order) -> Result<OrderId> {
    info!(order_id = %order.id, "Creating order");
    
    // 服务层：详细日志
    let result = order_service.create(order).await?;
    
    info!(order_id = %result, "Order created successfully");
    Ok(result)
}

// 基础设施层：调试日志
#[instrument(level = "debug")]
async fn save_to_db(order: &Order) -> Result<()> {
    debug!(table = "orders", "Saving to database");
    // ...
    Ok(())
}
```

### 2. 结构化日志字段

```rust
use tracing::{info, error};
use serde_json::json;

#[instrument(
    fields(
        user_id = %user.id,
        request_id = %request_id,
        endpoint = %endpoint
    )
)]
async fn handle_api_request(user: User, request_id: String, endpoint: String) {
    info!("Handling API request");
    
    // 动态添加字段
    tracing::Span::current().record("status", &"processing");
    
    match process_request().await {
        Ok(result) => {
            info!(
                status = "success",
                response_size = result.len(),
                "Request completed"
            );
        }
        Err(e) => {
            error!(
                error = %e,
                error_type = std::any::type_name_of_val(&e),
                "Request failed"
            );
        }
    }
}
```

### 3. 生产环境配置

```rust
use tracing_subscriber::{
    fmt,
    prelude::*,
    EnvFilter,
};

fn init_production_logging() {
    tracing_subscriber::registry()
        // 环境变量控制
        .with(
            EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| EnvFilter::new("info"))
        )
        // JSON 格式（便于日志聚合）
        .with(
            fmt::layer()
                .json()
                .with_current_span(true)
                .with_span_list(true)
                .with_target(true)
                .with_thread_ids(true)
                .with_file(true)
                .with_line_number(true)
        )
        .init();
}
```

### 4. 完整可观测性栈

```rust
use axum::{Router, routing::get};
use metrics_exporter_prometheus::PrometheusBuilder;
use std::net::SocketAddr;
use tracing::info;

#[tokio::main]
async fn main() {
    // 1. 初始化 Tracing
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_target(false)
        .init();
    
    // 2. 初始化 Metrics (Prometheus)
    let metrics_addr: SocketAddr = "0.0.0.0:9000".parse().unwrap();
    PrometheusBuilder::new()
        .with_http_listener(metrics_addr)
        .install()
        .expect("Failed to install metrics exporter");
    
    info!("Metrics endpoint: http://0.0.0.0:9000/metrics");
    
    // 3. 应用路由
    let app = Router::new()
        .route("/health", get(health_check));
    
    let app_addr: SocketAddr = "0.0.0.0:3000".parse().unwrap();
    info!("Starting server on {}", app_addr);
    
    axum_server::bind(app_addr)
        .serve(app.into_make_service())
        .await
        .unwrap();
}

async fn health_check() -> &'static str {
    metrics::counter!("health_check_total").increment(1);
    "OK"
}
```

---

## 📊 工具对比

### 日志库对比

| 工具 | 结构化 | 异步 | 性能 | 生态 | 推荐度 |
|------|--------|------|------|------|--------|
| **tracing** | ✅✅ | ✅ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 🌟 首选 |
| **log** | ❌ | ❌ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 💡 兼容性 |
| **slog** | ✅ | ❌ | ⭐⭐⭐⭐ | ⭐⭐⭐ | 💡 备选 |

### 指标库对比

| 工具 | 格式 | 导出 | 性能 | 推荐度 |
|------|------|------|------|--------|
| **metrics** | 通用 | 多种 | ⭐⭐⭐⭐⭐ | 🌟 首选 |
| **prometheus** | Prometheus | 自带 | ⭐⭐⭐⭐ | 💡 直接集成 |

---

## 🎯 实战场景

### 场景1: Web 服务监控

```rust
use axum::{
    Router,
    routing::get,
    middleware::{self, Next},
    extract::Request,
    response::Response,
};
use metrics::{counter, histogram};
use std::time::Instant;
use tracing::info;

async fn metrics_middleware(req: Request, next: Next) -> Response {
    let start = Instant::now();
    let method = req.method().clone();
    let uri = req.uri().clone();
    
    counter!("http_requests_total",
        "method" => method.to_string(),
        "endpoint" => uri.path().to_string()
    ).increment(1);
    
    let response = next.run(req).await;
    
    let duration = start.elapsed().as_secs_f64();
    histogram!("http_request_duration_seconds",
        "method" => method.to_string(),
        "endpoint" => uri.path().to_string(),
        "status" => response.status().as_u16().to_string()
    ).record(duration);
    
    response
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(|| async { "Hello, World!" }))
        .layer(middleware::from_fn(metrics_middleware));
    
    // ...
}
```

### 场景2: 分布式追踪

```rust
use tracing::{info, instrument};
use opentelemetry::global;

#[instrument]
async fn frontend_handler(request: Request) -> Response {
    info!("Frontend received request");
    
    // 调用后端服务
    let backend_response = call_backend_service(request).await;
    
    info!("Frontend sending response");
    backend_response
}

#[instrument]
async fn call_backend_service(request: Request) -> Response {
    info!("Backend processing request");
    
    // 调用数据库
    let data = query_database().await;
    
    Response::new(data)
}
```

---

## 🔗 相关资源

- [Tokio Tracing Guide](https://tokio.rs/tokio/topics/tracing)
- [OpenTelemetry Rust](https://opentelemetry.io/docs/instrumentation/rust/)
- [Prometheus Best Practices](https://prometheus.io/docs/practices/)

---

**导航**: [返回横切关注点](../README.md) | [下一类别：配置管理](../configuration/README.md)
