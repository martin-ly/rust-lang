# 应用监控（Application Monitoring）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [应用监控](#应用监控application-monitoring)
  - [概述](#概述)
  - [日志记录](#日志记录)
  - [指标收集](#指标收集)
  - [分布式追踪](#分布式追踪)
  - [实践示例](#实践示例)
  - [最佳实践](#最佳实践)
  - [参考资料](#参考资料)

---

## 概述

应用监控是确保系统可靠性和性能的关键。Rust 提供了多种监控工具和库，包括日志记录、指标收集和分布式追踪。

## 日志记录

### 使用 tracing

```rust
use tracing::{info, error, warn, debug};
use tracing_subscriber;

#[tokio::main]
async fn main() {
    // 初始化 tracing
    tracing_subscriber::fmt::init();

    info!("应用启动");

    match run_application().await {
        Ok(_) => info!("应用正常退出"),
        Err(e) => error!("应用错误: {}", e),
    }
}

async fn run_application() -> Result<(), String> {
    debug!("执行应用逻辑");
    // 应用逻辑
    Ok(())
}
```

### 结构化日志

```rust
use tracing::{info, instrument};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct User {
    id: u32,
    name: String,
}

#[instrument]
async fn process_user(user: User) -> Result<(), String> {
    info!(
        user_id = user.id,
        user_name = %user.name,
        "处理用户"
    );

    // 处理逻辑
    Ok(())
}
```

### 日志级别配置

```rust
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

fn init_logging() {
    tracing_subscriber::registry()
        .with(
            EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info".into())
        )
        .with(tracing_subscriber::fmt::layer())
        .init();
}
```

## 指标收集

### 使用 metrics

```rust
use metrics::{counter, gauge, histogram};
use metrics_exporter_prometheus::PrometheusBuilder;

fn init_metrics() {
    let builder = PrometheusBuilder::new();
    builder.install().expect("无法安装指标导出器");
}

fn record_metrics() {
    // 计数器
    counter!("requests_total", 1, "method" => "GET", "status" => "200");

    // 仪表盘
    gauge!("memory_usage_bytes", 1024.0);

    // 直方图
    histogram!("request_duration_seconds", 0.5);
}
```

### 自定义指标

```rust
use metrics::{register_counter, Counter};

lazy_static::lazy_static! {
    static ref REQUEST_COUNTER: Counter = register_counter!(
        "http_requests_total",
        "method" => "unknown"
    );
}

fn handle_request(method: &str) {
    REQUEST_COUNTER.increment(1);
    // 处理请求
}
```

## 分布式追踪

### 使用 OpenTelemetry

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::Registry;

fn init_tracing() {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)
        .expect("无法初始化追踪");

    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);

    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .init();
}

#[tracing::instrument]
async fn process_request() {
    // 自动创建 span
    // 处理请求
}
```

## 实践示例

### 示例 1：完整的监控系统

```rust
use tracing::{info, error, instrument};
use metrics::{counter, histogram, register_counter, Counter};
use std::time::Instant;

lazy_static::lazy_static! {
    static ref HTTP_REQUESTS: Counter = register_counter!("http_requests_total");
    static ref HTTP_DURATION: Counter = register_counter!("http_duration_seconds_total");
}

pub struct MonitoringMiddleware;

impl MonitoringMiddleware {
    #[instrument]
    pub async fn handle_request<F, Fut>(handler: F) -> Result<String, String>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<String, String>>,
    {
        let start = Instant::now();
        HTTP_REQUESTS.increment(1);

        info!("处理请求开始");

        let result = handler().await;

        let duration = start.elapsed();
        histogram!("request_duration_seconds", duration.as_secs_f64());

        match &result {
            Ok(_) => info!("请求成功"),
            Err(e) => error!("请求失败: {}", e),
        }

        result
    }
}
```

### 示例 2：健康检查端点

```rust
use axum::{
    routing::get,
    Router,
    response::Json,
};
use serde_json::json;
use std::sync::Arc;
use tokio::sync::RwLock;

#[derive(Clone)]
struct HealthStatus {
    status: Arc<RwLock<String>>,
}

async fn health_check(
    axum::extract::State(state): axum::extract::State<HealthStatus>,
) -> Json<serde_json::Value> {
    let status = state.status.read().await.clone();
    Json(json!({
        "status": status,
        "timestamp": chrono::Utc::now().to_rfc3339(),
    }))
}

async fn readiness_check() -> Json<serde_json::Value> {
    // 检查依赖服务
    Json(json!({
        "ready": true,
    }))
}

#[tokio::main]
async fn main() {
    let health_status = HealthStatus {
        status: Arc::new(RwLock::new("healthy".to_string())),
    };

    let app = Router::new()
        .route("/health", get(health_check))
        .route("/ready", get(readiness_check))
        .with_state(health_status);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    axum::serve(listener, app).await.unwrap();
}
```

### 示例 3：性能监控

```rust
use metrics::{histogram, counter};
use std::time::Instant;

pub struct PerformanceMonitor;

impl PerformanceMonitor {
    pub fn measure<F, T>(operation: &str, f: F) -> T
    where
        F: FnOnce() -> T,
    {
        let start = Instant::now();
        let result = f();
        let duration = start.elapsed();

        histogram!(
            "operation_duration_seconds",
            duration.as_secs_f64(),
            "operation" => operation
        );

        counter!(
            "operation_total",
            1,
            "operation" => operation
        );

        result
    }

    pub async fn measure_async<F, Fut, T>(operation: &str, f: F) -> T
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        let start = Instant::now();
        let result = f().await;
        let duration = start.elapsed();

        histogram!(
            "operation_duration_seconds",
            duration.as_secs_f64(),
            "operation" => operation
        );

        result
    }
}
```

## 最佳实践

### 1. 日志级别

```rust
// 使用适当的日志级别
tracing::trace!("详细的调试信息");
tracing::debug!("调试信息");
tracing::info!("一般信息");
tracing::warn!("警告信息");
tracing::error!("错误信息");
```

### 2. 结构化日志

```rust
// 使用结构化字段
info!(
    user_id = 123,
    action = "login",
    ip = "192.168.1.1",
    "用户登录"
);
```

### 3. 指标命名

```rust
// 使用一致的指标命名约定
// 格式: <namespace>_<metric_name>_<unit>
counter!("http_requests_total");
histogram!("http_request_duration_seconds");
gauge!("memory_usage_bytes");
```

### 4. 采样

```rust
// 对高频操作进行采样
if rand::random::<f64>() < 0.1 {
    histogram!("operation_duration_seconds", duration.as_secs_f64());
}
```

## 参考资料

- [监控索引](./00_index.md)
- [质量保障索引](../00_index.md)
- [Tracing 文档](https://docs.rs/tracing/)
- [Metrics 文档](https://docs.rs/metrics/)
- [OpenTelemetry 文档](https://opentelemetry.io/)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回质量保障: [`../00_index.md`](../00_index.md)
