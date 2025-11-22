# 追踪和日志（Tracing and Logging）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [追踪和日志](#追踪和日志tracing-and-logging)
  - [概述](#概述)
  - [使用 tracing](#使用-tracing)
  - [结构化日志](#结构化日志)
  - [分布式追踪](#分布式追踪)
  - [实践示例](#实践示例)
  - [最佳实践](#最佳实践)
  - [参考资料](#参考资料)

---

## 概述

追踪和日志是可观测性的核心组件。Rust 的 `tracing` 库提供了强大的结构化日志和分布式追踪功能。

## 使用 tracing

### 基本设置

```rust
use tracing::{info, error, warn, debug, instrument};
use tracing_subscriber;

fn init_tracing() {
    tracing_subscriber::fmt::init();
}

#[tokio::main]
async fn main() {
    init_tracing();

    info!("应用启动");
    process_request().await;
    info!("应用关闭");
}

#[instrument]
async fn process_request() {
    debug!("开始处理请求");
    // 处理逻辑
    info!("请求处理完成");
}
```

### 日志级别

```rust
use tracing::{trace, debug, info, warn, error};

fn log_examples() {
    trace!("最详细的调试信息");
    debug!("调试信息");
    info!("一般信息");
    warn!("警告信息");
    error!("错误信息");
}
```

## 结构化日志

### 字段记录

```rust
use tracing::{info, instrument};

#[instrument]
async fn handle_user_request(user_id: u32, action: &str) {
    info!(
        user_id = user_id,
        action = action,
        "处理用户请求"
    );
}

// 使用结构化字段
fn log_with_fields() {
    let user_id = 123;
    let email = "user@example.com";

    info!(
        user_id = user_id,
        email = %email,
        "用户登录"
    );
}
```

### 事件记录

```rust
use tracing::{event, Level};

fn log_event() {
    event!(
        Level::INFO,
        user_id = 123,
        action = "purchase",
        amount = 99.99,
        "用户购买商品"
    );
}
```

## 分布式追踪

### OpenTelemetry 集成

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::Registry;

fn init_otel_tracing() {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)
        .expect("无法初始化 OpenTelemetry");

    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);

    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::layer())
        .init();
}

#[tracing::instrument]
async fn process_order(order_id: u32) {
    // 自动创建 span
    validate_order(order_id).await;
    process_payment(order_id).await;
    ship_order(order_id).await;
}

#[tracing::instrument]
async fn validate_order(order_id: u32) {
    // 子 span
}

#[tracing::instrument]
async fn process_payment(order_id: u32) {
    // 子 span
}

#[tracing::instrument]
async fn ship_order(order_id: u32) {
    // 子 span
}
```

## 实践示例

### 示例 1：Web 应用日志

```rust
use axum::{
    extract::Request,
    middleware::Next,
    response::Response,
};
use tracing::{info, instrument};

pub async fn logging_middleware(
    request: Request,
    next: Next,
) -> Response {
    let method = request.method().clone();
    let uri = request.uri().clone();

    info!(
        method = %method,
        uri = %uri,
        "收到请求"
    );

    let start = std::time::Instant::now();
    let response = next.run(request).await;
    let duration = start.elapsed();

    info!(
        method = %method,
        uri = %uri,
        status = response.status().as_u16(),
        duration_ms = duration.as_millis(),
        "请求完成"
    );

    response
}

#[instrument]
async fn handle_api_request(user_id: u32, endpoint: &str) -> Result<String, String> {
    info!("处理 API 请求");
    // 处理逻辑
    Ok("成功".to_string())
}
```

### 示例 2：错误追踪

```rust
use tracing::{error, instrument};
use std::error::Error;

#[instrument]
async fn risky_operation() -> Result<(), Box<dyn Error>> {
    match perform_operation().await {
        Ok(result) => {
            info!(result = ?result, "操作成功");
            Ok(())
        }
        Err(e) => {
            error!(
                error = %e,
                error_debug = ?e,
                "操作失败"
            );
            Err(e)
        }
    }
}

async fn perform_operation() -> Result<String, String> {
    // 操作逻辑
    Err("操作失败".to_string())
}
```

### 示例 3：性能追踪

```rust
use tracing::{info, instrument};
use std::time::Instant;

#[instrument]
async fn expensive_operation() {
    let start = Instant::now();

    // 执行操作
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    let duration = start.elapsed();
    info!(
        duration_ms = duration.as_millis(),
        "操作完成"
    );
}
```

## 最佳实践

### 1. 使用适当的日志级别

```rust
// ✅ 正确：使用适当的级别
tracing::debug!("调试信息");
tracing::info!("一般信息");
tracing::warn!("警告");
tracing::error!("错误");

// ❌ 错误：过度使用 error 级别
tracing::error!("用户登录");  // 应该使用 info
```

### 2. 结构化字段

```rust
// ✅ 正确：使用结构化字段
info!(
    user_id = 123,
    action = "login",
    ip = "192.168.1.1",
    "用户登录"
);

// ❌ 错误：使用字符串拼接
info!("用户 123 从 192.168.1.1 登录");  // 难以解析
```

### 3. 使用 instrument 宏

```rust
// ✅ 正确：使用 instrument 自动记录
#[instrument]
async fn process_request(user_id: u32) {
    // 自动记录函数名、参数等
}

// ❌ 错误：手动记录
async fn process_request(user_id: u32) {
    info!("process_request: user_id={}", user_id);
}
```

### 4. 错误上下文

```rust
use tracing::{error, instrument};

#[instrument]
async fn handle_error() -> Result<(), String> {
    match risky_operation().await {
        Ok(_) => Ok(()),
        Err(e) => {
            error!(
                error = %e,
                context = "处理用户请求时出错",
                "操作失败"
            );
            Err(e)
        }
    }
}
```

## 参考资料

- [可观测性示例索引](./00_index.md)
- [实践示例索引](../00_index.md)
- [Tracing 文档](https://docs.rs/tracing/)
- [OpenTelemetry 文档](https://opentelemetry.io/)

---

**导航**:
- 返回索引: [`00_index.md`](./00_index.md)
- 返回实践示例: [`../00_index.md`](../00_index.md)
