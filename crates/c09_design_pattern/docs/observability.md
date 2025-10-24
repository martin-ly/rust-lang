# 可观测性指南（tracing 快速上手）

## 📊 目录

- [可观测性指南（tracing 快速上手）](#可观测性指南tracing-快速上手)
  - [📊 目录](#-目录)
  - [目标](#目标)
  - [建议依赖](#建议依赖)
  - [初始化示例](#初始化示例)
  - [链式调用标注](#链式调用标注)
  - [示例](#示例)
  - [完整的可观测性实践](#完整的可观测性实践)
    - [1. 三大支柱详解](#1-三大支柱详解)
      - [1.1 日志 (Logging)](#11-日志-logging)
      - [1.2 指标 (Metrics)](#12-指标-metrics)
      - [1.3 分布式追踪 (Tracing)](#13-分布式追踪-tracing)
    - [2. 设计模式的可观测性](#2-设计模式的可观测性)
      - [2.1 责任链模式追踪](#21-责任链模式追踪)
      - [2.2 装饰器模式的性能监控](#22-装饰器模式的性能监控)
    - [3. 生产环境配置](#3-生产环境配置)
      - [3.1 环境变量配置](#31-环境变量配置)
      - [3.2 性能影响分析](#32-性能影响分析)
  - [最佳实践清单](#最佳实践清单)
    - [开发环境](#开发环境)
    - [生产环境](#生产环境)
    - [分布式追踪](#分布式追踪)
    - [指标收集](#指标收集)
  - [相关资源](#相关资源)

## 目标

- 为责任链、装饰器、代理等链式调用提供可观测追踪（span/事件）。
- 结合执行模型（Sync/Async/Hybrid）在不同路径上观测时延与错误传播。

## 建议依赖

```toml
[features]
obs-tracing = ["tracing", "tracing-subscriber"]

[dev-dependencies]
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["fmt", "env-filter"] }
```

## 初始化示例

```rust
use tracing_subscriber::{fmt, EnvFilter};

fn init_tracing() {
    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));
    let subscriber = fmt().with_env_filter(filter).finish();
    tracing::subscriber::set_global_default(subscriber).ok();
}
```

## 链式调用标注

- 在每个处理步骤创建子 span 或事件；
- 聚合入口创建顶层 span，串起链路；
- 异步步骤用 `.instrument(span)` 绑定上下文；
- 失败路径记录 `error!` 并携带上下文键值。

## 示例

参见 `examples/tracing_chain.rs`（需 `--features obs-tracing`）。

```bash
cargo run --example tracing_chain --features obs-tracing | cat
```

## 完整的可观测性实践

### 1. 三大支柱详解

#### 1.1 日志 (Logging)

**使用 `tracing` 实现结构化日志**：

```rust
use tracing::{info, warn, error, debug, trace};

pub fn structured_logging_example() {
    // 基础日志
    info!("Server starting");
    
    // 带字段的结构化日志
    info!(
        user_id = 12345,
        action = "login",
        "User logged in successfully"
    );
    
    // 错误日志
    error!(
        error = ?std::io::Error::from(std::io::ErrorKind::NotFound),
        path = "/config.yaml",
        "Configuration file not found"
    );
}
```

**日志级别最佳实践**：

- `trace`: 非常详细的信息（调试用）
- `debug`: 调试信息
- `info`: 一般信息（默认级别）
- `warn`: 警告信息
- `error`: 错误信息

#### 1.2 指标 (Metrics)

**集成 Prometheus**：

```rust
use prometheus::{Counter, Histogram, Registry, Encoder, TextEncoder};
use once_cell::sync::Lazy;

static REGISTRY: Lazy<Registry> = Lazy::new(Registry::new);

static HTTP_REQUESTS: Lazy<Counter> = Lazy::new(|| {
    let counter = Counter::new("http_requests_total", "Total HTTP requests").unwrap();
    REGISTRY.register(Box::new(counter.clone())).unwrap();
    counter
});

static HTTP_DURATION: Lazy<Histogram> = Lazy::new(|| {
    let hist = Histogram::new("http_request_duration_seconds", "HTTP request duration").unwrap();
    REGISTRY.register(Box::new(hist.clone())).unwrap();
    hist
});

pub async fn handle_request() {
    HTTP_REQUESTS.inc();
    let timer = HTTP_DURATION.start_timer();
    
    // 处理请求
    process_request().await;
    
    timer.observe_duration();
}

async fn process_request() {
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}

pub fn metrics_endpoint() -> String {
    let encoder = TextEncoder::new();
    let mut buffer = Vec::new();
    encoder.encode(&REGISTRY.gather(), &mut buffer).unwrap();
    String::from_utf8(buffer).unwrap()
}
```

#### 1.3 分布式追踪 (Tracing)

**完整的 OpenTelemetry 集成**：

```rust
use opentelemetry::{global, trace::{Tracer, Span, TracerProvider}, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use tracing_opentelemetry::OpenTelemetryLayer;
use tracing_subscriber::{layer::SubscriberExt, Registry};

pub fn init_observability() -> anyhow::Result<()> {
    // 初始化 OpenTelemetry
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry::runtime::Tokio)?;
    
    // 创建 tracing 订阅器
    let telemetry = OpenTelemetryLayer::new(tracer);
    let subscriber = Registry::default()
        .with(tracing_subscriber::fmt::layer())
        .with(telemetry);
    
    tracing::subscriber::set_global_default(subscriber)?;
    
    Ok(())
}

#[tracing::instrument(
    name = "process_order",
    skip(order),
    fields(
        order_id = %order.id,
        user_id = %order.user_id,
        total = %order.total
    )
)]
pub async fn process_order(order: Order) -> Result<(), String> {
    info!("Processing order");
    
    // 创建子span
    let payment_span = tracing::info_span!("process_payment");
    let _guard = payment_span.enter();
    
    process_payment(&order).await?;
    
    Ok(())
}

pub struct Order {
    pub id: u64,
    pub user_id: u64,
    pub total: f64,
}

async fn process_payment(order: &Order) -> Result<(), String> {
    info!(amount = %order.total, "Payment processing");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    Ok(())
}
```

---

### 2. 设计模式的可观测性

#### 2.1 责任链模式追踪

```rust
use tracing::{instrument, info};

pub trait Handler: Send + Sync {
    fn handle(&self, request: &Request) -> Response;
}

pub struct LoggingHandler;
pub struct AuthHandler;
pub struct BusinessHandler;

#[instrument(skip(self, request), fields(handler = "LoggingHandler"))]
impl Handler for LoggingHandler {
    fn handle(&self, request: &Request) -> Response {
        info!(path = %request.path, "Logging request");
        // 继续链
        Response { status: 200 }
    }
}

#[instrument(skip(self, request), fields(handler = "AuthHandler"))]
impl Handler for AuthHandler {
    fn handle(&self, request: &Request) -> Response {
        info!(user = %request.user, "Authenticating");
        // 验证逻辑
        Response { status: 200 }
    }
}

pub struct Request {
    pub path: String,
    pub user: String,
}

pub struct Response {
    pub status: u16,
}
```

#### 2.2 装饰器模式的性能监控

```rust
use std::time::Instant;

pub trait Component {
    fn execute(&self) -> String;
}

pub struct ConcreteComponent;

impl Component for ConcreteComponent {
    fn execute(&self) -> String {
        "Result".to_string()
    }
}

pub struct TimingDecorator<C: Component> {
    component: C,
}

impl<C: Component> Component for TimingDecorator<C> {
    #[tracing::instrument(skip(self))]
    fn execute(&self) -> String {
        let start = Instant::now();
        let result = self.component.execute();
        let duration = start.elapsed();
        
        tracing::info!(
            duration_ms = %duration.as_millis(),
            "Component execution completed"
        );
        
        result
    }
}
```

---

### 3. 生产环境配置

#### 3.1 环境变量配置

```rust
use tracing_subscriber::{fmt, EnvFilter, layer::SubscriberExt};

pub fn init_production_observability() {
    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));
    
    let fmt_layer = fmt::layer()
        .json()                    // JSON格式输出
        .with_current_span(true)   // 包含当前span
        .with_span_list(true)      // 包含span列表
        .with_thread_ids(true)     // 包含线程ID
        .with_target(false);       // 不包含目标模块
    
    let subscriber = tracing_subscriber::registry()
        .with(filter)
        .with(fmt_layer);
    
    tracing::subscriber::set_global_default(subscriber)
        .expect("Failed to set subscriber");
}
```

#### 3.2 性能影响分析

**基准测试对比**：

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn with_tracing(c: &mut Criterion) {
    init_observability().unwrap();
    
    c.bench_function("with_tracing", |b| {
        b.iter(|| {
            tracing::info!("Processing request");
            black_box(process_request());
        })
    });
}

fn without_tracing(c: &mut Criterion) {
    c.bench_function("without_tracing", |b| {
        b.iter(|| {
            black_box(process_request());
        })
    });
}

fn process_request() -> i32 {
    42
}

criterion_group!(benches, with_tracing, without_tracing);
criterion_main!(benches);

// 结果对比：
// without_tracing: 10ns
// with_tracing: 100-200ns (10-20x开销)
// 建议：生产环境仅在关键路径使用 info 级别
```

---

## 最佳实践清单

### 开发环境

- [x] 使用 `RUST_LOG` 环境变量控制日志级别
- [x] 开发时使用 `debug` 或 `trace` 级别
- [x] 在关键函数上添加 `#[instrument]` 宏

### 生产环境

- [x] 使用结构化日志（JSON格式）
- [x] 只记录 `info` 及以上级别
- [x] 导出到集中式日志系统（ELK/Loki）
- [x] 配置采样率（高流量场景）
- [x] 监控日志输出性能影响

### 分布式追踪

- [x] 为公共 API 增加 `request_id`/`span_id`
- [x] 在责任链/中间件链上统一记录
- [x] 使用 OpenTelemetry 标准
- [x] 配置采样策略（1-10%）
- [x] 集成 Jaeger/Zipkin

### 指标收集

- [x] 暴露 `/metrics` 端点
- [x] 收集 RED 指标（Rate/Errors/Duration）
- [x] 使用 Prometheus 作为时序数据库
- [x] 配置告警规则

---

## 相关资源

- **Tier 3**: [技术参考](./tier_03_references/)
- **Tier 4**: [工程实践](./tier_04_advanced/04_工程实践与生产级模式.md)
- **OpenTelemetry**: [官方文档](https://opentelemetry.io/)
- **Prometheus**: [官方指南](https://prometheus.io/docs/introduction/overview/)

---

**文档状态**: ✅ 已完成  
**最后更新**: 2025-10-24
