# Rust 可观测性实战指南

> **定位**: 生产环境监控、追踪、日志集成
> **版本**: Rust 1.96.0+ / Edition 2024
> **适用场景**: 微服务、云原生应用、高性能服务

---

## 📋 目录

- [Rust 可观测性实战指南](.#rust-可观测性实战指南)
  - [📋 目录](.#-目录)
  - [🎯 三大支柱](.#-三大支柱)
  - [📊 Metrics (指标)](.#-metrics-指标)
    - [Prometheus 集成](.#prometheus-集成)
    - [Metrics 库选择](.#metrics-库选择)
  - [📝 Logging (日志)](.#-logging-日志)
    - [Tracing 生态](.#tracing-生态)
    - [结构化日志](.#结构化日志)
  - [🔗 Tracing (分布式追踪)](.#-tracing-分布式追踪)
    - [OpenTelemetry 集成](.#opentelemetry-集成)
    - [Jaeger/Zipkin 导出](.#jaegerzipkin-导出)
  - [📐 黄金信号](.#-黄金信号)
  - [🔧 实战模式](.#-实战模式)
    - [Axum 中间件集成](.#axum-中间件集成)
    - [异步任务追踪](.#异步任务追踪)
  - [📊 与 Go/Java 对比](.#-与-gojava-对比)
  - [🔗 参考资源](.#-参考资源)

---

## 🎯 三大支柱

```text
┌─────────────┐  ┌─────────────┐  ┌─────────────┐
│   Metrics   │  │    Logs     │  │   Traces    │
│ "发生了什么" │  │"为什么发生"  │  │"在哪里发生"  │
├─────────────┤  ├─────────────┤  ├─────────────┤
│ 聚合数值     │  │ 文本记录     │  │ 请求链路     │
│ 计数/直方图  │  │ 结构化/JSON  │  │ 跨服务 span  │
│ 时序数据库   │  │ 日志聚合     │  │ 采样/全量    │
└─────────────┘  └─────────────┘  └─────────────┘
         ↓              ↓              ↓
    ┌─────────────────────────────────────┐
    │         Grafana / Dashboard         │
    │    统一可视化 + 告警 + 探索           │
    └─────────────────────────────────────┘
```

---

## 📊 Metrics (指标)

### Prometheus 集成

```rust
use metrics::{counter, gauge, histogram, describe_counter};
use metrics_exporter_prometheus::PrometheusBuilder;

fn init_metrics() {
    PrometheusBuilder::new()
        .install_recorder()
        .expect("failed to install Prometheus recorder");

    describe_counter!(
        "http_requests_total",
        "Total number of HTTP requests"
    );
}

// 使用
fn handle_request() {
    counter!("http_requests_total", 1,
        "method" => "GET",
        "status" => "200"
    );
}

fn record_duration(duration_ms: f64) {
    histogram!("http_request_duration_ms", duration_ms);
}

fn update_connections(count: usize) {
    gauge!("active_connections", count as f64);
}
```

### Metrics 库选择

| 库 | 场景 | 性能 | 生态 |
|----|------|------|------|
| `metrics` | 通用指标 | ⭐⭐⭐ | Prometheus 原生 |
| `prometheus` | 直接集成 | ⭐⭐⭐ | 官方 crate |
| `opentelemetry` | 统一可观测性 | ⭐⭐ | 全栈支持 |

---

## 📝 Logging (日志)

### Tracing 生态

`tracing` 是 Rust 的现代日志/追踪框架：

```rust
use tracing::{info, warn, error, span, Level};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

fn init_logging() {
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer().json())
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();
}

#[tracing::instrument]
async fn process_order(order_id: u64) {
    info!(order_id, "processing order");

    let span = span!(Level::INFO, "validation", order_id);
    let _enter = span.enter();

    if let Err(e) = validate_order(order_id).await {
        error!(error = %e, "validation failed");
        return;
    }

    info!("order processed successfully");
}
```

**`tracing::instrument` 魔法**:

- 自动生成 span
- 记录函数参数（可过滤）
- 记录执行时间
- 关联错误与调用上下文

### 结构化日志

```rust
use tracing::info;

// 键值对格式 → 自动 JSON 化
info!(
    user_id = 42,
    action = "purchase",
    amount = 199.99,
    "user completed purchase"
);

// 输出 (JSON layer):
// {
//   "timestamp": "2026-05-08T12:00:00Z",
//   "level": "INFO",
//   "fields": {
//     "user_id": 42,
//     "action": "purchase",
//     "amount": 199.99,
//     "message": "user completed purchase"
//   },
//   "target": "my_app::orders"
// }
```

---

## 🔗 Tracing (分布式追踪)

### OpenTelemetry 集成

```rust
use opentelemetry::global;
use opentelemetry_sdk::trace::TracerProvider;
use tracing_opentelemetry::OpenTelemetryLayer;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

fn init_tracing() {
    let provider = TracerProvider::builder()
        .with_simple_exporter(
            opentelemetry_otlp::new_exporter()
                .http()
                .with_endpoint("http://otel-collector:4318")
        )
        .build();

    global::set_tracer_provider(provider.clone());

    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer())
        .with(OpenTelemetryLayer::new(provider.tracer("my-service")))
        .init();
}
```

### Jaeger/Zipkin 导出

```rust
// 通过 OTLP 协议导出到 Jaeger
// Jaeger 原生支持 OTLP (gRPC/HTTP)
//
// docker run -d --name jaeger \
//   -p 16686:16686 \
//   -p 4317:4317 \
//   -p 4318:4318 \
//   jaegertracing/all-in-one:latest
```

---

## 📐 黄金信号

Google SRE 推荐的四个关键指标：

| 信号 | 指标 | Rust 实现 |
|------|------|-----------|
| **延迟** | 请求处理时间 | `histogram!("request_duration_ms", duration)` |
| **流量** | 每秒请求数 | `counter!("requests_total", 1)` |
| **错误** | 错误率 | `counter!("errors_total", 1, "type" => "500")` |
| **饱和度** | 资源利用率 | `gauge!("cpu_usage", percent)` |

---

## 🔧 实战模式

### Axum 中间件集成

```rust
use axum::{Router, middleware::from_fn};
use tracing::info;

async fn trace_middleware<B>(
    request: axum::extract::Request<B>,
    next: axum::middleware::Next<B>,
) -> axum::response::Response {
    let start = std::time::Instant::now();
    let method = request.method().clone();
    let uri = request.uri().clone();

    let response = next.run(request).await;

    let duration = start.elapsed();
    info!(
        method = %method,
        uri = %uri,
        status = response.status().as_u16(),
        duration_ms = duration.as_secs_f64() * 1000.0,
        "request completed"
    );

    response
}

let app = Router::new()
    .layer(from_fn(trace_middleware));
```

### 异步任务追踪

```rust
use tracing::{info_span, Instrument};

// 为后台任务创建独立 span
let background_span = info_span!("background_worker", task_id = %uuid::Uuid::new_v4());

tokio::spawn(
    async move {
        loop {
            process_batch().await;
            tokio::time::sleep(Duration::from_secs(60)).await;
        }
    }
    .instrument(background_span)
);
```

---

## 📊 与 Go/Java 对比

| 维度 | Rust (tracing) | Go (OpenTelemetry) | Java (Micrometer) |
|------|----------------|-------------------|-------------------|
| 开销 | 极低 (零成本抽象) | 低 | 中 |
| 生态 | 年轻但快速演进 | 成熟 | 非常成熟 |
| 性能 | ⭐⭐⭐ | ⭐⭐ | ⭐⭐ |
| 学习曲线 | 中 | 低 | 低 |
| 最佳场景 | 高性能服务 | 云原生微服务 | 企业级应用 |

**Rust 优势**:

- `tracing` 的 span 机制比传统日志更强大
- 编译期优化消除未使用的追踪代码
- 与 async/await 深度集成

---

## 🔗 参考资源

- [tracing 文档](https://docs.rs/tracing)
- [metrics 文档](https://docs.rs/metrics)
- [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust)
- [项目 C06 异步模块](../../crates/c06_async)
- [Kubernetes 部署指南](kubernetes_deployment_guide.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
