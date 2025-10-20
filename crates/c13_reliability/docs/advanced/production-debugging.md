# 生产环境调试

> **学习目标**：掌握在生产环境中诊断和修复问题的策略、工具和最佳实践。

---

## 📖 目录

- [生产环境调试](#生产环境调试)
  - [📖 目录](#-目录)
  - [生产调试挑战](#生产调试挑战)
    - [特殊约束](#特殊约束)
    - [调试原则](#调试原则)
  - [可观测性架构](#可观测性架构)
    - [三大支柱](#三大支柱)
    - [集成策略](#集成策略)
  - [日志系统](#日志系统)
    - [结构化日志](#结构化日志)
    - [日志级别](#日志级别)
    - [日志聚合](#日志聚合)
    - [日志查询](#日志查询)
  - [指标监控](#指标监控)
    - [Prometheus 集成](#prometheus-集成)
    - [RED 方法](#red-方法)
    - [自定义指标](#自定义指标)
    - [告警规则](#告警规则)
  - [分布式追踪](#分布式追踪)
    - [OpenTelemetry](#opentelemetry)
    - [Jaeger 集成](#jaeger-集成)
    - [Span 设计](#span-设计)
    - [性能分析](#性能分析)
  - [错误追踪](#错误追踪)
    - [Sentry 集成](#sentry-集成)
    - [自定义错误上下文](#自定义错误上下文)
    - [错误分组](#错误分组)
  - [性能分析1](#性能分析1)
    - [CPU Profiling](#cpu-profiling)
    - [内存分析](#内存分析)
    - [实时分析](#实时分析)
  - [健康检查](#健康检查)
    - [端点设计](#端点设计)
    - [依赖检查](#依赖检查)
    - [优雅降级](#优雅降级)
  - [金丝雀部署](#金丝雀部署)
    - [流量分配](#流量分配)
    - [监控指标](#监控指标)
    - [回滚策略](#回滚策略)
  - [故障排查流程](#故障排查流程)
    - [问题定位](#问题定位)
    - [根因分析](#根因分析)
    - [修复验证](#修复验证)
  - [常见生产问题](#常见生产问题)
    - [内存泄漏](#内存泄漏)
    - [CPU 高负载](#cpu-高负载)
    - [连接池耗尽](#连接池耗尽)
    - [死锁与活锁](#死锁与活锁)
  - [应急响应](#应急响应)
    - [事故分级](#事故分级)
    - [响应流程](#响应流程)
    - [事后复盘](#事后复盘)
  - [安全调试](#安全调试)
    - [敏感信息脱敏](#敏感信息脱敏)
    - [访问控制](#访问控制)
    - [审计日志](#审计日志)
  - [工具集成](#工具集成)
    - [Kubernetes](#kubernetes)
    - [Docker](#docker)
    - [Cloud Provider](#cloud-provider)
  - [最佳实践](#最佳实践)
    - [设计阶段](#设计阶段)
    - [开发阶段](#开发阶段)
    - [部署阶段](#部署阶段)
    - [运维阶段](#运维阶段)
  - [总结](#总结)
    - [1. 可观测性三大支柱](#1-可观测性三大支柱)
    - [2. 关键实践](#2-关键实践)
    - [3. 应急响应](#3-应急响应)
    - [4. 持续改进](#4-持续改进)
  - [相关资源](#相关资源)

---

## 生产调试挑战

### 特殊约束

生产环境调试与开发环境截然不同：

| 方面 | 开发环境 | 生产环境 |
|------|---------|---------|
| **访问权限** | 完全访问 | 受限访问 |
| **调试工具** | 全部可用 | 部分可用 |
| **性能影响** | 可以容忍 | 必须最小化 |
| **数据安全** | 测试数据 | 真实数据 |
| **可重现性** | 容易 | 困难 |
| **回滚成本** | 低 | 高 |

### 调试原则

```text
生产调试黄金法则
├─ 1. 非侵入性
│  └─ 最小化对系统的影响
├─ 2. 可观测性
│  └─ 提前埋点，而非事后补救
├─ 3. 安全第一
│  └─ 保护用户数据和隐私
├─ 4. 快速恢复
│  └─ 优先恢复服务，再深入分析
└─ 5. 持续改进
   └─ 每次故障都是学习机会
```

---

## 可观测性架构

### 三大支柱

```rust
// 完整的可观测性栈
use tracing::{info, error, instrument};
use prometheus::{IntCounter, Histogram};
use opentelemetry::trace::Tracer;

pub struct ObservabilityStack {
    // 日志
    logger: Logger,
    
    // 指标
    request_counter: IntCounter,
    response_time: Histogram,
    
    // 追踪
    tracer: Box<dyn Tracer + Send + Sync>,
}

impl ObservabilityStack {
    #[instrument(skip(self))]
    pub async fn handle_request(&self, req: Request) -> Response {
        // 1. 日志记录
        info!(
            request_id = %req.id,
            method = %req.method,
            path = %req.path,
            "Handling request"
        );
        
        // 2. 指标更新
        self.request_counter.inc();
        let timer = self.response_time.start_timer();
        
        // 3. 追踪上下文
        let span = self.tracer.start("handle_request");
        
        let result = self.process(req).await;
        
        timer.observe_duration();
        span.end();
        
        result
    }
}
```

### 集成策略

```rust
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_observability() -> Result<()> {
    // 日志层
    let fmt_layer = tracing_subscriber::fmt::layer()
        .json()
        .with_target(true)
        .with_thread_ids(true)
        .with_file(true)
        .with_line_number(true);
    
    // OpenTelemetry 层
    let tracer = opentelemetry_jaeger::new_agent_pipeline()
        .with_service_name("my-service")
        .install_simple()?;
    let telemetry_layer = tracing_opentelemetry::layer().with_tracer(tracer);
    
    // 过滤层
    let filter_layer = tracing_subscriber::EnvFilter::try_from_default_env()
        .or_else(|_| tracing_subscriber::EnvFilter::try_new("info"))?;
    
    // 组合所有层
    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .with(telemetry_layer)
        .init();
    
    Ok(())
}
```

---

## 日志系统

### 结构化日志

```rust
use tracing::{info, error, warn};
use serde_json::json;

#[instrument(fields(user_id, request_id))]
async fn process_payment(
    user_id: u64,
    request_id: Uuid,
    amount: Decimal,
) -> Result<PaymentResult> {
    info!(
        user_id = %user_id,
        request_id = %request_id,
        amount = %amount,
        currency = "USD",
        "Starting payment processing"
    );
    
    match charge_card(user_id, amount).await {
        Ok(charge_id) => {
            info!(
                charge_id = %charge_id,
                "Payment successful"
            );
            Ok(PaymentResult::Success(charge_id))
        }
        Err(e) => {
            error!(
                error = %e,
                error_type = e.type_name(),
                "Payment failed",
            );
            Err(e)
        }
    }
}
```

### 日志级别

```rust
// 生产环境日志策略
pub enum LogLevel {
    // ERROR: 需要立即关注
    Error,   // 例: 支付失败、数据库连接断开
    
    // WARN: 潜在问题
    Warn,    // 例: 重试成功、降级服务
    
    // INFO: 关键业务事件
    Info,    // 例: 用户注册、订单创建
    
    // DEBUG: 详细诊断信息 (生产通常关闭)
    Debug,   // 例: SQL 查询、API 请求详情
    
    // TRACE: 超详细信息 (仅开发)
    Trace,   // 例: 函数进入/退出
}

impl LogLevel {
    pub fn production_filter() -> &'static str {
        // 默认 INFO，特定模块 DEBUG
        "info,my_app::auth=debug,sqlx=warn"
    }
}
```

### 日志聚合

```rust
// 发送日志到中心化系统
use tracing_appender::rolling::{RollingFileAppender, Rotation};

pub fn setup_log_shipping() {
    // 本地文件 (备份)
    let file_appender = RollingFileAppender::new(
        Rotation::DAILY,
        "/var/log/my-app",
        "app.log"
    );
    
    // Stdout (容器环境，由 Fluentd/Logstash 收集)
    let stdout_layer = tracing_subscriber::fmt::layer()
        .json()
        .with_writer(std::io::stdout);
    
    // Loki (可选)
    let loki_layer = tracing_loki::layer(
        tracing_loki::url::Url::parse("http://loki:3100").unwrap(),
        vec![
            ("service".to_string(), "my-service".to_string()),
            ("env".to_string(), "production".to_string()),
        ].into_iter().collect(),
        vec![].into_iter().collect(),
    ).unwrap();
    
    tracing_subscriber::registry()
        .with(stdout_layer)
        .with(loki_layer)
        .init();
}
```

### 日志查询

```bash
# Loki 查询语言 (LogQL)

# 查找错误
{service="my-app"} |= "ERROR"

# 特定用户的请求
{service="my-app"} | json | user_id="12345"

# 慢查询
{service="my-app"} | json | duration > 1s

# 聚合统计
sum(rate({service="my-app"} |= "ERROR"[5m])) by (error_type)
```

---

## 指标监控

### Prometheus 集成

```rust
use prometheus::{
    Encoder, TextEncoder,
    IntCounter, IntGauge, Histogram, HistogramOpts,
    register_int_counter, register_int_gauge, register_histogram,
};
use lazy_static::lazy_static;

lazy_static! {
    // 计数器: 单调递增
    pub static ref HTTP_REQUESTS_TOTAL: IntCounter = register_int_counter!(
        "http_requests_total",
        "Total number of HTTP requests"
    ).unwrap();
    
    // 仪表: 可增可减
    pub static ref ACTIVE_CONNECTIONS: IntGauge = register_int_gauge!(
        "active_connections",
        "Number of active connections"
    ).unwrap();
    
    // 直方图: 分布统计
    pub static ref HTTP_RESPONSE_TIME: Histogram = register_histogram!(
        "http_response_time_seconds",
        "HTTP response time in seconds",
        vec![0.001, 0.01, 0.1, 0.5, 1.0, 5.0]
    ).unwrap();
}

async fn handle_request(req: Request) -> Response {
    HTTP_REQUESTS_TOTAL.inc();
    ACTIVE_CONNECTIONS.inc();
    let timer = HTTP_RESPONSE_TIME.start_timer();
    
    let response = process(req).await;
    
    timer.observe_duration();
    ACTIVE_CONNECTIONS.dec();
    
    response
}

// Metrics 端点
async fn metrics_handler() -> impl Responder {
    let encoder = TextEncoder::new();
    let metric_families = prometheus::gather();
    let mut buffer = Vec::new();
    encoder.encode(&metric_families, &mut buffer).unwrap();
    
    HttpResponse::Ok()
        .content_type("text/plain; version=0.0.4")
        .body(buffer)
}
```

### RED 方法

**Rate, Errors, Duration**：

```rust
use prometheus::{HistogramVec, IntCounterVec};

lazy_static! {
    // Rate: 请求速率
    static ref HTTP_REQUESTS: IntCounterVec = register_int_counter_vec!(
        "http_requests_total",
        "Total HTTP requests",
        &["method", "endpoint", "status"]
    ).unwrap();
    
    // Errors: 错误率
    static ref HTTP_ERRORS: IntCounterVec = register_int_counter_vec!(
        "http_errors_total",
        "Total HTTP errors",
        &["method", "endpoint", "error_type"]
    ).unwrap();
    
    // Duration: 响应时间
    static ref HTTP_DURATION: HistogramVec = register_histogram_vec!(
        "http_request_duration_seconds",
        "HTTP request duration",
        &["method", "endpoint"],
        vec![0.001, 0.01, 0.1, 0.5, 1.0, 5.0, 10.0]
    ).unwrap();
}

async fn observe_request<F, Fut>(
    method: &str,
    endpoint: &str,
    handler: F,
) -> Result<Response>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = Result<Response>>,
{
    let timer = HTTP_DURATION
        .with_label_values(&[method, endpoint])
        .start_timer();
    
    match handler().await {
        Ok(response) => {
            HTTP_REQUESTS
                .with_label_values(&[method, endpoint, &response.status().as_str()])
                .inc();
            timer.observe_duration();
            Ok(response)
        }
        Err(e) => {
            HTTP_ERRORS
                .with_label_values(&[method, endpoint, e.type_name()])
                .inc();
            timer.observe_duration();
            Err(e)
        }
    }
}
```

### 自定义指标

```rust
// 业务指标
lazy_static! {
    // 支付成功率
    static ref PAYMENT_SUCCESS: IntCounter = register_int_counter!(
        "payments_success_total",
        "Successful payments"
    ).unwrap();
    
    static ref PAYMENT_FAILED: IntCounter = register_int_counter!(
        "payments_failed_total",
        "Failed payments"
    ).unwrap();
    
    // 购物车大小分布
    static ref CART_SIZE: Histogram = register_histogram!(
        "cart_size_items",
        "Number of items in cart",
        vec![1.0, 5.0, 10.0, 20.0, 50.0]
    ).unwrap();
    
    // 活跃用户
    static ref ACTIVE_USERS: IntGauge = register_int_gauge!(
        "active_users",
        "Number of active users"
    ).unwrap();
}
```

### 告警规则

```yaml
# prometheus_rules.yml
groups:
  - name: my_app_alerts
    interval: 10s
    rules:
      # 高错误率
      - alert: HighErrorRate
        expr: |
          sum(rate(http_errors_total[5m])) 
          / sum(rate(http_requests_total[5m])) > 0.05
        for: 2m
        labels:
          severity: critical
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value | humanizePercentage }}"
      
      # 慢响应
      - alert: SlowResponseTime
        expr: |
          histogram_quantile(0.95, 
            rate(http_request_duration_seconds_bucket[5m])
          ) > 1.0
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "95th percentile response time > 1s"
      
      # 服务宕机
      - alert: ServiceDown
        expr: up{job="my-app"} == 0
        for: 1m
        labels:
          severity: critical
        annotations:
          summary: "Service {{ $labels.instance }} is down"
```

---

## 分布式追踪

### OpenTelemetry

```rust
use opentelemetry::{global, sdk::trace as sdktrace, trace::Tracer};
use opentelemetry_otlp::WithExportConfig;

pub fn init_tracing() -> Result<()> {
    // OTLP 导出器
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://jaeger:4317")
        )
        .with_trace_config(
            sdktrace::config()
                .with_resource(opentelemetry::sdk::Resource::new(vec![
                    opentelemetry::KeyValue::new("service.name", "my-service"),
                    opentelemetry::KeyValue::new("service.version", "1.0.0"),
                ]))
        )
        .install_batch(opentelemetry::runtime::Tokio)?;
    
    global::set_tracer_provider(tracer);
    
    Ok(())
}
```

### Jaeger 集成

```rust
use tracing_opentelemetry::OpenTelemetrySpanExt;

#[instrument]
async fn fetch_user_data(user_id: u64) -> Result<User> {
    let span = tracing::Span::current();
    span.set_attribute("user_id", user_id.to_string());
    
    // 数据库查询
    let user = {
        let _db_span = info_span!("database_query", db.table = "users");
        db.query_user(user_id).await?
    };
    
    // 外部 API 调用
    let profile = {
        let _api_span = info_span!("external_api", api.endpoint = "profile");
        api_client.fetch_profile(user_id).await?
    };
    
    Ok(User { user, profile })
}
```

### Span 设计

```rust
use tracing::{info_span, Instrument};

async fn process_order(order_id: Uuid) -> Result<()> {
    // 根 Span
    async {
        info!(order_id = %order_id, "Processing order");
        
        // 子 Span 1: 验证
        validate_order(order_id)
            .instrument(info_span!("validate", step = "validation"))
            .await?;
        
        // 子 Span 2: 支付
        process_payment(order_id)
            .instrument(info_span!("payment", 
                payment.gateway = "stripe",
                payment.method = "card"
            ))
            .await?;
        
        // 子 Span 3: 发货
        schedule_shipment(order_id)
            .instrument(info_span!("shipment",
                shipment.carrier = "fedex"
            ))
            .await?;
        
        Ok(())
    }
    .instrument(info_span!("process_order", order_id = %order_id))
    .await
}
```

### 性能分析

```rust
// 使用 Span 进行性能分析
use tracing::{info_span, instrument};
use std::time::Instant;

#[instrument]
async fn analyze_performance() {
    let start = Instant::now();
    
    // 操作1
    let span1 = info_span!("database_queries");
    let _enter1 = span1.enter();
    let db_result = fetch_from_db().await;
    drop(_enter1);
    tracing::info!(elapsed_ms = start.elapsed().as_millis(), "DB queries completed");
    
    // 操作2
    let span2 = info_span!("cache_operations");
    let _enter2 = span2.enter();
    let cache_result = fetch_from_cache().await;
    drop(_enter2);
    tracing::info!(elapsed_ms = start.elapsed().as_millis(), "Cache ops completed");
    
    tracing::info!(total_ms = start.elapsed().as_millis(), "Analysis complete");
}
```

---

## 错误追踪

### Sentry 集成

```rust
use sentry;

pub fn init_error_tracking() {
    let _guard = sentry::init((
        "https://key@sentry.io/project",
        sentry::ClientOptions {
            release: Some(env!("CARGO_PKG_VERSION").into()),
            environment: Some("production".into()),
            traces_sample_rate: 0.1,
            ..Default::default()
        },
    ));
    
    // 设置全局错误处理
    std::panic::set_hook(Box::new(|panic_info| {
        sentry::integrations::panic::panic_to_sentry(panic_info);
    }));
}

async fn risky_operation() -> Result<()> {
    sentry::with_scope(
        |scope| {
            scope.set_tag("operation", "risky");
            scope.set_user(Some(sentry::User {
                id: Some("12345".into()),
                email: Some("user@example.com".into()),
                ..Default::default()
            }));
        },
        || async {
            // 操作代码
        },
    ).await
}
```

### 自定义错误上下文

```rust
use sentry::{capture_message, Level};

async fn handle_payment(payment_id: Uuid, amount: Decimal) -> Result<()> {
    match charge_card(payment_id, amount).await {
        Ok(_) => Ok(()),
        Err(e) => {
            // 捕获详细上下文
            sentry::configure_scope(|scope| {
                scope.set_context("payment", sentry::protocol::Context::from(json!({
                    "payment_id": payment_id.to_string(),
                    "amount": amount.to_string(),
                    "timestamp": chrono::Utc::now().to_rfc3339(),
                })));
                
                scope.set_extra("card_last4", "1234".into());
                scope.set_fingerprint(vec!["payment-error", &e.to_string()]);
            });
            
            sentry::capture_error(&e);
            Err(e)
        }
    }
}
```

### 错误分组

```rust
// 使用 fingerprint 控制错误分组
pub fn set_error_fingerprint(error: &Error) {
    let fingerprint = match error {
        Error::Database(ref e) => {
            vec!["database-error", e.code()]
        }
        Error::Network(ref e) => {
            vec!["network-error", e.kind().as_str()]
        }
        Error::Business(ref e) => {
            vec!["business-error", e.category()]
        }
        _ => vec!["unknown-error"],
    };
    
    sentry::configure_scope(|scope| {
        scope.set_fingerprint(Some(&fingerprint));
    });
}
```

---

## 性能分析1

### CPU Profiling

```rust
// 使用 pprof 进行在线 profiling
use pprof::ProfilerGuard;

// 在应用启动时
let guard = ProfilerGuard::new(100).unwrap();

// 提供 HTTP 端点
async fn profiling_endpoint() -> Result<Vec<u8>> {
    let report = guard.report().build().unwrap();
    let mut body = Vec::new();
    report.flamegraph(&mut body)?;
    Ok(body)
}
```

### 内存分析

```rust
// 使用 jemalloc + profiling
#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

#[cfg(feature = "profiling")]
use jemalloc_ctl::{stats, epoch};

async fn memory_stats() -> Result<MemoryStats> {
    epoch::mib()?.advance()?;
    
    let allocated = stats::allocated::mib()?.read()?;
    let resident = stats::resident::mib()?.read()?;
    
    Ok(MemoryStats {
        allocated_bytes: allocated,
        resident_bytes: resident,
    })
}
```

### 实时分析

```rust
// 定期收集运行时统计
use tokio::time::{interval, Duration};

pub async fn runtime_monitor() {
    let mut interval = interval(Duration::from_secs(60));
    
    loop {
        interval.tick().await;
        
        // 收集 Tokio 运行时统计
        let metrics = tokio::runtime::Handle::current().metrics();
        
        info!(
            workers = metrics.num_workers(),
            blocking_threads = metrics.num_blocking_threads(),
            "Runtime metrics"
        );
    }
}
```

---

## 健康检查

### 端点设计

```rust
use axum::{Router, Json};
use serde::Serialize;

#[derive(Serialize)]
struct HealthStatus {
    status: String,
    version: String,
    uptime: u64,
    checks: Vec<Check>,
}

#[derive(Serialize)]
struct Check {
    name: String,
    status: String,
    message: Option<String>,
}

async fn health_check() -> Json<HealthStatus> {
    let mut checks = vec![];
    
    // 检查数据库
    checks.push(check_database().await);
    
    // 检查 Redis
    checks.push(check_redis().await);
    
    // 检查外部 API
    checks.push(check_external_api().await);
    
    let all_healthy = checks.iter().all(|c| c.status == "healthy");
    
    Json(HealthStatus {
        status: if all_healthy { "healthy" } else { "degraded" }.to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
        uptime: get_uptime(),
        checks,
    })
}

async fn check_database() -> Check {
    match db_pool.acquire().await {
        Ok(_) => Check {
            name: "database".to_string(),
            status: "healthy".to_string(),
            message: None,
        },
        Err(e) => Check {
            name: "database".to_string(),
            status: "unhealthy".to_string(),
            message: Some(e.to_string()),
        },
    }
}
```

### 依赖检查

```rust
// 启动时检查所有依赖
pub async fn startup_checks() -> Result<()> {
    info!("Running startup checks...");
    
    // 1. 数据库连接
    db_pool.acquire().await
        .context("Database connection failed")?;
    info!("✓ Database connection OK");
    
    // 2. Redis 连接
    redis_client.ping().await
        .context("Redis connection failed")?;
    info!("✓ Redis connection OK");
    
    // 3. S3 访问
    s3_client.head_bucket("my-bucket").await
        .context("S3 access failed")?;
    info!("✓ S3 access OK");
    
    // 4. 必要配置
    ensure!(!CONFIG.secret_key.is_empty(), "SECRET_KEY not set");
    info!("✓ Configuration OK");
    
    info!("All startup checks passed");
    Ok(())
}
```

### 优雅降级

```rust
use std::sync::atomic::{AtomicBool, Ordering};

static CACHE_AVAILABLE: AtomicBool = AtomicBool::new(true);

async fn get_user(id: u64) -> Result<User> {
    // 尝试从缓存获取
    if CACHE_AVAILABLE.load(Ordering::Relaxed) {
        match cache.get(id).await {
            Ok(user) => return Ok(user),
            Err(e) => {
                warn!("Cache unavailable, falling back to DB: {}", e);
                CACHE_AVAILABLE.store(false, Ordering::Relaxed);
                
                // 启动恢复任务
                tokio::spawn(async {
                    tokio::time::sleep(Duration::from_secs(30)).await;
                    if cache.ping().await.is_ok() {
                        CACHE_AVAILABLE.store(true, Ordering::Relaxed);
                        info!("Cache recovered");
                    }
                });
            }
        }
    }
    
    // 降级到数据库
    db.get_user(id).await
}
```

---

## 金丝雀部署

### 流量分配

```rust
// 使用 feature flag 进行流量分配
use launchdarkly_server_sdk::{Client, Context};

pub async fn route_request(req: Request) -> Response {
    let user_id = req.user_id();
    
    // 构建 LaunchDarkly context
    let context = Context::builder(user_id.to_string())
        .set_value("email", req.user_email().into())
        .build()
        .unwrap();
    
    // 检查是否路由到新版本
    let use_new_version = ld_client
        .bool_variation(&context, "new-payment-flow", false)
        .await;
    
    if use_new_version {
        new_payment_handler(req).await
    } else {
        old_payment_handler(req).await
    }
}
```

### 监控指标

```rust
// 为金丝雀部署添加专门指标
lazy_static! {
    static ref CANARY_REQUESTS: IntCounterVec = register_int_counter_vec!(
        "canary_requests_total",
        "Requests to canary version",
        &["version", "status"]
    ).unwrap();
    
    static ref CANARY_ERRORS: IntCounterVec = register_int_counter_vec!(
        "canary_errors_total",
        "Errors in canary version",
        &["version", "error_type"]
    ).unwrap();
}

async fn canary_handler(version: &str, req: Request) -> Result<Response> {
    let result = process(req).await;
    
    CANARY_REQUESTS
        .with_label_values(&[version, if result.is_ok() { "success" } else { "error" }])
        .inc();
    
    if let Err(ref e) = result {
        CANARY_ERRORS
            .with_label_values(&[version, e.type_name()])
            .inc();
    }
    
    result
}
```

### 回滚策略

```rust
// 自动回滚逻辑
pub async fn monitor_canary_deployment() {
    let mut interval = interval(Duration::from_secs(10));
    
    loop {
        interval.tick().await;
        
        let error_rate = calculate_error_rate("canary").await;
        let baseline_error_rate = calculate_error_rate("stable").await;
        
        // 如果金丝雀错误率显著高于基线
        if error_rate > baseline_error_rate * 2.0 && error_rate > 0.05 {
            error!("Canary error rate too high: {}%, rolling back", error_rate * 100.0);
            
            // 触发回滚
            rollback_deployment().await;
            
            // 发送告警
            send_alert("Canary deployment rolled back due to high error rate").await;
            
            break;
        }
    }
}
```

---

## 故障排查流程

### 问题定位

```text
故障排查检查清单
├─ 1. 收集症状
│  ├─ 错误消息
│  ├─ 影响范围
│  ├─ 开始时间
│  └─ 相关事件（部署、配置变更）
├─ 2. 检查监控
│  ├─ Metrics (Grafana)
│  ├─ Logs (Loki/ELK)
│  ├─ Traces (Jaeger)
│  └─ Errors (Sentry)
├─ 3. 定位层级
│  ├─ 负载均衡器
│  ├─ 应用服务器
│  ├─ 数据库
│  ├─ 缓存
│  └─ 外部依赖
├─ 4. 形成假设
│  └─ 基于数据，而非猜测
└─ 5. 验证假设
   └─ 逐步排除
```

### 根因分析

```rust
// 5 Whys 分析法

// 问题: 用户无法登录
// 
// Why 1: 为什么用户无法登录？
// → 因为认证服务返回 500 错误
//
// Why 2: 为什么认证服务返回 500？
// → 因为数据库查询超时
//
// Why 3: 为什么数据库查询超时？
// → 因为连接池耗尽
//
// Why 4: 为什么连接池耗尽？
// → 因为某些查询没有正确释放连接
//
// Why 5: 为什么查询没有释放连接？
// → 因为错误处理路径中忘记调用 drop()
//
// 根因: 错误处理不当导致连接泄漏

// 修复
async fn query_with_proper_cleanup() -> Result<User> {
    let conn = pool.acquire().await?;
    
    let result = sqlx::query_as("SELECT * FROM users WHERE id = ?")
        .bind(user_id)
        .fetch_one(&mut *conn)  // &mut *conn 确保 Drop 被调用
        .await;
    
    // 即使出错，conn 也会被 drop
    result
}
```

### 修复验证

```rust
// 修复后验证流程
pub async fn verify_fix() -> Result<()> {
    info!("Verifying fix...");
    
    // 1. 功能测试
    let test_result = run_smoke_tests().await?;
    ensure!(test_result.all_passed(), "Smoke tests failed");
    
    // 2. 监控检查
    tokio::time::sleep(Duration::from_secs(60)).await;
    let error_rate = calculate_error_rate("production").await;
    ensure!(error_rate < 0.01, "Error rate still high");
    
    // 3. 性能检查
    let p95_latency = get_p95_latency().await;
    ensure!(p95_latency < Duration::from_millis(500), "Latency still high");
    
    info!("Fix verified successfully");
    Ok(())
}
```

---

## 常见生产问题

### 内存泄漏

**症状**:

- 内存使用持续增长
- OOM Killer 终止进程
- 性能逐渐下降

**排查**:

```bash
# 1. 查看内存趋势
kubectl top pods

# 2. 获取堆快照
curl http://pod-ip:9090/debug/pprof/heap > heap.prof

# 3. 分析
go tool pprof heap.prof
```

**常见原因**:

```rust
// ❌ 忘记清理订阅
lazy_static! {
    static ref SUBSCRIBERS: Mutex<Vec<Sender>> = Mutex::new(vec![]);
}

// ✅ 使用弱引用
use std::sync::Weak;

lazy_static! {
    static ref SUBSCRIBERS: Mutex<Vec<Weak<Sender>>> = Mutex::new(vec![]);
}

// 定期清理
fn cleanup_subscribers() {
    SUBSCRIBERS.lock().unwrap().retain(|s| s.upgrade().is_some());
}
```

### CPU 高负载

**症状**:

- CPU 使用率 > 80%
- 响应时间增加
- 请求排队

**排查**:

```bash
# 1. 火焰图
cargo flamegraph --pid $(pgrep my-app)

# 2. Top 命令
top -H -p $(pgrep my-app)

# 3. Perf
perf top -p $(pgrep my-app)
```

**常见原因**:

```rust
// ❌ 忙等待
loop {
    if condition {
        break;
    }
}

// ✅ 使用异步等待
while !condition {
    tokio::time::sleep(Duration::from_millis(100)).await;
}

// ❌ 不必要的克隆
for item in large_vec.clone() {
    process(item);
}

// ✅ 使用引用
for item in &large_vec {
    process(item);
}
```

### 连接池耗尽

**症状**:

- 获取连接超时
- 大量 "connection pool timeout" 错误

**排查**:

```rust
// 监控连接池状态
async fn monitor_pool() {
    loop {
        tokio::time::sleep(Duration::from_secs(10)).await;
        
        let stats = pool.status();
        warn!(
            "Pool: size={}, idle={}, waiting={}",
            stats.size, stats.idle, stats.waiting
        );
        
        if stats.waiting > 10 {
            error!("Connection pool exhausted!");
        }
    }
}
```

**解决方案**:

```rust
// 1. 增加池大小
let pool = PgPoolOptions::new()
    .max_connections(50)  // 增加
    .acquire_timeout(Duration::from_secs(5))
    .connect(&database_url)
    .await?;

// 2. 使用超时
let conn = tokio::time::timeout(
    Duration::from_secs(5),
    pool.acquire()
).await??;

// 3. 确保连接释放
async fn query() -> Result<()> {
    let mut conn = pool.acquire().await?;
    let result = sqlx::query("SELECT 1")
        .fetch_one(&mut *conn)
        .await?;
    // conn 自动 drop
    Ok(())
}
```

### 死锁与活锁

**症状**:

- 请求hang住
- 无错误日志
- CPU 可能很低

**排查**:

```rust
// 使用 parking_lot 的死锁检测
use parking_lot::deadlock;

fn start_deadlock_detector() {
    std::thread::spawn(move || {
        loop {
            std::thread::sleep(Duration::from_secs(1));
            let deadlocks = deadlock::check_deadlock();
            if !deadlocks.is_empty() {
                error!("{} deadlocks detected", deadlocks.len());
                for (i, threads) in deadlocks.iter().enumerate() {
                    error!("Deadlock #{}", i);
                    for t in threads {
                        error!("Thread {:?}\n{:?}", t.thread_id(), t.backtrace());
                    }
                }
            }
        }
    });
}
```

**解决方案**:

```rust
// ❌ 锁顺序不一致
let lock1 = mutex1.lock();
let lock2 = mutex2.lock();  // 可能死锁

// ✅ 始终按相同顺序获取锁
fn acquire_locks<T, U>(
    mutex1: &Mutex<T>,
    mutex2: &Mutex<U>
) -> (MutexGuard<T>, MutexGuard<U>) {
    let (first, second) = if mutex1.data_ptr() < mutex2.data_ptr() {
        (mutex1, mutex2)
    } else {
        (mutex2, mutex1)
    };
    // ...
}
```

---

## 应急响应

### 事故分级

| 级别 | 描述 | 响应时间 | 示例 |
|------|------|---------|------|
| **P0** | 核心服务完全不可用 | 立即 (5分钟) | 网站宕机、支付失败 |
| **P1** | 核心功能严重受损 | 紧急 (30分钟) | 性能严重下降、部分用户无法访问 |
| **P2** | 非核心功能故障 | 高优先级 (2小时) | 邮件发送失败、报表错误 |
| **P3** | 小问题或请求 | 正常 (1天) | UI bug、日志错误 |

### 响应流程

```text
事故响应 Runbook
├─ 1. 确认 (5分钟内)
│  ├─ 确认问题存在
│  ├─ 评估影响范围
│  └─ 确定事故级别
├─ 2. 通知 (立即)
│  ├─ 通知相关团队
│  ├─ 建立沟通渠道 (Slack/Teams)
│  └─ 分配事故指挥官
├─ 3. 缓解 (目标: 15-30分钟)
│  ├─ 回滚部署 (首选)
│  ├─ 切换流量
│  ├─ 扩容资源
│  └─ 启用降级方案
├─ 4. 监控
│  ├─ 验证缓解措施
│  ├─ 持续监控指标
│  └─ 更新状态页
├─ 5. 修复
│  ├─ 根因分析
│  ├─ 实施永久修复
│  └─ 代码审查
└─ 6. 复盘
   ├─ 事故报告
   ├─ 改进措施
   └─ 流程更新
```

### 事后复盘

```markdown
# 事故报告模板

## 基本信息
- **事故ID**: INC-2025-001
- **发生时间**: 2025-10-20 14:30 UTC
- **恢复时间**: 2025-10-20 15:15 UTC
- **持续时间**: 45分钟
- **事故级别**: P1

## 影响
- **受影响用户**: 约 10,000 用户 (20%)
- **业务影响**: 支付失败率 100%
- **财务影响**: 估计损失 $5,000

## 时间线
- 14:30 - 部署新版本 v1.2.0
- 14:35 - 支付错误告警触发
- 14:40 - 事故确认，开始调查
- 14:50 - 识别为数据库连接池配置错误
- 15:00 - 回滚到 v1.1.9
- 15:15 - 服务完全恢复

## 根本原因
v1.2.0 中数据库连接池最大连接数从 50 降低到 10，
导致高峰期连接池耗尽。

## 缓解措施
1. 立即回滚到 v1.1.9
2. 重启所有实例清理连接

## 永久修复
1. ✅ 恢复连接池配置到 50
2. ✅ 添加连接池指标监控
3. ✅ 在 staging 环境进行负载测试
4. ✅ 更新部署检查清单

## 改进行动项
1. [ ] 实施自动化配置验证 (Owner: @team-sre, Due: 2025-10-27)
2. [ ] 添加连接池告警 (Owner: @team-platform, Due: 2025-10-25)
3. [ ] 更新变更审查流程 (Owner: @team-lead, Due: 2025-10-22)

## 经验教训
**What went well**:
- 快速检测到问题
- 回滚流程顺利

**What went wrong**:
- 配置变更未充分测试
- 缺少连接池监控

**What got lucky**:
- 发生在非高峰时段
```

---

## 安全调试

### 敏感信息脱敏

```rust
use tracing::field::Visit;

// 自动脱敏敏感字段
#[derive(Debug)]
struct SensitiveData {
    user_id: u64,
    email: String,
    
    #[sensitive]  // 自定义属性
    password: String,
    
    #[sensitive]
    credit_card: String,
}

impl std::fmt::Display for SensitiveData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SensitiveData {{ user_id: {}, email: {}, password: [REDACTED], credit_card: [REDACTED] }}",
            self.user_id, self.email)
    }
}

// 日志脱敏过滤器
pub fn redact_sensitive_info(message: &str) -> String {
    let patterns = vec![
        (r"password[:=]\s*\S+", "password: [REDACTED]"),
        (r"\b\d{16}\b", "[CARD_REDACTED]"),  // 信用卡号
        (r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b", "[EMAIL_REDACTED]"),
    ];
    
    let mut result = message.to_string();
    for (pattern, replacement) in patterns {
        result = regex::Regex::new(pattern).unwrap()
            .replace_all(&result, replacement)
            .to_string();
    }
    result
}
```

### 访问控制

```rust
// 审计日志访问
#[derive(Debug)]
struct AuditLog {
    user: String,
    action: String,
    resource: String,
    timestamp: DateTime<Utc>,
    result: Result<(), String>,
}

async fn access_sensitive_data(
    user: &User,
    resource_id: Uuid,
) -> Result<Data> {
    // 检查权限
    ensure!(user.has_permission("read:sensitive"), "Access denied");
    
    // 记录审计日志
    audit_log.record(AuditLog {
        user: user.email.clone(),
        action: "read_sensitive_data".to_string(),
        resource: resource_id.to_string(),
        timestamp: Utc::now(),
        result: Ok(()),
    }).await;
    
    // 执行操作
    fetch_sensitive_data(resource_id).await
}
```

### 审计日志

```rust
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
struct SecurityEvent {
    event_type: String,
    user_id: Option<u64>,
    ip_address: String,
    user_agent: String,
    action: String,
    resource: String,
    success: bool,
    timestamp: DateTime<Utc>,
}

impl SecurityEvent {
    pub async fn log(&self) {
        // 写入专门的安全日志
        let json = serde_json::to_string(self).unwrap();
        
        // 1. 本地日志
        info!(target: "security_audit", "{}", json);
        
        // 2. SIEM 系统
        siem_client.send_event(self).await.ok();
        
        // 3. 合规存储 (不可变)
        compliance_storage.append(self).await.ok();
    }
}
```

---

## 工具集成

### Kubernetes

```bash
# 查看 Pod 日志
kubectl logs -f pod-name -c container-name

# 查看前一个实例的日志 (如果 crashed)
kubectl logs pod-name --previous

# 进入容器
kubectl exec -it pod-name -- bash

# Port forward
kubectl port-forward pod-name 8080:8080

# 查看事件
kubectl get events --sort-by='.lastTimestamp'

# 调试 Pod
kubectl debug pod-name -it --image=busybox --target=container-name
```

### Docker

```bash
# 查看容器日志
docker logs -f container-id

# 进入容器
docker exec -it container-id bash

# 查看容器统计
docker stats container-id

# 查看容器详情
docker inspect container-id
```

### Cloud Provider

**AWS CloudWatch**:

```bash
# 查询日志
aws logs filter-log-events \
  --log-group-name /aws/lambda/my-function \
  --start-time $(date -d '1 hour ago' +%s)000 \
  --filter-pattern "ERROR"
```

**GCP Logging**:

```bash
# 查询日志
gcloud logging read "resource.type=k8s_container" \
  --limit 100 \
  --format json
```

---

## 最佳实践

### 设计阶段

- ✅ 可观测性优先：从设计之初就考虑如何调试
- ✅ 幂等性：所有操作应该是幂等的
- ✅ 超时处理：所有外部调用必须有超时
- ✅ 重试策略：实现指数退避重试

### 开发阶段

- ✅ 结构化日志：使用 `tracing`，不是 `println!`
- ✅ 有意义的错误信息：包含上下文
- ✅ 请求ID：跨服务追踪
- ✅ 指标埋点：关键路径都要有指标

### 部署阶段

- ✅ 金丝雀部署：逐步推出新版本
- ✅ 蓝绿部署：快速回滚能力
- ✅ Feature Flag：运行时控制功能
- ✅ 健康检查：让负载均衡器知道服务状态

### 运维阶段

- ✅ 监控告警：主动发现问题
- ✅ Runbook：常见问题处理手册
- ✅ 定期演练：Chaos Engineering
- ✅ 事后复盘：持续改进

---

## 总结

生产环境调试的核心原则：

### 1. 可观测性三大支柱

- **日志**: 记录发生了什么
- **指标**: 告诉你系统健康状况
- **追踪**: 显示请求完整路径

### 2. 关键实践

- 结构化日志 (tracing)
- RED 指标 (Prometheus)
- 分布式追踪 (OpenTelemetry)
- 错误追踪 (Sentry)

### 3. 应急响应

- 快速恢复 > 深入分析
- 回滚优先
- 沟通透明
- 事后复盘

### 4. 持续改进

- 监控你关心的
- 告警可操作的
- 文档化经验
- 自动化流程

---

## 相关资源

- [rust-debugging.md](./rust-debugging.md) - Rust 调试完整指南
- [debugging-tools.md](./debugging-tools.md) - 调试工具生态
- [Google SRE Book](https://sre.google/books/)
- [Observability Engineering](https://www.oreilly.com/library/view/observability-engineering/9781492076438/)
- [OpenTelemetry Docs](https://opentelemetry.io/docs/)

---

**文档版本**: 1.0  
**最后更新**: 2025-10-20  
**维护者**: C13 Reliability Team
