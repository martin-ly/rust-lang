//! OpenTelemetry 全链路追踪实战示例
//!
//! 本示例展示如何在 Rust 应用中集成 OpenTelemetry，实现：
//! - 分布式追踪（Distributed Tracing）
//! - 自动上下文传播
//! - 导出到 Jaeger / OTLP / 标准输出
//! - 与 tokio/tracing 生态的无缝集成
//!
//! **前置条件**:
//! ```bash
//! # 启动本地 Jaeger（All-in-one）
//! docker run -d --name jaeger \
//!   -p 16686:16686 \
//!   -p 4317:4317 \
//!   -p 4318:4318 \
//!   jaegertracing/all-in-one:latest
//! ```
//!
//! Jaeger UI: http://localhost:16686
//!
//! 权威来源:
//! - [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust)
//! - [AWS Distro for OpenTelemetry](https://aws-otel.github.io/)
//! - [Cloudflare Tracing 实践](https://blog.cloudflare.com/)
//!
//! 运行方式:
//! ```bash
//! cargo run --example opentelemetry_full_demo -p c10_networks
//! ```

use std::time::Duration;
use tokio::time::sleep;
use tracing::{info, instrument, warn};

// ==================== 示例 1: OpenTelemetry 初始化 ====================

use opentelemetry::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::trace::SdkTracerProvider;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

/// 初始化 OpenTelemetry + tracing 集成
async fn init_telemetry() -> SdkTracerProvider {
    let resource = opentelemetry_sdk::Resource::builder()
        .with_service_name("rust-opentelemetry-demo")
        .with_attribute(opentelemetry::KeyValue::new(
            "service.version",
            env!("CARGO_PKG_VERSION"),
        ))
        .build();

    // 使用 OTLP HTTP 导出器（与项目依赖的 http-json feature 对齐）
    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_http()
        .with_endpoint("http://localhost:4318/v1/traces")
        .with_timeout(Duration::from_secs(3))
        .build()
        .expect("failed to create OTLP exporter");

    let provider = SdkTracerProvider::builder()
        .with_resource(resource)
        .with_batch_exporter(exporter)
        .with_sampler(opentelemetry_sdk::trace::Sampler::AlwaysOn)
        .build();

    // 创建 OpenTelemetry 的 tracing layer
    let otel_layer = tracing_opentelemetry::layer().with_tracer(provider.tracer("demo"));

    // 标准输出 layer（用于开发调试）
    let stdout_layer = tracing_subscriber::fmt::layer().pretty();

    // 初始化 subscriber
    tracing_subscriber::registry()
        .with(stdout_layer)
        .with(otel_layer)
        .init();

    provider
}

// ==================== 示例 2: 简单追踪函数 ====================

#[instrument]
async fn process_order(order_id: u64, user_id: u64) -> Result<String, &'static str> {
    info!(order_id, user_id, "开始处理订单");

    // 模拟数据库查询
    let items = fetch_order_items(order_id).await?;

    // 模拟库存检查
    check_inventory(&items).await?;

    // 模拟支付处理
    let payment_result = process_payment(order_id, &items).await?;

    info!(order_id, "订单处理完成");
    Ok(payment_result)
}

#[instrument]
async fn fetch_order_items(order_id: u64) -> Result<Vec<String>, &'static str> {
    info!(order_id, "查询订单商品");
    sleep(Duration::from_millis(50)).await;
    Ok(vec![
        format!("item_{}_1", order_id),
        format!("item_{}_2", order_id),
    ])
}

#[instrument]
async fn check_inventory(items: &[String]) -> Result<(), &'static str> {
    info!(?items, "检查库存");
    sleep(Duration::from_millis(30)).await;
    if items.len() > 10 {
        warn!("库存紧张");
    }
    Ok(())
}

#[instrument(fields(payment_method = "credit_card"))]
async fn process_payment(order_id: u64, items: &[String]) -> Result<String, &'static str> {
    info!(order_id, item_count = items.len(), "处理支付");
    sleep(Duration::from_millis(80)).await;
    Ok(format!("payment_{}", order_id))
}

// ==================== 示例 3: 跨服务上下文传播 ====================

use opentelemetry::propagation::TextMapPropagator;
use opentelemetry_sdk::propagation::TraceContextPropagator;
use std::collections::HashMap;

/// 模拟 HTTP 客户端：注入追踪上下文到请求头
fn inject_trace_context() -> HashMap<String, String> {
    let propagator = TraceContextPropagator::new();
    let mut headers = HashMap::new();
    let context = opentelemetry::context::Context::current();

    propagator.inject_context(&context, &mut headers);
    headers
}

/// 模拟 HTTP 服务端：从请求头提取追踪上下文
#[instrument]
async fn handle_incoming_request(headers: HashMap<String, String>) {
    let propagator = TraceContextPropagator::new();
    let parent_context = propagator.extract(&headers);

    // 在当前上下文中创建子 span
    let _guard = parent_context.attach();

    info!("处理跨服务请求，继承父追踪上下文");
    sleep(Duration::from_millis(20)).await;
}

// ==================== 示例 4: 自定义 Span 属性与事件 ====================

#[instrument(skip(sensitive_data))]
async fn authenticate_user(username: &str, sensitive_data: &str) -> Result<bool, &'static str> {
    let span = tracing::Span::current();

    // 添加自定义属性
    span.record("auth_method", "password");

    info!(username, "开始认证");

    // 模拟验证
    sleep(Duration::from_millis(40)).await;

    // 添加事件（在 span 内记录时间点）
    tracing::info!(target: "auth_events", "密码哈希计算完成");

    let success = sensitive_data.len() > 3;
    if success {
        info!(username, "认证成功");
    } else {
        warn!(username, "认证失败");
    }

    Ok(success)
}

// ==================== 示例 5: 批量操作追踪 ====================

#[instrument]
async fn batch_process_orders(order_ids: Vec<u64>) -> Vec<Result<String, &'static str>> {
    info!(count = order_ids.len(), "开始批量处理订单");

    let mut results = Vec::new();

    for (idx, order_id) in order_ids.into_iter().enumerate() {
        let span = tracing::info_span!("batch_item", index = idx, total = 3);
        let _enter = span.enter();

        let result = process_order(order_id, 1000 + order_id).await;
        results.push(result);
    }

    info!("批量处理完成");
    results
}

// ==================== 示例 6: 错误追踪与异常记录 ====================

#[instrument]
async fn risky_operation(should_fail: bool) -> Result<(), &'static str> {
    info!("执行风险操作");
    sleep(Duration::from_millis(30)).await;

    if should_fail {
        let span = tracing::Span::current();
        span.record("error", true);
        span.record("error.message", "模拟的业务错误");

        warn!("操作失败");
        return Err("business_logic_error");
    }

    Ok(())
}

// ==================== 示例 7: 指标（Metrics）集成概览 ====================

/// 虽然 OpenTelemetry 追踪（Tracing）是核心，但完整的可观测性还包括指标：
/// - `opentelemetry::metrics` 用于记录 Counter、Histogram、Gauge
/// - 与 Prometheus 或 OTLP 指标后端集成
///
/// ```rust,ignore
/// use opentelemetry::metrics::MeterProvider;
/// use opentelemetry::global;
///
/// let meter = global::meter("my_app");
/// let request_counter = meter.u64_counter("http_requests_total").build();
/// request_counter.add(1, &[opentelemetry::KeyValue::new("route", "/api/orders")]);
/// ```
fn metrics_overview() {
    println!("\n--- OpenTelemetry Metrics 概览 ---");
    println!("  追踪 (Tracing) 记录请求路径，指标 (Metrics) 记录聚合统计:");
    println!("  - Counter:    请求总数、错误总数");
    println!("  - Histogram:  请求延迟分布");
    println!("  - Gauge:      当前连接数、队列长度");
    println!("  - UpDownCounter: 活跃会话数");
}

// ==================== 主演示函数 ====================

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("📡 OpenTelemetry 全链路追踪实战演示\n");
    println!(
        "   确保 Jaeger 已启动: docker run -d -p 16686:16686 -p 4317:4317 -p 4318:4318 \
         jaegertracing/all-in-one:latest\n"
    );

    // 初始化遥测
    let provider = init_telemetry().await;

    println!("--- 示例 1: 简单订单处理追踪 ---");
    let result = process_order(42, 1001).await;
    println!("  结果: {:?}\n", result);

    println!("--- 示例 2: 跨服务上下文传播 ---");
    let headers = inject_trace_context();
    println!("  注入的请求头: {:?}", headers);
    handle_incoming_request(headers).await;
    println!();

    println!("--- 示例 3: 自定义属性与事件 ---");
    let auth_result = authenticate_user("alice", "secret123").await;
    println!("  认证结果: {:?}\n", auth_result);

    println!("--- 示例 4: 批量操作追踪 ---");
    let batch_results = batch_process_orders(vec![101, 102, 103]).await;
    println!("  批量结果: {:?}\n", batch_results);

    println!("--- 示例 5: 错误追踪 ---");
    let _ = risky_operation(true).await;
    let _ = risky_operation(false).await;
    println!();

    metrics_overview();

    // 刷新并关闭导出器
    sleep(Duration::from_secs(2)).await;
    provider.shutdown()?;

    println!("\n✅ OpenTelemetry 演示完成！");
    println!("   访问 http://localhost:16686 查看 Jaeger UI 中的追踪数据");
    println!("   搜索 Service: rust-opentelemetry-demo");

    Ok(())
}
