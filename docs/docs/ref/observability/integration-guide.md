# 可观测性集成指南 / Observability Integration Guide


## 📊 目录

- [概述 / Overview](#概述-overview)
- [快速开始 / Quick Start](#快速开始-quick-start)
  - [1. 启动本地可观测性栈 / Start Local Observability Stack](#1-启动本地可观测性栈-start-local-observability-stack)
  - [2. 验证服务状态 / Verify Service Status](#2-验证服务状态-verify-service-status)
  - [3. 访问 Web UI / Access Web UI](#3-访问-web-ui-access-web-ui)
- [集成步骤 / Integration Steps](#集成步骤-integration-steps)
  - [步骤 1: 添加依赖 / Step 1: Add Dependencies](#步骤-1-添加依赖-step-1-add-dependencies)
  - [步骤 2: 初始化可观测性 / Step 2: Initialize Observability](#步骤-2-初始化可观测性-step-2-initialize-observability)
  - [步骤 3: 在应用中使用 / Step 3: Use in Application](#步骤-3-在应用中使用-step-3-use-in-application)
  - [步骤 4: 添加指标 / Step 4: Add Metrics](#步骤-4-添加指标-step-4-add-metrics)
- [环境变量配置 / Environment Variables](#环境变量配置-environment-variables)
  - [开发环境 / Development Environment](#开发环境-development-environment)
  - [生产环境 / Production Environment](#生产环境-production-environment)
- [最佳实践 / Best Practices](#最佳实践-best-practices)
  - [1. 追踪最佳实践 / Tracing Best Practices](#1-追踪最佳实践-tracing-best-practices)
  - [2. 指标最佳实践 / Metrics Best Practices](#2-指标最佳实践-metrics-best-practices)
  - [3. 日志最佳实践 / Logging Best Practices](#3-日志最佳实践-logging-best-practices)
- [故障排除 / Troubleshooting](#故障排除-troubleshooting)
  - [常见问题 / Common Issues](#常见问题-common-issues)
  - [调试命令 / Debug Commands](#调试命令-debug-commands)
- [扩展阅读 / Further Reading](#扩展阅读-further-reading)


## 概述 / Overview

本指南详细说明如何在 Rust 项目中集成 OpenTelemetry 可观测性栈，包括追踪、指标、日志的配置和使用。

This guide details how to integrate OpenTelemetry observability stack in Rust projects, including configuration and usage of tracing, metrics, and logging.

## 快速开始 / Quick Start

### 1. 启动本地可观测性栈 / Start Local Observability Stack

```bash
# 使用 Docker Compose 启动完整栈
cd deploy/observability
docker-compose up -d

# 或使用 PowerShell 脚本
./scripts/observability/start-stack.ps1
```

### 2. 验证服务状态 / Verify Service Status

```bash
# 检查所有服务是否正常运行
./scripts/observability/e2e-verify.ps1
```

### 3. 访问 Web UI / Access Web UI

- **Jaeger (追踪)**: <http://localhost:16686>
- **Grafana (可视化)**: <http://localhost:3000> (admin/admin)
- **Prometheus (指标)**: <http://localhost:9090>
- **Tempo (追踪存储)**: <http://localhost:3200>

## 集成步骤 / Integration Steps

### 步骤 1: 添加依赖 / Step 1: Add Dependencies

在 `Cargo.toml` 中添加必要的依赖：

```toml
[dependencies]
# 基础 OpenTelemetry
opentelemetry = "0.21"
opentelemetry_sdk = "0.21"
opentelemetry-otlp = "0.14"

# 追踪
tracing = "0.1"
tracing-opentelemetry = "0.21"
tracing-subscriber = "0.3"

# 指标
opentelemetry-prometheus = "0.12"
prometheus = "0.13"

# HTTP 客户端
reqwest = { version = "0.11", features = ["json"] }
```

### 步骤 2: 初始化可观测性 / Step 2: Initialize Observability

```rust
use opentelemetry::global;
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use opentelemetry_otlp::WithExportConfig;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_observability() -> Result<(), Box<dyn std::error::Error>> {
    // 配置追踪
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317"),
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::AlwaysOn)
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(Resource::new(vec![
                    opentelemetry::KeyValue::new("service.name", "rust-app"),
                    opentelemetry::KeyValue::new("service.version", "1.0.0"),
                ])),
        )
        .install_simple()?;

    // 配置日志
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info".into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    Ok(())
}
```

### 步骤 3: 在应用中使用 / Step 3: Use in Application

```rust
use tracing::{info, error, instrument, span, Level};

#[instrument]
async fn process_request(user_id: u64, data: &str) -> Result<String, String> {
    let span = span!(Level::INFO, "process_request", user_id = user_id);
    let _enter = span.enter();
    
    info!("开始处理请求 / Starting request processing");
    
    // 业务逻辑
    let result = perform_business_logic(data).await?;
    
    info!("请求处理完成 / Request processing completed");
    Ok(result)
}

#[instrument]
async fn perform_business_logic(data: &str) -> Result<String, String> {
    // 模拟业务逻辑
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    Ok(format!("processed: {}", data))
}
```

### 步骤 4: 添加指标 / Step 4: Add Metrics

```rust
use opentelemetry::{
    metrics::{Counter, Histogram, Meter},
    KeyValue,
};
use std::sync::Arc;

pub struct Metrics {
    request_counter: Counter<u64>,
    request_duration: Histogram<f64>,
}

impl Metrics {
    pub fn new(meter: Meter) -> Self {
        Self {
            request_counter: meter
                .u64_counter("requests_total")
                .with_description("Total number of requests")
                .init(),
            request_duration: meter
                .f64_histogram("request_duration_seconds")
                .with_description("Request duration in seconds")
                .init(),
        }
    }

    pub fn record_request(&self, method: &str, status: u16) {
        self.request_counter.add(
            1,
            &[
                KeyValue::new("method", method.to_string()),
                KeyValue::new("status", status.to_string()),
            ],
        );
    }

    pub fn record_duration(&self, duration: f64) {
        self.request_duration.record(duration, &[]);
    }
}
```

## 环境变量配置 / Environment Variables

### 开发环境 / Development Environment

```bash
# 追踪配置
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317
OTEL_SERVICE_NAME=rust-app
OTEL_SERVICE_VERSION=1.0.0
OTEL_RESOURCE_ATTRIBUTES=deployment.environment=development

# 日志级别
RUST_LOG=info
```

### 生产环境 / Production Environment

```bash
# 追踪配置
OTEL_EXPORTER_OTLP_ENDPOINT=https://your-otel-collector.com:4317
OTEL_SERVICE_NAME=rust-app
OTEL_SERVICE_VERSION=1.0.0
OTEL_RESOURCE_ATTRIBUTES=deployment.environment=production

# 采样配置
OTEL_TRACES_SAMPLER=traceidratio
OTEL_TRACES_SAMPLER_ARG=0.1

# 日志级别
RUST_LOG=warn
```

## 最佳实践 / Best Practices

### 1. 追踪最佳实践 / Tracing Best Practices

- 使用有意义的 span 名称
- 添加相关的属性（attributes）
- 避免过度追踪，关注关键路径
- 使用适当的采样率

### 2. 指标最佳实践 / Metrics Best Practices

- 使用标准化的指标名称
- 添加适当的标签（labels）
- 避免高基数标签
- 定期清理不需要的指标

### 3. 日志最佳实践 / Logging Best Practices

- 使用结构化日志
- 避免记录敏感信息
- 使用适当的日志级别
- 包含足够的上下文信息

## 故障排除 / Troubleshooting

### 常见问题 / Common Issues

1. **连接失败 / Connection Failed**
   - 检查 OTel Collector 是否运行
   - 验证端点配置
   - 检查网络连接

2. **数据不显示 / Data Not Showing**
   - 检查采样配置
   - 验证服务名称
   - 查看 Collector 日志

3. **性能影响 / Performance Impact**
   - 调整采样率
   - 优化 span 数量
   - 使用异步导出

### 调试命令 / Debug Commands

```bash
# 检查服务状态
docker-compose ps

# 查看 Collector 日志
docker-compose logs otel-collector

# 检查端口占用
netstat -an | grep :4317
```

## 扩展阅读 / Further Reading

- [OpenTelemetry Rust Documentation](https://opentelemetry.io/docs/instrumentation/rust/)
- [Tracing Documentation](https://docs.rs/tracing/)
- [Prometheus Metrics](https://prometheus.io/docs/concepts/metric_types/)
- [Jaeger Tracing](https://www.jaegertracing.io/docs/)
