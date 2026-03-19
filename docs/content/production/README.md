# Rust 生产实践指南

> **定位**: 从开发到部署的完整生产环境实践指南
> **场景**: 云原生、微服务、Serverless、嵌入式
> **目标**: 可靠性、可观测性、安全性、性能优化
> **状态**: 🔄 持续完善

---

## 📋 目录

- [Rust 生产实践指南](#rust-生产实践指南)
  - [📋 目录](#-目录)
  - [🎯 目标](#-目标)
  - [📊 生产就绪检查清单](#-生产就绪检查清单)
    - [功能完整性](#功能完整性)
    - [可观测性](#可观测性)
    - [安全性](#安全性)
    - [性能](#性能)
  - [🐳 部署](#-部署)
    - [Docker 优化](#docker-优化)
      - [多阶段构建](#多阶段构建)
      - [镜像优化技巧](#镜像优化技巧)
    - [Kubernetes](#kubernetes)
      - [基础部署](#基础部署)
      - [HPA 配置](#hpa-配置)
    - [Serverless](#serverless)
      - [AWS Lambda](#aws-lambda)
      - [Cargo Lambda](#cargo-lambda)
  - [📈 监控与可观测性](#-监控与可观测性)
    - [指标收集](#指标收集)
      - [Prometheus 集成](#prometheus-集成)
    - [分布式追踪](#分布式追踪)
      - [OpenTelemetry + Jaeger](#opentelemetry--jaeger)
  - [🔒 安全](#-安全)
    - [依赖审计](#依赖审计)
    - [密钥管理](#密钥管理)
      - [AWS Secrets Manager](#aws-secrets-manager)
  - [⚡ 性能优化](#-性能优化)
    - [性能分析](#性能分析)
      - [Criterion 基准测试](#criterion-基准测试)
      - [flamegraph](#flamegraph)
    - [内存优化](#内存优化)
      - [内存分析工具](#内存分析工具)
      - [优化技巧](#优化技巧)
  - [🛡️ 可靠性](#️-可靠性)
    - [熔断器模式](#熔断器模式)
    - [优雅降级](#优雅降级)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 目标

本目录致力于提供：

1. **生产就绪检查清单**: 系统化的部署前验证
2. **实战经验**: 来自真实生产环境的最佳实践
3. **性能数据**: 基于实际测试的优化建议
4. **故障案例**: 常见问题和解决方案

---

## 📊 生产就绪检查清单

### 功能完整性

- [ ] 所有功能有单元测试覆盖 (>80%)
- [ ] 集成测试覆盖关键路径
- [ ] 端到端测试验证完整流程
- [ ] 错误处理完善，有明确的错误码
- [ ] 配置外部化，支持环境变量
- [ ] 健康检查端点实现
- [ ] 优雅关闭机制

### 可观测性

- [ ] 结构化日志输出
- [ ] 关键指标暴露 (Prometheus)
- [ ] 分布式追踪集成
- [ ] 性能基准测试
- [ ] 告警规则配置

### 安全性

- [ ] 依赖安全审计通过
- [ ] 密钥管理服务集成
- [ ] 输入验证和 Sanitization
- [ ] 敏感数据加密存储
- [ ] TLS 配置正确

### 性能

- [ ] 内存使用分析
- [ ] CPU 热点优化
- [ ] 并发模型评估
- [ ] 缓存策略实施
- [ ] 数据库连接池优化

---

## 🐳 部署

### Docker 优化

#### 多阶段构建

```dockerfile
# 构建阶段
FROM rust:1.94-slim as builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

# 缓存依赖
RUN cargo build --release && \
    rm -rf src/

# 生产镜像
FROM gcr.io/distroless/cc-debian12

COPY --from=builder /app/target/release/myapp /app/

EXPOSE 8080

USER nonroot:nonroot

ENTRYPOINT ["/app/myapp"]
```

#### 镜像优化技巧

| 技巧 | 效果 | 实施难度 |
|------|------|----------|
| 多阶段构建 | -90% 体积 | 低 |
| distroless 基础镜像 | -50% 攻击面 | 低 |
| 静态链接 musl | 无依赖 | 中 |
| 层缓存优化 | 加速构建 | 低 |
| cargo-chef | 依赖缓存 | 中 |

```dockerfile
# 使用 cargo-chef 优化缓存
FROM lukemathwalker/cargo-chef:latest-rust-1.94 as chef
WORKDIR /app

FROM chef as planner
COPY . .
RUN cargo chef prepare --recipe-path recipe.json

FROM chef as builder
COPY --from=planner /app/recipe.json recipe.json
# 构建依赖（缓存层）
RUN cargo chef cook --release --recipe-path recipe.json
# 构建应用
COPY . .
RUN cargo build --release --bin app

FROM debian:bookworm-slim as runtime
COPY --from=builder /app/target/release/app /usr/local/bin/
ENTRYPOINT ["/usr/local/bin/app"]
```

---

### Kubernetes

#### 基础部署

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-app
  template:
    metadata:
      labels:
        app: rust-app
    spec:
      containers:
      - name: app
        image: myregistry/rust-app:v1.0.0
        ports:
        - containerPort: 8080
        resources:
          requests:
            memory: "64Mi"
            cpu: "100m"
          limits:
            memory: "256Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
        lifecycle:
          preStop:
            exec:
              command: ["/bin/sh", "-c", "sleep 10"]
```

#### HPA 配置

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: rust-app-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: rust-app
  minReplicas: 3
  maxReplicas: 20
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 10
        periodSeconds: 60
```

---

### Serverless

#### AWS Lambda

```rust
use lambda_runtime::{service_fn, LambdaEvent, Error};
use serde_json::{json, Value};

#[tokio::main]
async fn main() -> Result<(), Error> {
    let func = service_fn(handler);
    lambda_runtime::run(func).await?;
    Ok(())
}

async fn handler(event: LambdaEvent<Value>) -> Result<Value, Error> {
    let name = event.payload["name"].as_str().unwrap_or("world");

    Ok(json!({
        "statusCode": 200,
        "body": format!("Hello, {}!", name)
    }))
}
```

#### Cargo Lambda

```bash
# 安装
cargo install cargo-lambda

# 构建
cargo lambda build --release --target x86_64-unknown-linux-musl

# 部署
cargo lambda deploy --region us-east-1
```

---

## 📈 监控与可观测性

### 指标收集

#### Prometheus 集成

```rust
use prometheus::{Counter, Histogram, Registry, TextEncoder};
use lazy_static::lazy_static;

lazy_static! {
    static ref REGISTRY: Registry = Registry::new();

    static ref REQUEST_COUNT: Counter = Counter::new(
        "http_requests_total",
        "Total HTTP requests"
    ).unwrap();

    static ref REQUEST_DURATION: Histogram = Histogram::with_opts(
        HistogramOpts::new(
            "http_request_duration_seconds",
            "HTTP request duration"
        ).buckets(vec![0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0])
    ).unwrap();
}

fn init_metrics() {
    REGISTRY.register(Box::new(REQUEST_COUNT.clone())).unwrap();
    REGISTRY.register(Box::new(REQUEST_DURATION.clone())).unwrap();
}

// 中间件
async fn metrics_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> Response {
    let start = Instant::now();

    REQUEST_COUNT.inc();

    let response = next.run(req).await;

    let duration = start.elapsed().as_secs_f64();
    REQUEST_DURATION.observe(duration);

    response
}
```

### 分布式追踪

#### OpenTelemetry + Jaeger

```rust
use opentelemetry::trace::Tracer;
use tracing::{info, instrument};
use tracing_subscriber::layer::SubscriberExt;

fn init_tracing() {
    let tracer = opentelemetry_jaeger::new_agent_pipeline()
        .with_service_name("rust-app")
        .install_simple()
        .unwrap();

    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);

    tracing_subscriber::registry()
        .with(telemetry)
        .with(tracing_subscriber::fmt::Layer::default())
        .init();
}

#[instrument(fields(user_id = %user_id))]
async fn process_user_request(user_id: u64) -> Result<(), Error> {
    info!("Processing request");

    let result = call_database(user_id).await?;

    info!("Request processed successfully");
    Ok(result)
}
```

---

## 🔒 安全

### 依赖审计

```bash
# 安装 cargo-audit
cargo install cargo-audit

# 运行审计
cargo audit

# 集成到 CI
cargo audit --deny warnings
```

```yaml
# .github/workflows/security.yml
name: Security Audit
on:
  schedule:
    - cron: '0 0 * * *'
  push:
    paths:
      - '**/Cargo.toml'
      - '**/Cargo.lock'

jobs:
  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: rustsec/audit-check@v1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}
```

### 密钥管理

#### AWS Secrets Manager

```rust
use aws_sdk_secretsmanager::Client;

async fn get_database_url() -> Result<String, Error> {
    let config = aws_config::load_from_env().await;
    let client = Client::new(&config);

    let resp = client
        .get_secret_value()
        .secret_id("prod/database/url")
        .send()
        .await?;

    Ok(resp.secret_string().unwrap_or_default().to_string())
}
```

---

## ⚡ 性能优化

### 性能分析

#### Criterion 基准测试

```rust
use criterion::{criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(20)));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

#### flamegraph

```bash
cargo install flamegraph

# 运行并生成火焰图
cargo flamegraph --bin myapp

# 在容器中使用
perf record -F 99 -g -- ./myapp
cargo flamegraph --perfdata perf.data
```

### 内存优化

#### 内存分析工具

```bash
# heaptrack
cargo install heaptrack
heaptrack ./target/release/myapp

# valgrind (开发环境)
valgrind --tool=massif ./target/release/myapp
```

#### 优化技巧

| 技术 | 效果 | 场景 |
|------|------|------|
| Arena Allocation | -30% 分配开销 | 短生命周期对象 |
| Object Pooling | -50% GC 压力 | 高频创建对象 |
| Zero-Copy | -90% 拷贝开销 | 网络/文件 I/O |
| Compact Strings | -40% 内存 | 短字符串 |

---

## 🛡️ 可靠性

### 熔断器模式

```rust
use std::sync::Arc;
use tokio::sync::Mutex;
use std::time::{Duration, Instant};

enum CircuitState {
    Closed,      // 正常
    Open,        // 熔断
    HalfOpen,    // 半开测试
}

struct CircuitBreaker {
    state: Arc<Mutex<CircuitState>>,
    failure_count: Arc<Mutex<u32>>,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
    threshold: u32,
    timeout: Duration,
}

impl CircuitBreaker {
    async fn call<F, Fut, T>(&self, f: F) -> Result<T, Error>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, Error>>,
    {
        let state = self.state.lock().await;

        match *state {
            CircuitState::Open => {
                let last = *self.last_failure_time.lock().await;
                if let Some(time) = last {
                    if time.elapsed() > self.timeout {
                        // 转为半开状态
                        drop(state);
                        *self.state.lock().await = CircuitState::HalfOpen;
                    } else {
                        return Err(Error::CircuitOpen);
                    }
                }
            }
            _ => {}
        }

        drop(state);

        match f().await {
            Ok(result) => {
                self.on_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_failure().await;
                Err(e)
            }
        }
    }

    async fn on_failure(&self) {
        let mut count = self.failure_count.lock().await;
        *count += 1;

        if *count >= self.threshold {
            *self.state.lock().await = CircuitState::Open;
            *self.last_failure_time.lock().await = Some(Instant::now());
        }
    }

    async fn on_success(&self) {
        *self.failure_count.lock().await = 0;
        *self.state.lock().await = CircuitState::Closed;
    }
}
```

### 优雅降级

```rust
use std::sync::atomic::{AtomicBool, Ordering};

struct Service {
    healthy: AtomicBool,
    degraded_mode: AtomicBool,
}

impl Service {
    async fn handle_request(&self, req: Request) -> Response {
        if self.degraded_mode.load(Ordering::Relaxed) {
            return self.handle_degraded(req).await;
        }

        match self.handle_normal(req).await {
            Ok(resp) => resp,
            Err(_) => {
                self.degraded_mode.store(true, Ordering::Relaxed);
                self.handle_degraded(req).await
            }
        }
    }

    async fn handle_normal(&self, req: Request) -> Result<Response, Error> {
        // 完整功能
        Ok(Response::full(self.process(req).await?))
    }

    async fn handle_degraded(&self, req: Request) -> Response {
        // 简化功能或缓存响应
        Response::cached(self.cache.get(&req.key).await)
    }
}
```

---

## 🔗 参考资源

- [The Twelve-Factor App](https://12factor.net/)
- [Google SRE Book](https://sre.google/sre-book/table-of-contents/)
- [AWS Well-Architected](https://aws.amazon.com/architecture/well-architected/)
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
**状态**: 🔄 持续完善中
