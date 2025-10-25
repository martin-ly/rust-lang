# c13_reliability 使用指南

## 📊 目录

- [c13\_reliability 使用指南](#c13_reliability-使用指南)
  - [📊 目录](#-目录)
  - [📦 快速开始](#-快速开始)
    - [1. 添加依赖](#1-添加依赖)
    - [2. 选择功能特性](#2-选择功能特性)
  - [🎯 功能特性说明](#-功能特性说明)
    - [默认特性 (default)](#默认特性-default)
    - [核心特性](#核心特性)
    - [可观测性特性](#可观测性特性)
    - [高级特性](#高级特性)
    - [环境支持](#环境支持)
    - [云原生特性 (可选)](#云原生特性-可选)
  - [📝 使用示例](#-使用示例)
    - [示例 1: 最小配置](#示例-1-最小配置)
    - [示例 2: 异步应用](#示例-2-异步应用)
    - [示例 3: 可观测性完整方案](#示例-3-可观测性完整方案)
    - [示例 4: 云原生部署](#示例-4-云原生部署)
    - [示例 5: 高性能配置](#示例-5-高性能配置)
    - [示例 6: 形式化验证](#示例-6-形式化验证)
    - [示例 7: 嵌入式系统](#示例-7-嵌入式系统)
  - [💻 代码示例](#-代码示例)
    - [基础使用](#基础使用)
    - [异步使用](#异步使用)
    - [监控和指标](#监控和指标)
    - [容错机制](#容错机制)
    - [OpenTelemetry 追踪](#opentelemetry-追踪)
  - [🔧 完整项目示例](#-完整项目示例)
    - [Web 服务项目的 Cargo.toml](#web-服务项目的-cargotoml)
    - [微服务项目的 Cargo.toml](#微服务项目的-cargotoml)
  - [🚀 运行和测试](#-运行和测试)
    - [构建项目](#构建项目)
    - [运行示例](#运行示例)
    - [运行测试](#运行测试)
  - [📊 性能优化建议](#-性能优化建议)
    - [1. 生产环境配置](#1-生产环境配置)
    - [2. 开发环境配置](#2-开发环境配置)
  - [🔒 安全性考虑](#-安全性考虑)
    - [1. 审计依赖](#1-审计依赖)
    - [2. 最小权限原则](#2-最小权限原则)
  - [📚 进一步学习](#-进一步学习)
  - [🤝 贡献和支持](#-贡献和支持)
  - [📄 许可证](#-许可证)

**版本**: 0.1.1  
**Rust 版本**: 1.90+  
**Edition**: 2024

## 📦 快速开始

### 1. 添加依赖

在您的项目 `Cargo.toml` 中添加：

```toml
[dependencies]
c13_reliability = { version = "0.1.1", path = "../c13_reliability" }

# 或者从 crates.io（发布后）
# c13_reliability = "0.1.1"

# 或者从 GitHub
# c13_reliability = { git = "https://github.com/rust-lang/c13_reliability" }
```

### 2. 选择功能特性

根据您的需求启用相应的 features：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = ["async", "monitoring", "fault-tolerance", "otlp"]
}
```

## 🎯 功能特性说明

### 默认特性 (default)

```toml
default = [
    "std", 
    "async", 
    "monitoring", 
    "fault-tolerance", 
    "otlp", 
    "logging", 
    "os-environment"
]
```

这些特性在不指定时会自动启用。

### 核心特性

| Feature | 说明 | 依赖项 |
|---------|------|--------|
| `std` | 标准库支持 | 无 |
| `async` | 异步运行时支持 | tokio, futures, async-trait |
| `monitoring` | 监控和指标收集 | metrics, prometheus, sysinfo |
| `fault-tolerance` | 容错机制 | parking_lot, dashmap, crossbeam |
| `logging` | 日志记录 | env_logger |

### 可观测性特性

| Feature | 说明 | 用途 |
|---------|------|------|
| `otlp` | OpenTelemetry OTLP 支持 | 分布式追踪 |
| `otlp-stdout` | OTLP 标准输出导出 | 调试和开发 |
| `otlp-proto` | OTLP 协议支持 | 协议解析 |

### 高级特性

| Feature | 说明 | 适用场景 |
|---------|------|----------|
| `chaos-engineering` | 混沌工程测试 | 压力测试 |
| `jemalloc` | jemalloc 内存分配器 | 性能优化 |
| `verification` | 形式化验证基础 | 代码验证 |
| `prusti` | Prusti 验证工具 | 静态分析 |
| `creusot` | Creusot 验证工具 | 演绎验证 |

### 环境支持

| Feature | 说明 | 目标环境 |
|---------|------|----------|
| `os-environment` | 操作系统环境 | 标准服务器 |
| `embedded-environment` | 嵌入式环境 | IoT 设备 |
| `container-environment` | 容器环境 | Docker/K8s |

### 云原生特性 (可选)

| Feature | 说明 | 何时启用 |
|---------|------|----------|
| `containers` | 容器支持 | 容器化部署 |
| `virtualization` | 虚拟化支持 | VM 环境 |
| `kubernetes` | Kubernetes 集成 | K8s 部署 |
| `docker-runtime` | Docker 运行时适配 | 本地 Docker |
| `oci` | OCI 规范支持 | OCI 容器 |

## 📝 使用示例

### 示例 1: 最小配置

仅使用核心功能，不需要异步和监控：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    default-features = false,
    features = ["std"]
}
```

### 示例 2: 异步应用

构建异步 Web 服务：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = ["async", "monitoring", "otlp"]
}
tokio = { version = "1.48", features = ["full"] }
```

### 示例 3: 可观测性完整方案

启用完整的可观测性支持：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = [
        "async",
        "monitoring",
        "fault-tolerance",
        "otlp",
        "otlp-proto",
        "logging"
    ]
}
```

### 示例 4: 云原生部署

Kubernetes 环境部署：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = [
        "async",
        "monitoring",
        "fault-tolerance",
        "otlp",
        "containers",
        "kubernetes"
    ]
}
```

### 示例 5: 高性能配置

使用 jemalloc 和容错机制：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = [
        "async",
        "fault-tolerance",
        "jemalloc",
        "monitoring"
    ]
}
```

### 示例 6: 形式化验证

开发时进行代码验证：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = ["verification", "prusti"]
}

# 开发依赖
[dev-dependencies]
prusti-contracts = "0.2"
```

### 示例 7: 嵌入式系统

资源受限的嵌入式环境：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    default-features = false,
    features = ["embedded-environment"]
}
```

## 💻 代码示例

### 基础使用

```rust
use c13_reliability::prelude::*;

fn main() {
    // 初始化可靠性框架
    let config = ReliabilityConfig::default();
    let reliability = Reliability::new(config);
    
    // 使用错误处理
    match reliability.execute(|| {
        // 您的业务逻辑
        Ok(())
    }) {
        Ok(_) => println!("执行成功"),
        Err(e) => eprintln!("执行失败: {}", e),
    }
}
```

### 异步使用

```rust
use c13_reliability::prelude::*;
use tokio;

#[tokio::main]
async fn main() {
    let config = ReliabilityConfig::default();
    let reliability = Reliability::new(config);
    
    // 异步执行
    if let Err(e) = reliability.execute_async(async {
        // 异步业务逻辑
        Ok(())
    }).await {
        eprintln!("异步执行失败: {}", e);
    }
}
```

### 监控和指标

```rust
use c13_reliability::monitoring::*;

fn main() {
    // 启用监控
    let monitor = Monitor::new();
    monitor.start();
    
    // 记录指标
    monitor.record_metric("request_count", 1.0);
    monitor.record_latency("api_latency", 125);
    
    // 导出 Prometheus 指标
    let metrics = monitor.export_prometheus();
    println!("{}", metrics);
}
```

### 容错机制

```rust
use c13_reliability::fault_tolerance::*;
use std::time::Duration;

fn main() {
    // 创建重试策略
    let retry = RetryPolicy::exponential_backoff(
        3,                              // 最大重试次数
        Duration::from_secs(1),         // 初始延迟
        Duration::from_secs(60)         // 最大延迟
    );
    
    // 执行带重试的操作
    let result = retry.execute(|| {
        // 可能失败的操作
        external_api_call()
    });
}

fn external_api_call() -> Result<String, Error> {
    // 外部 API 调用
    Ok("Success".to_string())
}
```

### OpenTelemetry 追踪

```rust
use c13_reliability::telemetry::*;
use tracing::{info, span, Level};

#[tokio::main]
async fn main() {
    // 初始化 OpenTelemetry
    let _guard = init_telemetry("my-service");
    
    // 创建 span
    let span = span!(Level::INFO, "process_request");
    let _enter = span.enter();
    
    info!("处理请求");
    process_request().await;
    info!("请求完成");
}

async fn process_request() {
    // 业务逻辑
}
```

## 🔧 完整项目示例

### Web 服务项目的 Cargo.toml

```toml
[package]
name = "my-web-service"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# 可靠性框架
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = [
        "async",
        "monitoring",
        "fault-tolerance",
        "otlp",
        "logging",
        "os-environment"
    ]
}

# 异步运行时
tokio = { version = "1.48", features = ["full"] }

# Web 框架
axum = "0.8"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }

[dev-dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = ["chaos-engineering"]
}
```

### 微服务项目的 Cargo.toml

```toml
[package]
name = "my-microservice"
version = "0.1.0"
edition = "2024"

[dependencies]
c13_reliability = { 
    version = "0.1.1",
    path = "../c13_reliability",
    features = [
        "async",
        "monitoring",
        "fault-tolerance",
        "otlp",
        "containers",
        "kubernetes",
        "jemalloc"
    ]
}

# 服务发现
consul = "0.4"

# 配置管理
config = "0.15"

# 数据库
sqlx = { version = "0.8", features = ["postgres", "runtime-tokio"] }

# 消息队列
rdkafka = "0.36"
```

## 🚀 运行和测试

### 构建项目

```bash
# 使用默认特性
cargo build

# 指定特性
cargo build --features "async,monitoring,otlp"

# 发布构建
cargo build --release --features "async,monitoring,fault-tolerance,jemalloc"
```

### 运行示例

```bash
# 运行基础示例
cargo run --example basic_usage

# 运行形式化验证示例
cargo run --example creusot_basic
cargo run --example prusti_basic
cargo run --example kani_basic
```

### 运行测试

```bash
# 运行所有测试
cargo test

# 运行特定特性的测试
cargo test --features "async,monitoring"

# 运行示例测试
cargo test --examples
```

## 📊 性能优化建议

### 1. 生产环境配置

```toml
[profile.release]
opt-level = 3
lto = true
codegen-units = 1
strip = true

[dependencies]
c13_reliability = { 
    version = "0.1.1",
    features = [
        "async",
        "fault-tolerance",
        "jemalloc",
        "monitoring"
    ]
}
```

### 2. 开发环境配置

```toml
[profile.dev]
opt-level = 0

[dependencies]
c13_reliability = { 
    version = "0.1.1",
    features = [
        "async",
        "logging",
        "chaos-engineering"
    ]
}
```

## 🔒 安全性考虑

### 1. 审计依赖

```bash
# 安装 cargo-audit
cargo install cargo-audit

# 检查安全漏洞
cargo audit
```

### 2. 最小权限原则

仅启用必需的特性：

```toml
[dependencies]
c13_reliability = { 
    version = "0.1.1",
    default-features = false,
    features = ["std", "async"]  # 仅启用必需特性
}
```

## 📚 进一步学习

- [错误处理最佳实践](./ERROR_HANDLING_GUIDE.md)
- [容错机制详解](./FAULT_TOLERANCE_GUIDE.md)
- [监控和可观测性](./MONITORING_GUIDE.md)
- [形式化验证工具](./FORMAL_VERIFICATION_TOOLS_GUIDE.md)

## 🤝 贡献和支持

- **GitHub**: <https://github.com/rust-lang/c13_reliability>
- **文档**: <https://docs.rs/c13_reliability>
- **问题反馈**: <https://github.com/rust-lang/c13_reliability/issues>

## 📄 许可证

MIT OR Apache-2.0

---

**最后更新**: 2025-10-20  
**维护者**: Rust Reliability Team
