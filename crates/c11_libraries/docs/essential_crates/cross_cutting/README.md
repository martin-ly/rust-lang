# 横切关注点 (Cross-Cutting Concerns)

**层级定位**: 贯穿所有层级的通用功能  
**重要程度**: ⭐⭐⭐⭐⭐ (对所有项目必备)  
**更新日期**: 2025-10-20  
**Rust 版本**: 1.90+

---

## 📋 目录

- [横切关注点 (Cross-Cutting Concerns)](#横切关注点-cross-cutting-concerns)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🗂️ 类别分类](#️-类别分类)
    - [核心类别 (6个)](#核心类别-6个)
  - [🎯 核心工具速览](#-核心工具速览)
    - [错误处理 (Error Handling)](#错误处理-error-handling)
    - [密码学 (Cryptography)](#密码学-cryptography)
    - [可观测性 (Observability)](#可观测性-observability)
    - [配置管理 (Configuration)](#配置管理-configuration)
  - [🚀 快速开始](#-快速开始)
    - [典型项目配置](#典型项目配置)
  - [📚 按场景导航](#-按场景导航)
    - [🌐 Web 应用开发](#-web-应用开发)
    - [📦 库开发](#-库开发)
    - [🎮 CLI 工具](#-cli-工具)
  - [🎓 学习路径](#-学习路径)
    - [第1阶段：错误处理 (Week 1)](#第1阶段错误处理-week-1)
    - [第2阶段：密码学基础 (Week 2)](#第2阶段密码学基础-week-2)
    - [第3阶段：可观测性 (Week 3)](#第3阶段可观测性-week-3)
    - [第4阶段：配置管理 (Week 4)](#第4阶段配置管理-week-4)
  - [💡 最佳实践](#-最佳实践)
    - [1. 错误处理策略](#1-错误处理策略)
    - [2. 分层配置](#2-分层配置)
    - [3. 结构化日志](#3-结构化日志)
  - [📊 工具选择决策树](#-工具选择决策树)
    - [错误处理选择](#错误处理选择)
    - [密码学选择](#密码学选择)
    - [可观测性选择](#可观测性选择)
  - [🌟 典型应用架构](#-典型应用架构)
    - [Web 应用完整配置](#web-应用完整配置)
  - [📈 统计信息](#-统计信息)
  - [🔗 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [最佳实践](#最佳实践)
  - [🔄 版本历史](#-版本历史)

## 📋 概述

横切关注点（Cross-Cutting Concerns）是指那些影响整个应用程序多个模块的功能，它们不属于特定的业务逻辑层，而是贯穿整个系统的通用需求。

---

## 🗂️ 类别分类

### 核心类别 (6个)

| # | 类别 | 说明 | 重要程度 |
|---|------|------|---------|
| 1 | [错误处理](./error_handling/README.md) | anyhow, thiserror, eyre | ⭐⭐⭐⭐⭐ |
| 2 | [密码学](./cryptography/README.md) | ring, rustls, argon2 | ⭐⭐⭐⭐⭐ |
| 3 | [可观测性](./observability/README.md) | tracing, metrics, OpenTelemetry | ⭐⭐⭐⭐⭐ |
| 4 | [配置管理](./configuration/README.md) | config, figment, dotenvy | ⭐⭐⭐⭐ |
| 5 | [国际化](./i18n/README.md) | fluent, gettext-rs | ⭐⭐⭐ |
| 6 | [序列化](./serialization/README.md) | serde, bincode, postcard | ⭐⭐⭐⭐⭐ |

---

## 🎯 核心工具速览

### 错误处理 (Error Handling)

| 工具 | 用途 | 场景 | 推荐度 |
|------|------|------|--------|
| **anyhow** | 应用层错误处理 | CLI, Web应用 | ✅ 必备 |
| **thiserror** | 库错误定义 | 库开发 | ✅ 必备 |
| **eyre** | 增强错误报告 | 复杂错误链 | 💡 推荐 |

### 密码学 (Cryptography)

| 工具 | 用途 | 场景 | 推荐度 |
|------|------|------|--------|
| **ring** | 通用密码学 | 加密、签名 | ✅ 必备 |
| **rustls** | TLS实现 | HTTPS服务 | ✅ 必备 |
| **argon2** | 密码哈希 | 用户认证 | ✅ 必备 |

### 可观测性 (Observability)

| 工具 | 用途 | 场景 | 推荐度 |
|------|------|------|--------|
| **tracing** | 结构化日志 | 应用追踪 | ✅ 必备 |
| **metrics** | 指标收集 | 性能监控 | 🌟 强推 |
| **opentelemetry** | 分布式追踪 | 微服务 | 🌟 强推 |

### 配置管理 (Configuration)

| 工具 | 用途 | 场景 | 推荐度 |
|------|------|------|--------|
| **config** | 多源配置 | 应用配置 | ✅ 必备 |
| **figment** | 类型安全配置 | Rocket框架 | 💡 推荐 |
| **dotenvy** | 环境变量 | 开发环境 | ✅ 必备 |

---

## 🚀 快速开始

### 典型项目配置

```toml
# Cargo.toml
[dependencies]
# 错误处理
anyhow = "1.0"           # 应用层
thiserror = "1.0"        # 库开发

# 密码学
ring = "0.17"            # 加密
rustls = "0.22"          # TLS
argon2 = "0.5"           # 密码哈希

# 可观测性
tracing = "0.1"          # 日志追踪
tracing-subscriber = "0.3"
metrics = "0.21"         # 指标

# 配置
config = "0.14"          # 配置管理
dotenvy = "0.15"         # 环境变量

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

---

## 📚 按场景导航

### 🌐 Web 应用开发

- [错误处理](./error_handling/README.md) - anyhow, thiserror
- [密码学](./cryptography/README.md) - rustls, argon2
- [可观测性](./observability/README.md) - tracing, metrics
- [配置管理](./configuration/README.md) - config, dotenvy

### 📦 库开发

- [错误处理](./error_handling/README.md#thiserror) - thiserror
- [序列化](./serialization/README.md) - serde
- [密码学](./cryptography/README.md) - ring

### 🎮 CLI 工具

- [错误处理](./error_handling/README.md#anyhow) - anyhow, eyre
- [配置管理](./configuration/README.md) - config
- [可观测性](./observability/README.md) - tracing

---

## 🎓 学习路径

### 第1阶段：错误处理 (Week 1)

1. **理解 Result 和 Option**
   - Rust 错误处理基础
   - ? 操作符的使用

2. **应用 anyhow**
   - 简化错误传播
   - Context 增强错误信息

3. **库开发用 thiserror**
   - 定义自定义错误类型
   - 实现 Error trait

### 第2阶段：密码学基础 (Week 2)

1. **密码学概念**
   - 对称加密 vs 非对称加密
   - 哈希 vs 加密

2. **ring 库使用**
   - HMAC 签名验证
   - AES 加密解密

3. **密码安全**
   - argon2 密码哈希
   - 安全存储实践

### 第3阶段：可观测性 (Week 3)

1. **结构化日志**
   - tracing 基础
   - Span 和 Event

2. **指标收集**
   - metrics 库
   - Prometheus 集成

3. **分布式追踪**
   - OpenTelemetry
   - Jaeger 集成

### 第4阶段：配置管理 (Week 4)

1. **环境变量**
   - dotenvy 使用
   - 12-factor 原则

2. **多源配置**
   - config 库
   - 配置优先级

3. **类型安全**
   - serde 反序列化
   - 配置验证

---

## 💡 最佳实践

### 1. 错误处理策略

```rust
// 应用层：使用 anyhow
use anyhow::{Context, Result};

fn process_file(path: &str) -> Result<String> {
    let content = std::fs::read_to_string(path)
        .context("Failed to read file")?;
    
    let processed = transform(&content)
        .context("Failed to transform content")?;
    
    Ok(processed)
}

// 库层：使用 thiserror
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MyError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Parse error at line {line}: {msg}")]
    Parse { line: usize, msg: String },
}
```

### 2. 分层配置

```rust
use config::{Config, Environment, File};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct AppConfig {
    database_url: String,
    log_level: String,
    port: u16,
}

fn load_config() -> Result<AppConfig> {
    let config = Config::builder()
        // 1. 默认配置
        .add_source(File::with_name("config/default"))
        // 2. 环境特定配置
        .add_source(File::with_name("config/local").required(false))
        // 3. 环境变量（优先级最高）
        .add_source(Environment::with_prefix("APP"))
        .build()?;
    
    config.try_deserialize()
}
```

### 3. 结构化日志

```rust
use tracing::{info, instrument, Level};
use tracing_subscriber;

#[instrument]
fn process_user(user_id: u64) -> Result<()> {
    info!(user_id, "Processing user");
    
    // 业务逻辑
    
    Ok(())
}

fn main() {
    tracing_subscriber::fmt()
        .with_max_level(Level::INFO)
        .init();
    
    process_user(123).unwrap();
}
```

---

## 📊 工具选择决策树

### 错误处理选择

```text
开发库？
├─ 是 → thiserror (定义自定义错误)
└─ 否 → 开发应用？
    ├─ CLI → anyhow 或 eyre (增强报告)
    └─ Web → anyhow + 错误响应中间件
```

### 密码学选择

```text
需求？
├─ TLS/HTTPS → rustls
├─ 密码哈希 → argon2
├─ JWT → jsonwebtoken
├─ 通用加密 → ring (AES, ChaCha20)
└─ 签名验证 → ring (HMAC, Ed25519)
```

### 可观测性选择

```text
项目规模？
├─ 小型 → tracing (日志)
├─ 中型 → tracing + env_logger
└─ 大型 → tracing + metrics + OpenTelemetry
    ├─ 日志 → tracing
    ├─ 指标 → metrics + Prometheus
    └─ 追踪 → OpenTelemetry + Jaeger
```

---

## 🌟 典型应用架构

### Web 应用完整配置

```rust
// main.rs
use anyhow::Result;
use config::Config;
use tracing::info;
use tracing_subscriber;

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();
    
    // 2. 加载配置
    dotenvy::dotenv().ok();
    let config = load_config()?;
    
    // 3. 启动服务
    info!("Starting server on port {}", config.port);
    start_server(config).await?;
    
    Ok(())
}
```

---

## 📈 统计信息

- **类别总数**: 6个
- **核心工具**: 20+
- **覆盖场景**: Web, CLI, 库开发, 微服务
- **文档状态**: 进行中

---

## 🔗 相关资源

### 官方文档

- [Rust Error Handling Book](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [RustCrypto](https://github.com/RustCrypto)
- [Tokio Tracing](https://tokio.rs/tokio/topics/tracing)

### 最佳实践

- [Rust API Guidelines - Error Handling](https://rust-lang.github.io/api-guidelines/errors.html)
- [OWASP Cryptographic Storage Cheat Sheet](https://cheatsheetseries.owasp.org/cheatsheets/Cryptographic_Storage_Cheat_Sheet.html)

---

## 🔄 版本历史

- **v1.0.0** (2025-10-20): 初始版本，错误处理类别

---

**导航**: [返回主页](../README.md) | [第1层：基础设施](../01_infrastructure/README.md)
