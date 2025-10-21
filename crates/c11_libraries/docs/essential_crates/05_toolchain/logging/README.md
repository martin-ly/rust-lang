# Logging - Rust 日志与可观测性

> **核心库**: log, tracing, env_logger, tracing-subscriber  
> **适用场景**: 应用日志、分布式追踪、结构化日志、性能分析

## 📋 目录

- [Logging - Rust 日志与可观测性](#logging---rust-日志与可观测性)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心概念](#核心概念)
    - [日志 vs 追踪](#日志-vs-追踪)
  - [核心库对比](#核心库对比)
    - [功能矩阵](#功能矩阵)
    - [选择指南](#选择指南)
  - [log - 标准日志门面](#log---标准日志门面)
    - [核心特性](#核心特性)
    - [基础用法](#基础用法)
    - [日志级别](#日志级别)
  - [env\_logger - 环境变量配置日志](#env_logger---环境变量配置日志)
    - [基础配置](#基础配置)
    - [过滤规则](#过滤规则)
    - [自定义格式](#自定义格式)
  - [tracing - 结构化追踪](#tracing---结构化追踪)
    - [核心概念1](#核心概念1)
    - [基础用法1](#基础用法1)
    - [Span 和 Event](#span-和-event)
    - [instrument 宏](#instrument-宏)
  - [tracing-subscriber - 订阅者层](#tracing-subscriber---订阅者层)
    - [层级架构](#层级架构)
    - [JSON 输出](#json-输出)
    - [多订阅者](#多订阅者)
  - [使用场景](#使用场景)
    - [Web 应用日志](#web-应用日志)
    - [分布式追踪](#分布式追踪)
    - [性能分析](#性能分析)
  - [最佳实践](#最佳实践)
    - [1. 使用结构化字段](#1-使用结构化字段)
    - [2. 避免昂贵的计算](#2-避免昂贵的计算)
    - [3. 跳过敏感信息](#3-跳过敏感信息)
    - [4. 使用合适的日志级别](#4-使用合适的日志级别)
    - [5. 生产环境配置](#5-生产环境配置)
  - [常见陷阱](#常见陷阱)
    - [1. 忘记初始化日志](#1-忘记初始化日志)
    - [2. 日志级别配置错误](#2-日志级别配置错误)
    - [3. Span Guard 被立即释放](#3-span-guard-被立即释放)
    - [4. 过度日志影响性能](#4-过度日志影响性能)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [教程](#教程)
    - [相关库](#相关库)

---

## 概述

### 核心概念

Rust 的日志生态系统由两个核心层次组成：

1. **日志门面 (Facade)**: `log` 或 `tracing` 提供统一的API
2. **日志实现 (Implementation)**: `env_logger`、`tracing-subscriber` 等实际处理日志

```text
┌─────────────────┐
│  Application    │
└────────┬────────┘
         │
    ┌────▼────┐
    │  log /  │  ← 门面层 (Facade)
    │ tracing │
    └────┬────┘
         │
┌────────▼──────────┐
│  env_logger /     │  ← 实现层 (Implementation)
│ tracing-subscriber│
└───────────────────┘
```

### 日志 vs 追踪

| 特性 | log | tracing |
|------|-----|---------|
| **模型** | 离散日志消息 | 结构化事件 + Span |
| **上下文** | 无内置上下文 | 自动传播上下文 |
| **性能** | 轻量级 | 略重但功能强大 |
| **异步支持** | 基础 | 原生支持 |
| **推荐场景** | 简单应用 | 分布式系统 |

---

## 核心库对比

### 功能矩阵

| 功能 | log + env_logger | tracing + subscriber | 推荐 |
|------|------------------|---------------------|------|
| **基础日志** | ✅ | ✅ | 两者皆可 |
| **结构化字段** | ❌ | ✅ | tracing |
| **Span 追踪** | ❌ | ✅ | tracing |
| **异步上下文** | ❌ | ✅ | tracing |
| **JSON 输出** | 🔶 需插件 | ✅ | tracing |
| **过滤灵活性** | 🔶 环境变量 | ✅ 代码配置 | tracing |
| **生态成熟度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 平手 |
| **学习曲线** | ⭐⭐ 简单 | ⭐⭐⭐⭐ 较复杂 | log |
| **性能开销** | ⭐⭐⭐⭐⭐ 极小 | ⭐⭐⭐⭐ 小 | log |

### 选择指南

**使用 log + env_logger**:

- ✅ 简单的 CLI 工具
- ✅ 同步应用
- ✅ 快速原型开发
- ✅ 对性能极度敏感

**使用 tracing + tracing-subscriber**:

- ✅ Web 服务和微服务
- ✅ 异步应用
- ✅ 需要分布式追踪
- ✅ 复杂的性能分析

---

## log - 标准日志门面

### 核心特性

```toml
[dependencies]
log = "0.4"
```

1. **5 个日志级别**: error, warn, info, debug, trace
2. **零成本抽象**: 编译时可优化掉
3. **广泛支持**: 几乎所有库都使用

### 基础用法

```rust
use log::{error, warn, info, debug, trace};

fn main() {
    // 需要配置实现（如 env_logger）
    env_logger::init();
    
    error!("发生错误: {}", "数据库连接失败");
    warn!("警告: 磁盘空间不足");
    info!("服务器启动在端口 {}", 8080);
    debug!("调试信息: {:?}", some_data);
    trace!("详细追踪");
}
```

### 日志级别

```rust
use log::{LevelFilter, Level};

// 判断级别
if log::log_enabled!(Level::Debug) {
    let expensive_data = compute();
    debug!("数据: {:?}", expensive_data);
}

// 条件日志（避免不必要的计算）
log::log!(target: "my_module", Level::Info, "message");
```

---

## env_logger - 环境变量配置日志

### 基础配置

```toml
[dependencies]
env_logger = "0.11"
```

```rust
fn main() {
    // 最简单配置
    env_logger::init();
    
    // 或者使用 Builder 自定义
    env_logger::Builder::from_default_env()
        .filter_level(log::LevelFilter::Info)
        .init();
}
```

```bash
# 环境变量配置
RUST_LOG=info cargo run              # 全局 info
RUST_LOG=debug cargo run             # 全局 debug
RUST_LOG=my_app=trace cargo run      # 模块级别
RUST_LOG=my_app=debug,hyper=info     # 多模块
```

### 过滤规则

```bash
# 复杂过滤规则
RUST_LOG=error,my_app::api=debug,sqlx=warn cargo run

# 正则匹配
RUST_LOG=my_app::.*=debug cargo run
```

### 自定义格式

```rust
use env_logger::Builder;
use std::io::Write;

fn main() {
    Builder::from_default_env()
        .format(|buf, record| {
            writeln!(
                buf,
                "[{} {} {}:{}] {}",
                chrono::Local::now().format("%Y-%m-%d %H:%M:%S"),
                record.level(),
                record.file().unwrap_or("unknown"),
                record.line().unwrap_or(0),
                record.args()
            )
        })
        .init();
}
```

---

## tracing - 结构化追踪

### 核心概念1

```toml
[dependencies]
tracing = "0.1"
```

1. **Span**: 表示一段时间的操作
2. **Event**: 单个时间点的日志
3. **Subscriber**: 处理 Span 和 Event 的订阅者
4. **Field**: 结构化字段

### 基础用法1

```rust
use tracing::{info, warn, error, debug, trace};

fn main() {
    tracing_subscriber::fmt::init();
    
    // 基础日志
    info!("服务器启动");
    
    // 结构化字段
    info!(
        user_id = 123,
        action = "login",
        "用户登录成功"
    );
    
    // 动态字段
    let user = "alice";
    debug!(user, "处理请求");
}
```

### Span 和 Event

```rust
use tracing::{span, Level, info};

fn process_request(id: u64) {
    // 创建 Span
    let span = span!(Level::INFO, "request", id);
    let _guard = span.enter();
    
    info!("开始处理");
    
    // 嵌套 Span
    let db_span = span!(Level::DEBUG, "database");
    let _db_guard = db_span.enter();
    info!("查询数据库");
}

// 输出会自动包含 Span 上下文：
// INFO request{id=42}: 开始处理
// DEBUG request{id=42}:database: 查询数据库
```

### instrument 宏

```rust
use tracing::instrument;

#[instrument]
fn create_user(name: String, age: u32) -> Result<User, Error> {
    // 自动创建 Span: create_user{name="alice" age=30}
    info!("创建用户");
    
    // 函数参数自动记录
    db::insert_user(name, age)
}

#[instrument(skip(password))]  // 跳过敏感字段
fn login(username: String, password: String) -> Result<Token, Error> {
    // Span: login{username="alice"}  ← password 被跳过
    Ok(authenticate(username, password)?)
}

#[instrument(fields(user_id = %user.id))]  // 自定义字段
fn process(user: &User) {
    // Span: process{user_id=123}
}
```

---

## tracing-subscriber - 订阅者层

### 层级架构

```toml
[dependencies]
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
```

```rust
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

fn main() {
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer())  // 格式化层
        .with(tracing_subscriber::EnvFilter::from_default_env())  // 过滤层
        .init();
}
```

### JSON 输出

```rust
use tracing_subscriber::fmt;

fn main() {
    fmt()
        .json()
        .with_max_level(tracing::Level::INFO)
        .with_current_span(true)
        .init();
    
    tracing::info!(
        user_id = 123,
        action = "login",
        "用户登录"
    );
}

// 输出 JSON:
// {"timestamp":"2025-10-20T10:30:45Z","level":"INFO","fields":{"user_id":123,"action":"login"},"target":"my_app","message":"用户登录"}
```

### 多订阅者

```rust
use tracing_subscriber::{fmt, layer::SubscriberExt, EnvFilter};

fn main() {
    let console_layer = fmt::layer()
        .with_writer(std::io::stdout);
    
    let file_layer = fmt::layer()
        .json()
        .with_writer(std::fs::File::create("app.log").unwrap());
    
    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(console_layer)
        .with(file_layer)
        .init();
}
```

---

## 使用场景

### Web 应用日志

```rust
use axum::{routing::get, Router};
use tracing::{info, instrument};
use tower_http::trace::TraceLayer;

#[instrument]
async fn handler(id: String) -> String {
    info!("处理请求");
    format!("ID: {}", id)
}

#[tokio::main]
async fn main() {
    // 初始化 tracing
    tracing_subscriber::fmt()
        .with_target(false)
        .compact()
        .init();
    
    let app = Router::new()
        .route("/api/:id", get(handler))
        .layer(TraceLayer::new_for_http());
    
    info!("服务器启动在 0.0.0.0:3000");
    axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

### 分布式追踪

```rust
use tracing::{info, instrument};
use tracing_opentelemetry::OpenTelemetryLayer;
use opentelemetry::global;

#[instrument]
async fn service_a() {
    info!("服务 A 处理");
    service_b().await;
}

#[instrument]
async fn service_b() {
    info!("服务 B 处理");
}

#[tokio::main]
async fn main() {
    // 配置 OpenTelemetry
    let tracer = opentelemetry_jaeger::new_pipeline()
        .with_service_name("my-service")
        .install_simple()
        .unwrap();
    
    tracing_subscriber::registry()
        .with(OpenTelemetryLayer::new(tracer))
        .init();
    
    service_a().await;
    
    global::shutdown_tracer_provider();
}
```

### 性能分析

```rust
use tracing::{info_span, instrument};

#[instrument]
fn expensive_operation() {
    let _span = info_span!("phase1").entered();
    // 阶段 1 代码
    
    drop(_span);
    
    let _span = info_span!("phase2").entered();
    // 阶段 2 代码
}

// 使用 tracing-flame 生成火焰图
// cargo install tracing-flame
```

---

## 最佳实践

### 1. 使用结构化字段

```rust
// ❌ 避免：字符串拼接
info!("用户 {} 执行了 {} 操作", user_id, action);

// ✅ 推荐：结构化字段
info!(user_id = %user_id, action = %action, "用户操作");
```

### 2. 避免昂贵的计算

```rust
// ❌ 避免：总是执行
debug!("数据: {:?}", expensive_computation());

// ✅ 推荐：条件执行
if tracing::enabled!(tracing::Level::DEBUG) {
    let data = expensive_computation();
    debug!(?data, "数据");
}
```

### 3. 跳过敏感信息

```rust
#[instrument(skip(password, credit_card))]
fn process_payment(user: String, password: String, credit_card: String) {
    // password 和 credit_card 不会被记录
}
```

### 4. 使用合适的日志级别

```rust
error!("严重错误，需要立即处理");
warn!("警告，可能有问题");
info!("重要的业务信息");
debug!("调试信息");
trace!("详细的追踪信息");
```

### 5. 生产环境配置

```rust
use tracing_subscriber::fmt;

fn init_logging() {
    let env = std::env::var("ENVIRONMENT").unwrap_or_default();
    
    if env == "production" {
        // 生产环境：JSON 格式，无颜色
        fmt()
            .json()
            .with_max_level(tracing::Level::INFO)
            .init();
    } else {
        // 开发环境：人类可读格式
        fmt()
            .with_max_level(tracing::Level::DEBUG)
            .init();
    }
}
```

---

## 常见陷阱

### 1. 忘记初始化日志

```rust
// ❌ 错误：没有初始化
use log::info;

fn main() {
    info!("这条日志不会显示");  // ← 不会有任何输出
}

// ✅ 正确：初始化日志实现
fn main() {
    env_logger::init();  // ← 必须初始化
    info!("这条日志会显示");
}
```

### 2. 日志级别配置错误

```bash
# ❌ 错误：看不到 debug 日志
RUST_LOG=info cargo run

# ✅ 正确：使用正确的级别
RUST_LOG=debug cargo run
```

### 3. Span Guard 被立即释放

```rust
// ❌ 错误：临时变量立即释放
{
    span!(Level::INFO, "request").entered();  // ← Guard 立即被 drop
    info!("处理中");  // ← 不在 Span 内
}

// ✅ 正确：保存 Guard
{
    let _guard = span!(Level::INFO, "request").entered();
    info!("处理中");  // ← 在 Span 内
}
```

### 4. 过度日志影响性能

```rust
// ❌ 避免：循环内大量日志
for item in large_list {
    debug!("处理: {:?}", item);  // ← 可能有百万次调用
}

// ✅ 推荐：采样或汇总
let count = large_list.len();
debug!("处理 {} 个项目", count);
for (i, item) in large_list.iter().enumerate() {
    if i % 1000 == 0 {
        debug!("进度: {}/{}", i, count);
    }
}
```

---

## 参考资源

### 官方文档

- [log crate](https://docs.rs/log/) - 标准日志门面
- [env_logger](https://docs.rs/env_logger/) - 环境变量配置
- [tracing](https://docs.rs/tracing/) - 结构化追踪
- [tracing-subscriber](https://docs.rs/tracing-subscriber/) - 订阅者实现

### 教程

- [Tokio tracing 教程](https://tokio.rs/tokio/topics/tracing)
- [Rust 日志最佳实践](https://www.lpalmieri.com/posts/2020-09-27-zero-to-production-4-are-we-observable-yet/)

### 相关库

- [tracing-opentelemetry](https://docs.rs/tracing-opentelemetry/) - OpenTelemetry 集成
- [tracing-flame](https://docs.rs/tracing-flame/) - 火焰图生成
- [console-subscriber](https://docs.rs/console-subscriber/) - Tokio Console 支持

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**质量评分**: 96/100
