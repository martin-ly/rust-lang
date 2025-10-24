# Rust 必备库字母索引 (2025)

> **快速查找**: 按字母顺序查找所有 Rust 必备库  
> **更新日期**: 2025-10-20 | **基于**: Rust 1.90

---


## 📊 目录

- [📋 目录](#目录)
- [🔍 使用说明](#使用说明)
  - [如何使用本索引](#如何使用本索引)
  - [成熟度评级说明](#成熟度评级说明)
- [A](#a)
  - [anyhow](#anyhow)
  - [argon2](#argon2)
  - [async-nats](#async-nats)
  - [async-std](#async-std)
  - [async-trait](#async-trait)
  - [axum](#axum)
- [B](#b)
  - [bevy](#bevy)
  - [bincode](#bincode)
  - [bytes](#bytes)
- [C](#c)
  - [cached](#cached)
  - [chrono](#chrono)
  - [clap](#clap)
  - [colored](#colored)
  - [criterion](#criterion)
  - [crossbeam](#crossbeam)
- [D](#d)
  - [dashmap](#dashmap)
  - [diesel](#diesel)
- [E](#e)
  - [egui](#egui)
- [F](#f)
  - [flume](#flume)
  - [futures](#futures)
- [G](#g)
  - [getrandom](#getrandom)
- [H](#h)
  - [hyper](#hyper)
- [I](#i)
  - [indicatif](#indicatif)
- [J](#j)
  - [jsonwebtoken](#jsonwebtoken)
  - [juniper](#juniper)
- [K](#k)
  - [kani](#kani)
- [L](#l)
  - [lapin](#lapin)
  - [log](#log)
- [M](#m)
  - [moka](#moka)
  - [mockall](#mockall)
- [N](#n)
  - [ndarray](#ndarray)
- [O](#o)
  - [oauth2](#oauth2)
- [P](#p)
  - [parking_lot](#parking_lot)
  - [polars](#polars)
  - [proptest](#proptest)
- [Q](#q)
  - [quinn](#quinn)
- [R](#r)
  - [rand](#rand)
  - [rayon](#rayon)
  - [rdkafka](#rdkafka)
  - [redis](#redis)
  - [regex](#regex)
  - [reqwest](#reqwest)
  - [ring](#ring)
  - [rocket](#rocket)
  - [rustls](#rustls)
- [S](#s)
  - [sea-orm](#sea-orm)
  - [serde](#serde)
  - [serde_json](#serde_json)
  - [smol](#smol)
  - [sqlx](#sqlx)
- [T](#t)
  - [tauri](#tauri)
  - [tera](#tera)
  - [thiserror](#thiserror)
  - [time](#time)
  - [tokio](#tokio)
  - [tokio-tungstenite](#tokio-tungstenite)
  - [tonic](#tonic)
  - [toml](#toml)
  - [tower](#tower)
  - [tracing](#tracing)
- [U](#u)
  - [uuid](#uuid)
- [V](#v)
  - [validator](#validator)
- [W](#w)
  - [wasm-bindgen](#wasm-bindgen)
- [X](#x)
- [Y](#y)
  - [yew](#yew)
- [Z](#z)
- [📚 相关资源](#相关资源)
  - [文档导航](#文档导航)
  - [学习资源](#学习资源)
  - [外部链接](#外部链接)
- [🤝 贡献指南](#贡献指南)
  - [如何贡献](#如何贡献)
  - [评级标准](#评级标准)
- [📝 更新记录](#更新记录)
  - [2025-10-20](#2025-10-20)
- [📄 许可证](#许可证)


## 📋 目录

[A](#a) | [B](#b) | [C](#c) | [D](#d) | [E](#e) | [F](#f) | [G](#g) | [H](#h) | [I](#i) | [J](#j) | [K](#k) | [L](#l) | [M](#m) | [N](#n) | [O](#o) | [P](#p) | [Q](#q) | [R](#r) | [S](#s) | [T](#t) | [U](#u) | [V](#v) | [W](#w) | [X](#x) | [Y](#y) | [Z](#z)

---

## 🔍 使用说明

### 如何使用本索引

1. **快速查找**: 点击上方字母跳转到对应章节
2. **查看详情**: 每个库都有详细的用途说明、版本信息和成熟度评级
3. **深入学习**: 点击文档链接查看完整使用指南
4. **技术选型**: 参考成熟度评级（⭐1-5）选择合适的库

### 成熟度评级说明

- ⭐⭐⭐⭐⭐ - 生产就绪，生态成熟，广泛使用
- ⭐⭐⭐⭐ - 稳定可靠，适合生产使用
- ⭐⭐⭐ - 功能完整，仍在快速发展
- ⭐⭐ - 可用但有限制，需谨慎评估
- ⭐ - 实验性质，不建议生产使用

---

## A

### anyhow

- **用途**: 应用程序错误处理，提供灵活的错误类型和上下文
- **crates.io**: [anyhow](https://crates.io/crates/anyhow)
- **版本**: 1.0.89+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 错误处理
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#错误处理)
- **关键特性**:
  - 简化错误传播 (`?` 操作符)
  - 支持错误上下文
  - 零成本抽象
  - 兼容所有实现 `std::error::Error` 的类型

**快速示例**:

```rust
use anyhow::{Context, Result};

fn read_config() -> Result<String> {
    std::fs::read_to_string("config.toml")
        .context("Failed to read config file")?;
    Ok(config)
}
```

---

### argon2

- **用途**: 密码哈希，抵抗 GPU 和 ASIC 攻击
- **crates.io**: [argon2](https://crates.io/crates/argon2)
- **版本**: 0.5+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 密码学与安全
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#密码学与安全)
- **关键特性**:
  - Argon2id 算法（推荐）
  - 抗时间-内存权衡攻击
  - OWASP 推荐的密码哈希算法
  - 内存困难和计算困难

**快速示例**:

```rust
use argon2::{Argon2, PasswordHasher, PasswordVerifier};

let password = b"hunter42";
let argon2 = Argon2::default();
let password_hash = argon2.hash_password(password, &salt)?;
```

---

### async-nats

- **用途**: NATS 消息队列客户端，支持 JetStream
- **crates.io**: [async-nats](https://crates.io/crates/async-nats)
- **版本**: 0.35+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 消息队列
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#消息队列与流处理)
- **关键特性**:
  - 异步客户端
  - JetStream 持久化支持
  - 请求-响应模式
  - 自动重连机制

**快速示例**:

```rust
use async_nats::Client;

let client = async_nats::connect("nats://localhost:4222").await?;
client.publish("subject", "Hello NATS".into()).await?;
```

---

### async-std

- **用途**: 异步运行时，提供与标准库类似的 API
- **crates.io**: [async-std](https://crates.io/crates/async-std)
- **版本**: 1.12+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 异步运行时
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#异步运行时)
- **关键特性**:
  - 类似标准库的 API 设计
  - 内置任务调度器
  - 跨平台支持
  - 易于学习

**快速示例**:

```rust
use async_std::task;

async fn hello() {
    println!("Hello, async-std!");
}

task::block_on(hello());
```

---

### async-trait

- **用途**: 为 trait 添加异步方法支持
- **crates.io**: [async-trait](https://crates.io/crates/async-trait)
- **版本**: 0.1+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 异步编程工具
- **文档**: [详细指南](../RUST_CRATES_CLASSIFICATION_2025.md#异步与并发)
- **关键特性**:
  - 简化异步 trait 定义
  - 自动处理 `Box<dyn Future>`
  - 零运行时开销
  - 广泛使用

**快速示例**:

```rust
use async_trait::async_trait;

#[async_trait]
trait Repository {
    async fn find_user(&self, id: u64) -> Option<User>;
}
```

---

### axum

- **用途**: Web 框架，基于 Tower 生态
- **crates.io**: [axum](https://crates.io/crates/axum)
- **版本**: 0.7+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: Web 框架
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#web-框架)
- **关键特性**:
  - 类型安全的路由提取
  - 基于 Tokio 和 Hyper
  - 强大的中间件系统
  - 优秀的错误处理

**快速示例**:

```rust
use axum::{Router, routing::get};

let app = Router::new()
    .route("/", get(|| async { "Hello, World!" }));

axum::Server::bind(&"0.0.0.0:3000".parse()?)
    .serve(app.into_make_service())
    .await?;
```

---

## B

### bevy

- **用途**: 游戏引擎，基于 ECS 架构
- **crates.io**: [bevy](https://crates.io/crates/bevy)
- **版本**: 0.14+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 游戏开发
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#游戏开发) | [游戏开发指南](./guides/RUST_GAME_DEVELOPMENT_2025.md)
- **关键特性**:
  - 数据驱动的 ECS 架构
  - 模块化插件系统
  - 2D/3D 渲染支持
  - 快速迭代开发

**快速示例**:

```rust
use bevy::prelude::*;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Startup, setup)
        .run();
}
```

---

### bincode

- **用途**: 二进制序列化，高性能、紧凑格式
- **crates.io**: [bincode](https://crates.io/crates/bincode)
- **版本**: 1.3+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 序列化
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#序列化与数据格式)
- **关键特性**:
  - 极致的性能
  - 紧凑的二进制格式
  - Serde 集成
  - 适合网络传输和存储

**快速示例**:

```rust
use bincode::{serialize, deserialize};

let encoded: Vec<u8> = serialize(&my_struct)?;
let decoded: MyStruct = deserialize(&encoded[..])?;
```

---

### bytes

- **用途**: 字节缓冲区，零拷贝操作
- **crates.io**: [bytes](https://crates.io/crates/bytes)
- **版本**: 1.7+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 内存管理
- **文档**: [详细指南](../RUST_CRATES_CLASSIFICATION_2025.md#内存管理)
- **关键特性**:
  - 引用计数的字节缓冲区
  - 零拷贝切片操作
  - 网络编程核心库
  - Tokio 生态标准

**快速示例**:

```rust
use bytes::{Bytes, BytesMut, BufMut};

let mut buf = BytesMut::with_capacity(1024);
buf.put_slice(b"hello world");
let frozen = buf.freeze(); // 零拷贝转换
```

---

## C

### cached

- **用途**: 内存缓存，支持多种缓存策略
- **crates.io**: [cached](https://crates.io/crates/cached)
- **版本**: 0.53+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 缓存
- **文档**: [详细指南](./03_application_dev/caching/README.md)
- **关键特性**:
  - 过程宏缓存装饰器
  - LRU/FIFO/LFU 策略
  - 异步缓存支持
  - TTL 过期机制

**快速示例**:

```rust
use cached::proc_macro::cached;

#[cached]
fn expensive_operation(n: u32) -> u32 {
    // 计算密集型操作
    n * n
}
```

---

### chrono

- **用途**: 时间日期处理，功能全面
- **crates.io**: [chrono](https://crates.io/crates/chrono)
- **版本**: 0.4+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 时间处理
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#核心基础库)
- **关键特性**:
  - 时区支持（Tz）
  - 时间算术运算
  - 格式化和解析
  - 与标准库兼容

**快速示例**:

```rust
use chrono::{DateTime, Utc, Local};

let now = Utc::now();
let formatted = now.format("%Y-%m-%d %H:%M:%S");
println!("Current time: {}", formatted);
```

---

### clap

- **用途**: CLI 参数解析，derive 宏支持
- **crates.io**: [clap](https://crates.io/crates/clap)
- **版本**: 4.5+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 命令行工具
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#命令行工具) | [CLI 开发指南](./guides/RUST_CLI_DEVELOPMENT_2025.md)
- **关键特性**:
  - Derive 宏简化定义
  - 自动生成帮助信息
  - 子命令支持
  - 完善的验证机制

**快速示例**:

```rust
use clap::Parser;

#[derive(Parser)]
struct Cli {
    #[arg(short, long)]
    name: String,
}

let cli = Cli::parse();
println!("Hello, {}!", cli.name);
```

---

### colored

- **用途**: 终端彩色输出
- **crates.io**: [colored](https://crates.io/crates/colored)
- **版本**: 2.1+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 命令行工具
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#命令行工具)
- **关键特性**:
  - 简洁的 API
  - 跨平台支持
  - 样式组合（粗体、斜体等）
  - 自动检测终端能力

**快速示例**:

```rust
use colored::Colorize;

println!("{}", "Error!".red().bold());
println!("{}", "Success!".green());
```

---

### criterion

- **用途**: 基准测试，统计分析
- **crates.io**: [criterion](https://crates.io/crates/criterion)
- **版本**: 0.5+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 测试工具
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#测试工具) | [测试策略指南](./guides/RUST_TESTING_STRATEGY_2025.md)
- **关键特性**:
  - 统计严谨的基准测试
  - 自动生成报告
  - 性能回归检测
  - HTML 可视化

**快速示例**:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, fibonacci_benchmark);
criterion_main!(benches);
```

---

### crossbeam

- **用途**: 并发数据结构和工具
- **crates.io**: [crossbeam](https://crates.io/crates/crossbeam)
- **版本**: 0.8+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 并发编程
- **文档**: [详细指南](../RUST_CRATES_CLASSIFICATION_2025.md#并发编程) | [并发编程指南](./guides/RUST_CONCURRENCY_PROGRAMMING_2025.md)
- **关键特性**:
  - 高性能通道（channel）
  - 无锁数据结构
  - 作用域线程
  - 内存回收（epoch-based）

**快速示例**:

```rust
use crossbeam::channel::{bounded, unbounded};

let (tx, rx) = unbounded();
tx.send(42).unwrap();
assert_eq!(rx.recv(), Ok(42));
```

---

## D

### dashmap

- **用途**: 并发哈希表
- **crates.io**: [dashmap](https://crates.io/crates/dashmap)
- **版本**: 6.1+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 并发数据结构
- **文档**: [详细指南](./02_system_programming/concurrency/README.md)
- **关键特性**:
  - 细粒度锁（sharded locking）
  - 高并发性能
  - 兼容 `std::collections::HashMap` API
  - 读操作近乎无锁

**快速示例**:

```rust
use dashmap::DashMap;

let map = DashMap::new();
map.insert("key", "value");
let value = map.get("key").unwrap();
```

---

### diesel

- **用途**: ORM 框架，编译时类型检查
- **crates.io**: [diesel](https://crates.io/crates/diesel)
- **版本**: 2.2+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 数据库 ORM
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#数据库访问) | [数据库编程指南](./guides/RUST_DATABASE_PROGRAMMING_2025.md)
- **关键特性**:
  - 编译时 SQL 验证
  - 类型安全的查询构建器
  - 迁移管理
  - PostgreSQL、MySQL、SQLite 支持

**快速示例**:

```rust
use diesel::prelude::*;

let results = users
    .filter(published.eq(true))
    .limit(5)
    .load::<User>(&mut conn)?;
```

---

## E

### egui

- **用途**: 即时模式 GUI 库
- **crates.io**: [egui](https://crates.io/crates/egui)
- **版本**: 0.28+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: GUI 开发
- **文档**: [详细指南](./04_domain_specific/gui/README.md)
- **关键特性**:
  - 即时模式（Immediate Mode）
  - 纯 Rust 实现
  - 跨平台（Web、Desktop）
  - 易于集成

**快速示例**:

```rust
use eframe::egui;

egui::CentralPanel::default().show(ctx, |ui| {
    ui.heading("My App");
    if ui.button("Click me!").clicked() {
        println!("Button clicked!");
    }
});
```

---

## F

### flume

- **用途**: 高性能 MPMC 通道
- **crates.io**: [flume](https://crates.io/crates/flume)
- **版本**: 0.11+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 并发通信
- **文档**: [详细指南](./02_system_programming/channels/README.md)
- **关键特性**:
  - 多生产者多消费者（MPMC）
  - 优于标准库性能
  - 异步和同步两种 API
  - 无限/有界通道

**快速示例**:

```rust
use flume::unbounded;

let (tx, rx) = unbounded();
tx.send(42).unwrap();
assert_eq!(rx.recv(), Ok(42));
```

---

### futures

- **用途**: 异步编程工具集
- **crates.io**: [futures](https://crates.io/crates/futures)
- **版本**: 0.3+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 异步编程
- **文档**: [详细指南](../RUST_CRATES_CLASSIFICATION_2025.md#异步与并发) | [异步编程指南](./guides/RUST_ASYNC_PROGRAMMING_2025.md)
- **关键特性**:
  - Future 组合子
  - Stream 和 Sink 抽象
  - 跨运行时兼容
  - 核心异步生态

**快速示例**:

```rust
use futures::future::{join, select};

let result = join(async_op1(), async_op2()).await;
```

---

## G

### getrandom

- **用途**: 跨平台随机数生成器
- **crates.io**: [getrandom](https://crates.io/crates/getrandom)
- **版本**: 0.2+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 随机数
- **文档**: [详细指南](./01_infrastructure/random/README.md)
- **关键特性**:
  - 调用系统 CSPRNG
  - 最小依赖
  - `no_std` 支持
  - `rand` 的底层依赖

**快速示例**:

```rust
use getrandom::getrandom;

let mut buf = [0u8; 32];
getrandom(&mut buf)?;
```

---

## H

### hyper

- **用途**: HTTP 底层库
- **crates.io**: [hyper](https://crates.io/crates/hyper)
- **版本**: 1.4+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: HTTP
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#http-客户端与服务器) | [网络编程指南](./guides/RUST_NETWORK_PROGRAMMING_2025.md)
- **关键特性**:
  - HTTP/1、HTTP/2、HTTP/3 支持
  - 高性能异步实现
  - Tokio 生态核心
  - 低级控制和灵活性

**快速示例**:

```rust
use hyper::{Body, Request, Response, Server};

let service = make_service_fn(|_conn| async {
    Ok::<_, Infallible>(service_fn(hello))
});

Server::bind(&([127, 0, 0, 1], 3000).into())
    .serve(service)
    .await?;
```

---

## I

### indicatif

- **用途**: 进度条和加载动画
- **crates.io**: [indicatif](https://crates.io/crates/indicatif)
- **版本**: 0.17+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 命令行工具
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#命令行工具)
- **关键特性**:
  - 多种进度条样式
  - 并行进度条
  - ETA 计算
  - 美观的终端输出

**快速示例**:

```rust
use indicatif::ProgressBar;

let pb = ProgressBar::new(100);
for i in 0..100 {
    pb.inc(1);
    // 执行工作
}
pb.finish_with_message("完成!");
```

---

## J

### jsonwebtoken

- **用途**: JWT 认证令牌
- **crates.io**: [jsonwebtoken](https://crates.io/crates/jsonwebtoken)
- **版本**: 9.3+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 认证授权
- **文档**: [详细指南](./cross_cutting/authentication/README.md) | [安全编程指南](./guides/RUST_SECURITY_PROGRAMMING_2025.md)
- **关键特性**:
  - JWT 编码/解码
  - 多种签名算法（HS256、RS256 等）
  - Claims 验证
  - 安全实现

**快速示例**:

```rust
use jsonwebtoken::{encode, decode, Header, Validation};

let token = encode(&Header::default(), &my_claims, &key)?;
let token_data = decode::<Claims>(&token, &key, &Validation::default())?;
```

---

### juniper

- **用途**: GraphQL 服务器
- **crates.io**: [juniper](https://crates.io/crates/juniper)
- **版本**: 0.16+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: Web API
- **文档**: [详细指南](./03_application_dev/graphql/README.md)
- **关键特性**:
  - 类型安全的 GraphQL
  - 过程宏定义 Schema
  - 与 Web 框架集成
  - 订阅（Subscriptions）支持

**快速示例**:

```rust
use juniper::{GraphQLObject, EmptySubscription, RootNode};

#[derive(GraphQLObject)]
struct User {
    id: i32,
    name: String,
}
```

---

## K

### kani

- **用途**: 形式化验证工具
- **crates.io**: [kani-verifier](https://crates.io/crates/kani-verifier)
- **版本**: 0.54+
- **成熟度**: ⭐⭐⭐
- **类别**: 验证工具
- **文档**: [详细指南](../../c13_reliability/docs/advanced/formal-verification.md)
- **关键特性**:
  - 基于 CBMC 的模型检查
  - 证明代码正确性
  - 未定义行为检测
  - AWS 官方支持

**快速示例**:

```rust
#[kani::proof]
fn verify_addition() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    if let Some(sum) = a.checked_add(b) {
        assert!(sum >= a && sum >= b);
    }
}
```

---

## L

### lapin

- **用途**: RabbitMQ 客户端
- **crates.io**: [lapin](https://crates.io/crates/lapin)
- **版本**: 2.5+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 消息队列
- **文档**: [详细指南](./03_application_dev/message_queues/README.md)
- **关键特性**:
  - 完整 AMQP 0.9.1 实现
  - 异步 API
  - 连接管理和重连
  - 确认和事务支持

**快速示例**:

```rust
use lapin::{Connection, ConnectionProperties, options::*};

let conn = Connection::connect("amqp://localhost", ConnectionProperties::default()).await?;
let channel = conn.create_channel().await?;
channel.basic_publish("", "my_queue", BasicPublishOptions::default(), b"hello", BasicProperties::default()).await?;
```

---

### log

- **用途**: 日志门面（Facade）
- **crates.io**: [log](https://crates.io/crates/log)
- **版本**: 0.4+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 日志
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#日志记录)
- **关键特性**:
  - 标准日志门面
  - 五级日志（trace、debug、info、warn、error）
  - 与多种日志后端兼容
  - 零依赖

**快速示例**:

```rust
use log::{info, warn, error};

info!("Application started");
warn!("Low memory warning");
error!("Failed to connect: {}", err);
```

---

## M

### moka

- **用途**: 高性能缓存库
- **crates.io**: [moka](https://crates.io/crates/moka)
- **版本**: 0.12+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 缓存
- **文档**: [详细指南](./03_application_dev/caching/README.md)
- **关键特性**:
  - 基于 Caffeine 算法
  - 异步和同步 API
  - TinyLFU 驱逐策略
  - TTL/TTI 支持

**快速示例**:

```rust
use moka::sync::Cache;

let cache: Cache<String, String> = Cache::new(10_000);
cache.insert("key".to_string(), "value".to_string());
let value = cache.get(&"key".to_string());
```

---

### mockall

- **用途**: Mock 测试框架
- **crates.io**: [mockall](https://crates.io/crates/mockall)
- **版本**: 0.13+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 测试工具
- **文档**: [详细指南](./05_toolchain/testing/README.md) | [测试策略指南](./guides/RUST_TESTING_STRATEGY_2025.md)
- **关键特性**:
  - 自动生成 Mock 对象
  - 行为验证
  - 返回值设置
  - 调用次数断言

**快速示例**:

```rust
use mockall::*;

#[automock]
trait Database {
    fn get_user(&self, id: u64) -> Option<User>;
}

let mut mock = MockDatabase::new();
mock.expect_get_user()
    .with(eq(42))
    .times(1)
    .returning(|_| Some(User::default()));
```

---

## N

### ndarray

- **用途**: N 维数组，科学计算
- **crates.io**: [ndarray](https://crates.io/crates/ndarray)
- **版本**: 0.15+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 科学计算
- **文档**: [详细指南](./04_domain_specific/scientific/README.md)
- **关键特性**:
  - NumPy 风格 API
  - 切片和视图（零拷贝）
  - BLAS/LAPACK 集成
  - 泛型元素类型

**快速示例**:

```rust
use ndarray::array;

let a = array![[1, 2, 3],
               [4, 5, 6]];
let sum = a.sum();
```

---

## O

### oauth2

- **用途**: OAuth2 认证客户端
- **crates.io**: [oauth2](https://crates.io/crates/oauth2)
- **版本**: 4.4+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 认证授权
- **文档**: [详细指南](./cross_cutting/authentication/README.md)
- **关键特性**:
  - OAuth 2.0 完整实现
  - 授权码流程
  - 客户端凭据流程
  - PKCE 支持

**快速示例**:

```rust
use oauth2::{AuthorizationCode, TokenResponse};

let token = client
    .exchange_code(AuthorizationCode::new(code))
    .request_async(async_http_client)
    .await?;
```

---

## P

### parking_lot

- **用途**: 高性能同步原语
- **crates.io**: [parking_lot](https://crates.io/crates/parking_lot)
- **版本**: 0.12+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 并发编程
- **文档**: [详细指南](../RUST_CRATES_CLASSIFICATION_2025.md#并发编程) | [并发编程指南](./guides/RUST_CONCURRENCY_PROGRAMMING_2025.md)
- **关键特性**:
  - 比标准库更快的 `Mutex` 和 `RwLock`
  - 公平锁选项
  - 零开销（小内存占用）
  - Drop-in 替换标准库

**快速示例**:

```rust
use parking_lot::Mutex;

let data = Mutex::new(0);
*data.lock() += 1;
```

---

### polars

- **用途**: 数据处理框架（类 Pandas）
- **crates.io**: [polars](https://crates.io/crates/polars)
- **版本**: 0.41+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 数据处理
- **文档**: [详细指南](./04_domain_specific/scientific/README.md)
- **关键特性**:
  - 极致性能（Apache Arrow）
  - 惰性求值
  - 并行执行
  - Pandas 风格 API

**快速示例**:

```rust
use polars::prelude::*;

let df = df! {
    "a" => &[1, 2, 3],
    "b" => &["x", "y", "z"],
}?;
```

---

### proptest

- **用途**: 属性测试（Property-based Testing）
- **crates.io**: [proptest](https://crates.io/crates/proptest)
- **版本**: 1.5+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 测试工具
- **文档**: [详细指南](./05_toolchain/testing/README.md)
- **关键特性**:
  - 自动生成测试用例
  - 反例缩减（Shrinking）
  - 可重现的随机测试
  - 丰富的策略（Strategy）

**快速示例**:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_reversing_twice(ref s in ".*") {
        let reversed: String = s.chars().rev().collect();
        let double_reversed: String = reversed.chars().rev().collect();
        prop_assert_eq!(s, &double_reversed);
    }
}
```

---

## Q

### quinn

- **用途**: QUIC 协议实现
- **crates.io**: [quinn](https://crates.io/crates/quinn)
- **版本**: 0.11+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 网络协议
- **文档**: [详细指南](./02_system_programming/networking/README.md) | [网络编程指南](./guides/RUST_NETWORK_PROGRAMMING_2025.md)
- **关键特性**:
  - 纯 Rust QUIC 实现
  - 基于 Tokio
  - HTTP/3 基础
  - 低延迟、多路复用

**快速示例**:

```rust
use quinn::{Endpoint, ServerConfig};

let endpoint = Endpoint::server(server_config, addr)?;
let incoming = endpoint.accept().await.unwrap();
let conn = incoming.await?;
```

---

## R

### rand

- **用途**: 随机数生成，灵活且强大
- **crates.io**: [rand](https://crates.io/crates/rand)
- **版本**: 0.8+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 随机数
- **文档**: [详细指南](./01_infrastructure/random/README.md)
- **关键特性**:
  - 多种随机数生成器（RNG）
  - 分布采样（正态分布、均匀分布等）
  - 加密安全 RNG（OsRng）
  - 可重现随机序列

**快速示例**:

```rust
use rand::Rng;

let mut rng = rand::thread_rng();
let n: u32 = rng.gen_range(0..100);
```

---

### rayon

- **用途**: 数据并行库
- **crates.io**: [rayon](https://crates.io/crates/rayon)
- **版本**: 1.10+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 并发编程
- **文档**: [详细指南](../RUST_CRATES_CLASSIFICATION_2025.md#并发编程) | [并发编程指南](./guides/RUST_CONCURRENCY_PROGRAMMING_2025.md)
- **关键特性**:
  - 并行迭代器
  - 工作窃取调度器
  - 自动负载均衡
  - 零配置并行化

**快速示例**:

```rust
use rayon::prelude::*;

let sum: i32 = (1..1000)
    .into_par_iter()
    .map(|x| x * x)
    .sum();
```

---

### rdkafka

- **用途**: Kafka 客户端
- **crates.io**: [rdkafka](https://crates.io/crates/rdkafka)
- **版本**: 0.36+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 消息队列
- **文档**: [详细指南](./03_application_dev/message_queues/README.md)
- **关键特性**:
  - 基于 librdkafka
  - 高性能、低延迟
  - 完整的 Kafka 协议支持
  - 生产者、消费者、流处理

**快速示例**:

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};

let producer: FutureProducer = ClientConfig::new()
    .set("bootstrap.servers", "localhost:9092")
    .create()?;

producer.send(
    FutureRecord::to("my-topic").payload("message").key("key"),
    Duration::from_secs(0),
).await?;
```

---

### redis

- **用途**: Redis 客户端
- **crates.io**: [redis](https://crates.io/crates/redis)
- **版本**: 0.26+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 数据库客户端
- **文档**: [详细指南](./03_application_dev/caching/README.md)
- **关键特性**:
  - 同步和异步 API
  - 连接池
  - 集群支持
  - Redis 协议完整实现

**快速示例**:

```rust
use redis::Commands;

let client = redis::Client::open("redis://127.0.0.1/")?;
let mut con = client.get_connection()?;
con.set("my_key", "value")?;
let value: String = con.get("my_key")?;
```

---

### regex

- **用途**: 正则表达式引擎
- **crates.io**: [regex](https://crates.io/crates/regex)
- **版本**: 1.10+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 文本处理
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#核心基础库)
- **关键特性**:
  - 线性时间复杂度（不会回溯）
  - Unicode 支持
  - 编译时优化
  - 线程安全

**快速示例**:

```rust
use regex::Regex;

let re = Regex::new(r"^\d{4}-\d{2}-\d{2}$")?;
assert!(re.is_match("2025-10-20"));
```

---

### reqwest

- **用途**: HTTP 客户端，易用且功能全面
- **crates.io**: [reqwest](https://crates.io/crates/reqwest)
- **版本**: 0.12+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: HTTP 客户端
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#http-客户端与服务器) | [网络编程指南](./guides/RUST_NETWORK_PROGRAMMING_2025.md)
- **关键特性**:
  - 异步和同步 API
  - JSON 支持
  - Cookie 管理
  - 中间件和拦截器

**快速示例**:

```rust
use reqwest;

let body = reqwest::get("https://api.example.com/data")
    .await?
    .text()
    .await?;
```

---

### ring

- **用途**: 加密库，安全且高性能
- **crates.io**: [ring](https://crates.io/crates/ring)
- **版本**: 0.17+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 密码学
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#密码学与安全) | [安全编程指南](./guides/RUST_SECURITY_PROGRAMMING_2025.md)
- **关键特性**:
  - 基于 BoringSSL（Google）
  - 现代加密算法
  - 常量时间操作
  - 高性能

**快速示例**:

```rust
use ring::digest::{digest, SHA256};

let hash = digest(&SHA256, b"hello world");
```

---

### rocket

- **用途**: Web 框架，类型安全
- **crates.io**: [rocket](https://crates.io/crates/rocket)
- **版本**: 0.5+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: Web 框架
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#web-框架)
- **关键特性**:
  - 类型安全的路由
  - 请求保护（Guards）
  - 自动 JSON 序列化
  - 优雅的宏 API

**快速示例**:

```rust
#[macro_use] extern crate rocket;

#[get("/")]
fn index() -> &'static str {
    "Hello, world!"
}

#[launch]
fn rocket() -> _ {
    rocket::build().mount("/", routes![index])
}
```

---

### rustls

- **用途**: TLS 协议实现，纯 Rust
- **crates.io**: [rustls](https://crates.io/crates/rustls)
- **版本**: 0.23+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 网络安全
- **文档**: [详细指南](./cross_cutting/security/README.md) | [安全编程指南](./guides/RUST_SECURITY_PROGRAMMING_2025.md)
- **关键特性**:
  - 纯 Rust TLS 实现
  - 现代密码套件
  - 无内存不安全代码
  - 高性能

**快速示例**:

```rust
use rustls::{ClientConfig, RootCertStore};

let mut root_store = RootCertStore::empty();
root_store.add_server_trust_anchors(webpki_roots::TLS_SERVER_ROOTS.0.iter().map(|ta| {
    OwnedTrustAnchor::from_subject_spki_name_constraints(
        ta.subject, ta.spki, ta.name_constraints,
    )
}));
let config = ClientConfig::builder()
    .with_safe_defaults()
    .with_root_certificates(root_store)
    .with_no_client_auth();
```

---

## S

### sea-orm

- **用途**: 异步 ORM 框架
- **crates.io**: [sea-orm](https://crates.io/crates/sea-orm)
- **版本**: 1.0+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 数据库 ORM
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#数据库访问) | [数据库编程指南](./guides/RUST_DATABASE_PROGRAMMING_2025.md)
- **关键特性**:
  - 异步优先设计
  - 关系映射
  - 迁移管理
  - PostgreSQL、MySQL、SQLite 支持

**快速示例**:

```rust
use sea_orm::*;

let users: Vec<user::Model> = User::find()
    .filter(user::Column::Status.eq("active"))
    .all(&db)
    .await?;
```

---

### serde

- **用途**: 序列化/反序列化框架
- **crates.io**: [serde](https://crates.io/crates/serde)
- **版本**: 1.0+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 序列化
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#序列化与数据格式)
- **关键特性**:
  - 零成本抽象
  - 数据格式无关
  - Derive 宏支持
  - 生态标准

**快速示例**:

```rust
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct User {
    name: String,
    age: u32,
}
```

---

### serde_json

- **用途**: JSON 序列化/反序列化
- **crates.io**: [serde_json](https://crates.io/crates/serde_json)
- **版本**: 1.0+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 序列化
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#序列化与数据格式)
- **关键特性**:
  - 高性能 JSON 解析
  - 类型安全
  - 流式解析
  - 漂亮打印

**快速示例**:

```rust
use serde_json::{json, Value};

let data = json!({
    "name": "John",
    "age": 30,
});
```

---

### smol

- **用途**: 轻量级异步运行时
- **crates.io**: [smol](https://crates.io/crates/smol)
- **版本**: 2.0+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 异步运行时
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#异步运行时) | [异步编程指南](./guides/RUST_ASYNC_PROGRAMMING_2025.md)
- **关键特性**:
  - 极简设计
  - 低内存占用
  - 与 async-std 兼容
  - 模块化组件

**快速示例**:

```rust
use smol;

smol::block_on(async {
    println!("Hello from smol!");
});
```

---

### sqlx

- **用途**: 异步 SQL 驱动，编译时验证
- **crates.io**: [sqlx](https://crates.io/crates/sqlx)
- **版本**: 0.8+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 数据库驱动
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#数据库访问) | [数据库编程指南](./guides/RUST_DATABASE_PROGRAMMING_2025.md)
- **关键特性**:
  - 编译时 SQL 验证
  - 异步原生支持
  - 连接池
  - PostgreSQL、MySQL、SQLite 支持

**快速示例**:

```rust
use sqlx::postgres::PgPoolOptions;

let pool = PgPoolOptions::new()
    .max_connections(5)
    .connect("postgres://localhost/mydb").await?;

let row: (i64,) = sqlx::query_as("SELECT $1")
    .bind(150_i64)
    .fetch_one(&pool).await?;
```

---

## T

### tauri

- **用途**: 桌面应用框架
- **crates.io**: [tauri](https://crates.io/crates/tauri)
- **版本**: 2.0+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: GUI 开发
- **文档**: [详细指南](./04_domain_specific/gui/README.md)
- **关键特性**:
  - 基于 Web 技术的 UI
  - Rust 后端
  - 小体积（<5MB）
  - 跨平台（Windows、macOS、Linux）

**快速示例**:

```rust
#[tauri::command]
fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

tauri::Builder::default()
    .invoke_handler(tauri::generate_handler![greet])
    .run(tauri::generate_context!())
    .expect("error while running tauri application");
```

---

### tera

- **用途**: 模板引擎，类 Jinja2
- **crates.io**: [tera](https://crates.io/crates/tera)
- **版本**: 1.20+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 模板引擎
- **文档**: [详细指南](./03_application_dev/template/README.md)
- **关键特性**:
  - Jinja2 风格语法
  - 模板继承
  - 自定义过滤器和函数
  - 自动转义

**快速示例**:

```rust
use tera::{Tera, Context};

let tera = Tera::new("templates/**/*")?;
let mut context = Context::new();
context.insert("name", "John");
let rendered = tera.render("hello.html", &context)?;
```

---

### thiserror

- **用途**: 自定义错误类型，derive 宏
- **crates.io**: [thiserror](https://crates.io/crates/thiserror)
- **版本**: 1.0+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 错误处理
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#错误处理)
- **关键特性**:
  - Derive 宏自动实现 `Error` trait
  - 源错误链（source chain）
  - 灵活的错误消息
  - 零运行时开销

**快速示例**:

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MyError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Parse error: {0}")]
    Parse(String),
}
```

---

### time

- **用途**: 时间处理，安全设计
- **crates.io**: [time](https://crates.io/crates/time)
- **版本**: 0.3+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 时间处理
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#核心基础库)
- **关键特性**:
  - 类型安全的 API
  - 无 panic 设计
  - 时区支持
  - 格式化和解析

**快速示例**:

```rust
use time::{OffsetDateTime, macros::format_description};

let now = OffsetDateTime::now_utc();
let format = format_description!("[year]-[month]-[day]");
let formatted = now.format(&format)?;
```

---

### tokio

- **用途**: 异步运行时，生态核心
- **crates.io**: [tokio](https://crates.io/crates/tokio)
- **版本**: 1.40+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 异步运行时
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#异步运行时) | [异步编程指南](./guides/RUST_ASYNC_PROGRAMMING_2025.md)
- **关键特性**:
  - 工作窃取调度器
  - 异步 I/O
  - 定时器和超时
  - 丰富的生态系统

**快速示例**:

```rust
use tokio;

#[tokio::main]
async fn main() {
    println!("Hello, Tokio!");
}
```

---

### tokio-tungstenite

- **用途**: WebSocket 客户端/服务器
- **crates.io**: [tokio-tungstenite](https://crates.io/crates/tokio-tungstenite)
- **版本**: 0.23+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: WebSocket
- **文档**: [详细指南](./03_application_dev/websocket/README.md)
- **关键特性**:
  - 基于 Tokio
  - 客户端和服务器支持
  - TLS 支持
  - 压缩扩展

**快速示例**:

```rust
use tokio_tungstenite::{connect_async, tungstenite::Message};

let (ws_stream, _) = connect_async("ws://localhost:8080").await?;
let (mut write, mut read) = ws_stream.split();
write.send(Message::Text("Hello WebSocket!".into())).await?;
```

---

### tonic

- **用途**: gRPC 框架
- **crates.io**: [tonic](https://crates.io/crates/tonic)
- **版本**: 0.12+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: RPC 框架
- **文档**: [详细指南](./03_application_dev/grpc/README.md)
- **关键特性**:
  - 基于 HTTP/2
  - 类型安全的 gRPC
  - 流式 RPC
  - 与 Protocol Buffers 集成

**快速示例**:

```rust
use tonic::{transport::Server, Request, Response, Status};

#[tonic::async_trait]
impl Greeter for MyGreeter {
    async fn say_hello(&self, request: Request<HelloRequest>) -> Result<Response<HelloReply>, Status> {
        Ok(Response::new(HelloReply {
            message: format!("Hello {}!", request.into_inner().name),
        }))
    }
}
```

---

### toml

- **用途**: TOML 格式解析和序列化
- **crates.io**: [toml](https://crates.io/crates/toml)
- **版本**: 0.8+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 序列化
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#序列化与数据格式)
- **关键特性**:
  - TOML 1.0 标准支持
  - Serde 集成
  - 保留注释和格式
  - 配置文件首选

**快速示例**:

```rust
use toml::Value;

let config: Value = toml::from_str(r#"
    [package]
    name = "myapp"
    version = "1.0.0"
"#)?;
```

---

### tower

- **用途**: 服务抽象和中间件
- **crates.io**: [tower](https://crates.io/crates/tower)
- **版本**: 0.4+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 服务抽象
- **文档**: [详细指南](./03_application_dev/middleware/README.md)
- **关键特性**:
  - `Service` trait 抽象
  - 可组合的中间件
  - 超时、重试、限流等
  - Hyper 和 Axum 的基础

**快速示例**:

```rust
use tower::{Service, ServiceBuilder};
use tower::limit::RateLimitLayer;

let service = ServiceBuilder::new()
    .rate_limit(50, Duration::from_secs(1))
    .service(my_service);
```

---

### tracing

- **用途**: 结构化日志和分布式追踪
- **crates.io**: [tracing](https://crates.io/crates/tracing)
- **版本**: 0.1+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 日志与追踪
- **文档**: [详细指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md#日志记录)
- **关键特性**:
  - 结构化日志
  - 跨度（Span）追踪
  - 异步友好
  - 丰富的生态（OpenTelemetry、Jaeger）

**快速示例**:

```rust
use tracing::{info, span, Level};

let span = span!(Level::INFO, "my_span");
let _enter = span.enter();
info!(user_id = 42, "User logged in");
```

---

## U

### uuid

- **用途**: UUID 生成和解析
- **crates.io**: [uuid](https://crates.io/crates/uuid)
- **版本**: 1.10+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: 工具库
- **文档**: [详细指南](./01_infrastructure/random/README.md)
- **关键特性**:
  - UUID v1/v4/v5 生成
  - Serde 支持
  - 零拷贝解析
  - 标准库兼容

**快速示例**:

```rust
use uuid::Uuid;

let id = Uuid::new_v4();
println!("Generated UUID: {}", id);
```

---

## V

### validator

- **用途**: 数据验证
- **crates.io**: [validator](https://crates.io/crates/validator)
- **版本**: 0.18+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 数据验证
- **文档**: [详细指南](./cross_cutting/validation/README.md)
- **关键特性**:
  - Derive 宏验证
  - 内置验证规则
  - 自定义验证器
  - 国际化支持

**快速示例**:

```rust
use validator::Validate;

#[derive(Validate)]
struct SignupData {
    #[validate(email)]
    email: String,
    
    #[validate(length(min = 8))]
    password: String,
}
```

---

## W

### wasm-bindgen

- **用途**: Rust 与 JavaScript 互操作
- **crates.io**: [wasm-bindgen](https://crates.io/crates/wasm-bindgen)
- **版本**: 0.2+
- **成熟度**: ⭐⭐⭐⭐⭐
- **类别**: WebAssembly
- **文档**: [详细指南](./04_domain_specific/wasm/README.md) | [WebAssembly 开发指南](./guides/RUST_WEBASSEMBLY_DEV_2025.md)
- **关键特性**:
  - Rust 和 JS 互操作
  - 自动生成绑定
  - Web API 访问
  - WASM 生态核心

**快速示例**:

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}
```

---

## X

暂无常用库

---

## Y

### yew

- **用途**: WebAssembly 前端框架
- **crates.io**: [yew](https://crates.io/crates/yew)
- **版本**: 0.21+
- **成熟度**: ⭐⭐⭐⭐
- **类别**: 前端框架
- **文档**: [详细指南](./04_domain_specific/wasm/README.md) | [WebAssembly 开发指南](./guides/RUST_WEBASSEMBLY_DEV_2025.md)
- **关键特性**:
  - 组件化开发
  - 虚拟 DOM
  - 类 React 设计
  - 纯 Rust 前端

**快速示例**:

```rust
use yew::prelude::*;

#[function_component(App)]
fn app() -> Html {
    html! {
        <h1>{"Hello Yew!"}</h1>
    }
}
```

---

## Z

暂无常用库

---

## 📚 相关资源

### 文档导航

- **[必备库指南](../RUST_ESSENTIAL_CRATES_GUIDE_2025.md)** - 详细使用说明和代码示例
- **[分类体系](../RUST_CRATES_CLASSIFICATION_2025.md)** - 按功能和场景分类
- **[成熟度评估](../RUST_CRATES_MATURITY_MATRIX_2025.md)** - 库的成熟度对比
- **[生态索引](../RUST_CRATES_ECOSYSTEM_INDEX_2025.md)** - 按功能快速查找

### 学习资源

- **[学习路径](./learning_paths/README.md)** - 系统化学习计划
- **[实战指南](./guides/)** - 15 个深度技术指南
- **[代码示例](./examples/)** - 实用代码片段
- **[基准测试](./benchmarks/)** - 性能对比数据

### 外部链接

- **[crates.io](https://crates.io/)** - Rust 官方包仓库
- **[lib.rs](https://lib.rs/)** - 社区驱动的包索引
- **[docs.rs](https://docs.rs/)** - 自动生成的文档
- **[Rust Book](https://doc.rust-lang.org/book/)** - Rust 官方教程

---

## 🤝 贡献指南

### 如何贡献

1. **更新库信息**: 提交 PR 更新版本号、成熟度评级
2. **添加新库**: 建议纳入新的必备库
3. **改进文档**: 修正错误、补充说明
4. **分享经验**: 提供使用案例和最佳实践

### 评级标准

我们的成熟度评级基于以下因素:

- **生态采用度**: 社区使用广泛程度
- **API 稳定性**: 版本迭代稳定性
- **文档质量**: 文档的完整性和易用性
- **维护活跃度**: GitHub 活跃度和问题响应速度
- **生产就绪**: 是否适合生产环境使用

---

## 📝 更新记录

### 2025-10-20

- ✅ 初始版本发布
- ✅ 收录 60+ 核心 Rust 库
- ✅ 完整的字母索引和快速查找
- ✅ 成熟度评级和使用说明
- ✅ 代码示例和文档链接

---

## 📄 许可证

本文档采用 [MIT License](../../LICENSE) 或 [Apache License 2.0](../../LICENSE-APACHE) 双重许可。

---

**最后更新**: 2025-10-20  
**维护者**: Rust 开源生态文档团队
