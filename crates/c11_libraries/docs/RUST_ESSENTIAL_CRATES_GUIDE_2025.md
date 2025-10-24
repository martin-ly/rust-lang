# Rust 必备开源库生态指南 (2025)

> **基于 Rust 1.90 版本** | **更新日期**: 2025-10-20  
> **目标**: 为 Rust 开发者提供全面、系统的开源库选择指南

---

## 📊 目录

- [Rust 必备开源库生态指南 (2025)](#rust-必备开源库生态指南-2025)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [概览](#概览)
    - [生态全景图](#生态全景图)
  - [核心基础库](#核心基础库)
    - [1. 序列化 - serde](#1-序列化---serde)
    - [2. 正则表达式 - regex](#2-正则表达式---regex)
    - [3. 随机数 - rand](#3-随机数---rand)
    - [4. 时间日期 - chrono / time](#4-时间日期---chrono--time)
  - [异步运行时](#异步运行时)
    - [1. tokio (主流选择)](#1-tokio-主流选择)
    - [2. async-std (简单易用)](#2-async-std-简单易用)
    - [3. smol (轻量高效)](#3-smol-轻量高效)
    - [异步运行时对比](#异步运行时对比)
  - [Web 框架](#web-框架)
    - [1. axum (现代首选)](#1-axum-现代首选)
    - [2. actix-web (成熟稳定)](#2-actix-web-成熟稳定)
    - [3. rocket (易用性强)](#3-rocket-易用性强)
    - [Web 框架对比](#web-框架对比)
  - [数据库与 ORM](#数据库与-orm)
    - [1. sqlx (推荐)](#1-sqlx-推荐)
    - [2. diesel (传统 ORM)](#2-diesel-传统-orm)
    - [3. sea-orm (新一代 ORM)](#3-sea-orm-新一代-orm)
    - [数据库库对比](#数据库库对比)
  - [消息队列与流处理](#消息队列与流处理)
    - [1. rdkafka (Kafka 客户端)](#1-rdkafka-kafka-客户端)
    - [2. lapin (RabbitMQ 客户端)](#2-lapin-rabbitmq-客户端)
    - [3. async-nats (NATS 客户端)](#3-async-nats-nats-客户端)
  - [序列化与数据格式](#序列化与数据格式)
    - [JSON - serde\_json](#json---serde_json)
    - [MessagePack - rmp-serde](#messagepack---rmp-serde)
    - [Protocol Buffers - prost](#protocol-buffers---prost)
  - [HTTP 客户端](#http-客户端)
    - [1. reqwest (推荐)](#1-reqwest-推荐)
    - [2. hyper (底层库)](#2-hyper-底层库)
  - [命令行工具](#命令行工具)
    - [1. clap (推荐)](#1-clap-推荐)
    - [2. indicatif (进度条)](#2-indicatif-进度条)
    - [3. colored (彩色输出)](#3-colored-彩色输出)
  - [日志与可观测性](#日志与可观测性)
    - [1. tracing (推荐)](#1-tracing-推荐)
    - [2. log (传统日志)](#2-log-传统日志)
    - [3. prometheus (指标)](#3-prometheus-指标)
  - [错误处理](#错误处理)
    - [1. anyhow (应用错误)](#1-anyhow-应用错误)
    - [2. thiserror (库错误)](#2-thiserror-库错误)
  - [测试工具](#测试工具)
    - [1. criterion (基准测试)](#1-criterion-基准测试)
    - [2. proptest (属性测试)](#2-proptest-属性测试)
    - [3. mockall (Mock)](#3-mockall-mock)
  - [密码学与安全](#密码学与安全)
    - [1. rustls (TLS)](#1-rustls-tls)
    - [2. ring (密码学)](#2-ring-密码学)
    - [3. argon2 (密码哈希)](#3-argon2-密码哈希)
  - [并发与并行](#并发与并行)
    - [1. rayon (数据并行)](#1-rayon-数据并行)
    - [2. crossbeam (并发工具)](#2-crossbeam-并发工具)
  - [图形与 GUI](#图形与-gui)
    - [1. egui (即时模式 GUI)](#1-egui-即时模式-gui)
    - [2. iced (响应式 GUI)](#2-iced-响应式-gui)
  - [游戏开发](#游戏开发)
    - [1. bevy (游戏引擎)](#1-bevy-游戏引擎)
  - [WebAssembly](#webassembly)
    - [1. wasm-bindgen](#1-wasm-bindgen)
    - [2. yew (Web 前端框架)](#2-yew-web-前端框架)
  - [嵌入式开发](#嵌入式开发)
    - [1. embedded-hal](#1-embedded-hal)
  - [性能分析](#性能分析)
    - [1. flamegraph](#1-flamegraph)
  - [代码质量](#代码质量)
    - [1. clippy (Linter)](#1-clippy-linter)
    - [2. rustfmt (格式化)](#2-rustfmt-格式化)
  - [选择决策树](#选择决策树)
    - [Web 应用开发](#web-应用开发)
    - [数据库访问](#数据库访问)
    - [错误处理1](#错误处理1)
  - [成熟度评估](#成熟度评估)
    - [评估标准](#评估标准)
    - [推荐库成熟度总览](#推荐库成熟度总览)
  - [快速参考](#快速参考)
    - [新项目必备库](#新项目必备库)
    - [学习路径](#学习路径)
  - [总结](#总结)
    - [核心建议](#核心建议)
    - [持续更新](#持续更新)

## 📋 目录

- [Rust 必备开源库生态指南 (2025)](#rust-必备开源库生态指南-2025)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [概览](#概览)
    - [生态全景图](#生态全景图)
  - [核心基础库](#核心基础库)
    - [1. 序列化 - serde](#1-序列化---serde)
    - [2. 正则表达式 - regex](#2-正则表达式---regex)
    - [3. 随机数 - rand](#3-随机数---rand)
    - [4. 时间日期 - chrono / time](#4-时间日期---chrono--time)
  - [异步运行时](#异步运行时)
    - [1. tokio (主流选择)](#1-tokio-主流选择)
    - [2. async-std (简单易用)](#2-async-std-简单易用)
    - [3. smol (轻量高效)](#3-smol-轻量高效)
    - [异步运行时对比](#异步运行时对比)
  - [Web 框架](#web-框架)
    - [1. axum (现代首选)](#1-axum-现代首选)
    - [2. actix-web (成熟稳定)](#2-actix-web-成熟稳定)
    - [3. rocket (易用性强)](#3-rocket-易用性强)
    - [Web 框架对比](#web-框架对比)
  - [数据库与 ORM](#数据库与-orm)
    - [1. sqlx (推荐)](#1-sqlx-推荐)
    - [2. diesel (传统 ORM)](#2-diesel-传统-orm)
    - [3. sea-orm (新一代 ORM)](#3-sea-orm-新一代-orm)
    - [数据库库对比](#数据库库对比)
  - [消息队列与流处理](#消息队列与流处理)
    - [1. rdkafka (Kafka 客户端)](#1-rdkafka-kafka-客户端)
    - [2. lapin (RabbitMQ 客户端)](#2-lapin-rabbitmq-客户端)
    - [3. async-nats (NATS 客户端)](#3-async-nats-nats-客户端)
  - [序列化与数据格式](#序列化与数据格式)
    - [JSON - serde\_json](#json---serde_json)
    - [MessagePack - rmp-serde](#messagepack---rmp-serde)
    - [Protocol Buffers - prost](#protocol-buffers---prost)
  - [HTTP 客户端](#http-客户端)
    - [1. reqwest (推荐)](#1-reqwest-推荐)
    - [2. hyper (底层库)](#2-hyper-底层库)
  - [命令行工具](#命令行工具)
    - [1. clap (推荐)](#1-clap-推荐)
    - [2. indicatif (进度条)](#2-indicatif-进度条)
    - [3. colored (彩色输出)](#3-colored-彩色输出)
  - [日志与可观测性](#日志与可观测性)
    - [1. tracing (推荐)](#1-tracing-推荐)
    - [2. log (传统日志)](#2-log-传统日志)
    - [3. prometheus (指标)](#3-prometheus-指标)
  - [错误处理](#错误处理)
    - [1. anyhow (应用错误)](#1-anyhow-应用错误)
    - [2. thiserror (库错误)](#2-thiserror-库错误)
  - [测试工具](#测试工具)
    - [1. criterion (基准测试)](#1-criterion-基准测试)
    - [2. proptest (属性测试)](#2-proptest-属性测试)
    - [3. mockall (Mock)](#3-mockall-mock)
  - [密码学与安全](#密码学与安全)
    - [1. rustls (TLS)](#1-rustls-tls)
    - [2. ring (密码学)](#2-ring-密码学)
    - [3. argon2 (密码哈希)](#3-argon2-密码哈希)
  - [并发与并行](#并发与并行)
    - [1. rayon (数据并行)](#1-rayon-数据并行)
    - [2. crossbeam (并发工具)](#2-crossbeam-并发工具)
  - [图形与 GUI](#图形与-gui)
    - [1. egui (即时模式 GUI)](#1-egui-即时模式-gui)
    - [2. iced (响应式 GUI)](#2-iced-响应式-gui)
  - [游戏开发](#游戏开发)
    - [1. bevy (游戏引擎)](#1-bevy-游戏引擎)
  - [WebAssembly](#webassembly)
    - [1. wasm-bindgen](#1-wasm-bindgen)
    - [2. yew (Web 前端框架)](#2-yew-web-前端框架)
  - [嵌入式开发](#嵌入式开发)
    - [1. embedded-hal](#1-embedded-hal)
  - [性能分析](#性能分析)
    - [1. flamegraph](#1-flamegraph)
  - [代码质量](#代码质量)
    - [1. clippy (Linter)](#1-clippy-linter)
    - [2. rustfmt (格式化)](#2-rustfmt-格式化)
  - [选择决策树](#选择决策树)
    - [Web 应用开发](#web-应用开发)
    - [数据库访问](#数据库访问)
    - [错误处理1](#错误处理1)
  - [成熟度评估](#成熟度评估)
    - [评估标准](#评估标准)
    - [推荐库成熟度总览](#推荐库成熟度总览)
  - [快速参考](#快速参考)
    - [新项目必备库](#新项目必备库)
    - [学习路径](#学习路径)
  - [总结](#总结)
    - [核心建议](#核心建议)
    - [持续更新](#持续更新)

---

## 概览

### 生态全景图

```text
Rust 开源库生态 (2025)
├─ 📦 核心基础
│  ├─ serde (序列化)
│  ├─ regex (正则表达式)
│  ├─ rand (随机数)
│  └─ chrono/time (时间日期)
├─ ⚡ 异步运行时
│  ├─ tokio (主流)
│  ├─ async-std (简单)
│  └─ smol (轻量)
├─ 🌐 Web 开发
│  ├─ axum (现代)
│  ├─ actix-web (成熟)
│  └─ rocket (易用)
├─ 🗄️ 数据库
│  ├─ sqlx (异步SQL)
│  ├─ diesel (ORM)
│  └─ sea-orm (新型ORM)
├─ 📨 消息队列
│  ├─ lapin (RabbitMQ)
│  ├─ rdkafka (Kafka)
│  └─ async-nats (NATS)
├─ 🔐 安全加密
│  ├─ rustls (TLS)
│  ├─ ring (密码学)
│  └─ argon2 (密码哈希)
├─ 📊 可观测性
│  ├─ tracing (日志追踪)
│  ├─ prometheus (指标)
│  └─ opentelemetry (分布式追踪)
├─ 🧪 测试工具
│  ├─ criterion (基准测试)
│  ├─ proptest (属性测试)
│  └─ mockall (Mock)
└─ 🛠️ 开发工具
   ├─ clap (CLI)
   ├─ anyhow/thiserror (错误)
   └─ cargo-* (工具链)
```

---

## 核心基础库

### 1. 序列化 - serde

**GitHub**: <https://github.com/serde-rs/serde>  
**版本**: 1.0.210+ (2025)  
**下载量**: 500M+  
**成熟度**: ⭐⭐⭐⭐⭐

**用途**:

- JSON/YAML/TOML/MessagePack 等格式序列化
- 数据结构与字符串互转
- API 数据交换

**核心特性**:

```rust
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
struct User {
    id: u64,
    name: String,
    email: String,
}

// JSON 序列化
let user = User { id: 1, name: "Alice".into(), email: "alice@example.com".into() };
let json = serde_json::to_string(&user)?;

// JSON 反序列化
let user: User = serde_json::from_str(&json)?;
```

**配套生态**:

- `serde_json` - JSON 支持 (最流行)
- `serde_yaml` - YAML 支持
- `toml` - TOML 支持
- `bincode` - 二进制格式
- `serde_urlencoded` - URL 编码

**使用场景**:

- ✅ Web API 数据交换
- ✅ 配置文件读写
- ✅ 持久化存储
- ✅ 网络协议

**选择理由**:

- 事实标准，几乎所有 crate 都支持
- 零成本抽象，性能优异
- derive 宏简化使用

---

### 2. 正则表达式 - regex

**GitHub**: <https://github.com/rust-lang/regex>  
**版本**: 1.10+  
**下载量**: 300M+  
**成熟度**: ⭐⭐⭐⭐⭐

**用途**:

- 文本匹配与搜索
- 字符串提取与替换
- 数据验证

**核心特性**:

```rust
use regex::Regex;

// 编译正则表达式
let re = Regex::new(r"^\d{4}-\d{2}-\d{2}$").unwrap();
assert!(re.is_match("2025-10-20"));

// 捕获组
let re = Regex::new(r"(\w+)@(\w+\.\w+)").unwrap();
if let Some(caps) = re.captures("user@example.com") {
    println!("User: {}, Domain: {}", &caps[1], &caps[2]);
}

// 替换
let re = Regex::new(r"\s+").unwrap();
let result = re.replace_all("hello   world", " ");
```

**性能优化**:

```rust
use regex::RegexBuilder;

// 预编译正则表达式
lazy_static! {
    static ref EMAIL_RE: Regex = Regex::new(
        r"^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$"
    ).unwrap();
}

// 使用构建器优化
let re = RegexBuilder::new(r"pattern")
    .case_insensitive(true)
    .multi_line(true)
    .build()?;
```

**使用场景**:

- ✅ 邮箱/电话验证
- ✅ 日志解析
- ✅ 文本处理
- ✅ Web 爬虫

---

### 3. 随机数 - rand

**GitHub**: <https://github.com/rust-random/rand>  
**版本**: 0.8+  
**下载量**: 250M+  
**成熟度**: ⭐⭐⭐⭐⭐

**用途**:

- 随机数生成
- 随机采样
- 密码学随机 (配合 `rand_chacha`)

**核心特性**:

```rust
use rand::{Rng, thread_rng};
use rand::distributions::{Alphanumeric, Uniform};

// 生成随机数
let mut rng = thread_rng();
let n: u32 = rng.gen();
let n: f64 = rng.gen_range(0.0..100.0);

// 随机字符串
let s: String = thread_rng()
    .sample_iter(&Alphanumeric)
    .take(30)
    .map(char::from)
    .collect();

// 随机选择
let choices = vec!["rock", "paper", "scissors"];
let choice = choices.choose(&mut rng).unwrap();

// 洗牌
let mut nums = vec![1, 2, 3, 4, 5];
nums.shuffle(&mut rng);
```

**密码学安全**:

```rust
use rand::rngs::OsRng;
use rand::RngCore;

let mut key = [0u8; 32];
OsRng.fill_bytes(&mut key);
```

**使用场景**:

- ✅ 游戏开发
- ✅ 模拟仿真
- ✅ 测试数据生成
- ✅ 密码学应用

---

### 4. 时间日期 - chrono / time

**GitHub**:

- chrono: <https://github.com/chronotope/chrono>
- time: <https://github.com/time-rs/time>

**版本**: chrono 0.4+ | time 0.3+  
**下载量**: chrono 200M+ | time 150M+  
**成熟度**: ⭐⭐⭐⭐⭐

**选择指南**:

- **chrono**: 更完整的功能，类似 Python `datetime`
- **time**: 更安全，避免时区问题

**chrono 核心特性**:

```rust
use chrono::{DateTime, Utc, Local, Duration, NaiveDate};

// 当前时间
let now: DateTime<Utc> = Utc::now();
let local: DateTime<Local> = Local::now();

// 解析时间
let dt = DateTime::parse_from_rfc3339("2025-10-20T14:30:00Z")?;

// 格式化
let formatted = now.format("%Y-%m-%d %H:%M:%S").to_string();

// 时间运算
let tomorrow = now + Duration::days(1);
let last_week = now - Duration::weeks(1);

// 时间比较
if tomorrow > now {
    println!("Tomorrow is in the future!");
}

// 解析日期
let date = NaiveDate::from_ymd_opt(2025, 10, 20).unwrap();
```

**time 核心特性**:

```rust
use time::{OffsetDateTime, Duration, format_description};

// 当前时间
let now = OffsetDateTime::now_utc();

// 格式化
let format = format_description::parse("[year]-[month]-[day]")?;
let formatted = now.format(&format)?;

// 时间运算
let future = now + Duration::hours(24);
```

**使用场景**:

- ✅ 时间戳处理
- ✅ 日志时间
- ✅ 调度任务
- ✅ 时区转换

---

## 异步运行时

### 1. tokio (主流选择)

**GitHub**: <https://github.com/tokio-rs/tokio>  
**版本**: 1.40+ (2025)  
**下载量**: 400M+  
**成熟度**: ⭐⭐⭐⭐⭐

**用途**:

- 异步 I/O
- 网络编程
- 并发任务调度

**核心特性**:

```rust
use tokio;

#[tokio::main]
async fn main() {
    // 并发执行多个任务
    let task1 = tokio::spawn(async {
        println!("Task 1");
    });
    
    let task2 = tokio::spawn(async {
        println!("Task 2");
    });
    
    // 等待所有任务
    let _ = tokio::join!(task1, task2);
}
```

**实用功能**:

```rust
use tokio::time::{sleep, Duration, timeout};
use tokio::sync::{Mutex, mpsc};
use tokio::fs::File;
use tokio::io::AsyncReadExt;

// 1. 超时控制
let result = timeout(Duration::from_secs(5), async_operation()).await;

// 2. 异步互斥锁
let data = Arc::new(Mutex::new(0));

// 3. 消息通道
let (tx, mut rx) = mpsc::channel(100);
tx.send("message").await?;

// 4. 异步文件 I/O
let mut file = File::open("data.txt").await?;
let mut contents = String::new();
file.read_to_string(&mut contents).await?;

// 5. 定时器
sleep(Duration::from_secs(1)).await;

// 6. 并发限制
use tokio::sync::Semaphore;
let sem = Arc::new(Semaphore::new(10)); // 最多10个并发
```

**运行时配置**:

```rust
// 多线程运行时
#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn main() { }

// 单线程运行时
#[tokio::main(flavor = "current_thread")]
async fn main() { }

// 自定义运行时
use tokio::runtime::Runtime;

let rt = Runtime::new()?;
rt.block_on(async {
    // 异步代码
});
```

**生态支持**:

- `tokio-util` - 实用工具
- `tokio-stream` - 异步流
- `tokio-console` - 运行时监控
- `tower` - 服务抽象

**使用场景**:

- ✅ Web 服务器
- ✅ 数据库连接
- ✅ 网络客户端
- ✅ 高并发应用

**选择理由**:

- 最成熟的异步运行时
- 生态最丰富
- 性能优异
- 文档完善

---

### 2. async-std (简单易用)

**GitHub**: <https://github.com/async-rs/async-std>  
**版本**: 1.12+  
**下载量**: 50M+  
**成熟度**: ⭐⭐⭐⭐

**用途**:

- 与标准库 API 一致的异步版本
- 快速原型开发

**核心特性**:

```rust
use async_std::task;
use async_std::fs::File;
use async_std::io::ReadExt;

#[async_std::main]
async fn main() {
    // API 设计类似标准库
    let mut file = File::open("data.txt").await?;
    let mut contents = String::new();
    file.read_to_string(&mut contents).await?;
    
    // 任务生成
    let handle = task::spawn(async {
        println!("Async task");
    });
    
    handle.await;
}
```

**使用场景**:

- ✅ 学习异步编程
- ✅ 小型项目
- ✅ 需要标准库 API 风格

**选择理由**:

- API 设计友好
- 学习曲线平缓
- 适合快速开发

---

### 3. smol (轻量高效)

**GitHub**: <https://github.com/smol-rs/smol>  
**版本**: 2.0+  
**下载量**: 20M+  
**成熟度**: ⭐⭐⭐⭐

**用途**:

- 轻量级异步运行时
- 嵌入式系统

**核心特性**:

```rust
use smol;

fn main() {
    smol::block_on(async {
        println!("Async with smol");
    });
}
```

**使用场景**:

- ✅ 资源受限环境
- ✅ 嵌入式应用
- ✅ CLI 工具

---

### 异步运行时对比

| 特性 | tokio | async-std | smol |
|------|-------|-----------|------|
| **成熟度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **生态** | 非常丰富 | 一般 | 较少 |
| **性能** | 极高 | 高 | 高 |
| **易用性** | 中等 | 简单 | 简单 |
| **文档** | 完善 | 良好 | 良好 |
| **适用场景** | 生产环境 | 学习/原型 | 轻量级应用 |
| **推荐度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |

**推荐**:

- 🏆 **生产环境**: tokio
- 📚 **学习入门**: async-std
- 🪶 **轻量应用**: smol

---

## Web 框架

### 1. axum (现代首选)

**GitHub**: <https://github.com/tokio-rs/axum>  
**版本**: 0.7+ (2025)  
**下载量**: 50M+  
**成熟度**: ⭐⭐⭐⭐⭐

**用途**:

- RESTful API
- 微服务
- WebSocket

**核心特性**:

```rust
use axum::{
    Router,
    routing::{get, post},
    extract::{Path, Query, Json},
    response::IntoResponse,
};
use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
struct CreateUser {
    name: String,
    email: String,
}

#[derive(Serialize)]
struct User {
    id: u64,
    name: String,
    email: String,
}

// 路由处理器
async fn get_user(Path(id): Path<u64>) -> Json<User> {
    Json(User {
        id,
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
    })
}

async fn create_user(Json(payload): Json<CreateUser>) -> impl IntoResponse {
    // 创建用户逻辑
    (axum::http::StatusCode::CREATED, Json(User {
        id: 1,
        name: payload.name,
        email: payload.email,
    }))
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/users/:id", get(get_user))
        .route("/users", post(create_user));
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();
    
    axum::serve(listener, app).await.unwrap();
}
```

**中间件支持**:

```rust
use axum::{
    middleware::{self, Next},
    http::Request,
};
use tower_http::{
    trace::TraceLayer,
    cors::CorsLayer,
    compression::CompressionLayer,
};

async fn auth_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> impl IntoResponse {
    // 认证逻辑
    next.run(req).await
}

let app = Router::new()
    .route("/", get(handler))
    .layer(middleware::from_fn(auth_middleware))
    .layer(TraceLayer::new_for_http())
    .layer(CorsLayer::permissive())
    .layer(CompressionLayer::new());
```

**状态管理**:

```rust
use axum::extract::State;
use std::sync::Arc;

#[derive(Clone)]
struct AppState {
    db: Arc<Database>,
}

async fn handler(State(state): State<AppState>) -> String {
    // 使用共享状态
    format!("Connected to DB")
}

let state = AppState {
    db: Arc::new(Database::new()),
};

let app = Router::new()
    .route("/", get(handler))
    .with_state(state);
```

**使用场景**:

- ✅ RESTful API
- ✅ 微服务
- ✅ 实时应用 (WebSocket)
- ✅ GraphQL (配合 async-graphql)

**选择理由**:

- 现代设计，利用 Rust 1.90 特性
- 类型安全的提取器
- 与 tower 生态完美集成
- 性能优异

---

### 2. actix-web (成熟稳定)

**GitHub**: <https://github.com/actix/actix-web>  
**版本**: 4.9+ (2025)  
**下载量**: 100M+  
**成熟度**: ⭐⭐⭐⭐⭐

**用途**:

- 高性能 Web 服务
- 大型应用

**核心特性**:

```rust
use actix_web::{web, App, HttpServer, HttpResponse};
use serde::Deserialize;

#[derive(Deserialize)]
struct Info {
    name: String,
}

async fn index(info: web::Query<Info>) -> HttpResponse {
    HttpResponse::Ok().body(format!("Hello {}!", info.name))
}

async fn create_user(user: web::Json<User>) -> HttpResponse {
    HttpResponse::Created().json(user.0)
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .route("/", web::get().to(index))
            .route("/users", web::post().to(create_user))
    })
    .bind(("127.0.0.1", 8080))?
    .run()
    .await
}
```

**使用场景**:

- ✅ 高并发 Web 服务
- ✅ 需要极致性能
- ✅ 大型企业应用

**选择理由**:

- 经过大规模生产验证
- 性能顶尖
- 功能完善

---

### 3. rocket (易用性强)

**GitHub**: <https://github.com/SergioBenitez/Rocket>  
**版本**: 0.5+ (2025)  
**下载量**: 50M+  
**成熟度**: ⭐⭐⭐⭐

**用途**:

- 快速开发
- 原型验证

**核心特性**:

```rust
#[macro_use] extern crate rocket;

#[get("/hello/<name>/<age>")]
fn hello(name: &str, age: u8) -> String {
    format!("Hello, {} year old named {}!", age, name)
}

#[launch]
fn rocket() -> _ {
    rocket::build().mount("/", routes![hello])
}
```

**使用场景**:

- ✅ 快速原型
- ✅ 小型项目
- ✅ 学习 Web 开发

---

### Web 框架对比

| 框架 | axum | actix-web | rocket |
|------|------|-----------|--------|
| **成熟度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **性能** | 极高 | 极高 | 高 |
| **易用性** | 中等 | 中等 | 简单 |
| **类型安全** | 优秀 | 良好 | 优秀 |
| **生态** | 快速增长 | 成熟 | 一般 |
| **学习曲线** | 中等 | 陡峭 | 平缓 |
| **推荐场景** | 新项目 | 生产级 | 学习/原型 |

**推荐**:

- 🏆 **2025 新项目**: axum
- 🔥 **高性能需求**: actix-web
- 📚 **快速开发**: rocket

---

## 数据库与 ORM

### 1. sqlx (推荐)

**GitHub**: <https://github.com/launchbadge/sqlx>  
**版本**: 0.8+ (2025)  
**下载量**: 80M+  
**成熟度**: ⭐⭐⭐⭐⭐

**用途**:

- 异步 SQL 数据库访问
- 编译时 SQL 验证
- 支持 PostgreSQL, MySQL, SQLite, MSSQL

**核心特性**:

```rust
use sqlx::{PgPool, FromRow};

#[derive(FromRow)]
struct User {
    id: i64,
    name: String,
    email: String,
}

#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    // 连接池
    let pool = PgPool::connect("postgres://user:pass@localhost/db").await?;
    
    // 查询 (编译时验证)
    let user = sqlx::query_as::<_, User>("SELECT * FROM users WHERE id = $1")
        .bind(1)
        .fetch_one(&pool)
        .await?;
    
    // 插入
    sqlx::query("INSERT INTO users (name, email) VALUES ($1, $2)")
        .bind("Alice")
        .bind("alice@example.com")
        .execute(&pool)
        .await?;
    
    // 事务
    let mut tx = pool.begin().await?;
    sqlx::query("UPDATE users SET name = $1 WHERE id = $2")
        .bind("Bob")
        .bind(1)
        .execute(&mut *tx)
        .await?;
    tx.commit().await?;
    
    Ok(())
}
```

**宏支持**:

```rust
// 编译时检查 SQL
let user = sqlx::query_as!(
    User,
    "SELECT id, name, email FROM users WHERE id = $1",
    user_id
)
.fetch_one(&pool)
.await?;
```

**迁移管理**:

```bash
# CLI 工具
sqlx migrate add create_users_table
sqlx migrate run
```

**使用场景**:

- ✅ 现代异步应用
- ✅ 需要编译时 SQL 检查
- ✅ 微服务架构

**选择理由**:

- 纯 Rust，无 C 依赖
- 异步优先
- 类型安全
- 性能优异

---

### 2. diesel (传统 ORM)

**GitHub**: <https://github.com/diesel-rs/diesel>  
**版本**: 2.2+ (2025)  
**下载量**: 60M+  
**成熟度**: ⭐⭐⭐⭐⭐

**用途**:

- 类型安全的 ORM
- 同步数据库访问
- 支持 PostgreSQL, MySQL, SQLite

**核心特性**:

```rust
use diesel::prelude::*;

#[derive(Queryable)]
struct User {
    id: i32,
    name: String,
    email: String,
}

#[derive(Insertable)]
#[diesel(table_name = users)]
struct NewUser<'a> {
    name: &'a str,
    email: &'a str,
}

fn main() {
    let connection = &mut establish_connection();
    
    // 查询
    use schema::users::dsl::*;
    let results = users
        .filter(email.like("%@example.com"))
        .limit(5)
        .load::<User>(connection)
        .expect("Error loading users");
    
    // 插入
    let new_user = NewUser {
        name: "Alice",
        email: "alice@example.com",
    };
    
    diesel::insert_into(users)
        .values(&new_user)
        .execute(connection)
        .expect("Error saving user");
}
```

**使用场景**:

- ✅ 同步应用
- ✅ 需要完整 ORM 功能
- ✅ 复杂查询构建

**选择理由**:

- 最成熟的 Rust ORM
- 类型安全查询
- DSL 强大

---

### 3. sea-orm (新一代 ORM)

**GitHub**: <https://github.com/SeaQL/sea-orm>  
**版本**: 1.0+ (2025)  
**下载量**: 20M+  
**成熟度**: ⭐⭐⭐⭐

**用途**:

- 异步 ORM
- 现代化设计

**核心特性**:

```rust
use sea_orm::*;

#[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i32,
    pub name: String,
    pub email: String,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}

async fn main() -> Result<(), DbErr> {
    let db = Database::connect("postgres://...").await?;
    
    // 查询
    let user: Option<Model> = Entity::find_by_id(1)
        .one(&db)
        .await?;
    
    // 插入
    let user = ActiveModel {
        name: Set("Alice".to_owned()),
        email: Set("alice@example.com".to_owned()),
        ..Default::default()
    };
    let result = user.insert(&db).await?;
    
    Ok(())
}
```

**使用场景**:

- ✅ 新项目
- ✅ 异步优先
- ✅ 需要现代化 ORM

---

### 数据库库对比

| 库 | sqlx | diesel | sea-orm |
|----|------|--------|---------|
| **类型** | SQL构建器 | ORM | ORM |
| **异步** | ✅ | ❌ (diesel-async可选) | ✅ |
| **成熟度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **易用性** | 中等 | 中等 | 简单 |
| **性能** | 极高 | 极高 | 高 |
| **灵活性** | 高 | 中 | 中 |
| **学习曲线** | 平缓 | 陡峭 | 平缓 |

**推荐**:

- 🏆 **异步应用**: sqlx
- 🔧 **同步应用**: diesel
- 🆕 **新项目**: sea-orm

---

## 消息队列与流处理

### 1. rdkafka (Kafka 客户端)

**GitHub**: <https://github.com/fede1024/rust-rdkafka>  
**版本**: 0.36+ (2025)  
**下载量**: 15M+  
**成熟度**: ⭐⭐⭐⭐⭐

**用途**:

- Kafka 生产者/消费者
- 流处理

**核心特性**:

```rust
use rdkafka::{
    producer::{FutureProducer, FutureRecord},
    consumer::{StreamConsumer, Consumer},
    ClientConfig, Message,
};

// 生产者
async fn produce() {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .create()
        .expect("Producer creation failed");
    
    let record = FutureRecord::to("my-topic")
        .payload("message payload")
        .key("message key");
    
    producer.send(record, Duration::from_secs(0)).await;
}

// 消费者
async fn consume() {
    let consumer: StreamConsumer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("group.id", "my-group")
        .create()
        .expect("Consumer creation failed");
    
    consumer.subscribe(&["my-topic"]).unwrap();
    
    loop {
        match consumer.recv().await {
            Ok(msg) => {
                let payload = msg.payload_view::<str>().unwrap().unwrap();
                println!("Received: {}", payload);
            }
            Err(e) => eprintln!("Error: {}", e),
        }
    }
}
```

**使用场景**:

- ✅ 事件流处理
- ✅ 日志聚合
- ✅ 微服务通信

---

### 2. lapin (RabbitMQ 客户端)

**GitHub**: <https://github.com/CleverCloud/lapin>  
**版本**: 2.5+ (2025)  
**下载量**: 10M+  
**成熟度**: ⭐⭐⭐⭐

**核心特性**:

```rust
use lapin::{
    Connection, ConnectionProperties,
    options::*, types::FieldTable,
};

#[tokio::main]
async fn main() {
    let conn = Connection::connect(
        "amqp://guest:guest@localhost:5672",
        ConnectionProperties::default()
    ).await.unwrap();
    
    let channel = conn.create_channel().await.unwrap();
    
    // 声明队列
    channel.queue_declare(
        "my_queue",
        QueueDeclareOptions::default(),
        FieldTable::default()
    ).await.unwrap();
    
    // 发布消息
    channel.basic_publish(
        "",
        "my_queue",
        BasicPublishOptions::default(),
        b"Hello RabbitMQ",
        BasicProperties::default()
    ).await.unwrap();
}
```

---

### 3. async-nats (NATS 客户端)

**GitHub**: <https://github.com/nats-io/nats.rs>  
**版本**: 0.35+ (2025)  
**下载量**: 8M+  
**成熟度**: ⭐⭐⭐⭐

**核心特性**:

```rust
use async_nats;

#[tokio::main]
async fn main() -> Result<(), async_nats::Error> {
    let client = async_nats::connect("nats://localhost:4222").await?;
    
    // 发布
    client.publish("my.subject", "Hello NATS".into()).await?;
    
    // 订阅
    let mut sub = client.subscribe("my.subject").await?;
    while let Some(msg) = sub.next().await {
        println!("Received: {:?}", msg);
    }
    
    Ok(())
}
```

---

## 序列化与数据格式

### JSON - serde_json

**版本**: 1.0.128+ (2025)  
**下载量**: 450M+  
**成熟度**: ⭐⭐⭐⭐⭐

```rust
use serde_json::{json, Value};

// 构建 JSON
let data = json!({
    "name": "Alice",
    "age": 30,
    "emails": ["alice@example.com"]
});

// 解析 JSON
let v: Value = serde_json::from_str(r#"{"name":"Bob"}"#)?;
println!("Name: {}", v["name"]);

// 序列化为字符串
let json_str = serde_json::to_string_pretty(&data)?;
```

### MessagePack - rmp-serde

**版本**: 1.3+ (2025)  
**下载量**: 15M+  
**成熟度**: ⭐⭐⭐⭐

```rust
use rmp_serde::{Serializer, Deserializer};

let data = MyStruct { /* ... */ };
let mut buf = Vec::new();
data.serialize(&mut Serializer::new(&mut buf))?;

// 反序列化
let decoded: MyStruct = rmp_serde::from_slice(&buf)?;
```

### Protocol Buffers - prost

**版本**: 0.13+ (2025)  
**下载量**: 40M+  
**成熟度**: ⭐⭐⭐⭐⭐

```rust
// 定义 .proto 文件后自动生成代码
use prost::Message;

let person = Person {
    name: "Alice".to_string(),
    id: 1,
    email: "alice@example.com".to_string(),
};

// 序列化
let mut buf = Vec::new();
person.encode(&mut buf)?;

// 反序列化
let decoded = Person::decode(&buf[..])?;
```

---

## HTTP 客户端

### 1. reqwest (推荐)

**GitHub**: <https://github.com/seanmonstar/reqwest>  
**版本**: 0.12+ (2025)  
**下载量**: 200M+  
**成熟度**: ⭐⭐⭐⭐⭐

**核心特性**:

```rust
use reqwest;

#[tokio::main]
async fn main() -> Result<(), reqwest::Error> {
    // GET 请求
    let resp = reqwest::get("https://api.example.com/users")
        .await?
        .json::<Vec<User>>()
        .await?;
    
    // POST 请求
    let client = reqwest::Client::new();
    let res = client
        .post("https://api.example.com/users")
        .json(&NewUser {
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
        })
        .send()
        .await?;
    
    // 自定义请求
    let response = client
        .request(reqwest::Method::PUT, "https://api.example.com/users/1")
        .header("Authorization", "Bearer token")
        .timeout(Duration::from_secs(10))
        .json(&update_data)
        .send()
        .await?;
    
    Ok(())
}
```

**高级功能**:

```rust
// 代理
let client = reqwest::Client::builder()
    .proxy(reqwest::Proxy::all("http://proxy:8080")?)
    .build()?;

// TLS 配置
let client = reqwest::Client::builder()
    .danger_accept_invalid_certs(true)
    .build()?;

// Cookie 支持
let client = reqwest::Client::builder()
    .cookie_store(true)
    .build()?;

// 文件上传
let form = reqwest::multipart::Form::new()
    .text("key", "value")
    .file("file", "/path/to/file")?;

client.post("https://api.example.com/upload")
    .multipart(form)
    .send()
    .await?;
```

**使用场景**:

- ✅ API 客户端
- ✅ Web 爬虫
- ✅ 微服务通信

---

### 2. hyper (底层库)

**GitHub**: <https://github.com/hyperium/hyper>  
**版本**: 1.4+ (2025)  
**下载量**: 150M+  
**成熟度**: ⭐⭐⭐⭐⭐

**用途**:

- 构建自定义 HTTP 客户端/服务器
- 底层 HTTP 协议处理

```rust
use hyper::{Body, Client, Request, Uri};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Client::new();
    
    let uri: Uri = "http://httpbin.org/get".parse()?;
    let resp = client.get(uri).await?;
    
    println!("Status: {}", resp.status());
    
    Ok(())
}
```

---

## 命令行工具

### 1. clap (推荐)

**GitHub**: <https://github.com/clap-rs/clap>  
**版本**: 4.5+ (2025)  
**下载量**: 250M+  
**成熟度**: ⭐⭐⭐⭐⭐

**核心特性**:

```rust
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "myapp")]
#[command(about = "A simple CLI tool", long_about = None)]
struct Cli {
    /// The name to greet
    #[arg(short, long)]
    name: String,
    
    /// Number of times to greet
    #[arg(short, long, default_value_t = 1)]
    count: u8,
    
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Adds files
    Add {
        /// Files to add
        files: Vec<String>,
    },
    /// Removes files
    Remove {
        /// Files to remove
        files: Vec<String>,
    },
}

fn main() {
    let cli = Cli::parse();
    
    for _ in 0..cli.count {
        println!("Hello {}!", cli.name);
    }
    
    match &cli.command {
        Some(Commands::Add { files }) => {
            println!("Adding files: {:?}", files);
        }
        Some(Commands::Remove { files }) => {
            println!("Removing files: {:?}", files);
        }
        None => {}
    }
}
```

**自动补全**:

```rust
use clap_complete::{generate, shells::Bash};

let mut cmd = Cli::command();
generate(Bash, &mut cmd, "myapp", &mut std::io::stdout());
```

---

### 2. indicatif (进度条)

**GitHub**: <https://github.com/console-rs/indicatif>  
**版本**: 0.17+ (2025)  
**下载量**: 50M+

```rust
use indicatif::{ProgressBar, ProgressStyle};

let pb = ProgressBar::new(100);
pb.set_style(
    ProgressStyle::default_bar()
        .template("[{elapsed_precise}] {bar:40.cyan/blue} {pos:>7}/{len:7} {msg}")
        .progress_chars("##-")
);

for i in 0..100 {
    pb.set_position(i);
    pb.set_message(format!("Processing item {}", i));
    thread::sleep(Duration::from_millis(50));
}
pb.finish_with_message("Done!");
```

---

### 3. colored (彩色输出)

**GitHub**: <https://github.com/mackwic/colored>  
**版本**: 2.1+ (2025)  
**下载量**: 80M+

```rust
use colored::*;

println!("{}", "Hello world".red());
println!("{}", "Hello world".bold().yellow());
println!("{}", "Error message".on_red().white());
```

---

## 日志与可观测性

### 1. tracing (推荐)

**GitHub**: <https://github.com/tokio-rs/tracing>  
**版本**: 0.1.40+ (2025)  
**下载量**: 200M+  
**成熟度**: ⭐⭐⭐⭐⭐

**核心特性**:

```rust
use tracing::{info, debug, error, instrument};
use tracing_subscriber;

#[instrument]
async fn fetch_user(user_id: u64) -> Result<User, Error> {
    info!("Fetching user {}", user_id);
    
    let user = db.query_user(user_id).await?;
    
    debug!(user.name = %user.name, "User fetched");
    
    Ok(user)
}

fn main() {
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();
    
    fetch_user(1).await;
}
```

**结构化日志**:

```rust
use tracing::{span, Level};

let span = span!(Level::INFO, "my_span", key = "value");
let _enter = span.enter();

info!(request_id = %req_id, user_id = user_id, "Processing request");
```

**配合 OpenTelemetry**:

```rust
use tracing_subscriber::layer::SubscriberExt;
use tracing_opentelemetry::OpenTelemetryLayer;

let tracer = opentelemetry_jaeger::new_agent_pipeline()
    .with_service_name("my-service")
    .install_simple()?;

let telemetry = OpenTelemetryLayer::new(tracer);

tracing_subscriber::registry()
    .with(telemetry)
    .init();
```

---

### 2. log (传统日志)

**GitHub**: <https://github.com/rust-lang/log>  
**版本**: 0.4+ (2025)  
**下载量**: 400M+  
**成熟度**: ⭐⭐⭐⭐⭐

```rust
use log::{info, warn, error};
use env_logger;

fn main() {
    env_logger::init();
    
    info!("Application started");
    warn!("Warning message");
    error!("Error occurred");
}
```

---

### 3. prometheus (指标)

**GitHub**: <https://github.com/tikv/rust-prometheus>  
**版本**: 0.13+ (2025)  
**下载量**: 20M+

```rust
use prometheus::{IntCounter, Encoder, TextEncoder};

let counter = IntCounter::new("my_counter", "My counter")?;
prometheus::register(Box::new(counter.clone()))?;

counter.inc();

// 导出指标
let encoder = TextEncoder::new();
let metric_families = prometheus::gather();
let mut buffer = vec![];
encoder.encode(&metric_families, &mut buffer)?;
```

---

## 错误处理

### 1. anyhow (应用错误)

**GitHub**: <https://github.com/dtolnay/anyhow>  
**版本**: 1.0.89+ (2025)  
**下载量**: 300M+  
**成熟度**: ⭐⭐⭐⭐⭐

```rust
use anyhow::{Result, Context};

fn read_config() -> Result<Config> {
    let content = std::fs::read_to_string("config.toml")
        .context("Failed to read config file")?;
    
    let config: Config = toml::from_str(&content)
        .context("Failed to parse config")?;
    
    Ok(config)
}

fn main() -> Result<()> {
    let config = read_config()?;
    Ok(())
}
```

---

### 2. thiserror (库错误)

**GitHub**: <https://github.com/dtolnay/thiserror>  
**版本**: 1.0.64+ (2025)  
**下载量**: 300M+  
**成熟度**: ⭐⭐⭐⭐⭐

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MyError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Parse error: {0}")]
    Parse(String),
    
    #[error("Not found: {id}")]
    NotFound { id: u64 },
}
```

---

## 测试工具

### 1. criterion (基准测试)

**GitHub**: <https://github.com/bheisler/criterion.rs>  
**版本**: 0.5+ (2025)  
**下载量**: 40M+

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n-1) + fibonacci(n-2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

---

### 2. proptest (属性测试)

**GitHub**: <https://github.com/proptest-rs/proptest>  
**版本**: 1.5+ (2025)  
**下载量**: 25M+

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_sort(ref mut v in prop::collection::vec(any::<i32>(), 0..100)) {
        v.sort();
        for i in 1..v.len() {
            assert!(v[i-1] <= v[i]);
        }
    }
}
```

---

### 3. mockall (Mock)

**GitHub**: <https://github.com/asomers/mockall>  
**版本**: 0.13+ (2025)  
**下载量**: 15M+

```rust
use mockall::{automock, predicate::*};

#[automock]
trait Database {
    fn get_user(&self, id: u64) -> Result<User, Error>;
}

#[test]
fn test_with_mock() {
    let mut mock = MockDatabase::new();
    mock.expect_get_user()
        .with(eq(1))
        .times(1)
        .returning(|_| Ok(User::default()));
    
    // 使用 mock
}
```

---

## 密码学与安全

### 1. rustls (TLS)

**GitHub**: <https://github.com/rustls/rustls>  
**版本**: 0.23+ (2025)  
**下载量**: 100M+  
**成熟度**: ⭐⭐⭐⭐⭐

```rust
use rustls::{ClientConfig, RootCertStore};
use std::sync::Arc;

let mut root_store = RootCertStore::empty();
root_store.add_trust_anchors(
    webpki_roots::TLS_SERVER_ROOTS.iter().cloned()
);

let config = ClientConfig::builder()
    .with_root_certificates(root_store)
    .with_no_client_auth();
```

---

### 2. ring (密码学)

**GitHub**: <https://github.com/briansmith/ring>  
**版本**: 0.17+ (2025)  
**下载量**: 150M+

```rust
use ring::{digest, rand, signature};

// SHA-256 哈希
let hash = digest::digest(&digest::SHA256, b"hello world");

// ECDSA 签名
let rng = rand::SystemRandom::new();
let pkcs8_bytes = signature::EcdsaKeyPair::generate_pkcs8(
    &signature::ECDSA_P256_SHA256_ASN1_SIGNING,
    &rng,
)?;
```

---

### 3. argon2 (密码哈希)

**GitHub**: <https://github.com/RustCrypto/password-hashes>  
**版本**: 0.5+ (2025)  
**下载量**: 10M+

```rust
use argon2::{
    password_hash::{rand_core::OsRng, PasswordHash, PasswordHasher, PasswordVerifier, SaltString},
    Argon2
};

// 哈希密码
let password = b"hunter42";
let salt = SaltString::generate(&mut OsRng);
let argon2 = Argon2::default();
let password_hash = argon2.hash_password(password, &salt)?.to_string();

// 验证密码
let parsed_hash = PasswordHash::new(&password_hash)?;
assert!(argon2.verify_password(password, &parsed_hash).is_ok());
```

---

## 并发与并行

### 1. rayon (数据并行)

**GitHub**: <https://github.com/rayon-rs/rayon>  
**版本**: 1.10+ (2025)  
**下载量**: 80M+  
**成熟度**: ⭐⭐⭐⭐⭐

```rust
use rayon::prelude::*;

// 并行迭代
let sum: i32 = (1..100)
    .into_par_iter()
    .map(|x| x * x)
    .sum();

// 并行排序
let mut data = vec![5, 3, 8, 1, 9];
data.par_sort();

// 并行搜索
let found = data.par_iter()
    .find_any(|&&x| x > 5);
```

---

### 2. crossbeam (并发工具)

**GitHub**: <https://github.com/crossbeam-rs/crossbeam>  
**版本**: 0.8+ (2025)  
**下载量**: 100M+

```rust
use crossbeam::channel::{unbounded, select};
use crossbeam::thread;

// 无界通道
let (s, r) = unbounded();
s.send(1)?;
let msg = r.recv()?;

// 作用域线程
thread::scope(|s| {
    s.spawn(|_| {
        println!("Hello from thread!");
    });
}).unwrap();

// Select 多个通道
select! {
    recv(r1) -> msg => println!("r1: {:?}", msg),
    recv(r2) -> msg => println!("r2: {:?}", msg),
}
```

---

## 图形与 GUI

### 1. egui (即时模式 GUI)

**GitHub**: <https://github.com/emilk/egui>  
**版本**: 0.28+ (2025)  
**下载量**: 20M+  
**成熟度**: ⭐⭐⭐⭐

```rust
use eframe::egui;

fn main() -> Result<(), eframe::Error> {
    eframe::run_native(
        "My App",
        eframe::NativeOptions::default(),
        Box::new(|_| Box::new(MyApp::default())),
    )
}

struct MyApp {
    name: String,
}

impl Default for MyApp {
    fn default() -> Self {
        Self {
            name: "Arthur".to_owned(),
        }
    }
}

impl eframe::App for MyApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        egui::CentralPanel::default().show(ctx, |ui| {
            ui.heading("My egui Application");
            ui.text_edit_singleline(&mut self.name);
            if ui.button("Click me").clicked() {
                println!("Hello {}!", self.name);
            }
        });
    }
}
```

---

### 2. iced (响应式 GUI)

**GitHub**: <https://github.com/iced-rs/iced>  
**版本**: 0.13+ (2025)  
**下载量**: 15M+

```rust
use iced::{Element, Sandbox, Settings};
use iced::widget::{button, column, text};

pub fn main() -> iced::Result {
    Counter::run(Settings::default())
}

struct Counter {
    value: i32,
}

#[derive(Debug, Clone, Copy)]
enum Message {
    Increment,
    Decrement,
}

impl Sandbox for Counter {
    type Message = Message;

    fn new() -> Self {
        Self { value: 0 }
    }

    fn title(&self) -> String {
        String::from("Counter")
    }

    fn update(&mut self, message: Message) {
        match message {
            Message::Increment => self.value += 1,
            Message::Decrement => self.value -= 1,
        }
    }

    fn view(&self) -> Element<Message> {
        column![
            button("Increment").on_press(Message::Increment),
            text(self.value).size(50),
            button("Decrement").on_press(Message::Decrement)
        ]
        .into()
    }
}
```

---

## 游戏开发

### 1. bevy (游戏引擎)

**GitHub**: <https://github.com/bevyengine/bevy>  
**版本**: 0.14+ (2025)  
**下载量**: 25M+  
**成熟度**: ⭐⭐⭐⭐

```rust
use bevy::prelude::*;

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .add_systems(Startup, setup)
        .add_systems(Update, hello_world_system)
        .run();
}

fn setup(mut commands: Commands) {
    commands.spawn(Camera2dBundle::default());
}

fn hello_world_system() {
    println!("hello world");
}
```

---

## WebAssembly

### 1. wasm-bindgen

**GitHub**: <https://github.com/rustwasm/wasm-bindgen>  
**版本**: 0.2.93+ (2025)  
**下载量**: 80M+  
**成熟度**: ⭐⭐⭐⭐⭐

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

#[wasm_bindgen(start)]
pub fn main() {
    log("Hello from Rust!");
}
```

---

### 2. yew (Web 前端框架)

**GitHub**: <https://github.com/yewstack/yew>  
**版本**: 0.21+ (2025)  
**下载量**: 10M+

```rust
use yew::prelude::*;

#[function_component(App)]
fn app() -> Html {
    let counter = use_state(|| 0);
    let onclick = {
        let counter = counter.clone();
        Callback::from(move |_| counter.set(*counter + 1))
    };

    html! {
        <div>
            <button {onclick}>{ "Increment" }</button>
            <p>{ *counter }</p>
        </div>
    }
}

fn main() {
    yew::Renderer::<App>::new().render();
}
```

---

## 嵌入式开发

### 1. embedded-hal

**GitHub**: <https://github.com/rust-embedded/embedded-hal>  
**版本**: 1.0+ (2025)  
**下载量**: 30M+  
**成熟度**: ⭐⭐⭐⭐⭐

```rust
use embedded_hal::digital::v2::OutputPin;

fn blink<P: OutputPin>(led: &mut P) {
    led.set_high().unwrap();
    delay.delay_ms(1000u32);
    led.set_low().unwrap();
    delay.delay_ms(1000u32);
}
```

---

## 性能分析

### 1. flamegraph

**GitHub**: <https://github.com/flamegraph-rs/flamegraph>  
**版本**: 0.6+ (2025)  
**下载量**: 5M+

```bash
# 安装
cargo install flamegraph

# 生成火焰图
cargo flamegraph --bin my-app

# 输出 flamegraph.svg
```

---

## 代码质量

### 1. clippy (Linter)

**内置工具**  
**版本**: 随 Rust 更新  
**成熟度**: ⭐⭐⭐⭐⭐

```bash
# 运行 clippy
cargo clippy

# 自动修复
cargo clippy --fix

# 严格模式
cargo clippy -- -D warnings
```

---

### 2. rustfmt (格式化)

**内置工具**  
**版本**: 随 Rust 更新  
**成熟度**: ⭐⭐⭐⭐⭐

```bash
# 格式化代码
cargo fmt

# 检查格式
cargo fmt -- --check
```

---

## 选择决策树

### Web 应用开发

```text
需要 Web 应用？
├─ 是：需要极致性能？
│  ├─ 是 → actix-web
│  └─ 否：需要现代化设计？
│     ├─ 是 → axum
│     └─ 否 → rocket
└─ 否：跳过
```

### 数据库访问

```text
需要数据库？
├─ 是：需要异步？
│  ├─ 是 → sqlx
│  └─ 否：需要完整 ORM？
│     ├─ 是 → diesel
│     └─ 否 → sqlx (同步模式)
└─ 否：跳过
```

### 错误处理1

```text
开发库还是应用？
├─ 库 → thiserror
└─ 应用 → anyhow
```

---

## 成熟度评估

### 评估标准

| 等级 | 下载量 | GitHub Star | 文档 | 社区 | 生产使用 |
|------|--------|------------|------|------|---------|
| ⭐⭐⭐⭐⭐ | >100M | >10K | 完善 | 活跃 | 广泛 |
| ⭐⭐⭐⭐ | >50M | >5K | 良好 | 活跃 | 常见 |
| ⭐⭐⭐ | >10M | >1K | 可用 | 一般 | 少量 |
| ⭐⭐ | >1M | >500 | 基础 | 较少 | 实验 |
| ⭐ | <1M | <500 | 缺失 | 很少 | 早期 |

### 推荐库成熟度总览

| 类别 | 库名 | 成熟度 | 推荐度 |
|------|------|--------|--------|
| **序列化** | serde | ⭐⭐⭐⭐⭐ | 必选 |
| **异步运行时** | tokio | ⭐⭐⭐⭐⭐ | 必选 |
| **Web框架** | axum | ⭐⭐⭐⭐⭐ | 优先 |
| **Web框架** | actix-web | ⭐⭐⭐⭐⭐ | 备选 |
| **数据库** | sqlx | ⭐⭐⭐⭐⭐ | 优先 |
| **数据库** | diesel | ⭐⭐⭐⭐⭐ | 备选 |
| **HTTP客户端** | reqwest | ⭐⭐⭐⭐⭐ | 必选 |
| **CLI** | clap | ⭐⭐⭐⭐⭐ | 必选 |
| **日志** | tracing | ⭐⭐⭐⭐⭐ | 优先 |
| **错误处理** | anyhow | ⭐⭐⭐⭐⭐ | 必选 |
| **错误处理** | thiserror | ⭐⭐⭐⭐⭐ | 必选 |
| **测试** | criterion | ⭐⭐⭐⭐⭐ | 推荐 |
| **密码学** | rustls | ⭐⭐⭐⭐⭐ | 优先 |
| **并发** | rayon | ⭐⭐⭐⭐⭐ | 推荐 |

---

## 快速参考

### 新项目必备库

```toml
[dependencies]
# 核心
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tokio = { version = "1", features = ["full"] }
anyhow = "1.0"

# Web (选择一个)
axum = "0.7"
# 或 actix-web = "4"

# 数据库 (按需)
sqlx = { version = "0.8", features = ["runtime-tokio-rustls", "postgres"] }

# HTTP 客户端
reqwest = { version = "0.12", features = ["json"] }

# 日志
tracing = "0.1"
tracing-subscriber = "0.3"

# CLI (如果需要)
clap = { version = "4", features = ["derive"] }

[dev-dependencies]
criterion = "0.5"
```

### 学习路径

1. **基础** (1周)
   - serde, regex, rand, chrono

2. **异步编程** (2周)
   - tokio, async-std

3. **Web 开发** (3周)
   - axum/actix-web, sqlx, reqwest

4. **进阶** (4周+)
   - tracing, rayon, 特定领域库

---

## 总结

### 核心建议

1. **优先选择成熟度 ⭐⭐⭐⭐⭐ 的库**
2. **异步运行时首选 tokio**
3. **Web 框架 2025 年首选 axum**
4. **数据库访问优先 sqlx**
5. **错误处理：应用用 anyhow，库用 thiserror**
6. **可观测性首选 tracing**
7. **CLI 工具必用 clap**

### 持续更新

Rust 生态快速发展，建议:

- 定期查看 [crates.io](https://crates.io/) 趋势
- 关注 [This Week in Rust](https://this-week-in-rust.org/)
- 参考 [Awesome Rust](https://github.com/rust-unofficial/awesome-rust)
- 查看各库的 CHANGELOG

---

**文档版本**: 1.0  
**最后更新**: 2025-10-20  
**基于版本**: Rust 1.90  
**维护者**: C11 Middlewares Team

---

**相关文档**:

- [Rust 开源库分类体系](./RUST_CRATES_CLASSIFICATION_2025.md)
- [Rust 开源库成熟度评估矩阵](./RUST_CRATES_MATURITY_MATRIX_2025.md)
- [Rust 开源库生态索引](./RUST_CRATES_ECOSYSTEM_INDEX_2025.md)
- [完整文档索引](./00_MASTER_INDEX.md)
