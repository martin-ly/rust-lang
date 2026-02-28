# Rust 项目最佳实践指南

> **创建日期**: 2025-12-11
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
>
> **研究笔记写作最佳实践** → [research_notes/BEST_PRACTICES.md](../research_notes/BEST_PRACTICES.md)

---

## 📋 目录 {#-目录}

- [Rust 项目最佳实践指南](#rust-项目最佳实践指南)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [概述](#概述)
  - [1. 代码质量最佳实践](#1-代码质量最佳实践)
    - [1.1 所有权和借用](#11-所有权和借用)
    - [1.2 类型安全](#12-类型安全)
    - [1.3 错误处理](#13-错误处理)
  - [2. 性能优化最佳实践](#2-性能优化最佳实践)
    - [2.1 内存管理](#21-内存管理)
    - [2.2 迭代器优化](#22-迭代器优化)
    - [2.3 零成本抽象](#23-零成本抽象)
  - [3. 错误处理最佳实践](#3-错误处理最佳实践)
    - [3.1 自定义错误类型](#31-自定义错误类型)
    - [3.2 错误传播](#32-错误传播)
  - [4. 测试最佳实践](#4-测试最佳实践)
    - [4.1 单元测试](#41-单元测试)
    - [4.2 集成测试](#42-集成测试)
    - [4.3 文档测试](#43-文档测试)
  - [5. 文档最佳实践](#5-文档最佳实践)
    - [5.1 代码文档](#51-代码文档)
    - [5.2 README 文档](#52-readme-文档)
  - [6. 安全性最佳实践](#6-安全性最佳实践)
    - [6.1 输入验证](#61-输入验证)
    - [6.2 资源管理](#62-资源管理)
  - [7. 并发编程最佳实践](#7-并发编程最佳实践)
    - [7.1 线程安全](#71-线程安全)
    - [7.2 无锁编程](#72-无锁编程)
  - [8. 异步编程最佳实践](#8-异步编程最佳实践)
    - [8.1 Future 和 async/await](#81-future-和-asyncawait)
    - [8.2 错误处理](#82-错误处理)
  - [9. 模块设计最佳实践](#9-模块设计最佳实践)
    - [9.1 模块组织](#91-模块组织)
    - [9.2 可见性控制](#92-可见性控制)
  - [10. 项目组织最佳实践](#10-项目组织最佳实践)
    - [10.1 目录结构](#101-目录结构)
    - [10.2 特性标志](#102-特性标志)
  - [11. 工具使用](#11-工具使用)
    - [11.1 Clippy](#111-clippy)
    - [11.2 rustfmt](#112-rustfmt)
    - [11.3 依赖管理](#113-依赖管理)
  - [12. 性能监控](#12-性能监控)
    - [12.1 基准测试](#121-基准测试)
    - [12.2 性能分析](#122-性能分析)
  - [13. 代码示例](#13-代码示例)
    - [13.1 新类型模式](#131-新类型模式)
    - [13.2 Builder 模式](#132-builder-模式)
    - [13.3 状态机模式](#133-状态机模式)
  - [14. 使用场景](#14-使用场景)
    - [场景1: 新项目启动](#场景1-新项目启动)
    - [场景2: 代码审查](#场景2-代码审查)
    - [场景3: 性能优化](#场景3-性能优化)
    - [场景4: 团队代码规范](#场景4-团队代码规范)
  - [15. 形式化链接](#15-形式化链接)
  - [相关资源](#相关资源)
    - [官方资源](#官方资源)
    - [在线课程 (Coursera)](#在线课程-coursera)
    - [项目资源](#项目资源)

---

## 概述

本文档提供 Rust 项目开发的综合最佳实践，涵盖从代码编写到项目组织的各个方面，合并了项目级代码质量、性能、测试、文档、工具使用等主题。

**形式化引用**：T-OW2、T-BR1、T-TY3、SEND-T1、SYNC-T1。综合见 [formal_methods](../research_notes/formal_methods/README.md)、[THEOREM_RUST_EXAMPLE_MAPPING](../research_notes/THEOREM_RUST_EXAMPLE_MAPPING.md)。

---

## 1. 代码质量最佳实践

### 1.1 所有权和借用

**✅ 最佳实践**:

```rust
// 优先使用引用而非所有权转移
fn process_data(data: &[i32]) -> i32 {
    data.iter().sum()
}

// 使用切片而非 Vec 作为参数
fn find_max(slice: &[i32]) -> Option<&i32> {
    slice.iter().max()
}

// 使用 Arc 共享不可变数据
use std::sync::Arc;
let data = Arc::new(vec![1, 2, 3]);
let data_clone = Arc::clone(&data);
```

**❌ 避免**: 不必要的所有权转移、不必要的 clone

```rust
// 不好的例子
fn bad_process(data: Vec<i32>) -> i32 {
    data.iter().sum() // 所有权转移不必要
}

// 好的例子
fn good_process(data: &[i32]) -> i32 {
    data.iter().sum()
}
```

### 1.2 类型安全

**✅ 最佳实践**: 使用新类型模式、枚举而非魔法数字、Option 而非 null

```rust
// 新类型模式
pub struct UserId(u64);
pub struct OrderId(u64);

impl UserId {
    pub fn new(id: u64) -> Self {
        UserId(id)
    }
}

// 枚举而非魔法数字
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Pending,
    Processing,
    Completed,
    Failed,
}

// Option 而非 null
fn find_user(id: UserId) -> Option<User> {
    // 实现
    None
}
```

### 1.3 错误处理

**✅ 最佳实践**: 使用 Result 和 ? 操作符、自定义错误类型、有意义的错误信息

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("IO 错误: {0}")]
    Io(#[from] std::io::Error),

    #[error("解析错误: {message}")]
    Parse { message: String, line: u32 },

    #[error("无效参数: {0}")]
    InvalidArg(String),
}

pub type Result<T> = std::result::Result<T, AppError>;

fn read_config(path: &str) -> Result<Config> {
    let content = std::fs::read_to_string(path)?; // ? 操作符传播错误
    let config: Config = serde_json::from_str(&content)
        .map_err(|e| AppError::Parse {
            message: e.to_string(),
            line: 0,
        })?;
    Ok(config)
}
```

---

## 2. 性能优化最佳实践

### 2.1 内存管理

**✅ 最佳实践**: Vec::with_capacity 预分配、Box 大结构体、Cow 避免克隆

```rust
// 预分配容量
let mut vec = Vec::with_capacity(1000);
for i in 0..1000 {
    vec.push(i); // 避免重复分配
}

// Box 大结构体
struct LargeData {
    data: Box<[u8; 1024 * 1024]>, // 1MB 在堆上
}

// Cow 避免克隆
use std::borrow::Cow;

fn process_string(s: Cow<str>) -> String {
    match s {
        Cow::Borrowed(s) => s.to_uppercase(),
        Cow::Owned(s) => s.to_uppercase(),
    }
}
```

### 2.2 迭代器优化

**✅ 最佳实践**: 迭代器链、collect 指定类型、enumerate 获取索引

```rust
// 迭代器链 - 零成本抽象
let sum: i32 = data.iter()
    .filter(|&&x| x > 0)
    .map(|x| x * 2)
    .sum();

// 单次遍历获取多个统计值
let (sum, max, min) = data.iter().fold(
    (0i32, i32::MIN, i32::MAX),
    |(sum, max, min), &x| (sum + x, max.max(x), min.min(x))
);

// 使用 enumerate
for (idx, value) in data.iter().enumerate() {
    println!("{}: {}", idx, value);
}
```

### 2.3 零成本抽象

**✅ 最佳实践**: 泛型、#[inline] 关键路径

```rust
// 泛型实现零成本抽象
fn process<T: AsRef<[u8]>>(data: T) -> u32 {
    data.as_ref().iter().map(|&b| b as u32).sum()
}

// 内联小函数
#[inline]
fn hot_path(x: i32) -> i32 {
    x * 2 + 1
}

// 标记冷路径
#[cold]
fn error_handler() {
    // 错误处理路径，很少执行
}
```

---

## 3. 错误处理最佳实践

### 3.1 自定义错误类型

**✅ 最佳实践**: 实现 Error + Display、thiserror 等

```rust
use thiserror::Error;
use std::fmt;

#[derive(Error, Debug)]
pub enum DatabaseError {
    #[error("连接失败: {0}")]
    ConnectionFailed(String),

    #[error("查询错误: {0}")]
    QueryError(#[from] sqlx::Error),

    #[error("记录未找到: id={0}")]
    NotFound(u64),
}

// 手动实现 Error trait
#[derive(Debug)]
pub struct CustomError {
    message: String,
    code: u32,
}

impl fmt::Display for CustomError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}", self.code, self.message)
    }
}

impl std::error::Error for CustomError {}
```

### 3.2 错误传播

**✅ 最佳实践**: ? 操作符、map_err 转换

```rust
fn process_file(path: &str) -> Result<Vec<u8>, AppError> {
    // ? 操作符自动转换错误类型
    let content = std::fs::read(path)?;

    // map_err 自定义错误信息
    let parsed = parse_data(&content)
        .map_err(|e| AppError::Parse {
            message: format!("解析 {} 失败: {}", path, e),
            line: 0,
        })?;

    Ok(parsed)
}
```

---

## 4. 测试最佳实践

### 4.1 单元测试

**✅ 最佳实践**: #[cfg(test)]、assert_eq、#[should_panic]

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
    }

    #[test]
    #[should_panic(expected = "Division by zero")]
    fn test_divide_by_zero() {
        divide(10, 0);
    }

    #[test]
    fn test_with_result() -> Result<(), String> {
        let result = some_operation()?;
        assert_eq!(result, expected);
        Ok(())
    }
}
```

### 4.2 集成测试

**✅ 最佳实践**: tests/ 目录、完整工作流测试

```rust
// tests/integration_test.rs
use my_crate::*;

#[test]
fn test_complete_workflow() {
    // 设置
    let config = Config::default();
    let mut app = Application::new(config);

    // 执行
    app.process_data("input").unwrap();

    // 验证
    assert_eq!(app.status(), Status::Completed);
}

#[test]
fn test_concurrent_access() {
    use std::thread;

    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let mut num = data.lock().unwrap();
            *num += 1;
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(*data.lock().unwrap(), 10);
}
```

### 4.3 文档测试

**✅ 最佳实践**: /// 示例块、可运行示例

```rust
/// 计算两个数的和
///
/// # Examples
///
/// ```
/// use my_crate::add;
///
/// assert_eq!(add(2, 3), 5);
/// ```
///
/// # Errors
///
/// 如果输入溢出，将返回错误
///
/// # Safety
///
/// 此函数不涉及 unsafe 操作
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

---

## 5. 文档最佳实践

### 5.1 代码文档

**✅ 最佳实践**: Arguments、Returns、Examples 块

```rust
/// 处理用户输入并返回处理结果
///
/// # Arguments
///
/// * `input` - 用户输入字符串，不能为空
/// * `options` - 处理选项
///
/// # Returns
///
/// 成功时返回 `Ok(ProcessResult)`，包含处理后的数据
/// 失败时返回 `Err(ProcessError)`，包含错误详情
///
/// # Examples
///
/// ```rust
/// use my_crate::{process, Options};
///
/// let options = Options::default();
/// let result = process("hello", &options)?;
/// # Ok::<(), my_crate::ProcessError>(())
/// ```
///
/// # Panics
///
/// 如果 `input` 为空字符串，将 panic
pub fn process(input: &str, options: &Options) -> Result<ProcessResult, ProcessError> {
    // 实现
}
```

### 5.2 README 文档

**✅ 最佳实践**: 项目概述、快速开始、特性列表、贡献指南

```markdown
        # 项目名称

        [![Crates.io](https://img.shields.io/crates/v/my_crate)](https://crates.io/crates/my_crate)
        [![Documentation](https://docs.rs/my_crate/badge.svg)](https://docs.rs/my_crate)

        > 项目一句话描述

        ## 特性

        - 特性 1
        - 特性 2
        - 特性 3

        ## 快速开始

        ```bash
        cargo add my_crate
        ```

        ```rust
        use my_crate::Client;

        let client = Client::new();
        let result = client.do_something().await?;
        ```

        ## 文档

        - [API 文档](https://docs.rs/my_crate)
        - [用户指南](https://my_crate.github.io/guide)

```

---

## 6. 安全性最佳实践

### 6.1 输入验证

**✅ 最佳实践**: 空值检查、长度限制、类型校验

```rust
use validator::{Validate, ValidationError};

#[derive(Debug, Validate)]
pub struct UserInput {
    #[validate(length(min = 1, max = 100))]
    pub name: String,

    #[validate(email)]
    pub email: String,

    #[validate(range(min = 18, max = 150))]
    pub age: u8,
}

fn process_input(input: &UserInput) -> Result<(), ValidationError> {
    input.validate()?;
    // 继续处理
    Ok(())
}
```

### 6.2 资源管理

**✅ 最佳实践**: RAII、Drop 实现、避免泄漏

```rust
pub struct ResourceHandle {
    handle: *mut c_void,
}

impl ResourceHandle {
    pub fn new() -> Option<Self> {
        let handle = unsafe { create_resource() };
        if handle.is_null() {
            None
        } else {
            Some(ResourceHandle { handle })
        }
    }
}

impl Drop for ResourceHandle {
    fn drop(&mut self) {
        unsafe {
            destroy_resource(self.handle);
        }
    }
}

// RAII 守卫模式
pub struct LockGuard<'a> {
    data: &'a mut Data,
}

impl<'a> Drop for LockGuard<'a> {
    fn drop(&mut self) {
        self.data.unlock();
    }
}
```

---

## 7. 并发编程最佳实践

### 7.1 线程安全

**✅ 最佳实践**: Arc + Mutex、通道优先于共享可变状态

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// Arc + Mutex 共享状态
let data = Arc::new(Mutex::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let data = Arc::clone(&data);
    let handle = thread::spawn(move || {
        let mut num = data.lock().unwrap();
        *num += 1;
    });
    handles.push(handle);
}

for handle in handles {
    handle.join().unwrap();
}

// 使用通道
use std::sync::mpsc;

let (tx, rx) = mpsc::channel();

thread::spawn(move || {
    tx.send(42).unwrap();
});

let received = rx.recv().unwrap();
```

### 7.2 无锁编程

**✅ 最佳实践**: AtomicUsize 等原子类型、Ordering 选型

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

fn increment() {
    COUNTER.fetch_add(1, Ordering::Relaxed);
}

fn get_count() -> usize {
    COUNTER.load(Ordering::Acquire)
}

// 使用 Ordering 规则
// - Relaxed: 不需要同步，只保证原子性
// - Acquire/Release: 用于生产者-消费者模式
// - SeqCst: 最严格的全序保证
```

---

## 8. 异步编程最佳实践

### 8.1 Future 和 async/await

**✅ 最佳实践**: async fn、.await、避免阻塞

```rust
use tokio::time::{sleep, Duration};

async fn fetch_data(url: &str) -> Result<String, reqwest::Error> {
    let response = reqwest::get(url).await?;
    let text = response.text().await?;
    Ok(text)
}

async fn process_concurrently(urls: Vec<String>) -> Vec<Result<String, reqwest::Error>> {
    use futures::future::join_all;

    let futures: Vec<_> = urls.iter()
        .map(|url| fetch_data(url))
        .collect();

    join_all(futures).await
}

// 避免在异步代码中阻塞
async fn cpu_intensive_task(data: Vec<u8>) -> Vec<u8> {
    tokio::task::spawn_blocking(move || {
        // CPU 密集型操作在线程池中执行
        heavy_computation(data)
    })
    .await
    .unwrap()
}
```

### 8.2 错误处理

**✅ 最佳实践**: Result 传播、`Box<dyn Error>`

```rust
use std::error::Error;

async fn complex_operation() -> Result<(), Box<dyn Error + Send + Sync>> {
    let data = fetch_data().await?;
    let processed = process(data).await?;
    save(processed).await?;
    Ok(())
}

// 或者使用 thiserror
#[derive(Debug, thiserror::Error)]
enum AsyncError {
    #[error("网络错误: {0}")]
    Network(#[from] reqwest::Error),

    #[error("超时")]
    Timeout,
}
```

---

## 9. 模块设计最佳实践

### 9.1 模块组织

**✅ 最佳实践**: pub mod、分层结构

```rust
// lib.rs
pub mod core {
    pub mod engine;
    pub mod types;
}

pub mod utils {
    pub mod helpers;
    mod internal; // 私有模块
}

// 使用 pub use 重新导出
pub use core::engine::Engine;
pub use core::types::{Config, Result};
```

### 9.2 可见性控制

**✅ 最佳实践**: pub、pub(crate)、pub(super)

```rust
mod inner {
    // 私有项
    fn private_fn() {}

    // 当前 crate 可见
    pub(crate) fn crate_fn() {}

    // 父模块可见
    pub(super) fn super_fn() {}

    // 完全公开
    pub fn public_fn() {}
}
```

---

## 10. 项目组织最佳实践

### 10.1 目录结构

**✅ 最佳实践**: src/、tests/、benches/、examples/

```text
my_project/
├── Cargo.toml
├── README.md
├── src/
│   ├── lib.rs          # 库入口
│   ├── main.rs         # 可执行文件入口
│   ├── core/
│   │   ├── mod.rs
│   │   ├── engine.rs
│   │   └── types.rs
│   └── utils/
│       ├── mod.rs
│       └── helpers.rs
├── tests/              # 集成测试
│   └── integration_test.rs
├── benches/            # 基准测试
│   └── bench.rs
├── examples/           # 示例代码
│   └── simple.rs
└── docs/               # 文档
    └── guide.md
```

### 10.2 特性标志

**✅ 最佳实践**: [features]、default、可选依赖

```toml
[features]
default = ["std", "serde"]
std = []
serde = ["dep:serde", "dep:serde_json"]
async = ["dep:tokio"]
full = ["std", "serde", "async"]

[dependencies]
serde = { version = "1.0", optional = true }
serde_json = { version = "1.0", optional = true }
tokio = { version = "1.0", features = ["full"], optional = true }

[dev-dependencies]
criterion = "0.5"
```

```rust
// 条件编译
#[cfg(feature = "serde")]
use serde::{Serialize, Deserialize};

#[cfg(feature = "serde")]
#[derive(Serialize, Deserialize)]
pub struct Config {
    // ...
}
```

---

## 11. 工具使用

### 11.1 Clippy

```bash
# 运行 clippy
cargo clippy

# 更严格的检查
cargo clippy -- -W clippy::all

# 自动修复
cargo clippy --fix

# 检查特定 lint
cargo clippy -- -D warnings
```

### 11.2 rustfmt

```bash
# 格式化代码
cargo fmt

# 检查格式
cargo fmt -- --check
```

### 11.3 依赖管理

```toml
[dependencies]
# 版本范围
tokio = { version = "1.0", features = ["rt", "net"] }
serde = { workspace = true }

# 可选依赖
async-trait = { version = "0.1", optional = true }

# 开发依赖
[dev-dependencies]
tokio-test = "0.4"
mockall = "0.12"
```

---

## 12. 性能监控

### 12.1 基准测试

**✅ 最佳实践**: criterion、benches/ 目录

```rust
// benches/my_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

### 12.2 性能分析

```bash
# 使用 perf (Linux)
perf record --call-graph=dwarf ./target/release/my_app
perf report

# 生成火焰图
cargo install flamegraph
cargo flamegraph --bin my_app

# 使用 valgrind
cargo install cargo-valgrind
cargo valgrind --bin my_app
```

---

## 13. 代码示例

### 13.1 新类型模式

```rust
use std::fmt;
use std::str::FromStr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UserId(u64);

impl UserId {
    pub fn new(id: u64) -> Self {
        UserId(id)
    }

    pub fn as_u64(&self) -> u64 {
        self.0
    }
}

impl fmt::Display for UserId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FromStr for UserId {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<u64>()
            .map(UserId::new)
            .map_err(|_| ParseError::new("无效的用户ID"))
    }
}
```

### 13.2 Builder 模式

```rust
#[derive(Debug, Clone)]
pub struct Config {
    host: String,
    port: u16,
    timeout: Duration,
    retries: u32,
}

impl Config {
    pub fn builder() -> ConfigBuilder {
        ConfigBuilder::default()
    }
}

#[derive(Debug, Default)]
pub struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
    timeout: Option<Duration>,
    retries: Option<u32>,
}

impl ConfigBuilder {
    pub fn host(mut self, host: impl Into<String>) -> Self {
        self.host = Some(host.into());
        self
    }

    pub fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }

    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    pub fn retries(mut self, retries: u32) -> Self {
        self.retries = Some(retries);
        self
    }

    pub fn build(self) -> Result<Config, ConfigError> {
        Ok(Config {
            host: self.host.ok_or(ConfigError::MissingField("host"))?,
            port: self.port.unwrap_or(8080),
            timeout: self.timeout.unwrap_or(Duration::from_secs(30)),
            retries: self.retries.unwrap_or(3),
        })
    }
}

// 使用
let config = Config::builder()
    .host("localhost")
    .port(3000)
    .timeout(Duration::from_secs(60))
    .retries(5)
    .build()?;
```

### 13.3 状态机模式

```rust
// 状态标记类型
pub struct Idle;
pub struct Running {
    start_time: Instant,
}
pub struct Stopped {
    duration: Duration,
}

// 状态机
pub struct StateMachine<State> {
    state: State,
}

impl StateMachine<Idle> {
    pub fn new() -> Self {
        StateMachine { state: Idle }
    }

    pub fn start(self) -> StateMachine<Running> {
        StateMachine {
            state: Running {
                start_time: Instant::now(),
            },
        }
    }
}

impl StateMachine<Running> {
    pub fn stop(self) -> StateMachine<Stopped> {
        let duration = self.state.start_time.elapsed();
        StateMachine {
            state: Stopped { duration },
        }
    }

    pub fn elapsed(&self) -> Duration {
        self.state.start_time.elapsed()
    }
}

impl StateMachine<Stopped> {
    pub fn duration(&self) -> Duration {
        self.state.duration
    }

    pub fn restart(self) -> StateMachine<Running> {
        StateMachine {
            state: Running {
                start_time: Instant::now(),
            },
        }
    }
}

// 使用
let machine = StateMachine::new();
let running = machine.start();
// ... 一些操作
let stopped = running.stop();
println!("运行时长: {:?}", stopped.duration());
```

---

## 14. 使用场景

### 场景1: 新项目启动

为新 Rust 项目建立最佳实践基线：

1. 参考 [项目组织最佳实践](#10-项目组织最佳实践) 建立目录结构
2. 配置 [Clippy](#111-clippy) 和 [rustfmt](#112-rustfmt)
3. 设置 [CI/CD 测试](#41-单元测试) 流程

### 场景2: 代码审查

使用本指南进行代码审查：

- 检查所有权和借用模式（[1.1 节](#11-所有权和借用)）
- 验证错误处理策略（[3. 错误处理](#3-错误处理最佳实践)）
- 评估性能优化机会（[2. 性能优化](#2-性能优化最佳实践)）

### 场景3: 性能优化

系统性地优化 Rust 代码性能：

1. 使用 [Criterion](#121-基准测试) 建立性能基准
2. 应用 [内存优化](#21-内存管理) 技巧
3. 实施 [迭代器优化](#22-迭代器优化)
4. 参考 [PERFORMANCE_TUNING_GUIDE.md](./PERFORMANCE_TUNING_GUIDE.md) 深度优化

### 场景4: 团队代码规范

建立团队统一的 Rust 编码规范：

- 定义错误处理模式（[3. 错误处理](#3-错误处理最佳实践)）
- 约定文档标准（[5. 文档](#5-文档最佳实践)）
- 设定测试覆盖率目标（[4. 测试](#4-测试最佳实践)）

---

## 15. 形式化链接

| 链接类型 | 目标文档 |
| :--- | :--- |
| **核心模块** | [C01 所有权](../../crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md) |
| :--- | :--- |
| :--- | :--- |
| :--- | :--- |
| **高级主题** | [C05 线程](../../crates/c05_threads/docs/00_MASTER_INDEX.md) |
| :--- | :--- |
| **相关指南** | [PERFORMANCE_TUNING_GUIDE.md](./PERFORMANCE_TUNING_GUIDE.md) |
| :--- | :--- |
| :--- | :--- |
| :--- | :--- |

---

## 相关资源

### 官方资源

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Rust API 指南](https://rust-lang.github.io/api-guidelines/)
- [Rust 性能书](https://nnethercote.github.io/perf-book/)
- [研究笔记最佳实践](../research_notes/BEST_PRACTICES.md) - 研究笔记写作规范

### 在线课程 (Coursera)

- [Rust Programming Specialization](https://www.coursera.org/specializations/rust-programming) (Duke University) - Rust基础、数据结构、并发编程
- [Programming in Rust](https://www.coursera.org/learn/programming-in-rust) (University of Colorado Boulder) - Rust编程基础
- Practical System Programming in Rust (Coursera Project) - 系统编程实践

> **提示**: 这些 Coursera 课程提供了结构化的学习路径，可作为本文档最佳实践的补充学习资源。

### 项目资源

- [C01 所有权](../../crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md)
- [C02 类型系统](../../crates/c02_type_system/docs/00_MASTER_INDEX.md)
- [C05 线程与并发](../../crates/c05_threads/docs/00_MASTER_INDEX.md)
- [C06 异步](../../crates/c06_async/docs/00_MASTER_INDEX.md)

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 持续更新
