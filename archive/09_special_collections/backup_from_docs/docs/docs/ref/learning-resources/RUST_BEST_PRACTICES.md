# 🦀 Rust最佳实践指南


## 📊 目录

- [📋 目录](#目录)
- [🏗️ 代码组织](#️-代码组织)
  - [模块结构](#模块结构)
  - [模块设计原则](#模块设计原则)
  - [示例代码组织](#示例代码组织)
- [🏷️ 命名规范](#️-命名规范)
  - [基本命名规则](#基本命名规则)
  - [命名示例](#命名示例)
  - [特殊命名约定](#特殊命名约定)
- [⚠️ 错误处理](#️-错误处理)
  - [错误类型设计](#错误类型设计)
  - [错误处理最佳实践](#错误处理最佳实践)
  - [错误恢复策略](#错误恢复策略)
- [⚡ 性能优化](#性能优化)
  - [内存优化](#内存优化)
  - [字符串优化](#字符串优化)
  - [算法优化](#算法优化)
- [🔒 安全编程](#安全编程)
  - [输入验证](#输入验证)
  - [安全的数据处理](#安全的数据处理)
  - [内存安全](#内存安全)
- [🧪 测试策略](#测试策略)
  - [单元测试](#单元测试)
  - [集成测试](#集成测试)
  - [属性测试](#属性测试)
  - [基准测试](#基准测试)
- [📚 文档编写](#文档编写)
  - [文档注释](#文档注释)
  - [模块文档](#模块文档)
- [📦 依赖管理](#依赖管理)
  - [Cargo.toml最佳实践](#cargotoml最佳实践)
  - [依赖选择原则](#依赖选择原则)
  - [依赖更新策略](#依赖更新策略)
- [🔄 并发编程](#并发编程)
  - [线程安全设计](#线程安全设计)
  - [异步编程模式](#异步编程模式)
- [🚀 异步编程](#异步编程)
  - [异步函数设计](#异步函数设计)
  - [异步并发模式](#异步并发模式)
- [🎯 总结](#总结)
  - [关键要点](#关键要点)
  - [持续改进](#持续改进)


**创建时间**: 2025年9月25日
**版本**: 1.0.0
**适用对象**: 所有Rust开发者

---

## 📋 目录

- [🦀 Rust最佳实践指南](#-rust最佳实践指南)
  - [📋 目录](#-目录)
    - [🏗️ 代码组织](#️-代码组织)
      - [模块结构](#模块结构)
      - [模块设计原则](#模块设计原则)
      - [示例代码组织](#示例代码组织)
    - [🏷️ 命名规范](#️-命名规范)
      - [基本命名规则](#基本命名规则)
      - [命名示例](#命名示例)
      - [特殊命名约定](#特殊命名约定)
    - [⚠️ 错误处理](#️-错误处理)

---

## 🏗️ 代码组织

### 模块结构

```rust
// 推荐的模块结构
src/
├── lib.rs          // 库的入口点
├── main.rs         // 二进制入口点
├── error.rs        // 错误定义
├── config.rs       // 配置管理
├── utils.rs        // 工具函数
├── types.rs        // 类型定义
├── traits.rs       // trait定义
├── macros.rs       // 宏定义
├── tests/          // 集成测试
│   ├── common.rs   // 测试工具
│   └── integration_tests.rs
└── benches/        // 基准测试
    └── benchmark.rs
```

### 模块设计原则

- **单一职责**: 每个模块应该只有一个职责
- **低耦合**: 模块之间应该尽可能独立
- **高内聚**: 模块内部应该紧密相关
- **清晰接口**: 模块接口应该清晰明确

### 示例代码组织

```rust
// lib.rs - 库的入口点
pub mod error;
pub mod config;
pub mod types;
pub mod traits;

pub use error::{Error, Result};
pub use config::Config;
pub use types::*;

// error.rs - 错误定义
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Invalid input: {message}")]
    InvalidInput { message: String },

    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    #[error("Parse error: {0}")]
    ParseError(#[from] serde_json::Error),
}

pub type Result<T> = std::result::Result<T, Error>;

// config.rs - 配置管理
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    pub host: String,
    pub port: u16,
    pub database_url: String,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            host: "127.0.0.1".to_string(),
            port: 8080,
            database_url: "sqlite://database.db".to_string(),
        }
    }
}
```

---

## 🏷️ 命名规范

### 基本命名规则

- **snake_case**: 变量、函数、模块名
- **PascalCase**: 类型、trait、枚举名
- **SCREAMING_SNAKE_CASE**: 常量、静态变量
- **T**: 泛型类型参数
- **U, V**: 多个泛型类型参数

### 命名示例

```rust
// 变量和函数
let user_name = "john_doe";
let max_retry_count = 3;

fn calculate_total_price(items: &[Item]) -> f64 {
    // 实现
}

// 类型和trait
struct UserAccount {
    id: u32,
    name: String,
}

trait DatabaseConnection {
    fn connect(&self) -> Result<()>;
}

// 枚举
enum HttpStatusCode {
    Ok = 200,
    NotFound = 404,
    InternalServerError = 500,
}

// 常量
const MAX_BUFFER_SIZE: usize = 1024;
const DEFAULT_TIMEOUT: u64 = 30;

// 泛型
struct Container<T> {
    items: Vec<T>,
}

fn process_items<T, U>(items: Vec<T>) -> Vec<U> {
    // 实现
}
```

### 特殊命名约定

```rust
// 构造函数
impl User {
    pub fn new(name: String, email: String) -> Self {
        Self { name, email }
    }

    pub fn from_json(data: &str) -> Result<Self> {
        // 实现
    }
}

// 转换方法
impl User {
    pub fn to_json(&self) -> Result<String> {
        // 实现
    }

    pub fn into_bytes(self) -> Vec<u8> {
        // 实现
    }
}

// 验证方法
impl User {
    pub fn is_valid(&self) -> bool {
        // 实现
    }

    pub fn validate_email(&self) -> Result<()> {
        // 实现
    }
}
```

---

## ⚠️ 错误处理

### 错误类型设计

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("Invalid input: {message}")]
    InvalidInput { message: String },

    #[error("Network error: {0}")]
    NetworkError(#[from] reqwest::Error),

    #[error("Database error: {0}")]
    DatabaseError(#[from] sqlx::Error),

    #[error("Authentication failed: {reason}")]
    AuthenticationFailed { reason: String },

    #[error("Internal server error: {0}")]
    InternalError(#[from] anyhow::Error),
}

pub type Result<T> = std::result::Result<T, AppError>;
```

### 错误处理最佳实践

```rust
// 使用?操作符进行错误传播
fn process_user_data(data: &str) -> Result<User> {
    let user: User = serde_json::from_str(data)?;
    user.validate()?;
    Ok(user)
}

// 使用map_err进行错误转换
fn parse_config(path: &str) -> Result<Config> {
    std::fs::read_to_string(path)
        .map_err(|e| AppError::InvalidInput {
            message: format!("Failed to read config file: {}", e),
        })?;
    // 继续处理
}

// 使用anyhow进行快速原型
use anyhow::Result;

fn quick_prototype() -> Result<()> {
    let data = std::fs::read_to_string("data.txt")?;
    let parsed: Value = serde_json::from_str(&data)?;
    println!("{:?}", parsed);
    Ok(())
}

// 自定义错误处理
fn handle_error(error: AppError) {
    match error {
        AppError::InvalidInput { message } => {
            eprintln!("Invalid input: {}", message);
        }
        AppError::NetworkError(e) => {
            eprintln!("Network error: {}", e);
        }
        AppError::DatabaseError(e) => {
            eprintln!("Database error: {}", e);
        }
        _ => {
            eprintln!("Unexpected error: {}", error);
        }
    }
}
```

### 错误恢复策略

```rust
// 重试机制
async fn fetch_with_retry(url: &str, max_retries: u32) -> Result<String> {
    let mut last_error = None;

    for attempt in 1..=max_retries {
        match reqwest::get(url).await {
            Ok(response) => {
                return response.text().await.map_err(AppError::from);
            }
            Err(e) => {
                last_error = Some(e);
                if attempt < max_retries {
                    tokio::time::sleep(tokio::time::Duration::from_secs(2_u64.pow(attempt))).await;
                }
            }
        }
    }

    Err(AppError::NetworkError(last_error.unwrap()))
}

// 降级处理
fn get_user_preferences(user_id: u32) -> Result<UserPreferences> {
    match database.get_preferences(user_id).await {
        Ok(prefs) => Ok(prefs),
        Err(_) => {
            // 降级到默认设置
            Ok(UserPreferences::default())
        }
    }
}
```

---

## ⚡ 性能优化

### 内存优化

```rust
// 使用String::with_capacity预分配内存
fn build_large_string(items: &[String]) -> String {
    let mut result = String::with_capacity(items.len() * 10);
    for item in items {
        result.push_str(item);
        result.push('\n');
    }
    result
}

// 使用Vec::with_capacity预分配内存
fn process_large_dataset(size: usize) -> Vec<u32> {
    let mut result = Vec::with_capacity(size);
    for i in 0..size {
        result.push(i as u32);
    }
    result
}

// 使用Box减少栈内存使用
struct LargeStruct {
    data: [u8; 1024],
}

fn create_large_struct() -> Box<LargeStruct> {
    Box::new(LargeStruct {
        data: [0; 1024],
    })
}
```

### 字符串优化

```rust
// 使用StringBuilder模式
fn build_query(conditions: &[String]) -> String {
    let mut query = String::new();
    query.push_str("SELECT * FROM users WHERE ");

    for (i, condition) in conditions.iter().enumerate() {
        if i > 0 {
            query.push_str(" AND ");
        }
        query.push_str(condition);
    }

    query
}

// 使用format!宏进行字符串格式化
fn format_user_info(user: &User) -> String {
    format!("User: {} (ID: {})", user.name, user.id)
}

// 使用Cow进行零拷贝字符串处理
use std::borrow::Cow;

fn process_text(text: &str) -> Cow<str> {
    if text.contains("error") {
        Cow::Owned(text.replace("error", "ERROR"))
    } else {
        Cow::Borrowed(text)
    }
}
```

### 算法优化

```rust
// 使用迭代器进行函数式编程
fn calculate_statistics(numbers: &[f64]) -> (f64, f64, f64) {
    let sum: f64 = numbers.iter().sum();
    let count = numbers.len() as f64;
    let mean = sum / count;

    let variance: f64 = numbers
        .iter()
        .map(|&x| (x - mean).powi(2))
        .sum::<f64>() / count;

    let std_dev = variance.sqrt();

    (mean, variance, std_dev)
}

// 使用并行迭代器进行并行处理
use rayon::prelude::*;

fn parallel_process(items: &[Item]) -> Vec<ProcessedItem> {
    items
        .par_iter()
        .map(|item| process_item(item))
        .collect()
}

// 使用缓存避免重复计算
use std::collections::HashMap;

struct Fibonacci {
    cache: HashMap<u32, u64>,
}

impl Fibonacci {
    fn new() -> Self {
        Self {
            cache: HashMap::new(),
        }
    }

    fn calculate(&mut self, n: u32) -> u64 {
        if let Some(&result) = self.cache.get(&n) {
            return result;
        }

        let result = match n {
            0 => 0,
            1 => 1,
            _ => self.calculate(n - 1) + self.calculate(n - 2),
        };

        self.cache.insert(n, result);
        result
    }
}
```

---

## 🔒 安全编程

### 输入验证

```rust
use validator::{Validate, ValidationError};

#[derive(Debug, Validate)]
struct UserRegistration {
    #[validate(email)]
    email: String,

    #[validate(length(min = 8, max = 100))]
    password: String,

    #[validate(length(min = 1, max = 50))]
    name: String,

    #[validate(range(min = 18, max = 120))]
    age: u32,
}

fn validate_user_input(data: &str) -> Result<UserRegistration> {
    let user: UserRegistration = serde_json::from_str(data)?;
    user.validate().map_err(|e| AppError::InvalidInput {
        message: format!("Validation failed: {}", e),
    })?;
    Ok(user)
}
```

### 安全的数据处理

```rust
// 使用安全的字符串处理
fn sanitize_input(input: &str) -> String {
    input
        .chars()
        .filter(|c| c.is_alphanumeric() || c.is_whitespace())
        .collect()
}

// 使用安全的文件路径处理
use std::path::{Path, PathBuf};

fn safe_file_path(base: &Path, filename: &str) -> Result<PathBuf> {
    let path = base.join(filename);

    // 检查路径遍历攻击
    if path.starts_with(base) {
        Ok(path)
    } else {
        Err(AppError::InvalidInput {
            message: "Invalid file path".to_string(),
        })
    }
}

// 使用安全的网络请求
async fn safe_http_request(url: &str) -> Result<String> {
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(30))
        .user_agent("MyApp/1.0")
        .build()?;

    let response = client.get(url).send().await?;

    if response.status().is_success() {
        Ok(response.text().await?)
    } else {
        Err(AppError::NetworkError(reqwest::Error::from(
            response.error_for_status().unwrap_err()
        )))
    }
}
```

### 内存安全

```rust
// 使用Arc进行线程安全的引用计数
use std::sync::Arc;
use std::thread;

struct SharedData {
    value: u32,
}

fn share_data_across_threads() {
    let data = Arc::new(SharedData { value: 42 });

    let handles: Vec<_> = (0..4)
        .map(|i| {
            let data = Arc::clone(&data);
            thread::spawn(move || {
                println!("Thread {}: value = {}", i, data.value);
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }
}

// 使用Mutex进行线程安全的数据访问
use std::sync::{Arc, Mutex};

struct ThreadSafeCounter {
    value: Mutex<u32>,
}

impl ThreadSafeCounter {
    fn new() -> Self {
        Self {
            value: Mutex::new(0),
        }
    }

    fn increment(&self) -> Result<u32> {
        let mut value = self.value.lock().map_err(|_| AppError::InternalError(
            anyhow::anyhow!("Failed to acquire lock")
        ))?;
        *value += 1;
        Ok(*value)
    }
}
```

---

## 🧪 测试策略

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_user_creation() {
        let user = User::new("John Doe".to_string(), "john@example.com".to_string());
        assert_eq!(user.name, "John Doe");
        assert_eq!(user.email, "john@example.com");
    }

    #[test]
    fn test_user_validation() {
        let valid_user = User {
            name: "John Doe".to_string(),
            email: "john@example.com".to_string(),
        };
        assert!(valid_user.is_valid());

        let invalid_user = User {
            name: "".to_string(),
            email: "invalid-email".to_string(),
        };
        assert!(!invalid_user.is_valid());
    }

    #[test]
    fn test_error_handling() {
        let result = process_user_data("invalid json");
        assert!(result.is_err());

        match result.unwrap_err() {
            AppError::InvalidInput { message } => {
                assert!(message.contains("invalid"));
            }
            _ => panic!("Expected InvalidInput error"),
        }
    }
}
```

### 集成测试

```rust
// tests/integration_tests.rs
use my_crate::*;

#[tokio::test]
async fn test_api_endpoint() {
    let app = create_test_app().await;
    let client = reqwest::Client::new();

    let response = client
        .get("http://localhost:3000/api/health")
        .send()
        .await
        .unwrap();

    assert_eq!(response.status(), 200);

    let body: serde_json::Value = response.json().await.unwrap();
    assert_eq!(body["status"], "healthy");
}

#[tokio::test]
async fn test_database_operations() {
    let db = create_test_database().await;

    let user = User {
        name: "Test User".to_string(),
        email: "test@example.com".to_string(),
    };

    let saved_user = db.save_user(user).await.unwrap();
    assert_eq!(saved_user.name, "Test User");

    let retrieved_user = db.get_user(saved_user.id).await.unwrap();
    assert_eq!(retrieved_user.name, "Test User");
}
```

### 属性测试

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_string_processing(s in "\\PC*") {
        let result = process_string(&s);
        assert!(result.len() <= s.len());
    }

    #[test]
    fn test_numeric_calculations(a in 0..1000i32, b in 0..1000i32) {
        let result = calculate(a, b);
        assert!(result >= 0);
    }
}
```

### 基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_string_processing(c: &mut Criterion) {
    let data = "test data".repeat(1000);

    c.bench_function("string_processing", |b| {
        b.iter(|| process_string(black_box(&data)))
    });
}

fn benchmark_numeric_calculations(c: &mut Criterion) {
    c.bench_function("numeric_calculations", |b| {
        b.iter(|| calculate(black_box(100), black_box(200)))
    });
}

criterion_group!(benches, benchmark_string_processing, benchmark_numeric_calculations);
criterion_main!(benches);
```

---

## 📚 文档编写

### 文档注释

```rust
/// 计算两个数的和
///
/// # 参数
///
/// * `a` - 第一个数
/// * `b` - 第二个数
///
/// # 返回值
///
/// 返回两个数的和
///
/// # 示例
///
/// ```rust
/// use my_crate::add;
///
/// let result = add(2, 3);
/// assert_eq!(result, 5);
/// ```
///
/// # 错误
///
/// 如果计算结果溢出，会返回错误
pub fn add(a: i32, b: i32) -> Result<i32> {
    a.checked_add(b).ok_or_else(|| AppError::InvalidInput {
        message: "Integer overflow".to_string(),
    })
}

/// 用户管理结构体
///
/// 提供用户的基本信息管理功能
///
/// # 示例
///
/// ```rust
/// use my_crate::User;
///
/// let user = User::new("John Doe".to_string(), "john@example.com".to_string());
/// assert_eq!(user.name, "John Doe");
/// ```
#[derive(Debug, Clone)]
pub struct User {
    /// 用户姓名
    pub name: String,
    /// 用户邮箱
    pub email: String,
}

impl User {
    /// 创建新用户
    ///
    /// # 参数
    ///
    /// * `name` - 用户姓名
    /// * `email` - 用户邮箱
    ///
    /// # 返回值
    ///
    /// 返回新创建的用户实例
    ///
    /// # 示例
    ///
    /// ```rust
    /// use my_crate::User;
    ///
    /// let user = User::new("John Doe".to_string(), "john@example.com".to_string());
    /// ```
    pub fn new(name: String, email: String) -> Self {
        Self { name, email }
    }

    /// 验证用户信息
    ///
    /// # 返回值
    ///
    /// 如果用户信息有效返回true，否则返回false
    ///
    /// # 示例
    ///
    /// ```rust
    /// use my_crate::User;
    ///
    /// let user = User::new("John Doe".to_string(), "john@example.com".to_string());
    /// assert!(user.is_valid());
    /// ```
    pub fn is_valid(&self) -> bool {
        !self.name.is_empty() && self.email.contains('@')
    }
}
```

### 模块文档

```rust
//! # 用户管理模块
//!
//! 提供用户的基本信息管理功能，包括用户创建、验证和查询。
//!
//! # 功能特性
//!
//! - 用户创建和验证
//! - 用户信息查询
//! - 用户状态管理
//!
//! # 使用示例
//!
//! ```rust
//! use my_crate::user::User;
//!
//! let user = User::new("John Doe".to_string(), "john@example.com".to_string());
//! assert!(user.is_valid());
//! ```
//!
//! # 错误处理
//!
//! 所有函数都返回Result类型，包含详细的错误信息。

pub mod user;
pub mod validation;
pub mod storage;

pub use user::User;
pub use validation::validate_user;
pub use storage::UserStorage;
```

---

## 📦 依赖管理

### Cargo.toml最佳实践

```toml
[package]
name = "my-project"
version = "0.1.0"
edition = "2024"
authors = ["Your Name <your.email@example.com>"]
description = "A brief description of your project"
license = "MIT"
repository = "https://github.com/username/my-project"
documentation = "https://docs.rs/my-project"
homepage = "https://github.com/username/my-project"
keywords = ["rust", "example", "library"]
categories = ["development-tools", "libraries"]

[dependencies]
# 核心依赖
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
thiserror = "1.0"

# 可选依赖
reqwest = { version = "0.11", optional = true, features = ["json"] }
tokio = { version = "1.0", optional = true, features = ["full"] }

# 开发依赖
[dev-dependencies]
tokio-test = "0.4"
tempfile = "3.0"
criterion = "0.5"
proptest = "1.0"
mockall = "0.12"
rstest = "0.18"

# 特性定义
[features]
default = ["std"]
std = []
async = ["tokio", "reqwest"]
doc = ["documentation"]

[dependencies.documentation]
optional = true
version = "1.0"
```

### 依赖选择原则

- **稳定性**: 选择稳定、维护良好的依赖
- **性能**: 考虑依赖的性能影响
- **安全性**: 定期检查依赖的安全漏洞
- **大小**: 考虑依赖对最终二进制文件大小的影响

### 依赖更新策略

```bash
# 检查过时的依赖
cargo outdated

# 更新所有依赖
cargo update

# 更新特定依赖
cargo update serde

# 检查安全漏洞
cargo audit
```

---

## 🔄 并发编程

### 线程安全设计

```rust
use std::sync::{Arc, Mutex, RwLock};
use std::thread;

// 使用Mutex保护共享数据
struct ThreadSafeCounter {
    value: Mutex<u32>,
}

impl ThreadSafeCounter {
    fn new() -> Self {
        Self {
            value: Mutex::new(0),
        }
    }

    fn increment(&self) -> Result<u32> {
        let mut value = self.value.lock().map_err(|_| AppError::InternalError(
            anyhow::anyhow!("Failed to acquire lock")
        ))?;
        *value += 1;
        Ok(*value)
    }
}

// 使用RwLock进行读写分离
struct ThreadSafeCache {
    data: RwLock<HashMap<String, String>>,
}

impl ThreadSafeCache {
    fn new() -> Self {
        Self {
            data: RwLock::new(HashMap::new()),
        }
    }

    fn get(&self, key: &str) -> Option<String> {
        let data = self.data.read().unwrap();
        data.get(key).cloned()
    }

    fn insert(&self, key: String, value: String) {
        let mut data = self.data.write().unwrap();
        data.insert(key, value);
    }
}
```

### 异步编程模式

```rust
use tokio::sync::{Mutex, RwLock};
use tokio::time::{sleep, Duration};

// 异步函数设计
async fn fetch_user_data(user_id: u32) -> Result<User> {
    let response = reqwest::get(&format!("https://api.example.com/users/{}", user_id))
        .await?;

    if response.status().is_success() {
        let user: User = response.json().await?;
        Ok(user)
    } else {
        Err(AppError::NetworkError(reqwest::Error::from(
            response.error_for_status().unwrap_err()
        )))
    }
}

// 异步并发处理
async fn process_multiple_users(user_ids: Vec<u32>) -> Vec<Result<User>> {
    let tasks: Vec<_> = user_ids
        .into_iter()
        .map(|id| fetch_user_data(id))
        .collect();

    futures::future::join_all(tasks).await
}

// 异步流处理
use futures::stream::{self, StreamExt};

async fn process_user_stream(user_ids: Vec<u32>) -> Vec<User> {
    stream::iter(user_ids)
        .map(|id| fetch_user_data(id))
        .buffer_unordered(10) // 限制并发数
        .filter_map(|result| async move {
            match result {
                Ok(user) => Some(user),
                Err(_) => None,
            }
        })
        .collect()
        .await
}
```

---

## 🚀 异步编程

### 异步函数设计

```rust
use tokio::time::{sleep, Duration};

// 异步函数
async fn async_operation() -> Result<String> {
    sleep(Duration::from_secs(1)).await;
    Ok("Operation completed".to_string())
}

// 异步错误处理
async fn async_with_error_handling() -> Result<()> {
    let result = async_operation().await?;
    println!("Result: {}", result);
    Ok(())
}

// 异步超时处理
use tokio::time::timeout;

async fn async_with_timeout() -> Result<String> {
    let result = timeout(Duration::from_secs(5), async_operation()).await??;
    Ok(result)
}
```

### 异步并发模式

```rust
// 并发执行多个异步任务
async fn concurrent_operations() -> Vec<Result<String>> {
    let tasks = vec![
        async_operation(),
        async_operation(),
        async_operation(),
    ];

    futures::future::join_all(tasks).await
}

// 使用select!进行异步选择
use tokio::select;

async fn async_select() -> Result<String> {
    let mut timeout_future = sleep(Duration::from_secs(5));
    let mut operation_future = async_operation();

    select! {
        result = operation_future => result,
        _ = timeout_future => Err(AppError::NetworkError(
            reqwest::Error::from(std::io::Error::new(
                std::io::ErrorKind::TimedOut,
                "Operation timed out"
            ))
        )),
    }
}
```

---

## 🎯 总结

### 关键要点

1. **代码组织**: 清晰的模块结构和职责分离
2. **命名规范**: 一致的命名约定和约定俗成的规则
3. **错误处理**: 完善的错误类型和错误传播机制
4. **性能优化**: 内存优化、算法优化和性能监控
5. **安全编程**: 输入验证、安全的数据处理和内存安全
6. **测试策略**: 全面的测试覆盖和测试自动化
7. **文档编写**: 清晰的文档注释和模块文档
8. **依赖管理**: 合理的依赖选择和版本管理
9. **并发编程**: 线程安全的设计和异步编程模式
10. **异步编程**: 高效的异步函数设计和并发模式

### 持续改进

- 定期审查代码质量
- 关注性能指标
- 更新依赖版本
- 学习新的最佳实践
- 参与社区讨论

---

-**遵循这些最佳实践，您将能够编写出高质量、高性能、安全可靠的Rust代码！🦀**-
