# 错误处理 - Error Handling

**版本**: 2.0  
**最后更新**: 2025-01-27  
**状态**: 完整版（已扩展）  

## 📋 目录

- [错误处理 - Error Handling](#错误处理---error-handling)
  - [📋 目录](#-目录)
  - [1. Rust 错误处理基础](#1-rust-错误处理基础)
    - [1.1 错误类型分类](#11-错误类型分类)
    - [1.2 Result 类型深入](#12-result-类型深入)
    - [1.3 Option 类型深入](#13-option-类型深入)
  - [2. 错误类型设计](#2-错误类型设计)
    - [2.1 自定义错误类型](#21-自定义错误类型)
    - [2.2 错误类型层级](#22-错误类型层级)
    - [2.3 使用 thiserror](#23-使用-thiserror)
    - [2.4 使用 anyhow](#24-使用-anyhow)
  - [3. 错误传播](#3-错误传播)
    - [3.1 ? 操作符](#31--操作符)
    - [3.2 错误转换](#32-错误转换)
    - [3.3 错误上下文](#33-错误上下文)
    - [3.4 错误链追踪](#34-错误链追踪)
  - [4. 错误恢复策略](#4-错误恢复策略)
    - [4.1 重试机制](#41-重试机制)
    - [4.2 降级策略](#42-降级策略)
    - [4.3 断路器模式](#43-断路器模式)
    - [4.4 超时处理](#44-超时处理)
  - [5. 错误处理模式](#5-错误处理模式)
    - [5.1 Railway-oriented Programming](#51-railway-oriented-programming)
    - [5.2 错误聚合](#52-错误聚合)
    - [5.3 早期返回模式](#53-早期返回模式)
  - [6. 最佳实践](#6-最佳实践)
    - [6.1 库 vs 应用](#61-库-vs-应用)
    - [6.2 错误报告](#62-错误报告)
    - [6.3 日志集成](#63-日志集成)
    - [6.4 监控告警](#64-监控告警)
  - [7. 高级主题](#7-高级主题)
    - [7.1 异步错误处理](#71-异步错误处理)
    - [7.2 跨线程错误传播](#72-跨线程错误传播)
    - [7.3 FFI 错误处理](#73-ffi-错误处理)
  - [📚 总结](#-总结)
    - [核心原则](#核心原则)
    - [工具推荐](#工具推荐)

## 1. Rust 错误处理基础

### 1.1 错误类型分类

Rust 将错误分为两类：可恢复和不可恢复错误。

```rust
// 错误分类

// 1. 可恢复错误 (Recoverable Errors)
// 使用 Result<T, E> 表示
fn read_file(path: &str) -> Result<String, std::io::Error> {
    std::fs::read_to_string(path)
    // 调用者可以决定如何处理错误
}

// 2. 不可恢复错误 (Unrecoverable Errors)
// 使用 panic! 宏
fn unrecoverable_error() {
    panic!("Something went terribly wrong!");
    // 程序终止
}

// 何时使用 panic!
// - 程序处于无效状态
// - 违反了不变量
// - 继续执行会导致更大问题
// - 测试失败
// - 原型开发

// 何时使用 Result
// - 网络请求失败
// - 文件不存在
// - 解析错误
// - 用户输入错误
// - 任何可预见的失败

// 示例：选择合适的错误类型
fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

fn array_access(arr: &[i32], index: usize) -> i32 {
    // panic 用于编程错误
    arr[index]  // 越界会 panic
}
```

### 1.2 Result 类型深入

`Result<T, E>` 是 Rust 错误处理的核心。

```rust
// Result 类型定义
// enum Result<T, E> {
//     Ok(T),
//     Err(E),
// }

use std::fs::File;
use std::io::{self, Read};

// 基本使用
fn open_file(path: &str) -> Result<File, io::Error> {
    File::open(path)
}

// 处理 Result
fn handle_result() {
    match open_file("test.txt") {
        Ok(file) => println!("File opened successfully"),
        Err(e) => println!("Error: {}", e),
    }
}

// 使用 unwrap (不推荐用于生产代码)
fn use_unwrap() {
    let file = open_file("test.txt").unwrap();
    // 如果失败会 panic
}

// 使用 expect (提供错误消息)
fn use_expect() {
    let file = open_file("test.txt")
        .expect("Failed to open test.txt");
}

// 使用 unwrap_or (提供默认值)
fn use_unwrap_or() {
    let content = read_file("test.txt")
        .unwrap_or_else(|_| String::from("default content"));
}

// Result 的方法
fn result_methods() {
    let result: Result<i32, &str> = Ok(42);
    
    // is_ok / is_err
    assert!(result.is_ok());
    assert!(!result.is_err());
    
    // ok / err - 转换为 Option
    assert_eq!(result.ok(), Some(42));
    assert_eq!(result.err(), None);
    
    // map - 转换 Ok 值
    let squared = result.map(|x| x * x);
    assert_eq!(squared, Ok(1764));
    
    // map_err - 转换 Err 值
    let result: Result<i32, &str> = Err("error");
    let mapped = result.map_err(|e| format!("Error: {}", e));
    
    // and_then - 链式调用
    let result = Ok(2);
    let chained = result.and_then(|x| Ok(x * 2));
    
    // or_else - 错误恢复
    let result: Result<i32, &str> = Err("error");
    let recovered = result.or_else(|_| Ok(0));
}

fn read_file(path: &str) -> Result<String, io::Error> {
    std::fs::read_to_string(path)
}
```

### 1.3 Option 类型深入

`Option<T>` 表示值可能不存在。

```rust
// Option 类型定义
// enum Option<T> {
//     Some(T),
//     None,
// }

// 基本使用
fn find_item(items: &[i32], target: i32) -> Option<usize> {
    items.iter().position(|&x| x == target)
}

// 处理 Option
fn handle_option() {
    match find_item(&[1, 2, 3], 2) {
        Some(index) => println!("Found at index {}", index),
        None => println!("Not found"),
    }
}

// Option 的方法
fn option_methods() {
    let opt = Some(42);
    
    // is_some / is_none
    assert!(opt.is_some());
    assert!(!opt.is_none());
    
    // unwrap_or / unwrap_or_else
    assert_eq!(opt.unwrap_or(0), 42);
    assert_eq!(None.unwrap_or(0), 0);
    
    // map
    let doubled = opt.map(|x| x * 2);
    assert_eq!(doubled, Some(84));
    
    // and_then
    let result = opt.and_then(|x| Some(x * 2));
    
    // filter
    let filtered = opt.filter(|&x| x > 40);
    assert_eq!(filtered, Some(42));
    
    // ok_or / ok_or_else - 转换为 Result
    let result: Result<i32, &str> = opt.ok_or("Value is None");
    assert_eq!(result, Ok(42));
}

// Option 与 Result 的转换
fn option_result_conversion() {
    let opt: Option<i32> = Some(42);
    let result: Result<i32, &str> = opt.ok_or("No value");
    
    let result: Result<i32, &str> = Ok(42);
    let opt: Option<i32> = result.ok();
}
```

## 2. 错误类型设计

### 2.1 自定义错误类型

创建自定义错误类型提供更好的错误信息。

```rust
use std::fmt;

// 基本自定义错误
#[derive(Debug)]
enum MyError {
    IoError(std::io::Error),
    ParseError(String),
    NotFound,
}

// 实现 Display trait
impl fmt::Display for MyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MyError::IoError(e) => write!(f, "IO error: {}", e),
            MyError::ParseError(msg) => write!(f, "Parse error: {}", msg),
            MyError::NotFound => write!(f, "Resource not found"),
        }
    }
}

// 实现 Error trait
impl std::error::Error for MyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            MyError::IoError(e) => Some(e),
            _ => None,
        }
    }
}

// From trait 用于错误转换
impl From<std::io::Error> for MyError {
    fn from(err: std::io::Error) -> Self {
        MyError::IoError(err)
    }
}

// 使用自定义错误
fn read_config(path: &str) -> Result<String, MyError> {
    let content = std::fs::read_to_string(path)?;  // 自动转换 io::Error
    
    if content.is_empty() {
        return Err(MyError::NotFound);
    }
    
    Ok(content)
}
```

### 2.2 错误类型层级

设计错误类型层级以表达不同层次的错误。

```rust
use std::fmt;

// 应用层错误
#[derive(Debug)]
pub enum AppError {
    Config(ConfigError),
    Database(DatabaseError),
    Network(NetworkError),
}

// 配置错误
#[derive(Debug)]
pub enum ConfigError {
    FileNotFound(String),
    ParseError(String),
    ValidationError(String),
}

// 数据库错误
#[derive(Debug)]
pub enum DatabaseError {
    ConnectionFailed,
    QueryFailed(String),
    TransactionFailed,
}

// 网络错误
#[derive(Debug)]
pub enum NetworkError {
    Timeout,
    ConnectionRefused,
    InvalidResponse,
}

// 实现 Display
impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AppError::Config(e) => write!(f, "Configuration error: {:?}", e),
            AppError::Database(e) => write!(f, "Database error: {:?}", e),
            AppError::Network(e) => write!(f, "Network error: {:?}", e),
        }
    }
}

// From 转换
impl From<ConfigError> for AppError {
    fn from(err: ConfigError) -> Self {
        AppError::Config(err)
    }
}

impl From<DatabaseError> for AppError {
    fn from(err: DatabaseError) -> Self {
        AppError::Database(err)
    }
}

// 使用层级错误
fn load_user_data(user_id: i32) -> Result<String, AppError> {
    // 配置层错误
    let config = load_config()?;
    
    // 数据库层错误
    let user = fetch_user(user_id)?;
    
    Ok(user)
}

fn load_config() -> Result<String, ConfigError> {
    Err(ConfigError::FileNotFound("config.toml".to_string()))
}

fn fetch_user(id: i32) -> Result<String, DatabaseError> {
    Err(DatabaseError::ConnectionFailed)
}
```

### 2.3 使用 thiserror

`thiserror` crate 简化错误类型定义。

```rust
// Cargo.toml
// [dependencies]
// thiserror = "1.0"

use thiserror::Error;

#[derive(Error, Debug)]
pub enum DataStoreError {
    #[error("data store disconnected")]
    Disconnect(#[from] std::io::Error),
    
    #[error("the data for key `{0}` is not available")]
    Redaction(String),
    
    #[error("invalid header (expected {expected:?}, found {found:?})")]
    InvalidHeader {
        expected: String,
        found: String,
    },
    
    #[error("unknown data store error")]
    Unknown,
}

// 使用 thiserror 定义的错误
fn use_thiserror() -> Result<(), DataStoreError> {
    // 自动实现了 Display 和 Error trait
    Err(DataStoreError::Redaction("sensitive_data".to_string()))
}

// 更复杂的示例
#[derive(Error, Debug)]
pub enum ApiError {
    #[error("API request failed: {0}")]
    RequestFailed(String),
    
    #[error("Authentication failed")]
    AuthenticationFailed,
    
    #[error("Rate limit exceeded: retry after {retry_after} seconds")]
    RateLimitExceeded { retry_after: u64 },
    
    #[error("Invalid response: {0}")]
    InvalidResponse(String),
    
    #[error(transparent)]
    IoError(#[from] std::io::Error),
    
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}
```

### 2.4 使用 anyhow

`anyhow` 用于应用程序级别的错误处理。

```rust
// Cargo.toml
// [dependencies]
// anyhow = "1.0"

use anyhow::{Context, Result, anyhow};

// anyhow::Result 是 Result<T, anyhow::Error> 的别名
fn read_config_file(path: &str) -> Result<String> {
    let content = std::fs::read_to_string(path)
        .context("Failed to read config file")?;
    
    if content.is_empty() {
        return Err(anyhow!("Config file is empty"));
    }
    
    Ok(content)
}

// 添加上下文
fn parse_config(content: &str) -> Result<Config> {
    serde_json::from_str(content)
        .context("Failed to parse config JSON")
}

// 链式上下文
fn load_user_config(user_id: i32) -> Result<Config> {
    let path = format!("/etc/app/user_{}.json", user_id);
    
    let content = read_config_file(&path)
        .with_context(|| format!("Loading config for user {}", user_id))?;
    
    parse_config(&content)
        .with_context(|| format!("Parsing config for user {}", user_id))
}

// Config 定义
use serde::Deserialize;

#[derive(Deserialize)]
struct Config {
    name: String,
    value: i32,
}

// anyhow 的优势
// 1. 自动包装任何实现 Error 的类型
// 2. 提供上下文信息
// 3. 错误链追踪
// 4. 不需要定义自定义错误类型
```

## 3. 错误传播

### 3.1 ? 操作符

`?` 操作符简化错误传播。

```rust
use std::fs::File;
use std::io::{self, Read};

// 不使用 ? 操作符
fn read_file_without_operator(path: &str) -> Result<String, io::Error> {
    let file = match File::open(path) {
        Ok(file) => file,
        Err(e) => return Err(e),
    };
    
    let mut content = String::new();
    match file.read_to_string(&mut content) {
        Ok(_) => Ok(content),
        Err(e) => Err(e),
    }
}

// 使用 ? 操作符
fn read_file_with_operator(path: &str) -> Result<String, io::Error> {
    let mut file = File::open(path)?;
    let mut content = String::new();
    file.read_to_string(&mut content)?;
    Ok(content)
}

// ? 操作符的工作原理
// 1. 如果是 Ok(value)，返回 value
// 2. 如果是 Err(e)，执行 From::from(e) 并返回

// ? 用于 Option
fn find_and_double(items: &[i32], target: i32) -> Option<i32> {
    let index = items.iter().position(|&x| x == target)?;
    Some(items[index] * 2)
}

// 在 main 函数中使用 ?
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let content = read_file_with_operator("test.txt")?;
    println!("{}", content);
    Ok(())
}
```

### 3.2 错误转换

自动转换不同的错误类型。

```rust
use std::fmt;
use std::num::ParseIntError;

// 自定义错误类型
#[derive(Debug)]
enum AppError {
    Io(std::io::Error),
    Parse(ParseIntError),
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AppError::Io(e) => write!(f, "IO error: {}", e),
            AppError::Parse(e) => write!(f, "Parse error: {}", e),
        }
    }
}

impl std::error::Error for AppError {}

// 实现 From trait 以支持自动转换
impl From<std::io::Error> for AppError {
    fn from(err: std::io::Error) -> Self {
        AppError::Io(err)
    }
}

impl From<ParseIntError> for AppError {
    fn from(err: ParseIntError) -> Self {
        AppError::Parse(err)
    }
}

// 使用自动转换
fn read_number_from_file(path: &str) -> Result<i32, AppError> {
    let content = std::fs::read_to_string(path)?;  // io::Error 自动转换
    let number = content.trim().parse()?;           // ParseIntError 自动转换
    Ok(number)
}

// 多种错误类型转换
fn complex_operation() -> Result<i32, AppError> {
    // 这两种错误都会自动转换为 AppError
    let file_content = std::fs::read_to_string("number.txt")?;
    let number: i32 = file_content.trim().parse()?;
    Ok(number * 2)
}
```

### 3.3 错误上下文

添加上下文信息使错误更有用。

```rust
use anyhow::{Context, Result};

// 添加简单上下文
fn read_config() -> Result<String> {
    std::fs::read_to_string("config.toml")
        .context("Failed to read configuration file")
}

// 添加动态上下文
fn read_user_file(user_id: i32) -> Result<String> {
    let path = format!("users/{}.json", user_id);
    std::fs::read_to_string(&path)
        .with_context(|| format!("Failed to read file for user {}", user_id))
}

// 链式上下文
fn process_user_data(user_id: i32) -> Result<()> {
    let data = read_user_file(user_id)
        .context("Reading user data")?;
    
    parse_user_data(&data)
        .with_context(|| format!("Parsing data for user {}", user_id))?;
    
    Ok(())
}

fn parse_user_data(data: &str) -> Result<()> {
    // 解析逻辑
    Ok(())
}

// 错误报告示例
fn report_error() {
    if let Err(e) = process_user_data(42) {
        eprintln!("Error: {:?}", e);
        // 打印完整的错误链
        for cause in e.chain() {
            eprintln!("Caused by: {}", cause);
        }
    }
}
```

### 3.4 错误链追踪

追踪错误的完整链条。

```rust
use std::error::Error;
use std::fmt;

// 可追踪的错误类型
#[derive(Debug)]
struct Layer1Error {
    source: Layer2Error,
}

#[derive(Debug)]
struct Layer2Error {
    source: std::io::Error,
}

impl fmt::Display for Layer1Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Layer 1 error")
    }
}

impl fmt::Display for Layer2Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Layer 2 error")
    }
}

impl Error for Layer1Error {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.source)
    }
}

impl Error for Layer2Error {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.source)
    }
}

// 打印错误链
fn print_error_chain(e: &dyn Error) {
    eprintln!("Error: {}", e);
    
    let mut current = e.source();
    while let Some(source) = current {
        eprintln!("Caused by: {}", source);
        current = source.source();
    }
}

// 使用示例
fn demonstrate_error_chain() {
    let io_error = std::io::Error::new(
        std::io::ErrorKind::NotFound,
        "file not found"
    );
    
    let layer2 = Layer2Error { source: io_error };
    let layer1 = Layer1Error { source: layer2 };
    
    print_error_chain(&layer1);
    // 输出:
    // Error: Layer 1 error
    // Caused by: Layer 2 error
    // Caused by: file not found
}
```

## 4. 错误恢复策略

### 4.1 重试机制

实现自动重试失败的操作。

```rust
use std::time::Duration;
use std::thread;

// 简单重试
fn retry_simple<F, T, E>(mut f: F, max_retries: u32) -> Result<T, E>
where
    F: FnMut() -> Result<T, E>,
{
    let mut attempts = 0;
    loop {
        match f() {
            Ok(result) => return Ok(result),
            Err(e) => {
                attempts += 1;
                if attempts >= max_retries {
                    return Err(e);
                }
            }
        }
    }
}

// 带延迟的重试
fn retry_with_delay<F, T, E>(
    mut f: F,
    max_retries: u32,
    delay: Duration,
) -> Result<T, E>
where
    F: FnMut() -> Result<T, E>,
{
    let mut attempts = 0;
    loop {
        match f() {
            Ok(result) => return Ok(result),
            Err(e) => {
                attempts += 1;
                if attempts >= max_retries {
                    return Err(e);
                }
                thread::sleep(delay);
            }
        }
    }
}

// 指数退避重试
fn retry_exponential_backoff<F, T, E>(
    mut f: F,
    max_retries: u32,
    initial_delay: Duration,
) -> Result<T, E>
where
    F: FnMut() -> Result<T, E>,
{
    let mut attempts = 0;
    let mut delay = initial_delay;
    
    loop {
        match f() {
            Ok(result) => return Ok(result),
            Err(e) => {
                attempts += 1;
                if attempts >= max_retries {
                    return Err(e);
                }
                thread::sleep(delay);
                delay *= 2;  // 指数增长
            }
        }
    }
}

// 使用示例
fn fetch_data() -> Result<String, std::io::Error> {
    // 模拟可能失败的网络请求
    Ok("data".to_string())
}

fn use_retry() {
    let result = retry_exponential_backoff(
        fetch_data,
        3,
        Duration::from_millis(100),
    );
    
    match result {
        Ok(data) => println!("Success: {}", data),
        Err(e) => eprintln!("Failed after retries: {}", e),
    }
}
```

### 4.2 降级策略

失败时使用降级方案。

```rust
// 降级策略示例

// 主函数失败时使用缓存
fn get_user_data(user_id: i32) -> String {
    fetch_from_api(user_id)
        .or_else(|_| fetch_from_cache(user_id))
        .or_else(|_| fetch_from_local_db(user_id))
        .unwrap_or_else(|_| default_user_data())
}

fn fetch_from_api(user_id: i32) -> Result<String, std::io::Error> {
    // 尝试从 API 获取
    Err(std::io::Error::new(std::io::ErrorKind::Other, "API failed"))
}

fn fetch_from_cache(user_id: i32) -> Result<String, std::io::Error> {
    // 尝试从缓存获取
    Err(std::io::Error::new(std::io::ErrorKind::Other, "Cache failed"))
}

fn fetch_from_local_db(user_id: i32) -> Result<String, std::io::Error> {
    // 尝试从本地数据库获取
    Ok(format!("User {} from DB", user_id))
}

fn default_user_data() -> String {
    "Default user data".to_string()
}

// 特性降级
struct Service {
    full_featured: bool,
}

impl Service {
    fn process_request(&self, request: Request) -> Result<Response, Error> {
        if self.full_featured {
            self.full_processing(request)
        } else {
            self.degraded_processing(request)
        }
    }
    
    fn full_processing(&self, request: Request) -> Result<Response, Error> {
        // 完整功能处理
        Ok(Response::Full)
    }
    
    fn degraded_processing(&self, request: Request) -> Result<Response, Error> {
        // 降级功能处理
        Ok(Response::Degraded)
    }
}

#[derive(Debug)]
struct Request;

#[derive(Debug)]
enum Response {
    Full,
    Degraded,
}

#[derive(Debug)]
struct Error;
```

### 4.3 断路器模式

防止级联失败。

```rust
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// 断路器状态
#[derive(Debug, Clone, PartialEq)]
enum CircuitState {
    Closed,    // 正常运行
    Open,      // 断开，拒绝请求
    HalfOpen,  // 尝试恢复
}

// 断路器
struct CircuitBreaker {
    state: Arc<Mutex<CircuitState>>,
    failure_threshold: u32,
    success_threshold: u32,
    timeout: Duration,
    failure_count: Arc<Mutex<u32>>,
    success_count: Arc<Mutex<u32>>,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
}

impl CircuitBreaker {
    fn new(failure_threshold: u32, success_threshold: u32, timeout: Duration) -> Self {
        Self {
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            failure_threshold,
            success_threshold,
            timeout,
            failure_count: Arc::new(Mutex::new(0)),
            success_count: Arc::new(Mutex::new(0)),
            last_failure_time: Arc::new(Mutex::new(None)),
        }
    }
    
    fn call<F, T, E>(&self, f: F) -> Result<T, E>
    where
        F: FnOnce() -> Result<T, E>,
        E: From<CircuitBreakerError>,
    {
        let state = self.state.lock().unwrap().clone();
        
        match state {
            CircuitState::Open => {
                // 检查是否可以进入半开状态
                if self.should_attempt_reset() {
                    *self.state.lock().unwrap() = CircuitState::HalfOpen;
                } else {
                    return Err(CircuitBreakerError::Open.into());
                }
            }
            CircuitState::Closed | CircuitState::HalfOpen => {}
        }
        
        // 执行函数
        match f() {
            Ok(result) => {
                self.on_success();
                Ok(result)
            }
            Err(e) => {
                self.on_failure();
                Err(e)
            }
        }
    }
    
    fn on_success(&self) {
        let state = self.state.lock().unwrap().clone();
        
        if state == CircuitState::HalfOpen {
            let mut success_count = self.success_count.lock().unwrap();
            *success_count += 1;
            
            if *success_count >= self.success_threshold {
                *self.state.lock().unwrap() = CircuitState::Closed;
                *self.failure_count.lock().unwrap() = 0;
                *success_count = 0;
            }
        }
    }
    
    fn on_failure(&self) {
        *self.last_failure_time.lock().unwrap() = Some(Instant::now());
        
        let mut failure_count = self.failure_count.lock().unwrap();
        *failure_count += 1;
        
        if *failure_count >= self.failure_threshold {
            *self.state.lock().unwrap() = CircuitState::Open;
        }
    }
    
    fn should_attempt_reset(&self) -> bool {
        if let Some(last_failure) = *self.last_failure_time.lock().unwrap() {
            Instant::now().duration_since(last_failure) > self.timeout
        } else {
            false
        }
    }
}

#[derive(Debug)]
enum CircuitBreakerError {
    Open,
}

impl std::fmt::Display for CircuitBreakerError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Circuit breaker is open")
    }
}

impl std::error::Error for CircuitBreakerError {}

// 使用示例
fn use_circuit_breaker() {
    let breaker = CircuitBreaker::new(
        3,                          // 失败阈值
        2,                          // 成功阈值
        Duration::from_secs(60),    // 超时时间
    );
    
    for _ in 0..10 {
        let result: Result<String, Box<dyn std::error::Error>> = breaker.call(|| {
            // 可能失败的操作
            Ok("success".to_string())
        });
        
        match result {
            Ok(data) => println!("Success: {}", data),
            Err(e) => eprintln!("Error: {}", e),
        }
    }
}
```

### 4.4 超时处理

设置操作超时限制。

```rust
use std::time::{Duration, Instant};
use std::thread;

// 简单超时
fn with_timeout<F, T>(f: F, timeout: Duration) -> Result<T, TimeoutError>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    let (tx, rx) = std::sync::mpsc::channel();
    
    thread::spawn(move || {
        let result = f();
        let _ = tx.send(result);
    });
    
    match rx.recv_timeout(timeout) {
        Ok(result) => Ok(result),
        Err(_) => Err(TimeoutError),
    }
}

#[derive(Debug)]
struct TimeoutError;

impl std::fmt::Display for TimeoutError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Operation timed out")
    }
}

impl std::error::Error for TimeoutError {}

// 异步超时（需要 tokio）
// use tokio::time::timeout;
// 
// async fn async_with_timeout() -> Result<String, Box<dyn std::error::Error>> {
//     let result = timeout(
//         Duration::from_secs(5),
//         fetch_data_async()
//     ).await??;
//     Ok(result)
// }
// 
// async fn fetch_data_async() -> Result<String, std::io::Error> {
//     Ok("data".to_string())
// }
```

## 5. 错误处理模式

### 5.1 Railway-oriented Programming

将错误处理看作铁路轨道。

```rust
// Railway-oriented Programming 模式

// 成功路径和错误路径像铁路的两条轨道

// 链式操作
fn process_data(input: &str) -> Result<String, String> {
    validate_input(input)?
        .and_then(parse_data)
        .and_then(transform_data)
        .and_then(format_output)
}

fn validate_input(input: &str) -> Result<String, String> {
    if input.is_empty() {
        Err("Input is empty".to_string())
    } else {
        Ok(input.to_string())
    }
}

fn parse_data(input: String) -> Result<ParsedData, String> {
    Ok(ParsedData { value: input })
}

fn transform_data(data: ParsedData) -> Result<TransformedData, String> {
    Ok(TransformedData { result: data.value.to_uppercase() })
}

fn format_output(data: TransformedData) -> Result<String, String> {
    Ok(format!("Result: {}", data.result))
}

struct ParsedData {
    value: String,
}

struct TransformedData {
    result: String,
}
```

### 5.2 错误聚合

收集多个操作的所有错误。

```rust
// 错误聚合示例

// 收集所有错误
fn validate_all(inputs: &[String]) -> Result<Vec<ValidatedInput>, Vec<ValidationError>> {
    let mut results = Vec::new();
    let mut errors = Vec::new();
    
    for input in inputs {
        match validate(input) {
            Ok(validated) => results.push(validated),
            Err(e) => errors.push(e),
        }
    }
    
    if errors.is_empty() {
        Ok(results)
    } else {
        Err(errors)
    }
}

#[derive(Debug)]
struct ValidatedInput {
    value: String,
}

#[derive(Debug)]
struct ValidationError {
    message: String,
}

fn validate(input: &str) -> Result<ValidatedInput, ValidationError> {
    if input.len() < 3 {
        Err(ValidationError {
            message: format!("Input '{}' is too short", input),
        })
    } else {
        Ok(ValidatedInput {
            value: input.to_string(),
        })
    }
}

// 使用示例
fn use_validation() {
    let inputs = vec![
        "ab".to_string(),
        "abc".to_string(),
        "x".to_string(),
        "valid".to_string(),
    ];
    
    match validate_all(&inputs) {
        Ok(results) => println!("All valid: {} items", results.len()),
        Err(errors) => {
            eprintln!("Validation failed with {} errors:", errors.len());
            for error in errors {
                eprintln!("  - {}", error.message);
            }
        }
    }
}
```

### 5.3 早期返回模式

尽早处理错误情况。

```rust
// 早期返回模式

// ❌ 嵌套的 if-else
fn process_nested(value: Option<i32>) -> Result<i32, String> {
    if let Some(v) = value {
        if v > 0 {
            if v < 100 {
                Ok(v * 2)
            } else {
                Err("Value too large".to_string())
            }
        } else {
            Err("Value must be positive".to_string())
        }
    } else {
        Err("No value provided".to_string())
    }
}

// ✅ 早期返回
fn process_early_return(value: Option<i32>) -> Result<i32, String> {
    let v = value.ok_or("No value provided")?;
    
    if v <= 0 {
        return Err("Value must be positive".to_string());
    }
    
    if v >= 100 {
        return Err("Value too large".to_string());
    }
    
    Ok(v * 2)
}

// 守卫子句模式
fn process_with_guards(input: &str) -> Result<String, String> {
    // 验证前提条件
    if input.is_empty() {
        return Err("Input is empty".to_string());
    }
    
    if input.len() > 100 {
        return Err("Input too long".to_string());
    }
    
    if !input.chars().all(|c| c.is_alphanumeric()) {
        return Err("Input contains invalid characters".to_string());
    }
    
    // 主要逻辑
    Ok(input.to_uppercase())
}
```

## 6. 最佳实践

### 6.1 库 vs 应用

库和应用的错误处理策略不同。

```rust
// 库的错误处理
pub mod library {
    use thiserror::Error;
    
    // 库应该定义具体的错误类型
    #[derive(Error, Debug)]
    pub enum LibraryError {
        #[error("invalid parameter: {0}")]
        InvalidParameter(String),
        
        #[error("operation failed: {0}")]
        OperationFailed(String),
        
        #[error(transparent)]
        IoError(#[from] std::io::Error),
    }
    
    // 库函数返回具体的错误类型
    pub fn library_function(param: &str) -> Result<String, LibraryError> {
        if param.is_empty() {
            return Err(LibraryError::InvalidParameter(
                "param cannot be empty".to_string()
            ));
        }
        Ok(param.to_uppercase())
    }
}

// 应用的错误处理
mod application {
    use anyhow::Result;
    
    // 应用可以使用 anyhow::Result
    pub fn application_function() -> Result<()> {
        let result = super::library::library_function("test")?;
        println!("{}", result);
        Ok(())
    }
}
```

### 6.2 错误报告

提供清晰的错误报告。

```rust
use anyhow::{Context, Result};

// 详细的错误报告
fn detailed_error_reporting() -> Result<()> {
    process_file("data.json")
        .context("Failed to process data file")?;
    Ok(())
}

fn process_file(path: &str) -> Result<()> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read file: {}", path))?;
    
    parse_content(&content)
        .with_context(|| format!("Failed to parse content from {}", path))?;
    
    Ok(())
}

fn parse_content(content: &str) -> Result<()> {
    // 解析逻辑
    Ok(())
}

// 用户友好的错误消息
fn user_friendly_errors() {
    if let Err(e) = detailed_error_reporting() {
        // 向用户显示友好消息
        eprintln!("An error occurred while processing the file.");
        eprintln!("Please check that the file exists and is readable.");
        
        // 向开发者记录详细错误
        log::error!("Error details: {:?}", e);
        
        // 打印错误链
        for (i, cause) in e.chain().enumerate() {
            if i == 0 {
                eprintln!("Error: {}", cause);
            } else {
                eprintln!("Caused by: {}", cause);
            }
        }
    }
}
```

### 6.3 日志集成

将错误处理与日志系统集成。

```rust
// Cargo.toml
// [dependencies]
// log = "0.4"
// env_logger = "0.10"

use log::{error, warn, info, debug};

fn operation_with_logging() -> Result<(), Box<dyn std::error::Error>> {
    info!("Starting operation");
    
    match risky_operation() {
        Ok(result) => {
            info!("Operation succeeded: {}", result);
            Ok(())
        }
        Err(e) => {
            error!("Operation failed: {}", e);
            // 记录错误详情
            for cause in e.chain() {
                error!("Caused by: {}", cause);
            }
            Err(e)
        }
    }
}

fn risky_operation() -> Result<String, Box<dyn std::error::Error>> {
    debug!("Executing risky operation");
    
    // 操作可能失败
    warn!("Operation is risky");
    
    Ok("success".to_string())
}

// 结构化日志
use log::Level;

fn structured_logging() {
    log!(Level::Error, "Error occurred"; 
        "user_id" => 42,
        "operation" => "fetch_data",
        "error_code" => "ERR001"
    );
}
```

### 6.4 监控告警

错误监控和告警。

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

// 错误计数器
struct ErrorMetrics {
    total_errors: Arc<AtomicU64>,
    error_rate: Arc<AtomicU64>,
}

impl ErrorMetrics {
    fn new() -> Self {
        Self {
            total_errors: Arc::new(AtomicU64::new(0)),
            error_rate: Arc::new(AtomicU64::new(0)),
        }
    }
    
    fn record_error(&self, error: &dyn std::error::Error) {
        self.total_errors.fetch_add(1, Ordering::Relaxed);
        
        // 记录错误类型
        log::error!("Error recorded: {}", error);
        
        // 检查是否需要告警
        if self.should_alert() {
            self.send_alert(error);
        }
    }
    
    fn should_alert(&self) -> bool {
        let error_count = self.total_errors.load(Ordering::Relaxed);
        error_count % 100 == 0  // 每100个错误告警一次
    }
    
    fn send_alert(&self, error: &dyn std::error::Error) {
        // 发送告警（邮件、短信、Slack等）
        eprintln!("ALERT: High error rate detected! Latest error: {}", error);
    }
}

// 使用示例
fn monitored_operation(metrics: &ErrorMetrics) -> Result<(), Box<dyn std::error::Error>> {
    match dangerous_operation() {
        Ok(result) => Ok(()),
        Err(e) => {
            metrics.record_error(e.as_ref());
            Err(e)
        }
    }
}

fn dangerous_operation() -> Result<(), Box<dyn std::error::Error>> {
    Err("Something went wrong".into())
}
```

## 7. 高级主题

### 7.1 异步错误处理

异步代码中的错误处理。

```rust
// 异步错误处理（需要 tokio）

// use tokio;
// use anyhow::Result;
// 
// #[tokio::main]
// async fn main() -> Result<()> {
//     async_operation().await?;
//     Ok(())
// }
// 
// async fn async_operation() -> Result<String> {
//     let result = fetch_data().await
//         .context("Failed to fetch data")?;
//     Ok(result)
// }
// 
// async fn fetch_data() -> Result<String> {
//     Ok("data".to_string())
// }
// 
// // 并发错误处理
// use futures::future::try_join_all;
// 
// async fn concurrent_operations() -> Result<Vec<String>> {
//     let futures = vec![
//         fetch_data(),
//         fetch_data(),
//         fetch_data(),
//     ];
//     
//     try_join_all(futures).await
// }
```

### 7.2 跨线程错误传播

在多线程环境中传播错误。

```rust
use std::thread;
use std::sync::mpsc;

// 跨线程错误传播
fn threaded_operation() -> Result<Vec<String>, String> {
    let (tx, rx) = mpsc::channel();
    let mut handles = vec![];
    
    for i in 0..3 {
        let tx = tx.clone();
        let handle = thread::spawn(move || {
            let result = worker_function(i);
            tx.send(result).unwrap();
        });
        handles.push(handle);
    }
    drop(tx);
    
    let mut results = Vec::new();
    for received in rx {
        results.push(received?);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    Ok(results)
}

fn worker_function(id: usize) -> Result<String, String> {
    if id % 2 == 0 {
        Ok(format!("Worker {} succeeded", id))
    } else {
        Err(format!("Worker {} failed", id))
    }
}
```

### 7.3 FFI 错误处理

与 C 代码交互时的错误处理。

```rust
use std::ffi::CString;
use std::os::raw::c_char;

// FFI 错误处理
#[repr(C)]
pub struct CError {
    code: i32,
    message: *const c_char,
}

#[no_mangle]
pub extern "C" fn rust_function(input: *const c_char) -> *mut CError {
    let input = unsafe {
        if input.is_null() {
            return create_error(1, "Null pointer");
        }
        std::ffi::CStr::from_ptr(input)
    };
    
    match process_input(input.to_str()) {
        Ok(_) => std::ptr::null_mut(),
        Err(e) => create_error(2, &e.to_string()),
    }
}

fn create_error(code: i32, message: &str) -> *mut CError {
    let c_message = CString::new(message).unwrap();
    Box::into_raw(Box::new(CError {
        code,
        message: c_message.into_raw(),
    }))
}

fn process_input(input: Result<&str, std::str::Utf8Error>) -> Result<(), Box<dyn std::error::Error>> {
    let input = input?;
    // 处理输入
    Ok(())
}

// 释放错误
#[no_mangle]
pub extern "C" fn free_error(error: *mut CError) {
    if !error.is_null() {
        unsafe {
            let error = Box::from_raw(error);
            let _ = CString::from_raw(error.message as *mut c_char);
        }
    }
}
```

## 📚 总结

Rust 错误处理的最佳实践：

### 核心原则

1. **使用类型系统**
   - `Result<T, E>` 用于可恢复错误
   - `panic!` 用于不可恢复错误
   - `Option<T>` 用于值可能不存在的情况

2. **设计好的错误类型**
   - 库：定义具体的错误类型
   - 应用：使用 `anyhow` 简化处理
   - 使用 `thiserror` 简化错误定义

3. **错误传播**
   - 使用 `?` 操作符
   - 添加上下文信息
   - 追踪错误链

4. **恢复策略**
   - 实现重试机制
   - 使用降级方案
   - 应用断路器模式
   - 设置超时限制

5. **错误报告**
   - 提供清晰的错误消息
   - 集成日志系统
   - 实现监控告警
   - 用户友好的错误展示

### 工具推荐

- **thiserror**: 定义错误类型
- **anyhow**: 应用级错误处理
- **log**: 日志记录
- **tracing**: 结构化日志和追踪

---

**相关文档**：

- [最佳实践](../05_practice/02_best_practices.md)
- [并发安全](./02_concurrency_safety.md)
- [性能优化](./03_performance_optimization.md)

**最后更新**: 2025年1月27日  
**维护状态**: 活跃维护中  
**质量等级**: 完整版
