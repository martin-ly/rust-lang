# 05. 错误传播机制


## 📊 目录

- [1. 引言](#1-引言)
- [2. 基础概念](#2-基础概念)
  - [2.1 错误传播定义](#21-错误传播定义)
- [3. ?操作符](#3-操作符)
  - [3.1 基本用法](#31-基本用法)
  - [3.2 编译时转换](#32-编译时转换)
  - [3.3 错误类型转换](#33-错误类型转换)
- [4. From特质](#4-from特质)
  - [4.1 自动转换](#41-自动转换)
  - [4.2 自定义转换](#42-自定义转换)
- [5. 错误链](#5-错误链)
  - [5.1 错误上下文](#51-错误上下文)
  - [5.2 错误链遍历](#52-错误链遍历)
- [6. 高级传播模式](#6-高级传播模式)
  - [6.1 条件传播](#61-条件传播)
  - [6.2 错误累积](#62-错误累积)
- [7. 异步错误传播](#7-异步错误传播)
  - [7.1 async/await中的传播](#71-asyncawait中的传播)
  - [7.2 Stream错误传播](#72-stream错误传播)
- [8. 错误传播最佳实践](#8-错误传播最佳实践)
  - [8.1 错误类型设计](#81-错误类型设计)
  - [8.2 避免反模式](#82-避免反模式)
- [9. 性能考虑](#9-性能考虑)
  - [9.1 零成本传播](#91-零成本传播)
  - [9.2 错误类型大小](#92-错误类型大小)
- [10. 总结](#10-总结)


## 1. 引言

错误传播是Rust错误处理系统的核心机制，通过?操作符和From特质实现错误在调用链中的自动传播。

## 2. 基础概念

### 2.1 错误传播定义

**定义 2.1** (错误传播)
错误传播是指错误值在函数调用链中从底层函数向高层函数传递的过程。

**定义 2.2** (传播函数)
传播函数将错误从一个类型转换为另一个类型：
$$\text{Propagate}: \text{Result}\langle T, E \rangle \rightarrow \text{Result}\langle T, E' \rangle$$

## 3. ?操作符

### 3.1 基本用法

```rust
fn process_file(path: &str) -> Result<String, std::io::Error> {
    let file = File::open(path)?;  // 错误传播
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;  // 错误传播
    Ok(contents)
}
```

### 3.2 编译时转换

```rust
// 源代码
fn example() -> Result<i32, String> {
    let value = "42".parse::<i32>()?;
    Ok(value)
}

// 编译器生成的代码
fn example() -> Result<i32, String> {
    let value = match "42".parse::<i32>() {
        Ok(value) => value,
        Err(e) => return Err(e.to_string()),
    };
    Ok(value)
}
```

### 3.3 错误类型转换

```rust
#[derive(Debug)]
enum AppError {
    Io(std::io::Error),
    Parse(String),
}

impl From<std::io::Error> for AppError {
    fn from(err: std::io::Error) -> Self {
        AppError::Io(err)
    }
}

impl From<std::num::ParseIntError> for AppError {
    fn from(err: std::num::ParseIntError) -> Self {
        AppError::Parse(err.to_string())
    }
}

fn process_data(data: &str) -> Result<i32, AppError> {
    let file = File::open(data)?;  // std::io::Error -> AppError
    let contents = file.read_to_string()?;  // std::io::Error -> AppError
    let value = contents.parse::<i32>()?;  // ParseIntError -> AppError
    Ok(value)
}
```

## 4. From特质

### 4.1 自动转换

```rust
// From特质定义
trait From<T> {
    fn from(T) -> Self;
}

// 自动实现
impl<T, E, F> From<F> for Result<T, E>
where
    E: From<F>,
{
    fn from(err: F) -> Self {
        Err(E::from(err))
    }
}
```

### 4.2 自定义转换

```rust
#[derive(Debug)]
enum DatabaseError {
    ConnectionFailed(String),
    QueryFailed(String),
    InvalidData(String),
}

impl From<std::io::Error> for DatabaseError {
    fn from(err: std::io::Error) -> Self {
        DatabaseError::ConnectionFailed(err.to_string())
    }
}

impl From<serde_json::Error> for DatabaseError {
    fn from(err: serde_json::Error) -> Self {
        DatabaseError::InvalidData(err.to_string())
    }
}
```

## 5. 错误链

### 5.1 错误上下文

```rust
use std::error::Error;

#[derive(Debug)]
struct AppError {
    message: String,
    source: Option<Box<dyn Error + 'static>>,
}

impl std::fmt::Display for AppError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl Error for AppError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.source.as_deref()
    }
}

impl From<std::io::Error> for AppError {
    fn from(err: std::io::Error) -> Self {
        AppError {
            message: "IO operation failed".to_string(),
            source: Some(Box::new(err)),
        }
    }
}
```

### 5.2 错误链遍历

```rust
fn print_error_chain(error: &dyn Error) {
    eprintln!("Error: {}", error);
    
    let mut source = error.source();
    while let Some(err) = source {
        eprintln!("Caused by: {}", err);
        source = err.source();
    }
}

// 使用示例
fn example() {
    let result: Result<(), AppError> = process_file("nonexistent.txt");
    if let Err(e) = result {
        print_error_chain(&e);
    }
}
```

## 6. 高级传播模式

### 6.1 条件传播

```rust
fn process_with_retry(data: &str) -> Result<i32, AppError> {
    let mut attempts = 0;
    loop {
        match process_data(data) {
            Ok(value) => return Ok(value),
            Err(e) => {
                attempts += 1;
                if attempts >= 3 {
                    return Err(e);
                }
                // 重试逻辑
                std::thread::sleep(std::time::Duration::from_millis(100));
            }
        }
    }
}
```

### 6.2 错误累积

```rust
#[derive(Debug)]
struct ValidationErrors {
    errors: Vec<String>,
}

impl ValidationErrors {
    fn new() -> Self {
        Self { errors: Vec::new() }
    }
    
    fn add_error(&mut self, error: String) {
        self.errors.push(error);
    }
    
    fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }
}

fn validate_data(data: &str) -> Result<(), ValidationErrors> {
    let mut errors = ValidationErrors::new();
    
    if data.is_empty() {
        errors.add_error("Data cannot be empty".to_string());
    }
    
    if !data.chars().all(char::is_numeric) {
        errors.add_error("Data must contain only numbers".to_string());
    }
    
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}
```

## 7. 异步错误传播

### 7.1 async/await中的传播

```rust
async fn async_process_file(path: &str) -> Result<String, std::io::Error> {
    let contents = tokio::fs::read_to_string(path).await?;
    Ok(contents)
}

async fn async_process_data(data: &str) -> Result<i32, AppError> {
    let file_contents = async_process_file(data).await?;
    let value = file_contents.parse::<i32>()?;
    Ok(value)
}
```

### 7.2 Stream错误传播

```rust
use tokio_stream::StreamExt;

async fn process_stream() -> Result<Vec<i32>, AppError> {
    let mut stream = tokio_stream::iter(1..=10);
    let mut results = Vec::new();
    
    while let Some(value) = stream.next().await {
        let processed = process_value(value)?;
        results.push(processed);
    }
    
    Ok(results)
}
```

## 8. 错误传播最佳实践

### 8.1 错误类型设计

```rust
// 好的错误类型设计
#[derive(Debug, thiserror::Error)]
enum AppError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Parse error: {0}")]
    Parse(#[from] std::num::ParseIntError),
    
    #[error("Validation error: {message}")]
    Validation { message: String },
    
    #[error("Network error: {0}")]
    Network(String),
}

// 使用示例
fn good_error_handling() -> Result<i32, AppError> {
    let data = std::fs::read_to_string("data.txt")?;
    let value = data.parse::<i32>()?;
    
    if value < 0 {
        return Err(AppError::Validation {
            message: "Value must be positive".to_string(),
        });
    }
    
    Ok(value)
}
```

### 8.2 避免反模式

```rust
// 避免：过度使用unwrap
fn bad_pattern() -> i32 {
    "42".parse::<i32>().unwrap()  // 可能panic
}

// 避免：忽略错误
fn ignore_error() {
    let _ = std::fs::read_to_string("file.txt");  // 忽略错误
}

// 避免：不适当的错误类型转换
fn inappropriate_conversion() -> Result<i32, String> {
    // 丢失了原始错误信息
    std::fs::read_to_string("file.txt")
        .map_err(|_| "File error".to_string())
}
```

## 9. 性能考虑

### 9.1 零成本传播

```rust
// 错误传播是零成本的
// 编译器在编译时处理所有转换

fn zero_cost_propagation() -> Result<i32, AppError> {
    let value = "42".parse::<i32>()?;  // 编译时转换
    Ok(value)
}
```

### 9.2 错误类型大小

```rust
// 考虑错误类型的大小
#[derive(Debug)]
enum CompactError {
    Io(std::io::Error),  // 通常较小
    Parse(String),       // 可能较大
}

// 使用Box减少大小
#[derive(Debug)]
enum CompactErrorBoxed {
    Io(std::io::Error),
    Parse(Box<String>),  // 减少枚举大小
}
```

## 10. 总结

错误传播机制是Rust错误处理系统的核心特性，提供了：

1. **自动传播**：通过?操作符自动传播错误
2. **类型转换**：通过From特质自动转换错误类型
3. **错误链**：保持错误上下文信息
4. **零成本**：编译时处理，无运行时开销

这些机制使得Rust程序能够优雅、高效地处理错误传播，是Rust可靠性保证的重要组成部分。
