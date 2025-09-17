# 错误处理最佳实践

本文档详细介绍 Rust 中的错误处理机制，包括 `Result`、`Option`、`panic!` 以及错误处理的最佳实践。

## 目录

- [错误处理概述](#错误处理概述)
- [panic! 宏](#panic-宏)
- [Result 类型](#result-类型)
- [Option 类型](#option-类型)
- [错误传播](#错误传播)
- [自定义错误类型](#自定义错误类型)
- [错误处理最佳实践](#错误处理最佳实践)

## 错误处理概述

Rust 将错误分为两大类：**可恢复错误**和**不可恢复错误**。

- **可恢复错误**：使用 `Result<T, E>` 类型处理
- **不可恢复错误**：使用 `panic!` 宏处理

```rust
// 可恢复错误
fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

// 不可恢复错误
fn must_divide(a: i32, b: i32) -> i32 {
    if b == 0 {
        panic!("Division by zero is not allowed!");
    }
    a / b
}
```

## panic! 宏

### 基本用法

```rust
fn main() {
    panic!("crash and burn");
}
```

### 条件性 panic

```rust
fn main() {
    let v = vec![1, 2, 3];
    v[99]; // 这会导致 panic
}
```

### 自定义 panic 消息

```rust
fn main() {
    let condition = false;
    
    if condition {
        panic!("The condition was not met!");
    }
}
```

### 设置 panic 行为

```rust
// 在 Cargo.toml 中设置
// [profile.release]
// panic = "abort"  // 或者 "unwind"
```

## Result 类型

### 2基本用法

```rust
use std::fs::File;

fn main() {
    let f = File::open("hello.txt");
    
    let f = match f {
        Ok(file) => file,
        Err(error) => {
            panic!("Problem opening the file: {:?}", error)
        },
    };
}
```

### 匹配不同的错误

```rust
use std::fs::File;
use std::io::ErrorKind;

fn main() {
    let f = File::open("hello.txt");
    
    let f = match f {
        Ok(file) => file,
        Err(error) => match error.kind() {
            ErrorKind::NotFound => match File::create("hello.txt") {
                Ok(fc) => fc,
                Err(e) => panic!("Problem creating the file: {:?}", e),
            },
            other_error => {
                panic!("Problem opening the file: {:?}", other_error)
            }
        },
    };
}
```

### 使用 unwrap 和 expect

```rust
use std::fs::File;

fn main() {
    // unwrap：成功时返回值，失败时 panic
    let f = File::open("hello.txt").unwrap();
    
    // expect：类似 unwrap，但可以自定义错误消息
    let f = File::open("hello.txt")
        .expect("Failed to open hello.txt");
}
```

## Option 类型

### 1基本用法

```rust
fn find_user(id: u32) -> Option<String> {
    if id == 1 {
        Some("Alice".to_string())
    } else {
        None
    }
}

fn main() {
    match find_user(1) {
        Some(name) => println!("User found: {}", name),
        None => println!("User not found"),
    }
}
```

### Option 的常用方法

```rust
fn main() {
    let some_number = Some(5);
    let some_string = Some("a string");
    let absent_number: Option<i32> = None;
    
    // unwrap_or：提供默认值
    let value = absent_number.unwrap_or(0);
    println!("Value: {}", value);
    
    // map：转换值
    let doubled = some_number.map(|x| x * 2);
    println!("Doubled: {:?}", doubled);
    
    // and_then：链式操作
    let result = some_number
        .and_then(|x| if x > 0 { Some(x * 2) } else { None });
    println!("Result: {:?}", result);
}
```

## 错误传播

### 使用 ? 操作符

```rust
use std::fs::File;
use std::io;
use std::io::Read;

fn read_username_from_file() -> Result<String, io::Error> {
    let mut f = File::open("hello.txt")?;
    let mut s = String::new();
    f.read_to_string(&mut s)?;
    Ok(s)
}

fn main() {
    match read_username_from_file() {
        Ok(username) => println!("Username: {}", username),
        Err(e) => println!("Error: {}", e),
    }
}
```

### 链式调用

```rust
use std::fs::File;
use std::io;
use std::io::Read;

fn read_username_from_file() -> Result<String, io::Error> {
    let mut s = String::new();
    File::open("hello.txt")?.read_to_string(&mut s)?;
    Ok(s)
}
```

### 在 Option 中使用 ?

```rust
fn last_char_of_first_line(text: &str) -> Option<char> {
    text.lines().next()?.chars().last()
}

fn main() {
    let text = "Hello\nWorld";
    match last_char_of_first_line(text) {
        Some(c) => println!("Last char: {}", c),
        None => println!("No last char found"),
    }
}
```

## 自定义错误类型

### 定义错误类型

```rust
use std::fmt;

#[derive(Debug)]
enum MathError {
    DivisionByZero,
    NegativeSquareRoot,
}

impl fmt::Display for MathError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            MathError::DivisionByZero => write!(f, "Division by zero"),
            MathError::NegativeSquareRoot => write!(f, "Square root of negative number"),
        }
    }
}

impl std::error::Error for MathError {}

fn divide(a: f64, b: f64) -> Result<f64, MathError> {
    if b == 0.0 {
        Err(MathError::DivisionByZero)
    } else {
        Ok(a / b)
    }
}

fn sqrt(x: f64) -> Result<f64, MathError> {
    if x < 0.0 {
        Err(MathError::NegativeSquareRoot)
    } else {
        Ok(x.sqrt())
    }
}

fn main() {
    match divide(10.0, 2.0) {
        Ok(result) => println!("Division result: {}", result),
        Err(e) => println!("Error: {}", e),
    }
    
    match sqrt(-1.0) {
        Ok(result) => println!("Square root: {}", result),
        Err(e) => println!("Error: {}", e),
    }
}
```

### 使用 thiserror 库

```rust
// 在 Cargo.toml 中添加依赖
// [dependencies]
// thiserror = "1.0"

use thiserror::Error;

#[derive(Error, Debug)]
pub enum MathError {
    #[error("Division by zero")]
    DivisionByZero,
    #[error("Square root of negative number")]
    NegativeSquareRoot,
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

fn divide(a: f64, b: f64) -> Result<f64, MathError> {
    if b == 0.0 {
        Err(MathError::DivisionByZero)
    } else {
        Ok(a / b)
    }
}
```

### 错误转换

```rust
use std::num::ParseIntError;

fn parse_and_double(s: &str) -> Result<i32, ParseIntError> {
    s.parse::<i32>().map(|n| n * 2)
}

fn main() {
    match parse_and_double("10") {
        Ok(n) => println!("Result: {}", n),
        Err(e) => println!("Error: {}", e),
    }
    
    match parse_and_double("abc") {
        Ok(n) => println!("Result: {}", n),
        Err(e) => println!("Error: {}", e),
    }
}
```

## 2错误处理最佳实践

### 1. 选择合适的错误处理方式

```rust
// 对于可恢复错误，使用 Result
fn read_config() -> Result<Config, ConfigError> {
    // ...
}

// 对于不可恢复错误，使用 panic!
fn validate_environment() {
    if std::env::var("DATABASE_URL").is_err() {
        panic!("DATABASE_URL environment variable is required");
    }
}
```

### 2. 使用 ? 操作符简化错误传播

```rust
use std::fs;
use std::io;

fn read_and_process_file(filename: &str) -> Result<String, io::Error> {
    let content = fs::read_to_string(filename)?;
    // 处理内容...
    Ok(content.to_uppercase())
}
```

### 3. 提供有意义的错误信息

```rust
use std::fs::File;
use std::io;

fn open_config_file() -> Result<File, io::Error> {
    File::open("config.toml")
        .map_err(|e| io::Error::new(
            io::ErrorKind::NotFound,
            format!("Configuration file not found: {}", e)
        ))
}
```

### 4. 使用 Result 组合子

```rust
fn process_numbers(input: &str) -> Result<i32, String> {
    input
        .parse::<i32>()
        .map_err(|_| "Invalid number".to_string())
        .and_then(|n| if n > 0 { Ok(n) } else { Err("Number must be positive".to_string()) })
        .map(|n| n * 2)
}

fn main() {
    match process_numbers("5") {
        Ok(result) => println!("Result: {}", result),
        Err(e) => println!("Error: {}", e),
    }
}
```

### 5. 错误日志记录

```rust
use log::{error, warn, info};

fn risky_operation() -> Result<(), Box<dyn std::error::Error>> {
    info!("Starting risky operation");
    
    match std::fs::read_to_string("important.txt") {
        Ok(content) => {
            info!("Successfully read file");
            // 处理内容...
            Ok(())
        }
        Err(e) => {
            error!("Failed to read file: {}", e);
            Err(e.into())
        }
    }
}
```

### 6. 错误恢复策略

```rust
use std::fs;
use std::io;

fn read_file_with_fallback(filename: &str) -> Result<String, io::Error> {
    // 尝试读取主文件
    match fs::read_to_string(filename) {
        Ok(content) => Ok(content),
        Err(_) => {
            // 如果失败，尝试读取备份文件
            let backup = format!("{}.backup", filename);
            fs::read_to_string(&backup)
        }
    }
}
```

## 性能考虑

### 错误处理的开销

```rust
// Result 类型在成功情况下几乎没有开销
fn fast_operation() -> Result<i32, String> {
    Ok(42)  // 零成本抽象
}

// 错误情况下的开销主要来自错误信息的创建
fn slow_error() -> Result<i32, String> {
    Err(format!("Detailed error message with context: {}", "context"))
}
```

### 使用 `Box<dyn Error>` 减少代码重复

```rust
use std::error::Error;

fn operation1() -> Result<(), Box<dyn Error>> {
    // ...
    Ok(())
}

fn operation2() -> Result<(), Box<dyn Error>> {
    // ...
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    operation1()?;
    operation2()?;
    Ok(())
}
```

## 相关主题

- [控制流基础](./control_flow_fundamentals.md)
- [函数与闭包详解](./functions_closures.md)
- [异步编程指南](./async_programming.md)
- [标准库错误类型](./std_error_types.md)
