# 错误处理基础（Error Handling Fundamentals）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [错误处理基础（Error Handling Fundamentals）](#错误处理基础error-handling-fundamentals)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [Result 类型](#result-类型)
    - [基本用法](#基本用法)
    - [Result 方法](#result-方法)
  - [Option 类型](#option-类型)
    - [基本用法](#基本用法-1)
    - [Option 方法](#option-方法)
  - [错误传播](#错误传播)
    - [使用 ? 操作符](#使用--操作符)
    - [链式错误处理](#链式错误处理)
  - [自定义错误类型](#自定义错误类型)
    - [使用 thiserror](#使用-thiserror)
    - [使用 anyhow](#使用-anyhow)
  - [实践示例](#实践示例)
    - [示例 1：文件处理](#示例-1文件处理)
    - [示例 2：网络请求](#示例-2网络请求)
    - [示例 3：配置解析](#示例-3配置解析)
  - [最佳实践](#最佳实践)
    - [1. 使用 ? 操作符传播错误](#1-使用--操作符传播错误)
    - [2. 提供有意义的错误消息](#2-提供有意义的错误消息)
    - [3. 使用适当的错误类型](#3-使用适当的错误类型)
  - [参考资料](#参考资料)

---

## 概述

Rust 没有异常机制，而是使用 `Result<T, E>` 和 `Option<T>` 类型来处理错误和可选值。这种设计使错误处理显式化，强制开发者处理可能的错误情况。

## Result 类型

### 基本用法

```rust
// Result<T, E> 表示操作可能成功（Ok(T)）或失败（Err(E)）
fn divide(a: f64, b: f64) -> Result<f64, String> {
    if b == 0.0 {
        Err("除数不能为零".to_string())
    } else {
        Ok(a / b)
    }
}

// 使用 match 处理 Result
fn example1() {
    match divide(10.0, 2.0) {
        Ok(result) => println!("结果: {}", result),
        Err(e) => println!("错误: {}", e),
    }
}

// 使用 unwrap（不推荐在生产代码中使用）
fn example2() {
    let result = divide(10.0, 2.0).unwrap();  // 如果失败会 panic
    println!("结果: {}", result);
}

// 使用 expect（提供错误消息）
fn example3() {
    let result = divide(10.0, 2.0)
        .expect("除法运算失败");  // 如果失败会 panic 并显示消息
    println!("结果: {}", result);
}
```

### Result 方法

```rust
// unwrap_or：失败时返回默认值
let result = divide(10.0, 0.0).unwrap_or(0.0);

// unwrap_or_else：失败时执行闭包
let result = divide(10.0, 0.0).unwrap_or_else(|e| {
    eprintln!("错误: {}", e);
    0.0
});

// map：转换 Ok 值
let result = divide(10.0, 2.0).map(|x| x * 2.0);

// map_err：转换 Err 值
let result = divide(10.0, 0.0).map_err(|e| format!("计算错误: {}", e));

// and_then：链式操作
let result = divide(10.0, 2.0)
    .and_then(|x| divide(x, 2.0));

// or_else：处理错误
let result = divide(10.0, 0.0)
    .or_else(|_| divide(10.0, 1.0));
```

## Option 类型

### 基本用法

```rust
// Option<T> 表示值可能存在（Some(T)）或不存在（None）
fn find_index(slice: &[i32], value: i32) -> Option<usize> {
    for (index, &item) in slice.iter().enumerate() {
        if item == value {
            return Some(index);
        }
    }
    None
}

// 使用 match 处理 Option
fn example1() {
    let numbers = vec![1, 2, 3, 4, 5];
    match find_index(&numbers, 3) {
        Some(index) => println!("找到索引: {}", index),
        None => println!("未找到"),
    }
}

// 使用 unwrap_or
let index = find_index(&numbers, 3).unwrap_or(0);

// 使用 map
let doubled = find_index(&numbers, 3).map(|i| i * 2);
```

### Option 方法

```rust
// is_some / is_none：检查是否有值
let opt = Some(5);
if opt.is_some() {
    println!("有值");
}

// unwrap_or_default：失败时返回默认值
let value: i32 = None.unwrap_or_default();  // 0

// map：转换 Some 值
let doubled = Some(5).map(|x| x * 2);  // Some(10)

// and_then：链式操作
let result = Some(5)
    .and_then(|x| if x > 0 { Some(x * 2) } else { None });

// filter：过滤值
let result = Some(5).filter(|&x| x > 3);  // Some(5)
let result = Some(2).filter(|&x| x > 3);  // None
```

## 错误传播

### 使用 ? 操作符

```rust
use std::fs::File;
use std::io::{self, Read};

// 使用 ? 操作符传播错误
fn read_file_contents(filename: &str) -> Result<String, io::Error> {
    let mut file = File::open(filename)?;  // 如果失败，返回错误
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;   // 如果失败，返回错误
    Ok(contents)
}

// 在 main 函数中使用
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let contents = read_file_contents("file.txt")?;
    println!("文件内容: {}", contents);
    Ok(())
}
```

### 链式错误处理

```rust
fn process_data(filename: &str) -> Result<i32, String> {
    let contents = read_file_contents(filename)
        .map_err(|e| format!("读取文件失败: {}", e))?;

    let number: i32 = contents.trim().parse()
        .map_err(|e| format!("解析数字失败: {}", e))?;

    Ok(number * 2)
}
```

## 自定义错误类型

### 使用 thiserror

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MathError {
    #[error("除数不能为零")]
    DivisionByZero,

    #[error("负数不能开平方根: {0}")]
    NegativeSquareRoot(f64),

    #[error("溢出: {0}")]
    Overflow(String),
}

fn divide(a: f64, b: f64) -> Result<f64, MathError> {
    if b == 0.0 {
        Err(MathError::DivisionByZero)
    } else {
        Ok(a / b)
    }
}

fn sqrt(x: f64) -> Result<f64, MathError> {
    if x < 0.0 {
        Err(MathError::NegativeSquareRoot(x))
    } else {
        Ok(x.sqrt())
    }
}
```

### 使用 anyhow

```rust
use anyhow::{Context, Result};

fn read_config() -> Result<String> {
    let path = "config.toml";
    let contents = std::fs::read_to_string(path)
        .with_context(|| format!("无法读取配置文件: {}", path))?;
    Ok(contents)
}

fn parse_config(contents: &str) -> Result<Config> {
    toml::from_str(contents)
        .context("解析配置文件失败")
}
```

## 实践示例

### 示例 1：文件处理

```rust
use std::fs::File;
use std::io::{self, BufRead, BufReader};

pub struct FileProcessor;

impl FileProcessor {
    pub fn read_lines(filename: &str) -> Result<Vec<String>, io::Error> {
        let file = File::open(filename)?;
        let reader = BufReader::new(file);
        reader.lines().collect()
    }

    pub fn process_file(filename: &str) -> Result<usize, String> {
        let lines = Self::read_lines(filename)
            .map_err(|e| format!("读取文件失败: {}", e))?;

        let count = lines
            .iter()
            .filter(|line| !line.trim().is_empty())
            .count();

        Ok(count)
    }
}
```

### 示例 2：网络请求

```rust
use std::io;

pub struct HttpClient;

impl HttpClient {
    pub fn get(url: &str) -> Result<String, HttpError> {
        // 模拟网络请求
        if url.starts_with("https://") {
            Ok(format!("响应来自: {}", url))
        } else {
            Err(HttpError::InvalidUrl(url.to_string()))
        }
    }
}

#[derive(Debug)]
pub enum HttpError {
    InvalidUrl(String),
    NetworkError(io::Error),
    Timeout,
}

impl std::fmt::Display for HttpError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            HttpError::InvalidUrl(url) => write!(f, "无效的 URL: {}", url),
            HttpError::NetworkError(e) => write!(f, "网络错误: {}", e),
            HttpError::Timeout => write!(f, "请求超时"),
        }
    }
}

impl std::error::Error for HttpError {}
```

### 示例 3：配置解析

```rust
use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct Config {
    pub host: String,
    pub port: u16,
    pub database_url: String,
}

pub fn load_config(path: &str) -> Result<Config, ConfigError> {
    let contents = std::fs::read_to_string(path)
        .map_err(|e| ConfigError::IoError(e))?;

    let config: Config = toml::from_str(&contents)
        .map_err(|e| ConfigError::ParseError(e))?;

    // 验证配置
    if config.port == 0 {
        return Err(ConfigError::InvalidConfig("端口不能为 0".to_string()));
    }

    Ok(config)
}

#[derive(Debug)]
pub enum ConfigError {
    IoError(std::io::Error),
    ParseError(toml::de::Error),
    InvalidConfig(String),
}

impl std::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ConfigError::IoError(e) => write!(f, "IO 错误: {}", e),
            ConfigError::ParseError(e) => write!(f, "解析错误: {}", e),
            ConfigError::InvalidConfig(msg) => write!(f, "无效配置: {}", msg),
        }
    }
}

impl std::error::Error for ConfigError {}
```

## 最佳实践

### 1. 使用 ? 操作符传播错误

```rust
// ✅ 推荐
fn process() -> Result<(), Error> {
    let data = read_data()?;
    let processed = process_data(data)?;
    save_data(processed)?;
    Ok(())
}

// ❌ 不推荐
fn process() -> Result<(), Error> {
    let data = match read_data() {
        Ok(d) => d,
        Err(e) => return Err(e),
    };
    // ...
}
```

### 2. 提供有意义的错误消息

```rust
// ✅ 推荐
let file = File::open(path)
    .with_context(|| format!("无法打开文件: {}", path))?;

// ❌ 不推荐
let file = File::open(path)?;  // 错误消息不够详细
```

### 3. 使用适当的错误类型

```rust
// ✅ 推荐：使用专门的错误类型
#[derive(Error, Debug)]
pub enum MyError {
    #[error("配置错误: {0}")]
    Config(String),
    #[error("网络错误: {0}")]
    Network(#[from] io::Error),
}

// ❌ 不推荐：使用 String 作为错误类型
fn bad_function() -> Result<(), String> {
    Err("错误".to_string())
}
```

## 参考资料

- [错误处理索引](./00_index.md)
- [Result 类型文档](https://doc.rust-lang.org/std/result/)
- [Option 类型文档](https://doc.rust-lang.org/std/option/)
- [thiserror 文档](https://docs.rs/thiserror/)
- [anyhow 文档](https://docs.rs/anyhow/)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回理论基础: [`../00_index.md`](../00_index.md)
