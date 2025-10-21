# 错误处理 (Error Handling)

> **核心库**: anyhow, thiserror, eyre  
> **适用场景**: 应用错误处理、库错误定义、错误追踪、错误转换  
> **技术栈定位**: 横切关注点 - 错误处理层

---

## 📋 目录

- [错误处理 (Error Handling)](#错误处理-error-handling)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. anyhow (应用层 ⭐⭐⭐⭐⭐)](#1-anyhow-应用层-)
      - [核心特性](#核心特性)
      - [基础用法](#基础用法)
      - [高级用法](#高级用法)
    - [2. thiserror (库层 ⭐⭐⭐⭐⭐)](#2-thiserror-库层-)
      - [基础用法2](#基础用法2)
      - [高级特性](#高级特性)
    - [3. eyre (增强报告 💡)](#3-eyre-增强报告-)
      - [基础用法3](#基础用法3)
      - [美化错误报告](#美化错误报告)
  - [💡 最佳实践](#-最佳实践)
    - [1. 应用层 vs 库层](#1-应用层-vs-库层)
    - [2. 错误分层](#2-错误分层)
    - [3. Web 框架集成](#3-web-框架集成)
    - [4. 错误恢复策略](#4-错误恢复策略)
  - [📊 工具对比](#-工具对比)
    - [功能对比](#功能对比)
    - [选择建议](#选择建议)
  - [🎯 实战场景](#-实战场景)
    - [场景1: CLI 工具](#场景1-cli-工具)
    - [场景2: 微服务](#场景2-微服务)
    - [场景3: 异步错误处理](#场景3-异步错误处理)
  - [🔗 相关资源](#-相关资源)

---

## 📋 概述

良好的错误处理是 Rust 应用程序的基石。
Rust 生态提供了多种工具来简化错误处理，从应用层到库层都有最佳实践。

---

## 🔧 核心工具

### 1. anyhow (应用层 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add anyhow`  
**用途**: 简化应用程序的错误处理

#### 核心特性

- ✅ 简单的 `Result<T>` 类型别名
- ✅ `Context` trait 增强错误信息
- ✅ 自动错误转换
- ✅ 美观的错误输出

#### 基础用法

```rust
use anyhow::{Context, Result};
use std::fs;

fn read_config(path: &str) -> Result<String> {
    let content = fs::read_to_string(path)
        .context("Failed to read config file")?;
    
    Ok(content)
}

fn parse_config(content: &str) -> Result<Config> {
    serde_json::from_str(content)
        .context("Failed to parse config JSON")?
}

fn main() -> Result<()> {
    let content = read_config("config.json")?;
    let config = parse_config(&content)?;
    
    println!("Config loaded: {:?}", config);
    Ok(())
}
```

#### 高级用法

**添加上下文信息**:

```rust
use anyhow::{Context, Result};

fn process_user(user_id: u64) -> Result<()> {
    let user = fetch_user(user_id)
        .with_context(|| format!("Failed to fetch user {}", user_id))?;
    
    validate_user(&user)
        .context("User validation failed")?;
    
    Ok(())
}
```

**自定义错误**:

```rust
use anyhow::{anyhow, bail, ensure, Result};

fn validate_age(age: i32) -> Result<()> {
    // 使用 ensure! 宏
    ensure!(age >= 0, "Age cannot be negative");
    ensure!(age <= 150, "Age is unrealistic");
    
    Ok(())
}

fn process_data(data: &[u8]) -> Result<String> {
    if data.is_empty() {
        // 使用 bail! 宏提前返回
        bail!("Data is empty");
    }
    
    String::from_utf8(data.to_vec())
        .map_err(|e| anyhow!("Invalid UTF-8: {}", e))
}
```

**错误降级**:

```rust
use anyhow::Result;

fn main() -> Result<()> {
    // 降级错误为警告
    if let Err(e) = optional_operation() {
        eprintln!("Warning: {:#}", e);
    }
    
    // 必须成功的操作
    critical_operation()?;
    
    Ok(())
}
```

---

### 2. thiserror (库层 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add thiserror`  
**用途**: 定义自定义错误类型

#### 基础用法2

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum DataStoreError {
    #[error("Data not found: {0}")]
    NotFound(String),
    
    #[error("Invalid input: {msg}")]
    InvalidInput { msg: String },
    
    #[error("IO error")]
    Io(#[from] std::io::Error),
    
    #[error("Parse error")]
    Parse(#[from] serde_json::Error),
    
    #[error("Unknown error")]
    Unknown,
}

// 使用
fn load_data(id: &str) -> Result<Data, DataStoreError> {
    if id.is_empty() {
        return Err(DataStoreError::InvalidInput {
            msg: "ID cannot be empty".to_string(),
        });
    }
    
    let content = std::fs::read_to_string(format!("data/{}.json", id))?;
    let data: Data = serde_json::from_str(&content)?;
    
    Ok(data)
}
```

#### 高级特性

**透明错误传播**:

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MyError {
    // 自动实现 From<std::io::Error>
    #[error("IO error")]
    Io(#[from] std::io::Error),
    
    // 自动实现 From<serde_json::Error>
    #[error("JSON error")]
    Json(#[from] serde_json::Error),
    
    // 透明传播，保留原始错误
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}
```

**带源错误的错误**:

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Invalid header (expected {expected:?}, found {found:?})")]
    InvalidHeader {
        expected: String,
        found: String,
    },
    
    #[error("Invalid field at line {line}")]
    InvalidField {
        line: usize,
        #[source]
        source: Box<dyn std::error::Error + Send + Sync>,
    },
}
```

---

### 3. eyre (增强报告 💡)

**添加依赖**: `cargo add eyre`  
**用途**: 增强的错误报告，带有更好的诊断信息

#### 基础用法3

```rust
use eyre::{Result, WrapErr};

fn main() -> Result<()> {
    let path = "config.toml";
    let config = std::fs::read_to_string(path)
        .wrap_err_with(|| format!("Failed to read config from {}", path))?;
    
    Ok(())
}
```

#### 美化错误报告

```rust
use eyre::{eyre, Result};

fn main() -> Result<()> {
    color_eyre::install()?;  // 安装彩色错误报告
    
    if std::env::var("API_KEY").is_err() {
        return Err(eyre!("API_KEY environment variable is not set"));
    }
    
    Ok(())
}
```

---

## 💡 最佳实践

### 1. 应用层 vs 库层

**应用层（使用 anyhow）**:

```rust
// src/main.rs
use anyhow::{Context, Result};

fn main() -> Result<()> {
    let config = load_config()
        .context("Failed to load configuration")?;
    
    run_app(config)?;
    
    Ok(())
}
```

**库层（使用 thiserror）**:

```rust
// src/lib.rs
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MyLibError {
    #[error("Configuration error: {0}")]
    Config(String),
    
    #[error("Network error")]
    Network(#[from] std::io::Error),
}

pub fn do_something() -> Result<(), MyLibError> {
    // ...
    Ok(())
}
```

### 2. 错误分层

```rust
// 领域错误
#[derive(Error, Debug)]
pub enum DomainError {
    #[error("User not found: {0}")]
    UserNotFound(String),
    
    #[error("Invalid email: {0}")]
    InvalidEmail(String),
}

// 基础设施错误
#[derive(Error, Debug)]
pub enum InfraError {
    #[error("Database error")]
    Database(#[from] sqlx::Error),
    
    #[error("Redis error")]
    Redis(#[from] redis::RedisError),
}

// 应用错误（聚合）
#[derive(Error, Debug)]
pub enum AppError {
    #[error("Domain error")]
    Domain(#[from] DomainError),
    
    #[error("Infrastructure error")]
    Infra(#[from] InfraError),
}
```

### 3. Web 框架集成

**Axum 示例**:

```rust
use axum::{
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use serde_json::json;

// 定义应用错误
#[derive(thiserror::Error, Debug)]
pub enum ApiError {
    #[error("Not found: {0}")]
    NotFound(String),
    
    #[error("Bad request: {0}")]
    BadRequest(String),
    
    #[error("Internal error")]
    Internal(#[from] anyhow::Error),
}

// 实现 IntoResponse
impl IntoResponse for ApiError {
    fn into_response(self) -> Response {
        let (status, message) = match self {
            ApiError::NotFound(msg) => (StatusCode::NOT_FOUND, msg),
            ApiError::BadRequest(msg) => (StatusCode::BAD_REQUEST, msg),
            ApiError::Internal(_) => (
                StatusCode::INTERNAL_SERVER_ERROR,
                "Internal server error".to_string(),
            ),
        };
        
        let body = Json(json!({
            "error": message,
        }));
        
        (status, body).into_response()
    }
}

// 使用
async fn get_user(user_id: String) -> Result<Json<User>, ApiError> {
    let user = fetch_user(&user_id)
        .await
        .ok_or_else(|| ApiError::NotFound(format!("User {} not found", user_id)))?;
    
    Ok(Json(user))
}
```

### 4. 错误恢复策略

```rust
use anyhow::Result;

fn main() -> Result<()> {
    // 策略1: 重试
    let data = retry(3, || fetch_data())?;
    
    // 策略2: 降级
    let config = load_config().unwrap_or_default();
    
    // 策略3: 缓存回退
    let result = fetch_fresh_data()
        .or_else(|_| load_from_cache())
        .context("Failed to get data from any source")?;
    
    Ok(())
}

fn retry<F, T, E>(times: usize, mut f: F) -> Result<T, E>
where
    F: FnMut() -> Result<T, E>,
{
    for _ in 0..times - 1 {
        if let ok @ Ok(_) = f() {
            return ok;
        }
    }
    f()
}
```

---

## 📊 工具对比

### 功能对比

| 特性 | anyhow | thiserror | eyre |
|------|--------|-----------|------|
| **使用场景** | 应用程序 | 库 | 应用程序 |
| **自定义错误** | ❌ | ✅✅ | ❌ |
| **上下文信息** | ✅✅ | ❌ | ✅✅ |
| **错误美化** | ✅ | ❌ | ✅✅ |
| **零成本抽象** | ✅ | ✅ | ✅ |
| **学习曲线** | 低 | 低 | 中 |

### 选择建议

```text
开发类型？
├─ 应用程序
│  ├─ 需要美化输出 → eyre
│  └─ 标准需求 → anyhow
└─ 库
   └─ 需要自定义错误 → thiserror
```

---

## 🎯 实战场景

### 场景1: CLI 工具

```rust
use anyhow::{Context, Result};
use clap::Parser;

#[derive(Parser)]
struct Cli {
    #[arg(short, long)]
    input: String,
    
    #[arg(short, long)]
    output: String,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    
    let content = std::fs::read_to_string(&cli.input)
        .with_context(|| format!("Failed to read input file: {}", cli.input))?;
    
    let processed = process(&content)
        .context("Failed to process content")?;
    
    std::fs::write(&cli.output, processed)
        .with_context(|| format!("Failed to write output file: {}", cli.output))?;
    
    println!("✅ Processing complete");
    Ok(())
}
```

### 场景2: 微服务

```rust
use thiserror::Error;

// 定义错误类型
#[derive(Error, Debug)]
pub enum ServiceError {
    #[error("Database error")]
    Database(#[from] sqlx::Error),
    
    #[error("Redis error")]
    Redis(#[from] redis::RedisError),
    
    #[error("HTTP error")]
    Http(#[from] reqwest::Error),
    
    #[error("Business logic error: {0}")]
    Business(String),
}

// 服务层
pub struct UserService {
    db: sqlx::PgPool,
    cache: redis::Client,
}

impl UserService {
    pub async fn get_user(&self, id: i64) -> Result<User, ServiceError> {
        // 尝试从缓存获取
        if let Ok(user) = self.get_from_cache(id).await {
            return Ok(user);
        }
        
        // 从数据库获取
        let user = sqlx::query_as::<_, User>("SELECT * FROM users WHERE id = $1")
            .bind(id)
            .fetch_one(&self.db)
            .await?;
        
        // 更新缓存
        self.set_cache(id, &user).await?;
        
        Ok(user)
    }
}
```

### 场景3: 异步错误处理

```rust
use anyhow::Result;
use tokio::task::JoinSet;

async fn process_batch(items: Vec<Item>) -> Result<Vec<Result<Output>>> {
    let mut set = JoinSet::new();
    
    for item in items {
        set.spawn(async move {
            process_item(item).await
        });
    }
    
    let mut results = Vec::new();
    while let Some(result) = set.join_next().await {
        results.push(result?);
    }
    
    Ok(results)
}
```

---

## 🔗 相关资源

- [Rust Error Handling Book](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [anyhow Documentation](https://docs.rs/anyhow/)
- [thiserror Documentation](https://docs.rs/thiserror/)
- [eyre Documentation](https://docs.rs/eyre/)

---

**导航**: [返回横切关注点](../README.md) | [下一类别：密码学](../cryptography/README.md)
