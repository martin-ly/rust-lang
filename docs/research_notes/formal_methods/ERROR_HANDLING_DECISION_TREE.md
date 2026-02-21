# Rust 错误处理决策树

> 一个系统化的错误处理策略选择指南

---

## 目录

1. [决策树总览](#决策树总览)
2. [决策维度详解](#决策维度详解)
3. [对比分析](#对比分析)
4. [最佳实践](#最佳实践)
5. [反模式警示](#反模式警示)
6. [代码示例](#代码示例)

---

## 决策树总览

```
                    ┌─────────────────────────────────────┐
                    │        开始错误处理决策              │
                    └───────────────┬─────────────────────┘
                                    │
                    ┌───────────────▼─────────────────────┐
                    │    错误是否可恢复？                  │
                    │    (能否继续程序执行？)              │
                    └───────┬───────────────┬─────────────┘
                            │               │
                    ┌───────▼───────┐   ┌───▼─────────────┐
                    │    是         │   │      否         │
                    │   (可恢复)    │   │   (不可恢复)    │
                    └───────┬───────┘   └───────┬─────────┘
                            │                   │
            ┌───────────────▼──────────┐   ┌───▼─────────────┐
            │ 错误传播范围？           │   │ 使用 panic!     │
            │                          │   │                 │
            └─┬──────────┬──────────┬──┘   │ • 程序bug       │
              │          │          │      │ • 契约违反      │
        ┌─────▼───┐ ┌────▼───┐ ┌───▼──┐   │ • 不可恢复状态  │
        │  本地   │ │ 跨函数 │ │跨线程│   └─────────────────┘
        │  处理   │ │ 传播   │ │/服务 │
        └────┬────┘ └───┬────┘ └─┬────┘
             │          │        │
    ┌────────▼────┐ ┌───▼────────▼──────────┐
    │ 立即处理    │ │ 使用 Result<T, E>     │
    │ (Option/   │ │                       │
    │  默认值)   │ │ • 库代码: thiserror   │
    └─────────────┘ │ • 应用: anyhow        │
                    │ • 跨服务: 序列化错误  │
                    └───────────────────────┘
```

---

## 决策维度详解

### 维度 1: 错误类型 - 可恢复 vs 不可恢复

| 特征 | 可恢复错误 | 不可恢复错误 |
|------|-----------|-------------|
| **定义** | 程序可以继续运行 | 程序状态已损坏，无法继续 |
| **示例** | 文件不存在、网络超时、无效输入 | 数组越界、空指针解引用、内部不一致 |
| **处理方式** | `Result<T, E>` | `panic!` |
| **恢复策略** | 重试、降级、返回错误 | 终止线程/进程 |

**决策问题**: *如果忽略这个错误，程序是否仍然处于有效状态？*

- **是** → 可恢复错误
- **否** → 不可恢复错误

---

### 维度 2: 错误传播范围

```
传播范围决策流程:

┌──────────────────────────────────────────────────────────────┐
│  错误发生在哪个边界？                                         │
└──────────────┬──────────────────┬──────────────┬─────────────┘
               │                  │              │
        ┌──────▼──────┐    ┌──────▼──────┐ ┌────▼────────┐
        │  函数内部   │    │  模块边界   │ │  系统边界   │
        │             │    │             │ │             │
        │ • 局部变量  │    │ • crate边界 │ │ • 线程边界  │
        │ • 临时计算  │    │ • 分层架构  │ │ • 进程边界  │
        │ • 内部状态  │    │ • 库接口    │ │ • 网络边界  │
        └──────┬──────┘    └──────┬──────┘ └─────┬───────┘
               │                  │              │
        ┌──────▼──────────────────▼──────────────▼───────┐
        │              选择传播机制                       │
        └──────────────┬─────────────────┬───────────────┘
                       │                 │
              ┌────────▼─────┐    ┌──────▼────────┐
              │ 本地处理     │    │ 错误传播      │
              │              │    │               │
              │ • unwrap/    │    │ • ? 操作符    │
              │   expect     │    │ • map_err     │
              │ • 默认值     │    │ • 错误转换    │
              │ • 内部状态   │    │ • 上下文包装  │
              └──────────────┘    └───────────────┘
```

#### 2.1 本地处理场景

| 场景 | 推荐方式 | 示例 |
|------|---------|------|
| 配置解析 | `expect` + 明确消息 | `config.parse::<u32>().expect("PORT must be a number")` |
| 默认值 | `unwrap_or` / `unwrap_or_else` | `timeout.unwrap_or(DEFAULT_TIMEOUT)` |
| 可选字段 | `Option` + `if let` | `if let Some(name) = user.nickname { ... }` |

#### 2.2 错误传播场景

| 边界类型 | 传播方式 | 注意事项 |
|---------|---------|---------|
| 函数边界 | `Result<T, E>` + `?` | 保持错误类型一致性 |
| 模块边界 | 定义模块级错误类型 | 使用 `thiserror` 派生 |
| Crate 边界 | 公开错误类型 | 文档化错误条件 |
| 线程边界 | `channel` + 专用错误类型 | 错误必须实现 `Send` |
| 异步边界 | `Result` in `Future` | 正确处理 `JoinHandle` |
| 服务边界 | 序列化错误 (JSON/Proto) | 包含错误码和消息 |

---

### 维度 3: 错误处理策略

```
┌──────────────────────────────────────────────────────────────┐
│                    选择处理策略                              │
└───────┬──────────────┬──────────────┬──────────────┬─────────┘
        │              │              │              │
   ┌────▼────┐   ┌────▼────┐   ┌─────▼─────┐  ┌─────▼─────┐
   │ 立即处理 │   │ 传播错误 │   │   重试    │  │   降级    │
   │         │   │         │   │           │  │           │
   │ 最简单  │   │ 最常见  │   │ 临时故障  │  │ 优雅失败  │
   └────┬────┘   └────┬────┘   └─────┬─────┘  └─────┬─────┘
        │             │              │              │
   ┌────▼─────────────┴──────────────┴──────────────┘
   │              策略选择矩阵                        │
   └────────────────────────────────────────────────┘
```

#### 策略选择矩阵

| 错误特征 | 立即处理 | 传播 | 重试 | 降级 | 典型场景 |
|---------|---------|------|------|------|---------|
| 配置错误 | ✅ | ❌ | ❌ | ❌ | 启动时检查 |
| 输入验证 | ✅ | ✅ | ❌ | ✅ | API 请求处理 |
| IO 错误 | ❌ | ✅ | ✅ | ✅ | 文件/网络操作 |
| 超时 | ❌ | ✅ | ✅ | ✅ | 外部服务调用 |
| 资源不足 | ❌ | ✅ | ✅ | ✅ | 内存/连接池 |
| 内部 Bug | ❌ | ❌ | ❌ | ❌ | `panic` |

#### 3.1 重试策略决策

```rust
// 重试决策树
fn should_retry(error: &Error) -> RetryDecision {
    match error.kind() {
        // 临时网络故障 → 重试
        ErrorKind::ConnectionRefused |
        ErrorKind::ConnectionReset |
        ErrorKind::ConnectionAborted |
        ErrorKind::TimedOut => RetryDecision::RetryWithBackoff,
        
        // 配置错误 → 不重试
        ErrorKind::InvalidInput |
        ErrorKind::NotFound => RetryDecision::FailFast,
        
        // 服务器错误 → 可能重试
        ErrorKind::Other => {
            if is_temporary(error) {
                RetryDecision::RetryWithBackoff
            } else {
                RetryDecision::FailFast
            }
        }
    }
}
```

#### 3.2 降级策略

| 服务状态 | 降级策略 | 示例 |
|---------|---------|------|
| 推荐服务不可用 | 使用缓存 | 显示上次推荐 |
| 认证服务超时 | 允许本地缓存凭证 | 短期免密登录 |
| 日志服务满载 | 丢弃日志 | 采样记录 |
| 数据库慢查询 | 返回简化数据 | 仅返回关键字段 |

---

### 维度 4: 库 vs 应用

```
┌─────────────────────────────────────────────────────────────┐
│                   库代码 (Library)                          │
├─────────────────────────────────────────────────────────────┤
│  目标: 提供精确、可操作的错误信息                            │
│  原则: 不假设使用场景，让调用者决定如何处理                    │
└─────────────────────────────────────────────────────────────┘
                              │
                    ┌─────────▼─────────┐
                    │ 使用 thiserror    │
                    │                   │
                    │ • 结构化错误类型  │
                    │ • 错误分类        │
                    │ • 可匹配的错误    │
                    │ • 零开销抽象      │
                    └───────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                  应用程序 (Application)                      │
├─────────────────────────────────────────────────────────────┤
│  目标: 快速开发，友好的错误报告                              │
│  原则: 统一错误处理，关注用户体验                            │
└─────────────────────────────────────────────────────────────┘
                              │
                    ┌─────────▼─────────┐
                    │ 使用 anyhow       │
                    │                   │
                    │ • 动态错误类型    │
                    │ • 自动上下文      │
                    │ • 链式错误追踪    │
                    │ • 开发效率高      │
                    └───────────────────┘
```

#### 对比表

| 方面 | 库代码 (Library) | 应用程序 (Application) |
|-----|-----------------|----------------------|
| **错误库** | `thiserror` | `anyhow` |
| **错误类型** | 具体、可枚举 | 动态、上下文丰富 |
| **错误转换** | 显式 `From` 实现 | 自动转换 |
| **错误匹配** | 用户可 `match` | 通常只报告 |
| **性能考虑** | 重要 | 相对次要 |
| **二进制大小** | 敏感 | 相对次要 |

---

## 对比分析

### Result vs Option vs panic

```
┌─────────────────────────────────────────────────────────────────┐
│                    Result<T, E>                                  │
├─────────────────────────────────────────────────────────────────┤
│  何时使用: 操作可能失败，调用者需要知道失败原因                  │
│  返回: Ok(T) 或 Err(E)                                          │
│  传播: ? 操作符                                                  │
└─────────────────────────────────────────────────────────────────┘
                              │
              ┌───────────────┴───────────────┐
              │                               │
    ┌─────────▼──────────┐        ┌───────────▼───────────┐
    │   Option<T>        │        │      panic!           │
    ├────────────────────┤        ├───────────────────────┤
    │ 何时使用: 值可能    │        │ 何时使用: 程序状态    │
    │ 不存在 (None)       │        │ 已损坏，无法恢复      │
    │                     │        │                       │
    │ 示例: 查找、可选    │        │ 示例: 内部不一致、    │
    │ 字段、缓存          │        │ 越界访问、契约违反    │
    │                     │        │                       │
    │ 转换: ok_or() 可    │        │ 替代: 在库中使用      │
    │ 转为 Result         │        │ Result + assert!      │
    └────────────────────┘        └───────────────────────┘
```

#### 详细对比

| 特性 | `Result<T, E>` | `Option<T>` | `panic!` |
|-----|---------------|-------------|----------|
| **用途** | 可恢复错误 | 可选值 | 不可恢复错误 |
| **错误信息** | 丰富 (E) | 无 (仅 None) | 消息 + 回溯 |
| **传播** | `?` 操作符 | `?` 操作符 (需转换) | 不可传播 |
| **性能开销** | 正常 | 最小 | 高 (展开栈) |
| **编译时检查** | 强制处理 | 强制处理 | 无 |
| **适用边界** | 库/应用边界 | 函数内部 | 仅程序终止 |

#### 转换关系

```rust
// Option → Result
let result = option.ok_or(Error::NotFound)?;
let result = option.ok_or_else(|| Error::compute())?;

// Result → Option
let option = result.ok();           // 丢弃错误
let option = result.err();          // 仅保留错误

// Result → panic (显式选择)
let value = result.expect("critical: must succeed");
let value = result.unwrap();        // 仅用于原型/测试
```

---

### thiserror vs anyhow

```
┌────────────────────────────────────────────────────────────────┐
│                      thiserror                                 │
│                      (库代码)                                   │
├────────────────────────────────────────────────────────────────┤
│ 设计哲学: 编译时确定错误类型，零运行时开销                       │
│ 核心特性:                                                      │
│   • #[derive(Error)] 自动实现 std::error::Error                │
│   • #[error("...")] 自定义 Display                             │
│   • #[from] 自动 From 实现                                     │
│   • #[source] 错误链                                           │
└────────────────────────────────────────────────────────────────┘

┌────────────────────────────────────────────────────────────────┐
│                      anyhow                                    │
│                      (应用代码)                                 │
├────────────────────────────────────────────────────────────────┤
│ 设计哲学: 运行时动态错误，关注开发效率                           │
│ 核心特性:                                                      │
│   • anyhow::Error 作为统一错误类型                             │
│   • .context() 添加上下文                                       │
│   • 自动回溯支持                                                │
│   • 与 ? 操作符无缝集成                                         │
└────────────────────────────────────────────────────────────────┘
```

#### 详细对比

| 特性 | `thiserror` | `anyhow` |
|-----|-------------|----------|
| **目标** | 库开发 | 应用开发 |
| **错误类型** | 静态、具体 | 动态、类型擦除 |
| **错误匹配** | 支持 (`match`) | 不支持 (通常) |
| **上下文** | 手动添加 | `.context()` 链式 |
| **回溯** | 需手动实现 | 内置支持 |
| **编译时开销** | 零 | 极小 |
| **运行时开销** | 零 | 极小 |
| **典型使用** | 定义错误枚举 | 函数返回类型 |

#### 混合使用模式

```rust
// 库代码 (lib.rs)
use thiserror::Error;

#[derive(Error, Debug)]
pub enum DataError {
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("parse error: {0}")]
    Parse(String),
    
    #[error("not found: {0}")]
    NotFound(String),
}

pub fn load_data(path: &str) -> Result<Data, DataError> {
    // 返回具体的 DataError
}

// 应用代码 (main.rs)
use anyhow::{Context, Result};

fn main() -> Result<()> {
    let data = my_lib::load_data("config.json")
        .context("failed to load application config")?;
    // 转换为 anyhow::Error，添加上下文
    
    Ok(())
}
```

---

### 自定义错误类型设计

```
┌────────────────────────────────────────────────────────────────┐
│                   错误类型设计层次                              │
└───────────────┬────────────────────────────────────────────────┘
                │
    ┌───────────▼────────────┐
    │  单层错误 (简单场景)   │
    │                        │
    │ enum Error {           │
    │     NotFound,          │
    │     InvalidInput,      │
    │     Io(std::io::Error),│
    │ }                      │
    └───────────┬────────────┘
                │
    ┌───────────▼────────────┐
    │ 分层错误 (复杂场景)    │
    │                        │
    │ enum AppError {        │
    │     Config(ConfigError),│
    │     Network(NetworkError),│
    │     Database(DbError), │
    │ }                      │
    │                        │
    │ // 每层定义自己的错误  │
    └───────────┬────────────┘
                │
    ┌───────────▼────────────┐
    │ 结构化错误 (API场景)   │
    │                        │
    │ struct ApiError {      │
    │     code: ErrorCode,   │
    │     message: String,   │
    │     details: Value,    │
    │     request_id: Uuid,  │
    │ }                      │
    └────────────────────────┘
```

#### 设计原则

| 原则 | 说明 | 示例 |
|-----|------|------|
| **正交分类** | 错误类别不重叠 | `NetworkError` vs `ParseError` |
| **信息丰富** | 包含诊断所需信息 | `NotFound { resource: String, id: String }` |
| **可序列化** | API 边界需支持序列化 | `#[derive(Serialize)]` |
| **可匹配** | 用户能针对性处理 | `Error::NotFound { .. }` |
| **向后兼容** | 添加变体不破坏 API | `#[non_exhaustive]` |

#### 推荐模式

```rust
use thiserror::Error;
use serde::Serialize;

// 错误码设计
#[derive(Error, Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[non_exhaustive]
pub enum ErrorCode {
    #[error("not_found")]
    NotFound = 404,
    
    #[error("invalid_input")]
    InvalidInput = 400,
    
    #[error("internal_error")]
    InternalError = 500,
}

// 结构化错误
#[derive(Error, Debug, Serialize)]
#[error("{code}: {message}")]
pub struct ApiError {
    pub code: ErrorCode,
    pub message: String,
    #[serde(skip)]
    pub source: Option<Box<dyn std::error::Error + Send + Sync>>,
    pub request_id: uuid::Uuid,
}

// 分层模块错误
#[derive(Error, Debug)]
pub enum AppError {
    #[error("configuration error: {0}")]
    Config(#[from] config::ConfigError),
    
    #[error("database error: {0}")]
    Database(#[from] db::DbError),
    
    #[error("external service error: {0}")]
    External(#[from] external::ServiceError),
    
    #[error("internal error: {0}")]
    Internal(String),
}
```

---

### 错误链和上下文

```
错误链结构:

┌────────────────────────────────────────────────────────────────┐
│ 顶层: 用户友好的错误消息                                        │
│ "Failed to load user profile"                                  │
├────────────────────────────────────────────────────────────────┤
│ 第1层: 操作上下文                                               │
│ "while parsing config file '/etc/app/config.yaml'"             │
├────────────────────────────────────────────────────────────────┤
│ 第2层: 底层错误                                                 │
│ "invalid YAML syntax at line 42, column 10"                    │
├────────────────────────────────────────────────────────────────┤
│ 第3层: 系统错误                                                 │
│ "expected ':', found '}'"                                      │
└────────────────────────────────────────────────────────────────┘
```

#### anyhow 上下文链

```rust
use anyhow::{Context, Result};

fn process_user(user_id: Uuid) -> Result<()> {
    let user = db::find_user(user_id)
        .with_context(|| format!("failed to find user {}", user_id))?;
    
    let config = fs::read_to_string(&user.config_path)
        .with_context(|| format!("failed to read config at {}", user.config_path))?;
    
    let settings: Settings = serde_yaml::from_str(&config)
        .context("failed to parse config as YAML")?;
    
    apply_settings(user_id, settings)
        .context("failed to apply settings")?;
    
    Ok(())
}

// 输出:
// Error: failed to apply settings
// 
// Caused by:
//   0: failed to parse config as YAML
//   1: invalid YAML syntax at line 42, column 10
//   2: while reading config at /home/user/.config/app.yaml
//   3: failed to find user 550e8400-e29b-41d4-a716-446655440000
```

#### thiserror 错误源

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ConfigError {
    #[error("failed to read config file: {path}")]
    Read {
        path: String,
        #[source]
        source: std::io::Error,
    },
    
    #[error("failed to parse config: {message}")]
    Parse {
        message: String,
        #[source]
        source: serde_yaml::Error,
    },
}

// 使用
fn load_config(path: &str) -> Result<Config, ConfigError> {
    let content = fs::read_to_string(path)
        .map_err(|e| ConfigError::Read {
            path: path.to_string(),
            source: e,
        })?;
    
    serde_yaml::from_str(&content)
        .map_err(|e| ConfigError::Parse {
            message: format!("invalid YAML in {}", path),
            source: e,
        })
}
```

---

## 最佳实践

### 1. 错误类型设计模式

#### 模式 A: 分层错误架构

```rust
// 领域层错误
#[derive(Error, Debug)]
pub enum DomainError {
    #[error("validation failed: {0}")]
    Validation(String),
    
    #[error("business rule violated: {0}")]
    BusinessRule(String),
}

// 应用层错误
#[derive(Error, Debug)]
pub enum ApplicationError {
    #[error("domain error: {0}")]
    Domain(#[from] DomainError),
    
    #[error("infrastructure error: {0}")]
    Infrastructure(#[source] InfrastructureError),
}

// 接口层错误
#[derive(Error, Debug, Serialize)]
#[serde(tag = "type", content = "detail")]
#[non_exhaustive]
pub enum ApiError {
    #[error("bad_request")]
    BadRequest { message: String },
    
    #[error("not_found")]
    NotFound { resource: String },
    
    #[error("internal_error")]
    InternalError { request_id: Uuid },
}

// 错误转换
impl From<ApplicationError> for ApiError {
    fn from(err: ApplicationError) -> Self {
        match err {
            ApplicationError::Domain(d) => ApiError::BadRequest {
                message: d.to_string(),
            },
            ApplicationError::Infrastructure(_) => ApiError::InternalError {
                request_id: Uuid::new_v4(),
            },
        }
    }
}
```

#### 模式 B: 错误状态码映射

```rust
pub trait HttpStatusCode {
    fn status_code(&self) -> StatusCode;
}

impl HttpStatusCode for ApiError {
    fn status_code(&self) -> StatusCode {
        match self {
            ApiError::BadRequest { .. } => StatusCode::BAD_REQUEST,
            ApiError::NotFound { .. } => StatusCode::NOT_FOUND,
            ApiError::Unauthorized => StatusCode::UNAUTHORIZED,
            ApiError::Forbidden => StatusCode::FORBIDDEN,
            ApiError::InternalError { .. } => StatusCode::INTERNAL_SERVER_ERROR,
        }
    }
}
```

#### 模式 C: 错误 Builder

```rust
#[derive(Debug)]
pub struct ErrorBuilder {
    code: ErrorCode,
    message: Option<String>,
    source: Option<Box<dyn std::error::Error + Send + Sync>>,
    context: HashMap<String, String>,
}

impl ErrorBuilder {
    pub fn new(code: ErrorCode) -> Self {
        Self {
            code,
            message: None,
            source: None,
            context: HashMap::new(),
        }
    }
    
    pub fn message(mut self, msg: impl Into<String>) -> Self {
        self.message = Some(msg.into());
        self
    }
    
    pub fn source(mut self, err: impl Into<Box<dyn std::error::Error + Send + Sync>>) -> Self {
        self.source = Some(err.into());
        self
    }
    
    pub fn context(mut self, key: &str, value: impl Into<String>) -> Self {
        self.context.insert(key.to_string(), value.into());
        self
    }
    
    pub fn build(self) -> AppError {
        AppError {
            code: self.code,
            message: self.message.unwrap_or_else(|| self.code.to_string()),
            source: self.source,
            context: self.context,
        }
    }
}

// 使用
let err = ErrorBuilder::new(ErrorCode::NotFound)
    .message("user not found")
    .context("user_id", user_id.to_string())
    .context("operation", "login")
    .build();
```

---

### 2. 错误转换和映射

#### 2.1 自动转换 (`From` trait)

```rust
use std::io;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("io error: {0}")]
    Io(#[from] io::Error),
    
    #[error("parse error: {0}")]
    Parse(#[from] serde_json::Error),
    
    #[error("database error: {0}")]
    Database(#[from] sqlx::Error),
}

// 现在 ? 会自动转换
fn read_config() -> Result<Config, AppError> {
    let content = fs::read_to_string("config.json")?; // io::Error → AppError
    let config = serde_json::from_str(&content)?;      // serde_json::Error → AppError
    Ok(config)
}
```

#### 2.2 映射错误 (`map_err`)

```rust
// 当需要自定义错误信息时
fn parse_port(s: &str) -> Result<u16, AppError> {
    s.parse::<u16>()
        .map_err(|e| AppError::InvalidPort {
            input: s.to_string(),
            source: e,
        })
}

// 或者使用 anyhow 添加上下文
fn load_users() -> Result<Vec<User>> {
    db::query("SELECT * FROM users")
        .fetch_all()
        .await
        .map_err(|e| anyhow!("failed to load users from database: {}", e))
}
```

#### 2.3 错误类型转换矩阵

| 从 / 到 | `Result<T, E1>` | `Result<T, E2>` | `Option<T>` | `panic` |
|--------|----------------|----------------|-------------|---------|
| `Result<T, E>` | `map_err` | `map_err` + `From` | `ok()` | `unwrap` |
| `Option<T>` | `ok_or` | `ok_or` + `From` | - | `unwrap` |
| `panic` | 捕获 (`catch_unwind`) | 捕获 + 转换 | 不支持 | - |

---

### 3. 错误报告和日志

#### 3.1 结构化日志集成

```rust
use tracing::{error, warn, info, instrument};

#[instrument(skip(db), fields(user_id = %user_id))]
async fn authenticate_user(
    db: &Database,
    user_id: Uuid,
    token: &str,
) -> Result<User, AuthError> {
    info!("attempting authentication");
    
    let user = db.find_user(user_id)
        .await
        .map_err(|e| {
            error!(
                error = %e,
                "database query failed"
            );
            AuthError::Database(e)
        })?;
    
    if !verify_token(&user, token) {
        warn!(
            token_prefix = %&token[..4],
            "invalid token provided"
        );
        return Err(AuthError::InvalidToken);
    }
    
    info!("authentication successful");
    Ok(user)
}
```

#### 3.2 用户友好的错误报告

```rust
pub fn format_error_report(err: &anyhow::Error) -> String {
    let mut report = String::new();
    
    // 用户友好的顶层消息
    report.push_str("操作失败: ");
    report.push_str(&err.to_string());
    report.push('\n');
    
    // 建议的解决步骤
    report.push_str("\n建议:\n");
    report.push_str(&suggest_fixes(err));
    
    // 技术细节（用于调试）
    report.push_str("\n\n技术详情:\n");
    for (i, cause) in err.chain().enumerate() {
        report.push_str(&format!("  {}: {}\n", i, cause));
    }
    
    // 回溯（如果有）
    if let Some(backtrace) = err.backtrace() {
        report.push_str("\n回溯:\n");
        report.push_str(&format!("{:?}", backtrace));
    }
    
    report
}

fn suggest_fixes(err: &anyhow::Error) -> String {
    if err.to_string().contains("connection refused") {
        "1. 检查服务是否正在运行\n2. 检查网络连接\n3. 验证端口号是否正确".to_string()
    } else if err.to_string().contains("permission denied") {
        "1. 检查文件权限\n2. 尝试使用 sudo 运行\n3. 更改文件所有者".to_string()
    } else {
        "请联系技术支持".to_string()
    }
}
```

#### 3.3 错误聚合和监控

```rust
use metrics::{counter, gauge, histogram};

pub fn report_error(err: &AppError) {
    // 按错误类型计数
    counter!("app.errors.total", 1, "type" => error_type_name(err));
    
    // 按错误码计数
    if let Some(code) = error_code(err) {
        counter!("app.errors.by_code", 1, "code" => code.to_string());
    }
    
    // 严重错误告警
    if is_critical(err) {
        counter!("app.errors.critical", 1);
        // 发送告警通知
    }
}
```

---

### 4. 测试错误处理

#### 4.1 测试错误类型

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_error_conversion() {
        let io_err = std::io::Error::new(
            std::io::ErrorKind::NotFound,
            "file not found"
        );
        
        let app_err: AppError = io_err.into();
        
        assert!(matches!(app_err, AppError::Io(_)));
        assert!(app_err.to_string().contains("file not found"));
    }
    
    #[test]
    fn test_error_downcast() {
        let err: anyhow::Error = ConfigError::NotFound {
            path: "/etc/config".into(),
        }.into();
        
        // 可以 downcast 回具体类型
        assert!(err.downcast_ref::<ConfigError>().is_some());
        
        // 检查具体变体
        if let Some(ConfigError::NotFound { path }) = err.downcast_ref() {
            assert_eq!(path, "/etc/config");
        }
    }
}
```

#### 4.2 测试错误传播

```rust
#[test]
fn test_error_propagation() {
    // 使用 assert_matches! (需要 nightly) 或自定义宏
    let result = load_config("nonexistent.json");
    
    match result {
        Err(AppError::Config(ConfigError::Read { path, .. })) => {
            assert_eq!(path, "nonexistent.json");
        }
        Ok(_) => panic!("expected error"),
        Err(e) => panic!("wrong error type: {:?}", e),
    }
}
```

#### 4.3 测试错误处理逻辑

```rust
#[tokio::test]
async fn test_retry_logic() {
    let mut attempts = 0;
    let result = retry_with_backoff(
        || {
            attempts += 1;
            if attempts < 3 {
                Err(io::Error::new(io::ErrorKind::TimedOut, "timeout"))
            } else {
                Ok("success")
            }
        },
        RetryPolicy::default(),
    ).await;
    
    assert!(result.is_ok());
    assert_eq!(attempts, 3);
}

#[tokio::test]
async fn test_circuit_breaker() {
    let mut cb = CircuitBreaker::new(3, Duration::from_secs(60));
    
    // 触发断路器
    for _ in 0..3 {
        cb.call(|| async { Err::<(), _>(io::Error::new(io::ErrorKind::Other, "fail")) }).await.ok();
    }
    
    // 断路器应打开
    assert!(cb.is_open());
    
    // 后续请求应快速失败
    let result = cb.call(|| async { Ok(()) }).await;
    assert!(matches!(result, Err(CircuitBreakerError::Open)));
}
```

---

## 反模式警示

### ❌ 反模式 1: 滥用 `unwrap()`

```rust
// ❌ 错误: 生产代码中使用 unwrap
let config = fs::read_to_string("config.json").unwrap();
let port = config.parse::<u16>().unwrap();

// ✅ 正确: 使用 ? 传播错误
let config = fs::read_to_string("config.json")
    .context("failed to read config")?;
let port = config.parse::<u16>()
    .context("invalid port number")?;

// ✅ 仅在以下情况使用 unwrap:
// 1. 测试代码
// 2. 静态已知为 Some/Ok 的情况
// 3. 使用 expect 提供有意义的错误消息
let val = Some(42).expect("this is a bug: value should exist");
```

### ❌ 反模式 2: 过度使用 `String` 作为错误

```rust
// ❌ 错误: 使用 String 丢失类型安全
fn do_something() -> Result<(), String> {
    Err("something went wrong".to_string())
}

// ❌ 错误: 调用者无法匹配具体错误
match do_something() {
    Err(s) if s.contains("not found") => ..., // 脆弱
    _ => ...,
}

// ✅ 正确: 使用结构化错误类型
#[derive(Error, Debug)]
enum MyError {
    #[error("not found: {0}")]
    NotFound(String),
    #[error("invalid input: {0}")]
    InvalidInput(String),
}

match do_something() {
    Err(MyError::NotFound(_)) => ..., // 类型安全
    Err(MyError::InvalidInput(_)) => ...,
    _ => ...,
}
```

### ❌ 反模式 3: 错误的 `?` 使用导致信息丢失

```rust
// ❌ 错误: 丢失了上下文信息
fn process_file(path: &str) -> Result<Data, io::Error> {
    let content = fs::read_to_string(path)?;
    let data = parse(&content)?; // parse 返回 Result<Data, ParseError>
                                 // 但函数签名强制转换为 io::Error
                                 // 丢失了原始错误信息
}

// ✅ 正确: 使用合适的错误类型
fn process_file(path: &str) -> Result<Data, AppError> {
    let content = fs::read_to_string(path)?;
    let data = parse(&content)?; // ParseError 自动转换为 AppError
    Ok(data)
}

// ✅ 或者使用 anyhow 保留所有错误
fn process_file(path: &str) -> Result<Data> {
    let content = fs::read_to_string(path)
        .with_context(|| format!("reading {}", path))?;
    let data = parse(&content)
        .context("parsing content")?;
    Ok(data)
}
```

### ❌ 反模式 4: 混淆 `Option` 和 `Result`

```rust
// ❌ 错误: Option 表示错误
fn find_user(id: Uuid) -> Option<User> {
    // 如果数据库连接失败返回 None?
    // 调用者无法区分 "不存在" 和 "出错了"
}

// ✅ 正确: Result 表示操作可能失败
fn find_user(id: Uuid) -> Result<Option<User>, DbError> {
    // Ok(None) = 用户不存在
    // Ok(Some(user)) = 找到用户
    // Err(e) = 数据库错误
}

// ✅ 或者使用自定义错误明确语义
#[derive(Error, Debug)]
enum FindUserError {
    #[error("user not found")]
    NotFound,
    #[error("database error: {0}")]
    Database(#[from] DbError),
}

fn find_user(id: Uuid) -> Result<User, FindUserError> {
    // ...
}
```

### ❌ 反模式 5: 忽略错误

```rust
// ❌ 错误: 完全忽略错误
let _ = file.write_all(data);

// ❌ 错误: 空 match 分支
match write_file(path, data) {
    Ok(_) => {},
    Err(_) => {}, // 静默吞掉错误!
}

// ✅ 正确: 至少记录错误
if let Err(e) = file.write_all(data) {
    log::error!("failed to write file: {}", e);
}

// ✅ 正确: 使用 let_else 语法
let Ok(result) = operation() else {
    return Err(error.into());
};

// ✅ 正确: 如果确实应该忽略，明确注释
let _ = cache.insert(key, value); // 缓存失败可接受
```

### ❌ 反模式 6: 过度详细的错误类型

```rust
// ❌ 错误: 过于详细的错误枚举
#[derive(Error, Debug)]
enum DatabaseError {
    #[error("connection timeout after 30s")]
    ConnectionTimeout30s,
    #[error("connection timeout after 60s")]
    ConnectionTimeout60s,
    #[error("mysql connection failed")]
    MySqlConnectionFailed,
    #[error("postgres connection failed")]
    PostgresConnectionFailed,
    // ... 数百个变体
}

// ✅ 正确: 结构化错误信息
#[derive(Error, Debug)]
enum DatabaseError {
    #[error("connection timeout after {duration}s")]
    ConnectionTimeout { duration: u64 },
    
    #[error("connection failed: {backend}")]
    ConnectionFailed { backend: BackendType },
    
    #[error("query failed: {message}")]
    QueryFailed { message: String },
}
```

### ❌ 反模式 7: 跨线程边界传递非 Send 错误

```rust
// ❌ 错误: Rc 不能跨线程
#[derive(Error, Debug)]
enum BadError {
    #[error("inner: {0}")]
    Inner(Rc<dyn std::error::Error>), // Rc 不是 Send!
}

// ❌ 这会导致编译错误
async fn bad_function() -> Result<(), BadError> {
    tokio::spawn(async move {
        Err(BadError::Inner(Rc::new(io::Error::new(...))))
    }).await.unwrap()
}

// ✅ 正确: 使用 Arc 或 Box
#[derive(Error, Debug)]
enum GoodError {
    #[error("inner: {0}")]
    Inner(#[source] Box<dyn std::error::Error + Send + Sync>),
}
```

### ❌ 反模式 8: 在热路径中创建错误字符串

```rust
// ❌ 错误: 每次调用都分配字符串，即使成功
fn parse_hot(input: &[u8]) -> Result<Item, String> {
    if input.is_empty() {
        return Err(format!("empty input at {}", location())); // 分配!
    }
    // ... 解析逻辑
}

// ✅ 正确: 使用静态错误或延迟格式化
#[derive(Error, Debug)]
enum ParseError {
    #[error("empty input")]
    EmptyInput,
    #[error("invalid byte at position {pos}: 0x{byte:02x}")]
    InvalidByte { pos: usize, byte: u8 },
}

// 或使用 thiserror 的 lazy format
#[derive(Error, Debug)]
enum LazyError {
    #[error("error at {location}")]
    At { location: &'static str },
}
```

---

## 代码示例

### 完整示例 1: 分层错误处理架构

```rust
//! 完整的多层错误处理示例

use std::collections::HashMap;
use thiserror::Error;
use anyhow::{Context, Result as AnyhowResult};
use serde::{Serialize, Deserialize};
use uuid::Uuid;

// ==================== 领域层 (Domain Layer) ====================

pub mod domain {
    use super::*;
    
    #[derive(Error, Debug, Clone, PartialEq)]
    pub enum ValidationError {
        #[error("field '{field}' is required")]
        Required { field: String },
        
        #[error("field '{field}' must be at least {min} characters")]
        TooShort { field: String, min: usize },
        
        #[error("invalid email format: {email}")]
        InvalidEmail { email: String },
    }
    
    #[derive(Error, Debug, Clone, PartialEq)]
    pub enum BusinessError {
        #[error("user already exists: {email}")]
        DuplicateUser { email: String },
        
        #[error("insufficient balance: required {required}, available {available}")]
        InsufficientBalance { required: f64, available: f64 },
        
        #[error("operation not permitted for user status: {status}")]
        InvalidStatus { status: String },
    }
    
    pub type DomainResult<T> = Result<T, DomainError>;
    
    #[derive(Error, Debug, Clone, PartialEq)]
    pub enum DomainError {
        #[error("validation failed: {0}")]
        Validation(#[from] ValidationError),
        
        #[error("business rule violated: {0}")]
        Business(#[from] BusinessError),
    }
}

// ==================== 应用层 (Application Layer) ====================

pub mod application {
    use super::*;
    use super::domain::*;
    
    #[derive(Error, Debug)]
    pub enum InfrastructureError {
        #[error("database error: {0}")]
        Database(String),
        
        #[error("cache error: {0}")]
        Cache(String),
        
        #[error("external service error: {code} - {message}")]
        ExternalService { code: u16, message: String },
    }
    
    #[derive(Error, Debug)]
    pub enum ApplicationError {
        #[error(transparent)]
        Domain(#[from] DomainError),
        
        #[error(transparent)]
        Infrastructure(#[from] InfrastructureError),
        
        #[error("concurrent modification detected")]
        ConcurrentModification,
        
        #[error("operation timeout after {0:?}")]
        Timeout(std::time::Duration),
    }
    
    pub type AppResult<T> = Result<T, ApplicationError>;
}

// ==================== 接口层 (Interface Layer) ====================

pub mod interface {
    use super::*;
    use super::application::*;
    use super::domain::*;
    
    #[derive(Debug, Serialize, Deserialize)]
    #[serde(rename_all = "snake_case")]
    pub enum ErrorCode {
        BadRequest = 400,
        Unauthorized = 401,
        Forbidden = 403,
        NotFound = 404,
        Conflict = 409,
        UnprocessableEntity = 422,
        InternalError = 500,
        ServiceUnavailable = 503,
    }
    
    #[derive(Debug, Serialize)]
    pub struct ApiErrorResponse {
        pub code: ErrorCode,
        pub message: String,
        pub request_id: Uuid,
        #[serde(skip_serializing_if = "Option::is_none")]
        pub details: Option<serde_json::Value>,
        #[serde(skip_serializing_if = "Option::is_none")]
        pub help_url: Option<String>,
    }
    
    #[derive(Error, Debug)]
    #[error("API error: {response:?}")]
    pub struct ApiError {
        response: ApiErrorResponse,
    }
    
    impl ApiError {
        pub fn from_app_error(err: ApplicationError, request_id: Uuid) -> Self {
            let (code, message, details) = match &err {
                ApplicationError::Domain(d) => match d {
                    DomainError::Validation(v) => (
                        ErrorCode::BadRequest,
                        v.to_string(),
                        Some(json!({"validation_error": v})),
                    ),
                    DomainError::Business(b) => match b {
                        BusinessError::DuplicateUser { .. } => (
                            ErrorCode::Conflict,
                            b.to_string(),
                            None,
                        ),
                        BusinessError::InsufficientBalance { .. } => (
                            ErrorCode::UnprocessableEntity,
                            b.to_string(),
                            None,
                        ),
                        _ => (
                            ErrorCode::BadRequest,
                            b.to_string(),
                            None,
                        ),
                    },
                },
                ApplicationError::Infrastructure(i) => match i {
                    InfrastructureError::Database(_) => (
                        ErrorCode::InternalError,
                        "internal server error".to_string(),
                        None,
                    ),
                    InfrastructureError::ExternalService { code, .. } if *code >= 500 => (
                        ErrorCode::ServiceUnavailable,
                        "upstream service unavailable".to_string(),
                        None,
                    ),
                    _ => (
                        ErrorCode::InternalError,
                        "internal server error".to_string(),
                        None,
                    ),
                },
                ApplicationError::Timeout(_) => (
                    ErrorCode::ServiceUnavailable,
                    "request timeout".to_string(),
                    None,
                ),
                _ => (
                    ErrorCode::InternalError,
                    "internal server error".to_string(),
                    None,
                ),
            };
            
            Self {
                response: ApiErrorResponse {
                    code,
                    message,
                    request_id,
                    details,
                    help_url: None,
                },
            }
        }
        
        pub fn into_response(self) -> ApiErrorResponse {
            self.response
        }
    }
}

// ==================== 使用示例 ====================

use domain::*;
use application::*;
use interface::*;

fn validate_user_input(email: &str, name: &str) -> DomainResult<()> {
    if email.is_empty() {
        return Err(ValidationError::Required {
            field: "email".to_string(),
        }.into());
    }
    
    if !email.contains('@') {
        return Err(ValidationError::InvalidEmail {
            email: email.to_string(),
        }.into());
    }
    
    if name.len() < 2 {
        return Err(ValidationError::TooShort {
            field: "name".to_string(),
            min: 2,
        }.into());
    }
    
    Ok(())
}

fn create_user(email: String, name: String) -> AppResult<User> {
    validate_user_input(&email, &name)?;
    
    // 模拟检查重复用户
    if email == "exists@example.com" {
        return Err(BusinessError::DuplicateUser { email }.into());
    }
    
    // 模拟数据库操作
    if email == "db_error@example.com" {
        return Err(InfrastructureError::Database(
            "connection refused".to_string()
        ).into());
    }
    
    Ok(User { email, name })
}

#[derive(Debug)]
struct User {
    email: String,
    name: String,
}

// HTTP 处理函数
fn handle_create_user(email: String, name: String) -> Result<ApiErrorResponse, ApiErrorResponse> {
    let request_id = Uuid::new_v4();
    
    match create_user(email, name) {
        Ok(user) => {
            println!("Created user: {:?}", user);
            // 返回成功响应
            unimplemented!()
        }
        Err(e) => {
            let api_error = ApiError::from_app_error(e, request_id);
            Err(api_error.into_response())
        }
    }
}

fn main() {
    // 成功场景
    println!("=== Test 1: Valid input ===");
    match handle_create_user("user@example.com".to_string(), "John".to_string()) {
        Ok(_) => println!("Success"),
        Err(e) => println!("Error: {:?}", e),
    }
    
    // 验证错误
    println!("\n=== Test 2: Invalid email ===");
    match handle_create_user("invalid-email".to_string(), "John".to_string()) {
        Ok(_) => println!("Success"),
        Err(e) => println!("Error: {:?}", e),
    }
    
    // 业务错误
    println!("\n=== Test 3: Duplicate user ===");
    match handle_create_user("exists@example.com".to_string(), "John".to_string()) {
        Ok(_) => println!("Success"),
        Err(e) => println!("Error: {:?}", e),
    }
    
    // 基础设施错误
    println!("\n=== Test 4: Database error ===");
    match handle_create_user("db_error@example.com".to_string(), "John".to_string()) {
        Ok(_) => println!("Success"),
        Err(e) => println!("Error: {:?}", e),
    }
}
```

### 完整示例 2: 带重试和断路器的错误处理

```rust
//! 生产级错误处理：重试、断路器、超时

use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::time::sleep;
use thiserror::Error;

// ==================== 错误定义 ====================

#[derive(Error, Debug, Clone)]
pub enum RetryError<E> {
    #[error("max retries exceeded after {attempts} attempts")]
    MaxRetriesExceeded { attempts: u32, last_error: E },
    
    #[error("non-retryable error: {0}")]
    NonRetryable(E),
}

#[derive(Error, Debug, Clone)]
pub enum CircuitBreakerError {
    #[error("circuit breaker is open")]
    Open,
    
    #[error("half-open state rejected request")]
    HalfOpenRejected,
}

// ==================== 重试策略 ====================

#[derive(Debug, Clone, Copy)]
pub struct RetryPolicy {
    pub max_attempts: u32,
    pub base_delay: Duration,
    pub max_delay: Duration,
    pub backoff_multiplier: f64,
}

impl Default for RetryPolicy {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            base_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(30),
            backoff_multiplier: 2.0,
        }
    }
}

impl RetryPolicy {
    pub fn exponential_backoff(&self, attempt: u32) -> Duration {
        let delay = self.base_delay.as_millis() as f64
            * self.backoff_multiplier.powi(attempt as i32);
        let delay = delay.min(self.max_delay.as_millis() as f64);
        Duration::from_millis(delay as u64)
    }
    
    pub fn with_jitter(&self, delay: Duration) -> Duration {
        use rand::Rng;
        let jitter = rand::thread_rng().gen_range(0.0..0.1);
        delay.mul_f64(1.0 + jitter)
    }
}

// ==================== 可重试错误 trait ====================

pub trait Retryable {
    fn is_retryable(&self) -> bool;
}

// ==================== 重试实现 ====================

pub async fn retry<F, Fut, T, E>(
    mut operation: F,
    policy: RetryPolicy,
) -> Result<T, RetryError<E>>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: Retryable + Clone + std::fmt::Debug,
{
    let mut last_error = None;
    
    for attempt in 0..policy.max_attempts {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(err) => {
                if !err.is_retryable() {
                    return Err(RetryError::NonRetryable(err));
                }
                
                last_error = Some(err);
                
                if attempt < policy.max_attempts - 1 {
                    let delay = policy.exponential_backoff(attempt);
                    let delay = policy.with_jitter(delay);
                    tracing::debug!(
                        attempt = attempt + 1,
                        ?delay,
                        "operation failed, retrying"
                    );
                    sleep(delay).await;
                }
            }
        }
    }
    
    Err(RetryError::MaxRetriesExceeded {
        attempts: policy.max_attempts,
        last_error: last_error.unwrap(),
    })
}

// ==================== 断路器 ====================

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CircuitState {
    Closed,      // 正常，允许请求
    Open,        // 故障，快速失败
    HalfOpen,    // 尝试恢复
}

#[derive(Debug)]
struct CircuitBreakerInner {
    state: CircuitState,
    failure_count: u32,
    last_failure_time: Option<Instant>,
    success_count: u32,
}

pub struct CircuitBreaker {
    inner: Arc<RwLock<CircuitBreakerInner>>,
    failure_threshold: u32,
    success_threshold: u32,
    timeout: Duration,
}

impl CircuitBreaker {
    pub fn new(failure_threshold: u32, timeout: Duration) -> Self {
        Self {
            inner: Arc::new(RwLock::new(CircuitBreakerInner {
                state: CircuitState::Closed,
                failure_count: 0,
                last_failure_time: None,
                success_count: 0,
            })),
            failure_threshold,
            success_threshold: 2, // 半开状态成功次数阈值
            timeout,
        }
    }
    
    pub async fn call<F, Fut, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<T, E>>,
    {
        // 检查状态
        {
            let inner = self.inner.read().await;
            match inner.state {
                CircuitState::Open => {
                    // 检查是否超时
                    if let Some(last_failure) = inner.last_failure_time {
                        if last_failure.elapsed() >= self.timeout {
                            // 转换为半开状态
                            drop(inner);
                            let mut inner = self.inner.write().await;
                            if matches!(inner.state, CircuitState::Open) {
                                inner.state = CircuitState::HalfOpen;
                                inner.success_count = 0;
                                tracing::info!("circuit breaker entering half-open state");
                            }
                        } else {
                            return Err(CircuitBreakerError::Open);
                        }
                    }
                }
                CircuitState::HalfOpen => {
                    // 半开状态只允许有限请求
                    if inner.success_count >= self.success_threshold {
                        // 已经验证可以恢复
                    }
                }
                CircuitState::Closed => {}
            }
        }
        
        // 执行操作
        let result = operation().await;
        
        // 更新状态
        let mut inner = self.inner.write().await;
        match result {
            Ok(_) => {
                match inner.state {
                    CircuitState::HalfOpen => {
                        inner.success_count += 1;
                        if inner.success_count >= self.success_threshold {
                            inner.state = CircuitState::Closed;
                            inner.failure_count = 0;
                            tracing::info!("circuit breaker closed");
                        }
                    }
                    CircuitState::Closed => {
                        inner.failure_count = 0;
                    }
                    CircuitState::Open => unreachable!(),
                }
                // 这里我们假设操作成功返回 Ok，但实际返回类型需要转换
                // 简化示例，实际实现需要处理类型转换
                Err(CircuitBreakerError::HalfOpenRejected)
            }
            Err(_) => {
                inner.failure_count += 1;
                inner.last_failure_time = Some(Instant::now());
                
                if inner.failure_count >= self.failure_threshold {
                    inner.state = CircuitState::Open;
                    tracing::warn!(
                        failures = inner.failure_count,
                        "circuit breaker opened"
                    );
                }
                Err(CircuitBreakerError::Open)
            }
        }
    }
    
    pub async fn state(&self) -> CircuitState {
        self.inner.read().await.state
    }
    
    pub async fn is_open(&self) -> bool {
        matches!(self.inner.read().await.state, CircuitState::Open)
    }
}

// ==================== 超时包装 ====================

pub async fn with_timeout<F, Fut, T>(
    operation: F,
    timeout: Duration,
) -> Result<T, tokio::time::error::Elapsed>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = T>,
{
    tokio::time::timeout(timeout, operation()).await
}

// ==================== 组合使用 ====================

pub struct ResilientClient {
    circuit_breaker: CircuitBreaker,
    retry_policy: RetryPolicy,
    timeout: Duration,
}

impl ResilientClient {
    pub fn new() -> Self {
        Self {
            circuit_breaker: CircuitBreaker::new(5, Duration::from_secs(60)),
            retry_policy: RetryPolicy::default(),
            timeout: Duration::from_secs(30),
        }
    }
    
    pub async fn call<F, Fut, T, E>(&self, operation: F) -> Result<T, ClientError<E>>
    where
        F: Fn() -> Fut + Clone,
        Fut: Future<Output = Result<T, E>>,
        E: Retryable + Clone + std::fmt::Debug + 'static,
    {
        // 1. 检查断路器
        if self.circuit_breaker.is_open().await {
            return Err(ClientError::CircuitBreakerOpen);
        }
        
        // 2. 执行带重试的操作
        let result = retry(operation.clone(), self.retry_policy.clone()).await;
        
        match result {
            Ok(value) => {
                // 记录成功
                self.circuit_breaker.call(|| async { Ok::<_, E>(()) }).await.ok();
                Ok(value)
            }
            Err(RetryError::NonRetryable(e)) => {
                Err(ClientError::NonRetryable(e))
            }
            Err(RetryError::MaxRetriesExceeded { attempts, last_error }) => {
                // 断路器记录失败
                self.circuit_breaker.call(|| async { Err::<(), _>(last_error.clone()) }).await.ok();
                Err(ClientError::MaxRetriesExceeded { attempts })
            }
        }
    }
}

#[derive(Error, Debug)]
pub enum ClientError<E> {
    #[error("circuit breaker is open")]
    CircuitBreakerOpen,
    
    #[error("max retries exceeded after {attempts} attempts")]
    MaxRetriesExceeded { attempts: u32 },
    
    #[error("non-retryable error: {0:?}")]
    NonRetryable(E),
    
    #[error("timeout")]
    Timeout,
}

// ==================== 测试 ====================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[derive(Debug, Clone)]
    struct TestError {
        retryable: bool,
    }
    
    impl Retryable for TestError {
        fn is_retryable(&self) -> bool {
            self.retryable
        }
    }
    
    impl std::fmt::Display for TestError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "test error")
        }
    }
    
    impl std::error::Error for TestError {}
    
    #[tokio::test]
    async fn test_retry_success_on_second_attempt() {
        let mut attempts = 0;
        
        let result = retry(
            || {
                attempts += 1;
                async move {
                    if attempts < 2 {
                        Err(TestError { retryable: true })
                    } else {
                        Ok("success")
                    }
                }
            },
            RetryPolicy::default(),
        ).await;
        
        assert!(result.is_ok());
        assert_eq!(attempts, 2);
    }
    
    #[tokio::test]
    async fn test_non_retryable_error() {
        let result: Result<(), RetryError<TestError>> = retry(
            || async move {
                Err(TestError { retryable: false })
            },
            RetryPolicy::default(),
        ).await;
        
        assert!(matches!(result, Err(RetryError::NonRetryable(_))));
    }
    
    #[tokio::test]
    async fn test_circuit_breaker_opens_after_failures() {
        let cb = CircuitBreaker::new(3, Duration::from_secs(60));
        
        // 触发 3 次失败
        for _ in 0..3 {
            let _: Result<(), _> = cb.call(|| async {
                Err::<(), ()>(())
            }).await;
        }
        
        // 断路器应该打开
        assert!(cb.is_open().await);
        
        // 后续请求应快速失败
        let result = cb.call(|| async { Ok::<(), ()>(()) }).await;
        assert!(matches!(result, Err(CircuitBreakerError::Open)));
    }
}
```

### 完整示例 3: anyhow + thiserror 混合使用

```rust
//! anyhow 和 thiserror 的最佳实践组合

// ==================== 库代码 (使用 thiserror) ====================

use thiserror::Error;
use std::path::PathBuf;

pub mod core {
    use super::*;
    
    #[derive(Error, Debug)]
    #[non_exhaustive]
    pub enum ConfigError {
        #[error("configuration file not found: {path}")]
        NotFound { path: PathBuf },
        
        #[error("invalid configuration format: {message}")]
        InvalidFormat { message: String },
        
        #[error("missing required field: {field}")]
        MissingField { field: String },
        
        #[error("io error while reading config: {0}")]
        Io(#[from] std::io::Error),
        
        #[error("parse error: {0}")]
        Parse(#[from] serde_json::Error),
    }
    
    #[derive(Error, Debug)]
    #[non_exhaustive]
    pub enum NetworkError {
        #[error("connection refused to {address}")]
        ConnectionRefused { address: String },
        
        #[error("connection timed out after {duration:?}")]
        Timeout { duration: std::time::Duration },
        
        #[error("dns resolution failed for {hostname}")]
        DnsFailed { hostname: String },
        
        #[error("tls handshake failed: {reason}")]
        TlsFailed { reason: String },
    }
    
    impl Retryable for NetworkError {
        fn is_retryable(&self) -> bool {
            matches!(self,
                NetworkError::ConnectionRefused { .. } |
                NetworkError::Timeout { .. } |
                NetworkError::DnsFailed { .. }
            )
        }
    }
    
    #[derive(Error, Debug)]
    #[non_exhaustive]
    pub enum CoreError {
        #[error("configuration error: {0}")]
        Config(#[from] ConfigError),
        
        #[error("network error: {0}")]
        Network(#[from] NetworkError),
        
        #[error("internal error: {message}")]
        Internal { message: String },
    }
    
    pub type CoreResult<T> = Result<T, CoreError>;
    
    pub trait Retryable {
        fn is_retryable(&self) -> bool;
    }
    
    impl Retryable for CoreError {
        fn is_retryable(&self) -> bool {
            matches!(self,
                CoreError::Network(e) if e.is_retryable()
            )
        }
    }
    
    // 库函数返回结构化错误
    pub fn load_config(path: &str) -> CoreResult<Config> {
        use std::fs;
        
        let content = fs::read_to_string(path)
            .map_err(|e| {
                if e.kind() == std::io::ErrorKind::NotFound {
                    ConfigError::NotFound { path: path.into() }
                } else {
                    e.into()
                }
            })?;
        
        let config: Config = serde_json::from_str(&content)
            .map_err(|e| ConfigError::InvalidFormat {
                message: format!("JSON parse error: {}", e),
            })?;
        
        config.validate()?;
        
        Ok(config)
    }
    
    #[derive(Debug, serde::Deserialize)]
    pub struct Config {
        pub server: ServerConfig,
        pub database: DatabaseConfig,
    }
    
    impl Config {
        fn validate(&self) -> CoreResult<()> {
            if self.server.port == 0 {
                return Err(ConfigError::InvalidFormat {
                    message: "port cannot be 0".to_string(),
                }.into());
            }
            Ok(())
        }
    }
    
    #[derive(Debug, serde::Deserialize)]
    pub struct ServerConfig {
        pub host: String,
        pub port: u16,
    }
    
    #[derive(Debug, serde::Deserialize)]
    pub struct DatabaseConfig {
        pub url: String,
        pub pool_size: u32,
    }
}

// ==================== 应用代码 (使用 anyhow) ====================

use anyhow::{Context, Result as AnyhowResult, bail, ensure};
use core::*;

fn main() -> AnyhowResult<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    // 加载配置
    let config = core::load_config("config.json")
        .context("failed to load application configuration")?;
    
    tracing::info!(
        host = %config.server.host,
        port = %config.server.port,
        "configuration loaded"
    );
    
    // 初始化应用
    let app = Application::new(config)
        .context("failed to initialize application")?;
    
    // 运行应用
    app.run()
        .context("application runtime error")?;
    
    Ok(())
}

struct Application {
    config: Config,
}

impl Application {
    fn new(config: Config) -> AnyhowResult<Self> {
        ensure!(
            config.database.pool_size > 0,
            "database pool size must be greater than 0"
        );
        
        Ok(Self { config })
    }
    
    fn run(&self) -> AnyhowResult<()> {
        tracing::info!("starting application");
        
        // 业务逻辑...
        
        Ok(())
    }
}

// ==================== 错误处理中间件模式 ====================

use std::fmt;

/// 为 anyhow::Error 添加结构化上下文
pub trait ErrorContext {
    fn with_suggestion(self, suggestion: impl Into<String>) -> Self;
    fn with_help_url(self, url: impl Into<String>) -> Self;
}

impl ErrorContext for anyhow::Error {
    fn with_suggestion(self, suggestion: impl Into<String>) -> Self {
        // 实际实现可以将建议存储在错误中
        // 这里简化处理
        self.context(format!("Suggestion: {}", suggestion.into()))
    }
    
    fn with_help_url(self, url: impl Into<String>) -> Self {
        self.context(format!("Help: {}", url.into()))
    }
}

/// 格式化错误报告给用户
pub fn format_user_facing_error(err: &anyhow::Error) -> String {
    let mut output = String::new();
    
    output.push_str("Error: ");
    output.push_str(&err.to_string());
    output.push('\n');
    
    // 收集上下文链
    let causes: Vec<_> = err.chain().skip(1).collect();
    if !causes.is_empty() {
        output.push_str("\nCaused by:\n");
        for (i, cause) in causes.iter().enumerate() {
            output.push_str(&format!("  {}: {}\n", i, cause));
        }
    }
    
    output
}

/// 格式化错误报告给开发者
pub fn format_debug_error(err: &anyhow::Error) -> String {
    let mut output = format_user_facing_error(err);
    
    if let Some(backtrace) = err.backtrace() {
        output.push_str("\nBacktrace:\n");
        output.push_str(&format!("{:?}", backtrace));
    }
    
    output
}

// ==================== 具体使用示例 ====================

#[cfg(test)]
mod examples {
    use super::*;
    
    /// 示例 1: 简单错误传播
    fn example_simple_propagation() -> AnyhowResult<()> {
        let data = std::fs::read_to_string("data.txt")
            .context("failed to read data file")?;
        
        let parsed: serde_json::Value = serde_json::from_str(&data)
            .context("failed to parse JSON data")?;
        
        println!("{:?}", parsed);
        Ok(())
    }
    
    /// 示例 2: 选择性处理特定错误
    fn example_selective_handling() -> AnyhowResult<()> {
        match core::load_config("config.json") {
            Ok(config) => {
                println!("Loaded config: {:?}", config);
                Ok(())
            }
            Err(CoreError::Config(ConfigError::NotFound { .. })) => {
                // 配置不存在，使用默认配置
                tracing::warn!("config not found, using defaults");
                Ok(())
            }
            Err(e) => {
                // 其他错误转换为 anyhow
                Err(e.into())
            }
        }
    }
    
    /// 示例 3: 批量操作收集错误
    fn example_collect_errors(paths: &[&str]) -> AnyhowResult<Vec<Config>> {
        use anyhow::anyhow;
        
        let mut configs = Vec::new();
        let mut errors = Vec::new();
        
        for path in paths {
            match core::load_config(path) {
                Ok(config) => configs.push(config),
                Err(e) => errors.push((path, e)),
            }
        }
        
        if !errors.is_empty() {
            let error_details: Vec<_> = errors
                .iter()
                .map(|(p, e)| format!("  - {}: {}", p, e))
                .collect();
            
            bail!(
                "failed to load {} config files:\n{}",
                errors.len(),
                error_details.join("\n")
            );
        }
        
        Ok(configs)
    }
    
    /// 示例 4: 错误转换和适配
    fn example_error_adaptation() -> AnyhowResult<()> {
        let result: Result<(), core::CoreError> = core::load_config("test.json").map(|_| ());
        
        // 转换为 anyhow 并添加上下文
        result
            .map_err(|e| {
                // 可以在这里根据错误类型做不同处理
                match &e {
                    core::CoreError::Network(_) => {
                        anyhow::Error::new(e)
                            .context("network connectivity issue")
                            .with_suggestion("check your internet connection")
                    }
                    _ => e.into(),
                }
            })?;
        
        Ok(())
    }
}
```

---

## 附录

### A. 快速决策参考表

| 场景 | 推荐方案 | 代码示例 |
|-----|---------|---------|
| 函数返回可能失败 | `Result<T, E>` | `fn foo() -> Result<T, MyError>` |
| 值可能不存在 | `Option<T>` | `fn find() -> Option<T>` |
| 内部不变性违反 | `panic!` | `unreachable!()` |
| 库错误定义 | `thiserror` | `#[derive(Error)] enum Error { ... }` |
| 应用错误处理 | `anyhow` | `fn main() -> anyhow::Result<()>` |
| 跨函数传播 | `?` 操作符 | `let x = may_fail()?;` |
| 添加上下文 | `.context()` | `.context("while reading file")?` |
| 临时故障 | 重试 | `retry(operation, policy).await?` |
| 下游故障 | 断路器 | `circuit_breaker.call(op).await?` |

### B. 常用 crate 对比

| Crate | 用途 | 开销 | 推荐场景 |
|------|------|------|---------|
| `thiserror` | 定义错误类型 | 零 | 库代码 |
| `anyhow` | 处理错误 | 极小 | 应用代码 |
| `eyre` | 增强 anyhow | 极小 | 需要自定义报告 |
| `snafu` | 结构化错误 | 零 | 复杂错误场景 |
| `fehler` | 异常式错误 | 极小 | 简化错误处理 |

### C. 进一步阅读

- [Rust Error Handling Best Practices](https://doc.rust-lang.org/stable/rust-by-example/error.html)
- [thiserror 文档](https://docs.rs/thiserror)
- [anyhow 文档](https://docs.rs/anyhow)
- [Rust API Guidelines: Error Handling](https://rust-lang.github.io/api-guidelines/interoperability.html#error-types-are-meaningful-and-well-behaved-c-good-err)
- [Error Handling in Rust - Andrew Gallant](https://blog.burntsushi.net/rust-error-handling/)
