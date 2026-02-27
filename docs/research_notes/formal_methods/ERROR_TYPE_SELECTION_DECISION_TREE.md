# 错误类型选择决策树

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **状态**: ✅ 已扩展
> **版本**: Rust 1.93.0+ (Edition 2024)

---

## 概述

Rust的错误处理生态系统丰富多样，本决策树帮助开发者在不同场景下选择最适合的错误类型和处理策略。

---

## 主决策树

```
错误处理需求分析
        │
        ├─ 可恢复错误?
        │  ├─ 否 → panic!
        │  │       └─ 不可恢复状态，程序终止
        │  │
        │  └─ 是 → 需要错误上下文?
        │          ├─ 是 → 使用 anyhow/eyre
        │          │       └─ 应用开发，快速迭代
        │          │
        │          └─ 否 → 错误类型复杂度?
        │                  ├─ 简单 → 使用标准库
        │                  │           ├─ Option<T> - 值可能存在/不存在
        │                  │           └─ Result<T, E> - 操作可能失败
        │                  │
        │                  └─ 复杂 → 自定义错误类型
        │                              └─ 库开发，精确控制
        │
        └─ 异步错误?
           └─ 使用 anyhow 或 thiserror
               └─ 与async/await良好集成
```

---

## 分支一：不可恢复错误 (panic!)

### 使用场景

| 场景 | 示例 | 原因 |
| :--- | :--- | :--- |
| 内部不变式违反 | 数组索引越界 | bug，不应发生 |
| 内存分配失败 | `Vec::with_capacity`失败 | 无法恢复 |
| 外部假设失败 | FFI返回无效值 | 契约违反 |

### 代码示例

```rust
// 内部不变式
let idx = vec.binary_search(&key).unwrap();  // 假设已排序

// 明确panic
if config.threads == 0 {
    panic!("线程数必须大于0");
}

// 使用expect增加上下文
let port = env::var("PORT").expect("PORT环境变量必须设置");
```

---

## 分支二：简单错误处理

### Option<T> - 值可能存在

```rust
// 使用场景: 值可能存在或不存在
fn find_user(id: u64) -> Option<User> {
    database.get(id).cloned()
}

// 处理Option
let user = find_user(42)?;  // 传播None

// 或提供默认值
let user = find_user(42).unwrap_or(default_user());

// 或转换错误
let user = find_user(42)
    .ok_or("用户不存在")?;
```

### Result<T, E> - 操作可能失败

```rust
// 使用标准错误类型
use std::io;
use std::fs::File;

fn read_config() -> Result<String, io::Error> {
    let file = File::open("config.toml")?;
    // 读取文件...
}

// 自定义错误消息
let contents = std::fs::read_to_string("config.toml")
    .map_err(|e| format!("读取配置失败: {}", e))?;
```

---

## 分支三：复杂错误类型

### 使用thiserror (库开发)

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ConfigError {
    #[error("IO错误: {0}")]
    Io(#[from] io::Error),

    #[error("解析错误: {message}")]
    Parse { message: String, line: usize },

    #[error("无效配置: {0}")]
    Invalid(String),
}

// 使用
fn load_config(path: &str) -> Result<Config, ConfigError> {
    let contents = std::fs::read_to_string(path)?;  // 自动转换io::Error

    parse_config(&contents)
        .map_err(|e| ConfigError::Parse {
            message: e.to_string(),
            line: e.line(),
        })?
}
```

### 使用anyhow (应用开发)

```rust
use anyhow::{Context, Result};

fn main() -> Result<()> {
    let config = std::fs::read_to_string("config.toml")
        .context("读取配置文件失败")?;

    let settings: Settings = toml::from_str(&config)
        .context("解析配置失败")?;

    run_app(settings)
        .context("运行应用失败")?;

    Ok(())
}
```

---

## 分支四：错误类型对比

### anyhow vs thiserror

| 维度 | anyhow | thiserror |
| :--- | :--- | :--- |
| 使用场景 | 应用开发 | 库开发 |
| 错误类型 | 动态 | 静态 |
| 性能 | 略低(动态分发) | 高(静态) |
| 灵活性 | 高 | 中等 |
| 学习曲线 | 低 | 中等 |

### 标准库 vs 外部库

| 需求 | 推荐 | 原因 |
| :--- | :--- | :--- |
| 简单脚本 | `Result<T, Box<dyn Error>>` | 简单 |
| CLI工具 | `anyhow` | 快速开发，良好上下文 |
| Web服务 | `thiserror` + `anyhow` | 结构化错误 + 应用错误 |
| 系统库 | `thiserror` | 精确控制，API稳定 |

---

## 分支五：特殊场景

### 异步错误处理

```rust
use anyhow::Result;
use tokio::fs;

async fn load_data() -> Result<Vec<u8>> {
    let data = fs::read("data.bin")
        .await
        .context("读取数据失败")?;

    Ok(data)
}

// 多个异步操作
async fn process() -> Result<()> {
    let (data1, data2) = tokio::try_join!(
        load_data().context("加载data1"),
        load_data().context("加载data2"),
    )?;

    Ok(())
}
```

### 错误转换

```rust
// 自动转换 (使用From trait)
#[derive(Debug, thiserror::Error)]
enum AppError {
    #[error("IO错误")]
    #[from]
    Io(io::Error),

    #[error("JSON解析错误")]
    #[from]
    Json(serde_json::Error),
}

// 手动转换
impl From<ParseIntError> for AppError {
    fn from(err: ParseIntError) -> Self {
        AppError::Invalid(format!("数字解析失败: {}", err))
    }
}
```

### 错误链与上下文

```rust
use anyhow::{Context, Result};

fn connect_database(url: &str) -> Result<Connection> {
    let config = parse_url(url)
        .context("解析数据库URL失败")?;

    let conn = establish_connection(&config)
        .context("建立连接失败")?;

    conn.authenticate()
        .context("认证失败")?;

    Ok(conn)
}

// 错误输出:
// Error: 认证失败
//
// Caused by:
//   无效凭据
//
// Caused by:
//   建立连接失败
// ...
```

---

## 错误处理最佳实践

### DO

```rust
// 使用?传播错误
let file = File::open(path)?;

// 添加上下文
let data = parse(&contents).context("解析数据失败")?;

// 使用特定错误类型
fn parse(s: &str) -> Result<Data, ParseError>;

// 处理所有错误分支
match result {
    Ok(v) => v,
    Err(e) if e.is_retriable() => retry(),
    Err(e) => return Err(e.into()),
}
```

### DON'T

```rust
// 不要滥用unwrap
let val = result.unwrap();  // 危险!

// 不要吞掉错误
let _ = do_something();  // 错误被忽略!

// 不要用()作为错误类型
Result<T, ()>  // 没有错误信息
```

---

## 决策速查表

| 场景 | 推荐方案 | 示例 |
| :--- | :--- | :--- |
| 简单可能失败 | `Result<T, E>` | 文件IO |
| 值可能存在 | `Option<T>` | HashMap查找 |
| 库API错误 | `thiserror` | 自定义Error枚举 |
| 应用错误处理 | `anyhow` | main函数 |
| 需要重试 | `backoff` crate | 网络请求 |
| 验证输入 | `validator` crate | 表单验证 |

---

## 与形式化方法关联

| 概念 | 形式化表示 | 相关文档 |
| :--- | :--- | :--- |
| Result | `Result<T, E> = Ok(T) \| Err(E)` | type_system_foundations.md |
| 错误传播 | `?` 运算符 | ownership_model.md §移动 |
| 类型安全 | 穷尽匹配检查 | borrow_checker_proof.md |

---

## 决策流程

```
错误处理需求？
│
├── 快速原型/应用开发
│   ├── 需要简单传播
│   │   └── 使用anyhow
│   │       ├── Result<T, anyhow::Error>
│   │       └── 自动上下文
│   │
│   └── 需要特定错误
│       └── 使用thiserror
│           └── 派生Error trait
│
├── 库开发
│   ├── 公开API需要精确错误
│   │   └── 自定义枚举错误
│   │       ├── 实现std::error::Error
│   │       └── 提供详细错误信息
│   │
│   └── 内部错误
│       └── 使用std::io::Error等
│
└── 特定领域
    ├── IO错误
    │   └── std::io::Error
    │
    ├── 解析错误
    │   └── 自定义ParseError
    │
    └── 验证错误
        └── 自定义ValidationError
```

---

## 错误类型对比

| 类型 | 适用场景 | 性能 | 灵活性 |
| :--- | :--- | :--- | :--- |
| `anyhow::Error` | 应用开发 | 中 | 高 |
| `thiserror` | 库开发 | 高 | 中 |
| 自定义枚举 | 精确控制 | 高 | 低 |
| `Box<dyn Error>` | 动态分发 | 中 | 高 |

---

## anyhow示例

```rust
use anyhow::{Context, Result};

fn read_config() -> Result<Config> {
    let content = std::fs::read_to_string("config.toml")
        .context("读取配置文件失败")?;
    let config: Config = toml::from_str(&content)
        .context("解析配置失败")?;
    Ok(config)
}
```

## thiserror示例

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ConfigError {
    #[error("IO错误: {0}")]
    Io(#[from] std::io::Error),
    #[error("解析错误: {0}")]
    Parse(#[from] toml::de::Error),
    #[error("验证失败: {message}")]
    Validation { message: String },
}
```

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 错误类型选择决策树完整版
