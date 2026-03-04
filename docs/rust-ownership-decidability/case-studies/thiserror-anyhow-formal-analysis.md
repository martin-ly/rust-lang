# Thiserror/Anyhow错误处理形式化分析

> **主题**: 错误处理库
> **形式化框架**: 错误派生 + 上下文传播
> **参考**: Thiserror/Anyhow Documentation

---

## 目录

- [Thiserror/Anyhow错误处理形式化分析](#thiserroranyhow错误处理形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Thiserror](#2-thiserror)
    - [定义 ERROR-1 ( 派生宏 )](#定义-error-1--派生宏-)
    - [定义 ERROR-2 ( 自动实现 )](#定义-error-2--自动实现-)
    - [定理 ERROR-T1 ( 类型安全 )](#定理-error-t1--类型安全-)
  - [3. Anyhow](#3-anyhow)
    - [定义 ANYHOW-1 ( Result别名 )](#定义-anyhow-1--result别名-)
    - [定义 ANYHOW-2 ( 上下文 )](#定义-anyhow-2--上下文-)
    - [定理 ANYHOW-T1 ( 自动转换 )](#定理-anyhow-t1--自动转换-)
  - [4. 组合使用](#4-组合使用)
    - [定义 COMBINE-1 ( 边界设计 )](#定义-combine-1--边界设计-)
    - [定理 COMBINE-T1 ( 无缝转换 )](#定理-combine-t1--无缝转换-)
  - [5. 定理与证明](#5-定理与证明)
    - [定理 ERR-T1 ( 零运行时开销 )](#定理-err-t1--零运行时开销-)
    - [定理 ERR-T2 ( 上下文保留 )](#定理-err-t2--上下文保留-)
  - [6. 代码示例](#6-代码示例)
    - [示例1: 库错误定义](#示例1-库错误定义)
    - [示例2: 应用错误处理](#示例2-应用错误处理)
    - [示例3: 错误链遍历](#示例3-错误链遍历)

---

## 1. 引言

错误处理双雄：

- **Thiserror**: 库代码，定义结构化错误
- **Anyhow**: 应用代码，简化错误传播

---

## 2. Thiserror

### 定义 ERROR-1 ( 派生宏 )

```rust
#[derive(Error, Debug)]
pub enum DataStoreError {
    #[error("data store disconnected")]
    Disconnect(#[from] io::Error),
    #[error("the data for key `{0}` is not available")]
    Redaction(String),
    #[error("invalid header (expected {expected:?}, found {found:?})")]
    InvalidHeader { expected: String, found: String },
}
```

**形式化**:

$$
\text{ErrorType} = \{ (variant_i, display_i, from_i^?) \}
$$

### 定义 ERROR-2 ( 自动实现 )

$$
\text{derive(Error)} \to \text{impl Display} + \text{impl Error} + \text{impl From}
$$

### 定理 ERROR-T1 ( 类型安全 )

错误类型在编译时确定。

$$
\forall e : \text{DataStoreError}.\ e \text{ matches exactly one variant}
$$

---

## 3. Anyhow

### 定义 ANYHOW-1 ( Result别名 )

```rust
type Result<T> = std::result::Result<T, anyhow::Error>;
```

$$
\text{anyhow::Result}<T> = \text{Result}<T, \text{dyn Error} + \text{Send} + \text{Sync}>
$$

### 定义 ANYHOW-2 ( 上下文 )

```rust
fs::read(path)
    .with_context(|| format!("failed to read config from {}", path))?
```

### 定理 ANYHOW-T1 ( 自动转换 )

任何错误可转换为anyhow::Error。

$$
\forall E : \text{Error}.\ E \to \text{anyhow::Error}
$$

---

## 4. 组合使用

### 定义 COMBINE-1 ( 边界设计 )

```rust
// Library: thiserror
#[derive(Error, Debug)]
pub enum MyError { ... }

// Application: anyhow
fn main() -> anyhow::Result<()> {
    let result = library_function()?;
    Ok(())
}
```

### 定理 COMBINE-T1 ( 无缝转换 )

库错误自动转换为anyhow错误。

$$
\text{MyError} : \text{Error} \to \text{anyhow::Error} \text{ via } \text{?}
$$

---

## 5. 定理与证明

### 定理 ERR-T1 ( 零运行时开销 )

Thiserror生成零开销代码。

$$
\text{derive(Error)} \to \text{hand-written\_equivalent}
$$

### 定理 ERR-T2 ( 上下文保留 )

 anyhow保留完整错误链。

$$
\text{Error::source} \to \text{full\_chain\_traversable}
$$

---

## 6. 代码示例

### 示例1: 库错误定义

```rust
use std::io;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ConfigError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("Parse error: {0}")]
    Parse(#[from] toml::de::Error),

    #[error("Missing required field: {0}")]
    MissingField(String),

    #[error("Invalid value for {field}: expected {expected}, got {actual}")]
    InvalidValue {
        field: String,
        expected: String,
        actual: String,
    },
}

pub type ConfigResult<T> = Result<T, ConfigError>;

pub fn load_config(path: &str) -> ConfigResult<Config> {
    let content = std::fs::read_to_string(path)?;  // io::Error -> ConfigError
    let config: Config = toml::from_str(&content)?;  // toml::Error -> ConfigError

    if config.name.is_empty() {
        return Err(ConfigError::MissingField("name".to_string()));
    }

    Ok(config)
}
```

### 示例2: 应用错误处理

```rust
use anyhow::{Context, Result};

fn main() -> Result<()> {
    let config = load_config("config.toml")
        .with_context(|| "failed to load application config")?;

    let data = fetch_data(&config.api_url)
        .context("failed to fetch remote data")?;

    process_data(data)
        .context("data processing failed")?;

    Ok(())
}

fn fetch_data(url: &str) -> Result<String> {
    reqwest::blocking::get(url)?
        .text()
        .map_err(|e| anyhow::anyhow!("request failed: {}", e))
}
```

### 示例3: 错误链遍历

```rust
use anyhow::Error;

fn print_error_chain(err: &Error) {
    eprintln!("Error: {}", err);

    let mut source = err.source();
    while let Some(err) = source {
        eprintln!("  Caused by: {}", err);
        source = err.source();
    }
}

// Output:
// Error: failed to load application config
//   Caused by: IO error: No such file or directory (os error 2)
```

---

**维护者**: Rust Error Handling Formal Methods Team
**创建日期**: 2026-03-05
**版本**: thiserror 1.x, anyhow 1.x
**状态**: ✅ 已对齐
