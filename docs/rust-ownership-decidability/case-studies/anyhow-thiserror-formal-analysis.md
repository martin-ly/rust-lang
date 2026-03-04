# Anyhow & Thiserror 错误处理形式化分析

> **主题**: 人体工学错误处理库
>
> **形式化框架**: 类型擦除 vs 具体类型
>
> **参考**: Anyhow Documentation; Thiserror Documentation

---

## 目录

- [Anyhow \& Thiserror 错误处理形式化分析](#anyhow--thiserror-错误处理形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 类型系统分析](#2-类型系统分析)
    - [2.1 Anyhow: 动态错误](#21-anyhow-动态错误)
    - [定义 2.1 (anyhow::Error)](#定义-21-anyhowerror)
    - [定理 2.1 (类型擦除)](#定理-21-类型擦除)
    - [2.2 Thiserror: 静态生成](#22-thiserror-静态生成)
    - [定义 2.2 (派生宏)](#定义-22-派生宏)
    - [定理 2.2 (零开销抽象)](#定理-22-零开销抽象)
  - [3. 上下文传播](#3-上下文传播)
    - [定理 3.1 (上下文附加)](#定理-31-上下文附加)
  - [4. ?操作符集成](#4-操作符集成)
    - [定理 4.1 (自动转换)](#定理-41-自动转换)
  - [5. 性能对比](#5-性能对比)
    - [对比表](#对比表)
  - [6. 反例](#6-反例)
    - [反例 6.1 (混用错误类型)](#反例-61-混用错误类型)
    - [反例 6.2 (过度使用上下文)](#反例-62-过度使用上下文)

---

## 1. 引言

错误处理库对比:

- **Anyhow**: 应用开发，快速原型，类型擦除
- **Thiserror**: 库开发，API设计，具体类型

---

## 2. 类型系统分析

### 2.1 Anyhow: 动态错误

### 定义 2.1 (anyhow::Error)

```rust
pub struct Error {
    inner: Box<dyn ErrorImpl>,
}
```

### 定理 2.1 (类型擦除)

> anyhow::Error擦除具体错误类型，提供统一接口。

**优势**:

- 无需定义错误类型
- 自动转换任何`std::error::Error`
- 简洁的`?`传播

**代价**:

- 运行时类型检查
- 无法精确匹配错误类型

∎

### 2.2 Thiserror: 静态生成

### 定义 2.2 (派生宏)

```rust
#[derive(Error, Debug)]
pub enum MyError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("parse error: {0}")]
    Parse(#[from] ParseIntError),
}
```

### 定理 2.2 (零开销抽象)

> thiserror生成的代码等价于手写实现。

**展开后**:

```rust
impl std::fmt::Display for MyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MyError::Io(e) => write!(f, "IO error: {}", e),
            MyError::Parse(e) => write!(f, "parse error: {}", e),
        }
    }
}

impl std::error::Error for MyError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            MyError::Io(e) => Some(e),
            MyError::Parse(e) => Some(e),
        }
    }
}
```

∎

---

## 3. 上下文传播

### 定理 3.1 (上下文附加)

> Anyhow支持运行时添加上下文。

```rust
use anyhow::{Context, Result};

fn read_config() -> Result<Config> {
    let content = fs::read_to_string("config.toml")
        .context("failed to read config file")?;  // 添加上下文

    let config = toml::from_str(&content)
        .with_context(|| format!("failed to parse config"))?;

    Ok(config)
}
```

**错误链**:

```text
Error: failed to read config file
Caused by:
    No such file or directory (os error 2)
```

∎

---

## 4. ?操作符集成

### 定理 4.1 (自动转换)

> Anyhow的`?`自动转换任何错误。

```rust
fn main() -> anyhow::Result<()> {
    let file = std::fs::File::open("test")?;  // io::Error → anyhow::Error
    let num: i32 = "abc".parse()?;            // ParseIntError → anyhow::Error
    Ok(())
}
```

**机制**:

```rust
impl From<E: std::error::Error> for Error {
    fn from(e: E) -> Self {
        // 类型擦除包装
    }
}
```

∎

---

## 5. 性能对比

### 对比表

| 特性 | Anyhow | Thiserror |
|------|--------|-----------|
| 返回类型大小 | 16 bytes (胖指针) | 1-32 bytes (具体) |
| 动态分发 | 是 | 否 |
| 类型匹配 | 运行时 | 编译时 |
| 适用场景 | 应用 | 库 |

---

## 6. 反例

### 反例 6.1 (混用错误类型)

```rust
// 错误: 混用anyhow和thiserror可能困惑
pub fn lib_function() -> anyhow::Result<()> {
    // 库应该返回具体错误类型
}

// 正确: 库返回具体类型
#[derive(Error, Debug)]
pub enum LibError { ... }

pub fn lib_function() -> Result<(), LibError> {
    ...
}
```

### 反例 6.2 (过度使用上下文)

```rust
// 过度包装，信息冗余
let x = op1().context("op1 failed")?;
let y = op2().context("op2 failed")?;
let z = op3().context("op3 failed")?;

// 更好的做法：在关键边界添加上下文
fn do_work() -> Result<()> {
    let x = op1()?;
    let y = op2()?;
    let z = op3()?;
    Ok(())
}.context("work failed")?;
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
