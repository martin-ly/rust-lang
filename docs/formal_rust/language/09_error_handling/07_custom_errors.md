# 自定义错误类型

## 📊 目录

- [自定义错误类型](#自定义错误类型)
  - [📊 目录](#-目录)
  - [1. 错误类型设计原则](#1-错误类型设计原则)
  - [2. thiserror与anyhow库](#2-thiserror与anyhow库)
  - [3. 错误链与上下文](#3-错误链与上下文)
  - [4. 工程案例](#4-工程案例)
    - [4.1 thiserror自定义错误](#41-thiserror自定义错误)
    - [4.2 anyhow动态错误](#42-anyhow动态错误)
  - [5. 批判性分析与未来值展望](#5-批判性分析与未来值展望)

## 1. 错误类型设计原则

- 明确错误语义、分层设计、可组合性
- 实现Debug、Display、Error trait

## 2. thiserror与anyhow库

- thiserror简化Error trait实现，支持错误链
- anyhow适合应用层动态错误聚合

## 3. 错误链与上下文

- source方法递归追踪底层错误
- with_context添加上下文信息

## 4. 工程案例

### 4.1 thiserror自定义错误

```rust
use thiserror::Error;
#[derive(Error, Debug)]
enum MyError {
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("parse error: {0}")]
    Parse(#[from] std::num::ParseIntError),
}
```

### 4.2 anyhow动态错误

```rust
use anyhow::{Result, Context};
fn do_work() -> Result<()> {
    let s = std::fs::read_to_string("foo.txt").context("read file failed")?;
    Ok(())
}
```

## 5. 批判性分析与未来值展望

- Rust自定义错误类型设计灵活，生态完善，但复杂错误链和上下文管理需依赖库
- 未来值可探索自动化错误类型生成与IDE集成

"

---
