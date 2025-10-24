# 错误传播机制


## 📊 目录

- [1. ?操作符与自动传播](#1-操作符与自动传播)
- [2. map/map_err与链式传播](#2-mapmap_err与链式传播)
- [3. 错误链与上下文](#3-错误链与上下文)
- [4. 工程案例](#4-工程案例)
  - [4.1 ?操作符传播](#41-操作符传播)
  - [4.2 map_err转换](#42-map_err转换)
  - [4.3 错误链追踪](#43-错误链追踪)
- [5. 批判性分析与未来值值值展望](#5-批判性分析与未来值值值展望)


## 1. ?操作符与自动传播

- ?操作符自动将Result/Option中的错误/空值向上传播
- 编译期类型检查保证传播路径安全

## 2. map/map_err与链式传播

- map处理成功值，map_err处理错误值
- and_then链式组合多步操作

## 3. 错误链与上下文

- thiserror/anyhow等库支持错误链追踪与上下文信息
- source方法递归追踪底层错误

## 4. 工程案例

### 4.1 ?操作符传播

```rust
fn read_config(path: &str) -> Result<Config, ConfigError> {
    let s = std::fs::read_to_string(path)?;
    let cfg = toml::from_str(&s)?;
    Ok(cfg)
}
```

### 4.2 map_err转换

```rust
fn parse_num(s: &str) -> Result<i32, String> {
    s.parse().map_err(|e| format!("parse error: {}", e))
}
```

### 4.3 错误链追踪

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

## 5. 批判性分析与未来值值值展望

- Rust错误传播机制类型安全、零成本，但复杂错误链和上下文管理需依赖第三方库
- 未来值值值可探索自动化错误链分析与IDE集成

"

---
