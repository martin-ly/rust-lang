# ⚠️ Rust 错误处理速查卡

> **快速参考** | [完整文档](../../crates/c03_control_fn/docs/) | [代码示例](../../crates/c03_control_fn/examples/)
> **最后更新**: 2025-11-15 | **Rust 版本**: 1.91.1+ | **Edition**: 2024

---

## 🎯 核心概念

### Result 类型

```rust
enum Result<T, E> {
    Ok(T),   // 成功值
    Err(E),  // 错误值
}
```

### Option 类型

```rust
enum Option<T> {
    Some(T),  // 有值
    None,     // 无值
}
```

---

## 📐 基本模式

### 模式 1: 匹配处理

```rust
match result {
    Ok(value) => println!("成功: {}", value),
    Err(e) => println!("错误: {}", e),
}
```

### 模式 2: unwrap 和 expect

```rust
// unwrap: 成功返回值，失败 panic
let value = result.unwrap();

// expect: 带错误消息的 unwrap
let value = result.expect("操作失败");
```

### 模式 3: ? 操作符

```rust
fn read_file() -> Result<String, io::Error> {
    let mut file = File::open("file.txt")?;  // 自动传播错误
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}
```

---

## 🔧 常用方法

### Result 方法

```rust
// 映射值
let result = Ok(5);
let mapped = result.map(|x| x * 2);  // Ok(10)

// 映射错误
let result = Err("error");
let mapped = result.map_err(|e| format!("Error: {}", e));

// 解包或使用默认值
let value = result.unwrap_or(0);
let value = result.unwrap_or_else(|e| calculate_default());

// 链式操作
let result = Ok(5)
    .and_then(|x| if x > 0 { Ok(x * 2) } else { Err("negative") })
    .map(|x| x + 1);
```

### Option 方法

```rust
// 映射值
let option = Some(5);
let mapped = option.map(|x| x * 2);  // Some(10)

// 过滤
let option = Some(5);
let filtered = option.filter(|&x| x > 3);  // Some(5)

// 解包或使用默认值
let value = option.unwrap_or(0);
let value = option.unwrap_or_else(|| calculate_default());
```

---

## 🎯 错误处理库

### anyhow - 灵活的错误处理

```rust
use anyhow::{Result, Context};

fn read_config() -> Result<Config> {
    let content = std::fs::read_to_string("config.toml")
        .context("无法读取配置文件")?;
    let config: Config = toml::from_str(&content)
        .context("配置文件格式错误")?;
    Ok(config)
}
```

### thiserror - 自定义错误类型

```rust
use thiserror::Error;

#[derive(Error, Debug)]
enum MyError {
    #[error("IO 错误: {0}")]
    Io(#[from] std::io::Error),
    #[error("解析错误: {0}")]
    Parse(#[from] serde_json::Error),
    #[error("自定义错误: {message}")]
    Custom { message: String },
}
```

---

## 🔗 相关资源

- [控制流完整文档](../../crates/c03_control_fn/docs/)
- [错误处理最佳实践](../../crates/c03_control_fn/docs/tier_02_guides/)
- [Rust 官方文档 - 错误处理](https://doc.rust-lang.org/book/ch09-00-error-handling.html)

---

---

## 🆕 Rust 1.91.1 错误处理改进

### ControlFlow 改进

**改进**: 可以携带详细的错误信息

```rust
// Rust 1.91.1 改进的 ControlFlow
use std::ops::ControlFlow;

fn validate(value: i32) -> ControlFlow<String, i32> {
    if value < 0 {
        ControlFlow::Break(format!("值 {} 不能为负数", value))
    } else {
        ControlFlow::Continue(value)
    }
}
```

**影响**: 更好的异步验证和转换

---

**最后更新**: 2025-11-15
**Rust 版本**: 1.91.1+ (Edition 2024)
