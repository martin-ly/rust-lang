# ⚠️ Rust 错误处理速查卡 {#️-rust-错误处理速查卡}

> **快速参考** | [完整文档](../../../crates/c03_control_fn/docs/) | [代码示例](../../../crates/c03_control_fn/examples/)
> **创建日期**: 2026-01-27
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [⚠️ Rust 错误处理速查卡 {#️-rust-错误处理速查卡}](#️-rust-错误处理速查卡-️-rust-错误处理速查卡)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [🎯 核心概念 {#-核心概念}](#-核心概念--核心概念)
    - [Result 类型](#result-类型)
    - [Option 类型](#option-类型)
  - [📐 基本模式 {#-基本模式}](#-基本模式--基本模式)
    - [模式 1: 匹配处理](#模式-1-匹配处理)
    - [模式 2: unwrap 和 expect](#模式-2-unwrap-和-expect)
    - [模式 3: ? 操作符](#模式-3--操作符)
  - [🔧 常用方法 {#-常用方法}](#-常用方法--常用方法)
    - [Result 方法](#result-方法)
    - [Option 方法](#option-方法)
  - [🎯 错误处理库 {#-错误处理库}](#-错误处理库--错误处理库)
    - [anyhow - 灵活的错误处理](#anyhow---灵活的错误处理)
    - [thiserror - 自定义错误类型](#thiserror---自定义错误类型)
  - [🚫 反例速查 {#-反例速查}](#-反例速查--反例速查)
    - [反例 1: 生产代码滥用 unwrap](#反例-1-生产代码滥用-unwrap)
    - [反例 2: 在非 Result 返回类型函数中使用 ? {#反例-2-在非-result-返回类型函数中使用-}](#反例-2-在非-result-返回类型函数中使用--反例-2-在非-result-返回类型函数中使用-)
    - [反例 3: 混淆 Option 与 Result 语义](#反例-3-混淆-option-与-result-语义)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)
  - [🧩 相关示例代码 {#-相关示例代码}](#-相关示例代码--相关示例代码)
  - [🔗 相关资源 {#-相关资源}](#-相关资源--相关资源)
  - [🆕 Rust 1.93.0 错误处理改进 {#-rust-1930-错误处理改进}](#-rust-1930-错误处理改进--rust-1930-错误处理改进)
    - [MaybeUninit 错误处理增强](#maybeuninit-错误处理增强)
  - [Rust 1.92.0 错误处理改进（历史）](#rust-1920-错误处理改进历史)
    - [ControlFlow 改进](#controlflow-改进)
  - [📚 相关资源 {#-相关资源-1}](#-相关资源--相关资源-1)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [相关速查卡](#相关速查卡)
  - [💡 使用场景 {#-使用场景}](#-使用场景--使用场景)
    - [场景 1: 配置文件解析](#场景-1-配置文件解析)
    - [场景 2: 用户输入验证](#场景-2-用户输入验证)
    - [场景 3: 链式操作处理](#场景-3-链式操作处理)
  - [⚠️ 边界情况 {#️-边界情况}](#️-边界情况-️-边界情况)
    - [边界 1: 错误类型转换](#边界-1-错误类型转换)
    - [边界 2:  panic 恢复](#边界-2--panic-恢复)
    - [形式化理论](#形式化理论)

---

## 🎯 核心概念 {#-核心概念}

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

## 📐 基本模式 {#-基本模式}

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

## 🔧 常用方法 {#-常用方法}

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

## 🎯 错误处理库 {#-错误处理库}

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

## 🚫 反例速查 {#-反例速查}

### 反例 1: 生产代码滥用 unwrap

**错误示例**:

```rust
fn read_config() -> Config {
    let content = std::fs::read_to_string("config.toml").unwrap();  // ❌ 失败即 panic
    toml::from_str(&content).unwrap()
}
```

**原因**: `unwrap` 在错误时 panic，不适合生产环境。

**修正**:

```rust
fn read_config() -> Result<Config, Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string("config.toml")?;
    Ok(toml::from_str(&content)?)
}
```

---

### 反例 2: 在非 Result 返回类型函数中使用 ? {#反例-2-在非-result-返回类型函数中使用-}

**错误示例**（以下代码无法通过编译）:

```rust,compile_fail
fn main() {
    let _f = std::fs::File::open("missing.txt")?;  // ❌ main 不返回 Result
}
```

**原因**: `?` 只能用于返回 `Result` 或 `Option` 的函数。

**修正**:

```rust
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let _f = std::fs::File::open("missing.txt")?;
    Ok(())
}
```

---

### 反例 3: 混淆 Option 与 Result 语义

**错误示例**:

```rust
fn find_user(id: u32) -> Result<User, ()> {  // ❌ 用 Result 表示“未找到”
    if let Some(u) = cache.get(id) {
        Ok(u.clone())
    } else {
        Err(())  // 未找到不是错误，是正常情况
    }
}
```

**原因**: “未找到”应用 `Option`，可恢复错误用 `Result`。

**修正**:

```rust
fn find_user(id: u32) -> Option<User> {
    cache.get(id).cloned()
}
```

**反例 3b: 在 #[test] 中未返回 Result 却使用 ?**（以下代码无法通过编译）:

```rust,compile_fail
#[test]
fn test_read() {
    let _f = std::fs::File::open("missing.txt")?;  // ❌ test 函数未声明 -> Result
}
```

---

## 📚 相关文档 {#-相关文档}

- [控制流与错误处理文档](../../../crates/c03_control_fn/docs/)
- [错误处理指南](../../../crates/c03_control_fn/docs/tier_02_guides/05_错误处理指南.md)

## 🧩 相关示例代码 {#-相关示例代码}

以下示例位于 `crates/c03_control_fn/examples/`，可直接运行（例如：`cargo run -p c03_control_fn --example error_handling_control_flow`）。

- [错误处理与控制流](../../../crates/c03_control_fn/examples/error_handling_control_flow.rs)
- [try 块与高级控制流](../../../crates/c03_control_fn/examples/try_blocks_advanced.rs)、[control_flow_example.rs](../../../crates/c03_control_fn/examples/control_flow_example.rs)

---

## 🔗 相关资源 {#-相关资源}

- [Rust 官方文档 - 错误处理](https://doc.rust-lang.org/book/ch09-00-error-handling.html)

---

## 🆕 Rust 1.93.0 错误处理改进 {#-rust-1930-错误处理改进}

### MaybeUninit 错误处理增强

**改进**: 新增安全的错误处理方法

```rust
// Rust 1.93.0 新特性
use std::mem::MaybeUninit;

// ✅ 1.93: 安全地处理未初始化内存的错误情况
let mut uninit = MaybeUninit::<String>::uninit();
// 使用新的 API 可以更安全地处理错误情况
```

**影响**: 更安全的错误处理模式

---

## Rust 1.92.0 错误处理改进（历史）

### ControlFlow 改进

**改进**: 可以携带详细的错误信息

```rust
// Rust 1.92.0 改进的 ControlFlow
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

## 📚 相关资源 {#-相关资源-1}

### 官方文档

- [Rust 错误处理文档](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [Rust Result 文档](https://doc.rust-lang.org/std/result/)
- [Rust Option 文档](https://doc.rust-lang.org/std/option/)

### 项目内部文档

- [错误处理完整文档](../../../crates/c03_control_fn/docs/tier_02_guides/05_错误处理指南.md)
- [错误处理研究笔记](../../research_notes/)

### 相关速查卡

- [类型系统速查卡](./type_system.md) - Result 和 Option 类型
- [控制流与函数速查卡](./control_flow_functions_cheatsheet.md) - 错误处理模式
- [所有权系统速查卡](./ownership_cheatsheet.md) - 所有权与错误处理
- [异步编程速查卡](./async_patterns.md) - 异步错误处理

---

## 💡 使用场景 {#-使用场景}

### 场景 1: 配置文件解析

```rust
use std::fs;
use std::path::Path;

#[derive(Debug)]
struct DatabaseConfig {
    host: String,
    port: u16,
    username: String,
    password: String,
}

fn parse_config(path: &str) -> Result<DatabaseConfig, Box<dyn std::error::Error>> {
    let content = fs::read_to_string(path)
        .map_err(|e| format!("无法读取配置文件 '{}': {}", path, e))?;

    let lines: Vec<&str> = content.lines().collect();
    if lines.len() < 4 {
        return Err("配置文件格式不完整".into());
    }

    Ok(DatabaseConfig {
        host: lines[0].to_string(),
        port: lines[1].parse().map_err(|_| "无效端口")?,
        username: lines[2].to_string(),
        password: lines[3].to_string(),
    })
}

fn main() {
    match parse_config("db.conf") {
        Ok(config) => println!("配置加载成功: {:?}", config),
        Err(e) => eprintln!("配置加载失败: {}", e),
    }
}
```

### 场景 2: 用户输入验证

```rust
#[derive(Debug)]
struct User {
    name: String,
    age: u8,
    email: String,
}

#[derive(Debug)]
enum ValidationError {
    NameTooShort,
    InvalidAge,
    InvalidEmail,
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ValidationError::NameTooShort => write!(f, "姓名至少需要2个字符"),
            ValidationError::InvalidAge => write!(f, "年龄必须在1-150之间"),
            ValidationError::InvalidEmail => write!(f, "邮箱格式不正确"),
        }
    }
}

impl std::error::Error for ValidationError {}

fn validate_user(name: &str, age: u8, email: &str) -> Result<User, ValidationError> {
    if name.len() < 2 {
        return Err(ValidationError::NameTooShort);
    }
    if age == 0 || age > 150 {
        return Err(ValidationError::InvalidAge);
    }
    if !email.contains('@') {
        return Err(ValidationError::InvalidEmail);
    }

    Ok(User {
        name: name.to_string(),
        age,
        email: email.to_string(),
    })
}

fn main() {
    match validate_user("张三", 25, "zhangsan@example.com") {
        Ok(user) => println!("用户验证通过: {:?}", user),
        Err(e) => println!("验证失败: {}", e),
    }
}
```

### 场景 3: 链式操作处理

```rust
fn divide(a: f64, b: f64) -> Result<f64, &'static str> {
    if b == 0.0 {
        return Err("除数不能为零");
    }
    Ok(a / b)
}

fn sqrt(x: f64) -> Result<f64, &'static str> {
    if x < 0.0 {
        return Err("负数不能开平方");
    }
    Ok(x.sqrt())
}

fn calculate(a: f64, b: f64) -> Result<f64, &'static str> {
    divide(a, b)?
        .abs()
        .pipe(|x| sqrt(x))
}

// 管道辅助函数
trait Pipe: Sized {
    fn pipe<R, E, F: FnOnce(Self) -> Result<R, E>>(self, f: F) -> Result<R, E> {
        f(self)
    }
}

impl<T: Sized> Pipe for T {}

fn main() {
    match calculate(10.0, 2.0) {
        Ok(result) => println!("结果: {}", result),
        Err(e) => println!("错误: {}", e),
    }
}
```

---

## ⚠️ 边界情况 {#️-边界情况}

### 边界 1: 错误类型转换

```rust
use std::num::ParseIntError;
use std::str::Utf8Error;

#[derive(Debug)]
enum AppError {
    Parse(ParseIntError),
    Encoding(Utf8Error),
    Custom(String),
}

impl From<ParseIntError> for AppError {
    fn from(e: ParseIntError) -> Self {
        AppError::Parse(e)
    }
}

impl From<Utf8Error> for AppError {
    fn from(e: Utf8Error) -> Self {
        AppError::Encoding(e)
    }
}

fn parse_and_validate(input: &str) -> Result<i32, AppError> {
    let num: i32 = input.parse()?;  // 自动转换为 AppError
    if num < 0 {
        return Err(AppError::Custom("负数不允许".to_string()));
    }
    Ok(num)
}

fn main() {
    match parse_and_validate("42") {
        Ok(n) => println!("解析成功: {}", n),
        Err(e) => println!("错误: {:?}", e),
    }
}
```

### 边界 2:  panic 恢复

```rust
use std::panic;

fn may_panic(x: i32) -> i32 {
    if x == 0 {
        panic!("不能为零!");
    }
    100 / x
}

fn main() {
    // 捕获 panic
    let result = panic::catch_unwind(|| {
        may_panic(0)
    });

    match result {
        Ok(value) => println!("结果: {}", value),
        Err(_) => println!("发生 panic，但已恢复"),
    }
}
```

### 形式化理论

- [类型系统完备性缺口](../../research_notes/formal_methods/00_completeness_gaps.md) — 错误处理相关的形式化保证
- [Send/Sync 形式化](../../research_notes/formal_methods/send_sync_formalization.md) — 错误在多线程间的传递

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.1+ (Edition 2024)
