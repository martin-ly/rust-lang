# Rust 最佳实践指南

> **最后更新**: 2026-03-08
> **适用版本**: Rust 1.94.0+

---

## 目录

- [Rust 最佳实践指南](#rust-最佳实践指南)
  - [目录](#目录)
  - [代码风格](#代码风格)
    - [命名规范](#命名规范)
    - [代码组织](#代码组织)
  - [错误处理](#错误处理)
    - [优先使用 Result 而非 panic](#优先使用-result-而非-panic)
    - [自定义错误类型](#自定义错误类型)
  - [性能优化](#性能优化)
    - [零成本抽象](#零成本抽象)
    - [内存布局优化](#内存布局优化)
  - [并发安全](#并发安全)
    - [Send 和 Sync](#send-和-sync)
    - [使用标准库并发原语](#使用标准库并发原语)
  - [测试实践](#测试实践)
    - [单元测试](#单元测试)
    - [文档测试](#文档测试)
  - [相关文档](#相关文档)

---

## 代码风格

### 命名规范

```rust
// 结构体使用 PascalCase
struct UserAccount { }

// 函数和变量使用 snake_case
fn calculate_total() -> i32 { }

// 常量使用 SCREAMING_SNAKE_CASE
const MAX_CONNECTIONS: usize = 100;

// 类型参数使用单个大写字母
fn process<T, U>(data: T) -> U { }
```

### 代码组织

```rust
// 1. 按功能分组相关代码
// 2. 使用模块清晰分离关注点
// 3. 优先使用组合而非继承

mod parser {
    pub struct Parser { }
    impl Parser {
        pub fn new() -> Self { }
    }
}
```

---

## 错误处理

### 优先使用 Result 而非 panic

```rust
// ✅ 好的做法
fn read_config(path: &str) -> Result<Config, io::Error> {
    let content = fs::read_to_string(path)?;
    Config::from_str(&content)
}

// ❌ 避免在库代码中使用 unwrap
let config = read_config("config.toml").unwrap();
```

### 自定义错误类型

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("Parse error: {0}")]
    Parse(String),
}
```

---

## 性能优化

### 零成本抽象

```rust
// 迭代器链在发布模式下会被优化为高效循环
let sum: i32 = (0..100)
    .filter(|x| x % 2 == 0)
    .map(|x| x * x)
    .sum();
```

### 内存布局优化

```rust
// 将大字段放在结构体后面
struct Optimized {
    small: u8,      // 1 byte
    _padding: [u8; 7],
    large: [u64; 100], // 大数组
}
```

---

## 并发安全

### Send 和 Sync

```rust
// 自动实现 Send 和 Sync 的类型是线程安全的
// 手动实现需要 unsafe

unsafe impl Send for MyType {}
unsafe impl Sync for MyType {}
```

### 使用标准库并发原语

```rust
use std::sync::{Arc, Mutex};
use std::thread;

let data = Arc::new(Mutex::new(0));
let data_clone = Arc::clone(&data);

thread::spawn(move || {
    let mut num = data_clone.lock().unwrap();
    *num += 1;
});
```

---

## 测试实践

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_addition() {
        assert_eq!(add(2, 2), 4);
    }

    #[test]
    #[should_panic(expected = "divide by zero")]
    fn test_divide_by_zero() {
        divide(1, 0);
    }
}
```

### 文档测试

```rust
/// 计算两数之和
/// ```
/// use mycrate::add;
/// assert_eq!(add(2, 3), 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

---

## 相关文档

- [README.md](./README.md)
- [CONTRIBUTING.md](./CONTRIBUTING.md)
- [TROUBLESHOOTING.md](./TROUBLESHOOTING.md)
