# 测试基础（Testing Fundamentals）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [测试基础](#测试基础testing-fundamentals)
  - [概述](#概述)
  - [单元测试](#单元测试)
  - [集成测试](#集成测试)
  - [文档测试](#文档测试)
  - [实践示例](#实践示例)
  - [最佳实践](#最佳实践)
  - [参考资料](#参考资料)

---

## 概述

Rust 内置了强大的测试框架，支持单元测试、集成测试和文档测试。测试是确保代码质量的重要手段。

## 单元测试

### 基本测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
    }
}

fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

### 测试失败

```rust
#[test]
fn test_failure() {
    panic!("这个测试会失败");
}

#[test]
#[should_panic(expected = "值超出范围")]
fn test_should_panic() {
    // 这个测试期望 panic
    if true {
        panic!("值超出范围");
    }
}
```

### 使用 Result

```rust
#[test]
fn test_with_result() -> Result<(), String> {
    if 2 + 2 == 4 {
        Ok(())
    } else {
        Err(String::from("数学出错了"))
    }
}
```

## 集成测试

### 测试目录结构

```
my_project/
├── Cargo.toml
├── src/
│   └── lib.rs
└── tests/
    └── integration_test.rs
```

### 集成测试示例

```rust
// tests/integration_test.rs
use my_project;

#[test]
fn test_integration() {
    let result = my_project::add(2, 3);
    assert_eq!(result, 5);
}

#[test]
fn test_multiple_operations() {
    assert_eq!(my_project::add(1, 1), 2);
    assert_eq!(my_project::multiply(2, 3), 6);
}
```

### 测试模块

```rust
// tests/common/mod.rs
pub fn setup() {
    // 测试设置代码
    println!("设置测试环境");
}

// tests/integration_test.rs
mod common;

#[test]
fn test_with_setup() {
    common::setup();
    // 测试代码
}
```

## 文档测试

### 代码示例作为测试

```rust
/// 将两个数字相加
///
/// # 示例
///
/// ```
/// let result = add(2, 3);
/// assert_eq!(result, 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

/// 计算阶乘
///
/// # 示例
///
/// ```
/// # use my_project::factorial;
/// assert_eq!(factorial(5), 120);
/// ```
pub fn factorial(n: u32) -> u32 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}
```

## 实践示例

### 示例 1：测试结构体

```rust
#[derive(Debug, PartialEq)]
struct Rectangle {
    width: u32,
    height: u32,
}

impl Rectangle {
    fn new(width: u32, height: u32) -> Self {
        Rectangle { width, height }
    }

    fn area(&self) -> u32 {
        self.width * self.height
    }

    fn can_hold(&self, other: &Rectangle) -> bool {
        self.width > other.width && self.height > other.height
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_area() {
        let rect = Rectangle::new(10, 20);
        assert_eq!(rect.area(), 200);
    }

    #[test]
    fn test_can_hold() {
        let rect1 = Rectangle::new(10, 20);
        let rect2 = Rectangle::new(5, 10);
        assert!(rect1.can_hold(&rect2));
        assert!(!rect2.can_hold(&rect1));
    }
}
```

### 示例 2：测试错误处理

```rust
pub struct Guess {
    value: i32,
}

impl Guess {
    pub fn new(value: i32) -> Result<Guess, String> {
        if value < 1 || value > 100 {
            return Err(format!("值必须在 1 到 100 之间，得到 {}", value));
        }
        Ok(Guess { value })
    }

    pub fn value(&self) -> i32 {
        self.value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_guess() {
        let guess = Guess::new(50).unwrap();
        assert_eq!(guess.value(), 50);
    }

    #[test]
    #[should_panic(expected = "值必须在 1 到 100 之间")]
    fn test_invalid_guess_too_high() {
        Guess::new(200).unwrap();
    }

    #[test]
    fn test_invalid_guess_result() {
        let result = Guess::new(200);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("值必须在 1 到 100 之间"));
    }
}
```

### 示例 3：异步测试

```rust
use tokio::test;

#[tokio::test]
async fn test_async_function() {
    let result = async_function().await;
    assert_eq!(result, 42);
}

async fn async_function() -> i32 {
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    42
}
```

### 示例 4：测试私有函数

```rust
pub fn add_two(a: i32) -> i32 {
    internal_adder(a, 2)
}

fn internal_adder(a: i32, b: i32) -> i32 {
    a + b
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_internal_adder() {
        // 可以测试私有函数
        assert_eq!(internal_adder(2, 3), 5);
    }
}
```

## 最佳实践

### 1. 测试组织

```rust
#[cfg(test)]
mod tests {
    use super::*;

    mod add_tests {
        use super::*;

        #[test]
        fn test_add_positive() {
            assert_eq!(add(2, 3), 5);
        }

        #[test]
        fn test_add_negative() {
            assert_eq!(add(-2, -3), -5);
        }
    }

    mod multiply_tests {
        use super::*;

        #[test]
        fn test_multiply() {
            assert_eq!(multiply(2, 3), 6);
        }
    }
}
```

### 2. 使用断言宏

```rust
#[test]
fn test_assertions() {
    let value = 5;

    assert!(value > 0);
    assert_eq!(value, 5);
    assert_ne!(value, 0);

    let result = Some(5);
    assert!(result.is_some());
    assert_eq!(result.unwrap(), 5);
}
```

### 3. 测试覆盖率

```rust
// 使用 cargo-tarpaulin 检查测试覆盖率
// cargo install cargo-tarpaulin
// cargo tarpaulin --out Html
```

### 4. 测试性能

```rust
use std::time::Duration;

#[test]
#[should_panic]
fn test_performance() {
    let start = std::time::Instant::now();
    // 执行操作
    let duration = start.elapsed();

    if duration > Duration::from_millis(100) {
        panic!("操作太慢");
    }
}
```

## 参考资料

- [测试索引](./00_index.md)
- [软件工程索引](../00_index.md)
- [Rust 测试文档](https://doc.rust-lang.org/book/ch11-00-testing.html)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回软件工程: [`../00_index.md`](../00_index.md)
