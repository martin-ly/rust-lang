# 04. Result和Option类型


## 📊 目录

- [1. 引言](#1-引言)
- [2. Result类型](#2-result类型)
  - [2.1 基础定义](#21-基础定义)
  - [2.2 构造方法](#22-构造方法)
  - [2.3 模式匹配](#23-模式匹配)
  - [2.4 错误传播](#24-错误传播)
- [3. Option类型](#3-option类型)
  - [3.1 基础定义](#31-基础定义)
  - [3.2 构造方法](#32-构造方法)
  - [3.3 模式匹配](#33-模式匹配)
  - [3.4 链式操作](#34-链式操作)
- [4. 组合方法](#4-组合方法)
  - [4.1 Result组合](#41-result组合)
  - [4.2 Option组合](#42-option组合)
- [5. 转换方法](#5-转换方法)
  - [5.1 Result转换](#51-result转换)
  - [5.2 映射方法](#52-映射方法)
- [6. 实用方法](#6-实用方法)
  - [6.1 解包方法](#61-解包方法)
  - [6.2 检查方法](#62-检查方法)
- [7. 高级模式](#7-高级模式)
  - [7.1 错误链](#71-错误链)
  - [7.2 自定义错误](#72-自定义错误)
- [8. 性能考虑](#8-性能考虑)
  - [8.1 零成本抽象](#81-零成本抽象)
  - [8.2 内存布局](#82-内存布局)
- [9. 最佳实践](#9-最佳实践)
  - [9.1 错误处理原则](#91-错误处理原则)
  - [9.2 避免反模式](#92-避免反模式)
- [10. 总结](#10-总结)


## 1. 引言

Result和Option是Rust错误处理系统的核心类型，提供了类型安全的错误处理机制。

## 2. Result类型

### 2.1 基础定义

**定义 2.1** (Result类型)
Result类型表示可能成功或失败的操作结果：
$$\text{Result}\langle T, E \rangle = \text{Ok}(T) + \text{Err}(E)$$

```rust
enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

### 2.2 构造方法

```rust
// 成功值构造
let success: Result<i32, String> = Ok(42);

// 错误值构造
let error: Result<i32, String> = Err("Something went wrong".to_string());

// 从函数返回
fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}
```

### 2.3 模式匹配

```rust
fn handle_result(result: Result<i32, String>) {
    match result {
        Ok(value) => println!("Success: {}", value),
        Err(error) => println!("Error: {}", error),
    }
}

// 使用if let
fn handle_success(result: Result<i32, String>) {
    if let Ok(value) = result {
        println!("Success: {}", value);
    }
}
```

### 2.4 错误传播

```rust
fn process_data(data: &str) -> Result<i32, String> {
    let parsed = data.parse::<i32>()
        .map_err(|e| format!("Parse error: {}", e))?;
    
    if parsed < 0 {
        return Err("Value must be positive".to_string());
    }
    
    Ok(parsed * 2)
}
```

## 3. Option类型

### 3.1 基础定义

**定义 3.1** (Option类型)
Option类型表示可能存在或不存在的值：
$$\text{Option}\langle T \rangle = \text{Some}(T) + \text{None}$$

```rust
enum Option<T> {
    Some(T),
    None,
}
```

### 3.2 构造方法

```rust
// 存在值构造
let some_value: Option<i32> = Some(42);

// 空值构造
let none_value: Option<i32> = None;

// 从函数返回
fn find_element(arr: &[i32], target: i32) -> Option<usize> {
    arr.iter().position(|&x| x == target)
}
```

### 3.3 模式匹配

```rust
fn handle_option(option: Option<i32>) {
    match option {
        Some(value) => println!("Found: {}", value),
        None => println!("Not found"),
    }
}

// 使用if let
fn handle_some(option: Option<i32>) {
    if let Some(value) = option {
        println!("Found: {}", value);
    }
}
```

### 3.4 链式操作

```rust
fn process_option(option: Option<i32>) -> Option<i32> {
    option
        .filter(|&x| x > 0)
        .map(|x| x * 2)
        .and_then(|x| if x < 100 { Some(x) } else { None })
}
```

## 4. 组合方法

### 4.1 Result组合

```rust
// 组合多个Result
fn combine_results() -> Result<i32, String> {
    let a = Ok(10);
    let b = Ok(20);
    
    // 使用and_then
    a.and_then(|x| b.map(|y| x + y))
}

// 收集多个Result
fn collect_results() -> Result<Vec<i32>, String> {
    let results = vec![Ok(1), Ok(2), Ok(3)];
    
    results.into_iter().collect()
}
```

### 4.2 Option组合

```rust
// 组合多个Option
fn combine_options() -> Option<i32> {
    let a = Some(10);
    let b = Some(20);
    
    // 使用and_then
    a.and_then(|x| b.map(|y| x + y))
}

// 收集多个Option
fn collect_options() -> Option<Vec<i32>> {
    let options = vec![Some(1), Some(2), Some(3)];
    
    options.into_iter().collect()
}
```

## 5. 转换方法

### 5.1 Result转换

```rust
// Result转Option
fn result_to_option(result: Result<i32, String>) -> Option<i32> {
    result.ok()
}

// Option转Result
fn option_to_result(option: Option<i32>) -> Result<i32, String> {
    option.ok_or("Value not found".to_string())
}

// 错误类型转换
fn convert_error(result: Result<i32, std::io::Error>) -> Result<i32, String> {
    result.map_err(|e| e.to_string())
}
```

### 5.2 映射方法

```rust
// 成功值映射
let result: Result<i32, String> = Ok(42);
let mapped = result.map(|x| x * 2);  // Ok(84)

// 错误值映射
let result: Result<i32, String> = Err("error".to_string());
let mapped = result.map_err(|e| format!("Custom: {}", e));

// 同时映射
let result: Result<i32, String> = Ok(42);
let mapped = result.map_or(0, |x| x * 2);  // 84
```

## 6. 实用方法

### 6.1 解包方法

```rust
// unwrap - 成功时返回值，失败时panic
let value = Ok(42).unwrap();  // 42

// unwrap_or - 失败时返回默认值
let value = Err("error").unwrap_or(0);  // 0

// unwrap_or_else - 失败时调用闭包
let value = Err("error").unwrap_or_else(|_| 42);  // 42

// expect - 失败时panic并显示消息
let value = Ok(42).expect("Should be a number");  // 42
```

### 6.2 检查方法

```rust
// 检查是否为成功
let result: Result<i32, String> = Ok(42);
assert!(result.is_ok());
assert!(!result.is_err());

// 检查是否为错误
let result: Result<i32, String> = Err("error".to_string());
assert!(result.is_err());
assert!(!result.is_ok());

// 获取成功值
let result: Result<i32, String> = Ok(42);
assert_eq!(result.ok(), Some(42));

// 获取错误值
let result: Result<i32, String> = Err("error".to_string());
assert_eq!(result.err(), Some("error".to_string()));
```

## 7. 高级模式

### 7.1 错误链

```rust
#[derive(Debug)]
enum AppError {
    Io(std::io::Error),
    Parse(String),
}

impl std::fmt::Display for AppError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            AppError::Io(e) => write!(f, "IO error: {}", e),
            AppError::Parse(e) => write!(f, "Parse error: {}", e),
        }
    }
}

impl std::error::Error for AppError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            AppError::Io(e) => Some(e),
            AppError::Parse(_) => None,
        }
    }
}
```

### 7.2 自定义错误

```rust
use thiserror::Error;

#[derive(Error, Debug)]
enum CustomError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Parse error: {0}")]
    Parse(String),
    
    #[error("Validation error: {0}")]
    Validation(String),
}

fn process_with_custom_error() -> Result<i32, CustomError> {
    let data = std::fs::read_to_string("data.txt")?;
    let value = data.parse::<i32>()
        .map_err(|e| CustomError::Parse(e.to_string()))?;
    
    if value < 0 {
        return Err(CustomError::Validation("Value must be positive".to_string()));
    }
    
    Ok(value)
}
```

## 8. 性能考虑

### 8.1 零成本抽象

```rust
// Result和Option在编译时被优化为简单的枚举
// 没有运行时开销

// 编译器优化示例
fn optimized_function() -> Result<i32, String> {
    Ok(42)  // 编译为简单的成功状态
}

// 编译后的代码类似于：
// enum Result { Ok(i32), Err(String) }
// 没有额外的运行时开销
```

### 8.2 内存布局

```rust
// Result<T, E>的内存布局
// 如果T和E的大小不同，Result会使用最大大小
// 加上一个判别字段（通常是一个字节）

// Option<T>的内存布局
// 对于非零类型，None表示为全零值
// 对于零类型，使用判别字段
```

## 9. 最佳实践

### 9.1 错误处理原则

```rust
// 1. 使用?操作符进行错误传播
fn good_error_handling() -> Result<String, std::io::Error> {
    let contents = std::fs::read_to_string("file.txt")?;
    Ok(contents)
}

// 2. 提供有意义的错误信息
fn meaningful_error() -> Result<i32, String> {
    "invalid".parse::<i32>()
        .map_err(|e| format!("Failed to parse number: {}", e))
}

// 3. 使用适当的错误类型
fn appropriate_error_type() -> Result<i32, std::num::ParseIntError> {
    "42".parse::<i32>()
}
```

### 9.2 避免反模式

```rust
// 避免：过度使用unwrap
fn bad_pattern() -> i32 {
    "42".parse::<i32>().unwrap()  // 可能panic
}

// 避免：忽略错误
fn ignore_error() {
    let _ = std::fs::read_to_string("file.txt");  // 忽略错误
}

// 避免：不适当的错误类型
fn inappropriate_error() -> Result<i32, Box<dyn std::error::Error>> {
    // 过于宽泛的错误类型
    Ok(42)
}
```

## 10. 总结

Result和Option类型是Rust错误处理系统的核心，提供了：

1. **类型安全**：编译时确保错误处理完整性
2. **零成本抽象**：没有运行时性能开销
3. **组合性**：支持复杂的错误处理模式
4. **可读性**：清晰的错误处理代码结构

这些类型使得Rust程序能够安全、高效地处理各种错误情况，是Rust可靠性保证的重要组成部分。
