# 错误处理

> **Rust 的健壮错误处理机制**
> **预计时间**: 4 小时
**权威来源**: [Rust Book - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)

## 🎯 学习目标

完成本章后，你将能够：

- [ ] 使用 `Result` 和 `Option` 处理错误
- [ ] 传播错误而不 panic
- [ ] 实现自定义错误类型
- [ ] 使用 `?` 运算符简化错误处理

## 📋 先决条件

- 理解枚举类型
- 了解模式匹配

## 🧠 核心概念

### 1. Result 类型

Rust 使用 `Result<T, E>` 表示可能失败的操作：

```rust
enum Result<T, E> {
    Ok(T),   // 成功，包含值
    Err(E),  // 失败，包含错误
}
```

#### 基础使用

```rust
use std::fs::File;

fn main() {
    let f = File::open("hello.txt");

    match f {
        Ok(file) => println!("File opened: {:?}", file),
        Err(error) => println!("Error: {:?}", error),
    }
}
```

#### 传播错误

```rust
use std::fs::File;
use std::io::{self, Read};

fn read_username_from_file() -> Result<String, io::Error> {
    let mut file = match File::open("hello.txt") {
        Ok(f) => f,
        Err(e) => return Err(e),  // 传播错误
    };

    let mut username = String::new();
    match file.read_to_string(&mut username) {
        Ok(_) => Ok(username),
        Err(e) => Err(e),
    }
}
```

#### ? 运算符简化

```rust
fn read_username_from_file() -> Result<String, io::Error> {
    let mut file = File::open("hello.txt")?;  // 如果 Err，直接返回
    let mut username = String::new();
    file.read_to_string(&mut username)?;
    Ok(username)
}

// 更简洁
fn read_username_from_file() -> Result<String, io::Error> {
    let mut username = String::new();
    File::open("hello.txt")?.read_to_string(&mut username)?;
    Ok(username)
}

// 最简洁
fn read_username_from_file() -> Result<String, io::Error> {
    std::fs::read_to_string("hello.txt")
}
```

### 2. Option 类型

`Option<T>` 用于可能为空的值：

```rust
enum Option<T> {
    Some(T),
    None,
}
```

#### 基础使用

```rust
fn find_char(s: &str, c: char) -> Option<usize> {
    s.find(c)
}

fn main() {
    match find_char("hello", 'e') {
        Some(index) => println!("Found at: {}", index),
        None => println!("Not found"),
    }
}
```

#### Option 到 Result 转换

```rust
fn get_element(vec: &[i32], index: usize) -> Result<i32, String> {
    vec.get(index)
        .copied()
        .ok_or_else(|| format!("Index {} out of bounds", index))
}
```

### 3. 错误处理辅助方法

| 方法 | 作用 | 示例 |
|------|------|------|
| `unwrap()` | 获取值或 panic | `f.unwrap()` |
| `expect()` | 带消息的 unwrap | `f.expect("file not found")` |
| `unwrap_or()` | 提供默认值 | `f.unwrap_or(0)` |
| `unwrap_or_default()` | 使用类型默认值 | `f.unwrap_or_default()` |
| `map()` | 转换 Ok/Some 值 | `r.map(\|x\| x * 2)` |
| `and_then()` | 链式操作 | `r.and_then(parse)` |

```rust
let result = "42".parse::<i32>();

// map 转换
let doubled = result.map(|n| n * 2);  // Ok(84)

// unwrap_or 提供默认值
let num = result.unwrap_or(0);  // 42 或 0

// and_then 链式
let result = "42".parse::<i32>()
    .and_then(|n| if n > 0 { Ok(n) } else { Err("negative") });
```

### 4. 自定义错误类型

```rust
use std::fmt;
use std::error::Error;

#[derive(Debug)]
enum MyError {
    NotFound(String),
    InvalidInput(String),
    IoError(std::io::Error),
}

impl fmt::Display for MyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MyError::NotFound(msg) => write!(f, "Not found: {}", msg),
            MyError::InvalidInput(msg) => write!(f, "Invalid input: {}", msg),
            MyError::IoError(e) => write!(f, "IO error: {}", e),
        }
    }
}

impl Error for MyError {}

// 从其他错误转换
impl From<std::io::Error> for MyError {
    fn from(err: std::io::Error) -> Self {
        MyError::IoError(err)
    }
}
```

### 5. 使用 thiserror 简化

```rust
use thiserror::Error;

#[derive(Error, Debug)]
enum AppError {
    #[error("database error: {0}")]
    Database(#[from] sqlx::Error),

    #[error("io error: {0}")]
    Io(#[from] std::io::Error),

    #[error("not found: {0}")]
    NotFound(String),
}
```

## 💻 综合示例

### 配置加载器

```rust
use std::collections::HashMap;
use std::fs;

#[derive(Debug)]
enum ConfigError {
    FileNotFound(String),
    ParseError(String),
    InvalidValue(String),
}

struct Config {
    settings: HashMap<String, String>,
}

impl Config {
    fn from_file(path: &str) -> Result<Self, ConfigError> {
        let content = fs::read_to_string(path)
            .map_err(|_| ConfigError::FileNotFound(path.to_string()))?;

        let mut settings = HashMap::new();

        for line in content.lines() {
            if line.starts_with('#') || line.is_empty() {
                continue;
            }

            let parts: Vec<&str> = line.splitn(2, '=').collect();
            if parts.len() != 2 {
                return Err(ConfigError::ParseError(line.to_string()));
            }

            settings.insert(parts[0].trim().to_string(),
                          parts[1].trim().to_string());
        }

        Ok(Config { settings })
    }

    fn get(&self, key: &str) -> Option<&String> {
        self.settings.get(key)
    }
}

fn main() {
    match Config::from_file("app.config") {
        Ok(config) => {
            println!("Host: {:?}", config.get("host"));
            println!("Port: {:?}", config.get("port"));
        }
        Err(e) => eprintln!("Failed to load config: {:?}", e),
    }
}
```

## ⚠️ 常见陷阱

| 错误 | 原因 | 修复 |
|------|------|------|
| `unwrap()` panic | 未处理的错误 | 使用 `match` 或 `?` |
| 忽略 Result | 编译警告 | 显式处理或使用 `let _ = ...` |
| 错误类型不匹配 | 未实现 From | 实现 `From` trait 或 map |

## 🎮 练习

### 练习 1: 改进错误处理

将以下代码的错误处理改进为使用 `Result`：

```rust
fn read_config() -> String {
    std::fs::read_to_string("config.txt").unwrap()
}
```

### 练习 2: 链式操作

使用 `map`, `and_then` 等方法实现一个函数，从字符串解析数字，加倍，再转换回字符串。

<details>
<summary>参考答案</summary>

```rust
fn process_number(s: &str) -> Result<String, String> {
    s.parse::<i32>()
        .map_err(|e| format!("Parse error: {}", e))
        .map(|n| n * 2)
        .map(|n| n.to_string())
}
```

</details>

## ✅ 自我检测

1. `Result` 和 `Option` 的主要区别是什么？
2. `?` 运算符的作用是什么？
3. 什么时候应该 panic，什么时候应该返回 Result？

## 📖 延伸阅读

- [Rust Book - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [thiserror crate](https://docs.rs/thiserror/)
- [anyhow crate](https://docs.rs/anyhow/)

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.94.0
**最后更新**: 2026-03-19
