# 📖 Rust 最佳实践指南 (Best Practices)

> **文档定位**: Rust 开发的最佳实践和编码规范
> **使用方式**: 作为日常开发参考，提升代码质量
> **相关文档**: [贡献指南](./CONTRIBUTING.md) | [快速参考](./QUICK_REFERENCE.md) | [故障排查](./TROUBLESHOOTING.md)

**最后更新**: 2025-10-19
**适用版本**: Rust 1.90+

---

## 📋 目录

- [📖 Rust 最佳实践指南 (Best Practices)](#-rust-最佳实践指南-best-practices)
  - [📋 目录](#-目录)
  - [代码风格](#代码风格)
    - [命名约定](#命名约定)
    - [代码组织](#代码组织)
    - [格式化](#格式化)
  - [所有权与借用](#所有权与借用)
    - [优先使用借用](#优先使用借用)
    - [避免不必要的克隆](#避免不必要的克隆)
    - [合理使用智能指针](#合理使用智能指针)
  - [错误处理](#错误处理)
    - [使用 Result 而非 panic](#使用-result-而非-panic)
    - [定义自定义错误类型](#定义自定义错误类型)
    - [提供有用的错误消息](#提供有用的错误消息)
  - [性能优化](#性能优化)
    - [使用迭代器](#使用迭代器)
    - [预分配容量](#预分配容量)
    - [避免不必要的分配](#避免不必要的分配)
    - [使用适当的集合类型](#使用适当的集合类型)
  - [并发编程](#并发编程)
    - [优先使用消息传递](#优先使用消息传递)
    - [正确使用 Arc 和 Mutex](#正确使用-arc-和-mutex)
    - [使用原子类型](#使用原子类型)
  - [API 设计](#api-设计)
    - [使用 Builder 模式](#使用-builder-模式)
    - [提供多种便利方法](#提供多种便利方法)
    - [接受灵活的参数类型](#接受灵活的参数类型)
  - [测试](#测试)
    - [编写充分的测试](#编写充分的测试)
    - [使用测试辅助函数](#使用测试辅助函数)
    - [使用基准测试](#使用基准测试)
  - [文档](#文档)
    - [编写清晰的文档注释](#编写清晰的文档注释)
  - [依赖管理](#依赖管理)
    - [谨慎选择依赖](#谨慎选择依赖)
  - [安全编程](#安全编程)
    - [最小化 unsafe 使用](#最小化-unsafe-使用)
  - [🔗 更多资源](#-更多资源)
    - [官方指南](#官方指南)
    - [项目文档](#项目文档)

---

## 代码风格

### 命名约定

```rust
// ✅ 好的做法

// 类型使用 PascalCase
struct UserProfile { }
enum Status { }
trait Drawable { }

// 函数和变量使用 snake_case
fn calculate_total() { }
let user_name = "Alice";

// 常量使用 SCREAMING_SNAKE_CASE
const MAX_CONNECTIONS: u32 = 100;
const API_VERSION: &str = "v1.0";

// 生命周期使用短小的名称
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str { x }

// ❌ 避免

// 不要使用 camelCase 命名函数
fn calculateTotal() { }  // 错误

// 不要使用非描述性名称
let x = get_data();  // x 是什么？
let data = get_data();  // 好一些，但还可以更具体
let user_profile = get_data();  // 更好
```

### 代码组织

```rust
// ✅ 好的做法

// 1. 按功能分组，使用模块
mod user {
    pub struct User { }
    pub fn create_user() { }
    pub fn delete_user() { }
}

mod auth {
    pub fn login() { }
    pub fn logout() { }
}

// 2. 使用 impl 块组织相关方法
impl User {
    // 构造函数
    pub fn new(name: String) -> Self { }

    // 访问器
    pub fn name(&self) -> &str { }

    // 修改器
    pub fn set_name(&mut self, name: String) { }

    // 其他方法
    pub fn is_valid(&self) -> bool { }
}

// 3. 将相关的 trait 实现放在一起
impl Display for User { }
impl Debug for User { }
impl PartialEq for User { }

// ❌ 避免

// 所有代码都放在一个文件中
// 没有模块划分
// 方法散乱分布
```

### 格式化

```rust
// ✅ 好的做法

// 使用 rustfmt 格式化代码
// cargo fmt

// 使用 4 空格缩进
fn main() {
    if condition {
        println!("hello");
    }
}

// 链式调用换行对齐
let result = vec![1, 2, 3]
    .iter()
    .map(|x| x * 2)
    .filter(|x| x > &5)
    .collect::<Vec<_>>();

// 长参数列表换行
fn complex_function(
    param1: String,
    param2: i32,
    param3: bool,
) -> Result<String, Error> {
    // ...
}

// ❌ 避免

// 手动格式化（容易不一致）
// 混用 tab 和空格
// 过长的行（> 100 字符）
```

---

## 所有权与借用

### 优先使用借用

```rust
// ✅ 好的做法

// 传递引用而非所有权
fn calculate_length(s: &String) -> usize {
    s.len()
}

let s1 = String::from("hello");
let len = calculate_length(&s1);
println!("{}, {}", s1, len);  // s1 仍然可用

// 使用切片类型更通用
fn first_word(s: &str) -> &str {
    // 接受 &String 或 &str
    &s[0..1]
}

// ❌ 避免

// 不必要地获取所有权
fn calculate_length(s: String) -> usize {
    s.len()
}  // s 被丢弃

let s1 = String::from("hello");
let len = calculate_length(s1);
// println!("{}", s1);  // 错误：s1 已被移动
```

### 避免不必要的克隆

```rust
// ✅ 好的做法

// 只在确实需要所有权时克隆
fn process_data(data: &[i32]) -> Vec<i32> {
    data.iter()
        .map(|x| x * 2)
        .collect()
}

// 使用 Cow (Clone on Write) 按需克隆
use std::borrow::Cow;

fn process_text<'a>(text: &'a str) -> Cow<'a, str> {
    if text.contains("bad") {
        Cow::Owned(text.replace("bad", "good"))
    } else {
        Cow::Borrowed(text)
    }
}

// ❌ 避免

// 过度克隆
fn process_data(data: &[i32]) -> Vec<i32> {
    let cloned = data.to_vec();  // 不必要的克隆
    cloned.iter()
        .map(|x| x * 2)
        .collect()
}
```

### 合理使用智能指针

```rust
// ✅ 好的做法

// Box: 堆分配大对象
struct LargeStruct { /* ... */ }
let large = Box::new(LargeStruct { /* ... */ });

// Rc: 共享不可变数据（单线程）
use std::rc::Rc;
let shared = Rc::new(vec![1, 2, 3]);
let reference1 = Rc::clone(&shared);
let reference2 = Rc::clone(&shared);

// Arc: 共享数据（多线程）
use std::sync::Arc;
let shared = Arc::new(vec![1, 2, 3]);

// RefCell: 内部可变性（单线程）
use std::cell::RefCell;
let data = RefCell::new(5);
*data.borrow_mut() += 1;

// ❌ 避免

// 过度使用 Rc/Arc
let x = Rc::new(5);  // 简单类型不需要

// 混用 Rc 和多线程
// 编译器会阻止这种错误用法
```

---

## 错误处理

### 使用 Result 而非 panic

```rust
// ✅ 好的做法

// 返回 Result 让调用者处理错误
fn divide(a: f64, b: f64) -> Result<f64, String> {
    if b == 0.0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

// 使用 ? 运算符传播错误
fn process_file(path: &str) -> Result<String, std::io::Error> {
    let content = std::fs::read_to_string(path)?;
    Ok(content.to_uppercase())
}

// ❌ 避免

// 使用 panic! 处理可恢复错误
fn divide(a: f64, b: f64) -> f64 {
    if b == 0.0 {
        panic!("Division by zero");  // 不好
    }
    a / b
}

// 忽略错误
let content = std::fs::read_to_string("file.txt").unwrap();  // 可能 panic
```

### 定义自定义错误类型

```rust
// ✅ 好的做法

use std::fmt;

#[derive(Debug)]
enum MyError {
    Io(std::io::Error),
    Parse(std::num::ParseIntError),
    Custom(String),
}

impl fmt::Display for MyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MyError::Io(e) => write!(f, "IO error: {}", e),
            MyError::Parse(e) => write!(f, "Parse error: {}", e),
            MyError::Custom(s) => write!(f, "Error: {}", s),
        }
    }
}

impl std::error::Error for MyError {}

// 实现 From 自动转换
impl From<std::io::Error> for MyError {
    fn from(err: std::io::Error) -> Self {
        MyError::Io(err)
    }
}

// 使用 thiserror 简化（推荐）
use thiserror::Error;

#[derive(Error, Debug)]
enum MyError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Parse error: {0}")]
    Parse(#[from] std::num::ParseIntError),

    #[error("{0}")]
    Custom(String),
}

// ❌ 避免

// 使用 String 作为错误类型
fn process() -> Result<(), String> {
    // 丢失了错误的类型信息
    Err("Something went wrong".to_string())
}
```

### 提供有用的错误消息

```rust
// ✅ 好的做法

// 包含上下文信息
fn read_config(path: &str) -> Result<Config, Error> {
    std::fs::read_to_string(path)
        .map_err(|e| Error::Io {
            path: path.to_string(),
            source: e,
        })?;
    // ...
}

// 使用 anyhow 添加上下文（应用程序）
use anyhow::{Context, Result};

fn process() -> Result<()> {
    let config = std::fs::read_to_string("config.toml")
        .context("Failed to read config file")?;
    // ...
}

// ❌ 避免

// 模糊的错误消息
fn process() -> Result<(), String> {
    Err("Error".to_string())  // 什么错误？
}
```

---

## 性能优化

### 使用迭代器

```rust
// ✅ 好的做法

// 迭代器是零成本抽象
let sum: i32 = (1..=100)
    .filter(|x| x % 2 == 0)
    .map(|x| x * x)
    .sum();

// 链式操作避免中间分配
let result: Vec<_> = data
    .iter()
    .filter(|x| x.is_valid())
    .map(|x| x.process())
    .collect();

// ❌ 避免

// 使用循环和临时变量（性能较差）
let mut filtered = Vec::new();
for x in &data {
    if x.is_valid() {
        filtered.push(x);
    }
}
let mut result = Vec::new();
for x in &filtered {
    result.push(x.process());
}
```

### 预分配容量

```rust
// ✅ 好的做法

// 已知大小时预分配
let mut v = Vec::with_capacity(1000);
for i in 0..1000 {
    v.push(i);
}

// 字符串拼接预分配
let mut s = String::with_capacity(total_len);
for part in parts {
    s.push_str(part);
}

// ❌ 避免

// 频繁重新分配
let mut v = Vec::new();
for i in 0..1000 {
    v.push(i);  // 可能多次重新分配
}
```

### 避免不必要的分配

```rust
// ✅ 好的做法

// 使用 &str 而非 String
fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

// 使用切片而非 Vec
fn sum(numbers: &[i32]) -> i32 {
    numbers.iter().sum()
}

// 原地修改
fn process_inplace(data: &mut [i32]) {
    for x in data {
        *x *= 2;
    }
}

// ❌ 避免

// 不必要的分配
fn greet(name: String) -> String {  // 不必要的所有权转移
    format!("Hello, {}!", name)
}

// 返回新向量而非原地修改
fn process(data: Vec<i32>) -> Vec<i32> {
    data.into_iter().map(|x| x * 2).collect()
}
```

### 使用适当的集合类型

```rust
// ✅ 好的做法

// 需要快速查找：使用 HashMap
use std::collections::HashMap;
let mut scores = HashMap::new();
scores.insert("Alice", 95);

// 需要有序：使用 BTreeMap
use std::collections::BTreeMap;
let mut sorted = BTreeMap::new();

// 需要唯一性：使用 HashSet
use std::collections::HashSet;
let mut unique = HashSet::new();

// 需要顺序访问：使用 Vec
let mut list = Vec::new();

// 需要队列：使用 VecDeque
use std::collections::VecDeque;
let mut queue = VecDeque::new();

// ❌ 避免

// 用 Vec 做频繁查找
let mut data = Vec::new();
if data.contains(&key) { }  // O(n)

// 应该用 HashSet
let mut data = HashSet::new();
if data.contains(&key) { }  // O(1)
```

---

## 并发编程

### 优先使用消息传递

```rust
// ✅ 好的做法

use std::sync::mpsc;
use std::thread;

// 使用 Channel 通信
let (tx, rx) = mpsc::channel();

thread::spawn(move || {
    tx.send("Hello").unwrap();
});

let msg = rx.recv().unwrap();
println!("{}", msg);

// ❌ 避免

// 过度使用共享状态
use std::sync::{Arc, Mutex};

let counter = Arc::new(Mutex::new(0));
// 多个线程竞争同一个锁
```

### 正确使用 Arc 和 Mutex

```rust
// ✅ 好的做法

use std::sync::{Arc, Mutex};
use std::thread;

// Arc<Mutex<T>> 用于共享可变状态
let counter = Arc::new(Mutex::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let counter = Arc::clone(&counter);
    let handle = thread::spawn(move || {
        let mut num = counter.lock().unwrap();
        *num += 1;
    });  // 锁在这里释放
    handles.push(handle);
}

// ❌ 避免

// 持有锁时间过长
let counter = Arc::new(Mutex::new(0));
let handle = thread::spawn(move || {
    let mut num = counter.lock().unwrap();
    *num += 1;
    // 执行耗时操作
    expensive_operation();  // 不好：持锁时间过长
});
```

### 使用原子类型

```rust
// ✅ 好的做法

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

// 简单计数使用原子类型
let counter = Arc::new(AtomicUsize::new(0));

let counter2 = Arc::clone(&counter);
thread::spawn(move || {
    counter2.fetch_add(1, Ordering::SeqCst);
});

// ❌ 避免

// 简单计数使用 Mutex（开销更大）
let counter = Arc::new(Mutex::new(0));
```

---

## API 设计

### 使用 Builder 模式

```rust
// ✅ 好的做法

// 复杂对象使用 Builder
pub struct Config {
    host: String,
    port: u16,
    timeout: u64,
}

pub struct ConfigBuilder {
    host: String,
    port: u16,
    timeout: u64,
}

impl ConfigBuilder {
    pub fn new() -> Self {
        Self {
            host: "localhost".to_string(),
            port: 8080,
            timeout: 30,
        }
    }

    pub fn host(mut self, host: String) -> Self {
        self.host = host;
        self
    }

    pub fn port(mut self, port: u16) -> Self {
        self.port = port;
        self
    }

    pub fn timeout(mut self, timeout: u64) -> Self {
        self.timeout = timeout;
        self
    }

    pub fn build(self) -> Config {
        Config {
            host: self.host,
            port: self.port,
            timeout: self.timeout,
        }
    }
}

// 使用
let config = ConfigBuilder::new()
    .host("api.example.com".to_string())
    .port(443)
    .build();

// 或使用 derive_builder
use derive_builder::Builder;

#[derive(Builder)]
pub struct Config {
    host: String,
    port: u16,
    #[builder(default = "30")]
    timeout: u64,
}
```

### 提供多种便利方法

```rust
// ✅ 好的做法

impl MyString {
    // 基本方法
    pub fn from_str(s: &str) -> Self {
        MyString(s.to_string())
    }

    // From trait
    impl From<String> for MyString {
        fn from(s: String) -> Self {
            MyString(s)
        }
    }

    // FromStr trait
    impl FromStr for MyString {
        type Err = ParseError;
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Ok(MyString(s.to_string()))
        }
    }
}

// 用户可以多种方式创建
let s1 = MyString::from_str("hello");
let s2 = MyString::from("hello".to_string());
let s3: MyString = "hello".parse().unwrap();
```

### 接受灵活的参数类型

```rust
// ✅ 好的做法

// 使用 impl Trait
fn print_items(items: impl IntoIterator<Item = String>) {
    for item in items {
        println!("{}", item);
    }
}

// 可以接受 Vec, 数组, 迭代器等
print_items(vec!["a".to_string(), "b".to_string()]);
print_items(["a".to_string(), "b".to_string()]);

// 使用 AsRef<str>
fn process_text(text: impl AsRef<str>) {
    let text = text.as_ref();
    println!("{}", text);
}

// 可以接受 &str, String, Cow 等
process_text("hello");
process_text(String::from("hello"));

// ❌ 避免

// 要求具体类型
fn print_items(items: Vec<String>) {  // 太严格
    for item in items {
        println!("{}", item);
    }
}
```

---

## 测试

### 编写充分的测试

```rust
// ✅ 好的做法

#[cfg(test)]
mod tests {
    use super::*;

    // 测试正常情况
    #[test]
    fn test_add_positive_numbers() {
        assert_eq!(add(2, 3), 5);
    }

    // 测试边界情况
    #[test]
    fn test_add_zero() {
        assert_eq!(add(0, 0), 0);
    }

    // 测试错误情况
    #[test]
    fn test_divide_by_zero() {
        let result = divide(10.0, 0.0);
        assert!(result.is_err());
    }

    // 测试 panic
    #[test]
    #[should_panic(expected = "divide by zero")]
    fn test_panic_on_zero() {
        divide_panicking(10, 0);
    }

    // 使用 Result 测试
    #[test]
    fn test_with_result() -> Result<(), String> {
        if add(2, 3) == 5 {
            Ok(())
        } else {
            Err("Math is broken".to_string())
        }
    }
}
```

### 使用测试辅助函数

```rust
// ✅ 好的做法

#[cfg(test)]
mod tests {
    use super::*;

    // 测试辅助函数
    fn create_test_user() -> User {
        User {
            id: 1,
            name: "Test User".to_string(),
            email: "test@example.com".to_string(),
        }
    }

    #[test]
    fn test_user_validation() {
        let user = create_test_user();
        assert!(user.is_valid());
    }

    #[test]
    fn test_user_serialization() {
        let user = create_test_user();
        let json = serde_json::to_string(&user).unwrap();
        assert!(json.contains("Test User"));
    }
}
```

### 使用基准测试

```rust
// ✅ 好的做法

// benches/my_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| {
        b.iter(|| fibonacci(black_box(20)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

---

## 文档

### 编写清晰的文档注释

```rust
// ✅ 好的做法

/// 计算两个数的和
///
/// # Examples
///
/// ```
/// let result = add(2, 3);
/// assert_eq!(result, 5);
/// ```
///
/// # Panics
///
/// 当结果溢出时会 panic
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

/// 用户配置
///
/// 存储用户的配置选项
///
/// # Fields
///
/// * `name` - 用户名
/// * `age` - 用户年龄
pub struct UserConfig {
    /// 用户名
    pub name: String,
    /// 用户年龄（必须 >= 0）
    pub age: u8,
}

// ❌ 避免

// 无文档
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 无用的文档
/// 加法函数
pub fn add(a: i32, b: i32) -> i32 {  // 名字已经说明了
    a + b
}
```

---

## 依赖管理

### 谨慎选择依赖

```toml
# ✅ 好的做法

[dependencies]
# 使用稳定、维护良好的库
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.0", features = ["full"] }

# 只启用需要的 features
serde_json = "1.0"  # 不启用不需要的 features

# 使用 workspace 管理多个 crate
[workspace]
members = ["crate1", "crate2"]

# ❌ 避免

# 过多的依赖
# 过时的依赖
# 不维护的依赖
```

---

## 安全编程

### 最小化 unsafe 使用

```rust
// ✅ 好的做法

// 只在必要时使用 unsafe
// 并清楚文档化安全要求
/// # Safety
///
/// `ptr` 必须是有效的、对齐的、非空的指针
pub unsafe fn read_unaligned(ptr: *const u8) -> u8 {
    std::ptr::read_unaligned(ptr)
}

// 将 unsafe 封装在安全接口中
pub struct Buffer {
    data: Vec<u8>,
}

impl Buffer {
    pub fn get(&self, index: usize) -> Option<u8> {
        if index < self.data.len() {
            // 内部使用 unsafe，但对外提供安全接口
            Some(unsafe { *self.data.get_unchecked(index) })
        } else {
            None
        }
    }
}

// ❌ 避免

// 不必要的 unsafe
pub fn add(a: i32, b: i32) -> i32 {
    unsafe {
        a + b  // 完全不需要 unsafe
    }
}
```

---

## 🔗 更多资源

### 官方指南

- **Rust API Guidelines**: [rust-lang.github.io/api-guidelines/](https://rust-lang.github.io/api-guidelines/)
- **Rust Performance Book**: [nnethercote.github.io/perf-book/](https://nnethercote.github.io/perf-book/)
- **Rust Design Patterns**: [rust-unofficial.github.io/patterns/](https://rust-unofficial.github.io/patterns/)

### 项目文档

- **快速参考**: [QUICK_REFERENCE.md](./QUICK_REFERENCE.md)
- **故障排查**: [TROUBLESHOOTING.md](./TROUBLESHOOTING.md)
- **贡献指南**: [CONTRIBUTING.md](./CONTRIBUTING.md)

---

**写出优雅的 Rust 代码！** 🚀

最佳实践是经验的总结，但不是教条。根据实际情况灵活应用。

**最后更新**: 2025-10-19
**维护团队**: Rust 学习社区
**版本**: v1.0
