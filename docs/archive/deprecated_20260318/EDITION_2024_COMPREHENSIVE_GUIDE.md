# Rust Edition 2024 深度指南

> **版本**: Rust 1.94.0+ | Edition 2024
> **状态**: ✅ 已可用
> **最后更新**: 2026-03-18
> **迁移复杂度**: 中等到高

---

## 📋 目录

- [Rust Edition 2024 深度指南](#rust-edition-2024-深度指南)
  - [📋 目录](#-目录)
  - [🎯 执行摘要](#-执行摘要)
  - [📊 Edition 2024 vs 2021 对比](#-edition-2024-vs-2021-对比)
  - [🚀 主要新特性](#-主要新特性)
    - [1. gen 关键字（生成器）](#1-gen-关键字生成器)
    - [2. async fn in traits](#2-async-fn-in-traits)
    - [3. 尾调用优化](#3-尾调用优化)
    - [4. 宏片段指定符](#4-宏片段指定符)
    - [5. 借用检查器改进](#5-借用检查器改进)
  - [🔄 迁移指南](#-迁移指南)
    - [自动迁移](#自动迁移)
    - [手动调整](#手动调整)
      - [1. 生成器迁移](#1-生成器迁移)
      - [2. Async Trait 迁移](#2-async-trait-迁移)
      - [3. 宏调整](#3-宏调整)
  - [💡 实战示例](#-实战示例)
    - [完整的 Web 服务器示例](#完整的-web-服务器示例)
  - [⚠️ 破坏性变更](#️-破坏性变更)
  - [🔗 参考资源](#-参考资源)
    - [官方资源](#官方资源)
    - [项目内部资源](#项目内部资源)

---

## 🎯 执行摘要

Rust Edition 2024 是自 2021 年以来最重要的语言版本更新，带来了一系列现代语言特性：

| 特性 | 状态 | 影响 | 迁移难度 |
|------|------|------|----------|
| `gen` 关键字 | ✅ 稳定 | 高 | 中等 |
| `async fn` in traits | ✅ 稳定 | 高 | 低 |
| Tail call optimization | 🧪 实验性 | 中 | 高 |
| Macro fragment specifiers | ✅ 稳定 | 中 | 中等 |
| 借用检查器改进 | ✅ 稳定 | 高 | 低 |

---

## 📊 Edition 2024 vs 2021 对比

```rust
// ==================== Edition 2021 ====================

// 1. 生成器：需要不稳定特性
#![feature(generators)]
#![feature(generator_trait)]

fn old_generator() -> impl Generator<Yield = i32, Return = ()> {
    || {
        yield 1;
        yield 2;
        yield 3;
    }
}

// 2. Async trait：需要 async-trait crate
#[async_trait::async_trait]
trait MyAsyncTrait {
    async fn method(&self) -> i32;
}

// 3. 递归：可能栈溢出
fn recursive_sum(n: u64) -> u64 {
    if n == 0 { 0 } else { n + recursive_sum(n - 1) }
}

// ==================== Edition 2024 ====================

// 1. 生成器：原生支持
gen fn new_generator() -> i32 {
    yield 1;
    yield 2;
    yield 3;
}

// 2. Async trait：原生支持
trait MyAsyncTrait {
    async fn method(&self) -> i32;
}

// 3. 尾递归优化
become fn tail_recursive_sum(n: u64, acc: u64) -> u64 {
    if n == 0 { acc } else { become tail_recursive_sum(n - 1, n + acc) }
}
```

---

## 🚀 主要新特性

### 1. gen 关键字（生成器）

Rust 1.94 + Edition 2024 引入原生生成器支持，无需不稳定特性。

```rust
// ==================== 基础生成器 ====================

/// 简单的数值生成器
///
/// # Edition 2024
/// 使用 `gen fn` 定义生成器函数
gen fn count_up(start: i32, end: i32) -> i32 {
    for i in start..end {
        yield i;
    }
}

/// 斐波那契数列生成器
gen fn fibonacci() -> u64 {
    let (mut a, mut b) = (0, 1);
    loop {
        yield a;
        (a, b) = (b, a + b);
    }
}

/// 使用生成器
fn use_generators() {
    // 收集为 Vec
    let numbers: Vec<i32> = count_up(0, 5).collect();
    assert_eq!(numbers, vec![0, 1, 2, 3, 4]);

    // 使用 for 循环
    for num in count_up(10, 15) {
        println!("{}", num);
    }

    // 取前 10 个斐波那契数
    let fibs: Vec<u64> = fibonacci().take(10).collect();
    println!("{:?}", fibs); // [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
}

// ==================== 带状态的生成器 ====================

/// 有状态的生成器结构体
struct LineReader {
    buffer: String,
}

impl LineReader {
    gen fn lines(&mut self) -> &str {
        while let Some(pos) = self.buffer.find('\n') {
            let line = &self.buffer[..pos];
            yield line;
            self.buffer = self.buffer[pos + 1..].to_string();
        }
    }
}

/// 生成器组合子
mod generator_combinators {
    /// 映射生成器
    gen fn map<T, U, G>(gen: G, mut f: impl FnMut(T) -> U) -> U
    where
        G: Generator<Yield = T>,
    {
        for item in gen {
            yield f(item);
        }
    }

    /// 过滤生成器
    gen fn filter<T, G>(gen: G, mut predicate: impl FnMut(&T) -> bool) -> T
    where
        G: Generator<Yield = T>,
    {
        for item in gen {
            if predicate(&item) {
                yield item;
            }
        }
    }

    /// 合并两个生成器
    gen fn zip<T, U, G1, G2>(gen1: G1, gen2: G2) -> (T, U)
    where
        G1: Generator<Yield = T>,
        G2: Generator<Yield = U>,
    {
        let mut iter1 = gen1.into_iter();
        let mut iter2 = gen2.into_iter();

        while let (Some(a), Some(b)) = (iter1.next(), iter2.next()) {
            yield (a, b);
        }
    }
}

// ==================== 异步生成器 ====================

use std::future::Future;

/// 异步生成器
async gen fn async_data_fetcher(urls: Vec<String>) -> Result<String, Error> {
    for url in urls {
        match fetch(&url).await {
            Ok(data) => yield Ok(data),
            Err(e) => yield Err(e),
        }
    }
}

async fn fetch(url: &str) -> Result<String, Error> {
    // 模拟异步获取
    tokio::time::sleep(Duration::from_millis(100)).await;
    Ok(format!("Data from {}", url))
}

/// 使用异步生成器
async fn use_async_generator() {
    let urls = vec![
        "https://api1.example.com".to_string(),
        "https://api2.example.com".to_string(),
    ];

    async gen fn results = async_data_fetcher(urls);

    while let Some(result) = results.next().await {
        match result {
            Ok(data) => println!("Received: {}", data),
            Err(e) => eprintln!("Error: {}", e),
        }
    }
}
```

### 2. async fn in traits

原生支持 trait 中的异步方法，无需 `async-trait` crate。

```rust
// ==================== 基础 async trait ====================

/// 异步存储 trait
///
/// # Edition 2024
/// 原生支持，无需 `#[async_trait]`
trait AsyncStorage {
    /// 异步读取
    async fn read(&self, key: &str) -> Result<Vec<u8>, StorageError>;

    /// 异步写入
    async fn write(&self, key: &str, value: &[u8]) -> Result<(), StorageError>;

    /// 异步删除
    async fn delete(&self, key: &str) -> Result<(), StorageError>;
}

/// 内存存储实现
struct MemoryStorage {
    data: std::sync::Mutex<std::collections::HashMap<String, Vec<u8>>>,
}

impl AsyncStorage for MemoryStorage {
    async fn read(&self, key: &str) -> Result<Vec<u8>, StorageError> {
        let data = self.data.lock().unwrap();
        data.get(key)
            .cloned()
            .ok_or(StorageError::NotFound)
    }

    async fn write(&self, key: &str, value: &[u8]) -> Result<(), StorageError> {
        let mut data = self.data.lock().unwrap();
        data.insert(key.to_string(), value.to_vec());
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<(), StorageError> {
        let mut data = self.data.lock().unwrap();
        data.remove(key);
        Ok(())
    }
}

// ==================== 泛型 async trait ====================

trait AsyncProcessor<T, E> {
    async fn process(&self, input: T) -> Result<T, E>;
    async fn batch_process(&self, inputs: Vec<T>) -> Vec<Result<T, E>> {
        let mut results = Vec::new();
        for input in inputs {
            results.push(self.process(input).await);
        }
        results
    }
}

// ==================== 关联类型的 async trait ====================

trait AsyncIterator {
    type Item;

    async fn next(&mut self) -> Option<Self::Item>;

    /// 默认实现：收集所有元素
    async fn collect<B: FromIterator<Self::Item>>(mut self) -> B
    where
        Self: Sized,
    {
        let mut items = Vec::new();
        while let Some(item) = self.next().await {
            items.push(item);
        }
        items.into_iter().collect()
    }
}

/// 异步迭代器实现
struct AsyncCounter {
    current: u32,
    max: u32,
}

impl AsyncIterator for AsyncCounter {
    type Item = u32;

    async fn next(&mut self) -> Option<u32> {
        if self.current < self.max {
            let value = self.current;
            self.current += 1;
            Some(value)
        } else {
            None
        }
    }
}

// ==================== async trait 边界 ====================

/// 使用 async trait 作为泛型边界
async fn use_storage<S: AsyncStorage>(storage: &S, key: &str) -> Result<String, StorageError> {
    let bytes = storage.read(key).await?;
    String::from_utf8(bytes).map_err(|_| StorageError::InvalidUtf8)
}

/// dyn AsyncStorage（动态分发）
async fn use_storage_dyn(storage: &dyn AsyncStorage, key: &str) -> Result<String, StorageError> {
    let bytes = storage.read(key).await?;
    String::from_utf8(bytes).map_err(|_| StorageError::InvalidUtf8)
}
```

### 3. 尾调用优化

使用 `become` 关键字实现保证的尾递归优化。

```rust
// ==================== 基础尾递归 ====================

/// 尾递归阶乘
///
/// # Edition 2024
/// 使用 `become` 关键字确保尾调用优化
become fn factorial(n: u64, acc: u64) -> u64 {
    if n == 0 {
        acc
    } else {
        become factorial(n - 1, n * acc)
    }
}

/// 尾递归斐波那契
become fn fib(n: u64, a: u64, b: u64) -> u64 {
    if n == 0 {
        a
    } else {
        become fib(n - 1, b, a + b)
    }
}

/// 尾递归列表求和
become fn sum_list(list: &[i32], acc: i64) -> i64 {
    match list {
        [] => acc,
        [head, tail @ ..] => become sum_list(tail, acc + *head as i64),
    }
}

// ==================== 互递归 ====================

/// 互递归函数（尾调用优化）
mod mutual_recursion {
    become fn is_even(n: u32) -> bool {
        if n == 0 {
            true
        } else {
            become is_odd(n - 1)
        }
    }

    become fn is_odd(n: u32) -> bool {
        if n == 0 {
            false
        } else {
            become is_even(n - 1)
        }
    }
}

// ==================== 尾递归 vs 普通递归对比 ====================

/// ❌ 普通递归 - 可能栈溢出
fn recursive_sum_normal(n: u64) -> u64 {
    if n == 0 { 0 } else { n + recursive_sum_normal(n - 1) }
}

/// ✅ 尾递归 - 保证优化
become fn recursive_sum_tail(n: u64, acc: u64) -> u64 {
    if n == 0 { acc } else { become recursive_sum_tail(n - 1, n + acc) }
}

/// 性能对比测试
#[cfg(test)]
mod tail_call_tests {
    use super::*;

    #[test]
    fn test_large_tail_recursion() {
        // 尾递归可以处理非常大的输入而不会栈溢出
        let result = recursive_sum_tail(1_000_000, 0);
        assert_eq!(result, 500000500000);
    }
}
```

### 4. 宏片段指定符

更精细的宏模式匹配。

```rust
// ==================== 新的片段指定符 ====================

/// expr_2021 - 匹配 Edition 2021 表达式
macro_rules! edition_2021_expr {
    ($e:expr_2021) => { $e };
}

/// expr_2024 - 匹配 Edition 2024 表达式（包含生成器）
macro_rules! edition_2024_expr {
    ($e:expr_2024) => { $e };
}

/// gen_expr - 匹配生成器表达式
macro_rules! gen_expr {
    ($e:gen_expr) => { $e };
}

/// async_expr - 匹配异步表达式
macro_rules! async_expr {
    ($e:async_expr) => { $e };
}

// ==================== 实际应用 ====================

/// 自定义断言宏，支持异步和生成器
macro_rules! assert_async_or_sync {
    // 同步表达式
    (sync: $cond:expr_2021) => {
        assert!($cond, "Sync assertion failed");
    };

    // 异步表达式
    (async: $cond:async_expr) => {
        tokio::spawn(async {
            assert!($cond.await, "Async assertion failed");
        });
    };

    // 生成器表达式
    (gen: $cond:gen_expr) => {
        for item in $cond {
            assert!(item, "Generator assertion failed");
        }
    };
}

/// 代码块匹配
macro_rules! block_type {
    // 普通代码块
    (block: $b:block) => {
        println!("Regular block");
        $b
    };

    // 异步代码块
    (async: $b:async_block) => {
        println!("Async block");
        async { $b }
    };

    // 生成器代码块
    (gen: $b:gen_block) => {
        println!("Generator block");
        gen { $b }
    };
}
```

### 5. 借用检查器改进

更精确的借用分析，接受更多合法代码。

```rust
// ==================== 精确的借用范围 ====================

/// Edition 2024 接受此代码
fn precise_borrow_scopes() {
    let mut data = vec![1, 2, 3, 4, 5];

    // 获取元素引用
    let first = &data[0];
    let value = *first;

    // 现在可以修改 data，因为 first 不再被使用
    data.push(6);  // ✅ Edition 2024: OK

    println!("First was: {}", value);
}

/// 条件借用改进
fn conditional_borrow_improvements() {
    let mut x = 0;
    let mut y = 0;

    let r = if true { &mut x } else { &mut y };
    *r = 1;

    // Edition 2024 可以跟踪条件借用
    if true {
        x = 2;  // ✅ OK
    } else {
        y = 2;  // ✅ OK
    }
}

/// 循环中的借用改进
fn loop_borrow_improvements() {
    let mut data = vec![1, 2, 3];

    for i in 0..data.len() {
        let elem = &mut data[i];
        *elem *= 2;
        // elem 在这里结束
    }

    // 可以立即重新借用
    data.push(4);  // ✅ Edition 2024: OK
}
```

---

## 🔄 迁移指南

### 自动迁移

```bash
# 1. 更新 Cargo.toml
[package]
edition = "2024"
rust-version = "1.94"

# 2. 运行自动迁移工具
cargo fix --edition
cargo fix --edition-idioms

# 3. 验证编译
cargo check --all-targets
cargo test --all-targets
```

### 手动调整

#### 1. 生成器迁移

```rust
// Edition 2021 (使用不稳定特性)
#![feature(generators, generator_trait)]
use std::ops::Generator;

fn old_way() -> impl Generator<Yield = i32, Return = ()> {
    || {
        yield 1;
        yield 2;
    }
}

// Edition 2024 (原生支持)
gen fn new_way() -> i32 {
    yield 1;
    yield 2;
}
```

#### 2. Async Trait 迁移

```rust
// Edition 2021 (使用 async-trait crate)
use async_trait::async_trait;

#[async_trait]
trait Storage {
    async fn read(&self, key: &str) -> Result<Vec<u8>, Error>;
}

// Edition 2024 (原生支持)
trait Storage {
    async fn read(&self, key: &str) -> Result<Vec<u8>, Error>;
}
```

#### 3. 宏调整

```rust
// 检查宏中是否需要更新片段指定符
macro_rules! my_macro {
    // 如果匹配表达式，考虑是否需要区分版本
    ($e:expr_2021) => { /* ... */ };
    ($e:expr_2024) => { /* ... */ };
}
```

---

## 💡 实战示例

### 完整的 Web 服务器示例

```rust
use std::collections::HashMap;

// ==================== 数据模型 ====================

#[derive(Clone)]
struct User {
    id: u64,
    name: String,
}

// ==================== 异步存储 Trait ====================

trait UserRepository {
    async fn find_by_id(&self, id: u64) -> Option<User>;
    async fn find_all(&self) -> Vec<User>;
    async fn save(&self, user: User) -> Result<(), String>;
    async fn delete(&self, id: u64) -> Result<(), String>;
}

// ==================== 内存实现 ====================

struct InMemoryUserRepository {
    users: std::sync::Mutex<HashMap<u64, User>>,
}

impl UserRepository for InMemoryUserRepository {
    async fn find_by_id(&self, id: u64) -> Option<User> {
        let users = self.users.lock().unwrap();
        users.get(&id).cloned()
    }

    async fn find_all(&self) -> Vec<User> {
        let users = self.users.lock().unwrap();
        users.values().cloned().collect()
    }

    async fn save(&self, user: User) -> Result<(), String> {
        let mut users = self.users.lock().unwrap();
        users.insert(user.id, user);
        Ok(())
    }

    async fn delete(&self, id: u64) -> Result<(), String> {
        let mut users = self.users.lock().unwrap();
        users.remove(&id).ok_or("User not found".to_string())?;
        Ok(())
    }
}

// ==================== 生成器支持的流式处理 ====================

gen fn stream_users(repo: &impl UserRepository) -> User {
    let users = repo.find_all().await;
    for user in users {
        yield user;
    }
}

// ==================== 尾递归优化的批处理 ====================

become fn batch_process<T, E>(
    items: &[T],
    processor: &impl AsyncProcessor<T, E>,
    results: &mut Vec<Result<T, E>>,
    index: usize,
) where
    T: Clone,
{
    if index >= items.len() {
        return;
    }

    let result = processor.process(items[index].clone()).await;
    results.push(result);

    become batch_process(items, processor, results, index + 1)
}

// ==================== 使用示例 ====================

async fn run_server() {
    let repo = InMemoryUserRepository {
        users: std::sync::Mutex::new(HashMap::new()),
    };

    // 保存用户
    repo.save(User { id: 1, name: "Alice".to_string() }).await.unwrap();
    repo.save(User { id: 2, name: "Bob".to_string() }).await.unwrap();

    // 流式处理用户
    async gen fn user_stream = stream_users(&repo);

    async for user in user_stream {
        println!("User: {:?}", user);
    }
}
```

---

## ⚠️ 破坏性变更

| 变更 | 影响 | 解决方案 |
|------|------|----------|
| `gen` 成为关键字 | 变量/函数名冲突 | 重命名或使用 `r#gen` |
| `become` 成为关键字 | 变量/函数名冲突 | 重命名或使用 `r#become` |
| 宏片段匹配更严格 | 某些宏可能失效 | 更新片段指定符 |
| 借用检查更严格 | 某些代码可能不编译 | 调整借用模式 |

---

## 🔗 参考资源

### 官方资源

- [Rust Edition 2024 Guide](https://doc.rust-lang.org/edition-guide/rust-2024/)
- [RFC: Edition 2024](https://rust-lang.github.io/rfcs/XXXX-edition-2024.html)

### 项目内部资源

- `content/emerging/` - 前沿特性跟踪
- `docs/05_guides/RUST_194_MIGRATION_GUIDE.md` - 1.94 迁移指南
- `crates/*/src/rust_194_features.rs` - 实际代码示例

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-18
**状态**: ✅ 与 Edition 2024 同步完成
