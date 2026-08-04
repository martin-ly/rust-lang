# 练习: 异步编程基础

---
**元数据**_

```yaml
id: c06_01
module: c06_async
title: "异步编程基础"
difficulty: intermediate
estimated_time: 30
tags: [async, await, tokio, futures]
```

---

## 📝 问题描述

将同步代码转换为异步代码，使用async/await语法实现并发网络请求。

## 🎯 学习目标

- 理解async/await语法
- 掌握异步函数的编写
- 学会使用tokio运行时
- 实现并发操作

## 💻 起始代码

[🚀 在 Playground 中打开](https://play.rust-lang.org/?version=stable&mode=debug&edition=2024)

```rust
use tokio;
use std::time::Duration;

// TODO: 将此函数转换为异步函数
fn fetch_data(id: u32) -> String {
    // 模拟网络请求
    std::thread::sleep(Duration::from_secs(1));
    format!("Data from request {}", id)
}

fn main() {
    // TODO: 使用tokio运行时
    let data1 = fetch_data(1);
    let data2 = fetch_data(2);
    
    println!("{}", data1);
    println!("{}", data2);
}
```

## ❓ 问题

1. 如何将同步函数改为异步函数？
2. 如何并发执行多个异步操作？
3. tokio运行时的作用是什么？

## 💡 提示

提示 1: async fn

使用`async fn`关键字声明异步函数：

```rust
async fn fetch_data(id: u32) -> String {
    // ...
}
```

提示 2: tokio::main

使用`#[tokio::main]`宏创建异步main函数：

```rust
#[tokio::main]
async fn main() {
    // ...
}
```

提示 3: await

使用`.await`等待异步操作完成：

```rust
let data = fetch_data(1).await;
```

提示 4: 并发

使用`tokio::join!`宏并发执行多个异步操作：

```rust
let (data1, data2) = tokio::join!(
    fetch_data(1),
    fetch_data(2)
);
```

## ✅ 测试用例

```rust
#[tokio::test]
async fn test_fetch_data() {
    let data = fetch_data(1).await;
    assert_eq!(data, "Data from request 1");
}

#[tokio::test]
async fn test_concurrent_fetch() {
    let start = std::time::Instant::now();
    
    let (data1, data2, data3) = tokio::join!(
        fetch_data(1),
        fetch_data(2),
        fetch_data(3)
    );
    
    let elapsed = start.elapsed();
    
    // 并发执行应该快于顺序执行
    assert!(elapsed < Duration::from_secs(2));
    assert!(data1.contains("1"));
    assert!(data2.contains("2"));
    assert!(data3.contains("3"));
}
```

## 📚 参考答案

点击查看答案 - 基础异步版本

```rust
use tokio;
use std::time::Duration;

async fn fetch_data(id: u32) -> String {
    // 使用tokio的异步sleep
    tokio::time::sleep(Duration::from_secs(1)).await;
    format!("Data from request {}", id)
}

#[tokio::main]
async fn main() {
    let data1 = fetch_data(1).await;
    let data2 = fetch_data(2).await;
    
    println!("{}", data1);
    println!("{}", data2);
}
```

**解释**:

- 使用`async fn`声明异步函数
- 使用`tokio::time::sleep`代替`std::thread::sleep`
- 使用`.await`等待异步操作完成
- 使用`#[tokio::main]`创建异步runtime

**性能**: 这个版本是顺序执行的，总时间约2秒。
点击查看答案 - 并发版本

```rust
use tokio;
use std::time::Duration;

async fn fetch_data(id: u32) -> String {
    tokio::time::sleep(Duration::from_secs(1)).await;
    format!("Data from request {}", id)
}

#[tokio::main]
async fn main() {
    // 并发执行两个请求
    let (data1, data2) = tokio::join!(
        fetch_data(1),
        fetch_data(2)
    );
    
    println!("{}", data1);
    println!("{}", data2);
}
```

**解释**:

- `tokio::join!`宏并发执行多个Future
- 两个请求同时进行，而不是顺序执行
- 总时间约1秒，而不是2秒

**性能提升**: 2倍速度提升！
点击查看答案 - 高级版本（错误处理）

```rust
use tokio;
use std::time::Duration;

#[derive(Debug)]
enum FetchError {
    Timeout,
    InvalidResponse,
}

async fn fetch_data_with_timeout(
    id: u32,
    timeout: Duration
) -> Result<String, FetchError> {
    // 使用tokio::time::timeout添加超时
    let result = tokio::time::timeout(
        timeout,
        async {
            tokio::time::sleep(Duration::from_secs(1)).await;
            format!("Data from request {}", id)
        }
    ).await;
    
    match result {
        Ok(data) => Ok(data),
        Err(_) => Err(FetchError::Timeout),
    }
}

#[tokio::main]
async fn main() {
    // 并发执行，带超时处理
    let results = tokio::join!(
        fetch_data_with_timeout(1, Duration::from_secs(2)),
        fetch_data_with_timeout(2, Duration::from_secs(2))
    );
    
    match results.0 {
        Ok(data) => println!("Success: {}", data),
        Err(e) => println!("Error: {:?}", e),
    }
    
    match results.1 {
        Ok(data) => println!("Success: {}", data),
        Err(e) => println!("Error: {:?}", e),
    }
}
```

**高级特性**:

- 添加超时控制
- 使用`Result`进行错误处理
- 更健壮的生产代码

## 🎓 扩展学习

### async/await vs 线程

```rust
// 线程: 操作系统级并发（重量级）
std::thread::spawn(|| {
    // CPU密集型任务
});

// async/await: 用户态并发（轻量级）
tokio::spawn(async {
    // I/O密集型任务
});
```

### 何时使用async

- ✅ 网络请求
- ✅ 文件I/O
- ✅ 数据库查询
- ✅ 高并发服务器
- ❌ CPU密集型计算（使用线程）

### tokio运行时

```rust
// 单线程运行时
#[tokio::main(flavor = "current_thread")]
async fn main() { }

// 多线程运行时（默认）
#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn main() { }
```

## 🔗 相关资源

- [Tokio Tutorial](https://tokio.rs/tokio/tutorial)
- [Async Book](https://rust-lang.github.io/async-book/)
- [Tokio API Docs](https://docs.rs/tokio)
- 下一个练习: [02_futures.md](./02_futures.md)

---

**难度**: 🟡 中级  
**预计时间**: 30 分钟  
**创建日期**: 2025-10-20
