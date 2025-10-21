# Futures - 异步编程基础

## 📋 目录

- [概述](#概述)
- [核心概念](#核心概念)
- [Futures Crate](#futures-crate)
- [异步运行时对比](#异步运行时对比)
- [常用工具](#常用工具)
- [实战示例](#实战示例)
- [最佳实践](#最佳实践)

---

## 概述

Futures 是 Rust 异步编程的核心抽象，代表一个尚未完成的计算。

### 核心依赖

```toml
[dependencies]
# Futures 工具库
futures = "0.3"

# 异步运行时
tokio = { version = "1.35", features = ["full"] }
async-std = "1.12"
smol = "2.0"
```

---

## 核心概念

### Future Trait

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// Future 的核心定义
pub trait Future {
    type Output;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}

// Poll 枚举
pub enum Poll<T> {
    Ready(T),      // 已完成
    Pending,       // 未完成，需要再次轮询
}
```

### 异步执行模型

```rust
async fn hello_world() {
    println!("Hello");
    // .await 暂停执行，让出控制权
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    println!("World");
}

// 等价于：
fn hello_world_manual() -> impl Future<Output = ()> {
    async {
        println!("Hello");
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        println!("World");
    }
}
```

---

## Futures Crate

### 安装与导入

```toml
[dependencies]
futures = { version = "0.3", features = ["std", "async-await"] }
```

### 核心模块

| 模块 | 用途 | 示例 |
|------|------|------|
| `future` | Future 工具函数 | `join!`, `select!`, `ready` |
| `stream` | 异步迭代器 | `Stream` trait, `StreamExt` |
| `sink` | 异步写入 | `Sink` trait, `SinkExt` |
| `io` | 异步 I/O | `AsyncRead`, `AsyncWrite` |
| `task` | 任务管理 | `spawn`, `block_on` |
| `channel` | 异步通道 | `mpsc`, `oneshot` |

---

## 异步运行时对比

### 功能矩阵

| 特性 | Tokio | async-std | smol |
|------|-------|-----------|------|
| **生态成熟度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |
| **性能** | 高 | 中高 | 高 |
| **API 风格** | 工业级 | 类标准库 | 极简 |
| **功能完整性** | 非常完整 | 完整 | 精简 |
| **学习曲线** | 中等 | 平缓 | 平缓 |
| **二进制大小** | 较大 | 中等 | 小 |

### Tokio

```rust
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() {
    println!("开始");
    sleep(Duration::from_secs(1)).await;
    println!("结束");
}
```

### async-std

```rust
use async_std::task;
use std::time::Duration;

fn main() {
    task::block_on(async {
        println!("开始");
        task::sleep(Duration::from_secs(1)).await;
        println!("结束");
    });
}
```

### smol

```rust
use smol::Timer;
use std::time::Duration;

fn main() {
    smol::block_on(async {
        println!("开始");
        Timer::after(Duration::from_secs(1)).await;
        println!("结束");
    });
}
```

---

## 常用工具

### 1. 组合 Futures

#### `join!` - 并发执行

```rust
use futures::join;

async fn fetch_user(id: u32) -> String {
    format!("User {}", id)
}

async fn fetch_posts(user_id: u32) -> Vec<String> {
    vec![format!("Post by user {}", user_id)]
}

async fn load_profile(id: u32) {
    // 并发执行，等待所有完成
    let (user, posts) = join!(
        fetch_user(id),
        fetch_posts(id)
    );
    
    println!("用户: {}, 帖子数: {}", user, posts.len());
}
```

#### `try_join!` - 错误短路

```rust
use futures::try_join;

async fn fetch_data() -> Result<String, std::io::Error> {
    Ok("数据".to_string())
}

async fn fetch_config() -> Result<String, std::io::Error> {
    Ok("配置".to_string())
}

async fn load_all() -> Result<(), std::io::Error> {
    // 任意一个失败则提前返回
    let (data, config) = try_join!(
        fetch_data(),
        fetch_config()
    )?;
    
    println!("数据: {}, 配置: {}", data, config);
    Ok(())
}
```

#### `select!` - 竞速

```rust
use futures::select;
use futures::future::FutureExt;

async fn task1() -> i32 { 1 }
async fn task2() -> i32 { 2 }

async fn race() {
    // 哪个先完成用哪个
    select! {
        result1 = task1().fuse() => println!("任务1先完成: {}", result1),
        result2 = task2().fuse() => println!("任务2先完成: {}", result2),
    }
}
```

### 2. Stream 流处理

#### 创建 Stream

```rust
use futures::stream::{self, StreamExt};

async fn stream_basics() {
    // 从迭代器创建
    let mut stream = stream::iter(vec![1, 2, 3, 4, 5]);
    
    // 消费 stream
    while let Some(item) = stream.next().await {
        println!("项: {}", item);
    }
}
```

#### Stream 转换

```rust
use futures::stream::{self, StreamExt};

async fn stream_transformations() {
    let stream = stream::iter(1..=10);
    
    let result: Vec<_> = stream
        .filter(|x| async move { x % 2 == 0 })  // 过滤偶数
        .map(|x| x * 2)                          // 乘以2
        .take(3)                                 // 取前3个
        .collect()                               // 收集到 Vec
        .await;
    
    println!("{:?}", result); // [4, 8, 12]
}
```

#### 缓冲与并发

```rust
use futures::stream::{self, StreamExt};

async fn concurrent_processing() {
    let stream = stream::iter(1..=10);
    
    // 并发处理（最多3个同时）
    let results: Vec<_> = stream
        .map(|x| async move {
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            x * 2
        })
        .buffer_unordered(3)  // 并发度为3
        .collect()
        .await;
    
    println!("{:?}", results);
}
```

### 3. Sink 数据写入

```rust
use futures::sink::SinkExt;
use futures::channel::mpsc;

async fn sink_example() {
    let (mut tx, mut rx) = mpsc::channel(10);
    
    // 发送数据
    tx.send(1).await.unwrap();
    tx.send(2).await.unwrap();
    tx.send(3).await.unwrap();
    
    // 关闭发送端
    tx.close().await.unwrap();
    
    // 接收数据
    while let Some(item) = rx.next().await {
        println!("收到: {}", item);
    }
}
```

### 4. 异步 I/O

```rust
use futures::io::{AsyncReadExt, AsyncWriteExt};

async fn async_io_example() {
    // 异步读取
    let mut reader = futures::io::Cursor::new(b"Hello, World!");
    let mut buffer = [0u8; 5];
    
    reader.read_exact(&mut buffer).await.unwrap();
    println!("{:?}", std::str::from_utf8(&buffer).unwrap());
    
    // 异步写入
    let mut writer = Vec::new();
    writer.write_all(b"Async write").await.unwrap();
    println!("{:?}", String::from_utf8(writer).unwrap());
}
```

---

## 实战示例

### 1. 超时控制

```rust
use tokio::time::{timeout, Duration};

async fn may_take_long() -> Result<String, &'static str> {
    tokio::time::sleep(Duration::from_secs(2)).await;
    Ok("完成".to_string())
}

async fn with_timeout() {
    match timeout(Duration::from_secs(1), may_take_long()).await {
        Ok(Ok(result)) => println!("成功: {}", result),
        Ok(Err(e)) => println!("任务错误: {}", e),
        Err(_) => println!("超时！"),
    }
}
```

### 2. 并发限制

```rust
use futures::stream::{self, StreamExt};
use tokio::time::{sleep, Duration};

async fn rate_limited_tasks() {
    let tasks: Vec<_> = (0..20)
        .map(|i| async move {
            println!("任务 {} 开始", i);
            sleep(Duration::from_millis(100)).await;
            println!("任务 {} 完成", i);
            i
        })
        .collect();
    
    // 最多5个并发任务
    let results: Vec<_> = stream::iter(tasks)
        .buffer_unordered(5)
        .collect()
        .await;
    
    println!("完成 {} 个任务", results.len());
}
```

### 3. 重试机制

```rust
use tokio::time::{sleep, Duration};

async fn unreliable_operation() -> Result<String, &'static str> {
    static mut ATTEMPT: i32 = 0;
    unsafe {
        ATTEMPT += 1;
        if ATTEMPT < 3 {
            Err("失败")
        } else {
            Ok("成功".to_string())
        }
    }
}

async fn retry_with_backoff() {
    let mut delay = Duration::from_millis(100);
    
    for attempt in 1..=5 {
        match unreliable_operation().await {
            Ok(result) => {
                println!("成功: {}", result);
                return;
            }
            Err(e) => {
                println!("尝试 {} 失败: {}", attempt, e);
                sleep(delay).await;
                delay *= 2; // 指数退避
            }
        }
    }
    
    println!("所有尝试都失败了");
}
```

### 4. 异步管道

```rust
use futures::stream::{self, StreamExt};

async fn pipeline() {
    let numbers = stream::iter(1..=10);
    
    let result = numbers
        // 阶段1: 过滤
        .filter(|x| async move { x % 2 == 0 })
        // 阶段2: 转换
        .map(|x| async move { x * x })
        .buffered(3)
        // 阶段3: 累加
        .fold(0, |acc, x| async move { acc + x })
        .await;
    
    println!("结果: {}", result); // 2² + 4² + 6² + 8² + 10² = 220
}
```

### 5. 取消与清理

```rust
use tokio::select;
use tokio::time::{sleep, Duration};
use tokio::sync::oneshot;

async fn cancellable_task() {
    let (cancel_tx, mut cancel_rx) = oneshot::channel::<()>();
    
    let task = tokio::spawn(async move {
        loop {
            println!("工作中...");
            sleep(Duration::from_millis(500)).await;
        }
    });
    
    // 2秒后取消
    tokio::spawn(async move {
        sleep(Duration::from_secs(2)).await;
        let _ = cancel_tx.send(());
    });
    
    select! {
        _ = task => println!("任务完成"),
        _ = cancel_rx => {
            println!("任务被取消");
        }
    }
}
```

---

## 最佳实践

### 1. 避免阻塞

```rust
// ❌ 错误：在异步上下文中阻塞
async fn bad_example() {
    std::thread::sleep(std::time::Duration::from_secs(1)); // 阻塞整个线程
}

// ✅ 正确：使用异步睡眠
async fn good_example() {
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
}
```

### 2. 正确的取消处理

```rust
use tokio::select;

async fn cancellation_safe() {
    let mut data = Vec::new();
    
    loop {
        select! {
            // 使用 biased 确保取消优先
            biased;
            
            _ = tokio::signal::ctrl_c() => {
                println!("正在清理...");
                // 清理逻辑
                break;
            }
            item = fetch_data() => {
                data.push(item);
            }
        }
    }
}

async fn fetch_data() -> i32 {
    42
}
```

### 3. 错误传播

```rust
use anyhow::Result;

async fn error_propagation() -> Result<()> {
    let data = fetch_critical_data().await?;
    let processed = process_data(data).await?;
    save_result(processed).await?;
    Ok(())
}

async fn fetch_critical_data() -> Result<String> {
    Ok("数据".to_string())
}

async fn process_data(data: String) -> Result<String> {
    Ok(data.to_uppercase())
}

async fn save_result(data: String) -> Result<()> {
    Ok(())
}
```

### 4. 资源管理

```rust
use tokio::io::AsyncWriteExt;

async fn resource_management() -> std::io::Result<()> {
    let mut file = tokio::fs::File::create("output.txt").await?;
    
    // 即使出错，Drop 也会确保资源清理
    file.write_all(b"Hello, async world!").await?;
    file.sync_all().await?;
    
    Ok(())
} // file 自动关闭
```

### 5. 避免过度嵌套

```rust
// ❌ 不好：深度嵌套
async fn nested_bad() {
    match fetch_user().await {
        Some(user) => {
            match fetch_posts(user.id).await {
                Some(posts) => {
                    for post in posts {
                        println!("{}", post);
                    }
                }
                None => println!("没有帖子"),
            }
        }
        None => println!("没有用户"),
    }
}

// ✅ 好：提前返回
async fn flat_good() {
    let user = match fetch_user().await {
        Some(u) => u,
        None => {
            println!("没有用户");
            return;
        }
    };
    
    let posts = match fetch_posts(user.id).await {
        Some(p) => p,
        None => {
            println!("没有帖子");
            return;
        }
    };
    
    for post in posts {
        println!("{}", post);
    }
}

#[derive(Debug)]
struct User {
    id: u32,
}

async fn fetch_user() -> Option<User> {
    Some(User { id: 1 })
}

async fn fetch_posts(user_id: u32) -> Option<Vec<String>> {
    Some(vec!["帖子1".to_string()])
}
```

---

## 性能优化

### 1. 批量操作

```rust
use futures::stream::{self, StreamExt};

async fn batch_processing() {
    let items = stream::iter(1..=100);
    
    items
        .chunks(10)  // 每次处理10个
        .for_each(|batch| async move {
            process_batch(batch).await;
        })
        .await;
}

async fn process_batch(batch: Vec<i32>) {
    println!("处理批次: {:?}", batch);
}
```

### 2. 预取与缓冲

```rust
use futures::stream::{self, StreamExt};

async fn prefetching() {
    let stream = stream::iter(1..=100)
        .map(|x| async move {
            expensive_operation(x).await
        })
        .buffered(10);  // 预取10个
    
    stream.for_each(|result| async move {
        println!("结果: {}", result);
    }).await;
}

async fn expensive_operation(x: i32) -> i32 {
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    x * 2
}
```

---

## 技术选型

| 场景 | 推荐方案 | 原因 |
|------|----------|------|
| **Web 服务** | Tokio | 生态完整，高性能 |
| **CLI 工具** | async-std / smol | API 简单，二进制小 |
| **嵌入式** | smol | 最小依赖 |
| **学习** | async-std | 类标准库 API |
| **高性能** | Tokio | 优化最好 |

---

## 参考资源

- [Futures Crate 文档](https://docs.rs/futures/)
- [Tokio 官方教程](https://tokio.rs/tokio/tutorial)
- [Async Book](https://rust-lang.github.io/async-book/)
- [async-std 文档](https://docs.rs/async-std/)
