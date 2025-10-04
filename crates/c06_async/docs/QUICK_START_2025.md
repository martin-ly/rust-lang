# Rust 异步编程快速入门 2025

## Quick Start Guide for Rust Async Programming

**适合人群**: Rust 初学者、异步编程新手  
**预计时间**: 30-60 分钟  
**前置知识**: 基础 Rust 语法

---

## 🚀 5 分钟上手

### 1. 你的第一个异步程序

创建 `hello_async.rs`:

```rust
// 使用 Tokio 运行时
#[tokio::main]
async fn main() {
    println!("Hello, async world!");
    
    // 异步等待 1 秒
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    
    println!("1 秒后...");
}
```

**运行**:

```bash
# 添加依赖
cargo add tokio --features full

# 运行
cargo run
```

**输出**:

```text
Hello, async world!
(等待 1 秒)
1 秒后...
```

### 2. 并发执行多个任务

```rust
#[tokio::main]
async fn main() {
    // 并发执行 3 个任务
    let (result1, result2, result3) = tokio::join!(
        task1(),
        task2(),
        task3(),
    );
    
    println!("结果: {}, {}, {}", result1, result2, result3);
}

async fn task1() -> i32 {
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    println!("Task 1 完成");
    42
}

async fn task2() -> i32 {
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    println!("Task 2 完成");
    100
}

async fn task3() -> i32 {
    tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;
    println!("Task 3 完成");
    200
}
```

---

## 📖 核心概念 (10 分钟)

### async/await 关键字

```rust
// async fn 返回一个 Future
async fn fetch_data() -> String {
    // await 等待 Future 完成
    let data = some_async_operation().await;
    data
}

// 等价于:
fn fetch_data() -> impl Future<Output = String> {
    async {
        let data = some_async_operation().await;
        data
    }
}
```

**关键点**:

- `async fn` 创建异步函数
- `.await` 等待 Future 完成
- `async` 块创建异步代码块
- 异步函数必须在异步上下文中调用

### Future trait

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// Future 的核心定义
pub trait Future {
    type Output;  // 完成时的返回值
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}

// Poll 表示 Future 的状态
pub enum Poll<T> {
    Ready(T),    // 完成，返回结果
    Pending,     // 未完成，稍后再试
}
```

**理解**:

- Future 是惰性的，不会自动执行
- 需要被 poll 才会推进
- 运行时负责 poll Future

---

## 🔧 常用模式 (20 分钟)

### 1. 生成任务 (Spawning Tasks)

```rust
use tokio::task;

#[tokio::main]
async fn main() {
    // 生成异步任务
    let handle = tokio::spawn(async {
        println!("异步任务执行中...");
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        42  // 返回值
    });
    
    // 等待任务完成
    let result = handle.await.unwrap();
    println!("任务结果: {}", result);
}
```

**要点**:

- `tokio::spawn` 生成独立任务
- 返回 `JoinHandle` 用于等待结果
- 任务在后台并发执行

### 2. Channel 通信

```rust
use tokio::sync::mpsc;

#[tokio::main]
async fn main() {
    // 创建通道 (容量 100)
    let (tx, mut rx) = mpsc::channel(100);
    
    // 发送者任务
    tokio::spawn(async move {
        for i in 0..5 {
            tx.send(i).await.unwrap();
            println!("发送: {}", i);
        }
    });
    
    // 接收者
    while let Some(msg) = rx.recv().await {
        println!("接收: {}", msg);
    }
}
```

**Channel 类型**:

- `mpsc`: 多生产者单消费者
- `oneshot`: 一次性通信
- `broadcast`: 广播
- `watch`: 状态监听

### 3. 超时控制

```rust
use tokio::time::{timeout, Duration};

#[tokio::main]
async fn main() {
    // 5 秒超时
    match timeout(Duration::from_secs(5), slow_operation()).await {
        Ok(result) => println!("成功: {:?}", result),
        Err(_) => println!("超时!"),
    }
}

async fn slow_operation() -> String {
    tokio::time::sleep(Duration::from_secs(10)).await;
    "完成".to_string()
}
```

### 4. 错误处理

```rust
use anyhow::{Context, Result};

#[tokio::main]
async fn main() -> Result<()> {
    let data = load_data().await?;
    process(data).await?;
    Ok(())
}

async fn load_data() -> Result<String> {
    tokio::fs::read_to_string("data.txt")
        .await
        .context("无法读取文件")
}

async fn process(data: String) -> Result<()> {
    // 处理数据
    Ok(())
}
```

### 5. 并发模式

```rust
use tokio;

#[tokio::main]
async fn main() {
    // 模式 1: 并发等待所有任务
    let (r1, r2, r3) = tokio::join!(task1(), task2(), task3());
    
    // 模式 2: 等待第一个完成
    tokio::select! {
        result = task1() => println!("Task 1 先完成: {}", result),
        result = task2() => println!("Task 2 先完成: {}", result),
    }
    
    // 模式 3: 批量执行
    let mut handles = vec![];
    for i in 0..10 {
        handles.push(tokio::spawn(async move {
            work(i).await
        }));
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
}
```

---

## 🎯 实战示例 (30 分钟)

### 示例 1: HTTP 客户端

```rust
use reqwest;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 发送 GET 请求
    let response = reqwest::get("https://api.github.com/repos/rust-lang/rust")
        .await?
        .text()
        .await?;
    
    println!("响应: {}", response);
    Ok(())
}
```

### 示例 2: TCP Echo 服务器

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("服务器监听 8080 端口");
    
    loop {
        let (socket, _) = listener.accept().await?;
        tokio::spawn(handle_client(socket));
    }
}

async fn handle_client(mut socket: TcpStream) {
    let mut buf = vec![0; 1024];
    
    loop {
        match socket.read(&mut buf).await {
            Ok(0) => break,  // 连接关闭
            Ok(n) => {
                // 回显数据
                socket.write_all(&buf[..n]).await.unwrap();
            }
            Err(_) => break,
        }
    }
}
```

### 示例 3: 并发爬虫

```rust
use reqwest;
use tokio;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let urls = vec![
        "https://www.rust-lang.org",
        "https://docs.rs",
        "https://crates.io",
    ];
    
    let mut handles = vec![];
    
    for url in urls {
        let handle = tokio::spawn(async move {
            match fetch(url).await {
                Ok(content) => println!("{}: {} bytes", url, content.len()),
                Err(e) => println!("{}: 错误 - {}", url, e),
            }
        });
        handles.push(handle);
    }
    
    // 等待所有任务完成
    for handle in handles {
        handle.await?;
    }
    
    Ok(())
}

async fn fetch(url: &str) -> Result<String, reqwest::Error> {
    reqwest::get(url).await?.text().await
}
```

---

## 💡 常见陷阱与解决方案

### 陷阱 1: 忘记 .await

```rust
// ❌ 错误: Future 不会执行
async fn wrong() {
    do_async_work();  // 没有 .await，不会执行!
}

// ✅ 正确
async fn correct() {
    do_async_work().await;  // 正确等待
}
```

### 陷阱 2: 阻塞运行时

```rust
// ❌ 错误: 阻塞整个运行时
async fn wrong() {
    std::thread::sleep(std::time::Duration::from_secs(1));  // 阻塞!
}

// ✅ 正确: 使用异步 sleep
async fn correct() {
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
}

// ✅ 正确: CPU 密集型任务使用 spawn_blocking
async fn correct_cpu_intensive() {
    tokio::task::spawn_blocking(|| {
        // CPU 密集型计算
        heavy_computation();
    }).await.unwrap();
}
```

### 陷阱 3: 不必要的 `Arc<Mutex<T>>`

```rust
// ❌ 可能过度: 对于异步场景
use std::sync::{Arc, Mutex};
let data = Arc::new(Mutex::new(vec![]));

// ✅ 更好: 使用异步 Mutex
use tokio::sync::Mutex;
let data = Arc::new(Mutex::new(vec![]));

// ✅ 或者使用 channel 通信
let (tx, rx) = mpsc::channel(100);
```

### 陷阱 4: 生命周期问题

```rust
// ❌ 错误: 借用不能跨越 .await
async fn wrong(data: &str) {
    let borrowed = data;
    some_async_op().await;
    println!("{}", borrowed);  // 可能错误
}

// ✅ 正确: 使用 owned 数据
async fn correct(data: String) {
    let owned = data;
    some_async_op().await;
    println!("{}", owned);  // OK
}
```

---

## 📚 学习路径

### 第 1 周: 基础

- ✅ 理解 async/await
- ✅ 使用 tokio::spawn
- ✅ Channel 通信
- ✅ 基础错误处理

**练习**: 实现简单的异步计算器

### 第 2 周: 进阶

- ✅ 超时与取消
- ✅ 并发模式 (join, select)
- ✅ 异步 I/O
- ✅ 同步原语 (Mutex, RwLock)

**练习**: 实现 TCP Echo 服务器

### 第 3 周: 深入

- ✅ Actor 模式
- ✅ Reactor 模式
- ✅ 设计模式 (重试、熔断)
- ✅ 性能优化

**练习**: 实现一个异步任务队列

### 第 4 周: 实战

- ✅ Web 服务开发
- ✅ 分布式系统
- ✅ 生产级架构
- ✅ 可观测性

**练习**: 构建完整的微服务

---

## 🔗 下一步

### 深入学习

1. 阅读 [异步编程超级综合指南 2025](./ASYNC_COMPREHENSIVE_GUIDE_2025.md)
2. 研究 [运行时深度对比](./ASYNC_RUNTIME_COMPARISON_2025.md)
3. 运行 [综合模式示例](../examples/comprehensive_async_patterns_2025.rs)

### 实践项目

- 构建异步 Web 服务器
- 实现分布式任务队列
- 开发实时通信系统
- 创建命令行工具

### 社区资源

- [Tokio 官方教程](https://tokio.rs/tokio/tutorial)
- [Async Book](https://rust-lang.github.io/async-book/)
- [Rust 异步编程](https://rust-lang.github.io/async-book/)

---

## ❓ 常见问题

### Q: 什么时候使用异步？

**A**:

- ✅ I/O 密集型任务 (网络、文件)
- ✅ 需要高并发
- ✅ 低延迟要求
- ❌ CPU 密集型 (使用线程)

### Q: Tokio vs Smol?

**A**:

- **Tokio**: 功能全面，生态丰富，适合生产环境
- **Smol**: 轻量级，适合嵌入式、CLI 工具

### Q: 如何调试异步代码?

**A**:

- 使用 `tokio-console` 可视化调试
- 添加 `tracing` 日志
- 使用 `println!` 或 `dbg!`

### Q: 性能如何优化?

**A**:

- 减少锁竞争
- 使用 `spawn_blocking` 处理阻塞操作
- 批量处理
- 使用有界 channel

---

**作者**: Rust Async Team  
**更新**: 2025-10-04  
**许可**: MIT
