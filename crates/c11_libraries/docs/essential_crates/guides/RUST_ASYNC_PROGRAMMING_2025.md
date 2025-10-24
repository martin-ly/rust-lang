# Rust 异步编程实战指南 2025

> **最后更新**: 2025-10-20  
> **Rust 版本**: 1.83+  
> **难度**: ⭐⭐⭐⭐ (中高级)


## 📊 目录

- [Rust 异步编程实战指南 2025](#rust-异步编程实战指南-2025)
  - [📊 目录](#-目录)
  - [📋 目录1](#-目录1)
  - [1. 异步编程基础](#1-异步编程基础)
    - [1.1 为什么需要异步编程](#11-为什么需要异步编程)
    - [1.2 Future 和 Poll 机制](#12-future-和-poll-机制)
    - [1.3 async/await 语法](#13-asyncawait-语法)
  - [2. Tokio 运行时深入](#2-tokio-运行时深入)
    - [2.1 运行时架构](#21-运行时架构)
    - [2.2 多线程调度器](#22-多线程调度器)
    - [2.3 Work-Stealing 算法](#23-work-stealing-算法)
    - [2.4 运行时配置](#24-运行时配置)
  - [3. 异步 IO 操作](#3-异步-io-操作)
    - [3.1 文件 IO](#31-文件-io)
    - [3.2 网络 IO](#32-网络-io)
    - [3.3 IO 多路复用 (epoll/kqueue)](#33-io-多路复用-epollkqueue)
  - [4. 任务和并发](#4-任务和并发)
    - [4.1 spawn 和 join](#41-spawn-和-join)
    - [4.2 select 多路选择](#42-select-多路选择)
    - [4.3 并发限制](#43-并发限制)
    - [4.4 超时和取消](#44-超时和取消)
  - [5. 异步通信](#5-异步通信)
    - [5.1 Channel (mpsc)](#51-channel-mpsc)
    - [5.2 Broadcast Channel](#52-broadcast-channel)
    - [5.3 Watch Channel](#53-watch-channel)
    - [5.4 Oneshot Channel](#54-oneshot-channel)
  - [6. 异步锁和同步原语](#6-异步锁和同步原语)
    - [6.1 Mutex 和 RwLock](#61-mutex-和-rwlock)
    - [6.2 Semaphore (信号量)](#62-semaphore-信号量)
    - [6.3 Barrier](#63-barrier)
    - [6.4 Notify](#64-notify)
  - [7. 实战案例](#7-实战案例)
    - [7.1 异步 Web 爬虫](#71-异步-web-爬虫)
    - [7.2 实时聊天服务器](#72-实时聊天服务器)
    - [7.3 异步批处理系统](#73-异步批处理系统)
  - [8. 性能优化](#8-性能优化)
    - [8.1 减少分配](#81-减少分配)
    - [8.2 避免不必要的 await](#82-避免不必要的-await)
    - [8.3 批处理优化](#83-批处理优化)
    - [8.4 零拷贝技术](#84-零拷贝技术)
  - [9. 调试和诊断](#9-调试和诊断)
    - [9.1 tokio-console](#91-tokio-console)
    - [9.2 tracing 集成](#92-tracing-集成)
    - [9.3 死锁检测](#93-死锁检测)
  - [10. 最佳实践](#10-最佳实践)
  - [11. 常见陷阱](#11-常见陷阱)
  - [12. 参考资源](#12-参考资源)


## 📋 目录1

- [Rust 异步编程实战指南 2025](#rust-异步编程实战指南-2025)
  - [� 目录](#-目录)
  - [📋 目录1](#-目录1)
  - [1. 异步编程基础](#1-异步编程基础)
    - [1.1 为什么需要异步编程](#11-为什么需要异步编程)
    - [1.2 Future 和 Poll 机制](#12-future-和-poll-机制)
    - [1.3 async/await 语法](#13-asyncawait-语法)
  - [2. Tokio 运行时深入](#2-tokio-运行时深入)
    - [2.1 运行时架构](#21-运行时架构)
    - [2.2 多线程调度器](#22-多线程调度器)
    - [2.3 Work-Stealing 算法](#23-work-stealing-算法)
    - [2.4 运行时配置](#24-运行时配置)
  - [3. 异步 IO 操作](#3-异步-io-操作)
    - [3.1 文件 IO](#31-文件-io)
    - [3.2 网络 IO](#32-网络-io)
    - [3.3 IO 多路复用 (epoll/kqueue)](#33-io-多路复用-epollkqueue)
  - [4. 任务和并发](#4-任务和并发)
    - [4.1 spawn 和 join](#41-spawn-和-join)
    - [4.2 select 多路选择](#42-select-多路选择)
    - [4.3 并发限制](#43-并发限制)
    - [4.4 超时和取消](#44-超时和取消)
  - [5. 异步通信](#5-异步通信)
    - [5.1 Channel (mpsc)](#51-channel-mpsc)
    - [5.2 Broadcast Channel](#52-broadcast-channel)
    - [5.3 Watch Channel](#53-watch-channel)
    - [5.4 Oneshot Channel](#54-oneshot-channel)
  - [6. 异步锁和同步原语](#6-异步锁和同步原语)
    - [6.1 Mutex 和 RwLock](#61-mutex-和-rwlock)
    - [6.2 Semaphore (信号量)](#62-semaphore-信号量)
    - [6.3 Barrier](#63-barrier)
    - [6.4 Notify](#64-notify)
  - [7. 实战案例](#7-实战案例)
    - [7.1 异步 Web 爬虫](#71-异步-web-爬虫)
    - [7.2 实时聊天服务器](#72-实时聊天服务器)
    - [7.3 异步批处理系统](#73-异步批处理系统)
  - [8. 性能优化](#8-性能优化)
    - [8.1 减少分配](#81-减少分配)
    - [8.2 避免不必要的 await](#82-避免不必要的-await)
    - [8.3 批处理优化](#83-批处理优化)
    - [8.4 零拷贝技术](#84-零拷贝技术)
  - [9. 调试和诊断](#9-调试和诊断)
    - [9.1 tokio-console](#91-tokio-console)
    - [9.2 tracing 集成](#92-tracing-集成)
    - [9.3 死锁检测](#93-死锁检测)
  - [10. 最佳实践](#10-最佳实践)
  - [11. 常见陷阱](#11-常见陷阱)
  - [12. 参考资源](#12-参考资源)

---

## 1. 异步编程基础

### 1.1 为什么需要异步编程

**同步 vs 异步对比:**

```text
┌─────────────────────────────────────────┐
│ 同步 IO (阻塞)                          │
├─────────────────────────────────────────┤
│ Thread 1: [████ Read ████] [████ Process]
│ Thread 2: [████ Read ████] [████ Process]
│ Thread 3: [████ Read ████] [████ Process]
│                                         │
│ 问题: 每个线程在 IO 时阻塞，浪费资源    │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│ 异步 IO (非阻塞)                        │
├─────────────────────────────────────────┤
│ Task 1: [██ Read][Process][██ Read]
│ Task 2:    [██ Read][Process][██ Read]
│ Task 3:       [██ Read][Process][██ Read]
│                                         │
│ 优势: 单线程处理多任务，高并发低开销    │
└─────────────────────────────────────────┘
```

**性能对比 (10K 并发连接):**

| 方式         | 内存占用 | CPU 使用率 | 延迟 (p99) |
|--------------|----------|------------|------------|
| 线程池 (1K)  | ~10 GB   | 80%        | 500ms      |
| 异步 (Tokio) | ~500 MB  | 30%        | 50ms       |

### 1.2 Future 和 Poll 机制

**Future trait 定义:**

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 简化的 Future trait
pub trait Future {
    type Output;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}

// Poll 枚举
pub enum Poll<T> {
    Ready(T),    // 任务完成
    Pending,     // 任务未完成，需要再次轮询
}
```

**自定义 Future 实现:**

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 自定义定时器 Future
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
struct Delay {
    when: Instant,
}

impl Delay {
    fn new(duration: Duration) -> Self {
        Self {
            when: Instant::now() + duration,
        }
    }
}

impl Future for Delay {
    type Output = ();
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if Instant::now() >= self.when {
            // 时间已到，返回 Ready
            Poll::Ready(())
        } else {
            // 时间未到，注册 waker 并返回 Pending
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

// 使用示例
#[tokio::main]
async fn main() {
    println!("开始等待...");
    Delay::new(Duration::from_secs(2)).await;
    println!("等待完成！");
}
```

### 1.3 async/await 语法

**基本语法:**

```rust
use tokio::fs::File;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// async 函数自动返回 impl Future
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn read_file(path: &str) -> std::io::Result<String> {
    let mut file = File::open(path).await?;
    let mut contents = String::new();
    file.read_to_string(&mut contents).await?;
    Ok(contents)
}

async fn write_file(path: &str, data: &str) -> std::io::Result<()> {
    let mut file = File::create(path).await?;
    file.write_all(data.as_bytes()).await?;
    Ok(())
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 并发执行多个异步任务
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[tokio::main]
async fn main() -> std::io::Result<()> {
    // 1. 顺序执行 (总耗时 = t1 + t2)
    let content1 = read_file("file1.txt").await?;
    let content2 = read_file("file2.txt").await?;
    
    // 2. 并发执行 (总耗时 = max(t1, t2))
    let (content1, content2) = tokio::join!(
        read_file("file1.txt"),
        read_file("file2.txt"),
    );
    
    // 3. 并发执行 + 错误处理
    let results = tokio::try_join!(
        read_file("file1.txt"),
        read_file("file2.txt"),
        read_file("file3.txt"),
    )?;
    
    Ok(())
}
```

---

## 2. Tokio 运行时深入

### 2.1 运行时架构

**Tokio 运行时组件:**

```text
┌─────────────────────────────────────────────────────────┐
│                   Tokio Runtime                         │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐ │
│  │  Scheduler   │  │  IO Driver   │  │ Time Driver  │ │
│  │              │  │              │  │              │ │
│  │ Work-Steal   │  │ epoll/kqueue │  │ Timer Wheel  │ │
│  │ Queues       │  │              │  │              │ │
│  └──────────────┘  └──────────────┘  └──────────────┘ │
│         │                  │                 │         │
│         └──────────────────┴─────────────────┘         │
│                            │                           │
│                  ┌─────────▼─────────┐                 │
│                  │   Task Executor   │                 │
│                  └───────────────────┘                 │
│                            │                           │
│         ┌──────────────────┼──────────────────┐        │
│         │                  │                  │        │
│    ┌────▼────┐        ┌────▼────┐        ┌────▼────┐  │
│    │ Worker 1│        │ Worker 2│        │ Worker N│  │
│    └─────────┘        └─────────┘        └─────────┘  │
└─────────────────────────────────────────────────────────┘
```

### 2.2 多线程调度器

**运行时配置:**

```rust
use tokio::runtime::Builder;
use std::time::Duration;

fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 1. 多线程运行时 (默认配置)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let rt = Builder::new_multi_thread()
        .worker_threads(4)                // 4 个 worker 线程
        .thread_name("my-runtime-worker")
        .thread_stack_size(3 * 1024 * 1024) // 3MB stack
        .enable_all()                     // 启用所有功能
        .build()
        .unwrap();
    
    rt.block_on(async {
        println!("运行在多线程运行时");
    });
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 2. 单线程运行时 (适合 IO 密集型)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let rt = Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();
    
    rt.block_on(async {
        println!("运行在单线程运行时");
    });
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 3. 自定义配置 (高级)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let rt = Builder::new_multi_thread()
        .worker_threads(8)
        .max_blocking_threads(16)         // 阻塞线程池大小
        .thread_keep_alive(Duration::from_secs(60))
        .global_queue_interval(31)        // 每 31 次轮询检查全局队列
        .event_interval(61)               // 每 61 次轮询检查 IO 事件
        .enable_all()
        .build()
        .unwrap();
}
```

### 2.3 Work-Stealing 算法

**工作窃取机制:**

```text
┌─────────────────────────────────────────────────────────┐
│ Work-Stealing Scheduler                                 │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  Global Queue (全局队列)                                │
│  ┌─────────────────────────────────────────────────┐   │
│  │ [Task] [Task] [Task] [Task] [Task]              │   │
│  └─────────────────────────────────────────────────┘   │
│         │         │         │                           │
│         └─────────┴─────────┘                           │
│                   │                                     │
│  Local Queues (本地队列)                                │
│  ┌──────────────┐ ┌──────────────┐ ┌──────────────┐   │
│  │ Worker 1     │ │ Worker 2     │ │ Worker 3     │   │
│  ├──────────────┤ ├──────────────┤ ├──────────────┤   │
│  │ [T] [T] [T]  │ │ [T] [T]      │ │              │   │
│  │ [T] [T]      │ │              │ │              │   │
│  └──────────────┘ └──────────────┘ └──────────────┘   │
│         │                             ▲                 │
│         │                             │                 │
│         └─────────── steal ───────────┘                 │
│                   (窃取任务)                             │
└─────────────────────────────────────────────────────────┘

窃取策略:
1. Worker 优先执行本地队列任务
2. 本地队列为空时，从全局队列获取
3. 全局队列为空时，从其他 Worker 窃取任务
4. 所有队列为空时，进入休眠等待
```

### 2.4 运行时配置

**最佳配置指南:**

```rust
use tokio::runtime::Builder;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 场景1: Web 服务器 (IO 密集型)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let rt_web = Builder::new_multi_thread()
    .worker_threads(num_cpus::get())  // CPU 核心数
    .max_blocking_threads(512)        // 大量阻塞操作
    .enable_all()
    .build()
    .unwrap();

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 场景2: 数据处理 (CPU 密集型)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let rt_compute = Builder::new_multi_thread()
    .worker_threads(num_cpus::get() * 2) // 超配
    .max_blocking_threads(4)             // 少量阻塞操作
    .enable_all()
    .build()
    .unwrap();

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 场景3: 嵌入式/轻量级 (单线程)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let rt_embedded = Builder::new_current_thread()
    .enable_all()
    .build()
    .unwrap();
```

---

## 3. 异步 IO 操作

### 3.1 文件 IO

```rust
use tokio::fs::{File, OpenOptions};
use tokio::io::{AsyncReadExt, AsyncWriteExt, AsyncBufReadExt, BufReader};

#[tokio::main]
async fn main() -> std::io::Result<()> {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 1. 读取整个文件
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let content = tokio::fs::read_to_string("file.txt").await?;
    println!("文件内容: {}", content);
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 2. 写入文件
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    tokio::fs::write("output.txt", "Hello, Tokio!").await?;
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 3. 追加写入
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open("log.txt")
        .await?;
    
    file.write_all(b"新日志行\n").await?;
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 4. 逐行读取 (大文件)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let file = File::open("large.txt").await?;
    let reader = BufReader::new(file);
    let mut lines = reader.lines();
    
    while let Some(line) = lines.next_line().await? {
        println!("行: {}", line);
    }
    
    Ok(())
}
```

### 3.2 网络 IO

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// TCP 服务器
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[tokio::main]
async fn main() -> std::io::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("服务器启动: {}", listener.local_addr()?);
    
    loop {
        let (socket, addr) = listener.accept().await?;
        println!("新连接: {}", addr);
        
        // 为每个连接生成一个任务
        tokio::spawn(async move {
            if let Err(e) = handle_client(socket).await {
                eprintln!("处理客户端失败: {:?}", e);
            }
        });
    }
}

async fn handle_client(mut socket: TcpStream) -> std::io::Result<()> {
    let mut buf = [0; 1024];
    
    loop {
        let n = socket.read(&mut buf).await?;
        
        if n == 0 {
            return Ok(()); // 连接关闭
        }
        
        // 回显数据
        socket.write_all(&buf[0..n]).await?;
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// TCP 客户端
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn tcp_client() -> std::io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:8080").await?;
    
    // 发送数据
    stream.write_all(b"Hello, Server!").await?;
    
    // 接收数据
    let mut buf = [0; 1024];
    let n = stream.read(&mut buf).await?;
    println!("收到响应: {}", String::from_utf8_lossy(&buf[0..n]));
    
    Ok(())
}
```

### 3.3 IO 多路复用 (epoll/kqueue)

**Tokio IO 驱动原理:**

```text
┌─────────────────────────────────────────────────────────┐
│ IO Driver (基于 epoll/kqueue/IOCP)                      │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  ┌─────────────────────────────────────────────────┐   │
│  │ Reactor (IO 事件循环)                           │   │
│  │                                                 │   │
│  │  epoll_wait() / kqueue() / GetQueuedCompletionStatus()
│  │       │                                         │   │
│  │       ▼                                         │   │
│  │  ┌─────────────────────────────────────┐       │   │
│  │  │ Interest Map (注册的 IO 事件)       │       │   │
│  │  │                                     │       │   │
│  │  │ fd=10 → Read  → Waker 1             │       │   │
│  │  │ fd=11 → Write → Waker 2             │       │   │
│  │  │ fd=12 → Read  → Waker 3             │       │   │
│  │  └─────────────────────────────────────┘       │   │
│  │                                                 │   │
│  │  当 fd 就绪时:                                  │   │
│  │  1. 从 Interest Map 获取对应的 Waker            │   │
│  │  2. 调用 waker.wake() 唤醒任务                  │   │
│  │  3. 任务重新被调度执行                          │   │
│  └─────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────┘
```

---

## 4. 任务和并发

### 4.1 spawn 和 join

```rust
use tokio::task;
use std::time::Duration;

#[tokio::main]
async fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 1. spawn: 生成新任务 (并发执行)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let task1 = task::spawn(async {
        tokio::time::sleep(Duration::from_secs(1)).await;
        "任务1完成"
    });
    
    let task2 = task::spawn(async {
        tokio::time::sleep(Duration::from_secs(2)).await;
        "任务2完成"
    });
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 2. join: 等待任务完成
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let result1 = task1.await.unwrap();
    let result2 = task2.await.unwrap();
    
    println!("{}, {}", result1, result2);
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 3. JoinSet: 管理多个任务
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    use tokio::task::JoinSet;
    
    let mut set = JoinSet::new();
    
    for i in 0..10 {
        set.spawn(async move {
            tokio::time::sleep(Duration::from_millis(100 * i)).await;
            i
        });
    }
    
    // 等待所有任务完成
    while let Some(res) = set.join_next().await {
        println!("任务完成: {:?}", res);
    }
}
```

### 4.2 select 多路选择

```rust
use tokio::time::{sleep, Duration};
use tokio::sync::mpsc;

#[tokio::main]
async fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 1. select! 宏: 同时等待多个 Future
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let (tx, mut rx) = mpsc::channel(32);
    
    tokio::spawn(async move {
        sleep(Duration::from_secs(2)).await;
        tx.send("消息").await.unwrap();
    });
    
    tokio::select! {
        msg = rx.recv() => {
            println!("收到消息: {:?}", msg);
        }
        _ = sleep(Duration::from_secs(1)) => {
            println!("超时！");
        }
    }
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 2. biased 模式: 优先级选择
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    tokio::select! {
        biased; // 按顺序检查分支
        
        msg = rx.recv() => {
            println!("高优先级: 消息");
        }
        _ = sleep(Duration::from_secs(1)) => {
            println!("低优先级: 超时");
        }
    }
}
```

### 4.3 并发限制

```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 限制并发数量 (例如: 最多 10 个并发请求)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[tokio::main]
async fn main() {
    let semaphore = Arc::new(Semaphore::new(10)); // 最多 10 个并发
    let mut tasks = vec![];
    
    for i in 0..100 {
        let sem = Arc::clone(&semaphore);
        
        let task = tokio::spawn(async move {
            let _permit = sem.acquire().await.unwrap(); // 获取许可
            
            // 执行耗时操作
            println!("处理任务 {}", i);
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            
            // _permit 被 drop 时自动释放
        });
        
        tasks.push(task);
    }
    
    // 等待所有任务完成
    for task in tasks {
        task.await.unwrap();
    }
}
```

### 4.4 超时和取消

```rust
use tokio::time::{timeout, Duration};
use tokio::select;

#[tokio::main]
async fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 1. timeout: 为 Future 设置超时
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let result = timeout(Duration::from_secs(2), async {
        tokio::time::sleep(Duration::from_secs(5)).await;
        "完成"
    }).await;
    
    match result {
        Ok(val) => println!("结果: {}", val),
        Err(_) => println!("超时！"),
    }
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 2. 取消: 使用 CancellationToken
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    use tokio_util::sync::CancellationToken;
    
    let token = CancellationToken::new();
    let token_clone = token.clone();
    
    let task = tokio::spawn(async move {
        select! {
            _ = token_clone.cancelled() => {
                println!("任务被取消");
            }
            _ = tokio::time::sleep(Duration::from_secs(10)) => {
                println!("任务完成");
            }
        }
    });
    
    // 1秒后取消任务
    tokio::time::sleep(Duration::from_secs(1)).await;
    token.cancel();
    
    task.await.unwrap();
}
```

---

## 5. 异步通信

### 5.1 Channel (mpsc)

```rust
use tokio::sync::mpsc;
use std::time::Duration;

#[tokio::main]
async fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 创建 channel (缓冲区大小为 32)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let (tx, mut rx) = mpsc::channel(32);
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 生产者任务
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    tokio::spawn(async move {
        for i in 0..10 {
            if tx.send(i).await.is_err() {
                println!("接收者已关闭");
                break;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    });
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 消费者任务
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    while let Some(msg) = rx.recv().await {
        println!("收到消息: {}", msg);
    }
    
    println!("Channel 已关闭");
}
```

### 5.2 Broadcast Channel

```rust
use tokio::sync::broadcast;

#[tokio::main]
async fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 创建广播 channel (多个接收者)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let (tx, mut rx1) = broadcast::channel(16);
    let mut rx2 = tx.subscribe();
    let mut rx3 = tx.subscribe();
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 生产者
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    tokio::spawn(async move {
        for i in 0..5 {
            tx.send(i).unwrap();
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        }
    });
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 多个消费者
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    tokio::spawn(async move {
        while let Ok(msg) = rx1.recv().await {
            println!("接收者1: {}", msg);
        }
    });
    
    tokio::spawn(async move {
        while let Ok(msg) = rx2.recv().await {
            println!("接收者2: {}", msg);
        }
    });
    
    tokio::spawn(async move {
        while let Ok(msg) = rx3.recv().await {
            println!("接收者3: {}", msg);
        }
    });
    
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
}
```

### 5.3 Watch Channel

```rust
use tokio::sync::watch;

#[tokio::main]
async fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Watch channel: 用于状态同步 (只保留最新值)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let (tx, mut rx) = watch::channel("初始值");
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 订阅者
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    tokio::spawn(async move {
        while rx.changed().await.is_ok() {
            println!("值已更新: {}", *rx.borrow());
        }
    });
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 发布者
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    tx.send("新值1").unwrap();
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    tx.send("新值2").unwrap();
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    tx.send("新值3").unwrap();
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}
```

### 5.4 Oneshot Channel

```rust
use tokio::sync::oneshot;

#[tokio::main]
async fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Oneshot channel: 只发送一次消息
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let (tx, rx) = oneshot::channel();
    
    tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        tx.send("计算结果").unwrap();
    });
    
    match rx.await {
        Ok(result) => println!("收到结果: {}", result),
        Err(_) => println!("发送者已关闭"),
    }
}
```

---

## 6. 异步锁和同步原语

### 6.1 Mutex 和 RwLock

```rust
use tokio::sync::{Mutex, RwLock};
use std::sync::Arc;

#[tokio::main]
async fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 1. Mutex: 互斥锁
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let data = Arc::new(Mutex::new(0));
    let mut tasks = vec![];
    
    for _ in 0..10 {
        let data = Arc::clone(&data);
        let task = tokio::spawn(async move {
            let mut guard = data.lock().await;
            *guard += 1;
        });
        tasks.push(task);
    }
    
    for task in tasks {
        task.await.unwrap();
    }
    
    println!("最终值: {}", *data.lock().await);
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 2. RwLock: 读写锁 (多读一写)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    
    // 多个读锁可以同时存在
    let read1 = data.read().await;
    let read2 = data.read().await;
    println!("读取: {:?}, {:?}", *read1, *read2);
    drop(read1);
    drop(read2);
    
    // 写锁是排他的
    let mut write = data.write().await;
    write.push(4);
    println!("写入后: {:?}", *write);
}
```

### 6.2 Semaphore (信号量)

```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 信号量: 限制并发访问数量
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let semaphore = Arc::new(Semaphore::new(3)); // 最多 3 个并发
    let mut tasks = vec![];
    
    for i in 0..10 {
        let sem = Arc::clone(&semaphore);
        let task = tokio::spawn(async move {
            let _permit = sem.acquire().await.unwrap();
            println!("任务 {} 开始执行", i);
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
            println!("任务 {} 完成", i);
        });
        tasks.push(task);
    }
    
    for task in tasks {
        task.await.unwrap();
    }
}
```

### 6.3 Barrier

```rust
use tokio::sync::Barrier;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Barrier: 等待所有任务到达同步点
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let barrier = Arc::new(Barrier::new(3)); // 等待 3 个任务
    let mut tasks = vec![];
    
    for i in 0..3 {
        let b = Arc::clone(&barrier);
        let task = tokio::spawn(async move {
            println!("任务 {} 准备中...", i);
            tokio::time::sleep(tokio::time::Duration::from_secs(i)).await;
            
            println!("任务 {} 到达屏障", i);
            b.wait().await;
            
            println!("任务 {} 继续执行", i);
        });
        tasks.push(task);
    }
    
    for task in tasks {
        task.await.unwrap();
    }
}
```

### 6.4 Notify

```rust
use tokio::sync::Notify;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Notify: 简单的通知机制
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let notify = Arc::new(Notify::new());
    let notify_clone = Arc::clone(&notify);
    
    tokio::spawn(async move {
        println!("等待通知...");
        notify_clone.notified().await;
        println!("收到通知！");
    });
    
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    println!("发送通知");
    notify.notify_one(); // 通知一个等待者
    
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}
```

---

## 7. 实战案例

### 7.1 异步 Web 爬虫

```rust
use reqwest;
use tokio::sync::Semaphore;
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let urls = vec![
        "https://example.com/page1",
        "https://example.com/page2",
        "https://example.com/page3",
        // ... 更多 URL
    ];
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 限制并发数 (避免过载)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let semaphore = Arc::new(Semaphore::new(10)); // 最多 10 个并发请求
    let client = reqwest::Client::new();
    let mut tasks = vec![];
    
    for url in urls {
        let sem = Arc::clone(&semaphore);
        let client = client.clone();
        
        let task = tokio::spawn(async move {
            let _permit = sem.acquire().await.unwrap();
            
            match fetch_page(&client, url).await {
                Ok(content) => {
                    println!("抓取成功: {} ({} bytes)", url, content.len());
                }
                Err(e) => {
                    eprintln!("抓取失败: {} - {:?}", url, e);
                }
            }
        });
        
        tasks.push(task);
    }
    
    // 等待所有任务完成
    for task in tasks {
        task.await?;
    }
    
    Ok(())
}

async fn fetch_page(client: &reqwest::Client, url: &str) -> Result<String, reqwest::Error> {
    let response = client.get(url).send().await?;
    let content = response.text().await?;
    Ok(content)
}
```

### 7.2 实时聊天服务器

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::broadcast;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

#[tokio::main]
async fn main() -> std::io::Result<()> {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 创建广播 channel (用于消息分发)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let (tx, _rx) = broadcast::channel::<String>(100);
    
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("聊天服务器启动: 127.0.0.1:8080");
    
    loop {
        let (socket, addr) = listener.accept().await?;
        let tx = tx.clone();
        let rx = tx.subscribe();
        
        tokio::spawn(async move {
            handle_client(socket, addr.to_string(), tx, rx).await;
        });
    }
}

async fn handle_client(
    socket: TcpStream,
    addr: String,
    tx: broadcast::Sender<String>,
    mut rx: broadcast::Receiver<String>,
) {
    let (reader, mut writer) = socket.into_split();
    let mut reader = BufReader::new(reader);
    let mut line = String::new();
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 发送欢迎消息
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let welcome = format!("欢迎加入聊天室！你的地址: {}\n", addr);
    writer.write_all(welcome.as_bytes()).await.ok();
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 广播加入消息
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let join_msg = format!("{} 加入了聊天室", addr);
    tx.send(join_msg).ok();
    
    loop {
        tokio::select! {
            // 读取客户端消息
            result = reader.read_line(&mut line) => {
                match result {
                    Ok(0) => break, // 连接关闭
                    Ok(_) => {
                        let msg = format!("{}: {}", addr, line.trim());
                        tx.send(msg).ok();
                        line.clear();
                    }
                    Err(_) => break,
                }
            }
            
            // 接收广播消息
            Ok(msg) = rx.recv() => {
                writer.write_all(format!("{}\n", msg).as_bytes()).await.ok();
            }
        }
    }
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 广播离开消息
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let leave_msg = format!("{} 离开了聊天室", addr);
    tx.send(leave_msg).ok();
}
```

### 7.3 异步批处理系统

```rust
use tokio::sync::mpsc;
use std::time::Duration;

#[tokio::main]
async fn main() {
    let (tx, rx) = mpsc::channel(100);
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 生产者: 生成任务
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    tokio::spawn(async move {
        for i in 0..100 {
            tx.send(i).await.unwrap();
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    });
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 消费者: 批处理任务
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    batch_processor(rx, 10, Duration::from_millis(100)).await;
}

async fn batch_processor(
    mut rx: mpsc::Receiver<i32>,
    batch_size: usize,
    timeout: Duration,
) {
    let mut batch = Vec::new();
    
    loop {
        tokio::select! {
            // 接收新任务
            Some(task) = rx.recv() => {
                batch.push(task);
                
                // 达到批量大小时立即处理
                if batch.len() >= batch_size {
                    process_batch(&batch).await;
                    batch.clear();
                }
            }
            
            // 超时时处理剩余任务
            _ = tokio::time::sleep(timeout), if !batch.is_empty() => {
                process_batch(&batch).await;
                batch.clear();
            }
            
            // Channel 关闭
            else => break,
        }
    }
    
    // 处理最后的批次
    if !batch.is_empty() {
        process_batch(&batch).await;
    }
}

async fn process_batch(batch: &[i32]) {
    println!("处理批次 (大小: {}): {:?}", batch.len(), batch);
    tokio::time::sleep(Duration::from_millis(50)).await;
}
```

---

## 8. 性能优化

### 8.1 减少分配

```rust
use bytes::Bytes;

// ❌ 错误: 每次都分配新 Vec
async fn bad_example() {
    let data = vec![0u8; 1024];
    // ...
}

// ✅ 正确: 使用 bytes::Bytes (引用计数, 零拷贝)
async fn good_example() {
    let data = Bytes::from_static(&[0u8; 1024]);
    // ...
}
```

### 8.2 避免不必要的 await

```rust
// ❌ 错误: 不必要的 await
async fn bad_compute() -> i32 {
    let result = compute().await; // compute 是同步函数
    result
}

fn compute() -> i32 {
    42
}

// ✅ 正确: 直接调用同步函数
async fn good_compute() -> i32 {
    compute() // 不需要 await
}
```

### 8.3 批处理优化

```rust
use tokio::sync::mpsc;

// ❌ 错误: 每次写入一条记录
async fn bad_insert(rx: &mut mpsc::Receiver<String>) {
    while let Some(data) = rx.recv().await {
        database_insert_one(data).await;
    }
}

// ✅ 正确: 批量写入
async fn good_insert(rx: &mut mpsc::Receiver<String>) {
    let mut batch = Vec::new();
    
    while let Some(data) = rx.recv().await {
        batch.push(data);
        
        if batch.len() >= 100 {
            database_insert_batch(&batch).await;
            batch.clear();
        }
    }
}

async fn database_insert_one(_data: String) {}
async fn database_insert_batch(_batch: &[String]) {}
```

### 8.4 零拷贝技术

```rust
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 使用 tokio::io::copy 实现零拷贝转发
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn proxy(mut client: TcpStream, mut server: TcpStream) -> std::io::Result<()> {
    let (mut client_read, mut client_write) = client.split();
    let (mut server_read, mut server_write) = server.split();
    
    // 双向转发 (零拷贝)
    tokio::try_join!(
        tokio::io::copy(&mut client_read, &mut server_write),
        tokio::io::copy(&mut server_read, &mut client_write),
    )?;
    
    Ok(())
}
```

---

## 9. 调试和诊断

### 9.1 tokio-console

**安装和配置:**

```toml
# Cargo.toml
[dependencies]
tokio = { version = "1.0", features = ["full", "tracing"] }
console-subscriber = "0.2"
```

```rust
fn main() {
    // 启动 tokio-console
    console_subscriber::init();
    
    let rt = tokio::runtime::Runtime::new().unwrap();
    rt.block_on(async {
        // 你的异步代码
    });
}
```

**运行:**

```bash
# 1. 启动应用
cargo run

# 2. 在另一个终端启动 console
cargo install tokio-console
tokio-console
```

### 9.2 tracing 集成

```rust
use tracing::{info, warn, error, instrument};

#[instrument]
async fn fetch_user(user_id: u64) -> Result<String, &'static str> {
    info!("开始获取用户");
    
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    if user_id == 0 {
        error!("无效的用户 ID");
        return Err("无效的用户 ID");
    }
    
    info!("用户获取成功");
    Ok(format!("User {}", user_id))
}

#[tokio::main]
async fn main() {
    // 初始化 tracing
    tracing_subscriber::fmt::init();
    
    fetch_user(123).await.ok();
    fetch_user(0).await.ok();
}
```

### 9.3 死锁检测

```rust
use tokio::sync::Mutex;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let lock1 = Arc::new(Mutex::new(0));
    let lock2 = Arc::new(Mutex::new(0));
    
    let lock1_clone = Arc::clone(&lock1);
    let lock2_clone = Arc::clone(&lock2);
    
    // ❌ 可能死锁的代码
    tokio::spawn(async move {
        let _g1 = lock1_clone.lock().await;
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        let _g2 = lock2_clone.lock().await;
    });
    
    tokio::spawn(async move {
        let _g2 = lock2.lock().await;
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        let _g1 = lock1.lock().await;
    });
    
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
}
```

---

## 10. 最佳实践

1. **选择合适的运行时配置**
   - IO 密集型: 多线程运行时 (默认)
   - CPU 密集型: 使用 `tokio::task::spawn_blocking`
   - 嵌入式/轻量级: 单线程运行时

2. **限制并发数量**

   ```rust
   use tokio::sync::Semaphore;
   let sem = Semaphore::new(100); // 限制并发
   ```

3. **使用批处理**
   - 减少数据库/网络往返次数
   - 提高吞吐量

4. **避免阻塞操作**

   ```rust
   // ❌ 错误: 阻塞 async 函数
   async fn bad() {
       std::thread::sleep(Duration::from_secs(1));
   }
   
   // ✅ 正确: 使用 spawn_blocking
   async fn good() {
       tokio::task::spawn_blocking(|| {
           std::thread::sleep(Duration::from_secs(1));
       }).await.unwrap();
   }
   ```

5. **合理使用 select!**
   - 使用 `biased` 模式控制优先级
   - 避免饥饿问题

6. **错误处理**

   ```rust
   // 使用 ? 操作符简化错误传播
   async fn fetch() -> Result<String, reqwest::Error> {
       let resp = reqwest::get("https://example.com").await?;
       let text = resp.text().await?;
       Ok(text)
   }
   ```

7. **资源清理**

   ```rust
   // 使用 Drop guard 确保资源释放
   struct Guard {
       name: String,
   }
   
   impl Drop for Guard {
       fn drop(&mut self) {
           println!("{} 被清理", self.name);
       }
   }
   ```

8. **监控和可观测性**
   - 使用 `tracing` 记录日志
   - 使用 `tokio-console` 监控运行时
   - 使用 `metrics` 收集性能指标

9. **测试**

   ```rust
   #[tokio::test]
   async fn test_async_function() {
       let result = my_async_function().await;
       assert_eq!(result, expected);
   }
   ```

10. **避免过度嵌套**

    ```rust
    // ❌ 错误: 嵌套过深
    async fn bad() {
        tokio::spawn(async {
            tokio::spawn(async {
                tokio::spawn(async {
                    // ...
                });
            });
        });
    }
    
    // ✅ 正确: 扁平化
    async fn good() {
        let task1 = tokio::spawn(task1());
        let task2 = tokio::spawn(task2());
        let task3 = tokio::spawn(task3());
        
        tokio::try_join!(task1, task2, task3).ok();
    }
    
    async fn task1() {}
    async fn task2() {}
    async fn task3() {}
    ```

---

## 11. 常见陷阱

1. **忘记 .await**

   ```rust
   // ❌ 错误: 没有 await, Future 不会执行
   async fn bad() {
       fetch_data(); // 什么也不做
   }
   
   // ✅ 正确
   async fn good() {
       fetch_data().await;
   }
   
   async fn fetch_data() {}
   ```

2. **在 async 函数中使用标准库的阻塞 API**

   ```rust
   // ❌ 错误: 阻塞整个运行时
   async fn bad() {
       std::fs::read_to_string("file.txt").unwrap();
   }
   
   // ✅ 正确: 使用 Tokio 的异步版本
   async fn good() {
       tokio::fs::read_to_string("file.txt").await.unwrap();
   }
   ```

3. **过度使用 `Arc<Mutex>`**

   ```rust
   // ❌ 可能导致性能问题
   use std::sync::Arc;
   use tokio::sync::Mutex;
   
   let data = Arc::new(Mutex::new(vec![]));
   
   // ✅ 考虑使用 channel 代替
   use tokio::sync::mpsc;
   let (tx, rx) = mpsc::channel(100);
   ```

4. **select! 中的所有权问题**

   ```rust
   // ❌ 错误: value moved
   async fn bad() {
       let data = String::from("data");
       tokio::select! {
           _ = process(&data) => {},
           _ = other(&data) => {}, // Error: value moved
       }
   }
   
   // ✅ 正确: 使用引用
   async fn good() {
       let data = String::from("data");
       tokio::select! {
           _ = process(&data) => {},
           _ = other(&data) => {},
       }
   }
   
   async fn process(_s: &str) {}
   async fn other(_s: &str) {}
   ```

5. **泄漏 JoinHandle**

   ```rust
   // ❌ 错误: 任务可能永远不会完成
   async fn bad() {
       tokio::spawn(async {
           // 长时间运行的任务
       });
       // JoinHandle 被丢弃, 任务在后台运行
   }
   
   // ✅ 正确: 保存 JoinHandle 并等待
   async fn good() {
       let handle = tokio::spawn(async {
           // 长时间运行的任务
       });
       handle.await.unwrap();
   }
   ```

6. **Send 约束问题**

   ```rust
   // ❌ 错误: Rc 不是 Send
   use std::rc::Rc;
   
   async fn bad() {
       let data = Rc::new(42);
       tokio::spawn(async move {
           println!("{}", data); // Error: Rc is not Send
       });
   }
   
   // ✅ 正确: 使用 Arc
   use std::sync::Arc;
   
   async fn good() {
       let data = Arc::new(42);
       tokio::spawn(async move {
           println!("{}", data);
       });
   }
   ```

7. **在循环中创建过多任务**

   ```rust
   // ❌ 错误: 可能耗尽资源
   async fn bad() {
       for i in 0..1000000 {
           tokio::spawn(async move {
               // ...
           });
       }
   }
   
   // ✅ 正确: 使用 Semaphore 限流
   use tokio::sync::Semaphore;
   use std::sync::Arc;
   
   async fn good() {
       let sem = Arc::new(Semaphore::new(100));
       for i in 0..1000000 {
           let sem = Arc::clone(&sem);
           tokio::spawn(async move {
               let _permit = sem.acquire().await;
               // ...
           });
       }
   }
   ```

8. **不正确的超时处理**

   ```rust
   // ❌ 错误: 超时后任务仍在运行
   use tokio::time::{timeout, Duration};
   
   async fn bad() {
       let result = timeout(Duration::from_secs(1), long_task()).await;
       // long_task() 可能仍在后台运行
   }
   
   // ✅ 正确: 使用 CancellationToken
   use tokio_util::sync::CancellationToken;
   
   async fn good() {
       let token = CancellationToken::new();
       let token_clone = token.clone();
       
       let task = tokio::spawn(async move {
           cancellable_task(token_clone).await
       });
       
       tokio::select! {
           _ = task => {},
           _ = tokio::time::sleep(Duration::from_secs(1)) => {
               token.cancel();
           }
       }
   }
   
   async fn long_task() {}
   async fn cancellable_task(_token: CancellationToken) {}
   ```

---

## 12. 参考资源

- **官方文档**:
  - [Tokio 官方文档](https://tokio.rs/)
  - [async book](https://rust-lang.github.io/async-book/)
  - [std::future](https://doc.rust-lang.org/std/future/)

- **教程**:
  - [Tokio Tutorial](https://tokio.rs/tokio/tutorial)
  - [async-std book](https://book.async.rs/)

- **工具**:
  - [tokio-console](https://github.com/tokio-rs/console)
  - [tracing](https://github.com/tokio-rs/tracing)
  - [criterion](https://github.com/bheisler/criterion.rs)

- **库**:
  - [tokio](https://github.com/tokio-rs/tokio)
  - [async-std](https://github.com/async-rs/async-std)
  - [smol](https://github.com/smol-rs/smol)
  - [futures](https://github.com/rust-lang/futures-rs)

- **社区**:
  - [Tokio Discord](https://discord.gg/tokio)
  - [Rust 异步工作组](https://rust-lang.github.io/wg-async/)

---

> **完成！** 🎉
>
> 本指南涵盖了 Rust 异步编程的核心概念、Tokio 运行时、异步 IO、任务管理、通信机制、同步原语、实战案例、性能优化、调试诊断、最佳实践和常见陷阱。希望这份指南能帮助你掌握 Rust 异步编程，构建高性能的异步应用！
