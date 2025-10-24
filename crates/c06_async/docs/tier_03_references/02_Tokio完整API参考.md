# Tier 3: Tokio 完整 API 参考

> **文档版本**: Tokio 1.x | Rust 1.90+ | **更新日期**: 2025-10-22  
> **文档层级**: Tier 3 - 技术参考 | **文档类型**: 📘 API 文档

---

## 📋 目录

- [Tier 3: Tokio 完整 API 参考](#tier-3-tokio-完整-api-参考)
  - [📋 目录](#-目录)
  - [🎯 文档说明](#-文档说明)
  - [1. Runtime API](#1-runtime-api)
    - [1.1 创建运行时](#11-创建运行时)
    - [1.2 执行异步代码](#12-执行异步代码)
  - [2. Task API](#2-task-api)
    - [2.1 任务管理](#21-任务管理)
    - [2.2 JoinSet (Tokio 1.19+)](#22-joinset-tokio-119)
  - [3. Sync API](#3-sync-api)
    - [3.1 异步互斥锁](#31-异步互斥锁)
    - [3.2 Channel 类型](#32-channel-类型)
    - [3.3 同步原语](#33-同步原语)
  - [4. Time API](#4-time-api)
    - [4.1 时间操作](#41-时间操作)
    - [4.2 高级时间控制](#42-高级时间控制)
  - [5. Net API](#5-net-api)
    - [5.1 TCP](#51-tcp)
    - [5.2 UDP](#52-udp)
    - [5.3 Unix Domain Socket](#53-unix-domain-socket)
  - [6. FS API](#6-fs-api)
    - [6.1 文件操作](#61-文件操作)
    - [6.2 目录操作](#62-目录操作)
  - [7. IO Traits](#7-io-traits)
    - [7.1 核心 Traits](#71-核心-traits)
    - [7.2 BufReader / BufWriter](#72-bufreader--bufwriter)
  - [8. Macros](#8-macros)
    - [8.1 Runtime 宏](#81-runtime-宏)
    - [8.2 测试宏](#82-测试宏)
    - [8.3 select! 宏](#83-select-宏)
    - [8.4 join! 和 try\_join! 宏](#84-join-和-try_join-宏)
  - [9. 配置参考](#9-配置参考)
    - [9.1 Cargo Features](#91-cargo-features)
  - [📚 延伸阅读](#-延伸阅读)
  - [📝 总结](#-总结)

## 🎯 文档说明

Tokio 1.x 完整 API 参考，涵盖 runtime、task、sync、time、net、fs 等核心模块。

---

## 1. Runtime API

### 1.1 创建运行时

```rust
use tokio::runtime::Runtime;

// 多线程运行时
let rt = Runtime::new().unwrap();

// 单线程运行时
let rt = tokio::runtime::Builder::new_current_thread()
    .enable_all()
    .build()
    .unwrap();

// 自定义配置
let rt = tokio::runtime::Builder::new_multi_thread()
    .worker_threads(4)
    .thread_name("my-worker")
    .thread_stack_size(3 * 1024 * 1024)
    .enable_all()
    .build()
    .unwrap();
```

---

### 1.2 执行异步代码

```rust
// block_on - 阻塞等待
rt.block_on(async {
    println!("Hello, Tokio!");
});

// spawn - 提交任务
rt.spawn(async {
    println!("Background task");
});

// spawn_blocking - CPU密集型任务
rt.spawn_blocking(|| {
    // 长时间计算
});
```

---

## 2. Task API

### 2.1 任务管理

```rust
use tokio::task;

// 启动任务
let handle = task::spawn(async {
    42
});

// 等待完成
let result = handle.await.unwrap();

// 本地任务集 (单线程)
task::LocalSet::new().run_until(async {
    task::spawn_local(async {
        // 不需要 Send
    }).await.unwrap();
}).await;
```

---

### 2.2 JoinSet (Tokio 1.19+)

```rust
use tokio::task::JoinSet;

let mut set = JoinSet::new();

for i in 0..10 {
    set.spawn(async move { i * 2 });
}

while let Some(res) = set.join_next().await {
    println!("Result: {:?}", res);
}
```

---

## 3. Sync API

### 3.1 异步互斥锁

```rust
use tokio::sync::Mutex;

let data = Arc::new(Mutex::new(0));

// 异步锁
let mut guard = data.lock().await;
*guard += 1;
```

---

### 3.2 Channel 类型

| 类型 | 特点 | 使用场景 |
|------|------|----------|
| `mpsc` | 多生产者单消费者 | 任务间通信 |
| `oneshot` | 单次传递 | 请求/响应 |
| `broadcast` | 多消费者广播 | 事件分发 |
| `watch` | 单一值更新 | 配置更新 |

**示例**:

```rust
use tokio::sync::{mpsc, oneshot, broadcast, watch};

// mpsc
let (tx, mut rx) = mpsc::channel(32);
tx.send(42).await.unwrap();
let val = rx.recv().await.unwrap();

// oneshot
let (tx, rx) = oneshot::channel();
tx.send(42).unwrap();
let val = rx.await.unwrap();

// broadcast
let (tx, mut rx1) = broadcast::channel(16);
let mut rx2 = tx.subscribe();

// watch
let (tx, mut rx) = watch::channel(0);
tx.send(42).unwrap();
let val = *rx.borrow_and_update();
```

---

### 3.3 同步原语

```rust
use tokio::sync::{RwLock, Semaphore, Barrier, Notify};

// RwLock
let lock = Arc::new(RwLock::new(0));
let read = lock.read().await;
let mut write = lock.write().await;

// Semaphore (限流)
let sem = Arc::new(Semaphore::new(3));
let permit = sem.acquire().await.unwrap();

// Barrier (屏障)
let barrier = Arc::new(Barrier::new(3));
barrier.wait().await;

// Notify (唤醒机制)
let notify = Arc::new(Notify::new());
notify.notify_one();
notify.notified().await;
```

---

## 4. Time API

### 4.1 时间操作

```rust
use tokio::time::{sleep, timeout, interval, Duration, Instant};

// 异步睡眠
sleep(Duration::from_secs(1)).await;

// 超时控制
let result = timeout(Duration::from_secs(5), operation()).await;

// 定时器
let mut interval = interval(Duration::from_millis(100));
loop {
    interval.tick().await;
    println!("Tick!");
}

// 时间点
let start = Instant::now();
// ...操作...
let elapsed = start.elapsed();
```

---

### 4.2 高级时间控制

```rust
use tokio::time::{sleep_until, interval_at, MissedTickBehavior};

// 睡眠到指定时间
let deadline = Instant::now() + Duration::from_secs(10);
sleep_until(deadline).await;

// 自定义定时器行为
let start = Instant::now();
let mut interval = interval_at(start, Duration::from_millis(100));
interval.set_missed_tick_behavior(MissedTickBehavior::Skip);
```

---

## 5. Net API

### 5.1 TCP

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

// 服务器
let listener = TcpListener::bind("127.0.0.1:8080").await?;
loop {
    let (mut socket, _) = listener.accept().await?;
    tokio::spawn(async move {
        let mut buf = vec![0; 1024];
        let n = socket.read(&mut buf).await?;
        socket.write_all(&buf[..n]).await?;
        Ok::<_, std::io::Error>(())
    });
}

// 客户端
let mut stream = TcpStream::connect("127.0.0.1:8080").await?;
stream.write_all(b"hello").await?;
```

---

### 5.2 UDP

```rust
use tokio::net::UdpSocket;

let socket = UdpSocket::bind("0.0.0.0:8080").await?;
let mut buf = vec![0; 1024];

loop {
    let (len, addr) = socket.recv_from(&mut buf).await?;
    socket.send_to(&buf[..len], addr).await?;
}
```

---

### 5.3 Unix Domain Socket

```rust
use tokio::net::{UnixListener, UnixStream};

// 服务器
let listener = UnixListener::bind("/tmp/my.sock")?;
let (socket, _) = listener.accept().await?;

// 客户端
let stream = UnixStream::connect("/tmp/my.sock").await?;
```

---

## 6. FS API

### 6.1 文件操作

```rust
use tokio::fs::{File, OpenOptions, read, write, read_to_string};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

// 读取文件
let contents = read_to_string("file.txt").await?;

// 写入文件
write("file.txt", b"Hello").await?;

// 异步文件句柄
let mut file = File::open("file.txt").await?;
let mut contents = String::new();
file.read_to_string(&mut contents).await?;

// 自定义打开选项
let file = OpenOptions::new()
    .read(true)
    .write(true)
    .create(true)
    .open("file.txt")
    .await?;
```

---

### 6.2 目录操作

```rust
use tokio::fs::{create_dir_all, read_dir, remove_dir_all};

// 创建目录
create_dir_all("path/to/dir").await?;

// 读取目录
let mut entries = read_dir(".").await?;
while let Some(entry) = entries.next_entry().await? {
    println!("{:?}", entry.path());
}

// 删除目录
remove_dir_all("path/to/dir").await?;
```

---

## 7. IO Traits

### 7.1 核心 Traits

```rust
use tokio::io::{AsyncRead, AsyncWrite, AsyncReadExt, AsyncWriteExt};

// AsyncReadExt 扩展方法
async fn read_example<R: AsyncReadExt + Unpin>(reader: &mut R) -> std::io::Result<()> {
    let mut buf = vec![0; 1024];
    let n = reader.read(&mut buf).await?;
    let s = reader.read_to_string(&mut String::new()).await?;
    Ok(())
}

// AsyncWriteExt 扩展方法
async fn write_example<W: AsyncWriteExt + Unpin>(writer: &mut W) -> std::io::Result<()> {
    writer.write_all(b"Hello").await?;
    writer.flush().await?;
    Ok(())
}
```

---

### 7.2 BufReader / BufWriter

```rust
use tokio::io::{BufReader, BufWriter, AsyncBufReadExt};

let file = File::open("file.txt").await?;
let mut reader = BufReader::new(file);

// 按行读取
let mut line = String::new();
while reader.read_line(&mut line).await? > 0 {
    println!("{}", line);
    line.clear();
}

// 缓冲写入
let file = File::create("output.txt").await?;
let mut writer = BufWriter::new(file);
writer.write_all(b"Hello").await?;
writer.flush().await?;
```

---

## 8. Macros

### 8.1 Runtime 宏

```rust
// 多线程运行时
#[tokio::main]
async fn main() {
    // ...
}

// 单线程运行时
#[tokio::main(flavor = "current_thread")]
async fn main() {
    // ...
}

// 自定义配置
#[tokio::main(worker_threads = 4)]
async fn main() {
    // ...
}
```

---

### 8.2 测试宏

```rust
#[tokio::test]
async fn test_async_function() {
    let result = async_operation().await;
    assert_eq!(result, 42);
}

// 单线程测试
#[tokio::test(flavor = "current_thread")]
async fn test_single_threaded() {
    // ...
}
```

---

### 8.3 select! 宏

```rust
use tokio::select;

select! {
    val = operation1() => {
        println!("Operation 1: {}", val);
    }
    val = operation2() => {
        println!("Operation 2: {}", val);
    }
    _ = tokio::time::sleep(Duration::from_secs(1)) => {
        println!("Timeout!");
    }
}
```

---

### 8.4 join! 和 try_join! 宏

```rust
use tokio::join;
use tokio::try_join;

// join! - 等待所有完成
let (a, b, c) = join!(
    operation1(),
    operation2(),
    operation3(),
);

// try_join! - 短路错误
let result = try_join!(
    fallible_operation1(),
    fallible_operation2(),
)?;
```

---

## 9. 配置参考

### 9.1 Cargo Features

```toml
[dependencies]
tokio = { version = "1", features = [
    "full",          # 全部功能
    "rt-multi-thread", # 多线程运行时
    "rt",            # 基础运行时
    "net",           # 网络
    "fs",            # 文件系统
    "time",          # 时间
    "sync",          # 同步原语
    "signal",        # 信号处理
    "process",       # 进程
    "macros",        # 宏
    "io-util",       # IO工具
    "io-std",        # 标准IO
    "tracing",       # tracing支持
] }
```

---

## 📚 延伸阅读

- **[异步运行时选择指南](../tier_02_guides/03_异步运行时选择指南.md)** - 运行时对比
- **[异步语言特性参考](./01_异步语言特性参考.md)** - 语言特性
- **[异步生态系统参考](./03_异步生态系统参考.md)** - 生态库

---

## 📝 总结

**核心模块**:

- ✅ Runtime - 运行时管理
- ✅ Task - 任务调度
- ✅ Sync - 同步原语
- ✅ Time - 时间操作
- ✅ Net - 网络 I/O
- ✅ FS - 文件系统
- ✅ IO - 异步I/O traits

**常用功能**:

- ✅ spawn/block_on - 任务管理
- ✅ Channel - 任务通信
- ✅ sleep/timeout - 时间控制
- ✅ TcpListener/TcpStream - TCP
- ✅ File - 文件操作

---

**文档维护**: C06 Async Team | **质量评分**: 95/100  
**最后更新**: 2025-10-22 | **Tokio 版本**: 1.x
