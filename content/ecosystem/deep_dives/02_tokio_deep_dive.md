# Tokio 深度解析

**EN**: Tokio Deep Dive
**Summary**: A practical deep dive into the Tokio async runtime: tasks, schedulers, I/O drivers, synchronization primitives, timers, and production patterns.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 通用 Rust 异步概念（Future、async/await、Pin、Waker）请见 [`concept/03_advanced/01_async/`](../../../concept/03_advanced/01_async/)；并发原语请见 [`concept/03_advanced/00_concurrency/`](../../../concept/03_advanced/00_concurrency/)。

---

## 目录

- [Tokio 深度解析](#tokio-深度解析)
  - [目录](#目录)
  - [一、定位与核心设计](#一定位与核心设计)
  - [二、运行时模型](#二运行时模型)
    - [2.1 创建 Runtime](#21-创建-runtime)
    - [2.2 Multi-thread vs Current-thread](#22-multi-thread-vs-current-thread)
  - [三、任务（Task）](#三任务task)
    - [3.1 任务与线程的区别](#31-任务与线程的区别)
    - [3.2 JoinSet](#32-joinset)
  - [四、I/O 驱动](#四io-驱动)
    - [4.1 TCP](#41-tcp)
    - [4.2 AsyncFd](#42-asyncfd)
  - [五、同步原语](#五同步原语)
    - [5.1 Mutex 使用示例](#51-mutex-使用示例)
    - [5.2 Channel 选择](#52-channel-选择)
  - [六、时间](#六时间)
    - [6.1 Interval 行为](#61-interval-行为)
  - [七、阻塞任务](#七阻塞任务)
  - [八、运行时选择指南](#八运行时选择指南)
  - [九、生产实践](#九生产实践)
    - [9.1 优雅关闭](#91-优雅关闭)
    - [9.2 配置 Runtime 线程数](#92-配置-runtime-线程数)
    - [9.3 与 Axum / Tower 结合](#93-与-axum--tower-结合)
  - [十、常见陷阱](#十常见陷阱)
  - [十一、延伸阅读](#十一延伸阅读)

---

## 一、定位与核心设计

Tokio 是 Rust 生态中最广泛使用的异步运行时，为 `std::future::Future` 提供执行环境。它不替代 Rust 的 `async/await` 语言特性，而是补齐三个关键能力：

- **任务调度器（Scheduler）**：决定哪些 Future 在何时被 poll。
- **I/O 驱动（I/O Driver）**：把 epoll/kqueue/IOCP 封装成 `AsyncRead` / `AsyncWrite` / `AsyncFd`。
- **异步同步原语**：`tokio::sync::Mutex`、`mpsc`、`Notify` 等，供异步任务协作。

Tokio 遵循“运行时与库解耦”的设计：业务代码写 `async fn`，库代码写 `Future`，最终由 Tokio runtime 驱动执行。

> **权威来源**: Future / async / await / Pin / Waker 语义详见 [`concept/03_advanced/01_async/02_async.md`](../../../concept/03_advanced/01_async/02_async.md)。

---

## 二、运行时模型

### 2.1 创建 Runtime

```rust
use tokio::runtime::Runtime;

fn main() {
    let rt = Runtime::new().unwrap();
    rt.block_on(async {
        println!("hello from tokio");
    });
}
```

或使用宏：

```rust
#[tokio::main]
async fn main() {
    println!("hello from tokio");
}
```

### 2.2 Multi-thread vs Current-thread

| Runtime | 适用场景 | 特点 |
|---|---|---|
| `Runtime::new()` / `#[tokio::main]` | 通用服务端 | 多线程 work-stealing 调度，默认同 CPU 核心数 |
| `runtime::Builder::new_current_thread()` | 单线程、嵌入式、测试 | 所有任务运行在一个线程，无 Send 约束 |

```rust
use tokio::runtime;

let rt = runtime::Builder::new_multi_thread()
    .worker_threads(4)
    .enable_all()
    .build()
    .unwrap();
```

> **权威来源**: 并发与线程模型详见 [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../concept/03_advanced/00_concurrency/01_concurrency.md)。

---

## 三、任务（Task）

任务是一个被 runtime 调度的 Future，通常通过 `tokio::spawn` 创建。

```rust
#[tokio::main]
async fn main() {
    let handle = tokio::spawn(async {
        42
    });

    let result = handle.await.unwrap();
    assert_eq!(result, 42);
}
```

### 3.1 任务与线程的区别

- **线程**：OS 调度单元，切换成本高，栈内存大。
- **任务**：用户态调度单元，成千上万个任务可在少量线程上协作执行。
- **任务要求**：被 `spawn` 的 Future 必须满足 `Send + 'static`（current-thread runtime 除外）。

### 3.2 JoinSet

`tokio::task::JoinSet` 用于管理一组同类型任务，并在它们完成时依次 await。

```rust
use tokio::task::JoinSet;

let mut set = JoinSet::new();
for i in 0..10 {
    set.spawn(async move { i * i });
}

while let Some(res) = set.join_next().await {
    println!("{}", res.unwrap());
}
```

---

## 四、I/O 驱动

Tokio 的 I/O 基于操作系统异步接口：Linux epoll、macOS/BSD kqueue、Windows IOCP。

### 4.1 TCP

```rust
use tokio::net::{TcpListener, TcpStream};

#[tokio::main]
async fn main() -> tokio::io::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    loop {
        let (socket, _) = listener.accept().await?;
        tokio::spawn(handle_connection(socket));
    }
}

async fn handle_connection(mut socket: TcpStream) -> tokio::io::Result<()> {
    let (reader, writer) = socket.split();
    tokio::io::copy(&mut reader, &mut writer).await?;
    Ok(())
}
```

### 4.2 AsyncFd

对于自定义文件描述符（如 FFI 返回的 fd），使用 `AsyncFd` 包装以接入 Tokio reactor。

```rust
use tokio::io::unix::AsyncFd;
```

---

## 五、同步原语

Tokio 提供一组专为异步设计的同步原语：

| 原语 | 用途 | 对应 std |
|---|---|---|
| `tokio::sync::Mutex` | 异步互斥 | `std::sync::Mutex` |
| `tokio::sync::RwLock` | 异步读写锁 | `std::sync::RwLock` |
| `tokio::sync::Semaphore` | 并发配额 | 无直接对应 |
| `tokio::sync::mpsc` | 多生产者单消费者通道 | `std::sync::mpsc` |
| `tokio::sync::broadcast` | 广播通道 | 无直接对应 |
| `tokio::sync::watch` | 单生产者多消费者、最新值 | 无直接对应 |
| `tokio::sync::Notify` | 单次通知 | `std::sync::Condvar` |
| `tokio::sync::Barrier` | 异步屏障 | `std::sync::Barrier` |

### 5.1 Mutex 使用示例

```rust
use tokio::sync::Mutex;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let counter = Arc::new(Mutex::new(0));

    for _ in 0..10 {
        let c = Arc::clone(&counter);
        tokio::spawn(async move {
            let mut n = c.lock().await;
            *n += 1;
        });
    }

    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    assert_eq!(*counter.lock().await, 10);
}
```

> **关键区别**：`tokio::sync::Mutex` 在持有锁时不会阻塞线程，而是让出任务；因此可以在 async 上下文中安全使用。不要在 async 中直接使用 `std::sync::Mutex` 进行长时间持有。

### 5.2 Channel 选择

- **`mpsc`**：任务间传递命令/事件，一个消费者。
- **`broadcast`**：通知多个订阅者同一事件。
- **`watch`**：共享可变配置，订阅者只关心最新值。

---

## 六、时间

Tokio 提供异步时间 API：

```rust
use tokio::time::{sleep, interval, timeout, Duration};

#[tokio::main]
async fn main() {
    // 延迟
    sleep(Duration::from_secs(1)).await;

    // 定时器
    let mut ticker = interval(Duration::from_secs(1));
    ticker.tick().await; // 第一次立即触发或等待一个周期，视设置而定

    // 超时
    let result = timeout(Duration::from_millis(100), slow_op()).await;
}

async fn slow_op() { sleep(Duration::from_secs(1)).await }
```

### 6.1 Interval 行为

默认 `interval` 会累积错过的 tick；若需跳过错过的时间点，使用 `MissedTickBehavior::Skip`。

```rust
use tokio::time::{interval, MissedTickBehavior};

let mut ticker = interval(Duration::from_secs(1));
ticker.set_missed_tick_behavior(MissedTickBehavior::Skip);
```

---

## 七、阻塞任务

在 async 任务中执行 CPU 密集型或同步阻塞操作会阻塞整个工作线程，降低并发能力。应使用 `tokio::task::spawn_blocking`。

```rust
#[tokio::main]
async fn main() {
    let result = tokio::task::spawn_blocking(|| {
        // 长时间 CPU 计算或同步 I/O
        expensive_computation()
    })
    .await
    .unwrap();
}
```

---

## 八、运行时选择指南

| 场景 | 推荐 Runtime | 理由 |
|---|---|---|
| HTTP / gRPC 服务端 | `multi_thread` | 高并发、多核利用 |
| CLI 工具 | `current_thread` 或 `multi_thread` | 通常只需一个任务链 |
| 嵌入式 / no_std 边界 | `current_thread` | 资源受限、无 Send 需求 |
| 测试 | `current_thread` | 测试更简单、确定性高 |
| CPU 密集型 + I/O 混合 | `multi_thread` + `spawn_blocking` | 避免阻塞 I/O 任务 |

---

## 九、生产实践

### 9.1 优雅关闭

```rust
use tokio::signal;

async fn shutdown_signal() {
    let ctrl_c = async { signal::ctrl_c().await.expect("ctrl+c handler"); };
    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("terminate signal")
            .recv()
            .await;
    };

    tokio::select! {
        _ = ctrl_c => {},
        _ = terminate => {},
    }
}
```

### 9.2 配置 Runtime 线程数

```rust
let rt = tokio::runtime::Builder::new_multi_thread()
    .worker_threads(num_cpus::get())
    .max_blocking_threads(512)
    .enable_all()
    .build()
    .unwrap();
```

### 9.3 与 Axum / Tower 结合

Axum 直接依赖 Tokio runtime。在 Axum 应用中，通常使用 `#[tokio::main]` 并提供 `tokio::net::TcpListener`。

> **延伸阅读**: Axum 详见 [`01_axum_deep_dive.md`](./01_axum_deep_dive.md)。

---

## 十、常见陷阱

1. **在 async 中调用阻塞 API**：应使用 `spawn_blocking`。
2. **`tokio::sync::Mutex` 跨 await 死锁**：不要在持有异步锁的同时调用可能长时间等待的其他异步锁。
3. **任务泄漏**：未 await 的 `JoinHandle` 会导致任务继续运行；必要时使用 `AbortHandle`。
4. **Interval 累积**：高负载下 missed tick 会堆积，需配置 `MissedTickBehavior`。
5. **Runtime 嵌套**：避免在 Tokio runtime 内部创建新的 Tokio runtime（panic 风险）。
6. **未启用 feature**：`tokio = { version = "1", features = ["full"] }` 开启全部功能；生产环境应只启用需要的 feature。

---

## 十一、延伸阅读

- [Tokio 官方文档](https://tokio.rs/)
- [Tokio 教程](https://tokio.rs/tokio/tutorial)
- [Async/await 心智模型](https://rust-lang.github.io/async-book/)
- 异步基础：[`concept/03_advanced/01_async/02_async.md`](../../../concept/03_advanced/01_async/02_async.md)
- 并发原语：[`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../concept/03_advanced/00_concurrency/01_concurrency.md)
- Axum 深度解析：[`01_axum_deep_dive.md`](./01_axum_deep_dive.md)
