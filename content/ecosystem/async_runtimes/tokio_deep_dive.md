> **生态状态提示**：本文档提及 `async-std` 与/或 `wasm32-wasi`。请注意：
>
> - `async-std` 项目已进入维护模式，2024 年后不再活跃开发；新项目建议优先评估 **Tokio** 或 **smol**。
> - `wasm32-wasi` 旧目标名已重命名为 **`wasm32-wasip1`**；WASI Preview 2 对应目标为 **`wasm32-wasip2`**。

---

# Tokio 异步运行时深度解析

> **定位**: Rust 生态核心 — 异步运行时
> **版本**: Tokio 1.40+ (兼容 Rust 1.96.0+)
> **适用场景**: 高并发网络服务、实时数据处理、微服务架构

---

## 📋 目录

- [Tokio 异步运行时深度解析](#tokio-异步运行时深度解析)
  - [📋 目录](#-目录)
  - [🎯 架构概览](#-架构概览)
  - [⚙️ 核心组件](#️-核心组件)
    - [1. 运行时 (Runtime)](#1-运行时-runtime)
    - [2. 任务调度器 (Scheduler)](#2-任务调度器-scheduler)
    - [3. I/O 驱动 (I/O Driver)](#3-io-驱动-io-driver)
    - [4. 时间驱动 (Time Driver)](#4-时间驱动-time-driver)
  - [🔧 工作线程模型](#-工作线程模型)
  - [📊 与其他运行时对比](#-与其他运行时对比)
  - [🚀 性能调优](#-性能调优)
    - [工作线程数](#工作线程数)
    - [阻塞操作](#阻塞操作)
    - [批处理 I/O](#批处理-io)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 架构概览

```text
┌─────────────────────────────────────────┐
│           Application Layer             │
│  (axum / tonic / reqwest / sqlx ...)    │
├─────────────────────────────────────────┤
│              Tokio Runtime              │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐    │
│  │ Task    │ │ I/O     │ │ Timer   │    │
│  │ Scheduler│ │ Driver  │ │ Driver  │   │
│  └────┬────┘ └────┬────┘ └────┬────┘    │
│       └─────────────┴─────────────┘     │
│              Work Stealing Queue        │
├─────────────────────────────────────────┤
│         OS / epoll / kqueue / IOCP      │
└─────────────────────────────────────────┘
```

Tokio 是 Rust 生态中最广泛使用的异步运行时，提供：

- **多线程任务调度**: 工作窃取 (work-stealing) 调度器
- **非阻塞 I/O**: 基于 epoll/kqueue/IOCP 的统一抽象
- **定时器**: 高效的时间轮 (timing wheel) 实现
- **同步原语**: async Mutex, RwLock, Semaphore, Barrier
- **通道**: mpsc, broadcast, watch, oneshot

---

## ⚙️ 核心组件

### 1. 运行时 (Runtime)

```rust
use tokio::runtime::{Builder, Runtime};

// 多线程运行时 (默认)
let rt = tokio::runtime::Runtime::new().unwrap();

// 自定义配置
let rt = Builder::new_multi_thread()
    .worker_threads(8)
    .max_blocking_threads(512)
    .thread_stack_size(3 * 1024 * 1024)
    .enable_all()
    .build()
    .unwrap();
```

| 运行时类型 | 适用场景 | 线程模型 |
|-----------|---------|---------|
| `new_multi_thread()` | 高并发网络服务 | N 工作线程 + M 阻塞线程 |
| `new_current_thread()` | 单线程/嵌入式 | 仅主线程 |

---

### 2. 任务调度器 (Scheduler)

Tokio 使用 **work-stealing** 调度器：

- **全局队列**: 所有线程可访问，用于跨线程任务分发
- **本地队列**: 每个工作线程一个，LIFO 顺序执行（缓存友好）
- **窃取**: 当本地队列为空时，从其他线程的队列尾部 FIFO 窃取任务

```rust
// 任务生成方式对比

// spawn: 进入全局队列，可能被任意线程执行
let handle = tokio::spawn(async_task());

// spawn_local (current_thread runtime): 仅当前线程执行
tokio::task::spawn_local(async_task());

// block_in_place: 将当前任务转为阻塞，释放线程
let result = tokio::task::block_in_place(|| heavy_cpu_work());
```

---

### 3. I/O 驱动 (I/O Driver)

Tokio 的 I/O 基于操作系统异步接口：

| 操作系统 | 后端 | 特性 |
|---------|------|------|
| Linux | epoll | 高效，O(1) 事件通知 |
| macOS/BSD | kqueue | 支持文件描述符和进程事件 |
| Windows | IOCP | 真正的异步 I/O，无轮询 |
| Linux 5.1+ | io_uring (可选) | 零系统调用批量提交 |

```rust
use tokio::net::TcpListener;

// TcpListener 是非阻塞的，背后注册到 epoll/kqueue/IOCP
let listener = TcpListener::bind("127.0.0.1:8080").await?;
loop {
    let (socket, addr) = listener.accept().await?;
    tokio::spawn(handle_connection(socket, addr));
}
```

---

### 4. 时间驱动 (Time Driver)

Tokio 使用 **分层时间轮 (Hierarchical Timing Wheel)**:

```rust
use tokio::time::{sleep, interval, timeout, Duration};

// sleep: 任务挂起直到时间到达
sleep(Duration::from_millis(100)).await;

// interval: 周期性触发
let mut tick = interval(Duration::from_secs(1));
tick.tick().await; // 首次触发

// timeout: 包装 Future，超时取消
let result = timeout(Duration::from_secs(5), fetch_data()).await;
```

**时间轮层级**:

- 毫秒级轮: 256 槽，每槽 1ms
- 秒级轮: 64 槽，每槽 1s
- 分钟级轮: 60 槽
- 效率: O(1) 插入，O(1) 到期检查

---

## 🔧 工作线程模型

```text
Thread 1          Thread 2          Thread 3
┌─────────┐       ┌─────────┐       ┌─────────┐
│ Local   │       │ Local   │       │ Local   │
│ Queue   │       │ Queue   │       │ Queue   │
│ [A,B,C] │       │ [D,E]   │       │ []      │
└────┬────┘       └────┬────┘       └────┬────┘
     │ LIFO execution   │ LIFO execution  │  steal from T1/T2
     ▼                  ▼                 ▼
   run A              run D            steal C (FIFO)
```

**调度规则**:

1. 优先执行本地队列任务（LIFO — 缓存局部性最佳）
2. 本地为空 → 检查全局队列
3. 全局为空 → 从其他线程窃取（FIFO — 减少竞争）

---

## 📊 与其他运行时对比

| 特性 | Tokio | async-std [已归档] [已停止维护，不推荐] | smol | embassy |
|------|-------|-----------|------|---------|
| 调度模型 | 工作窃取 | 工作窃取 | 单队列 | 协作式 |
| 默认线程数 | num_cpus | num_cpus | 单线程 | 单线程 |
| 生态成熟度 | ⭐⭐⭐ | ⭐⭐ | ⭐⭐ | ⭐⭐ |
| 网络协议栈 | 完整 | 基础 | 基础 | 嵌入式 |
| 适用场景 | 通用服务端 | 通用 | 小型应用 | 嵌入式/IoT |
| 与 std 兼容 | 独立生态 | 接近 std | 接近 std | no_std |

**选择决策树**:

```text
需要 no_std? ──是──→ Embassy
                └──否──→ 需要成熟生态? ──是──→ Tokio
                                      └──否──→ 追求简洁? ──是──→ smol
                                                            └──否──→ tokio [历史: async-std [已归档]]
```

---

## 🚀 性能调优

### 工作线程数

```rust
// 默认 = CPU 核心数，通常最优
// CPU 密集型任务: 略少于核心数 (留核心给 OS)
// I/O 密集型任务: 等于或略多于核心数

let rt = tokio::runtime::Builder::new_multi_thread()
    .worker_threads(num_cpus::get())
    .build()?;
```

### 阻塞操作

```rust
// ❌ 错误: 在工作线程中执行阻塞操作
async fn bad() {
    std::thread::sleep(Duration::from_secs(1)); // 阻塞整个线程！
}

// ✅ 正确: 使用 spawn_blocking
async fn good() {
    tokio::task::spawn_blocking(|| {
        std::thread::sleep(Duration::from_secs(1));
    }).await.unwrap();
}
```

### 批处理 I/O

```rust
// 使用 JoinSet 并发处理多个请求
use tokio::task::JoinSet;

let mut set = JoinSet::new();
for url in urls {
    set.spawn(fetch(url));
}
while let Some(result) = set.join_next().await {
    process(result?);
}
```

---

## 🔗 参考资源

- [Tokio 官方文档](https://tokio.rs/)
- [Tokio 内部原理](https://tokio.rs/blog/2019-10-scheduler)
- [项目 C06 异步模块](../../crates/c06_async/src/lib.rs)
- [项目 Async Closures 指南](../../crates/c06_async/docs/ASYNC_CLOSURES_GUIDE.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
