# 第2层：系统编程层 (System Programming Layer)

> **定位**: 系统级编程所需的并发、内存、I/O 等核心能力  
> **特点**: 高性能、零成本抽象、安全并发  
> **版本**: Rust 1.90 (2025)

---

## 📋 目录

- [第2层：系统编程层 (System Programming Layer)](#第2层系统编程层-system-programming-layer)
  - [📋 目录](#-目录)
  - [层级概述](#层级概述)
    - [核心能力](#核心能力)
    - [技术栈选择](#技术栈选择)
  - [核心类别](#核心类别)
    - [1. 异步运行时 (`async_runtime/`)](#1-异步运行时-async_runtime)
    - [2. 并发原语 (`concurrency/`)](#2-并发原语-concurrency)
    - [3. 内存管理 (`memory/`)](#3-内存管理-memory)
    - [4. 网络编程 (`networking/`)](#4-网络编程-networking)
    - [5. 文件 I/O (`io/`)](#5-文件-io-io)
    - [6. 通道 (`channels/`)](#6-通道-channels)
    - [7. Unsafe Rust (`unsafe/`)](#7-unsafe-rust-unsafe)
    - [8. 进程与系统 (`process_system/`)](#8-进程与系统-process_system)
  - [技术选型指南](#技术选型指南)
    - [异步 vs 同步](#异步-vs-同步)
    - [并发模型选择](#并发模型选择)
    - [内存管理策略](#内存管理策略)
  - [学习路径](#学习路径)
    - [初级（1-2周）](#初级1-2周)
    - [中级（3-4周）](#中级3-4周)
    - [高级（5-8周）](#高级5-8周)
  - [最佳实践](#最佳实践)
    - [1. 异步 + 同步混合](#1-异步--同步混合)
    - [2. 合理使用通道](#2-合理使用通道)
    - [3. 内存池复用](#3-内存池复用)
    - [4. 零拷贝优化](#4-零拷贝优化)
    - [5. 优雅关闭](#5-优雅关闭)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [深度文章](#深度文章)
    - [实战项目](#实战项目)
    - [相关文档](#相关文档)

---

## 层级概述

### 核心能力

**系统编程层** 是 Rust 生态的核心力量所在，提供构建高性能系统级应用的基础设施。

**关键特性**:

1. **零成本抽象**: 无运行时开销的高层抽象
2. **内存安全**: 编译期保证，无需 GC
3. **并发安全**: 类型系统保证线程安全
4. **可预测性能**: 无 GC 暂停，确定性延迟

**典型应用场景**:

- 🚀 高性能服务器（Web、数据库、缓存）
- 🔧 系统工具（CLI、守护进程、网络工具）
- 📡 网络服务（代理、负载均衡、网关）
- 🎮 实时系统（游戏服务器、流媒体）
- 🔐 安全关键系统（加密、认证、审计）

### 技术栈选择

**按并发模型分类**:

| 模型 | 适用场景 | 核心库 | 性能特点 |
|------|---------|--------|----------|
| **异步 I/O** | 网络密集型 | tokio, async-std | 高并发、低延迟 |
| **数据并行** | 计算密集型 | rayon | 充分利用多核 |
| **混合模型** | 复杂系统 | tokio + rayon | 灵活组合 |

**按性能需求分类**:

| 需求 | 技术栈 | 权衡 |
|------|--------|------|
| **极致性能** | tokio + parking_lot + bytes | 复杂度高 |
| **快速开发** | async-std + crossbeam | 易用性优先 |
| **轻量级** | smol + flume | 依赖少、体积小 |

---

## 核心类别

### 1. 异步运行时 ([`async_runtime/`](./async_runtime/))

**对比矩阵**:

| 库名 | 特点 | 生态规模 | 学习曲线 | 推荐度 |
|------|------|---------|---------|--------|
| **tokio** | 功能最全、生态最大、工业标准 | ⭐⭐⭐⭐⭐ | 中 | ⭐⭐⭐⭐⭐ |
| **async-std** | 类似标准库 API、易上手 | ⭐⭐⭐⭐ | 低 | ⭐⭐⭐⭐ |
| **smol** | 轻量级、高性能、模块化 | ⭐⭐⭐ | 中 | ⭐⭐⭐⭐ |

**快速示例** (tokio):

```rust
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() {
    // 并发任务
    let task1 = tokio::spawn(async {
        sleep(Duration::from_secs(1)).await;
        println!("Task 1 完成");
        1
    });
    
    let task2 = tokio::spawn(async {
        sleep(Duration::from_secs(2)).await;
        println!("Task 2 完成");
        2
    });
    
    // 等待所有任务
    let (r1, r2) = tokio::join!(task1, task2);
    println!("结果: {} + {} = {}", r1.unwrap(), r2.unwrap(), r1.unwrap() + r2.unwrap());
}
```

**性能数据**:

- **吞吐量**: 1M+ req/s (单核，echo server)
- **延迟**: P99 < 1ms (空载)
- **内存**: ~5MB (最小配置)

**选择建议**:

- **选 tokio**: 生产环境、需要完整生态（如 hyper, tonic）
- **选 async-std**: 学习异步编程、API 简单场景
- **选 smol**: 嵌入式、WASM、最小化依赖

**详细文档**: [`async_runtime/README.md`](./async_runtime/)

---

### 2. 并发原语 ([`concurrency/`](./concurrency/))

**对比矩阵**:

| 库名 | 用途 | 特点 | 推荐度 |
|------|------|------|--------|
| **rayon** | 数据并行 | 自动负载均衡、work-stealing | ⭐⭐⭐⭐⭐ |
| **crossbeam** | 并发数据结构 | 无锁算法、channel | ⭐⭐⭐⭐⭐ |
| **parking_lot** | 高性能锁 | 比标准库快 2-3x | ⭐⭐⭐⭐⭐ |

**快速示例** (rayon):

```rust
use rayon::prelude::*;

// 并行计算
let sum: i32 = (1..=1_000_000)
    .into_par_iter()
    .map(|x| x * x)
    .sum();

println!("平方和: {}", sum);

// 并行排序
let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6];
data.par_sort_unstable();
```

**性能对比**:

| 操作 | 串行 | rayon | 加速比 (8核) |
|------|------|-------|-------------|
| 求和 (1M) | 2.5ms | 0.4ms | 6.25x |
| 排序 (1M) | 120ms | 20ms | 6.0x |
| map-reduce | 50ms | 8ms | 6.25x |

**详细文档**: [`concurrency/README.md`](./concurrency/)

---

### 3. 内存管理 ([`memory/`](./memory/))

**对比矩阵**:

| 库名 | 用途 | 特点 | 推荐度 |
|------|------|------|--------|
| **bytes** | 字节缓冲区 | 零拷贝、引用计数 | ⭐⭐⭐⭐⭐ |
| **bumpalo** | 竞技场分配器 | 快速分配、批量释放 | ⭐⭐⭐⭐ |
| **slab** | 对象池 | 固定大小、O(1) 分配 | ⭐⭐⭐⭐ |

**快速示例** (bytes):

```rust
use bytes::{Bytes, BytesMut, Buf, BufMut};

// 零拷贝切片
let data = Bytes::from("Hello, world!");
let slice1 = data.slice(0..5);  // "Hello"
let slice2 = data.slice(7..12); // "world"

// 可变缓冲区
let mut buf = BytesMut::with_capacity(1024);
buf.put_slice(b"Hello");
buf.put_u32(42);
```

**详细文档**: [`memory/README.md`](./memory/)

---

### 4. 网络编程 ([`networking/`](./networking/))

**对比矩阵**:

| 库名 | 层次 | 特点 | 推荐度 |
|------|------|------|--------|
| **mio** | 底层事件驱动 | epoll/kqueue 封装 | ⭐⭐⭐⭐ |
| **socket2** | Socket API | 跨平台、功能全 | ⭐⭐⭐⭐ |
| **quinn** | QUIC 协议 | HTTP/3、UDP | ⭐⭐⭐⭐ |

**技术栈建议**:

- **高层应用**: tokio + hyper/tonic（不直接用 mio）
- **自定义协议**: tokio + mio
- **UDP 应用**: socket2 + tokio
- **HTTP/3**: quinn + h3

**详细文档**: [`networking/README.md`](./networking/)

---

### 5. 文件 I/O ([`io/`](./io/))

**对比矩阵**:

| 库名 | 特点 | 适用场景 | 推荐度 |
|------|------|---------|--------|
| **tokio::fs** | 异步文件 I/O | 高并发、非阻塞 | ⭐⭐⭐⭐⭐ |
| **std::fs** | 同步文件 I/O | 简单场景、脚本 | ⭐⭐⭐⭐⭐ |
| **memmap2** | 内存映射 | 大文件、随机访问 | ⭐⭐⭐⭐ |
| **walkdir** | 目录遍历 | 递归搜索 | ⭐⭐⭐⭐ |

**性能对比** (读取 1GB 文件):

| 方法 | 耗时 | 内存 | 适用场景 |
|------|------|------|----------|
| `std::fs::read` | 3.2s | 1GB | 小文件 |
| `BufReader` | 1.5s | 8KB | 顺序读取 |
| `memmap2` | 0.1s | ~100MB | 随机访问 |
| `tokio::fs` | 1.6s | 8KB | 异步场景 |

**详细文档**: [`io/README.md`](./io/)

---

### 6. 通道 ([`channels/`](./channels/))

**对比矩阵**:

| 库名 | 类型 | 性能 | 特点 | 推荐度 |
|------|------|------|------|--------|
| **crossbeam-channel** | MPMC | ⚡⚡⚡⚡⚡ | 无锁、select | ⭐⭐⭐⭐⭐ |
| **flume** | MPMC | ⚡⚡⚡⚡⚡ | 异步兼容 | ⭐⭐⭐⭐ |
| **tokio::sync::mpsc** | 异步 MPSC | ⚡⚡⚡⚡ | Tokio 生态 | ⭐⭐⭐⭐⭐ |
| **std::sync::mpsc** | MPSC | ⚡⚡⚡ | 标准库 | ⭐⭐⭐ |

**选择建议**:

- **同步场景**: crossbeam-channel（最快）
- **异步场景**: tokio::sync::mpsc
- **混合场景**: flume（同步/异步兼容）
- **简单场景**: std::sync::mpsc

**详细文档**: [`channels/README.md`](./channels/)

---

### 7. Unsafe Rust ([`unsafe/`](./unsafe/))

**核心概念**:

- 裸指针操作
- FFI（Foreign Function Interface）
- 内联汇编
- 不安全 trait

**使用场景**:

- 🔧 与 C/C++ 互操作
- ⚡ 性能关键路径优化
- 🎯 实现无锁数据结构
- 🔌 硬件底层操作

**安全准则**:

1. **最小化使用**: 尽可能用安全抽象
2. **隔离封装**: 提供安全 API 接口
3. **详细文档**: 说明不变量和前置条件
4. **充分测试**: 包括边界条件和并发场景

**详细文档**: [`unsafe/README.md`](./unsafe/)

---

### 8. 进程与系统 ([`process_system/`](./process_system/))

**核心库**:

| 库名 | 用途 | 推荐度 |
|------|------|--------|
| **nix** | Unix 系统调用 | ⭐⭐⭐⭐⭐ |
| **sysinfo** | 系统信息 | ⭐⭐⭐⭐⭐ |
| **signal-hook** | 信号处理 | ⭐⭐⭐⭐⭐ |
| **daemonize** | 守护进程 | ⭐⭐⭐⭐ |

**功能覆盖**:

- 进程管理（fork, exec, wait）
- 信号处理（SIGTERM, SIGINT, 自定义）
- 系统监控（CPU, 内存, 磁盘, 网络）
- 进程间通信（管道, 共享内存）
- 守护进程化

**详细文档**: [`process_system/README.md`](./process_system/)

---

## 技术选型指南

### 异步 vs 同步

**选择异步** (tokio/async-std):

- ✅ I/O 密集型（网络服务、数据库）
- ✅ 高并发（>1000 连接）
- ✅ 低延迟要求
- ✅ 需要异步生态（hyper, tonic）

**选择同步** (rayon/crossbeam):

- ✅ 计算密集型（数据处理、图像处理）
- ✅ 简单场景（CLI 工具、脚本）
- ✅ 低并发（<100 连接）
- ✅ 不需要异步生态

**混合模型**:

```rust
#[tokio::main]
async fn main() {
    // 异步处理网络请求
    let data = fetch_data().await;
    
    // 同步处理计算密集任务（使用 spawn_blocking）
    let result = tokio::task::spawn_blocking(move || {
        // 在线程池中执行
        rayon::par_iter(&data)
            .map(|x| expensive_computation(x))
            .collect()
    }).await?;
}
```

### 并发模型选择

**决策树**:

```text
I/O 密集型？
├─ 是 → 异步 I/O (tokio)
│  └─ 需要计算？
│     ├─ 是 → tokio + rayon (spawn_blocking)
│     └─ 否 → tokio
│
└─ 否 → 计算密集型
   ├─ 数据并行？
   │  └─ 是 → rayon
   │
   └─ 任务并行？
      └─ 是 → crossbeam + 线程池
```

### 内存管理策略

**标准策略** (大多数场景):

- 使用标准库智能指针（`Box`, `Rc`, `Arc`）
- 必要时使用 `bytes` 减少拷贝
- 避免手动内存管理

**高性能策略** (性能关键场景):

- 使用 `bumpalo` 竞技场分配器（批量分配/释放）
- 使用 `slab` 对象池（固定大小对象）
- 使用 `bytes` 零拷贝（网络/I/O）
- 使用 `parking_lot` 高性能锁

**权衡**:

| 策略 | 性能 | 复杂度 | 内存使用 |
|------|------|--------|----------|
| 标准库 | ⭐⭐⭐ | 低 | 中 |
| bytes | ⭐⭐⭐⭐ | 中 | 低 |
| bumpalo | ⭐⭐⭐⭐⭐ | 高 | 高（短期） |
| slab | ⭐⭐⭐⭐⭐ | 中 | 中 |

---

## 学习路径

### 初级（1-2周）

**目标**: 掌握基础异步编程和并发原语

1. **异步基础** (tokio)
   - `async/await` 语法
   - `tokio::spawn` 任务
   - `tokio::join!` 并发
   - 简单 TCP echo server

2. **数据并行** (rayon)
   - `par_iter()` 并行迭代
   - `par_sort()` 并行排序
   - 图像处理示例

**实战项目**: 多线程文件处理工具

### 中级（3-4周）

**目标**: 深入异步编程和高级并发

1. **异步进阶** (tokio)
   - `tokio::select!` 多路复用
   - `tokio::time` 定时器
   - `tokio::sync` 同步原语
   - HTTP 服务器

2. **并发数据结构** (crossbeam)
   - `crossbeam-channel` 通道
   - `crossbeam-epoch` 无锁算法
   - 生产者-消费者模式

3. **内存优化** (bytes)
   - 零拷贝技术
   - 缓冲区管理
   - 网络协议解析

**实战项目**: Web 代理服务器

### 高级（5-8周）

**目标**: 系统级编程和性能优化

1. **系统编程** (nix, sysinfo)
   - 进程管理
   - 信号处理
   - 系统监控

2. **Unsafe Rust**
   - FFI 互操作
   - 无锁数据结构
   - 性能优化

3. **综合项目**
   - 分布式系统
   - 高性能服务器
   - 实时数据处理

**实战项目**: 分布式缓存系统（类 Redis）

---

## 最佳实践

### 1. 异步 + 同步混合

**描述**: 在异步运行时中执行同步任务。

```rust
#[tokio::main]
async fn main() {
    // CPU 密集任务放到 spawn_blocking
    let result = tokio::task::spawn_blocking(|| {
        // 这里会在专门的线程池执行，不会阻塞异步运行时
        expensive_computation()
    }).await.unwrap();
}
```

### 2. 合理使用通道

**描述**: 根据场景选择通道类型。

```rust
use tokio::sync::mpsc;

// 异步场景：tokio::sync::mpsc
let (tx, mut rx) = mpsc::channel(100);

tokio::spawn(async move {
    while let Some(msg) = rx.recv().await {
        process(msg).await;
    }
});
```

### 3. 内存池复用

**描述**: 高频分配场景使用对象池。

```rust
use slab::Slab;

// 对象池，复用内存
let mut pool = Slab::new();
let key = pool.insert(data);
// ... 使用
pool.remove(key);  // 归还池中
```

### 4. 零拷贝优化

**描述**: 网络/I/O 密集场景使用 `bytes`。

```rust
use bytes::Bytes;

// 零拷贝切片
let data = Bytes::from(vec![1, 2, 3, 4]);
let slice1 = data.slice(0..2);  // 不拷贝
let slice2 = data.slice(2..4);  // 不拷贝
```

### 5. 优雅关闭

**描述**: 正确处理信号和资源清理。

```rust
use tokio::signal;

#[tokio::main]
async fn main() {
    tokio::select! {
        _ = signal::ctrl_c() => {
            println!("收到 Ctrl+C，优雅关闭...");
            cleanup().await;
        }
        _ = run_server() => {}
    }
}
```

---

## 参考资源

### 官方文档

- 📚 [Tokio 官方教程](https://tokio.rs/tokio/tutorial)
- 📚 [Async Book](https://rust-lang.github.io/async-book/)
- 📚 [Rayon 文档](https://docs.rs/rayon/)

### 深度文章

- 📖 [Async Rust: Blocking Inside Async Code](https://ryhl.io/blog/async-what-is-blocking/)
- 📖 [Rust Concurrency Patterns](https://rust-unofficial.github.io/patterns/patterns/index.html)
- 📖 [Zero-Cost Async I/O](https://boats.gitlab.io/blog/post/zero-cost-async-io/)

### 实战项目

- 💻 [mini-redis](https://github.com/tokio-rs/mini-redis) - Tokio 官方示例
- 💻 [hyper](https://github.com/hyperium/hyper) - HTTP 库
- 💻 [mio](https://github.com/tokio-rs/mio) - 底层 I/O 库

### 相关文档

- 🔗 [应用开发层](../03_application_dev/README.md)
- 🔗 [基础设施层](../01_infrastructure/README.md)
- 🔗 [异步运行时详解](./async_runtime/README.md)

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**维护者**: Rust 学习社区
