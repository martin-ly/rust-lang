# 并发示例（Concurrent Examples）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [并发示例（Concurrent Examples）索引](#并发示例concurrent-examples索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心示例](#-核心示例)
    - [1. 线程同步（Thread Synchronization）](#1-线程同步thread-synchronization)
    - [2. 消息传递（Message Passing）](#2-消息传递message-passing)
    - [3. 异步编程（Async Programming）](#3-异步编程async-programming)
    - [4. 无锁编程（Lock-Free Programming）](#4-无锁编程lock-free-programming)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c05_threads/src/`](#cratesc05_threadssrc)
      - [`crates/c06_async/src/`](#cratesc06_asyncsrc)
    - [快速开始示例](#快速开始示例)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块提供 Rust 并发编程的实用示例，涵盖线程同步、消息传递、异步编程和无锁编程等核心主题。所有示例均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **并发安全**: 专注于安全并发编程实践
- **最佳实践**: 基于 Rust 社区最新并发实践
- **完整覆盖**: 涵盖多个并发模式
- **易于理解**: 提供详细的并发说明和代码示例

## 📚 核心示例

### 1. 线程同步（Thread Synchronization）

**推荐库**: `std::sync`, `parking_lot`, `crossbeam`

- **互斥锁使用**: `Mutex`, `RwLock` 使用示例
- **读写锁使用**: 读写锁、条件变量使用
- **条件变量示例**: 条件变量、屏障同步
- **屏障同步示例**: 屏障、信号量同步

**相关资源**:

- [Rust Book - Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [parking_lot 文档](https://docs.rs/parking_lot/)
- [crossbeam 文档](https://docs.rs/crossbeam/)

### 2. 消息传递（Message Passing）

**推荐库**: `std::sync::mpsc`, `crossbeam-channel`, `flume`

- **通道通信**: 通道、多生产者单消费者
- **生产者-消费者模式**: 经典并发模式实现
- **工作窃取模式**: 工作窃取队列、任务调度
- **背压处理**: 背压、流量控制

**相关资源**:

- [Rust Book - Channels](https://doc.rust-lang.org/book/ch16-02-message-passing.html)
- [crossbeam-channel 文档](https://docs.rs/crossbeam-channel/)
- [flume 文档](https://docs.rs/flume/)

### 3. 异步编程（Async Programming）

**推荐库**: `tokio`, `async-std`, `futures`

- **Future 实现**: 自定义 Future 类型
- **异步流处理**: `Stream` trait 和异步迭代
- **异步错误处理**: 异步环境下的错误处理
- **异步并发模式**: 异步任务管理、并发控制

**相关资源**:

- [Tokio 文档](https://tokio.rs/)
- [async-std 文档](https://docs.rs/async-std/)
- [futures 文档](https://docs.rs/futures/)

### 4. 无锁编程（Lock-Free Programming）

**推荐库**: `std::sync::atomic`, `crossbeam`, `lockfree`

- **原子操作**: 原子类型、原子操作
- **无锁数据结构**: 无锁队列、无锁栈
- **内存序示例**: 内存序、内存屏障
- **无锁算法实现**: 无锁算法、CAS 操作

**相关资源**:

- [Rust Book - Atomics](https://doc.rust-lang.org/nomicon/atomics.html)
- [crossbeam 文档](https://docs.rs/crossbeam/)
- [lockfree 文档](https://docs.rs/lockfree/)

## 💻 实践与样例

### 代码示例位置

- **并发示例**: [crates/c05_threads](../../../crates/c05_threads/)
- **异步编程**: [crates/c06_async](../../../crates/c06_async/)
- **分布式系统**: [crates/c20_distributed](../../../crates/c20_distributed/)

### 文件级清单（精选）

#### `crates/c05_threads/src/`

- `synchronization_examples.rs` - 同步原语示例
- `message_passing_examples.rs` - 消息传递示例
- `concurrent_patterns.rs` - 并发模式示例

#### `crates/c06_async/src/`

- `async_concurrency_examples.rs` - 异步并发示例
- `future_implementations.rs` - Future 实现示例
- `async_streams.rs` - 异步流示例

### 快速开始示例

```rust
// 线程同步示例
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("结果: {}", *counter.lock().unwrap());
}
```

```rust
// 消息传递示例
use std::sync::mpsc;
use std::thread;

fn main() {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let val = String::from("hello");
        tx.send(val).unwrap();
    });

    let received = rx.recv().unwrap();
    println!("收到: {}", received);
}
```

---

## 🔗 相关索引

- **理论基础（并发模型）**: [`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- **编程范式（并发）**: [`../../02_programming_paradigms/05_concurrent/00_index.md`](../../02_programming_paradigms/05_concurrent/00_index.md)
- **设计模式（并发模式）**: [`../../03_design_patterns/04_concurrent/00_index.md`](../../03_design_patterns/04_concurrent/00_index.md)

---

## 🧭 导航

- **返回实用示例**: [`../00_index.md`](../00_index.md)
- **安全示例**: [`../05_security_examples/00_index.md`](../05_security_examples/00_index.md)
- **异步示例**: [`../07_async_examples/00_index.md`](../07_async_examples/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
