# 第 2 章：运行时与执行模型

- [第 2 章：运行时与执行模型](#第-2-章运行时与执行模型)
  - [1. 核心概念区分](#1-核心概念区分)
    - [1.1. `Future`：描述任务](#11-future描述任务)
    - [1.2. `Executor`：驱动任务](#12-executor驱动任务)
    - [1.3. `Runtime`：提供环境](#13-runtime提供环境)
  - [2. 执行器 (`Executor`) 的工作原理](#2-执行器-executor-的工作原理)
    - [2.1. 核心职责](#21-核心职责)
    - [2.2. 概念实现：一个简单的执行器](#22-概念实现一个简单的执行器)
    - [2.3. 任务调度策略](#23-任务调度策略)
  - [3. 运行时 (`Runtime`) 的构成](#3-运行时-runtime-的构成)
    - [3.1. I/O 事件通知（反应器 Reactor）](#31-io-事件通知反应器-reactor)
    - [3.2. 定时器 API](#32-定时器-api)
    - [3.3. 任务生成 (`spawn`)](#33-任务生成-spawn)
    - [3.4. 线程池模型](#34-线程池模型)
  - [4. 运行时生态与对比](#4-运行时生态与对比)
    - [4.1. 分离的哲学：优势与挑战](#41-分离的哲学优势与挑战)
    - [4.2. 主流运行时对比](#42-主流运行时对比)
  - [5. 总结](#5-总结)

---

## 1. 核心概念区分

在 Rust 的异步世界中，`Future`、`Executor` 和 `Runtime` 是三个紧密相关但职责分明的核心概念。

### 1.1. `Future`：描述任务

如前一章所述，`Future` 是一个描述异步计算的惰性状态机。它本身什么也不做。

### 1.2. `Executor`：驱动任务

**执行器 (Executor)** 是驱动 `Future` 直至完成的核心组件。它的唯一工作就是接收任务 (`Future`)，并不断在其上调用 `.poll()` 方法。

### 1.3. `Runtime`：提供环境

**运行时 (Runtime)** 是一个为异步任务提供所有必要服务的"大管家"。它通常**包含**一个或多个执行器，并额外提供：

- **I/O 事件源**：与操作系统交互（例如，通过 `epoll`, `kqueue`, `io_uring`），监听网络、文件等 I/O 资源的状态。
- **定时器**：提供 `sleep` 或延时功能。
- **任务生成接口**：如 `spawn`，用于将一个顶层 `Future` 作为一个新任务交给执行器。
- **线程池**：用于并行地执行多个任务（在多线程运行时中）。

简单来说：**`Runtime` 搭台，`Executor` 唱戏，`Future` 是剧本。**

## 2. 执行器 (`Executor`) 的工作原理

### 2.1. 核心职责

1. **任务队列 (Task Queue)**：持有一个队列，存放所有准备好被 `poll` 的任务。
2. **轮询循环 (Polling Loop)**：不断从队列中取出任务，调用其 `poll` 方法。
3. **处理结果**：
    - 如果 `poll` 返回 `Poll::Ready`，任务完成，将其丢弃。
    - 如果 `poll` 返回 `Poll::Pending`，将任务挂起，等待 `Waker` 的通知。
4. **响应唤醒**：当 `Waker` 被调用时，将对应的任务重新放回任务队列。

### 2.2. 概念实现：一个简单的执行器

为了更好地理解，我们可以勾画一个极简的、单线程的执行器。

```rust
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex, Condvar};
use std::task::{Context, Poll, Waker};

// 任务队列
type Task = Pin<Box<dyn Future<Output = ()> + Send>>;
let task_queue = Arc::new(Mutex::new(VecDeque::new()));
let wake_cond = Arc::new(Condvar::new());

// Waker 的实现需要将任务重新放回队列
// (此处省略 Waker 的复杂实现细节)

// 执行器的主循环
let queue_clone = task_queue.clone();
let cond_clone = wake_cond.clone();
std::thread::spawn(move || {
    loop {
        let mut guard = queue_clone.lock().unwrap();
        while guard.is_empty() {
            // 如果队列为空，则等待 Waker 的通知
            guard = cond_clone.wait(guard).unwrap();
        }

        let task = guard.pop_front().unwrap();
        drop(guard); // 尽早释放锁

        // 创建一个 Waker 并 poll 任务
        let waker = unimplemented!(); // 需要一个能唤醒这个循环的 Waker
        let mut context = Context::from_waker(&waker);
        
        if task.as_mut().poll(&mut context) == Poll::Pending {
            // 如果任务未完成，它已经被 Waker 负责，此处无需操作
        }
    }
});

// spawn 函数：将 Future 添加到队列并通知执行器
fn spawn(future: impl Future<Output = ()> + Send + 'static) {
    let task = Box::pin(future);
    task_queue.lock().unwrap().push_back(task);
    wake_cond.notify_one();
}
```

*注意：这是一个高度简化的概念模型，真正的 `Waker` 实现要复杂得多，通常需要 `ArcWake` Trait。*

### 2.3. 任务调度策略

- **单线程执行器**: 所有任务都在同一个线程上轮询。实现简单，没有同步开销，但无法利用多核。
- **多线程执行器**:
  - **工作分享 (Work-Sharing)**: 维护一个全局的任务队列，多个工作线程都从这个队列中取任务。优点是实现简单，缺点是全局队列需要锁保护，容易成为性能瓶瓶颈。
  - **工作窃取 (Work-Stealing)**: 每个工作线程都有自己的本地任务队列。当一个线程的本地队列为空时，它会去"窃取"其他线程队列中的任务来执行。这是 `tokio` 和 `Rayon` 等高性能库采用的策略，能更好地实现负载均衡并减少锁竞争。

## 3. 运行时 (`Runtime`) 的构成

一个生产级的运行时远比一个简单的执行器复杂。

### 3.1. I/O 事件通知（反应器 Reactor）

这是运行时的核心功能之一。当一个异步 I/O 操作（如 `TcpStream::read`）被 `poll` 且无法立即完成时，会发生以下情况：

1. 该操作向运行时内部的**反应器 (Reactor)** 注册。注册内容包括：感兴趣的事件（如"可读"）和与当前任务关联的 `Waker`。
2. `Future` 返回 `Poll::Pending`。
3. 反应器通过 `epoll` (Linux), `kqueue` (macOS), `IOCP` (Windows) 等操作系统 API 监听大量 I/O 资源。
4. 当操作系统通知某个资源（如套接字）变为可读时，反应器找到与之关联的 `Waker` 并调用 `wake()`。
5. 执行器收到通知，将对应任务调度回来，再次 `poll` 时，I/O 操作现在就可以立即完成。

### 3.2. 定时器 API

运行时通常还包含一个定时器实现，允许 `Future` 在未来的特定时间点被唤醒。`async_std::task::sleep` 或 `tokio::time::sleep` 就是基于此实现的。

### 3.3. 任务生成 (`spawn`)

运行时提供一个用户友好的接口（如 `tokio::spawn`）来接收顶层 `Future`，将其包装成任务并交给执行器。这些 `spawn` 的函数通常要求 `Future` 是 `Send` 的（如果运行时是多线程的）和 `'static` 的（因为任务的生命周期独立于创建它的函数）。

### 3.4. 线程池模型

多线程运行时会管理一个工作线程池。

- **`tokio`**: 默认采用多线程、工作窃取模型，旨在最大化 CPU 密集型和 I/O 密集型混合负载的吞吐量。
- **`async-std`**: 每个任务都会被随机分配到一个工作线程上。

## 4. 运行时生态与对比

### 4.1. 分离的哲学：优势与挑战

Rust 将语言核心（`Future`, `async/await`）与运行时分离，这是一个关键的设计决策。

- **优势**:
  - **灵活性**: 社区可以为不同场景（通用网络、嵌入式、WebAssembly）创建高度优化的运行时。
  - **专业化**: 运行时可以独立于语言进行创新，集成最新的操作系统特性或调度算法。
- **挑战**:
  - **生态碎片化**: 不同运行时的 I/O 类型和同步原语（如 `Mutex`）通常不兼容，导致库需要在它们之间做选择或提供特性开关（feature flags）。
  - **学习成本**: 新手需要理解运行时的概念并做出选择。

### 4.2. 主流运行时对比

| 特性 | `tokio` | `async-std` | `smol` |
| :--- | :--- | :--- | :--- |
| **设计哲学** | 功能全面、性能驱动 | 模仿标准库 API，易于上手 | 模块化、轻量级 |
| **调度模型** | 多线程，工作窃取 | 多线程，工作分享 | 默认单线程，可配置 |
| **生态系统** | 最庞大、最成熟，是事实标准 | 较小，但核心功能完备 | 实验性，专注于简洁 |
| **主要优势** | 性能、稳定性和丰富的生态库 | 简洁、符合直觉的 API | 简单、可组合 |
| **适用场景** | 生产级网络服务、数据库等 | 学习、中小型项目 | 嵌入式、需要自定义运行时的场景 |

## 5. 总结

Rust 的异步执行模型是一个分层系统。`Future` 描述了"做什么"，执行器决定了"何时做"，而运行时则提供了"在哪里做"以及"如何与外部世界（I/O、时间）交互"的全套环境。理解这种职责分离是掌握 Rust 异步编程的关键。虽然运行时的分离带来了生态上的挑战，但也赋予了 Rust 社区巨大的灵活性，能够为各种不同的应用场景打造出最高效、最合适的异步解决方案。
