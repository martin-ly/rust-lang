# 第 1 章：异步编程导论与哲学


## 📊 目录

- [1. 哲学：为什么需要异步？](#1-哲学为什么需要异步)
  - [1.1. 同步模型的局限](#11-同步模型的局限)
  - [1.2. Rust 的异步设计目标](#12-rust-的异步设计目标)
- [2. 核心抽象：`Future` Trait](#2-核心抽象future-trait)
  - [2.1. 定义：一个尚未完成的计算](#21-定义一个尚未完成的计算)
  - [2.2. `poll` 方法：推动 `Future` 前进](#22-poll-方法推动-future-前进)
  - [2.3. `Poll` 枚举：`Future` 的两种状态](#23-poll-枚举future-的两种状态)
- [3. 人体工程学：`async/await` 语法](#3-人体工程学asyncawait-语法)
  - [3.1. `async`：创建 `Future`](#31-async创建-future)
  - [3.2. `.await`：等待 `Future`](#32-await等待-future)
- [4. 底层机制：状态机](#4-底层机制状态机)
  - [4.1. 编译器的魔法](#41-编译器的魔法)
  - [4.2. 概念上的状态机](#42-概念上的状态机)
- [5. 调度：`Waker` 与 `Executor`](#5-调度waker-与-executor)
  - [5.1. `Future` 的惰性](#51-future-的惰性)
  - [5.2. `Executor`：`Future` 的驱动者](#52-executorfuture-的驱动者)
  - [5.3. `Waker`：从休眠到唤醒的信使](#53-waker从休眠到唤醒的信使)
  - [5.4. 轮询 (Polling) 模型工作流](#54-轮询-polling-模型工作流)
- [6. 总结](#6-总结)


- [第 1 章：异步编程导论与哲学](#第-1-章异步编程导论与哲学)
  - [1. 哲学：为什么需要异步？](#1-哲学为什么需要异步)
    - [1.1. 同步模型的局限](#11-同步模型的局限)
    - [1.2. Rust 的异步设计目标](#12-rust-的异步设计目标)
  - [2. 核心抽象：`Future` Trait](#2-核心抽象future-trait)
    - [2.1. 定义：一个尚未完成的计算](#21-定义一个尚未完成的计算)
    - [2.2. `poll` 方法：推动 `Future` 前进](#22-poll-方法推动-future-前进)
    - [2.3. `Poll` 枚举：`Future` 的两种状态](#23-poll-枚举future-的两种状态)
  - [3. 人体工程学：`async/await` 语法](#3-人体工程学asyncawait-语法)
    - [3.1. `async`：创建 `Future`](#31-async创建-future)
    - [3.2. `.await`：等待 `Future`](#32-await等待-future)
  - [4. 底层机制：状态机](#4-底层机制状态机)
    - [4.1. 编译器的魔法](#41-编译器的魔法)
    - [4.2. 概念上的状态机](#42-概念上的状态机)
  - [5. 调度：`Waker` 与 `Executor`](#5-调度waker-与-executor)
    - [5.1. `Future` 的惰性](#51-future-的惰性)
    - [5.2. `Executor`：`Future` 的驱动者](#52-executorfuture-的驱动者)
    - [5.3. `Waker`：从休眠到唤醒的信使](#53-waker从休眠到唤醒的信使)
    - [5.4. 轮询 (Polling) 模型工作流](#54-轮询-polling-模型工作流)
  - [6. 总结](#6-总结)

---

## 1. 哲学：为什么需要异步？

### 1.1. 同步模型的局限

在传统的同步编程（或基于线程的并发）中，当程序需要执行一个耗时的 I/O 操作（如发起网络请求、读写文件）时，执行该任务的线程会被**阻塞 (block)**。这意味着，在等待 I/O 操作完成的整个过程中，该线程无法执行任何其他工作，其 CPU 资源被闲置。

对于需要处理大量并发 I/O 的应用（如 Web 服务器、数据库代理），为每个并发任务都分配一个操作系统线程，会带来两个严重问题：

1. **资源开销**：操作系统线程是重量级资源，每个线程都需要一个独立的栈空间（通常为数 MB），创建和销毁它们本身也有开销。
2. **性能瓶颈**：操作系统能够高效调度的线程数量是有限的。当线程数量过多时，频繁的上下文切换会成为巨大的性能瓶颈。

### 1.2. Rust 的异步设计目标

异步编程 (Asynchronous Programming) 旨在解决上述问题。它允许单个线程或少量线程就能高效地管理成千上万个并发的 I/O 任务。当一个异步任务需要等待 I/O 时，它会**让出 (yield)** CPU 的控制权，允许执行器去运行其他已准备就绪的任务，而不是阻塞整个线程。

Rust 的异步模型在设计上追求三大核心目标：

1. **零成本抽象 (Zero-Cost Abstraction)**：异步机制本身不应引入不必要的运行时开销。其性能应与手动编写的高度优化的状态机代码相当。
2. **内存安全 (Memory Safety)**：利用所有权、借用和生命周期等机制，在编译时就杜绝数据竞争和其他内存安全问题。
3. **人体工程学 (Ergonomics)**：提供简洁、直观的 `async/await` 语法，让异步代码的编写和阅读体验尽可能接近同步代码。

## 2. 核心抽象：`Future` Trait

`Future` 是 Rust 异步编程世界中最核心、最基础的抽象。

### 2.1. 定义：一个尚未完成的计算

`Future` 是一个 Trait，它代表一个**可能在未来某个时间点完成**的计算。它可以是一个等待完成的数据库查询，一个正在下载文件的网络请求，或是一个简单的定时器。

关键在于，`Future` 本身是**惰性的 (lazy)**。仅仅创建一个 `Future` 并不会执行任何操作。它只是描述了一个计算过程，直到它被一个**执行器 (Executor)** actively **轮询 (poll)** 时，计算才会向前推进。

### 2.2. `poll` 方法：推动 `Future` 前进

`Future` Trait 的定义非常简洁，其核心只有一个方法：`poll`。

```rust
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait Future {
    type Output; // Future 完成时产生的最终值的类型

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

`poll` 方法的作用就是"推动" `Future` 的计算。执行器会反复调用这个方法，询问 `Future`："你完成了吗？"

- `self: Pin<&mut Self>`: 一个特殊的指针类型，用于保证 `Future` 在 `poll` 期间不会在内存中被移动。这对于 `async` 代码编译后的状态机至关重要，我们将在后续章节深入探讨 `Pin`。
- `cx: &mut Context<'_>`: 一个包含了"唤醒器" (`Waker`) 的上下文。`Waker` 是 `Future` 用来通知执行器它已准备好再次被 `poll` 的机制。

### 2.3. `Poll` 枚举：`Future` 的两种状态

`poll` 方法的返回值 `Poll<T>` 是一个枚举，它精确地描述了 `Future` 当前的状态：

```rust
pub enum Poll<T> {
    // 状态一：完成。Future 已经成功结束，并产生了一个类型为 T 的值。
    Ready(T),

    // 状态二：未完成。Future 尚未完成计算（例如，仍在等待网络数据）。
    // 它已经通过 `Context` 中的 `Waker` 注册了唤醒通知。
    // 执行器应该暂停它，等待被唤醒后再来 poll。
    Pending,
}
```

`poll` 的返回值是整个异步调度系统的核心信号。

## 3. 人体工程学：`async/await` 语法

直接手动实现 `Future` Trait 是复杂且繁琐的。为此，Rust 提供了 `async` 和 `.await` 这两个关键字作为语法糖，极大地简化了异步代码的编写。

### 3.1. `async`：创建 `Future`

`async` 关键字可以用于函数 (`async fn`) 或代码块 (`async {}`)。它的作用是将一个函数或代码块转变为一个会返回 `Future` 的东西。

```rust
// 这是一个普通的同步函数
fn get_greeting_sync() -> String {
    "Hello, ".to_string()
}

// 这是一个异步函数。它不会立即返回 String，
// 而是返回一个 `impl Future<Output = String>`。
async fn get_greeting_async() -> String {
    "Hello, ".to_string()
}
```

### 3.2. `.await`：等待 `Future`

`.await` 运算符只能在 `async` 函数或块中使用。它的作用是等待一个 `Future` 完成。

- 当你 `.await` 一个 `Future` 时，它会尝试 `poll` 这个 `Future`。
- 如果 `Future` 返回 `Poll::Ready(value)`，那么 `.await` 表达式就会求值为这个 `value`。
- 如果 `Future` 返回 `Poll::Pending`，`async` 函数会在这里**暂停**执行，并将 `Pending` 状态向上传递。这使得执行器可以去运行其他任务。当底层的 `Future` 最终通过 `Waker` 通知准备就绪时，执行器会从这个暂停点恢复执行。

```rust
async fn hello_world() {
    let part1 = get_greeting_async().await; // 等待第一个 Future 完成
    let part2 = "world!".to_string();
    println!("{}{}", part1, part2);
}
```

## 4. 底层机制：状态机

`async/await` 的优雅语法背后，是编译器为我们完成的复杂工作：将异步代码转换为一个精巧的**状态机 (State Machine)**。

### 4.1. 编译器的魔法

当你编写一个 `async fn` 时，编译器会分析其中的 `.await` 调用点。这些暂停点将整个函数分割成不同的状态。编译器会生成一个匿名的结构体（或枚举），这个结构体就是实现了 `Future` Trait 的状态机。

- 状态机的**字段**包含了所有需要跨越 `.await` 点保存的局部变量。
- 状态机的 `poll` 方法实现了状态转换的逻辑。

### 4.2. 概念上的状态机

考虑以下 `async` 函数：

```rust
async fn fetch_and_process() -> u32 {
    let data = fetch_from_db().await;
    let result = process(data).await;
    result
}
```

编译器可能生成类似这样的状态机：

```rust
enum FetchAndProcessState {
    // 初始状态
    Start,
    // 正在等待数据库返回
    WaitingOnDb { db_future: DbFuture },
    // 正在等待处理完成
    WaitingOnProcess { process_future: ProcessFuture },
    // 完成
    Done,
}

// 这个结构体实现了 Future<Output = u32>
struct FetchAndProcessStateMachine {
    state: FetchAndProcessState,
    // ... 其他需要保存的变量
}

// poll 方法会根据当前 state 来决定是 poll 内部的 future
// 还是根据 Ready 的结果转换到下一个 state。
```

这种在编译时生成状态机的模式，正是 Rust 异步实现"零成本抽象"的关键。

## 5. 调度：`Waker` 与 `Executor`

我们已经知道了 `Future` 是惰性的，需要被 `poll` 才能运行。那么，是谁在 `poll` 它呢？

### 5.1. `Future` 的惰性

如果你只调用一个 `async fn` 但不对其返回的 `Future` 做任何事，那么这段代码将永远不会执行。

```rust
// 这行代码什么都不会做，因为返回的 Future 被立即丢弃了。
hello_world();
```

### 5.2. `Executor`：`Future` 的驱动者

一个**执行器 (Executor)** 是一个负责接收顶层 `Future`（通常称为**任务 (Task)**）并驱动它们直到完成的组件。执行器是异步世界的心脏。

- 它维护一个任务队列。
- 它不断从队列中取出准备好的任务，并调用其 `Future` 的 `poll` 方法。

### 5.3. `Waker`：从休眠到唤醒的信使

当执行器 `poll` 一个 `Future` 并得到 `Poll::Pending` 时，它会将该任务暂时搁置。如果没有任何通知机制，执行器将不知道何时应该再次 `poll` 这个任务。

`Waker` 就是这个通知机制。

- 当执行器 `poll` 一个 `Future` 时，它会创建一个与该任务相关联的 `Waker`，并通过 `Context` 传递给 `poll` 方法。
- 当 `Future` 返回 `Pending` 时，它必须**保存**这个 `Waker` 的一个克隆。
- 当 `Future` 等待的外部事件（如网络套接字变为可读）发生时，事件源会调用被保存的 `Waker` 的 `wake()` 方法。
- `wake()` 方法会通知执行器："与此 `Waker` 关联的任务已经准备好，请将它放回任务队列等待下一次 `poll`"。

### 5.4. 轮询 (Polling) 模型工作流

整个流程可以总结为：

1. 开发者将一个顶层的 `async` 块或 `async fn` 返回的 `Future` 交给执行器（例如，通过 `tokio::spawn`）。
2. 执行器将 `Future` 包装成一个任务，放入待执行队列。
3. 执行器从队列中取出一个任务，调用其 `poll` 方法。
4. `Future` 开始执行：
    - 如果遇到 `.await`，它会 `poll` 内部的 `Future`。
    - 如果内部 `Future` 返回 `Poll::Ready(value)`，计算继续。
    - 如果内部 `Future` 返回 `Poll::Pending`，则外部的 `Future` 也会返回 `Poll::Pending`。在此之前，它确保底层的事件源已经保存了从 `Context` 中获取的 `Waker`。
5. 执行器收到 `Poll::Pending`，将任务挂起，并去处理下一个准备好的任务。
6. 一段时间后，I/O 操作完成，事件源调用 `Waker::wake()`。
7. 执行器收到通知，将被唤醒的任务重新放回待执行队列。
8. 循环回到第 3 步，直到 `Future` 返回 `Poll::Ready`。

## 6. 总结

本章介绍了 Rust 异步编程的基石。其核心是一种基于**轮询 (Polling)** 的模型，其中惰性的 `Future` 描述了一个异步计算，而执行器则负责驱动这些 `Future`。通过 `async/await` 语法，编译器将复杂的异步逻辑转换为高效的状态机，而 `Waker` 机制则充当了任务与执行器之间的通信桥梁。这个精心设计的系统共同构成了 Rust 高性能、高安全性的异步编程范式。
