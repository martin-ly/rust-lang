# Rust 异步编程详解

## 目录

- [Rust 异步编程详解](#rust-异步编程详解)
  - [目录](#目录)
  - [思维导图 (Text)](#思维导图-text)
  - [1. 基本概念](#1-基本概念)
    - [1.1 异步编程简介](#11-异步编程简介)
      - [定义](#定义)
      - [与同步/线程/回调对比](#与同步线程回调对比)
      - [Rust 的目标](#rust-的目标)
    - [1.2 Future 特质](#12-future-特质)
      - [核心定义](#核心定义)
      - [`Future` Trait 定义](#future-trait-定义)
      - [`Poll` 枚举](#poll-枚举)
      - [形式化定义尝试](#形式化定义尝试)
      - [核心特点](#核心特点)
      - [代码示例：`ReadyFuture`](#代码示例readyfuture)
    - [1.3 `async`/`await` 语法](#13-asyncawait-语法)
      - [定义与作用](#定义与作用)
      - [`async fn` / `async {}`](#async-fn--async-)
      - [`.await` 表达式](#await-表达式)
      - [形式化语义](#形式化语义)
      - [代码示例：异步函数](#代码示例异步函数)
  - [2. 原理与机制](#2-原理与机制)
    - [2.1 状态机转换原理](#21-状态机转换原理)
      - [核心机制](#核心机制)
      - [转换过程](#转换过程)
      - [代码示例：概念状态机](#代码示例概念状态机)
      - [关键特性](#关键特性)
      - [形式化推理：状态转换](#形式化推理状态转换)
    - [2.2 `Pin` 与内存安全](#22-pin-与内存安全)
      - [问题背景：自引用结构](#问题背景自引用结构)
      - [代码示例：自引用结构问题](#代码示例自引用结构问题)
      - [`Pin` 的定义与作用](#pin-的定义与作用)
      - [`Pin` 的核心 API](#pin-的核心-api)
      - [`Pin` 与 `Future`](#pin-与-future)
      - [形式化推理：`Pin` 的保证](#形式化推理pin-的保证)
    - [2.3 `Waker` 与任务唤醒](#23-waker-与任务唤醒)
      - [核心概念](#核心概念)
      - [`Context` 与 `Waker`](#context-与-waker)
      - [唤醒机制流程](#唤醒机制流程)
      - [代码示例：概念 `Waker` 创建](#代码示例概念-waker-创建)
      - [形式化推理：`Waker` 的契约](#形式化推理waker-的契约)
  - [3. 执行器与运行时](#3-执行器与运行时)
    - [3.1 执行器的工作原理](#31-执行器的工作原理)
      - [3.1.1 角色定义](#311-角色定义)
      - [3.1.2 基本实现流程 (概念代码)](#312-基本实现流程-概念代码)
      - [3.1.3 形式化推理：执行器的进展保证](#313-形式化推理执行器的进展保证)
      - [3.1.4 关键设计考量](#314-关键设计考量)
    - [3.2 异步运行时对比](#32-异步运行时对比)
      - [3.2.1 运行时定义](#321-运行时定义)
      - [3.2.2 主流运行时对比表](#322-主流运行时对比表)
      - [3.2.3 选择考量](#323-选择考量)
  - [4. 高级特性与应用](#4-高级特性与应用)
    - [4.1 异步流 (`Stream`)](#41-异步流-stream)
      - [4.1.1 定义](#411-定义)
      - [4.1.2 `Stream` Trait 定义](#412-stream-trait-定义)
      - [4.1.3 代码示例：消费 Stream](#413-代码示例消费-stream)
    - [4.2 取消与超时](#42-取消与超时)
      - [4.2.1 概念](#421-概念)
      - [4.2.2 代码示例：`tokio::select!` 超时](#422-代码示例tokioselect-超时)
      - [4.2.3 代码示例：概念可取消任务](#423-代码示例概念可取消任务)
    - [4.3 异步锁与同步原语](#43-异步锁与同步原语)
      - [4.3.1 必要性](#431-必要性)
      - [4.3.2 代码示例：`tokio::sync::Mutex`](#432-代码示例tokiosyncmutex)
      - [4.3.3 常见异步原语](#433-常见异步原语)
  - [5. 形式化证明与推理](#5-形式化证明与推理)
    - [5.1 异步执行模型的形式化表示](#51-异步执行模型的形式化表示)
    - [5.2 调度公平性证明](#52-调度公平性证明)
      - [定义：调度策略 D](#定义调度策略-d)
      - [定理：公平性条件](#定理公平性条件)
    - [5.3 活性与安全性保证](#53-活性与安全性保证)
      - [5.3.1 Waker 正确性定理](#531-waker-正确性定理)
      - [5.3.2 异步执行安全性](#532-异步执行安全性)
  - [6. 总结](#6-总结)

## 思维导图 (Text)

```text
Rust异步编程详解 (基于view02.md)
├── 1. 基本概念
│   ├── 1.1 异步编程简介 (定义, 对比, Rust目标)
│   ├── 1.2 Future 特质 (核心定义, Trait, Poll, 形式化, 特点, 示例)
│   └── 1.3 async/await 语法 (定义, 作用, 形式化语义, 示例)
├── 2. 原理与机制
│   ├── 2.1 状态机转换 (核心机制, 转换过程, 示例状态机, 特性, 形式化)
│   ├── 2.2 Pin与内存安全 (问题背景, 示例, Pin定义/API, 与Future关系, 形式化)
│   └── 2.3 Waker与任务唤醒 (核心概念, Context/Waker, 流程, 示例, 形式化)
├── 3. 执行器与运行时
│   ├── 3.1 执行器工作原理 (角色, 概念实现, 形式化, 设计考量)
│   └── 3.2 异步运行时对比 (定义, 对比表, 选择考量)
├── 4. 高级特性与应用
│   ├── 4.1 异步流 (Stream) (定义, Trait, 示例)
│   ├── 4.2 取消与超时 (概念, select!示例, CancellableTask示例)
│   └── 4.3 异步锁与同步原语 (必要性, Mutex示例, 常见原语)
├── 5. 形式化证明与推理
│   ├── 5.1 形式化表示 (操作语义 Poll/Schedule)
│   ├── 5.2 调度公平性证明 (策略定义, 公平性定理)
│   └── 5.3 活性与安全性保证 (Waker正确性, Send/Sync/Drop/Lifetimes)
└── 6. 总结
```

---

## 1. 基本概念

### 1.1 异步编程简介

#### 定义

异步编程是一种并发编程范式，允许程序在执行一个可能耗时较长（通常是 I/O 操作，如网络请求、磁盘读写）的操作时，不必阻塞当前执行线程，而是可以切换去处理其他任务。当该耗时操作完成时，程序会收到通知并可以回来继续处理该操作的结果。

#### 与同步/线程/回调对比

| 模型       | 优点                                       | 缺点                                            |
| ---------- | ------------------------------------------ | ----------------------------------------------- |
| 同步       | 编程模型简单，逻辑清晰                     | 阻塞线程，并发能力差，资源利用率低              |
| 多线程     | 利用多核实现真并行，概念相对直接           | 资源开销大 (线程栈)，上下文切换成本高，易数据竞争 |
| 回调       | 非阻塞，资源开销小                         | 回调地狱 (Callback Hell)，代码难以理解和维护     |
| **Rust 异步** | **非阻塞，资源开销小，高性能 I/O，内存安全** | **学习曲线陡峭，需要运行时，调试相对复杂**        |

#### Rust 的目标

Rust 的异步模型旨在提供：

1. **零成本抽象 (Zero-Cost Abstraction)**：尽可能减少异步机制本身的运行时开销，使得性能接近手动编写的高效状态机代码。
2. **内存安全 (Memory Safety)**：利用 Rust 的所有权和借用系统，在编译时防止数据竞争，即使在复杂的并发场景下。
3. **人体工程学 (Ergonomics)**：通过 `async`/`await` 语法，提供类似同步代码的编程体验，避免回调地狱。

### 1.2 Future 特质

#### 核心定义

`Future` 是 Rust 异步编程的**核心抽象**。它代表一个**可能尚未完成的异步计算**或操作。`Future` 本身是惰性的，它描述了计算过程，但直到被执行器 (Executor) **轮询 (poll)** 时才会实际执行。

#### `Future` Trait 定义

```rust
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait Future {
    // Future 完成时产生的输出值的类型
    type Output;

    // 尝试推进 Future 的计算
    // self: Pin<&mut Self> 保证 Future 在 poll 期间不会被移动内存地址
    // cx: 包含 Waker 的上下文，用于 Future 在 Pending 时注册唤醒通知
    // 返回值 Poll<Self::Output>: 表示 Future 当前的状态
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

#### `Poll` 枚举

`Poll<T>` 枚举表示 `Future` 在一次 `poll` 调用后的状态：

```rust
pub enum Poll<T> {
    // Future 已经成功完成，并产生了一个类型为 T 的值
    Ready(T),
    // Future 尚未完成，执行器应该在未来某个时间点再次 poll 它
    // Future 负责在变为 Ready 之前，通过 Context 中的 Waker 通知执行器
    Pending,
}
```

#### 形式化定义尝试

可以将 `Future` 概念化为一个状态机，其行为可以用一个四元组粗略描述：

`Future<T> ≈ (State, Poll<T>, Context, TransitionFunction)`

其中：

- `State`: Future 内部可能的状态集合。
- `Poll<T>`: 可能的轮询结果 (`Ready(T)` 或 `Pending`)。
- `Context`: 包含 `Waker` 的执行上下文。
- `TransitionFunction`: `poll` 方法的核心逻辑，根据当前 `State` 和 `Context` 计算出新的 `State'` 并返回 `Poll<T>`。
    `TransitionFunction: State × Context → (State', Poll<T>)`

#### 核心特点

- **惰性 (Lazy)**：`Future` 在创建时不会执行任何操作，只有当 `poll` 方法被调用时，计算才会推进。
- **可组合 (Composable)**：`Future` 可以被组合（例如，通过 `async`/`await` 或组合子函数）来构建更复杂的异步逻辑流。
- **零开销 (Zero-cost)**：`Future` trait 和 `async/await` 的设计目标是最小化运行时开销。状态机直接在编译时生成，没有虚拟机或解释器成本。

#### 代码示例：`ReadyFuture`

这是一个立即完成的简单 `Future` 实现：

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 一个 Future，它在第一次被 poll 时就立即返回 Ready 状态
struct ReadyFuture<T>(Option<T>); // 使用 Option 确保值只被取出一次

impl<T> ReadyFuture<T> {
    fn new(value: T) -> Self {
        ReadyFuture(Some(value))
    }
}

impl<T> Future for ReadyFuture<T> {
    type Output = T;

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        // 从 Option 中取出值。如果已经是 None，说明 Future 已经被 poll 并完成了。
        match self.0.take() {
            Some(value) => Poll::Ready(value), // 返回 Ready 状态和值
            None => panic!("ReadyFuture polled after completion"), // 不应该在完成后再次 poll
        }
    }
}

// 如何使用 (需要一个执行器来运行)
async fn run_ready() {
    let my_future = ReadyFuture::new(42);
    let result = my_future.await; // .await 会 poll 这个 Future
    println!("ReadyFuture result: {}", result); // 输出 42
}
```

### 1.3 `async`/`await` 语法

#### 定义与作用

`async` 和 `await` 是 Rust 提供的**语法糖 (Syntactic Sugar)**，它们极大地简化了编写和使用 `Future` 的过程，使得异步代码在结构上更接近同步代码。

#### `async fn` / `async {}`

- `async fn`：用于定义一个异步函数。调用 `async fn` 不会立即执行函数体，而是返回一个实现了 `Future` 的匿名类型。函数体内的代码会被编译器转换为这个 `Future` 的状态机逻辑。
- `async {}`：用于创建一个异步代码块。它会立即开始执行，直到遇到第一个 `.await` 点。然后，它返回一个 `Future`，代表块中剩余的计算。

#### `.await` 表达式

- 只能在 `async fn` 或 `async {}` 内部使用。
- 用于等待一个 `Future` 的完成。
- 当对一个 `future` 调用 `.await` 时：
    1. `future.poll()` 被调用。
    2. 如果返回 `Poll::Ready(value)`，则 `.await` 表达式的结果就是 `value`。
    3. 如果返回 `Poll::Pending`，当前的 `async` 函数/块会**暂停**执行（将控制权**让出**给执行器），并保存当前状态。它会在底层的 `Future` 通过 `Waker` 通知执行器准备好后，才可能被恢复执行并再次 `poll`。

#### 形式化语义

文档中给出的形式化语义大致解释了 `async`/`await` 的转换：

- **`async fn` 转换**:
    `⟦async fn f(x: T) → U { e }⟧ = fn f(x: T) → impl Future<Output = U> { async move { ⟦e⟧ } }`
    这表示一个 `async fn` 被转换成一个普通的同步函数，该函数返回一个实现了 `Future` 的类型（通常是一个匿名状态机）。`async move { ... }` 创建了这个状态机实例。`⟦e⟧` 代表对函数体 `e` 的转换。

- **`.await` 转换**:
    `⟦e.await⟧ = match poll(e, cx) { Ready(v) → v, Pending → suspend(cx) and return Pending }`
    这表示 `.await` 表达式会被转换成对 `Future` `e` 的 `poll` 调用。如果 `poll` 返回 `Ready(v)`，表达式的值就是 `v`。如果返回 `Pending`，当前任务会暂停执行 (`suspend(cx)`)，并且当前的 `poll` 调用会向上返回 `Pending`。

#### 代码示例：异步函数

```rust
use std::time::Duration;

// 定义一个异步函数，模拟网络请求
async fn fetch_data(url: &str) -> Result<String, String> {
    println!("Fetching data from {}...", url);
    // 模拟耗时的 I/O 操作
    tokio::time::sleep(Duration::from_secs(1)).await; // 使用 .await 等待 sleep Future 完成
    println!("...Data fetched from {}", url);
    // 实际应用中这里会是网络库的异步调用
    Ok(format!("Data for {}", url))
}

// 在另一个异步函数中使用 .await
async fn process_urls() {
    let url1 = "https://example.com";
    let url2 = "https://anotherexample.org";

    // 调用 fetch_data 并使用 .await 等待结果
    match fetch_data(url1).await {
        Ok(data) => println!("Processing successful: {}", data),
        Err(e) => eprintln!("Error fetching {}: {}", url1, e),
    }

    match fetch_data(url2).await {
        Ok(data) => println!("Processing successful: {}", data),
        Err(e) => eprintln!("Error fetching {}: {}", url2, e),
    }
}

// 运行 (需要 Tokio 运行时)
// #[tokio::main]
// async fn main() {
//     process_urls().await;
// }
```

## 2. 原理与机制

### 2.1 状态机转换原理

#### 核心机制

Rust 编译器是实现 `async`/`await` 的关键。它将 `async fn` 或 `async {}` 块的代码**转换**成一个实现了 `std::future::Future` trait 的**匿名结构体**，这个结构体本质上是一个**状态机**。

#### 转换过程

1. **状态识别**：编译器分析 `async` 代码块，识别出所有的 `.await` 调用点。这些点是 `Future` 可能暂停执行的地方，因此定义了状态机的不同**状态 (State)**。初始状态是函数/块的开始，每个 `.await` 之后是一个新的状态，最终有一个完成状态。
2. **变量捕获**：所有需要在 `.await` 调用之间保持存活的局部变量（包括参数、中间结果、引用等）会被编译器**捕获**并存储为状态机结构体的**成员字段**。
3. **`poll` 方法实现**：编译器为状态机结构体生成 `poll` 方法的实现。这个方法包含一个大的 `match` 语句（或类似的控制流），根据当前状态执行相应的代码片段：
    - 执行代码直到下一个 `.await` 点。
    - 调用内部 `Future` 的 `poll` 方法。
    - 根据内部 `poll` 的结果：
        - 如果 `Ready`，则更新状态机状态到下一个状态，并可能继续执行或返回值。
        - 如果 `Pending`，则保存当前状态，并向上返回 `Pending`。
4. **自引用处理**：如果状态机捕获的变量之间存在引用关系（例如，一个变量是另一个变量的引用），编译器需要确保这些引用在 `Future` 可能被移动时仍然有效。这就是 `Pin` 发挥作用的地方。

#### 代码示例：概念状态机

`view02.md` 中给出的 `ExampleFuture` 是对这个过程的一个很好的概念性展示：

```rust
# // 假设存在以下定义
# use std::future::Future;
# use std::pin::Pin;
# use std::task::{Context, Poll};
# struct AnotherFuture; // 假设这是 another_async_fn 返回的 Future 类型
# impl Future for AnotherFuture { type Output = u32; fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> { Poll::Ready(10) } }
# fn another_async_fn(_x: u32) -> AnotherFuture { AnotherFuture }
# mod ExampleStateMod { // 避免命名冲突
#     use super::*;
    // 对应 async fn example(x: u32) -> u32 { let y = another_async_fn(x).await; y + 1 }
    enum ExampleState {
        Start(u32), // 初始状态，持有参数 x
        WaitingOnAnother { fut: AnotherFuture }, // 等待内部 Future 完成的状态
        Done, // 完成状态
    }

    struct ExampleFuture {
        state: ExampleState,
    }

    impl ExampleFuture {
        fn new(x: u32) -> Self {
            ExampleFuture { state: ExampleState::Start(x) }
        }
    }

    impl Future for ExampleFuture {
        type Output = u32;

        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<u32> {
            // 使用 unsafe 或 pin-project 来安全地获取 &mut self.state
            let this = unsafe { self.get_unchecked_mut() };

            loop { // 使用 loop 来允许状态转换后立即 poll 下一个状态
                match &mut this.state {
                    ExampleState::Start(x) => {
                        // 执行 .await 之前的代码：调用 another_async_fn
                        let fut = another_async_fn(*x);
                        // 转移到下一个状态，保存内部 Future
                        this.state = ExampleState::WaitingOnAnother { fut };
                        // 注意：不立即返回，继续 loop 以 poll 新状态
                    }
                    ExampleState::WaitingOnAnother { fut } => {
                        // 对内部 Future 调用 poll (即 .await 的核心)
                        // 需要 Pin::new(fut).poll(...)，因为 fut 可能也是自引用的
                        match unsafe { Pin::new_unchecked(fut) }.poll(cx) {
                            Poll::Ready(y) => {
                                // 内部 Future 完成，执行 .await 之后的代码 (y + 1)
                                let result = y + 1;
                                // 转移到完成状态
                                this.state = ExampleState::Done;
                                // 返回最终结果
                                return Poll::Ready(result);
                            }
                            Poll::Pending => {
                                // 内部 Future 未完成，向上返回 Pending
                                return Poll::Pending;
                            }
                        }
                    }
                    ExampleState::Done => {
                        // Future 完成后不应该再被 poll
                        panic!("Future polled after completion");
                    }
                }
            }
        }
    }
# }
```

#### 关键特性

- **状态保存 (State Saving)**：局部变量被保存在状态机结构体中，跨越 `await`。
- **断点恢复 (Resumption)**：`poll` 方法能从上次暂停 (`Pending`) 的状态继续执行。
- **效率 (Efficiency)**：编译器直接生成状态机，避免了运行时解释或调度的额外开销（相比某些语言的绿色线程）。

#### 形式化推理：状态转换

状态机的转换可以看作是由 `poll` 驱动的离散事件系统。

- **状态 (State)**: `S = {S_start, S_awaiting_1, ..., S_done}`
- **事件 (Event)**: `E = {Poll(InternalFuture)}` (内部 Future 的轮询结果)
- **转换函数 (Transition)**: `δ: S × E → S`
- **输出函数 (Output)**: `λ: S × E → Poll<Output>`

当 `Executor` 调用 `poll(StateMachine, Context)` 时：

1. 获取当前状态 `s ∈ S`。
2. 执行与 `s` 相关的同步代码。
3. 如果遇到 `await internal_future`：
    a.  调用 `poll(internal_future, Context)`，得到事件 `e ∈ E` (即 `Ready(v)` 或 `Pending`)。
    b.  计算下一状态 `s' = δ(s, e)`。
    c.  计算输出 `p = λ(s, e)`。
    d.  更新状态机状态为 `s'`。
    e.  返回输出 `p`。

这个过程保证了计算的逐步推进，并且只有在所有内部 `Future` 都 `Ready` 时，整个状态机才会最终返回 `Ready`。

### 2.2 `Pin` 与内存安全

#### 问题背景：自引用结构

在异步编程中，生成的 `Future` 状态机常常需要包含**自引用 (Self-Referential)** 结构。这意味着状态机结构体内部的一个字段（通常是一个引用或指针）指向了同一结构体内部的另一个字段。

#### 代码示例：自引用结构问题

```rust
async fn self_referential_example() {
    let mut data = [0u8; 10]; // 数据存储在 Future 的状态机中
    // 创建一个指向 data 的引用，这个引用也存储在状态机中
    let slice: &[u8] = &data[0..5];

    // 假设这里有一个 .await 点
    // 如果 Future 在 await 期间被移动了内存位置 (e.g., 从栈移到堆，或在 Vec 中移动)
    // 那么 slice 就会变成一个悬垂引用，指向旧的、无效的内存地址！
    some_async_operation().await;

    println!("Slice: {:?}", slice); // 可能导致未定义行为 (UB)
}
# async fn some_async_operation() {} // 辅助函数
```

#### `Pin` 的定义与作用

`Pin<P>` (其中 `P` 是某种指针类型，如 `&mut T`, `Box<T>`) 是 Rust 类型系统提供的一种机制，用于**保证**其指向的数据 `T` 在内存中的位置**不会被移动**（除非 `T` 显式标记为 `Unpin`）。

- **核心保证**：如果一个值被 `Pin` 包裹，你不能轻易地获得它的所有权或可变引用来移动它。
- **`Unpin` Trait**：这是一个自动 trait (auto trait)，大多数类型（如 `i32`, `String`, `Vec<T>`）默认实现 `Unpin`。如果一个类型 `T` 是 `Unpin`，意味着移动它总是安全的，因此 `Pin` 对它不起实际的固定作用。对于包含自引用的状态机，编译器通常会使其**不是 `Unpin`**。

#### `Pin` 的核心 API

```rust
use std::ops::{Deref, DerefMut};
use std::marker::PhantomData; // Unpin 不是必须的，但加在这里示意

pub struct Pin<P> {
    pointer: P,
    // _marker: PhantomPinned, // 实际实现中有 PhantomPinned 标记
}

impl<P: Deref> Pin<P> {
    // 可以安全地获取不可变引用，因为这不会导致移动
    pub fn as_ref(&self) -> Pin<&P::Target> { /* ... */ }
    // Deref trait 实现，允许通过 &pin 访问 &T
    // fn deref(&self) -> &P::Target { self.pointer.deref() }
}

impl<P: DerefMut> Pin<P> {
    // 可以安全地获取可变引用，因为这不会导致移动
    pub fn as_mut(&mut self) -> Pin<&mut P::Target> { /* ... */ }

    // 关键：只有当 T 是 Unpin 时，才能安全地从 Pin<P<T>> 获取 &mut T
    // 因为 Unpin 类型移动是安全的，所以固定没有意义，可以解开 Pin
    pub fn get_mut(self) -> P where P::Target: Unpin {
        self.pointer
    }

    // 对于 !Unpin 的类型，直接获取 &mut T 是 unsafe 的，需要特殊方法
    // pub unsafe fn get_unchecked_mut(self) -> P { self.pointer }
}
```

#### `Pin` 与 `Future`

`Future::poll` 方法的签名是 `fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;`

- 接收 `Pin<&mut Self>` 而不是 `&mut Self`，正是为了确保 `Future` 状态机在 `poll` 调用期间不会被移动。
- 这允许 `poll` 方法内部安全地操作可能存在的自引用。
- 获取状态机内部字段的可变引用通常需要 `unsafe` 代码或者像 `pin-project` 这样的库来保证不违反 `Pin` 的约束（即不移动被固定的数据）。

#### 形式化推理：`Pin` 的保证

令 `addr(x)` 表示变量 `x` 的内存地址。

1. **Rust 的移动语义**：`let y = x;` 可能导致 `addr(y) ≠ addr(x_old)`。
2. **自引用结构**：存在结构体 `S` 包含字段 `f` 和 `ptr`，使得 `addr(*ptr) == addr(f)` 或 `addr(f) <= addr(*ptr) < addr(f) + size_of_val(f)`。
3. **问题**：如果移动 `S` 到新地址 `addr(S')`，则 `addr(S'.f)` 改变，但 `S'.ptr` 仍然指向旧的 `addr(f)`，导致 `ptr` 无效。
4. **`Pin` 的保证**：如果 `p = Pin::new(&mut s)` 或 `p = Box::pin(s)` 且 `S: !Unpin`，则 Rust 保证在 `p` 的生命周期内，`addr(s)` **不会改变**。
5. **推论**：由于 `addr(s)` 不变，`addr(s.f)` 也不变。因此，即使 `s` 包含自引用 `s.ptr`，该引用将始终保持有效。
6. **`poll` 的安全性**：因为 `poll` 接收 `Pin<&mut Self>`，执行器保证了 `Future` 在 `poll` 期间地址不变，从而允许状态机安全地处理内部自引用。

### 2.3 `Waker` 与任务唤醒

#### 核心概念

当一个 `Future` 在 `poll` 时无法立即完成（例如，等待网络数据到达或定时器触发），它需要一种机制来通知执行器它**稍后可能**准备好继续执行。`Waker` 就是这个通知机制。

#### `Context` 与 `Waker`

`Future::poll` 方法接收一个 `Context<'_>` 参数。`Context` 主要的作用是**携带**与当前正在被 `poll` 的任务相关联的 `Waker`。

```rust
use std::task::Waker;

pub struct Context<'a> {
    waker: &'a Waker,
    // Context 还可以携带其他上下文信息，但 Waker 是核心
    // _marker: PhantomData<&'a ()>,
}

impl<'a> Context<'a> {
    pub fn from_waker(waker: &'a Waker) -> Context<'a> {
        Context { waker }
    }
    pub fn waker(&self) -> &'a Waker {
        self.waker
    }
}

// Waker 本身是一个轻量级句柄，内部包含如何唤醒特定任务的信息
// 它通常包含一个指向任务状态的指针和一个函数指针（vtable）
pub struct Waker {
    // 内部实现细节，通常包含 RawWaker
    // raw_waker: RawWaker,
}

// RawWaker 包含数据指针和 vtable (函数指针表)
// pub struct RawWaker {
//     data: *const (),
//     vtable: &'static RawWakerVTable,
// }
// pub struct RawWakerVTable {
//     clone: unsafe fn(*const ()) -> RawWaker,
//     wake: unsafe fn(*const ()),
//     wake_by_ref: unsafe fn(*const ()),
//     drop: unsafe fn(*const ()),
// }

impl Waker {
    // 消耗 Waker 并唤醒任务
    pub fn wake(self) {
        // 内部调用 vtable 中的 wake 函数
        // (self.raw_waker.vtable().wake)(self.raw_waker.data());
    }
    // 不消耗 Waker，仅唤醒任务（用于多次唤醒或共享 Waker）
    pub fn wake_by_ref(&self) {
        // 内部调用 vtable 中的 wake_by_ref 函数
        // (self.raw_waker.vtable().wake_by_ref)(self.raw_waker.data());
    }
    // Waker 可以被克隆，以便在多个地方注册
    // impl Clone for Waker { ... }
}
```

#### 唤醒机制流程

1. **执行器调用 `poll`**：执行器选择一个任务，为其创建一个 `Waker`，并调用 `Future::poll(self, &mut Context::from_waker(&waker))`。
2. **`Future` 返回 `Pending`**：如果 `Future` 无法立即完成，它需要：
    a.  **保存 `Waker`**：克隆 `Context` 中的 `waker` (`cx.waker().clone()`) 并将其存储起来，通常与它正在等待的资源关联（例如，在 I/O 事件监听器中注册回调，回调函数持有这个 `Waker`）。
    b.  返回 `Poll::Pending`。
3. **资源就绪**：当等待的外部事件发生时（例如，socket 变为可读、定时器到期），与该事件关联的代码（通常是运行时的一部分）会调用之前保存的 `Waker` 的 `wake()` 或 `wake_by_ref()` 方法。
4. **`Waker::wake()` 执行**：`wake()` 方法的实现（由执行器提供）通常会将关联的任务标记为“就绪”，并将其放回执行器的待运行队列中。
5. **执行器再次 `poll`**：执行器在未来的某个时间点会从队列中取出这个就绪的任务，并再次调用它的 `poll` 方法，从而允许 `Future` 继续执行。

#### 代码示例：概念 `Waker` 创建

（展示如何在执行器中创建 `Waker`，基于 `MiniExecutor` 示例）

```rust
# // 假设存在以下定义
# use std::future::Future;
# use std::pin::Pin;
# use std::task::{Context, Poll, Wake, Waker};
# use std::sync::{Arc, Mutex};
# use std::collections::VecDeque;
# struct Task {
#     future: Mutex<Pin<Box<dyn Future<Output = ()> + Send>>>,
#     task_queue: Arc<Mutex<VecDeque<Arc<Task>>>>,
# }
# impl Wake for Task { fn wake(self: Arc<Self>) { self.task_queue.lock().unwrap().push_back(self.clone()); } }
# struct MiniExecutor { task_queue: Arc<Mutex<VecDeque<Arc<Task>>>> }
# impl MiniExecutor {
#     fn run(&self) {
#         loop {
#             let task = { /* ... 获取任务 ... */
#                 let mut queue = self.task_queue.lock().unwrap();
#                 if queue.is_empty() { break; }
#                 queue.pop_front().unwrap()
#             };
#             let future_lock = task.future.lock().unwrap(); // Moved lock acquisition earlier
            // --- Waker 创建 ---
            // 1. 从任务本身（或其句柄）创建 Waker
            //    这通常需要实现 Wake trait for Arc<Task>
            //    Waker::from(task.clone()) 利用了 Wake trait 的实现
            let waker = Waker::from(task.clone()); // `task` 是 Arc<Task>

            // 2. 从 Waker 创建 Context
            let mut context = Context::from_waker(&waker);
            // --- 结束 Waker 创建 ---

            // 3. 将 Context 传递给 poll
            if let Poll::Pending = future_lock.as_mut().poll(&mut context) {
                // 如果返回 Pending，Waker 已经被 Future (理论上) 保存了
            }
#         }
#     }
# }

// Wake trait 的实现 (关键部分)
// impl Wake for Task {
//     fn wake(self: Arc<Self>) {
//         // wake 的核心逻辑：将任务重新放入执行器的队列
//         self.task_queue.lock().unwrap().push_back(self.clone());
//     }
// }
```

#### 形式化推理：`Waker` 的契约

`Waker` 提供了一个关于异步进展的关键契约：

1. **活性保证 (Liveness)**：如果一个 `Future` 返回 `Poll::Pending` 并正确注册了 `Waker`，那么当它等待的事件发生时，**最终**会调用 `Waker::wake()`（或 `wake_by_ref()`）。
2. **调度保证 (Scheduling)**：如果 `Waker::wake()` 被调用，那么执行器**最终**会再次 `poll` 与该 `Waker` 相关联的 `Future`（除非该 `Future` 已经被丢弃或完成了）。
3. **幂等性 (Idempotence, for wake)**：多次调用 `wake()` 应该与调用一次效果相同（即任务被标记为就绪一次）。执行器需要处理重复唤醒的情况。

这个契约确保了返回 `Pending` 的 `Future` 不会被永久遗忘，保证了异步任务的最终进展（如果外部事件确实发生）。

## 3. 执行器与运行时

### 3.1 执行器的工作原理

#### 3.1.1 角色定义

**执行器 (Executor)** 是 Rust 异步编程的核心驱动力。它的主要职责是：

1. **接收任务 (Task)**：接受表示顶层异步计算的 `Future`（通常包装在一个任务结构中）。
2. **调度任务 (Scheduling)**：决定哪个任务应该在何时运行。这可能基于简单的队列、优先级、或更复杂的策略如工作窃取 (Work-Stealing)。
3. **轮询 Future (Polling)**：调用任务的 `Future::poll` 方法来推进其计算。
4. **处理唤醒 (Waking)**：管理 `Waker`，并在 `Waker` 被调用时将相应的任务重新加入调度队列。

#### 3.1.2 基本实现流程 (概念代码)

`view02.md` 中提供的 `MiniExecutor` 是一个极简执行器的示例：

```rust
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Wake, Waker};

// 任务结构，包含 Future 和指向任务队列的引用 (用于 Waker)
struct Task {
    future: Mutex<Pin<Box<dyn Future<Output = ()> + Send>>>, // Future 本身
    task_queue: Arc<Mutex<VecDeque<Arc<Task>>>>, // 用于 Wake 实现
}

// 实现 Wake trait，定义 Waker::wake() 的行为
impl Wake for Task {
    fn wake(self: Arc<Self>) {
        // 最简单的 wake 实现：将任务自身 (Arc<Task>) 放回队列
        self.task_queue.lock().unwrap().push_back(self.clone());
    }
    // wake_by_ref 可以类似实现，不消耗 Arc
}

// 最小化执行器
struct MiniExecutor {
    // 存储待运行任务的队列
    task_queue: Arc<Mutex<VecDeque<Arc<Task>>>>,
}

impl MiniExecutor {
    fn new() -> Self {
        MiniExecutor {
            task_queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    // 用于向执行器提交新任务
    fn spawn<F>(&self, future: F)
    where
        F: Future<Output = ()> + Send + 'static, // Future 必须 Send + 'static
    {
        // 创建 Task 结构
        let task = Arc::new(Task {
            future: Mutex::new(Box::pin(future)), // 将 Future Pin 住并放入 Box
            task_queue: Arc::clone(&self.task_queue),
        });

        // 将新任务加入队列
        self.task_queue.lock().unwrap().push_back(task);
    }

    // 运行执行器的主循环
    fn run(&self) {
        loop {
            // 1. 从队列获取下一个任务
            let task = { // 使用块来限制锁的范围
                let mut queue = self.task_queue.lock().unwrap();
                if let Some(task) = queue.pop_front() {
                    task // 返回任务
                } else {
                    // 如果队列为空，可以简单退出，或更复杂地等待新任务/事件
                    break; // 简单退出
                    // 实际执行器会在这里集成 I/O 事件轮询 (epoll_wait, etc.)
                }
            };

            // 2. 为任务创建 Waker 和 Context
            let waker = Waker::from(task.clone()); // 利用 Wake trait 实现
            let mut context = Context::from_waker(&waker);

            // 3. 轮询 Future
            let mut future_lock = task.future.lock().unwrap(); // 获取 Future 的锁
            // 调用 poll 方法
            if let Poll::Pending = future_lock.as_mut().poll(&mut context) {
                // Future 返回 Pending:
                // - Waker (理论上) 已被 Future 内部注册。
                // - 任务暂时挂起，等待 Waker 被调用。
                // - 执行器继续循环处理下一个任务。
                // 注意：这个简单的执行器不会将 Pending 的任务放回队列，
                // 它依赖 Waker::wake() 将其重新加入。
            } else {
                // Future 返回 Ready:
                // - 任务已完成。
                // - 这个简单的执行器不需要做特殊处理，任务不会再被放回队列。
            }
            // 锁在这里释放
        }
    }
}

// 使用示例
// fn main() {
//     let executor = MiniExecutor::new();
//     executor.spawn(async { println!("Task 1"); });
//     executor.spawn(async { println!("Task 2"); });
//     executor.run(); // 运行执行器直到队列为空
// }
```

#### 3.1.3 形式化推理：执行器的进展保证

执行器通过 `poll` 和 `wake` 机制保证了任务的活性（最终会进展）：

1. **前提**：假设 `Future` 正确实现了 `poll`（即在返回 `Pending` 前注册了 `Waker`）并且外部事件源最终会调用 `wake`。
2. **执行器循环不变式 (Loop Invariant)**：在 `run` 循环的每次迭代开始时，`task_queue` 包含所有当前已就绪（或新提交）的任务。
3. **进展步骤**：
    - 如果任务 `poll` 返回 `Ready`，任务完成，从系统中移除。
    - 如果任务 `poll` 返回 `Pending`，任务暂时从活动执行中移除。
    - 当 `Waker::wake()` 被调用时，根据 `Wake` trait 实现，任务被重新加入 `task_queue`。
4. **结论**：只要存在就绪任务或有 `Waker` 被调用，执行器的 `run` 循环就能持续从队列中获取任务并 `poll` 它们，从而保证了系统的整体进展。

#### 3.1.4 关键设计考量

真实的执行器比 `MiniExecutor` 复杂得多，需要考虑：

- **调度策略 (Scheduling Strategy)**：
  - FIFO (先进先出)：简单，但可能导致长任务阻塞短任务。
  - 优先级调度：允许高优先级任务抢先执行。
  - 工作窃取 (Work-Stealing)：用于多线程执行器，空闲线程从其他忙碌线程的队列中“窃取”任务，提高负载均衡和 CPU 利用率。
- **I/O 事件集成 (Reactor)**：执行器需要与操作系统的 I/O 事件通知机制（如 epoll, kqueue, IOCP, io_uring）集成。当没有就绪任务时，执行器会阻塞等待 I/O 事件，而不是忙等。事件发生后，相关的 `Waker` 被调用，任务变为就绪。
- **定时器管理 (Timers)**：提供异步定时器功能（如 `tokio::time::sleep`）。
- **任务生命周期管理**：处理任务的取消、panic 等。
- **线程池管理**：对于多线程执行器，需要管理工作线程的创建、销毁和同步。

### 3.2 异步运行时对比

#### 3.2.1 运行时定义

**异步运行时 (Async Runtime)** 通常不仅仅是一个执行器，它是一个**完整的异步编程环境**，通常包含：

1. **执行器 (Executor)**：负责调度和运行异步任务。
2. **I/O 反应器 (Reactor)**：与操作系统交互，监听网络、文件、定时器等 I/O 事件，并在事件就绪时唤醒相应的任务。
3. **异步 API 封装**：提供易于使用的异步版本的标准库功能（如文件读写 `tokio::fs`，网络 `tokio::net`，定时器 `tokio::time`）。
4. **同步原语**：提供异步版本的锁、通道等 (`tokio::sync`)。
5. **任务生成工具**：如 `tokio::spawn`。

#### 3.2.2 主流运行时对比表

| 特性 | Tokio | async-std | smol | monoio |
| :---- | :---- | :---- | :---- | :----- |
| **架构** | 多线程工作窃取 | 多线程固定线程池 | 轻量多线程/可配置 | 单线程 (per-core) |
| **I/O 模型** | 基于 epoll/kqueue/IOCP 等 | 基于 epoll/kqueue/IOCP 等 | 基于 `polling` 库 (跨平台) | 基于 `io_uring` (Linux) |
| **内存开销** | 中等 | 中等 | 低 | 极低 |
| **特化优化** | 网络应用，高性能 | 类 `std` API 风格，易用性 | 小型应用，模块化，嵌入式 | 极高性能 I/O，特定场景 |
| **生态系统** | **最广泛** | 良好 | 适中 | 新兴，专注 io_uring |
| **主要场景** | Web 服务器，网络客户端 | 通用异步应用 | 嵌入式，需要定制运行时 | 需要极限 I/O 性能的 Linux 应用 |

#### 3.2.3 选择考量

选择哪个运行时取决于具体需求：

- **需要强大的网络功能和最广泛的库支持？** -> **Tokio** 通常是首选。
- **偏好与标准库 `std` 类似的 API 体验？** -> **async-std** 是个不错的选择。
- **需要一个轻量级、模块化、或嵌入式友好的运行时？** -> **smol** 及其相关库值得考虑。
- **目标平台是 Linux 且追求极致 I/O 性能？** -> **monoio** 可能提供优势（但生态较新）。
- **通常不建议在一个项目中混合使用不同运行时的 I/O 类型或执行器**，因为它们通常不兼容。

## 4. 高级特性与应用

### 4.1 异步流 (`Stream`)

#### 4.1.1 定义

`Stream` trait 是 `Future` 在处理**一系列**异步产生的值时的对应概念。它类似于同步世界中的 `Iterator`，但其 `next` 操作是异步的。

#### 4.1.2 `Stream` Trait 定义

```rust
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait Stream {
    // Stream 产生的元素的类型
    type Item;

    // 尝试从流中获取下一个元素
    // 返回 Poll<Option<Self::Item>>:
    // - Poll::Ready(Some(item)): 成功获取下一个元素 item
    // - Poll::Ready(None): 流已经结束
    // - Poll::Pending: 当前没有可用的元素，但流尚未结束，需要稍后重试
    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>>;

    // Stream trait 还提供了 size_hint 等可选方法
}
```

#### 4.1.3 代码示例：消费 Stream

通常使用 `futures` crate（或运行时提供的封装）中的 `StreamExt` trait 来方便地处理 `Stream`。

```rust
use futures::stream::{self, StreamExt}; // 需要添加 futures = "0.3" 依赖

async fn process_stream() {
    // 创建一个简单的数字流 (0, 1, 2)
    let mut number_stream = stream::iter(0..3);

    // 使用 while let 和 .next().await 来异步地迭代流
    // .next() 来自 StreamExt trait
    println!("Processing stream:");
    while let Some(number) = number_stream.next().await {
        println!("Got number: {}", number);
        // 模拟异步处理每个元素
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    }
    println!("Stream finished.");
}

// 运行 (需要 Tokio 运行时 和 futures crate)
// #[tokio::main]
// async fn main() {
//     process_stream().await;
// }
```

`Stream` 对于处理如网络数据块、数据库结果集、事件队列等场景非常有用。

### 4.2 取消与超时

#### 4.2.1 概念

在异步编程中，能够**取消**不再需要的任务或为操作设置**超时**是非常重要的。

- **超时 (Timeout)**：限制一个异步操作必须在指定时间内完成。
- **取消 (Cancellation)**：主动停止一个正在运行或等待的异步任务。Rust 的 `Future` 被丢弃 (drop) 时，其计算通常也就停止了（尽管底层操作可能仍在进行，需要正确处理）。

#### 4.2.2 代码示例：`tokio::select!` 超时

`tokio::select!` 宏是实现超时和处理多个 `Future` 竞争完成的常用方式。

```rust
use tokio::time::{sleep, Duration};

// 模拟一个可能耗时很长的操作
async fn long_running_task() -> Result<String, String> {
    println!("Long task started...");
    sleep(Duration::from_secs(5)).await; // 模拟 5 秒操作
    println!("Long task finished normally.");
    Ok("Task completed".to_string())
}

async fn task_with_timeout() {
    let timeout_duration = Duration::from_secs(2); // 设置 2 秒超时

    println!("Running task with timeout ({}s)...", timeout_duration.as_secs());

    // tokio::select! 会同时运行内部的 Future
    // 哪个 Future 先完成，对应的分支就会被执行，其他 Future 会被取消 (drop)
    tokio::select! {
        // 分支 1: 运行 long_running_task
        result = long_running_task() => {
            match result {
                Ok(data) => println!("Task succeeded: {}", data),
                Err(e) => println!("Task failed: {}", e),
            }
        }
        // 分支 2: 等待超时
        _ = sleep(timeout_duration) => {
            println!("Task timed out after {} seconds!", timeout_duration.as_secs());
        }
    }
}

// 运行 (需要 Tokio 运行时)
// #[tokio::main]
// async fn main() {
//     task_with_timeout().await;
// }
// 预期输出会是 "Task timed out..." 因为 long_running_task 需要 5 秒
```

#### 4.2.3 代码示例：概念可取消任务

可以通过共享状态（如 `AtomicBool`）来实现更精细的任务取消。

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use tokio::time::{sleep, Duration};

// 模拟一个可以被外部取消的任务
async fn cancellable_task(cancel_flag: Arc<AtomicBool>) {
    println!("Cancellable task started. Working...");
    for i in 0..10 {
        // 在执行工作的关键点检查取消标志
        if cancel_flag.load(Ordering::Relaxed) {
            println!("Task cancelled at step {}!", i);
            return; // 提前退出
        }

        println!("Working on step {}...", i);
        // 模拟工作和可能的 await 点
        sleep(Duration::from_millis(300)).await;
    }
    println!("Cancellable task finished normally.");
}

async fn run_cancellation() {
    // 创建取消标志
    let cancel_flag = Arc::new(AtomicBool::new(false));
    let flag_clone = cancel_flag.clone(); // 克隆 Arc 给任务

    // 启动可取消任务
    let task_handle = tokio::spawn(cancellable_task(flag_clone));

    // 让任务运行一段时间
    sleep(Duration::from_secs(1)).await;

    // 发出取消信号
    println!(">>> Sending cancellation signal <<<");
    cancel_flag.store(true, Ordering::Relaxed);

    // 等待任务结束 (无论是否被取消)
    let _ = task_handle.await;
    println!("Cancellation demo finished.");
}

// 运行 (需要 Tokio 运行时)
// #[tokio::main]
// async fn main() {
//     run_cancellation().await;
// }
```

### 4.3 异步锁与同步原语

#### 4.3.1 必要性

在异步代码中直接使用标准库的同步原语（如 `std::sync::Mutex`）通常是**不推荐**的，因为当它们发生阻塞时（例如，等待锁），它们会**阻塞整个 OS 线程**，这与异步编程的目标（避免阻塞线程）相悖。如果执行器线程被阻塞，它就无法去轮询其他就绪的任务。

因此，异步运行时（如 Tokio, async-std）提供了**异步版本**的同步原语。这些原语在需要等待时，会返回 `Pending` 并注册 `Waker`，从而允许执行器切换到其他任务，而不是阻塞线程。

#### 4.3.2 代码示例：`tokio::sync::Mutex`

```rust
use std::sync::Arc;
use tokio::sync::Mutex; // 使用 Tokio 的异步 Mutex
use tokio::time::{sleep, Duration};

// 共享状态，需要 Arc 和 Mutex
struct SharedState {
    counter: u32,
}

// 异步任务，访问共享状态
async fn task_accessing_shared_state(state: Arc<Mutex<SharedState>>, id: u32) {
    println!("Task {} trying to acquire lock...", id);
    // 异步地获取锁，如果锁不可用，任务会暂停 (yield) 而非阻塞线程
    let mut locked_state = state.lock().await;
    println!("Task {} acquired lock.", id);

    // 访问和修改共享状态
    locked_state.counter += 1;
    let current_count = locked_state.counter;
    println!("Task {} updated counter to: {}", id, current_count);

    // 模拟持有锁时的一些工作
    sleep(Duration::from_millis(100 * id as u64)).await;

    println!("Task {} releasing lock.", id);
    // MutexGuard 在离开作用域时自动释放锁 (locked_state 被 drop)
}

async fn run_async_mutex() {
    let shared_state = Arc::new(Mutex::new(SharedState { counter: 0 }));

    let mut handles = vec![];
    for i in 1..=3 {
        let state_clone = Arc::clone(&shared_state);
        // 启动多个并发任务访问同一状态
        let handle = tokio::spawn(task_accessing_shared_state(state_clone, i));
        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        let _ = handle.await;
    }

    // 检查最终状态
    let final_state = shared_state.lock().await;
    println!("Final counter value: {}", final_state.counter); // 应该是 3
}

// 运行 (需要 Tokio 运行时)
// #[tokio::main]
// async fn main() {
//     run_async_mutex().await;
// }
```

#### 4.3.3 常见异步原语

异步运行时通常提供以下原语的异步版本：

- `Mutex`: 异步互斥锁。
- `RwLock`: 异步读写锁。
- `Semaphore`: 异步信号量，用于限制并发访问数量。
- `Notify`: 异步通知机制，允许任务等待某个事件发生（类似条件变量）。
- `Barrier`: 异步屏障，允许多个任务相互等待直到所有任务都到达屏障点。
- Channels (`oneshot`, `mpsc`, `broadcast`, `watch`): 用于任务间异步通信的各种通道类型。

## 5. 形式化证明与推理

本节回顾并解释 `view02.md` 中提到的形式化概念，以更严谨地理解 Rust 异步模型。

### 5.1 异步执行模型的形式化表示

文档中给出的操作语义是对 `poll` 和执行器调度行为的一种简化描述：

- **`Poll(F)` 语义**:
    `Poll(F) = { match F with | Ready(v) => return v | Pending => register_waker() and yield end }`
  - **解释**: 这描述了对 `Future` F 进行 `poll` 的操作。如果 `Future` 已经 `Ready` 并有结果 `v`，则返回 `v`。如果 `Future` 是 `Pending`，则（隐含地）假定 `Future` 内部会注册 `Waker`，然后当前执行流程**让出 (yield)** 控制权。

- **`Schedule(T)` 语义**:
    `Schedule(T) = { while !Empty(ReadyQueue) do t = Dequeue(ReadyQueue); result = Poll(t); if result == Pending then /* 任务注册了 Waker */ else /* 任务完成 */ end }`
  - **解释**: 这描述了执行器 `T` 的基本调度循环。只要就绪队列 `ReadyQueue` 不为空，就取出一个任务 `t` 并 `Poll` 它。如果结果是 `Pending`，则（根据 `Poll(F)` 的语义）任务已经注册了 `Waker`，等待被唤醒；执行器继续处理下一个任务。如果结果是 `Ready`，则任务完成。这个模型简化了 `Waker` 被调用后任务如何回到 `ReadyQueue` 的过程。

这些形式化表示有助于理解 `poll`/`yield`/`schedule` 的核心交互，但省略了许多细节（如 `Context`, `Pin`, `Waker` 的具体创建和传递、错误处理、任务生命周期等）。

### 5.2 调度公平性证明

公平性是调度算法的重要属性，保证没有任务会被无限期地“饿死”。

#### 定义：调度策略 D

`D: 2^T × H → T`

- `T`: 所有任务的集合。
- `2^T`: 当前就绪任务的集合（T 的幂集）。
- `H`: 任务执行的历史信息（可选，用于更复杂的调度）。
- `D`: 调度函数，根据当前就绪任务集和历史，选择下一个要执行的任务 `t ∈ T`。

#### 定理：公平性条件

`∀t∈T. (∃n∈ℕ. ∀h∈H_{>=t_0}. |{t'∈ready(h) | priority(t') > priority(t)}| < n) ⇒ ◇scheduled(t)`

- **解释**: 对于系统中的**任何**任务 `t`：
  - **如果** (`⇒` 左侧)：存在一个时刻 `t_0` 之后，对于所有的执行历史 `h`，优先级高于 `t` 的就绪任务的数量 `|...|` 有一个**上界 `n`**（即不会有无限多更高优先级的任务持续插队）...
  - **那么** (`⇒` 右侧)：任务 `t` **最终 (`◇`) 会被调度执行 (`scheduled(t)`)**。
- **意义**: 这个定理形式化了“只要高优先级任务的干扰是有限的，低优先级任务最终也能得到执行机会”的直觉概念。一个公平的调度器必须满足此属性。简单 FIFO 调度通常是公平的（如果所有任务都会最终完成或让出）。优先级抢占调度需要额外机制（如优先级老化）来保证公平性。

### 5.3 活性与安全性保证

#### 5.3.1 Waker 正确性定理

1. **`wake(w)` ⇒ ◇`poll(task(w))`**: 如果 `Waker w` 被调用，那么与 `w` 关联的任务 `task(w)` 最终会被执行器再次轮询（假设任务未被丢弃）。
2. **`wake(clone(w))` ≡ `wake(w)`**: 克隆出的 `Waker` 具有与原始 `Waker` 相同的唤醒效果。

这个定理是保证异步系统不会死锁或丢失唤醒信号的基础。

#### 5.3.2 异步执行安全性

Rust 的核心优势在于其**编译时安全保证**，这些保证同样适用于异步代码：

1. **数据竞争避免 (Data Race Freedom)**：
    - `Future` 要在多线程执行器间移动，必须是 `Send`。这意味着 `Future` 状态机捕获的所有数据要么是 `Send`（所有权转移或 `Copy`），要么是通过 `&T` 共享且 `T: Sync`。
    - 对于跨 `await` 共享的可变状态，必须使用线程安全的同步原语（如 `Arc<Mutex<T>>` 且 `T: Send`），Rust 的类型系统会强制检查这一点。
    - **形式化意义**：确保了即使在并发执行和任务切换的情况下，也满足 Rust 的基本借用规则（任一时刻要么一个可变借用，要么多个不可变借用）。

2. **资源管理 (Resource Management)**：
    - `Future` 也是值，遵循 Rust 的所有权和生命周期规则。
    - 当 `Future`（或持有它的任务）被丢弃 (`drop`) 时，其内部状态（捕获的变量）也会被正确地 `drop`，确保资源（如文件句柄、网络连接、内存）被释放。
    - **形式化意义**：保证了即使在复杂的异步控制流（如取消、超时）下，RAII (Resource Acquisition Is Initialization) 原则依然有效。

3. **内存安全 (Memory Safety)**：
    - `Pin` 机制防止了自引用状态机移动导致的悬垂指针。
    - 所有权和生命周期系统防止了 use-after-free 和 double-free 等问题。
    - **形式化意义**：保证了即使 `Future` 的执行在时间上是不连续的（由于 `await` 暂停），其内部状态和引用的内存访问始终是有效的。

这些安全性保证是 Rust 异步区别于其他语言（如 C++ 手动管理或依赖 GC 的语言）的关键优势。

## 6. 总结

通过对 `view02.md` 的详细展开，我们可以更深入地理解 Rust 异步编程的精妙设计与内在机制：

- **核心抽象**：`Future` trait 定义了异步计算单元，`Poll` 枚举表示其状态。
- **易用性**：`async`/`await` 语法糖将复杂的异步逻辑转换为直观的状态机。
- **内存安全**：`Pin` 机制解决了自引用状态机带来的内存安全挑战。
- **进展保证**：`Waker` 和 `Context` 构成了任务唤醒机制，确保了 `Pending` 的任务在条件满足时能被重新调度。
- **驱动力**：执行器负责调度和轮询 `Future`，运行时则提供了完整的异步环境。
- **严谨性**：模型的设计考虑了形式化推理，如调度公平性和 Waker 契约，并由 Rust 强大的类型系统提供安全性保证。

虽然 Rust 异步引入了新的概念和一定的复杂性，但其提供的编译时安全保证和运行时高性能，
使其成为构建健壮、高效并发系统的有力工具。
理解这些底层原理对于充分利用 Rust 异步的潜力至关重要。
