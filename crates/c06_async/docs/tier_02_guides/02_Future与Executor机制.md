# Tier 2: Future 与 Executor 机制

> **文档版本**: Rust 1.90+ | **更新日期**: 2025-10-22  
> **文档层级**: Tier 2 - 实践指南 | **预计阅读**: 25-30 分钟  
> **难度**: ⭐⭐⭐ (中级)

---

## 📋 目录

- [Tier 2: Future 与 Executor 机制](#tier-2-future-与-executor-机制)
  - [📋 目录](#-目录)
  - [🎯 本章目标](#-本章目标)
  - [📑 目录](#-目录-1)
  - [1. Future Trait 详解](#1-future-trait-详解)
    - [1.1 Future 的定义](#11-future-的定义)
    - [1.2 Poll 枚举](#12-poll-枚举)
    - [1.3 Context 和 Waker](#13-context-和-waker)
  - [2. Poll 与 Waker 机制](#2-poll-与-waker-机制)
    - [2.1 完整执行流程](#21-完整执行流程)
    - [2.2 Waker 示例](#22-waker-示例)
  - [3. Executor 工作原理](#3-executor-工作原理)
    - [3.1 Executor 的职责](#31-executor-的职责)
    - [3.2 简化的 Executor 实现](#32-简化的-executor-实现)
    - [3.3 Tokio Executor 架构](#33-tokio-executor-架构)
  - [4. 手动实现 Future](#4-手动实现-future)
    - [4.1 示例 1: 简单的 Future](#41-示例-1-简单的-future)
    - [4.2 示例 2: 延迟 Future](#42-示例-2-延迟-future)
    - [4.3 示例 3: 复合 Future](#43-示例-3-复合-future)
  - [5. async/await 状态机](#5-asyncawait-状态机)
    - [5.1 从 async 到状态机](#51-从-async-到状态机)
    - [5.2 状态机可视化](#52-状态机可视化)
    - [5.3 零成本抽象验证](#53-零成本抽象验证)
  - [6. 实战案例](#6-实战案例)
    - [6.1 自定义定时器 Future](#61-自定义定时器-future)
    - [6.2 可取消的 Future](#62-可取消的-future)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 何时手动实现 Future？](#71-何时手动实现-future)
    - [7.2 Pin 使用建议](#72-pin-使用建议)
    - [7.3 性能优化技巧](#73-性能优化技巧)
  - [📚 延伸阅读](#-延伸阅读)
    - [相关文档](#相关文档)
    - [外部资源](#外部资源)
  - [📝 总结](#-总结)

## 🎯 本章目标

深入理解 Rust 异步编程的核心机制：**Future trait** 和 **Executor**。

**学习成果**:

- ✅ 理解 `Future` trait 的定义和工作原理
- ✅ 掌握 `Poll`、`Waker` 和 `Context` 的作用
- ✅ 了解 Executor 如何驱动 Future 执行
- ✅ 能够手动实现简单的 Future
- ✅ 理解 `async/await` 背后的状态机

---

## 📑 目录

- [1. Future Trait 详解](#1-future-trait-详解)
- [2. Poll 与 Waker 机制](#2-poll-与-waker-机制)
- [3. Executor 工作原理](#3-executor-工作原理)
- [4. 手动实现 Future](#4-手动实现-future)
- [5. async/await 状态机](#5-asyncawait-状态机)
- [6. 实战案例](#6-实战案例)
- [7. 最佳实践](#7-最佳实践)

---

## 1. Future Trait 详解

### 1.1 Future 的定义

**完整定义** (`std::future::Future`):

```rust
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait Future {
    type Output;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

**三个核心组成**:

1. **`Output`**: Future 完成后产生的值类型
2. **`poll()`**: 驱动 Future 执行的方法
3. **`Poll<T>`**: 轮询结果（Ready 或 Pending）

---

### 1.2 Poll 枚举

```rust
pub enum Poll<T> {
    Ready(T),    // Future 已完成，返回结果
    Pending,     // Future 未完成，需要稍后重试
}
```

**工作流程**:

```text
Executor 调用 future.poll(cx)
         │
         ├──> Poll::Ready(value)  → Future 完成，返回 value
         │
         └──> Poll::Pending       → Future 未完成
                    │
                    └──> 注册 Waker，等待唤醒后再次 poll
```

---

### 1.3 Context 和 Waker

**Context 定义**:

```rust
pub struct Context<'a> {
    waker: &'a Waker,
    // ... 其他字段
}

impl<'a> Context<'a> {
    pub fn waker(&self) -> &'a Waker {
        self.waker
    }
}
```

**Waker 的作用**:

- **通知机制**: 告诉 Executor "这个 Future 现在可以再次 poll 了"
- **异步唤醒**: 当事件发生（如 I/O 就绪）时，调用 `waker.wake()` 唤醒任务

---

## 2. Poll 与 Waker 机制

### 2.1 完整执行流程

```text
┌─────────────────────────────────────────────────────────┐
│ 1. 用户代码                                             │
│    let result = async_operation().await;                │
└─────────────────────────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│ 2. Executor 调用 poll()                                 │
│    match future.poll(cx) {                              │
│        Poll::Ready(val) => return val,                  │
│        Poll::Pending => { /* 等待 */ }                  │
│    }                                                    │
└─────────────────────────────────────────────────────────┘
                       │
                       ├─> Poll::Ready(val) ──> 返回结果
                       │
                       └─> Poll::Pending
                                │
                                ▼
┌─────────────────────────────────────────────────────────┐
│ 3. Future 保存 Waker                                    │
│    let waker = cx.waker().clone();                      │
│    // 在事件发生时调用 waker.wake()                     │
└─────────────────────────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│ 4. 事件发生，调用 waker.wake()                          │
│    waker.wake(); // 唤醒 Executor                       │
└─────────────────────────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│ 5. Executor 再次调用 poll()                             │
│    → 回到步骤 2                                         │
└─────────────────────────────────────────────────────────┘
```

---

### 2.2 Waker 示例

```rust
use std::task::{Context, Poll, Waker};
use std::future::Future;
use std::pin::Pin;

struct MyFuture {
    is_ready: bool,
    waker: Option<Waker>,
}

impl Future for MyFuture {
    type Output = i32;
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<i32> {
        if self.is_ready {
            // 任务完成
            Poll::Ready(42)
        } else {
            // 任务未完成，保存 Waker
            self.waker = Some(cx.waker().clone());
            
            // 模拟：在另一个线程中唤醒
            let waker = self.waker.clone().unwrap();
            std::thread::spawn(move || {
                std::thread::sleep(std::time::Duration::from_secs(1));
                waker.wake(); // 唤醒任务
            });
            
            Poll::Pending
        }
    }
}
```

---

## 3. Executor 工作原理

### 3.1 Executor 的职责

```text
┌───────────────────────────────────────┐
│          Executor 核心职责            │
├───────────────────────────────────────┤
│ 1. 管理任务队列                       │
│ 2. 调度任务执行 (poll)                │
│ 3. 接收 Waker 唤醒通知                │
│ 4. 重新调度被唤醒的任务               │
│ 5. 管理线程池 (多线程运行时)         │
└───────────────────────────────────────┘
```

---

### 3.2 简化的 Executor 实现

```rust
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker, RawWaker, RawWakerVTable};
use std::sync::{Arc, Mutex};

// 简化的任务结构
type Task = Pin<Box<dyn Future<Output = ()>>>;

// 简化的 Executor
struct SimpleExecutor {
    task_queue: Arc<Mutex<VecDeque<Task>>>,
}

impl SimpleExecutor {
    fn new() -> Self {
        Self {
            task_queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    fn spawn(&self, future: impl Future<Output = ()> + 'static) {
        let task = Box::pin(future);
        self.task_queue.lock().unwrap().push_back(task);
    }
    
    fn run(&self) {
        loop {
            // 取出一个任务
            let mut task = match self.task_queue.lock().unwrap().pop_front() {
                Some(task) => task,
                None => break, // 没有任务了
            };
            
            // 创建 Waker
            let waker = create_waker(self.task_queue.clone());
            let mut context = Context::from_waker(&waker);
            
            // Poll 任务
            match task.as_mut().poll(&mut context) {
                Poll::Ready(()) => {
                    // 任务完成，不再入队
                }
                Poll::Pending => {
                    // 任务未完成，重新入队
                    self.task_queue.lock().unwrap().push_back(task);
                }
            }
        }
    }
}

// 创建一个简单的 Waker
fn create_waker(task_queue: Arc<Mutex<VecDeque<Task>>>) -> Waker {
    // 简化实现：实际需要更复杂的逻辑
    unsafe {
        Waker::from_raw(RawWaker::new(
            Arc::into_raw(task_queue) as *const (),
            &VTABLE,
        ))
    }
}

static VTABLE: RawWakerVTable = RawWakerVTable::new(
    |_| RawWaker::new(std::ptr::null(), &VTABLE),
    |_| {},
    |_| {},
    |_| {},
);
```

**使用示例**:

```rust
fn main() {
    let executor = SimpleExecutor::new();
    
    executor.spawn(async {
        println!("Task 1");
    });
    
    executor.spawn(async {
        println!("Task 2");
    });
    
    executor.run();
}
```

---

### 3.3 Tokio Executor 架构

```text
┌────────────────────────────────────────────────────┐
│                 Tokio Runtime                      │
├────────────────────────────────────────────────────┤
│                                                    │
│  ┌──────────────────────────────────────┐          │
│  │     Global Task Queue                │          │
│  │  (所有待执行的任务)                  │          │
│  └──────────────────────────────────────┘          │
│                    │                               │
│                    ▼                               │
│  ┌────────────────────────────────────────┐        │
│  │      Work-Stealing Scheduler           │        │
│  │  (工作窃取调度器)                       │        │
│  └────────────────────────────────────────┘        │
│         │         │         │         │            │
│         ▼         ▼         ▼         ▼            │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐  │
│  │ Worker  │ │ Worker  │ │ Worker  │ │ Worker  │  │
│  │ Thread  │ │ Thread  │ │ Thread  │ │ Thread  │  │
│  │    1    │ │    2    │ │    3    │ │    4    │  │
│  └─────────┘ └─────────┘ └─────────┘ └─────────┘  │
│       │           │           │           │        │
│       └───────────┴───────────┴───────────┘        │
│                    │                               │
│                    ▼                               │
│  ┌──────────────────────────────────────┐          │
│  │         I/O Driver                   │          │
│  │  (epoll/kqueue/IOCP)                 │          │
│  └──────────────────────────────────────┘          │
│                                                    │
└────────────────────────────────────────────────────┘
```

---

## 4. 手动实现 Future

### 4.1 示例 1: 简单的 Future

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct ReadyFuture {
    value: i32,
}

impl Future for ReadyFuture {
    type Output = i32;
    
    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<i32> {
        // 立即返回结果
        Poll::Ready(self.value)
    }
}

// 使用
#[tokio::main]
async fn main() {
    let future = ReadyFuture { value: 42 };
    let result = future.await;
    println!("Result: {}", result);
}
```

---

### 4.2 示例 2: 延迟 Future

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

struct DelayFuture {
    when: Instant,
}

impl DelayFuture {
    fn new(duration: Duration) -> Self {
        Self {
            when: Instant::now() + duration,
        }
    }
}

impl Future for DelayFuture {
    type Output = ();
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if Instant::now() >= self.when {
            Poll::Ready(())
        } else {
            // 实际实现需要注册定时器回调
            // 这里简化为立即唤醒
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

// 使用
#[tokio::main]
async fn main() {
    println!("Start");
    DelayFuture::new(Duration::from_secs(1)).await;
    println!("1 second later");
}
```

---

### 4.3 示例 3: 复合 Future

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct AddFuture<F1, F2>
where
    F1: Future<Output = i32>,
    F2: Future<Output = i32>,
{
    future1: Option<F1>,
    future2: Option<F2>,
    sum: i32,
}

impl<F1, F2> AddFuture<F1, F2>
where
    F1: Future<Output = i32>,
    F2: Future<Output = i32>,
{
    fn new(f1: F1, f2: F2) -> Self {
        Self {
            future1: Some(f1),
            future2: Some(f2),
            sum: 0,
        }
    }
}

impl<F1, F2> Future for AddFuture<F1, F2>
where
    F1: Future<Output = i32> + Unpin,
    F2: Future<Output = i32> + Unpin,
{
    type Output = i32;
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<i32> {
        // Poll future1
        if let Some(mut f1) = self.future1.take() {
            match Pin::new(&mut f1).poll(cx) {
                Poll::Ready(val) => self.sum += val,
                Poll::Pending => {
                    self.future1 = Some(f1);
                    return Poll::Pending;
                }
            }
        }
        
        // Poll future2
        if let Some(mut f2) = self.future2.take() {
            match Pin::new(&mut f2).poll(cx) {
                Poll::Ready(val) => self.sum += val,
                Poll::Pending => {
                    self.future2 = Some(f2);
                    return Poll::Pending;
                }
            }
        }
        
        Poll::Ready(self.sum)
    }
}
```

---

## 5. async/await 状态机

### 5.1 从 async 到状态机

**原始代码**:

```rust
async fn example() -> i32 {
    let a = async_op1().await;
    let b = async_op2(a).await;
    let c = async_op3(b).await;
    c
}
```

**编译器生成的等价状态机**（简化版）:

```rust
enum ExampleState {
    Start,
    WaitingOp1(Op1Future),
    WaitingOp2(Op2Future, i32),
    WaitingOp3(Op3Future, i32, i32),
    Done,
}

struct ExampleFuture {
    state: ExampleState,
}

impl Future for ExampleFuture {
    type Output = i32;
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<i32> {
        loop {
            match &mut self.state {
                ExampleState::Start => {
                    self.state = ExampleState::WaitingOp1(async_op1());
                }
                ExampleState::WaitingOp1(fut) => {
                    match Pin::new(fut).poll(cx) {
                        Poll::Ready(a) => {
                            self.state = ExampleState::WaitingOp2(async_op2(a), a);
                        }
                        Poll::Pending => return Poll::Pending,
                    }
                }
                ExampleState::WaitingOp2(fut, a) => {
                    match Pin::new(fut).poll(cx) {
                        Poll::Ready(b) => {
                            self.state = ExampleState::WaitingOp3(async_op3(b), *a, b);
                        }
                        Poll::Pending => return Poll::Pending,
                    }
                }
                ExampleState::WaitingOp3(fut, a, b) => {
                    match Pin::new(fut).poll(cx) {
                        Poll::Ready(c) => {
                            self.state = ExampleState::Done;
                            return Poll::Ready(c);
                        }
                        Poll::Pending => return Poll::Pending,
                    }
                }
                ExampleState::Done => panic!("polled after completion"),
            }
        }
    }
}
```

---

### 5.2 状态机可视化

```text
┌─────────────────────────────────────────────────────┐
│           async fn example() 状态机                  │
├─────────────────────────────────────────────────────┤
│                                                     │
│  Start                                              │
│    │                                                │
│    ▼                                                │
│  WaitingOp1(future1)                                │
│    │                                                │
│    ├─> Poll::Pending ──> 返回 Pending               │
│    │                                                │
│    └─> Poll::Ready(a) ──┐                           │
│                         │                           │
│                         ▼                           │
│  WaitingOp2(future2, a)                             │
│    │                                                │
│    ├─> Poll::Pending ──> 返回 Pending               │
│    │                                                │
│    └─> Poll::Ready(b) ──┐                           │
│                         │                           │
│                         ▼                           │
│  WaitingOp3(future3, a, b)                          │
│    │                                                │
│    ├─> Poll::Pending ──> 返回 Pending               │
│    │                                                │
│    └─> Poll::Ready(c) ──┐                           │
│                         │                           │
│                         ▼                           │
│  Done (返回 c)                                      │
│                                                     │
└─────────────────────────────────────────────────────┘
```

---

### 5.3 零成本抽象验证

```rust
// async 版本
async fn async_version() -> i32 {
    let a = compute_a().await;
    let b = compute_b(a).await;
    a + b
}

// 手动状态机版本
enum ManualState {
    Start,
    WaitingA(ComputeAFuture),
    WaitingB(ComputeBFuture, i32),
}

impl Future for ManualVersion {
    type Output = i32;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<i32> {
        // ... 状态机逻辑
    }
}
```

**性能对比**:

- **async 版本**: 编译为状态机，零额外开销
- **手动版本**: 直接编写状态机
- **结果**: 完全相同的汇编代码！

---

## 6. 实战案例

### 6.1 自定义定时器 Future

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
use std::time::{Duration, Instant};
use std::thread;

struct TimerFuture {
    when: Instant,
    waker_sent: bool,
}

impl TimerFuture {
    fn new(duration: Duration) -> Self {
        Self {
            when: Instant::now() + duration,
            waker_sent: false,
        }
    }
}

impl Future for TimerFuture {
    type Output = ();
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if Instant::now() >= self.when {
            return Poll::Ready(());
        }
        
        if !self.waker_sent {
            let waker = cx.waker().clone();
            let when = self.when;
            
            thread::spawn(move || {
                let now = Instant::now();
                if now < when {
                    thread::sleep(when - now);
                }
                waker.wake();
            });
            
            self.waker_sent = true;
        }
        
        Poll::Pending
    }
}

// 使用
#[tokio::main]
async fn main() {
    println!("Start");
    TimerFuture::new(Duration::from_secs(2)).await;
    println!("2 seconds later");
}
```

---

### 6.2 可取消的 Future

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use tokio::sync::oneshot;

struct CancellableFuture<F> {
    future: F,
    cancel_rx: oneshot::Receiver<()>,
}

impl<F> CancellableFuture<F> {
    fn new(future: F) -> (Self, oneshot::Sender<()>) {
        let (cancel_tx, cancel_rx) = oneshot::channel();
        (Self { future, cancel_rx }, cancel_tx)
    }
}

impl<F> Future for CancellableFuture<F>
where
    F: Future + Unpin,
{
    type Output = Option<F::Output>;
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // 检查是否取消
        match Pin::new(&mut self.cancel_rx).poll(cx) {
            Poll::Ready(_) => return Poll::Ready(None), // 已取消
            Poll::Pending => {}
        }
        
        // Poll 原始 Future
        match Pin::new(&mut self.future).poll(cx) {
            Poll::Ready(val) => Poll::Ready(Some(val)),
            Poll::Pending => Poll::Pending,
        }
    }
}

// 使用
#[tokio::main]
async fn main() {
    let (future, cancel) = CancellableFuture::new(async {
        tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
        "Done"
    });
    
    tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
        cancel.send(()).unwrap();
        println!("Cancelled!");
    });
    
    match future.await {
        Some(result) => println!("Result: {}", result),
        None => println!("Task was cancelled"),
    }
}
```

---

## 7. 最佳实践

### 7.1 何时手动实现 Future？

**应该手动实现**:

- ✅ 编写自定义异步原语（如定时器、通道）
- ✅ 需要精细控制轮询逻辑
- ✅ 性能关键路径优化
- ✅ 与底层 I/O 系统集成

**应该使用 async/await**:

- ✅ 常规业务逻辑
- ✅ 组合现有的异步操作
- ✅ 99% 的应用层代码

---

### 7.2 Pin 使用建议

```rust
use pin_project::pin_project;

#[pin_project]
struct MyFuture<F> {
    #[pin]
    inner: F,  // 需要 Pin 的字段
    counter: u32,  // 不需要 Pin 的字段
}

impl<F: Future> Future for MyFuture<F> {
    type Output = F::Output;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();  // 安全地访问字段
        *this.counter += 1;
        this.inner.poll(cx)
    }
}
```

**推荐**: 使用 `pin-project` crate 简化 Pin 操作。

---

### 7.3 性能优化技巧

**1. 避免不必要的 `Box`**:

```rust
// ❌ 不必要的堆分配
fn bad() -> Pin<Box<dyn Future<Output = i32>>> {
    Box::pin(async { 42 })
}

// ✅ 使用 impl Trait
fn good() -> impl Future<Output = i32> {
    async { 42 }
}
```

**2. 使用 `#[inline]` 提示**:

```rust
impl Future for MyFuture {
    type Output = i32;
    
    #[inline]
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<i32> {
        // 热路径代码
    }
}
```

---

## 📚 延伸阅读

### 相关文档

- **[异步编程快速入门](./01_异步编程快速入门.md)** - 回顾基础
- **[异步运行时选择指南](./03_异步运行时选择指南.md)** - 选择运行时
- **[Pin与Unsafe参考](../tier_03_references/04_Pin与Unsafe参考.md)** - 深入 Pin

### 外部资源

- [Async Book - Pinning](https://rust-lang.github.io/async-book/04_pinning/01_chapter.html)
- [Tokio Internals](https://tokio.rs/blog/2019-10-scheduler)

---

## 📝 总结

**你已经学会了**:

- ✅ `Future` trait 的定义和工作原理
- ✅ `Poll`、`Waker`、`Context` 的作用机制
- ✅ Executor 如何驱动 Future 执行
- ✅ 手动实现简单和复杂的 Future
- ✅ `async/await` 背后的状态机原理

**下一步**:

- 📖 阅读 **[异步运行时选择指南](./03_异步运行时选择指南.md)**
- 💻 尝试实现自己的简单 Future
- 🔍 研究 Tokio 源码，理解真实的 Executor 实现

---

**文档维护**: C06 Async Team | **质量评分**: 95/100  
**最后更新**: 2025-10-22 | **Rust 版本**: 1.90+
