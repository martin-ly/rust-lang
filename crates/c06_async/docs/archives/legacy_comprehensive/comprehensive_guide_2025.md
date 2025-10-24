# Rust 异步编程超级综合指南 2025

## 📊 目录

- [Rust 异步编程超级综合指南 2025](#rust-异步编程超级综合指南-2025)
  - [📊 目录](#-目录)
  - [Rust Asynchronous Programming Ultimate Guide 2025](#rust-asynchronous-programming-ultimate-guide-2025)
  - [📋 目录 (Table of Contents)](#-目录-table-of-contents)
  - [第一部分: 理论基础与形式化](#第一部分-理论基础与形式化)
    - [1. 异步编程理论基础](#1-异步编程理论基础)
      - [1.1 异步编程的数学模型](#11-异步编程的数学模型)
      - [1.2 异步语义 (Async Semantics)](#12-异步语义-async-semantics)
      - [1.3 调度理论](#13-调度理论)
    - [2. 并发模型形式化分析](#2-并发模型形式化分析)
      - [2.1 Actor 模型形式化](#21-actor-模型形式化)
      - [2.2 Reactor 模型形式化](#22-reactor-模型形式化)
      - [2.3 CSP 模型形式化](#23-csp-模型形式化)
    - [3. Future 与状态机理论](#3-future-与状态机理论)
      - [3.1 状态机转换](#31-状态机转换)
      - [3.2 Pin 与内存安全](#32-pin-与内存安全)
  - [第二部分: 设计模式与惯用法](#第二部分-设计模式与惯用法)
    - [4. Actor 模式深度解析](#4-actor-模式深度解析)
      - [4.1 Actor 模式核心概念](#41-actor-模式核心概念)
      - [4.2 实现方案对比](#42-实现方案对比)
      - [4.3 Actor 最佳实践](#43-actor-最佳实践)
    - [5. Reactor 模式与事件循环](#5-reactor-模式与事件循环)
      - [5.1 Reactor 核心原理](#51-reactor-核心原理)
      - [5.2 Tokio Reactor 深入](#52-tokio-reactor-深入)
      - [5.3 自定义 Reactor 示例](#53-自定义-reactor-示例)
    - [6. CSP 模式与通道通信](#6-csp-模式与通道通信)
      - [6.1 CSP 理论回顾](#61-csp-理论回顾)
      - [6.2 Channel 类型全解](#62-channel-类型全解)
      - [6.3 CSP 设计模式](#63-csp-设计模式)
    - [7. 异步设计模式集合](#7-异步设计模式集合)
      - [7.1 创建型模式](#71-创建型模式)
      - [7.2 结构型模式](#72-结构型模式)
      - [7.3 行为型模式](#73-行为型模式)
  - [相关文档](#相关文档)

## Rust Asynchronous Programming Ultimate Guide 2025

**版本**: Rust 1.90+ | Tokio 1.41+ | Smol 2.0+  
**日期**: 2025年10月4日  
**状态**: 生产就绪

---

## 📋 目录 (Table of Contents)

- [Rust 异步编程超级综合指南 2025](#rust-异步编程超级综合指南-2025)
  - [📊 目录](#-目录)
  - [Rust Asynchronous Programming Ultimate Guide 2025](#rust-asynchronous-programming-ultimate-guide-2025)
  - [📋 目录 (Table of Contents)](#-目录-table-of-contents)
  - [第一部分: 理论基础与形式化](#第一部分-理论基础与形式化)
    - [1. 异步编程理论基础](#1-异步编程理论基础)
      - [1.1 异步编程的数学模型](#11-异步编程的数学模型)
      - [1.2 异步语义 (Async Semantics)](#12-异步语义-async-semantics)
      - [1.3 调度理论](#13-调度理论)
    - [2. 并发模型形式化分析](#2-并发模型形式化分析)
      - [2.1 Actor 模型形式化](#21-actor-模型形式化)
      - [2.2 Reactor 模型形式化](#22-reactor-模型形式化)
      - [2.3 CSP 模型形式化](#23-csp-模型形式化)
    - [3. Future 与状态机理论](#3-future-与状态机理论)
      - [3.1 状态机转换](#31-状态机转换)
      - [3.2 Pin 与内存安全](#32-pin-与内存安全)
  - [第二部分: 设计模式与惯用法](#第二部分-设计模式与惯用法)
    - [4. Actor 模式深度解析](#4-actor-模式深度解析)
      - [4.1 Actor 模式核心概念](#41-actor-模式核心概念)
      - [4.2 实现方案对比](#42-实现方案对比)
      - [4.3 Actor 最佳实践](#43-actor-最佳实践)
    - [5. Reactor 模式与事件循环](#5-reactor-模式与事件循环)
      - [5.1 Reactor 核心原理](#51-reactor-核心原理)
      - [5.2 Tokio Reactor 深入](#52-tokio-reactor-深入)
      - [5.3 自定义 Reactor 示例](#53-自定义-reactor-示例)
    - [6. CSP 模式与通道通信](#6-csp-模式与通道通信)
      - [6.1 CSP 理论回顾](#61-csp-理论回顾)
      - [6.2 Channel 类型全解](#62-channel-类型全解)
      - [6.3 CSP 设计模式](#63-csp-设计模式)
    - [7. 异步设计模式集合](#7-异步设计模式集合)
      - [7.1 创建型模式](#71-创建型模式)
      - [7.2 结构型模式](#72-结构型模式)
      - [7.3 行为型模式](#73-行为型模式)
  - [相关文档](#相关文档)

---

## 第一部分: 理论基础与形式化

### 1. 异步编程理论基础

#### 1.1 异步编程的数学模型

**定义 1.1 (Future)**  
Future 是一个延迟计算，形式化定义为：

```text
F = (S, ι, τ, P)
其中:
  S: 状态集合 {Pending, Ready(T), Polled}
  ι: 初始状态 ∈ S
  τ: 状态转换函数 τ: S × Context → S
  P: poll 函数 P: &mut Self × &mut Context → Poll<T>
```

**定理 1.1 (Future 组合性)**  
给定两个 Future F₁ 和 F₂，存在组合运算：

```text
F₁ ∘ F₂ = Future { poll: |cx| match F₁.poll(cx) {
    Ready(v) => F₂.poll(cx),
    Pending => Pending
}}
```

#### 1.2 异步语义 (Async Semantics)

**语义规则 1: async fn 转换**:

```text
async fn foo() -> T { ... }

⟹ 编译器转换为 ⟹

fn foo() -> impl Future<Output = T> {
    // 状态机实现
    FooFuture { state: State::Start }
}
```

**语义规则 2: await 点 (Await Point)**:

```text
let x = future.await;

⟹ 展开为 ⟹

loop {
    match future.poll(cx) {
        Poll::Ready(val) => break val,
        Poll::Pending => {
            // 注册 waker
            // yield control
            return Poll::Pending
        }
    }
}
```

#### 1.3 调度理论

**定义 1.2 (异步调度器)**:

```text
Scheduler = (TaskQueue, Executor, Runtime)

调度策略:
  FIFO: 先进先出
  Priority: 优先级调度
  Work-Stealing: 工作窃取
  Fair: 公平调度
```

**性能模型**:

```text
延迟 (Latency) = 排队时间 + 执行时间 + 上下文切换开销
吞吐量 (Throughput) = 任务数 / 总时间
```

---

### 2. 并发模型形式化分析

#### 2.1 Actor 模型形式化

**定义 2.1 (Actor)**:

```text
Actor = (State, Mailbox, Behavior)

状态转移:
  Config = (A, M)  // A: Actor 集合, M: 传输中消息
  
  转换规则:
  ───────────────────────────────────────────
  a ∈ A, mailbox(a) = [m|ms], 
  β(state(a), m) = (s', actions)
  ───────────────────────────────────────────
  (A, M) → (A', M')
  where:
    state'(a) = s'
    mailbox'(a) = ms
    M' = M ∪ {新消息}
    A' = A ∪ {新 Actors}
```

**性质 2.1 (Actor 不变量)**:

```text
∀ actor ∈ System:
  1. 消息有序性: msg₁ before msg₂ ⟹ 处理(msg₁) before 处理(msg₂)
  2. 状态封装: ∀ a₁, a₂: state(a₁) ⊥ state(a₂)
  3. 位置透明: send(addr, msg) 不依赖物理位置
```

#### 2.2 Reactor 模型形式化

**定义 2.2 (Reactor)**:

```text
Reactor = (EventDemux, Handlers, EventLoop)

事件循环伪代码:
  loop:
    events := demux.select(sources)
    for e ∈ events:
      handler := handlers[e.source]
      handler.handle(e)
```

**性质 2.2 (Reactor 特性)**:

```text
1. 单线程性: 所有 handlers 在同一线程执行
2. 非阻塞: I/O 操作不阻塞事件循环
3. 响应性: ∀ event: response_time < timeout
```

#### 2.3 CSP 模型形式化

**定义 2.3 (CSP Process)**:

```text
P ::= STOP           // 停止
    | SKIP           // 空操作
    | a → P          // 前缀
    | P □ Q          // 外部选择
    | P ⊓ Q          // 内部选择
    | P ∥ Q          // 并行组合
    | P ||| Q        // 交错

Channel 语义:
  c!v: 在 c 上发送 v
  c?x: 从 c 接收到 x
```

**定理 2.1 (CSP 等价关系)**:

```text
Rust 实现 ≅ CSP 理论:
  tokio::spawn(async { ... }) ≅ P
  mpsc::channel() ≅ channel c
  tx.send(v).await ≅ c!v
  rx.recv().await ≅ c?x
  tokio::select! ≅ P □ Q
```

---

### 3. Future 与状态机理论

#### 3.1 状态机转换

**示例: async 函数的状态机生成**:

```rust
// 源代码
async fn example() -> i32 {
    let x = async_op1().await;  // 第一个 await 点
    let y = async_op2().await;  // 第二个 await 点
    x + y
}

// 编译器生成的状态机
enum ExampleFutureState {
    Start,
    WaitOp1(Op1Future),
    WaitOp2 { x: i32, op2: Op2Future },
    Done,
}

impl Future for ExampleFuture {
    type Output = i32;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<i32> {
        loop {
            match self.state {
                Start => {
                    // 启动 op1
                    self.state = WaitOp1(async_op1());
                }
                WaitOp1(ref mut fut) => {
                    match fut.poll(cx) {
                        Ready(x) => {
                            self.state = WaitOp2 { 
                                x, 
                                op2: async_op2() 
                            };
                        }
                        Pending => return Pending,
                    }
                }
                WaitOp2 { x, ref mut op2 } => {
                    match op2.poll(cx) {
                        Ready(y) => {
                            self.state = Done;
                            return Ready(x + y);
                        }
                        Pending => return Pending,
                    }
                }
                Done => panic!("polled after completion"),
            }
        }
    }
}
```

#### 3.2 Pin 与内存安全

**定义 3.1 (Pin 语义)**:

```text
Pin<P>: 保证 P 指向的数据不会被移动

关键不变量:
  ∀ p: Pin<&mut T>, ∀ t: Time:
    addr(p, t) = addr(p, t+1)  // 地址不变
```

**使用场景**:

```rust
// 自引用结构
struct SelfRef {
    data: String,
    ptr: *const String,  // 指向 data
}

// Pin 保证安全性
impl Future for SelfRefFuture {
    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Output> {
        // self 被 pin，data 地址不变
        // ptr 始终有效
    }
}
```

---

## 第二部分: 设计模式与惯用法

### 4. Actor 模式深度解析

#### 4.1 Actor 模式核心概念

**特征**:

- 📨 消息传递 (Message Passing)
- 🔒 状态封装 (State Encapsulation)
- 🎯 位置透明 (Location Transparency)
- ⚡ 异步通信 (Asynchronous Communication)

#### 4.2 实现方案对比

**方案 1: Actix**:

```rust
use actix::prelude::*;

// 定义消息
#[derive(Message)]
#[rtype(result = "i32")]
struct Add(i32, i32);

// 定义 Actor
struct Calculator { total: i32 }

impl Actor for Calculator {
    type Context = Context<Self>;
}

// 消息处理
impl Handler<Add> for Calculator {
    type Result = i32;
    
    fn handle(&mut self, msg: Add, _ctx: &mut Context<Self>) -> i32 {
        self.total += msg.0 + msg.1;
        self.total
    }
}

// 使用
#[actix::main]
async fn main() {
    let addr = Calculator { total: 0 }.start();
    let result = addr.send(Add(10, 20)).await.unwrap();
    println!("结果: {}", result);
}
```

**优点**:

- ✅ 类型安全的消息
- ✅ 自动生命周期管理
- ✅ 内置监督策略

**缺点**:

- ❌ 较重的运行时
- ❌ 学习曲线陡峭

**方案 2: 手写 Actor (轻量级)**:

```rust
use tokio::sync::mpsc;

// Actor trait
trait Actor: Send + 'static {
    type Message: Send;
    
    async fn handle(&mut self, msg: Self::Message);
}

// Actor 运行器
async fn run_actor<A: Actor>(mut actor: A, mut rx: mpsc::Receiver<A::Message>) {
    while let Some(msg) = rx.recv().await {
        actor.handle(msg).await;
    }
}

// 示例: 计数器 Actor
struct Counter { count: i32 }

impl Actor for Counter {
    type Message = CounterMsg;
    
    async fn handle(&mut self, msg: Self::Message) {
        match msg {
            CounterMsg::Increment(n) => {
                self.count += n;
                println!("Count: {}", self.count);
            }
            CounterMsg::Get(tx) => {
                let _ = tx.send(self.count);
            }
        }
    }
}

enum CounterMsg {
    Increment(i32),
    Get(tokio::sync::oneshot::Sender<i32>),
}

// 使用
#[tokio::main]
async fn main() {
    let (tx, rx) = mpsc::channel(100);
    let actor = Counter { count: 0 };
    
    tokio::spawn(run_actor(actor, rx));
    
    tx.send(CounterMsg::Increment(5)).await.unwrap();
    
    let (result_tx, result_rx) = tokio::sync::oneshot::channel();
    tx.send(CounterMsg::Get(result_tx)).await.unwrap();
    let count = result_rx.await.unwrap();
    println!("最终计数: {}", count);
}
```

**优点**:

- ✅ 极轻量
- ✅ 完全控制
- ✅ 易于定制

**缺点**:

- ❌ 需要手动实现功能
- ❌ 缺少监督机制

#### 4.3 Actor 最佳实践

**1. 消息设计**:

```rust
// ✅ 好的设计: 清晰的消息类型
enum BankAccountMsg {
    Deposit { amount: u64, reply: oneshot::Sender<Balance> },
    Withdraw { amount: u64, reply: oneshot::Sender<Result<Balance, Error>> },
    GetBalance { reply: oneshot::Sender<Balance> },
}

// ❌ 避免: 泛化的消息
enum GenericMsg {
    DoSomething(Box<dyn Any>),  // 类型不安全
}
```

**2. 错误处理**:

```rust
impl Handler<OperationMsg> for MyActor {
    type Result = ResponseFuture<Result<T, Error>>;
    
    fn handle(&mut self, msg: OperationMsg, _ctx: &mut Context<Self>) -> Self::Result {
        Box::pin(async move {
            // 结构化错误处理
            let result = risky_operation().await
                .map_err(|e| Error::OperationFailed(e))?;
            Ok(result)
        })
    }
}
```

**3. 背压控制**:

```rust
// 使用有界通道防止内存溢出
let (tx, rx) = mpsc::channel(100);  // 限制队列大小

// 发送时处理背压
match tx.try_send(msg) {
    Ok(()) => println!("消息已发送"),
    Err(mpsc::error::TrySendError::Full(_)) => {
        println!("Actor 繁忙，应用背压");
        // 实施背压策略
    }
    Err(mpsc::error::TrySendError::Closed(_)) => {
        println!("Actor 已关闭");
    }
}
```

---

### 5. Reactor 模式与事件循环

#### 5.1 Reactor 核心原理

**架构图**:

```text
┌─────────────────────────────────────┐
│         应用代码                    │
│  ┌──────────┐  ┌──────────┐        │
│  │ Future 1 │  │ Future 2 │  ...   │
│  └────┬─────┘  └────┬─────┘        │
└───────┼─────────────┼──────────────┘
        │             │
┌───────▼─────────────▼──────────────┐
│         Runtime/Executor           │
│  ┌────────────────────────────┐   │
│  │      Task Scheduler        │   │
│  └──────────┬─────────────────┘   │
└─────────────┼─────────────────────┘
              │
┌─────────────▼─────────────────────┐
│          Reactor                  │
│  ┌────────────────────────────┐  │
│  │   Event Demultiplexer      │  │
│  │   (epoll/kqueue/IOCP)      │  │
│  └────────────────────────────┘  │
└───────────────────────────────────┘
```

#### 5.2 Tokio Reactor 深入

**组件分析**:

```rust
// Tokio 的核心组件

// 1. Runtime: 管理线程池和任务调度
let rt = tokio::runtime::Runtime::new().unwrap();

// 2. Reactor: 驱动 I/O 事件
// 内部使用 mio (Metal I/O)
// - Linux: epoll
// - macOS/BSD: kqueue  
// - Windows: IOCP

// 3. Driver: 时间驱动器
// 管理定时器和超时

// 4. Scheduler: 任务调度器
// - multi_thread: 工作窃取调度
// - current_thread: 单线程调度
```

**事件循环实现**:

```rust
// 简化的事件循环伪代码
loop {
    // 1. 从 Reactor 获取就绪事件
    let events = reactor.poll(timeout);
    
    // 2. 唤醒对应的 Future
    for event in events {
        if let Some(waker) = wakers.get(event.token) {
            waker.wake();
        }
    }
    
    // 3. 调度并执行就绪任务
    while let Some(task) = scheduler.pop_ready() {
        task.poll();
    }
    
    // 4. 处理定时器
    timers.advance_to(now());
}
```

#### 5.3 自定义 Reactor 示例

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;

// 自定义事件类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum EventType {
    Read,
    Write,
    Timer,
}

// 事件
struct Event {
    source: u64,
    event_type: EventType,
    data: Vec<u8>,
}

// 事件处理器
#[async_trait::async_trait]
trait EventHandler: Send + Sync {
    async fn handle(&self, event: Event);
}

// Reactor 实现
struct CustomReactor {
    handlers: Arc<Mutex<HashMap<(u64, EventType), Arc<dyn EventHandler>>>>,
    event_queue: Arc<Mutex<Vec<Event>>>,
}

impl CustomReactor {
    fn new() -> Self {
        Self {
            handlers: Arc::new(Mutex::new(HashMap::new())),
            event_queue: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    // 注册处理器
    fn register(&self, source: u64, event_type: EventType, handler: Arc<dyn EventHandler>) {
        let mut handlers = self.handlers.lock().unwrap();
        handlers.insert((source, event_type), handler);
    }
    
    // 提交事件
    fn submit(&self, event: Event) {
        let mut queue = self.event_queue.lock().unwrap();
        queue.push(event);
    }
    
    // 事件循环
    async fn run(&self, iterations: usize) {
        for _ in 0..iterations {
            // 获取事件
            let events = {
                let mut queue = self.event_queue.lock().unwrap();
                std::mem::take(&mut *queue)
            };
            
            // 分发事件
            for event in events {
                let handler = {
                    let handlers = self.handlers.lock().unwrap();
                    handlers.get(&(event.source, event.event_type)).cloned()
                };
                
                if let Some(h) = handler {
                    h.handle(event).await;
                }
            }
            
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        }
    }
}

// 使用示例
struct LogHandler;

#[async_trait::async_trait]
impl EventHandler for LogHandler {
    async fn handle(&self, event: Event) {
        println!("处理事件: source={}, type={:?}", event.source, event.event_type);
    }
}

#[tokio::main]
async fn main() {
    let reactor = CustomReactor::new();
    reactor.register(1, EventType::Read, Arc::new(LogHandler));
    
    reactor.submit(Event {
        source: 1,
        event_type: EventType::Read,
        data: vec![1, 2, 3],
    });
    
    reactor.run(5).await;
}
```

---

### 6. CSP 模式与通道通信

#### 6.1 CSP 理论回顾

**核心概念**:

```text
Process: 独立执行单元
Channel: 进程间通信管道
Communication: 同步或异步消息传递
```

**Rust 实现映射**:

```text
tokio::spawn() ≈ go func()
mpsc::channel() ≈ make(chan T)
tx.send().await ≈ ch <- value
rx.recv().await ≈ value := <-ch
tokio::select! ≈ select {}
```

#### 6.2 Channel 类型全解

**1. MPSC (Multi-Producer Single-Consumer)**:

```rust
use tokio::sync::mpsc;

// 有界通道 - 提供背压
let (tx, mut rx) = mpsc::channel(100);

// 无界通道 - 注意内存使用
let (tx, mut rx) = mpsc::unbounded_channel();

// 发送
tx.send(value).await?;

// 接收
while let Some(msg) = rx.recv().await {
    println!("收到: {}", msg);
}
```

**2. Oneshot (一次性通道)**:

```rust
use tokio::sync::oneshot;

let (tx, rx) = oneshot::channel();

// 发送一个值
tx.send(42).unwrap();

// 接收
let value = rx.await.unwrap();
```

**3. Broadcast (广播)**:

```rust
use tokio::sync::broadcast;

let (tx, mut rx1) = broadcast::channel(16);
let mut rx2 = tx.subscribe();

// 发送给所有订阅者
tx.send(10).unwrap();

// 多个接收者
let v1 = rx1.recv().await.unwrap();
let v2 = rx2.recv().await.unwrap();
```

**4. Watch (状态监听)**:

```rust
use tokio::sync::watch;

let (tx, mut rx) = watch::channel("initial");

// 更新值
tx.send("updated").unwrap();

// 等待变化
rx.changed().await.unwrap();
let value = *rx.borrow();
```

#### 6.3 CSP 设计模式

**模式 1: 生产者-消费者**:

```rust
async fn producer_consumer_pattern() {
    let (tx, mut rx) = mpsc::channel(100);
    
    // 生产者
    let producer = tokio::spawn(async move {
        for i in 0..10 {
            tx.send(i).await.unwrap();
            println!("生产: {}", i);
        }
    });
    
    // 消费者
    let consumer = tokio::spawn(async move {
        while let Some(item) = rx.recv().await {
            println!("消费: {}", item);
            // 处理 item
        }
    });
    
    tokio::join!(producer, consumer);
}
```

**模式 2: Fan-Out (分发)**:

```rust
async fn fan_out_pattern() {
    let (tx, _) = mpsc::channel(100);
    
    // 创建多个消费者
    let mut handles = vec![];
    for i in 0..3 {
        let mut rx = tx.subscribe();
        let handle = tokio::spawn(async move {
            while let Some(msg) = rx.recv().await {
                println!("Worker {} 处理: {}", i, msg);
            }
        });
        handles.push(handle);
    }
    
    // 发送消息
    for msg in 0..10 {
        tx.send(msg).await.unwrap();
    }
    
    // 等待所有 worker
    futures::future::join_all(handles).await;
}
```

**模式 3: Fan-In (汇聚)**:

```rust
async fn fan_in_pattern() {
    let (result_tx, mut result_rx) = mpsc::channel(100);
    
    // 多个生产者
    for i in 0..3 {
        let tx = result_tx.clone();
        tokio::spawn(async move {
            for j in 0..5 {
                tx.send((i, j)).await.unwrap();
            }
        });
    }
    
    drop(result_tx); // 关闭原始发送端
    
    // 汇聚结果
    while let Some((worker, result)) = result_rx.recv().await {
        println!("来自 Worker {}: {}", worker, result);
    }
}
```

**模式 4: Pipeline (流水线)**:

```rust
async fn pipeline_pattern() {
    // 阶段 1: 生成数据
    let stage1 = |tx: mpsc::Sender<i32>| async move {
        for i in 1..=10 {
            tx.send(i).await.unwrap();
        }
    };
    
    // 阶段 2: 处理数据
    let stage2 = |mut rx: mpsc::Receiver<i32>, tx: mpsc::Sender<i32>| async move {
        while let Some(n) = rx.recv().await {
            tx.send(n * 2).await.unwrap();
        }
    };
    
    // 阶段 3: 收集结果
    let stage3 = |mut rx: mpsc::Receiver<i32>| async move {
        let mut sum = 0;
        while let Some(n) = rx.recv().await {
            sum += n;
        }
        sum
    };
    
    // 连接管道
    let (tx1, rx1) = mpsc::channel(10);
    let (tx2, rx2) = mpsc::channel(10);
    
    let h1 = tokio::spawn(stage1(tx1));
    let h2 = tokio::spawn(stage2(rx1, tx2));
    let h3 = tokio::spawn(stage3(rx2));
    
    let _ = h1.await;
    let _ = h2.await;
    let result = h3.await.unwrap();
    println!("Pipeline 结果: {}", result);
}
```

---

### 7. 异步设计模式集合

#### 7.1 创建型模式

**1. Builder 模式 (异步版本)**:

```rust
struct AsyncServiceBuilder {
    config: Option<Config>,
    runtime: Option<Runtime>,
}

impl AsyncServiceBuilder {
    fn new() -> Self {
        Self { config: None, runtime: None }
    }
    
    fn with_config(mut self, config: Config) -> Self {
        self.config = Some(config);
        self
    }
    
    fn with_runtime(mut self, runtime: Runtime) -> Self {
        self.runtime = Some(runtime);
        self
    }
    
    async fn build(self) -> Result<AsyncService, Error> {
        let config = self.config.ok_or(Error::MissingConfig)?;
        let runtime = self.runtime.ok_or(Error::MissingRuntime)?;
        
        // 异步初始化
        let connection = connect_database(&config).await?;
        let cache = init_cache(&config).await?;
        
        Ok(AsyncService {
            config,
            runtime,
            connection,
            cache,
        })
    }
}

// 使用
let service = AsyncServiceBuilder::new()
    .with_config(config)
    .with_runtime(runtime)
    .build()
    .await?;
```

**2. Factory 模式 (异步版本)**:

```rust
#[async_trait]
trait AsyncFactory {
    type Product;
    async fn create(&self) -> Result<Self::Product, Error>;
}

struct DatabaseFactory {
    config: DatabaseConfig,
}

#[async_trait]
impl AsyncFactory for DatabaseFactory {
    type Product = DatabaseConnection;
    
    async fn create(&self) -> Result<DatabaseConnection, Error> {
        // 异步创建连接
        let conn = DatabaseConnection::connect(&self.config).await?;
        conn.initialize().await?;
        Ok(conn)
    }
}
```

#### 7.2 结构型模式

**1. Adapter 模式 (异步适配器)**:

```rust
// 目标接口
#[async_trait]
trait ModernApi {
    async fn fetch_data(&self, id: u64) -> Result<Data, Error>;
}

// 旧接口 (同步)
trait LegacyApi {
    fn get_data(&self, id: u64) -> Result<Data, Error>;
}

// 适配器
struct AsyncAdapter<T: LegacyApi> {
    legacy: T,
}

#[async_trait]
impl<T: LegacyApi + Send + Sync> ModernApi for AsyncAdapter<T> {
    async fn fetch_data(&self, id: u64) -> Result<Data, Error> {
        // 在阻塞线程池中执行同步代码
        tokio::task::spawn_blocking(move || {
            self.legacy.get_data(id)
        })
        .await?
    }
}
```

**2. Proxy 模式 (缓存代理)**:

```rust
#[async_trait]
trait DataService {
    async fn get(&self, key: &str) -> Result<Value, Error>;
}

struct CachingProxy<S: DataService> {
    service: S,
    cache: Arc<RwLock<HashMap<String, Value>>>,
}

#[async_trait]
impl<S: DataService + Send + Sync> DataService for CachingProxy<S> {
    async fn get(&self, key: &str) -> Result<Value, Error> {
        // 检查缓存
        {
            let cache = self.cache.read().await;
            if let Some(value) = cache.get(key) {
                return Ok(value.clone());
            }
        }
        
        // 缓存未命中，调用实际服务
        let value = self.service.get(key).await?;
        
        // 更新缓存
        {
            let mut cache = self.cache.write().await;
            cache.insert(key.to_string(), value.clone());
        }
        
        Ok(value)
    }
}
```

#### 7.3 行为型模式

**1. Strategy 模式 (异步策略)**:

```rust
#[async_trait]
trait RetryStrategy {
    async fn execute<F, T>(&self, operation: F) -> Result<T, Error>
    where
        F: Future<Output = Result<T, Error>> + Send,
        T: Send;
}

struct ExponentialBackoff {
    max_retries: usize,
    base_delay: Duration,
}

#[async_trait]
impl RetryStrategy for ExponentialBackoff {
    async fn execute<F, T>(&self, mut operation: F) -> Result<T, Error>
    where
        F: Future<Output = Result<T, Error>> + Send,
        T: Send,
    {
        let mut attempt = 0;
        loop {
            match operation.await {
                Ok(result) => return Ok(result),
                Err(e) if attempt < self.max_retries => {
                    attempt += 1;
                    let delay = self.base_delay * 2_u32.pow(attempt as u32);
                    tokio::time::sleep(delay).await;
                }
                Err(e) => return Err(e),
            }
        }
    }
}

// 使用
let strategy = ExponentialBackoff {
    max_retries: 3,
    base_delay: Duration::from_millis(100),
};

let result = strategy.execute(|| async {
    unreliable_operation().await
}).await?;
```

**2. Observer 模式 (事件流)**:

```rust
use tokio::sync::broadcast;

struct EventBus {
    tx: broadcast::Sender<Event>,
}

impl EventBus {
    fn new() -> Self {
        let (tx, _) = broadcast::channel(1000);
        Self { tx }
    }
    
    fn subscribe(&self) -> broadcast::Receiver<Event> {
        self.tx.subscribe()
    }
    
    fn publish(&self, event: Event) {
        let _ = self.tx.send(event);
    }
}

// 使用
#[tokio::main]
async fn main() {
    let bus = EventBus::new();
    let mut rx = bus.subscribe();
    
    tokio::spawn(async move {
        while let Ok(event) = rx.recv().await {
            println!("收到事件: {:?}", event);
        }
    });
    
    bus.publish(Event::UserLoggedIn { user_id: 123 });
}
```

**3. Chain of Responsibility (异步责任链)**:

```rust
#[async_trait]
trait Handler: Send + Sync {
    async fn handle(&self, request: Request) -> Result<Response, Error>;
    fn set_next(&mut self, next: Box<dyn Handler>);
}

struct AuthHandler {
    next: Option<Box<dyn Handler>>,
}

#[async_trait]
impl Handler for AuthHandler {
    async fn handle(&self, request: Request) -> Result<Response, Error> {
        // 验证认证
        if !request.is_authenticated() {
            return Err(Error::Unauthorized);
        }
        
        // 传递给下一个处理器
        if let Some(next) = &self.next {
            next.handle(request).await
        } else {
            Ok(Response::default())
        }
    }
    
    fn set_next(&mut self, next: Box<dyn Handler>) {
        self.next = Some(next);
    }
}

// 构建责任链
let mut auth = Box::new(AuthHandler { next: None });
let mut logging = Box::new(LoggingHandler { next: None });
let business = Box::new(BusinessHandler);

logging.set_next(business);
auth.set_next(logging);

// 使用
let response = auth.handle(request).await?;
```

---

*（文档继续...由于长度限制，剩余章节将在后续文件中创建）*-

## 相关文档

- [第二部分: 运行时与实践](./ASYNC_RUNTIME_GUIDE_2025.md)
- [第三部分: 架构模式](./ASYNC_ARCHITECTURE_PATTERNS_2025.md)
- [第四部分: 高级优化](./ASYNC_OPTIMIZATION_GUIDE_2025.md)
- [示例代码集合](../examples/)

---

**版权信息**: MIT License  
**维护者**: Rust Async Team  
**最后更新**: 2025-10-04
