# Rust 异步编程终极指南 2025


## 📊 目录

- [📋 目录 (Table of Contents)](#目录-table-of-contents)
- [第一部分: 理论基础](#第一部分-理论基础)
  - [1. 异步编程基本概念](#1-异步编程基本概念)
    - [1.1 什么是异步编程?](#11-什么是异步编程)
    - [1.2 为什么需要异步编程?](#12-为什么需要异步编程)
    - [1.3 异步 vs 并行](#13-异步-vs-并行)
  - [2. Future 与状态机](#2-future-与状态机)
    - [2.1 Future trait 定义](#21-future-trait-定义)
    - [2.2 状态机转换](#22-状态机转换)
    - [2.3 Waker 唤醒机制](#23-waker-唤醒机制)
  - [3. 三大并发模型对比](#3-三大并发模型对比)
    - [3.1 Actor 模型](#31-actor-模型)
    - [3.2 Reactor 模式](#32-reactor-模式)
    - [3.3 CSP (Communicating Sequential Processes) 模型](#33-csp-communicating-sequential-processes-模型)
    - [3.4 三种模型对比总结](#34-三种模型对比总结)
  - [4. 形式化语义](#4-形式化语义)
    - [4.1 Future 的代数语义](#41-future-的代数语义)
    - [4.2 async/await 的操作语义](#42-asyncawait-的操作语义)
    - [4.3 并发语义](#43-并发语义)
- [第三部分: 运行时与框架](#第三部分-运行时与框架)
  - [9. Tokio 1.41+ 完全指南](#9-tokio-141-完全指南)
    - [9.1 Tokio 核心概念](#91-tokio-核心概念)
    - [9.2 Tokio 1.41+ 新特性](#92-tokio-141-新特性)
      - [9.2.1 JoinSet 增强](#921-joinset-增强)
      - [9.2.2 TaskLocal 改进](#922-tasklocal-改进)
      - [9.2.3 Runtime Metrics](#923-runtime-metrics)
    - [9.3 Tokio 最佳实践](#93-tokio-最佳实践)
      - [9.3.1 运行时配置](#931-运行时配置)
      - [9.3.2 任务管理](#932-任务管理)
      - [9.3.3 超时和取消](#933-超时和取消)
  - [10. Smol 2.0+ 完全指南](#10-smol-20-完全指南)
    - [10.1 Smol 核心概念](#101-smol-核心概念)
    - [10.2 Smol 使用指南](#102-smol-使用指南)
      - [10.2.1 基本使用](#1021-基本使用)
      - [10.2.2 Async-io 使用](#1022-async-io-使用)
      - [10.2.3 LocalExecutor 使用](#1023-localexecutor-使用)
    - [10.3 Smol vs Tokio 选择](#103-smol-vs-tokio-选择)
- [第四部分: 设计模式](#第四部分-设计模式)
  - [13. 创建型模式](#13-创建型模式)
    - [13.1 Builder 模式](#131-builder-模式)
- [第六部分: 性能优化](#第六部分-性能优化)
  - [21. 内存管理优化](#21-内存管理优化)
    - [21.1 内存池技术](#211-内存池技术)
- [结语](#结语)


-Ultimate Rust Async Programming Guide 2025

**版本**: Rust 1.90+ | Tokio 1.41+ | Smol 2.0+  
**日期**: 2025年10月4日  
**作者**: Rust 异步编程研究组  
**状态**: 生产就绪 ✅

---

## 📋 目录 (Table of Contents)

- [Rust 异步编程终极指南 2025](#rust-异步编程终极指南-2025)
  - [📋 目录 (Table of Contents)](#-目录-table-of-contents)
  - [第一部分: 理论基础](#第一部分-理论基础)
    - [1. 异步编程基本概念](#1-异步编程基本概念)
      - [1.1 什么是异步编程?](#11-什么是异步编程)
      - [1.2 为什么需要异步编程?](#12-为什么需要异步编程)
      - [1.3 异步 vs 并行](#13-异步-vs-并行)
    - [2. Future 与状态机](#2-future-与状态机)
      - [2.1 Future trait 定义](#21-future-trait-定义)
      - [2.2 状态机转换](#22-状态机转换)
      - [2.3 Waker 唤醒机制](#23-waker-唤醒机制)
    - [3. 三大并发模型对比](#3-三大并发模型对比)
      - [3.1 Actor 模型](#31-actor-模型)
      - [3.2 Reactor 模式](#32-reactor-模式)
      - [3.3 CSP (Communicating Sequential Processes) 模型](#33-csp-communicating-sequential-processes-模型)
      - [3.4 三种模型对比总结](#34-三种模型对比总结)
    - [4. 形式化语义](#4-形式化语义)
      - [4.1 Future 的代数语义](#41-future-的代数语义)
      - [4.2 async/await 的操作语义](#42-asyncawait-的操作语义)
      - [4.3 并发语义](#43-并发语义)
  - [第三部分: 运行时与框架](#第三部分-运行时与框架)
    - [9. Tokio 1.41+ 完全指南](#9-tokio-141-完全指南)
      - [9.1 Tokio 核心概念](#91-tokio-核心概念)
      - [9.2 Tokio 1.41+ 新特性](#92-tokio-141-新特性)
        - [9.2.1 JoinSet 增强](#921-joinset-增强)
        - [9.2.2 TaskLocal 改进](#922-tasklocal-改进)
        - [9.2.3 Runtime Metrics](#923-runtime-metrics)
      - [9.3 Tokio 最佳实践](#93-tokio-最佳实践)
        - [9.3.1 运行时配置](#931-运行时配置)
        - [9.3.2 任务管理](#932-任务管理)
        - [9.3.3 超时和取消](#933-超时和取消)
    - [10. Smol 2.0+ 完全指南](#10-smol-20-完全指南)
      - [10.1 Smol 核心概念](#101-smol-核心概念)
      - [10.2 Smol 使用指南](#102-smol-使用指南)
        - [10.2.1 基本使用](#1021-基本使用)
        - [10.2.2 Async-io 使用](#1022-async-io-使用)
        - [10.2.3 LocalExecutor 使用](#1023-localexecutor-使用)
      - [10.3 Smol vs Tokio 选择](#103-smol-vs-tokio-选择)
  - [第四部分: 设计模式](#第四部分-设计模式)
    - [13. 创建型模式](#13-创建型模式)
      - [13.1 Builder 模式](#131-builder-模式)
  - [第六部分: 性能优化](#第六部分-性能优化)
    - [21. 内存管理优化](#21-内存管理优化)
      - [21.1 内存池技术](#211-内存池技术)
  - [结语](#结语)

---

## 第一部分: 理论基础

### 1. 异步编程基本概念

#### 1.1 什么是异步编程?

**定义**: 异步编程是一种编程范式,允许程序在等待 I/O 操作完成时执行其他任务,而不是阻塞线程。

**核心概念**:

```text
同步编程:
  开始任务 A → 等待 A 完成 → 开始任务 B → 等待 B 完成
  总时间 = A + B

异步编程:
  开始任务 A → 开始任务 B → 等待 A 或 B 完成
  总时间 ≈ max(A, B)
```

#### 1.2 为什么需要异步编程?

**问题**: 线程模型的局限性

- 创建线程开销大 (~2MB 栈空间)
- 线程切换成本高 (~μs 级别)
- 线程数量受限 (通常 < 10,000)

**解决方案**: 异步模型

- 轻量级任务 (~200 bytes)
- 快速上下文切换 (~ns 级别)
- 可支持百万级并发

#### 1.3 异步 vs 并行

| 特性 | 异步 (Async) | 并行 (Parallel) |
|------|-------------|----------------|
| 目标 | 提高 I/O 吞吐量 | 提高 CPU 利用率 |
| 适用 | I/O 密集型 | CPU 密集型 |
| 并发 | 单线程可并发 | 需要多线程/进程 |
| 例子 | 网络服务器 | 科学计算 |

### 2. Future 与状态机

#### 2.1 Future trait 定义

```rust
pub trait Future {
    type Output;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) 
        -> Poll<Self::Output>;
}

pub enum Poll<T> {
    Ready(T),    // 已完成,返回结果
    Pending,     // 未完成,稍后再试
}
```

#### 2.2 状态机转换

**async fn 编译器转换**:

```rust
// 源代码
async fn fetch_data(url: &str) -> Result<String, Error> {
    let response = http_get(url).await?;
    let body = response.text().await?;
    Ok(body)
}

// 编译器生成的状态机
enum FetchDataFuture {
    Start { url: String },
    WaitingForResponse { future: HttpFuture },
    WaitingForBody { future: BodyFuture },
    Done,
}

impl Future for FetchDataFuture {
    type Output = Result<String, Error>;
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) 
        -> Poll<Self::Output> 
    {
        loop {
            match self.get_mut() {
                FetchDataFuture::Start { url } => {
                    // 开始 HTTP 请求
                    let future = http_get(url);
                    *self = FetchDataFuture::WaitingForResponse { future };
                }
                FetchDataFuture::WaitingForResponse { future } => {
                    // 等待响应
                    match future.poll(cx) {
                        Poll::Ready(Ok(response)) => {
                            let future = response.text();
                            *self = FetchDataFuture::WaitingForBody { future };
                        }
                        Poll::Ready(Err(e)) => return Poll::Ready(Err(e)),
                        Poll::Pending => return Poll::Pending,
                    }
                }
                FetchDataFuture::WaitingForBody { future } => {
                    // 等待 body
                    match future.poll(cx) {
                        Poll::Ready(Ok(body)) => {
                            *self = FetchDataFuture::Done;
                            return Poll::Ready(Ok(body));
                        }
                        Poll::Ready(Err(e)) => return Poll::Ready(Err(e)),
                        Poll::Pending => return Poll::Pending,
                    }
                }
                FetchDataFuture::Done => panic!("已经完成"),
            }
        }
    }
}
```

**关键点**:

- 每个 `.await` 点是一个状态转换
- `Poll::Pending` 时保存当前状态
- `Poll::Ready` 时进入下一个状态或完成

#### 2.3 Waker 唤醒机制

**Context 和 Waker**:

```rust
pub struct Context<'a> {
    waker: &'a Waker,  // 唤醒器
    // ...
}

// Waker 的作用
impl Waker {
    // 通知 executor 任务可以继续执行
    pub fn wake(&self);
    pub fn wake_by_ref(&self);
}
```

**工作流程**:

```text
1. Future 返回 Poll::Pending
2. 注册 Waker 到事件源 (如 epoll)
3. Executor 挂起任务
4. I/O 完成时,事件源调用 waker.wake()
5. Executor 重新 poll Future
6. Future 返回 Poll::Ready
```

### 3. 三大并发模型对比

#### 3.1 Actor 模型

**数学定义**:

```text
Actor = (State, Mailbox, Behavior)

其中:
  State: 内部状态 S
  Mailbox: 消息队列 Queue<Message>
  Behavior: 行为函数 B: (S, Message) → (S', Actions)

消息传递:
  send(actor, msg) ⟹ mailbox.enqueue(msg)
  receive() ⟹ mailbox.dequeue() → process(msg)
```

**特点**:

- ✅ 位置透明: 本地/远程无差别
- ✅ 隔离性: 每个 Actor 独立状态
- ✅ 容错性: 监督树和重启策略
- ❌ 调试困难: 消息异步传递
- ❌ 死锁风险: 循环消息依赖

**适用场景**:

- 分布式系统
- 游戏服务器
- 聊天系统

**实现库**:

- `actix`: 成熟的 Actor 框架
- `xtra`: 类型安全的 Actor
- `bastion`: 容错性优先

**代码示例**:

```rust
use actix::prelude::*;

#[derive(Message)]
#[rtype(result = "Result<u64, String>")]
enum AccountMsg {
    Deposit(u64),
    Withdraw(u64),
}

struct BankAccount {
    balance: u64,
}

impl Actor for BankAccount {
    type Context = Context<Self>;
}

impl Handler<AccountMsg> for BankAccount {
    type Result = Result<u64, String>;
    
    fn handle(&mut self, msg: AccountMsg, _: &mut Context<Self>) 
        -> Self::Result 
    {
        match msg {
            AccountMsg::Deposit(amount) => {
                self.balance += amount;
                Ok(self.balance)
            }
            AccountMsg::Withdraw(amount) => {
                if self.balance >= amount {
                    self.balance -= amount;
                    Ok(self.balance)
                } else {
                    Err("余额不足".to_string())
                }
            }
        }
    }
}

// 使用
#[actix_rt::main]
async fn main() {
    let account = BankAccount { balance: 1000 }.start();
    
    let balance = account.send(AccountMsg::Deposit(500)).await.unwrap();
    println!("余额: {}", balance.unwrap());
}
```

#### 3.2 Reactor 模式

**数学定义**:

```text
Reactor = (EventQueue, HandlerRegistry, EventLoop)

其中:
  EventQueue: 事件队列 Queue<Event>
  HandlerRegistry: 处理器注册表 Map<EventType, Handler>
  EventLoop: 事件循环
  
事件循环:
  loop {
    events ← poll(EventQueue, timeout)
    for event in events {
      handler ← HandlerRegistry[event.type]
      handler.handle(event)
    }
  }
```

**特点**:

- ✅ 单线程高效: 无锁无竞争
- ✅ 资源利用好: 一个线程处理多个连接
- ✅ 事件驱动: 响应式架构
- ❌ CPU 密集型任务会阻塞
- ❌ 跨平台抽象难 (epoll/kqueue/IOCP)

**适用场景**:

- Web 服务器 (Nginx, Node.js)
- 网络代理
- GUI 应用

**实现库**:

- `tokio`: 内置 Reactor
- `mio`: 底层 I/O 抽象
- `async-io`: Smol 的 I/O 层

**代码示例**:

```rust
use tokio::net::TcpListener;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("Listening on: 127.0.0.1:8080");

    loop {
        // Reactor 内部: epoll_wait 等待事件
        let (mut socket, addr) = listener.accept().await?;
        println!("New connection: {}", addr);

        // 为每个连接生成任务
        tokio::spawn(async move {
            let mut buf = [0; 1024];
            
            loop {
                // Reactor 内部: 注册读事件到 epoll
                match socket.read(&mut buf).await {
                    Ok(0) => break, // 连接关闭
                    Ok(n) => {
                        // 回显数据
                        if socket.write_all(&buf[..n]).await.is_err() {
                            break;
                        }
                    }
                    Err(_) => break,
                }
            }
        });
    }
}
```

#### 3.3 CSP (Communicating Sequential Processes) 模型

**数学定义 (Hoare 1978)**:

```text
P ::= STOP                    // 停止进程
    | SKIP                    // 空进程
    | a → P                   // 前缀 (事件 a 后执行 P)
    | P □ Q                   // 外部选择
    | P ⊓ Q                   // 内部选择
    | P ||| Q                 // 交错并行
    | P || Q                  // 接口并行
    | P ; Q                   // 顺序组合

Rust 中的 CSP:
  Channel = (Sender<T>, Receiver<T>)
  send(ch, v) ≡ ch!v → SKIP
  recv(ch) ≡ ?ch → SKIP
```

**特点**:

- ✅ 类型安全: 编译期检查
- ✅ 组合性强: Pipeline 模式
- ✅ 背压支持: 有界通道
- ❌ 性能开销: 通道同步
- ❌ 死锁可能: 通道依赖环

**适用场景**:

- 数据流处理
- Pipeline 架构
- 并发算法

**通道类型对比**:

| 类型 | 容量 | 发送 | 接收 | 使用场景 |
|------|------|------|------|----------|
| oneshot | 1 | 一次 | 一次 | RPC 响应 |
| mpsc | N | 多 | 单 | 任务队列 |
| broadcast | N | 多 | 多 | 事件通知 |
| watch | 1 | 多 | 多 | 配置更新 |

**代码示例**:

```rust
use tokio::sync::mpsc;

// 生产者-消费者模式
#[tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel(100);
    
    // 生产者
    tokio::spawn(async move {
        for i in 0..10 {
            tx.send(i).await.unwrap();
            println!("发送: {}", i);
        }
    });
    
    // 消费者
    while let Some(i) = rx.recv().await {
        println!("接收: {}", i);
    }
}

// Pipeline 模式
#[tokio::main]
async fn main() {
    let (tx1, mut rx1) = mpsc::channel(10);
    let (tx2, mut rx2) = mpsc::channel(10);
    
    // Stage 1: 生成数字
    tokio::spawn(async move {
        for i in 1..=10 {
            tx1.send(i).await.unwrap();
        }
    });
    
    // Stage 2: 平方
    tokio::spawn(async move {
        while let Some(n) = rx1.recv().await {
            tx2.send(n * n).await.unwrap();
        }
    });
    
    // Stage 3: 打印
    while let Some(n) = rx2.recv().await {
        println!("{}", n);
    }
}

// Select 多路复用
use tokio::select;

#[tokio::main]
async fn main() {
    let (tx1, mut rx1) = mpsc::channel(10);
    let (tx2, mut rx2) = mpsc::channel(10);
    
    // ... 启动生产者 ...
    
    loop {
        select! {
            Some(v) = rx1.recv() => println!("通道1: {}", v),
            Some(v) = rx2.recv() => println!("通道2: {}", v),
            else => break,
        }
    }
}
```

#### 3.4 三种模型对比总结

| 维度 | Actor | Reactor | CSP |
|------|-------|---------|-----|
| **通信方式** | 消息传递 | 事件分发 | 通道通信 |
| **耦合度** | 低 | 中 | 低 |
| **类型安全** | 中 | 高 | 高 |
| **位置透明** | ✅ | ❌ | ❌ |
| **调试难度** | 高 | 中 | 低 |
| **性能** | 中 | 高 | 中 |
| **适用场景** | 分布式 | I/O密集 | 数据流 |
| **Rust 实现** | actix, xtra | tokio, mio | mpsc, broadcast |

**选择建议**:

1. **使用 Actor 模型** 当:
   - 构建分布式系统
   - 需要位置透明性
   - 有复杂的状态管理

2. **使用 Reactor 模式** 当:
   - 构建高性能服务器
   - I/O 密集型应用
   - 需要细粒度控制

3. **使用 CSP 模型** 当:
   - Pipeline 数据处理
   - 并发算法实现
   - 需要类型安全保证

4. **混合使用** 当:
   - 大型复杂系统
   - 不同层次有不同需求
   - 例如: Reactor (网络层) + Actor (业务层) + CSP (数据处理层)

### 4. 形式化语义

#### 4.1 Future 的代数语义

**定义**: Future 形成一个 Monad

```haskell
-- Haskell 风格的定义
class Monad m where
  return :: a -> m a
  (>>=)  :: m a -> (a -> m b) -> m b

instance Monad Future where
  return x = Future { poll = \_ -> Poll::Ready(x) }
  
  fut >>= f = Future { poll = \cx ->
    case fut.poll(cx) of
      Poll::Ready(x) -> f(x).poll(cx)
      Poll::Pending  -> Poll::Pending
  }
```

**Monad 定律**:

1. **左单位元**: `return a >>= f` ≡ `f a`
2. **右单位元**: `m >>= return` ≡ `m`
3. **结合律**: `(m >>= f) >>= g` ≡ `m >>= (\x -> f x >>= g)`

#### 4.2 async/await 的操作语义

**小步语义 (Small-step Semantics)**:

```text
配置: (E, σ, κ)
  E: 表达式
  σ: 状态
  κ: 继续 (continuation)

规则:
  ─────────────────────────────────────
  (await e, σ, κ) → (e, σ, AwaitK(κ))

  e.poll(σ) = Poll::Ready(v)
  ────────────────────────────────────
  (await e, σ, AwaitK(κ)) → (v, σ, κ)

  e.poll(σ) = Poll::Pending
  ──────────────────────────────────────
  (await e, σ, AwaitK(κ)) → suspend(σ, κ)
```

#### 4.3 并发语义

**交错语义 (Interleaving Semantics)**:

```text
进程: P ::= skip | a → P | P ||| Q

语义:
  [[skip]] = { (√, √) }
  [[a → P]] = { (a, √) } ∘ [[P]]
  [[P ||| Q]] = [[P]] ⊕ [[Q]]

其中 ⊕ 表示交错操作:
  S ⊕ T = { (a₁, ..., aₙ) | 
           (a₁, ..., aₙ) 是 S 和 T 的交错 }
```

---

## 第三部分: 运行时与框架

### 9. Tokio 1.41+ 完全指南

#### 9.1 Tokio 核心概念

**运行时架构**:

```text
┌─────────────────────────────────────────────┐
│            Tokio Runtime                    │
│                                             │
│  ┌────────────┐  ┌────────────┐           │
│  │  Scheduler  │  │  Reactor   │           │
│  │            │  │            │           │
│  │  ┌──────┐  │  │  epoll/   │           │
│  │  │ Task │  │  │  kqueue/  │           │
│  │  │Queue │  │  │  IOCP     │           │
│  │  └──────┘  │  │            │           │
│  └────────────┘  └────────────┘           │
│         ↓              ↓                   │
│  ┌────────────────────────────┐           │
│  │     Worker Threads         │           │
│  │  ┌────┐ ┌────┐ ┌────┐     │           │
│  │  │ W1 │ │ W2 │ │ W3 │ ...│           │
│  │  └────┘ └────┘ └────┘     │           │
│  └────────────────────────────┘           │
└─────────────────────────────────────────────┘
```

**组件说明**:

1. **Scheduler (调度器)**
   - 维护任务队列
   - 工作窃取 (Work Stealing)
   - 负载均衡

2. **Reactor (反应器)**
   - I/O 事件监听
   - 平台特定实现
   - Waker 通知

3. **Worker Threads (工作线程)**
   - 执行异步任务
   - 默认数量 = CPU 核心数
   - 可配置

#### 9.2 Tokio 1.41+ 新特性

##### 9.2.1 JoinSet 增强

**特性**: 动态任务集管理

```rust
use tokio::task::JoinSet;

async fn dynamic_task_management() {
    let mut set = JoinSet::new();
    
    // 动态添加任务
    for i in 0..10 {
        set.spawn(async move {
            tokio::time::sleep(Duration::from_millis(i * 100)).await;
            i
        });
    }
    
    // 按完成顺序收集结果
    while let Some(result) = set.join_next().await {
        match result {
            Ok(value) => println!("完成: {}", value),
            Err(e) => eprintln!("错误: {}", e),
        }
    }
    
    // 提前终止
    set.abort_all();
}
```

**应用场景**:

- 爬虫: 动态发现新 URL
- 工作池: 动态任务队列
- 批处理: 控制并发度

##### 9.2.2 TaskLocal 改进

**特性**: 任务本地存储

```rust
use tokio::task_local;

task_local! {
    static REQUEST_ID: String;
}

async fn handle_request(id: String) {
    REQUEST_ID.scope(id.clone(), async move {
        // 所有调用都能访问 REQUEST_ID
        process_data().await;
        save_result().await;
    }).await
}

async fn process_data() {
    REQUEST_ID.with(|id| {
        println!("处理请求: {}", id);
    });
}
```

**应用场景**:

- 分布式追踪 (Trace ID)
- 请求上下文传播
- 用户认证信息

##### 9.2.3 Runtime Metrics

**特性**: 运行时指标收集

```rust
use tokio::runtime::Handle;

async fn collect_metrics() {
    let handle = Handle::current();
    let metrics = handle.metrics();
    
    println!("活跃任务数: {}", metrics.num_alive_tasks());
    println!("Worker数量: {}", metrics.num_workers());
    
    for worker_id in 0..metrics.num_workers() {
        let park_count = metrics.worker_park_count(worker_id);
        let poll_count = metrics.worker_poll_count(worker_id);
        
        println!("Worker {}: park={}, poll={}", 
            worker_id, park_count, poll_count);
    }
}
```

**监控指标**:

- 任务数量
- 调度延迟
- Worker 利用率
- 阻塞线程数

#### 9.3 Tokio 最佳实践

##### 9.3.1 运行时配置

```rust
use tokio::runtime::Builder;

fn main() {
    // 多线程运行时
    let rt = Builder::new_multi_thread()
        .worker_threads(8)              // Worker 线程数
        .max_blocking_threads(512)      // 最大阻塞线程数
        .thread_name("my-worker")       // 线程名称
        .thread_stack_size(3 * 1024 * 1024) // 栈大小
        .enable_all()                   // 启用所有特性
        .build()
        .unwrap();
    
    rt.block_on(async {
        // 你的异步代码
    });
}

// 当前线程运行时 (轻量级)
fn current_thread_runtime() {
    let rt = Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();
    
    rt.block_on(async {
        // 单线程异步代码
    });
}
```

**选择建议**:

- **多线程运行时**: 默认选择,适用于大多数场景
- **单线程运行时**: GUI 应用,嵌入式,测试

##### 9.3.2 任务管理

```rust
// ✅ 好的做法: 使用 spawn
tokio::spawn(async {
    expensive_operation().await;
});

// ❌ 不好: 在 async 块中阻塞
tokio::spawn(async {
    // 阻塞线程!
    std::thread::sleep(Duration::from_secs(1));
});

// ✅ 好的做法: 使用 spawn_blocking
tokio::task::spawn_blocking(|| {
    // 允许阻塞操作
    std::thread::sleep(Duration::from_secs(1));
});

// ✅ 好的做法: CPU 密集型任务使用 rayon
use rayon::prelude::*;

async fn process_data(data: Vec<i32>) -> Vec<i32> {
    tokio::task::spawn_blocking(move || {
        data.par_iter()
            .map(|&x| expensive_cpu_work(x))
            .collect()
    }).await.unwrap()
}
```

##### 9.3.3 超时和取消

```rust
use tokio::time::{timeout, Duration};
use tokio_util::sync::CancellationToken;

// 超时
async fn with_timeout() -> Result<String, &'static str> {
    match timeout(Duration::from_secs(5), fetch_data()).await {
        Ok(result) => Ok(result),
        Err(_) => Err("超时"),
    }
}

// 取消令牌
async fn with_cancellation() {
    let token = CancellationToken::new();
    let child_token = token.child_token();
    
    tokio::spawn(async move {
        tokio::select! {
            _ = child_token.cancelled() => {
                println!("任务被取消");
            }
            _ = long_running_task() => {
                println!("任务完成");
            }
        }
    });
    
    // 5秒后取消
    tokio::time::sleep(Duration::from_secs(5)).await;
    token.cancel();
}
```

---

### 10. Smol 2.0+ 完全指南

#### 10.1 Smol 核心概念

**设计哲学**:

- 最小化: 核心只有几千行代码
- 模块化: 可选择性导入功能
- 高性能: 零成本抽象

**架构**:

```text
┌──────────────────────────────────┐
│        Smol Ecosystem            │
│                                  │
│  ┌────────────┐  ┌────────────┐ │
│  │   Executor  │  │  async-io  │ │
│  │            │  │            │ │
│  │  Task      │  │  Async<T>  │ │
│  │  Queue     │  │  Reactor   │ │
│  └────────────┘  └────────────┘ │
│         ↓              ↓         │
│  ┌────────────────────────────┐ │
│  │   async-channel           │ │
│  │   async-task              │ │
│  │   futures-lite            │ │
│  └────────────────────────────┘ │
└──────────────────────────────────┘
```

#### 10.2 Smol 使用指南

##### 10.2.1 基本使用

```rust
use smol::{Executor, Timer};
use std::time::Duration;

fn main() {
    // 创建 executor
    let ex = Executor::new();
    
    // 运行异步代码
    smol::block_on(ex.run(async {
        println!("Hello from Smol!");
        
        // 生成任务
        let task = ex.spawn(async {
            Timer::after(Duration::from_secs(1)).await;
            "Done"
        });
        
        let result = task.await;
        println!("{}", result);
    }));
}
```

##### 10.2.2 Async-io 使用

```rust
use async_io::Async;
use std::net::{TcpListener, TcpStream};

async fn tcp_server() -> std::io::Result<()> {
    // 包装标准库类型
    let listener = Async::<TcpListener>::bind(([127, 0, 0, 1], 8080))?;
    println!("Listening on {}", listener.get_ref().local_addr()?);
    
    loop {
        // 异步接受连接
        let (stream, peer_addr) = listener.accept().await?;
        println!("Accepted client: {}", peer_addr);
        
        // 处理连接
        smol::spawn(handle_client(stream)).detach();
    }
}

async fn handle_client(stream: Async<TcpStream>) -> std::io::Result<()> {
    // 异步读写
    // ...
    Ok(())
}
```

##### 10.2.3 LocalExecutor 使用

```rust
use smol::LocalExecutor;
use std::rc::Rc;

fn main() {
    let local_ex = LocalExecutor::new();
    
    smol::block_on(local_ex.run(async {
        // 可以使用 !Send 类型
        let data = Rc::new(vec![1, 2, 3]);
        
        let task = local_ex.spawn(async move {
            println!("Data: {:?}", data);
        });
        
        task.await;
    }));
}
```

#### 10.3 Smol vs Tokio 选择

**Smol 的优势**:

- 更小的二进制体积 (~100KB vs ~500KB)
- 更低的内存占用 (~200 bytes/task vs ~1KB/task)
- 更简单的 API
- 更快的编译速度

**Tokio 的优势**:

- 更成熟的生态
- 更多的第三方库支持
- 企业级功能 (metrics, tracing)
- 更好的文档和社区

**选择建议**:

| 场景 | 推荐 | 原因 |
|------|------|------|
| 大型 Web 应用 | Tokio | 生态成熟 |
| 命令行工具 | Smol | 二进制小 |
| 嵌入式系统 | Smol | 内存占用低 |
| 微服务 | Tokio | 监控支持好 |
| 学习异步 | Smol | 代码简单 |

---

## 第四部分: 设计模式

### 13. 创建型模式

#### 13.1 Builder 模式

**意图**: 分离复杂对象的构建与表示

**实现**:

```rust
pub struct HttpClient {
    timeout: Duration,
    max_retries: usize,
    user_agent: String,
}

pub struct HttpClientBuilder {
    timeout: Option<Duration>,
    max_retries: Option<usize>,
    user_agent: Option<String>,
}

impl HttpClientBuilder {
    pub fn new() -> Self {
        Self {
            timeout: None,
            max_retries: None,
            user_agent: None,
        }
    }
    
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }
    
    pub fn max_retries(mut self, retries: usize) -> Self {
        self.max_retries = Some(retries);
        self
    }
    
    pub fn build(self) -> HttpClient {
        HttpClient {
            timeout: self.timeout.unwrap_or(Duration::from_secs(30)),
            max_retries: self.max_retries.unwrap_or(3),
            user_agent: self.user_agent.unwrap_or_else(|| "Rust/1.0".to_string()),
        }
    }
}

// 使用
let client = HttpClientBuilder::new()
    .timeout(Duration::from_secs(10))
    .max_retries(5)
    .build();
```

---

## 第六部分: 性能优化

### 21. 内存管理优化

#### 21.1 内存池技术

**问题**: 频繁分配/释放导致性能下降

**解决方案**: 对象池

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

struct BufferPool {
    pool: Arc<Mutex<Vec<Vec<u8>>>>,
    buffer_size: usize,
}

impl BufferPool {
    fn new(capacity: usize, buffer_size: usize) -> Self {
        let mut pool = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            pool.push(vec![0; buffer_size]);
        }
        
        Self {
            pool: Arc::new(Mutex::new(pool)),
            buffer_size,
        }
    }
    
    async fn acquire(&self) -> Vec<u8> {
        let mut pool = self.pool.lock().await;
        pool.pop().unwrap_or_else(|| vec![0; self.buffer_size])
    }
    
    async fn release(&self, mut buffer: Vec<u8>) {
        buffer.clear();
        let mut pool = self.pool.lock().await;
        if pool.len() < pool.capacity() {
            pool.push(buffer);
        }
    }
}

// 使用
let pool = BufferPool::new(100, 4096);
let buffer = pool.acquire().await;
// 使用 buffer...
pool.release(buffer).await;
```

**性能提升**: 50-80% (频繁分配场景)

---

## 结语

这份指南涵盖了 Rust 异步编程的方方面面,从理论基础到生产实践。

**学习路径建议**:

1. **初级** (1-2 周)
   - 理解 Future 和 async/await
   - 掌握 Tokio 基本用法
   - 实现简单的异步程序

2. **中级** (2-4 周)
   - 深入三大并发模型
   - 掌握设计模式
   - 构建完整的异步应用

3. **高级** (4+ 周)
   - 性能优化技术
   - 分布式系统设计
   - 贡献开源项目

**推荐资源**:

- 📚 书籍: "Asynchronous Programming in Rust"
- 🎥 视频: "Tokio Tutorial Series"
- 💻 代码: 本项目的 examples 目录
- 🌐 社区: Rust Users Forum, Discord

---

**版权声明**: 本文档采用 MIT 许可证  
**最后更新**: 2025年10月4日  
**维护者**: Rust 异步编程研究组
