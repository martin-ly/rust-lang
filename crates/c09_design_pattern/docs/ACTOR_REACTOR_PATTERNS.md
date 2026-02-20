# Actor与Reactor模式：异步调度机制的形式化分析

## 目录

- [Actor与Reactor模式：异步调度机制的形式化分析](#actor与reactor模式异步调度机制的形式化分析)
  - [目录](#目录)
  - [1. 理论基础](#1-理论基础)
    - [1.1 并发模型分类](#11-并发模型分类)
    - [1.2 事件驱动架构](#12-事件驱动架构)
  - [2. Actor模型](#2-actor模型)
    - [2.1 形式化定义](#21-形式化定义)
      - [定义2.1（Actor）](#定义21actor)
      - [Actions（动作集合）](#actions动作集合)
    - [2.2 操作语义](#22-操作语义)
      - [消息传递语义](#消息传递语义)
      - [执行模型（小步语义）](#执行模型小步语义)
    - [2.3 Actor律（Actor Laws）](#23-actor律actor-laws)
      - [律1：消息顺序保证](#律1消息顺序保证)
      - [律2：不同发送者的消息无序](#律2不同发送者的消息无序)
      - [律3：Actor创建的确定性](#律3actor创建的确定性)
    - [2.4 Rust中的Actor实现](#24-rust中的actor实现)
      - [基于Channel的简单Actor](#基于channel的简单actor)
  - [3. Reactor模式](#3-reactor模式)
    - [3.1 形式化定义](#31-形式化定义)
      - [定义3.1（Reactor）](#定义31reactor)
      - [事件类型](#事件类型)
    - [3.2 操作语义](#32-操作语义)
      - [Reactor循环（伪代码）](#reactor循环伪代码)
      - [形式化（小步语义）](#形式化小步语义)
    - [3.3 Reactor模式的关键组件](#33-reactor模式的关键组件)
      - [1. 事件多路复用器（Demultiplexer）](#1-事件多路复用器demultiplexer)
      - [2. 事件处理器（Handler）](#2-事件处理器handler)
      - [3. Reactor核心](#3-reactor核心)
    - [3.4 Tokio中的Reactor实现](#34-tokio中的reactor实现)
  - [4. 对比分析](#4-对比分析)
    - [4.1 架构差异](#41-架构差异)
    - [4.2 组合关系](#42-组合关系)
    - [4.3 性能对比](#43-性能对比)
      - [Actor模型](#actor模型)
      - [Reactor模式](#reactor模式)
    - [4.4 形式化等价性](#44-形式化等价性)
      - [定理4.1（Actor到Reactor的编码）](#定理41actor到reactor的编码)
  - [5. Rust实现](#5-rust实现)
    - [5.1 完整Actor系统实现](#51-完整actor系统实现)
    - [5.2 简化的Reactor实现](#52-简化的reactor实现)
  - [6. 形式化证明](#6-形式化证明)
    - [6.1 Actor模型的正确性](#61-actor模型的正确性)
      - [定理6.1（消息传递的可靠性）](#定理61消息传递的可靠性)
      - [定理6.2（Actor的隔离性）](#定理62actor的隔离性)
    - [6.2 Reactor模式的活性](#62-reactor模式的活性)
      - [定理6.3（事件最终被处理）](#定理63事件最终被处理)
  - [7. 实践示例](#7-实践示例)
    - [7.1 聊天服务器（Actor模型）](#71-聊天服务器actor模型)
    - [7.2 HTTP服务器（Reactor模式）](#72-http服务器reactor模式)
    - [7.3 组合：Actor-based HTTP服务](#73-组合actor-based-http服务)
  - [8. 结论](#8-结论)
    - [核心要点](#核心要点)
    - [选择指南](#选择指南)

---

## 1. 理论基础

### 1.1 并发模型分类

并发编程模型可分为两大类：

1. **共享内存模型**（Shared Memory）
   - 线程通过共享变量通信
   - 需要锁/原子操作保证一致性
   - 例：Java Threads, POSIX threads

2. **消息传递模型**（Message Passing）
   - 进程/Actor通过消息通信
   - 无共享状态，消息作为同步点
   - 例：Erlang, Akka, Actor模型

### 1.2 事件驱动架构

**Reactor模式**是事件驱动架构的核心，基于以下原理：

- **事件循环**（Event Loop）：持续监听事件源
- **多路复用**（Multiplexing）：单线程处理多个IO源
- **回调/Future**：事件就绪时触发处理逻辑

---

## 2. Actor模型

### 2.1 形式化定义

#### 定义2.1（Actor）

Actor `α` 是一个自治的计算实体，定义为五元组：

```text
α = (S, M, B, s₀, addr)
```

其中：

- `S`: 内部状态空间
- `M`: 消息类型集合
- `B: S × M → S × Actions`: 行为函数
- `s₀ ∈ S`: 初始状态
- `addr`: 唯一地址

#### Actions（动作集合）

```text
Actions ::= send(addr, msg)        // 发送消息
          | create(ActorDef)        // 创建新Actor
          | become(Behavior)        // 改变行为
          | ε                       // 空动作
```

### 2.2 操作语义

#### 消息传递语义

```text
α₁ @ s₁ ─send(addr_α₂, m)→ α₁ @ s₁'
                ↓
            [mailbox_α₂]
                ↓
α₂ @ s₂ ─receive(m)→ α₂ @ s₂'
```

**关键性质**：

1. **异步性**：发送不阻塞
2. **隔离性**：Actor间无共享状态
3. **公平性**：邮箱中的消息最终会被处理

#### 执行模型（小步语义）

```text
────────────────────────────── (Actor-Send)
⟨send(α, m), σ⟩ → ⟨(), σ[mailbox(α) ← append(m)]⟩

mailbox(α) = m::ms    B(s, m) = (s', actions)
────────────────────────────────────────────── (Actor-Receive)
⟨α @ s, σ⟩ → ⟨actions, σ[α ← s', mailbox(α) ← ms]⟩
```

### 2.3 Actor律（Actor Laws）

#### 律1：消息顺序保证

对于同一发送者发给同一接收者的消息序列，接收顺序保持：

```text
send(α, m₁); send(α, m₂)  ⟹  receive(m₁) happens-before receive(m₂)
```

#### 律2：不同发送者的消息无序

来自不同发送者的消息可以以任意顺序交错：

```text
send_α₁(β, m₁) ∥ send_α₂(β, m₂)  ⟹  receive_order(m₁, m₂) ∈ {(m₁, m₂), (m₂, m₁)}
```

#### 律3：Actor创建的确定性

Actor的创建返回唯一地址：

```text
create(behavior) ⟹ ∃!addr. actor_at(addr) = behavior
```

### 2.4 Rust中的Actor实现

#### 基于Channel的简单Actor

```rust
use tokio::sync::mpsc;
use std::fmt::Debug;

/// Actor trait定义
pub trait Actor: Send + 'static {
    type Message: Send + Debug;

    /// 处理消息，返回新状态（可选）
    fn handle(&mut self, msg: Self::Message);
}

/// Actor运行时
pub struct ActorHandle<M> {
    sender: mpsc::UnboundedSender<M>,
}

impl<M: Send + 'static> ActorHandle<M> {
    /// 发送消息到Actor（异步、非阻塞）
    pub fn send(&self, msg: M) -> Result<(), mpsc::error::SendError<M>> {
        self.sender.send(msg)
    }
}

/// Actor系统
pub struct ActorSystem;

impl ActorSystem {
    /// 启动Actor，返回其句柄
    pub fn spawn<A: Actor>(mut actor: A) -> ActorHandle<A::Message> {
        let (tx, mut rx) = mpsc::unbounded_channel();

        tokio::spawn(async move {
            while let Some(msg) = rx.recv().await {
                actor.handle(msg);
            }
        });

        ActorHandle { sender: tx }
    }
}

/// 示例：计数器Actor
pub struct CounterActor {
    count: u64,
}

pub enum CounterMessage {
    Increment,
    Decrement,
    GetCount(tokio::sync::oneshot::Sender<u64>),
}

impl Actor for CounterActor {
    type Message = CounterMessage;

    fn handle(&mut self, msg: Self::Message) {
        match msg {
            CounterMessage::Increment => {
                self.count += 1;
                println!("Count: {}", self.count);
            }
            CounterMessage::Decrement => {
                self.count = self.count.saturating_sub(1);
                println!("Count: {}", self.count);
            }
            CounterMessage::GetCount(reply) => {
                let _ = reply.send(self.count);
            }
        }
    }
}
```

**使用示例**：

```rust
#[tokio::main]
async fn main() {
    let counter = CounterActor { count: 0 };
    let handle = ActorSystem::spawn(counter);

    // 发送消息（非阻塞）
    handle.send(CounterMessage::Increment).unwrap();
    handle.send(CounterMessage::Increment).unwrap();

    // 查询状态
    let (tx, rx) = tokio::sync::oneshot::channel();
    handle.send(CounterMessage::GetCount(tx)).unwrap();
    let count = rx.await.unwrap();
    println!("Final count: {}", count);
}
```

---

## 3. Reactor模式

### 3.1 形式化定义

#### 定义3.1（Reactor）

Reactor `R` 是事件驱动的调度器，定义为：

```text
R = (EventLoop, Demux, Handlers)
```

其中：

- `EventLoop`: 循环等待事件
- `Demux`: 多路复用器（如epoll, kqueue）
- `Handlers`: 事件处理器映射 `Event → Handler`

#### 事件类型

```text
Event ::= Readable(fd)      // 文件描述符可读
        | Writable(fd)      // 文件描述符可写
        | Timer(id)         // 定时器触发
        | Signal(sig)       // 信号到达
```

### 3.2 操作语义

#### Reactor循环（伪代码）

```text
loop {
    events = demux.wait();       // 阻塞等待事件
    for event in events {
        handler = handlers[event.type];
        handler.dispatch(event);  // 回调处理
    }
}
```

#### 形式化（小步语义）

```text
demux.ready() = ∅
───────────────────────── (Reactor-Wait)
⟨reactor, σ⟩ → ⟨reactor, σ⟩  (blocking)

demux.ready() = {e₁, ..., eₙ}    handlers[eᵢ] = hᵢ
────────────────────────────────────────────── (Reactor-Dispatch)
⟨reactor, σ⟩ → ⟨h₁(e₁); ...; hₙ(eₙ), σ'⟩
```

### 3.3 Reactor模式的关键组件

#### 1. 事件多路复用器（Demultiplexer）

```rust
use std::os::unix::io::RawFd;

pub enum Interest {
    Readable,
    Writable,
}

pub trait Demultiplexer {
    /// 注册文件描述符
    fn register(&mut self, fd: RawFd, interest: Interest);

    /// 等待事件（阻塞）
    fn wait(&mut self, timeout: Option<Duration>) -> Vec<Event>;

    /// 注销文件描述符
    fn unregister(&mut self, fd: RawFd);
}
```

#### 2. 事件处理器（Handler）

```rust
pub trait EventHandler {
    fn handle_read(&mut self, fd: RawFd);
    fn handle_write(&mut self, fd: RawFd);
    fn handle_error(&mut self, fd: RawFd, error: std::io::Error);
}
```

#### 3. Reactor核心

```rust
use std::collections::HashMap;

pub struct Reactor {
    demux: Box<dyn Demultiplexer>,
    handlers: HashMap<RawFd, Box<dyn EventHandler>>,
    running: bool,
}

impl Reactor {
    pub fn run(&mut self) {
        self.running = true;

        while self.running {
            let events = self.demux.wait(None);

            for event in events {
                if let Some(handler) = self.handlers.get_mut(&event.fd) {
                    match event.kind {
                        EventKind::Readable => handler.handle_read(event.fd),
                        EventKind::Writable => handler.handle_write(event.fd),
                        EventKind::Error(e) => handler.handle_error(event.fd, e),
                    }
                }
            }
        }
    }

    pub fn register(&mut self, fd: RawFd, handler: Box<dyn EventHandler>) {
        self.demux.register(fd, Interest::Readable);
        self.handlers.insert(fd, handler);
    }

    pub fn stop(&mut self) {
        self.running = false;
    }
}
```

### 3.4 Tokio中的Reactor实现

Tokio使用**mio**库实现跨平台的Reactor：

```rust
// 简化的Tokio Reactor架构
pub struct TokioReactor {
    // epoll (Linux) / kqueue (macOS) / IOCP (Windows)
    io_driver: mio::Poll,

    // 就绪队列
    ready_queue: VecDeque<Task>,

    // 定时器堆
    timer_wheel: TimerWheel,
}

impl TokioReactor {
    pub fn block_on<F: Future>(&mut self, fut: F) -> F::Output {
        let mut fut = std::pin::pin!(fut);
        let waker = self.create_waker();
        let mut cx = Context::from_waker(&waker);

        loop {
            // 1. Poll Future
            match fut.as_mut().poll(&mut cx) {
                Poll::Ready(output) => return output,
                Poll::Pending => {}
            }

            // 2. 处理就绪的IO事件
            self.drive_io();

            // 3. 处理到期的定时器
            self.drive_timers();

            // 4. 执行就绪任务
            self.run_ready_tasks();
        }
    }

    fn drive_io(&mut self) {
        let mut events = mio::Events::with_capacity(1024);
        self.io_driver.poll(&mut events, Some(Duration::ZERO)).unwrap();

        for event in events.iter() {
            // 唤醒等待该IO事件的Future
            self.wake_task(event.token());
        }
    }
}
```

---

## 4. 对比分析

### 4.1 架构差异

| 维度         | Actor模型              | Reactor模式        |
| :--- | :--- | :--- || **抽象级别** | 高层（业务逻辑）       | 低层（IO多路复用） |
| **通信方式** | 消息传递               | 事件回调           |
| **状态管理** | Actor内部状态          | Handler内部状态    |
| **并发单元** | Actor                  | 事件循环           |
| **调度方式** | 邮箱队列               | 就绪队列           |
| **典型应用** | 分布式系统、游戏服务器 | 网络服务器、异步IO |

### 4.2 组合关系

**Actor可以基于Reactor实现**：

```text
┌─────────────────────────────────┐
│         Actor Layer             │  (业务逻辑)
│  ┌──────┐  ┌──────┐  ┌──────┐   │
│  │Actor1│  │Actor2│  │Actor3│   │
│  └──┬───┘  └──┬───┘  └──┬───┘   │
│     │ msg     │ msg     │ msg   │
├─────┼─────────┼─────────┼───────┤
│     ↓         ↓         ↓       │
│  ┌───────────────────────────┐  │  (调度层)
│  │    Actor Scheduler        │  │
│  │  (基于消息队列的调度)       │  │
│  └────────────┬──────────────┘  │
├───────────────┼─────────────────┤
│               ↓                 │
│  ┌───────────────────────────┐  │  (IO层)
│  │       Reactor             │  │
│  │  ┌─────────────────────┐  │  │
│  │  │  Event Loop (epoll) │  │  │
│  │  └─────────────────────┘  │  │
│  └───────────────────────────┘  │
└─────────────────────────────────┘
```

### 4.3 性能对比

#### Actor模型

**优点**：

- 隔离性好，无数据竞争
- 易于扩展到分布式
- 背压控制天然（邮箱容量限制）

**缺点**：

- 消息复制开销
- 邮箱管理开销
- 不适合高频小消息

#### Reactor模式

**优点**：

- 高效IO多路复用
- 单线程处理高并发
- 零拷贝支持

**缺点**：

- 回调地狱（无async/await时）
- 难以处理CPU密集任务
- 错误处理复杂

### 4.4 形式化等价性

#### 定理4.1（Actor到Reactor的编码）

对于任意Actor系统 `AS = {α₁, ..., αₙ}`，存在Reactor系统 `R` 使得：

```text
behavior(AS) ≡ behavior(R)
```

**构造**：

1. 每个Actor邮箱映射为IO源（如管道）
2. Actor的`receive`映射为Reactor的事件处理
3. Actor的`send`映射为写事件

**证明略**（通过双模拟bisimulation）。

---

## 5. Rust实现

### 5.1 完整Actor系统实现

```rust
use tokio::sync::mpsc;
use std::collections::HashMap;
use std::sync::Arc;

/// Actor地址类型
pub type ActorAddr = u64;

/// Actor消息trait
pub trait Message: Send + 'static {}

/// Actor trait
pub trait Actor: Send + 'static {
    type Message: Message;

    fn handle(&mut self, msg: Self::Message, ctx: &mut ActorContext<Self>);
}

/// Actor上下文
pub struct ActorContext<A: Actor> {
    addr: ActorAddr,
    system: Arc<ActorSystemInner>,
    _phantom: std::marker::PhantomData<A>,
}

impl<A: Actor> ActorContext<A> {
    /// 发送消息到指定Actor
    pub fn send<T: Message>(&self, addr: ActorAddr, msg: T) {
        self.system.send(addr, Box::new(msg));
    }

    /// 停止当前Actor
    pub fn stop(&self) {
        self.system.stop_actor(self.addr);
    }
}

/// Actor系统内部
struct ActorSystemInner {
    actors: std::sync::Mutex<HashMap<ActorAddr, mpsc::UnboundedSender<Box<dyn Message>>>>,
    next_id: std::sync::atomic::AtomicU64,
}

impl ActorSystemInner {
    fn send(&self, addr: ActorAddr, msg: Box<dyn Message>) {
        let actors = self.actors.lock().unwrap();
        if let Some(sender) = actors.get(&addr) {
            let _ = sender.send(msg);
        }
    }

    fn stop_actor(&self, addr: ActorAddr) {
        let mut actors = self.actors.lock().unwrap();
        actors.remove(&addr);
    }
}

/// Actor系统
#[derive(Clone)]
pub struct ActorSystem {
    inner: Arc<ActorSystemInner>,
}

impl ActorSystem {
    pub fn new() -> Self {
        Self {
            inner: Arc::new(ActorSystemInner {
                actors: std::sync::Mutex::new(HashMap::new()),
                next_id: std::sync::atomic::AtomicU64::new(1),
            }),
        }
    }

    pub fn spawn<A: Actor>(&self, mut actor: A) -> ActorAddr {
        let addr = self.inner.next_id.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let (tx, mut rx) = mpsc::unbounded_channel::<Box<dyn Message>>();

        let inner = self.inner.clone();
        tokio::spawn(async move {
            let mut ctx = ActorContext {
                addr,
                system: inner,
                _phantom: std::marker::PhantomData,
            };

            while let Some(msg) = rx.recv().await {
                // 类型擦除恢复
                if let Some(typed_msg) = (msg as Box<dyn std::any::Any>).downcast::<A::Message>().ok() {
                    actor.handle(*typed_msg, &mut ctx);
                }
            }
        });

        self.inner.actors.lock().unwrap().insert(addr, tx);
        addr
    }
}
```

### 5.2 简化的Reactor实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};
use std::future::Future;
use std::pin::Pin;

/// 简化的Reactor
pub struct SimpleReactor {
    tasks: Arc<Mutex<HashMap<u64, Pin<Box<dyn Future<Output = ()> + Send>>>>>,
    wakers: Arc<Mutex<HashMap<u64, Waker>>>,
    next_id: Arc<std::sync::atomic::AtomicU64>,
}

impl SimpleReactor {
    pub fn new() -> Self {
        Self {
            tasks: Arc::new(Mutex::new(HashMap::new())),
            wakers: Arc::new(Mutex::new(HashMap::new())),
            next_id: Arc::new(std::sync::atomic::AtomicU64::new(0)),
        }
    }

    pub fn spawn<F>(&self, fut: F) -> u64
    where F: Future<Output = ()> + Send + 'static
    {
        let id = self.next_id.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        self.tasks.lock().unwrap().insert(id, Box::pin(fut));
        self.wake(id);
        id
    }

    pub fn wake(&self, id: u64) {
        if let Some(waker) = self.wakers.lock().unwrap().get(&id) {
            waker.wake_by_ref();
        }
    }

    pub fn run(&self) {
        loop {
            let mut tasks = self.tasks.lock().unwrap();
            if tasks.is_empty() {
                break;
            }

            let ids: Vec<u64> = tasks.keys().copied().collect();
            drop(tasks);

            for id in ids {
                self.poll_task(id);
            }
        }
    }

    fn poll_task(&self, id: u64) {
        let waker = self.create_waker(id);
        let mut cx = Context::from_waker(&waker);

        let mut tasks = self.tasks.lock().unwrap();
        if let Some(mut task) = tasks.remove(&id) {
            drop(tasks);

            match task.as_mut().poll(&mut cx) {
                Poll::Ready(()) => {
                    // 任务完成
                }
                Poll::Pending => {
                    // 重新加入
                    self.tasks.lock().unwrap().insert(id, task);
                }
            }
        }
    }

    fn create_waker(&self, id: u64) -> Waker {
        // 实际实现需要使用RawWaker
        unimplemented!("需要实现RawWaker")
    }
}
```

---

## 6. 形式化证明

### 6.1 Actor模型的正确性

#### 定理6.1（消息传递的可靠性）

在无故障的Actor系统中，发送的消息最终会被接收：

```text
∀α, β ∈ Actors, ∀m ∈ Messages:
    send(β, m) ⟹ ◇(β receives m)
```

其中 `◇` 表示"最终"（时态逻辑）。

**证明**：

1. 邮箱是FIFO队列，消息不会丢失
2. Actor是公平调度的，每个Actor最终会被调度
3. 因此，邮箱中的消息最终会被处理。∎

#### 定理6.2（Actor的隔离性）

不同Actor的状态不会相互干扰：

```text
∀α, β ∈ Actors (α ≠ β):
    state(α) ∩ state(β) = ∅
```

**证明**：

- 每个Actor有独立的状态空间
- 通信只通过消息传递，消息是值传递（copy）或所有权转移
- 因此状态不共享。∎

### 6.2 Reactor模式的活性

#### 定理6.3（事件最终被处理）

在公平调度下，就绪的事件最终会被处理：

```text
∀e ∈ Events: ready(e) ⟹ ◇(handle(e))
```

**证明**：

1. Reactor循环持续运行
2. `demux.wait()` 返回所有就绪事件
3. 循环体遍历所有就绪事件并调用handler
4. 因此每个就绪事件最终被处理。∎

---

## 7. 实践示例

### 7.1 聊天服务器（Actor模型）

```rust
use tokio::sync::mpsc;

pub enum ChatMessage {
    Connect { user: String, sender: mpsc::UnboundedSender<String> },
    Disconnect { user: String },
    Message { user: String, text: String },
}

pub struct ChatRoomActor {
    users: HashMap<String, mpsc::UnboundedSender<String>>,
}

impl Actor for ChatRoomActor {
    type Message = ChatMessage;

    fn handle(&mut self, msg: Self::Message, _ctx: &mut ActorContext<Self>) {
        match msg {
            ChatMessage::Connect { user, sender } => {
                println!("{} joined", user);
                self.users.insert(user.clone(), sender);
                self.broadcast(&format!("{} joined the room", user), &user);
            }
            ChatMessage::Disconnect { user } => {
                self.users.remove(&user);
                self.broadcast(&format!("{} left the room", user), "");
            }
            ChatMessage::Message { user, text } => {
                let msg = format!("{}: {}", user, text);
                self.broadcast(&msg, &user);
            }
        }
    }
}

impl ChatRoomActor {
    fn broadcast(&self, msg: &str, exclude: &str) {
        for (user, sender) in &self.users {
            if user != exclude {
                let _ = sender.send(msg.to_string());
            }
        }
    }
}
```

### 7.2 HTTP服务器（Reactor模式）

```rust
use tokio::net::TcpListener;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

pub async fn run_http_server(addr: &str) -> std::io::Result<()> {
    let listener = TcpListener::bind(addr).await?;
    println!("Server listening on {}", addr);

    loop {
        let (mut socket, _) = listener.accept().await?;

        tokio::spawn(async move {
            let mut buffer = [0u8; 1024];

            match socket.read(&mut buffer).await {
                Ok(n) if n > 0 => {
                    let request = String::from_utf8_lossy(&buffer[..n]);
                    println!("Received: {}", request);

                    let response = "HTTP/1.1 200 OK\r\nContent-Length: 13\r\n\r\nHello, World!";
                    socket.write_all(response.as_bytes()).await.unwrap();
                }
                _ => {}
            }
        });
    }
}
```

### 7.3 组合：Actor-based HTTP服务

```rust
pub enum HttpMessage {
    Request { path: String, reply: tokio::sync::oneshot::Sender<String> },
}

pub struct HttpHandlerActor;

impl Actor for HttpHandlerActor {
    type Message = HttpMessage;

    fn handle(&mut self, msg: Self::Message, _ctx: &mut ActorContext<Self>) {
        match msg {
            HttpMessage::Request { path, reply } => {
                let response = match path.as_str() {
                    "/" => "Home Page",
                    "/about" => "About Page",
                    _ => "404 Not Found",
                };
                let _ = reply.send(response.to_string());
            }
        }
    }
}

pub async fn run_actor_http_server(addr: &str, actor: ActorAddr) -> std::io::Result<()> {
    let listener = TcpListener::bind(addr).await?;

    loop {
        let (mut socket, _) = listener.accept().await?;

        tokio::spawn(async move {
            // Parse request (simplified)
            let path = "/".to_string();

            let (tx, rx) = tokio::sync::oneshot::channel();
            // Send to actor
            // actor.send(HttpMessage::Request { path, reply: tx });

            if let Ok(response) = rx.await {
                let http_response = format!(
                    "HTTP/1.1 200 OK\r\nContent-Length: {}\r\n\r\n{}",
                    response.len(),
                    response
                );
                socket.write_all(http_response.as_bytes()).await.unwrap();
            }
        });
    }
}
```

---

## 8. 结论

### 核心要点

1. **Actor模型**：高层抽象，消息传递，隔离性强
2. **Reactor模式**：低层机制，事件驱动，高效IO
3. **互补关系**：Actor可基于Reactor实现
4. **Rust优势**：所有权系统天然适配Actor模型

### 选择指南

| 场景                       | 推荐模式 | 理由            |
| :--- | :--- | :--- || 高并发IO（Web服务器）      | Reactor  | 单线程高效      |
| 业务逻辑复杂（游戏服务器） | Actor    | 状态隔离        |
| 分布式系统                 | Actor    | 透明的远程通信  |
| 实时流处理                 | 混合     | Actor + Reactor |

---

**文档版本**: 1.0
**最后更新**: 2025-10-02
**Rust版本**: 1.90+ (Edition 2024)
