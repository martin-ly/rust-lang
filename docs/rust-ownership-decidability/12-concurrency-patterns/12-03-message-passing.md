# Rust 消息传递模式

> **Rust版本**: 1.94
> **覆盖范围**: Channel、Actor模型、CSP理论、消息协议设计
> **权威参考**: The Go Programming Language (并发章节), Akka Documentation

---

## 目录

- [Rust 消息传递模式](#rust-消息传递模式)
  - [目录](#目录)
  - [1. 理论基础](#1-理论基础)
    - [1.1 CSP 理论](#11-csp-理论)
    - [1.2 Actor 模型](#12-actor-模型)
    - [1.3 消息传递 vs 共享状态](#13-消息传递-vs-共享状态)
  - [2. Channel 详解](#2-channel-详解)
    - [2.1 mpsc 通道](#21-mpsc-通道)
    - [2.2 mpmc 通道](#22-mpmc-通道)
    - [2.3 无界与有界通道](#23-无界与有界通道)
    - [2.4 Select 多路复用](#24-select-多路复用)
  - [3. Actor 模式实现](#3-actor-模式实现)
    - [3.1 Actor 基础](#31-actor-基础)
    - [3.2 消息协议设计](#32-消息协议设计)
      - [Rust 1.94 延迟初始化在 Actor 中的应用](#rust-194-延迟初始化在-actor-中的应用)

---

## 1. 理论基础

### 1.1 CSP 理论

CSP（Communicating Sequential Processes）由 Tony Hoare 于 1978 年提出，是一种用于描述并发系统交互的形式化语言。

**核心原则**:

```
"Do not communicate by sharing memory; instead, share memory by communicating."
```

**形式化定义**:

```text
P ::= STOP | SKIP | a → P | P □ Q | P ⊓ Q | P || Q | P \ A | P; Q

其中：
- STOP: 死锁进程
- SKIP: 成功终止
- a → P: 执行动作 a 后变为 P
- □: 外部选择
- ⊓: 内部选择
- ||: 并行组合
- \: 隐藏
- ;: 顺序组合
```

**Rust 中的 CSP 实现**:

```rust
/// CSP 风格的通道通信
use std::sync::mpsc;
use std::thread;

fn csp_example() {
    let (tx, rx) = mpsc::channel::<i32>();

    // 生产者进程
    let producer = thread::spawn(move || {
        for i in 0..10 {
            // 发送动作
            tx.send(i).unwrap();
        }
        // 通道关闭表示进程终止
    });

    // 消费者进程
    let consumer = thread::spawn(move || {
        while let Ok(value) = rx.recv() {
            // 接收动作
            println!("Received: {}", value);
        }
    });

    producer.join().unwrap();
    consumer.join().unwrap();
}
```

### 1.2 Actor 模型

Actor 模型由 Carl Hewitt 于 1973 年提出，每个 Actor 是一个独立的计算单元。

**Actor 公理**:

```text
1. 创建: Actor 可以创建更多 Actor
2. 发送: Actor 可以向其他 Actor 发送消息
3. 行为: Actor 可以指定对下一条消息的响应方式
```

**Actor 属性**:

| 属性 | 描述 | Rust 实现 |
|------|------|-----------|
| 封装 | 状态不直接暴露 | 私有字段 + 消息接口 |
| 并发 | 独立执行 | Tokio spawn |
| 异步 | 非阻塞通信 | Channel + await |
| 位置透明 | 本地/远程无差别 | 统一的 Handle |

### 1.3 消息传递 vs 共享状态

```rust
/// 共享状态方式
mod shared_state {
    use std::sync::{Arc, Mutex};
    use std::thread;

    pub fn increment_counter() {
        let counter = Arc::new(Mutex::new(0));
        let mut handles = vec![];

        for _ in 0..10 {
            let c = counter.clone();
            handles.push(thread::spawn(move || {
                let mut num = c.lock().unwrap();
                *num += 1;
            }));
        }

        for h in handles { h.join().unwrap(); }
        println!("Result: {}", *counter.lock().unwrap());
    }
}

/// 消息传递方式
mod message_passing {
    use std::sync::mpsc;
    use std::thread;

    pub fn increment_counter() {
        let (tx, rx) = mpsc::channel::<i32>();

        // 计数器 Actor
        let counter = thread::spawn(move || {
            let mut count = 0;
            while let Ok(delta) = rx.recv() {
                count += delta;
            }
            count
        });

        // 发送增量消息
        for _ in 0..10 {
            tx.send(1).unwrap();
        }
        drop(tx);

        let result = counter.join().unwrap();
        println!("Result: {}", result);
    }
}

/// 对比分析
///
/// 共享状态：
/// - 优点：低延迟，直接访问
/// - 缺点：需要锁，容易死锁
/// - 适用：高频、细粒度更新
///
/// 消息传递：
/// - 优点：天然安全，易于分布
/// - 缺点：拷贝开销，延迟较高
/// - 适用：粗粒度操作，分布式系统
```

---

## 2. Channel 详解

### 2.1 mpsc 通道

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

/// 多生产者单消费者模式
pub struct TaskScheduler<T> {
    sender: mpsc::Sender<T>,
    handle: thread::JoinHandle<()>,
}

impl<T: Send + 'static> TaskScheduler<T> {
    pub fn new<F>(mut worker: F) -> Self
    where
        F: FnMut(T) + Send + 'static,
    {
        let (sender, receiver) = mpsc::channel::<T>();

        let handle = thread::spawn(move || {
            while let Ok(task) = receiver.recv() {
                worker(task);
            }
        });

        Self { sender, handle }
    }

    pub fn schedule(&self, task: T) -> Result<(), mpsc::SendError<T>> {
        self.sender.send(task)
    }

    pub fn shutdown(self) {
        drop(self.sender);
        self.handle.join().unwrap();
    }
}

/// 带有优先级的任务调度
use std::collections::BinaryHeap;
use std::cmp::Ordering;

#[derive(Debug)]
pub struct PriorityTask<T> {
    priority: u8,
    task: T,
}

impl<T> PartialEq for PriorityTask<T> {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl<T> Eq for PriorityTask<T> {}

impl<T> PartialOrd for PriorityTask<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for PriorityTask<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        other.priority.cmp(&self.priority) // 反向比较：高优先级在前
    }
}

pub struct PriorityScheduler<T: Send + 'static> {
    sender: mpsc::Sender<PriorityTask<T>>,
}

impl<T: Send + 'static> PriorityScheduler<T> {
    pub fn new<F>(mut worker: F) -> Self
    where
        F: FnMut(T) + Send + 'static,
    {
        let (sender, receiver) = mpsc::channel::<PriorityTask<T>>();

        thread::spawn(move || {
            let mut heap = BinaryHeap::new();

            loop {
                // 先处理队列中所有消息
                while let Ok(task) = receiver.try_recv() {
                    heap.push(task);
                }

                if let Some(task) = heap.pop() {
                    worker(task.task);
                } else {
                    // 阻塞等待新消息
                    match receiver.recv() {
                        Ok(task) => heap.push(task),
                        Err(_) => break,
                    }
                }
            }
        });

        Self { sender }
    }

    pub fn schedule(&self, priority: u8, task: T) -> Result<(), mpsc::SendError<PriorityTask<T>>> {
        self.sender.send(PriorityTask { priority, task })
    }
}

/// 带有超时的工作窃取
pub struct WorkStealingQueue<T> {
    local: mpsc::Sender<T>,
    stealers: Vec<mpsc::Sender<T>>,
}

impl<T: Clone + Send + 'static> WorkStealingQueue<T> {
    pub fn new_with_stealers(worker_count: usize) -> Vec<Self> {
        let mut senders = vec![];
        let mut receivers = vec![];

        for _ in 0..worker_count {
            let (tx, rx) = mpsc::channel::<T>();
            senders.push(tx);
            receivers.push(rx);
        }

        // 为每个 worker 创建带有窃取能力的队列
        senders.into_iter().enumerate().map(|(i, local)| {
            let stealers: Vec<_> = (0..worker_count)
                .filter(|&j| j != i)
                .map(|j| senders[j].clone())
                .collect();

            // 启动 worker
            let rx = receivers[i].clone();
            let all_receivers: Vec<_> = receivers.iter().map(|r| r.clone()).collect();

            thread::spawn(move || {
                loop {
                    // 首先尝试本地队列
                    match rx.recv_timeout(Duration::from_millis(10)) {
                        Ok(task) => {
                            // 处理任务
                        }
                        Err(mpsc::RecvTimeoutError::Timeout) => {
                            // 尝试从其他队列窃取
                            for (j, other_rx) in all_receivers.iter().enumerate() {
                                if j != i {
                                    if let Ok(task) = other_rx.try_recv() {
                                        // 窃取成功
                                        break;
                                    }
                                }
                            }
                        }
                        Err(mpsc::RecvTimeoutError::Disconnected) => break,
                    }
                }
            });

            Self { local, stealers }
        }).collect()
    }
}
```

### 2.2 mpmc 通道

```rust
use crossbeam::channel::{self, Sender, Receiver, Select};
use std::thread;

/// 多生产者多消费者通道
pub struct MpmcChannel<T> {
    senders: Vec<Sender<T>>,
    receivers: Vec<Receiver<T>>,
}

impl<T: Send + 'static> MpmcChannel<T> {
    pub fn bounded(capacity: usize, producers: usize, consumers: usize) -> Self {
        let (tx, rx) = channel::bounded::<T>(capacity);

        let senders: Vec<_> = (0..producers)
            .map(|_| tx.clone())
            .collect();

        let receivers: Vec<_> = (0..consumers)
            .map(|_| rx.clone())
            .collect();

        Self { senders, receivers }
    }

    pub fn send(&self, sender_id: usize, msg: T) -> Result<(), channel::SendError<T>> {
        self.senders[sender_id % self.senders.len()].send(msg)
    }

    pub fn recv(&self, receiver_id: usize) -> Result<T, channel::RecvError> {
        self.receivers[receiver_id % self.receivers.len()].recv()
    }
}

/// 负载均衡的消费者组
pub struct ConsumerGroup<T> {
    receivers: Vec<Receiver<T>>,
    round_robin: std::sync::atomic::AtomicUsize,
}

impl<T> ConsumerGroup<T> {
    pub fn new(receivers: Vec<Receiver<T>>) -> Self {
        Self {
            receivers,
            round_robin: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    /// 轮询选择接收者
    pub fn recv_round_robin(&self) -> Result<T, channel::RecvError> {
        let start = self.round_robin.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

        for i in 0..self.receivers.len() {
            let idx = (start + i) % self.receivers.len();
            match self.receivers[idx].try_recv() {
                Ok(msg) => return Ok(msg),
                Err(_) => continue,
            }
        }

        // 所有队列都空，阻塞等待
        let mut select = Select::new();
        for rx in &self.receivers {
            select.recv(rx);
        }

        let oper = select.select();
        let index = oper.index();
        oper.recv(&self.receivers[index])
    }
}
```

### 2.3 无界与有界通道

```rust
use std::sync::mpsc;
use crossbeam::channel;

/// 有界通道 - 背压控制
pub struct BoundedChannel<T> {
    sender: channel::Sender<T>,
    capacity: usize,
}

impl<T> BoundedChannel<T> {
    pub fn new(capacity: usize) -> (Self, channel::Receiver<T>) {
        let (tx, rx) = channel::bounded(capacity);
        (Self { sender: tx, capacity }, rx)
    }

    /// 非阻塞发送，失败时返回错误
    pub fn try_send(&self, msg: T) -> Result<(), channel::TrySendError<T>> {
        self.sender.try_send(msg)
    }

    /// 超时发送
    pub fn send_timeout(
        &self,
        msg: T,
        timeout: std::time::Duration,
    ) -> Result<(), channel::RecvTimeoutError> {
        // 使用 crossbeam 的 send_deadline
        let deadline = std::time::Instant::now() + timeout;
        self.sender.send_deadline(msg, deadline)
    }

    /// 获取当前队列长度
    pub fn len(&self) -> usize {
        self.sender.len()
    }

    /// 检查是否已满
    pub fn is_full(&self) -> bool {
        self.len() >= self.capacity
    }
}

/// 背压策略枚举
#[derive(Debug, Clone, Copy)]
pub enum BackpressureStrategy {
    /// 阻塞等待
    Block,
    /// 丢弃最旧消息
    DropOldest,
    /// 丢弃最新消息
    DropNewest,
    /// 使用指数退避重试
    ExponentialBackoff,
}

pub struct AdaptiveChannel<T> {
    sender: channel::Sender<T>,
    strategy: BackpressureStrategy,
}

impl<T> AdaptiveChannel<T> {
    pub fn with_strategy(capacity: usize, strategy: BackpressureStrategy) -> (Self, channel::Receiver<T>) {
        let (tx, rx) = channel::bounded(capacity);
        (Self { sender: tx, strategy }, rx)
    }

    pub fn send(&self, msg: T) -> Result<(), SendError<T>> {
        match self.strategy {
            BackpressureStrategy::Block => {
                self.sender.send(msg).map_err(|e| SendError(e.into_inner()))
            }
            BackpressureStrategy::DropOldest => {
                while self.sender.is_full() {
                    let _ = self.sender.try_recv();
                }
                self.sender.send(msg).map_err(|e| SendError(e.into_inner()))
            }
            BackpressureStrategy::DropNewest => {
                match self.sender.try_send(msg) {
                    Ok(()) => Ok(()),
                    Err(channel::TrySendError::Full(m)) => Err(SendError(m)),
                    Err(channel::TrySendError::Disconnected(m)) => Err(SendError(m)),
                }
            }
            BackpressureStrategy::ExponentialBackoff => {
                let mut backoff = 1u64;
                loop {
                    match self.sender.try_send(msg) {
                        Ok(()) => return Ok(()),
                        Err(channel::TrySendError::Disconnected(m)) => return Err(SendError(m)),
                        Err(channel::TrySendError::Full(m)) => {
                            std::thread::sleep(std::time::Duration::from_millis(backoff));
                            backoff = (backoff * 2).min(1000);
                        }
                    }
                }
            }
        }
    }
}

pub struct SendError<T>(pub T);
```

### 2.4 Select 多路复用

```rust
use crossbeam::channel::{self, Select};
use std::time::Duration;

/// Select 多路复用模式
pub fn select_example() {
    let (tx1, rx1) = channel::unbounded::<i32>();
    let (tx2, rx2) = channel::unbounded::<String>();

    // 生产者
    std::thread::spawn(move || {
        tx1.send(42).unwrap();
    });

    std::thread::spawn(move || {
        tx2.send("hello".to_string()).unwrap();
    });

    // 使用 Select 多路复用
    let mut sel = Select::new();
    let oper1 = sel.recv(&rx1);
    let oper2 = sel.recv(&rx2);

    match sel.select() {
        oper if oper.index() == oper1 => {
            let val = oper.recv(&rx1).unwrap();
            println!("Received i32: {}", val);
        }
        oper if oper.index() == oper2 => {
            let val = oper.recv(&rx2).unwrap();
            println!("Received String: {}", val);
        }
        _ => unreachable!(),
    }
}

/// 超时 Select
pub fn select_with_timeout() {
    let (tx, rx) = channel::bounded::<i32>(1);

    let result = channel::recv_timeout(&rx, Duration::from_secs(1));

    match result {
        Ok(val) => println!("Received: {}", val),
        Err(channel::RecvTimeoutError::Timeout) => println!("Timeout"),
        Err(channel::RecvTimeoutError::Disconnected) => println!("Disconnected"),
    }
}

/// 优先级 Select
pub struct PrioritySelect<T> {
    high_priority: channel::Receiver<T>,
    normal_priority: channel::Receiver<T>,
    low_priority: channel::Receiver<T>,
}

impl<T> PrioritySelect<T> {
    pub fn recv(&self) -> Result<T, channel::RecvError> {
        // 首先尝试高优先级（非阻塞）
        if let Ok(msg) = self.high_priority.try_recv() {
            return Ok(msg);
        }

        // 然后尝试普通优先级
        if let Ok(msg) = self.normal_priority.try_recv() {
            return Ok(msg);
        }

        // 最后选择所有通道
        let mut sel = Select::new();
        sel.recv(&self.high_priority);
        sel.recv(&self.normal_priority);
        sel.recv(&self.low_priority);

        let oper = sel.select();
        let index = oper.index();

        if index == 0 {
            oper.recv(&self.high_priority)
        } else if index == 1 {
            oper.recv(&self.normal_priority)
        } else {
            oper.recv(&self.low_priority)
        }
    }
}
```

---

## 3. Actor 模式实现

### 3.1 Actor 基础

```rust
use tokio::sync::{mpsc, oneshot};
use std::sync::Arc;

/// Actor 消息 trait
pub trait Message: Send + 'static {
    type Result: Send + 'static;
}

/// Actor 句柄
pub struct ActorHandle<A: Actor> {
    sender: mpsc::UnboundedSender<A::Msg>,
}

impl<A: Actor> Clone for ActorHandle<A> {
    fn clone(&self) -> Self {
        Self { sender: self.sender.clone() }
    }
}

impl<A: Actor> ActorHandle<A> {
    pub async fn send<M>(&self, msg: M) -> Result<M::Result, ActorError>
    where
        M: Message,
        A: Handler<M>,
    {
        let (tx, rx) = oneshot::channel();
        let envelope = Envelope::new(msg, tx);
        self.sender.send(envelope).map_err(|_| ActorError::ActorStopped)?;
        rx.await.map_err(|_| ActorError::ActorStopped)
    }

    pub fn try_send<M>(&self, msg: M) -> Result<(), ActorError>
    where
        M: Message,
        A: Handler<M>,
    {
        let (tx, _rx) = oneshot::channel();
        let envelope = Envelope::new(msg, tx);
        self.sender.send(envelope).map_err(|_| ActorError::ActorStopped)
    }
}

/// Actor trait
#[async_trait::async_trait]
pub trait Actor: Sized + Send + 'static {
    type Msg: Send + 'static;

    async fn handle_message(&mut self, msg: Self::Msg);

    async fn started(&mut self) {}
    async fn stopping(&mut self) {}
    async fn stopped(&mut self) {}
}

/// Handler trait 用于特定消息类型
#[async_trait::async_trait]
pub trait Handler<M: Message>: Actor {
    async fn handle(&mut self, msg: M, ctx: &mut Context<Self>) -> M::Result;
}

/// Actor 上下文
pub struct Context<A: Actor> {
    handle: ActorHandle<A>,
}

/// 信封类型用于类型擦除
pub struct Envelope<A: Actor> {
    handler: Box<dyn FnOnce(&mut A, &mut Context<A>) + Send>,
}

impl<A: Actor> Envelope<A> {
    pub fn new<M>(msg: M, respond_to: oneshot::Sender<M::Result>) -> Self
    where
        M: Message,
        A: Handler<M>,
    {
        Self {
            handler: Box::new(move |actor, ctx| {
                // 这里需要运行时支持来处理异步 handler
                // 简化示例
            }),
        }
    }
}

#[derive(Debug)]
pub enum ActorError {
    ActorStopped,
    Timeout,
    MailboxFull,
}

/// 简单 Actor 实现示例：计数器
pub struct Counter {
    count: i32,
}

impl Counter {
    pub fn new() -> Self {
        Self { count: 0 }
    }
}

#[async_trait::async_trait]
impl Actor for Counter {
    type Msg = CounterMsg;

    async fn handle_message(&mut self, msg: Self::Msg) {
        match msg {
            CounterMsg::Increment => self.count += 1,
            CounterMsg::Decrement => self.count -= 1,
            CounterMsg::Get { respond_to } => {
                let _ = respond_to.send(self.count);
            }
        }
    }
}

pub enum CounterMsg {
    Increment,
    Decrement,
    Get { respond_to: oneshot::Sender<i32> },
}

/// 启动 Actor
pub fn start<A: Actor>(actor: A) -> ActorHandle<A> {
    let (tx, mut rx) = mpsc::unbounded_channel::<A::Msg>();
    let handle = ActorHandle { sender: tx };

    tokio::spawn(async move {
        let mut actor = actor;
        actor.started().await;

        while let Some(msg) = rx.recv().await {
            actor.handle_message(msg).await;
        }

        actor.stopping().await;
        actor.stopped().await;
    });

    handle
}
```

### 3.2 消息协议设计

#### Rust 1.94 延迟初始化在 Actor 中的应用

```rust
use std::sync::LazyLock;
use std::cell::LazyCell;
use tokio::sync::{mpsc, oneshot};

/// 全局消息路由表 - 延迟初始化
static MESSAGE_ROUTER: LazyLock<MessageRouter> = LazyLock::new(|| {
    MessageRouter::new()
});

pub struct MessageRouter {
    routes: std::collections::HashMap<String, mpsc::Sender<Vec<u8>>>,
}

impl MessageRouter {
    fn new() -> Self {
        Self {
            routes: std::collections::HashMap::new(),
        }
    }

    pub fn register(&mut self, topic: String, sender: mpsc::Sender<Vec<u8>>) {
        self.routes.insert(topic, sender);
    }

    pub fn get_sender(&self, topic: &str) -> Option<&mpsc::Sender<Vec<u8>>> {
        self.routes.get(topic)
    }
}

/// 获取全局路由器（Rust 1.94 API）
pub fn get_router() -> &'static MessageRouter {
    MESSAGE_ROUTER.get()
}

/// 带延迟初始化的 Actor
pub struct LazyActor {
    state: LazyCell<ActorState>,
    inbox: mpsc::Receiver<Message>,
}

struct ActorState {
    message_count: usize,
    last_message: Option<String>,
}

impl LazyActor {
    pub fn new(inbox: mpsc::Receiver<Message>) -> Self {
        Self {
            state: LazyCell::new(|| ActorState {
                message_count: 0,
                last_message: None,
            }),
            inbox,
        }
    }

    pub fn handle_message(&mut self, msg: Message) {
        // Rust 1.94: 使用 force_mut() 确保初始化并获取可变访问
        let state = self.state.force_mut();
        state.message_count += 1;
        state.last_message = Some(format!("{:?}", msg));

        match msg {
            Message::Process(data) => {
                println!("Processing {} bytes (message #{})", data.len(), state.message_count);
            }
            Message::Shutdown => {
                println!("Actor shutting down after {} messages", state.message_count);
            }
        }
    }
}

#[derive(Debug)]
pub enum Message {
    Process(Vec<u8>),
    Shutdown,
}
```

```rust
/// CQRS 风格的消息协议
pub mod protocol {
    use serde::{Serialize, Deserialize};

    /// 命令 - 改变状态
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub enum Command {
        CreateUser { id: String, name: String, email: String },
        UpdateUser { id: String, name: Option<String>, email: Option<String> },
        DeleteUser { id: String },
    }

    /// 事件 - 状态已改变
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub enum Event {
        UserCreated { id: String, name: String, email: String, timestamp: u64 },
        UserUpdated { id: String, changes: Vec<String>, timestamp: u64 },
        UserDeleted { id: String, timestamp: u64 },
    }

    /// 查询 - 读取状态
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub enum Query {
        GetUser { id: String },
        ListUsers { page: usize, per_page: usize },
        SearchUsers { query: String, limit: usize },
    }

    /// 查询结果
    #[derive(Debug, Clone, Serialize, Deserialize)]
pub enum QueryResult {
        User(Option<User>),
        UserList { users: Vec<User>, total: usize },
        Error { code: String, message: String },
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct User {
        pub id: String,
        pub name: String,
        pub email: String,
        pub created_at: u64,
        pub updated_at: u64,
    }
}

/// Actor 消息枚举
use protocol::*;

pub enum UserActorMessage {
    Command(Command, tokio::sync::oneshot::Sender<Result<(), CommandError>>),
    Query(Query, tokio::sync::oneshot::Sender<QueryResult>),
    Subscribe(tokio::sync::mpsc::Sender<Event>), // 事件订阅
}

#[derive(Debug)]
pub enum CommandError {
    UserAlreadyExists,
    UserNotFound,
    InvalidInput(String),
    InternalError(String),
}

/// 实现 Actor
pub struct UserActor {
    users: std::collections::HashMap<String, User>,
    subscribers: Vec<tokio::sync::mpsc::Sender<Event>>,
}

impl UserActor {
    async fn handle_command(&mut self, cmd: Command) -> Result<(), CommandError> {
        match cmd {
            Command::CreateUser { id, name, email } => {
                if self.users.contains_key(&id) {
                    return Err(CommandError::UserAlreadyExists);
                }

                let user = User {
                    id: id.clone(),
                    name,
                    email,
                    created_at: now(),
                    updated_at: now(),
                };

                self.users.insert(id.clone(), user);

                self.broadcast(Event::UserCreated {
                    id,
                    name: name.clone(),
                    email: email.clone(),
                    timestamp: now(),
                }).await;

                Ok(())
            }
            Command::UpdateUser { id, name, email } => {
                let user = self.users.get_mut(&id)
                    .ok_or(CommandError::UserNotFound)?;

                let mut changes = vec![];

                if let Some(new_name) = name {
                    if new_name != user.name {
                        changes.push(format!("name: {} -> {}", user.name, new_name));
                        user.name = new_name;
                    }
                }

                if let Some(new_email) = email {
                    if new_email != user.email {
                        changes.push(format!("email: {} -> {}", user.email, new_email));
                        user.email = new_email;
                    }
                }

                user.updated_at = now();

                self.broadcast(Event::UserUpdated {
                    id,
                    changes,
                    timestamp: now(),
                }).await;

                Ok(())
            }
            Command::DeleteUser { id } => {
                self.users.remove(&id)
                    .ok_or(CommandError::UserNotFound)?;

                self.broadcast(Event::UserDeleted {
                    id,
                    timestamp: now(),
                }).await;

                Ok(())
            }
        }
    }

    async fn handle_query(&self, query: Query) -> QueryResult {
        match query {
            Query::GetUser { id } => {
                QueryResult::User(self.users.get(&id).cloned())
            }
            Query::ListUsers { page, per_page } => {
                let users: Vec<_> = self.users.values()
                    .skip(page * per_page)
                    .take(per_page)
                    .cloned()
                    .collect();
                QueryResult::UserList { users, total: self.users.len() }
            }
            Query::SearchUsers { query, limit } => {
                let users: Vec<_> = self.users.values()
                    .filter(|u| u.name.contains(&query) || u.email.contains(&query))
                    .take(limit)
                    .cloned()
                    .collect();
                QueryResult::UserList { users, total: users.len() }
            }
        }
    }

    async fn broadcast(&self, event: Event) {
        for subscriber in &self.subscribers {
            let _ = subscriber.send(event.clone()).await;
        }
    }
}

fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs()
}
```

（继续创建其他文件...）
