# Actor/Reactor模式与CSP语义模型：异步算法调度机制

**版本**: 1.0.0  
**Rust版本**: 1.90+  
**Edition**: 2024  
**最后更新**: 2025-10-02

---

## 目录

- [Actor/Reactor模式与CSP语义模型：异步算法调度机制](#actorreactor模式与csp语义模型异步算法调度机制)
  - [目录](#目录)
  - [1. Actor模型](#1-actor模型)
    - [1.1 理论基础](#11-理论基础)
      - [定义1.1（Actor）](#定义11actor)
      - [Actor三大公理](#actor三大公理)
    - [1.2 操作语义](#12-操作语义)
    - [1.3 Rust实现：算法Actor系统](#13-rust实现算法actor系统)
  - [2. Reactor模式](#2-reactor模式)
    - [2.1 理论基础](#21-理论基础)
      - [定义2.1（Reactor）](#定义21reactor)
    - [2.2 执行流程](#22-执行流程)
    - [2.3 Rust实现：算法Reactor](#23-rust实现算法reactor)
  - [3. CSP通信顺序进程](#3-csp通信顺序进程)
    - [3.1 理论基础](#31-理论基础)
      - [定义3.1（CSP进程）](#定义31csp进程)
      - [Channel通信](#channel通信)
    - [3.2 Rust中的CSP实现](#32-rust中的csp实现)
  - [4. Golang CSP vs Rust Async对比](#4-golang-csp-vs-rust-async对比)
    - [4.1 语法对比](#41-语法对比)
      - [Golang: Goroutine + Channel](#golang-goroutine--channel)
      - [Rust: Async/Await](#rust-asyncawait)
    - [4.2 语义对比表](#42-语义对比表)
    - [4.3 形式化等价性](#43-形式化等价性)
      - [定理4.1（通信等价）](#定理41通信等价)
  - [5. 调度机制原理](#5-调度机制原理)
    - [5.1 Actor调度](#51-actor调度)
    - [5.2 Reactor调度](#52-reactor调度)
    - [5.3 CSP调度](#53-csp调度)
  - [6. 算法应用示例](#6-算法应用示例)
    - [6.1 并行归并排序（Actor模式）](#61-并行归并排序actor模式)
    - [6.2 图遍历（Reactor模式）](#62-图遍历reactor模式)
    - [6.3 MapReduce（CSP风格）](#63-mapreducecsp风格)
  - [7. 形式化验证](#7-形式化验证)
    - [7.1 Actor系统的性质](#71-actor系统的性质)
      - [性质7.1（消息传递保序性）](#性质71消息传递保序性)
      - [性质7.2（Actor隔离性）](#性质72actor隔离性)
    - [7.2 Reactor系统的性质](#72-reactor系统的性质)
      - [性质7.3（事件处理的完整性）](#性质73事件处理的完整性)
    - [7.3 CSP系统的性质](#73-csp系统的性质)
      - [性质7.4（死锁自由）](#性质74死锁自由)
  - [8. 总结](#8-总结)
    - [对比表](#对比表)
    - [选择指南](#选择指南)

---

## 1. Actor模型

### 1.1 理论基础

#### 定义1.1（Actor）

Actor是一个独立的计算实体，定义为五元组：

```text
Actor = (S, M, B, s₀, addr)

其中:
- S: 状态空间
- M: 消息类型集合
- B: S × M → S × Actions: 行为函数
- s₀ ∈ S: 初始状态
- addr: 唯一地址（邮箱）
```

#### Actor三大公理

1. **消息发送**: Actor可以发送消息给其他Actor
2. **Actor创建**: Actor可以创建新的Actor
3. **行为改变**: Actor可以决定如何响应下一条消息

### 1.2 操作语义

```text
消息传递规则:

α₁ @ s₁ ─send(addr_α₂, m)→ α₁ @ s₁'
            ↓
        mailbox(α₂) ← append(m)
            ↓
α₂ @ s₂ ─receive(m)→ α₂ @ s₂'
            ↓
        B(s₂, m) = (s₂', actions)
```

### 1.3 Rust实现：算法Actor系统

```rust
//! Actor模型用于算法的异步执行和调度

use tokio::sync::mpsc;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

/// Actor消息trait
pub trait ActorMessage: Send + 'static {}

/// Actor trait：定义Actor的行为
pub trait Actor: Send + 'static {
    type Message: ActorMessage;
    type State: Send;
    
    /// 处理消息，返回新状态和动作
    fn handle(
        &mut self,
        msg: Self::Message,
        state: Self::State,
        ctx: &mut ActorContext<Self>,
    ) -> Self::State;
    
    /// 初始状态
    fn initial_state(&self) -> Self::State;
}

/// Actor上下文：提供Actor运行时能力
pub struct ActorContext<A: Actor> {
    addr: ActorAddr,
    system: Arc<ActorSystem>,
    _phantom: std::marker::PhantomData<A>,
}

impl<A: Actor> ActorContext<A> {
    /// 发送消息到指定Actor（非阻塞）
    pub fn send<M: ActorMessage>(&self, addr: ActorAddr, msg: M) {
        self.system.send_message(addr, Box::new(msg));
    }
    
    /// 创建新Actor
    pub fn spawn<A2: Actor>(&self, actor: A2) -> ActorAddr {
        self.system.spawn_actor(actor)
    }
    
    /// 停止当前Actor
    pub fn stop(&self) {
        self.system.stop_actor(self.addr);
    }
}

/// Actor地址
pub type ActorAddr = u64;

/// Actor系统：管理所有Actor
pub struct ActorSystem {
    actors: Arc<Mutex<HashMap<ActorAddr, mpsc::UnboundedSender<Box<dyn ActorMessage>>>>>,
    next_id: Arc<std::sync::atomic::AtomicU64>,
}

impl ActorSystem {
    pub fn new() -> Self {
        Self {
            actors: Arc::new(Mutex::new(HashMap::new())),
            next_id: Arc::new(std::sync::atomic::AtomicU64::new(1)),
        }
    }
    
    /// 启动Actor
    pub fn spawn_actor<A: Actor>(&self, mut actor: A) -> ActorAddr {
        let addr = self.next_id.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let (tx, mut rx) = mpsc::unbounded_channel();
        
        let system = Arc::new(self.clone());
        let mut state = actor.initial_state();
        
        tokio::spawn(async move {
            let mut ctx = ActorContext {
                addr,
                system,
                _phantom: std::marker::PhantomData,
            };
            
            while let Some(msg) = rx.recv().await {
                // 安全的类型转换（实际需要Any trait）
                if let Ok(typed_msg) = unsafe {
                    std::mem::transmute::<Box<dyn ActorMessage>, Box<A::Message>>(msg)
                } {
                    state = actor.handle(*typed_msg, state, &mut ctx);
                }
            }
        });
        
        // 注册Actor
        tokio::runtime::Handle::current().block_on(async {
            self.actors.lock().await.insert(addr, tx);
        });
        
        addr
    }
    
    /// 发送消息
    pub fn send_message(&self, addr: ActorAddr, msg: Box<dyn ActorMessage>) {
        let actors = self.actors.clone();
        tokio::spawn(async move {
            if let Some(tx) = actors.lock().await.get(&addr) {
                let _ = tx.send(msg);
            }
        });
    }
    
    /// 停止Actor
    pub fn stop_actor(&self, addr: ActorAddr) {
        let actors = self.actors.clone();
        tokio::spawn(async move {
            actors.lock().await.remove(&addr);
        });
    }
}

impl Clone for ActorSystem {
    fn clone(&self) -> Self {
        Self {
            actors: self.actors.clone(),
            next_id: self.next_id.clone(),
        }
    }
}

/// 示例：算法执行Actor
pub struct AlgorithmActor;

#[derive(Debug)]
pub enum AlgorithmMessage {
    Sort(Vec<i32>),
    Search(Vec<i32>, i32),
    Result(Vec<i32>),
}

impl ActorMessage for AlgorithmMessage {}

pub struct AlgorithmState {
    pub results: Vec<Vec<i32>>,
}

impl Actor for AlgorithmActor {
    type Message = AlgorithmMessage;
    type State = AlgorithmState;
    
    fn handle(
        &mut self,
        msg: Self::Message,
        mut state: Self::State,
        _ctx: &mut ActorContext<Self>,
    ) -> Self::State {
        match msg {
            AlgorithmMessage::Sort(mut data) => {
                // 执行排序算法
                data.sort();
                println!("排序完成: {:?}", data);
                state.results.push(data);
            }
            AlgorithmMessage::Search(data, target) => {
                // 执行搜索算法
                if let Ok(idx) = data.binary_search(&target) {
                    println!("找到 {} 在位置 {}", target, idx);
                }
            }
            AlgorithmMessage::Result(result) => {
                println!("收到结果: {:?}", result);
            }
        }
        state
    }
    
    fn initial_state(&self) -> Self::State {
        AlgorithmState {
            results: Vec::new(),
        }
    }
}
```

---

## 2. Reactor模式

### 2.1 理论基础

#### 定义2.1（Reactor）

Reactor是事件驱动的IO多路复用模式：

```text
Reactor = (EventLoop, Demux, Handlers)

其中:
- EventLoop: 事件循环
- Demux: IO多路复用器（epoll/kqueue/IOCP）
- Handlers: 事件处理器映射
```

### 2.2 执行流程

```text
┌─────────────────────────────────┐
│      Reactor Event Loop         │
└─────────────────────────────────┘
            ↓
    ┌───────────────┐
    │  Wait Events  │ ← epoll_wait/kqueue
    └───────────────┘
            ↓
    ┌───────────────┐
    │ Event Ready?  │
    └───────────────┘
      ↙           ↘
   Yes             No → Back to Wait
    ↓
┌───────────────┐
│ Dispatch to   │
│   Handler     │
└───────────────┘
    ↓
┌───────────────┐
│ Execute Task  │
└───────────────┘
    ↓
Back to Event Loop
```

### 2.3 Rust实现：算法Reactor

```rust
//! Reactor模式用于算法的异步IO调度

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// Task ID
type TaskId = u64;

/// Reactor: 事件驱动的任务调度器
pub struct Reactor {
    /// 就绪任务队列
    ready_queue: Arc<Mutex<Vec<TaskId>>>,
    /// 任务映射
    tasks: Arc<Mutex<HashMap<TaskId, Pin<Box<dyn Future<Output = ()> + Send>>>>>,
    /// Waker映射
    wakers: Arc<Mutex<HashMap<TaskId, Waker>>>,
    /// 下一个任务ID
    next_id: Arc<Mutex<u64>>,
}

impl Reactor {
    pub fn new() -> Self {
        Self {
            ready_queue: Arc::new(Mutex::new(Vec::new())),
            tasks: Arc::new(Mutex::new(HashMap::new())),
            wakers: Arc::new(Mutex::new(HashMap::new())),
            next_id: Arc::new(Mutex::new(0)),
        }
    }
    
    /// 提交任务
    pub fn spawn<F>(&self, future: F) -> TaskId
    where
        F: Future<Output = ()> + Send + 'static,
    {
        let id = {
            let mut next_id = self.next_id.lock().unwrap();
            let id = *next_id;
            *next_id += 1;
            id
        };
        
        self.tasks.lock().unwrap().insert(id, Box::pin(future));
        self.ready_queue.lock().unwrap().push(id);
        
        id
    }
    
    /// 运行Reactor
    pub fn run(&self) {
        loop {
            // 1. 从就绪队列获取任务
            let task_id = {
                let mut queue = self.ready_queue.lock().unwrap();
                if queue.is_empty() {
                    break;
                }
                queue.remove(0)
            };
            
            // 2. 获取任务
            let mut task_opt = self.tasks.lock().unwrap().remove(&task_id);
            
            if let Some(mut task) = task_opt {
                // 3. 创建Waker
                let waker = self.create_waker(task_id);
                let mut context = Context::from_waker(&waker);
                
                // 4. Poll任务
                match task.as_mut().poll(&mut context) {
                    Poll::Ready(()) => {
                        // 任务完成，从wakers中移除
                        self.wakers.lock().unwrap().remove(&task_id);
                    }
                    Poll::Pending => {
                        // 任务未完成，重新放回
                        self.tasks.lock().unwrap().insert(task_id, task);
                        self.wakers.lock().unwrap().insert(task_id, waker);
                    }
                }
            }
        }
    }
    
    /// 创建Waker
    fn create_waker(&self, task_id: TaskId) -> Waker {
        let ready_queue = self.ready_queue.clone();
        
        // 简化版Waker（实际需要使用RawWaker）
        waker_fn::waker_fn(move || {
            ready_queue.lock().unwrap().push(task_id);
        })
    }
}

/// 算法任务包装
pub struct AlgorithmTask<F, T> {
    future: F,
    _phantom: std::marker::PhantomData<T>,
}

impl<F, T> AlgorithmTask<F, T>
where
    F: Future<Output = T>,
{
    pub fn new(future: F) -> Self {
        Self {
            future,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<F, T> Future for AlgorithmTask<F, T>
where
    F: Future<Output = T>,
{
    type Output = T;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // 安全性：future字段不移动
        unsafe {
            let this = self.get_unchecked_mut();
            Pin::new_unchecked(&mut this.future).poll(cx)
        }
    }
}

// waker_fn依赖（简化实现）
mod waker_fn {
    use std::task::{RawWaker, RawWakerVTable, Waker};
    
    pub fn waker_fn<F: Fn() + Send + Sync + 'static>(f: F) -> Waker {
        let raw = Box::into_raw(Box::new(f));
        unsafe { Waker::from_raw(new_raw_waker(raw)) }
    }
    
    fn new_raw_waker<F>(ptr: *const F) -> RawWaker
    where
        F: Fn() + Send + Sync + 'static,
    {
        RawWaker::new(ptr as *const (), &VTABLE)
    }
    
    const VTABLE: RawWakerVTable = RawWakerVTable::new(
        |ptr| new_raw_waker(ptr as *const fn()),
        |ptr| unsafe { (*(ptr as *const fn()))() },
        |ptr| unsafe { (*(ptr as *const fn()))() },
        |ptr| unsafe { drop(Box::from_raw(ptr as *mut fn())) },
    );
}
```

---

## 3. CSP通信顺序进程

### 3.1 理论基础

#### 定义3.1（CSP进程）

```text
P ::= STOP              // 死锁
    | SKIP              // 成功终止
    | a → P             // 事件前缀
    | P □ Q             // 外部选择
    | P ⊓ Q             // 内部选择
    | P ||| Q           // 交错并行
    | P || Q            // 同步并行
    | P \ A             // 隐藏
```

#### Channel通信

```text
发送: c!v → P
接收: c?x → Q

同步语义:
(c!v → P) || (c?x → Q) → τ → (P || Q[v/x])
```

### 3.2 Rust中的CSP实现

```rust
//! CSP风格的channel通信

use std::sync::mpsc;
use std::thread;

/// CSP进程trait
pub trait CspProcess {
    type Input;
    type Output;
    
    /// 执行进程
    fn run(&self, input: Self::Input) -> Self::Output;
}

/// Channel包装
pub struct CspChannel<T> {
    sender: mpsc::Sender<T>,
    receiver: mpsc::Receiver<T>,
}

impl<T> CspChannel<T> {
    pub fn new() -> Self {
        let (sender, receiver) = mpsc::channel();
        Self { sender, receiver }
    }
    
    /// 分离发送和接收端
    pub fn split(self) -> (CspSender<T>, CspReceiver<T>) {
        (
            CspSender { sender: self.sender },
            CspReceiver { receiver: self.receiver },
        )
    }
}

pub struct CspSender<T> {
    sender: mpsc::Sender<T>,
}

impl<T> CspSender<T> {
    /// 发送（阻塞）
    pub fn send(&self, value: T) -> Result<(), mpsc::SendError<T>> {
        self.sender.send(value)
    }
}

pub struct CspReceiver<T> {
    receiver: mpsc::Receiver<T>,
}

impl<T> CspReceiver<T> {
    /// 接收（阻塞）
    pub fn recv(&self) -> Result<T, mpsc::RecvError> {
        self.receiver.recv()
    }
}

/// 算法pipeline：CSP风格
pub fn algorithm_pipeline() {
    // 创建channels
    let ch1 = CspChannel::new();
    let ch2 = CspChannel::new();
    
    let (tx1, rx1) = ch1.split();
    let (tx2, rx2) = ch2.split();
    
    // Stage 1: 生成数据
    let generator = thread::spawn(move || {
        for i in 0..10 {
            println!("[Generator] 发送: {}", i);
            tx1.send(i).unwrap();
        }
    });
    
    // Stage 2: 处理数据
    let processor = thread::spawn(move || {
        while let Ok(value) = rx1.recv() {
            let processed = value * 2;
            println!("[Processor] 处理: {} -> {}", value, processed);
            tx2.send(processed).unwrap();
        }
    });
    
    // Stage 3: 收集结果
    let collector = thread::spawn(move || {
        let mut results = Vec::new();
        while let Ok(value) = rx2.recv() {
            println!("[Collector] 收集: {}", value);
            results.push(value);
            if results.len() == 10 {
                break;
            }
        }
        results
    });
    
    // 等待完成
    generator.join().unwrap();
    drop(processor); // 关闭channel
    let results = collector.join().unwrap();
    println!("最终结果: {:?}", results);
}
```

---

## 4. Golang CSP vs Rust Async对比

### 4.1 语法对比

#### Golang: Goroutine + Channel

```go
// Golang CSP风格
func quickSort(arr []int) []int {
    if len(arr) <= 1 {
        return arr
    }
    
    pivot := arr[0]
    less := make(chan []int, 1)
    greater := make(chan []int, 1)
    
    // 并行分治
    go func() {
        lessArr := []int{}
        for _, v := range arr[1:] {
            if v < pivot {
                lessArr = append(lessArr, v)
            }
        }
        less <- quickSort(lessArr)
    }()
    
    go func() {
        greaterArr := []int{}
        for _, v := range arr[1:] {
            if v >= pivot {
                greaterArr = append(greaterArr, v)
            }
        }
        greater <- quickSort(greaterArr)
    }()
    
    // 合并结果
    lessResult := <-less
    greaterResult := <-greater
    
    result := append(lessResult, pivot)
    result = append(result, greaterResult...)
    return result
}
```

#### Rust: Async/Await

```rust
// Rust Async风格
pub async fn quick_sort_async(mut arr: Vec<i32>) -> Vec<i32> {
    if arr.len() <= 1 {
        return arr;
    }
    
    let pivot = arr[0];
    let (less, greater): (Vec<_>, Vec<_>) = arr[1..]
        .iter()
        .partition(|&&x| x < pivot);
    
    // 并行分治
    let (less_sorted, greater_sorted) = tokio::join!(
        quick_sort_async(less),
        quick_sort_async(greater)
    );
    
    // 合并结果
    let mut result = less_sorted;
    result.push(pivot);
    result.extend(greater_sorted);
    result
}
```

### 4.2 语义对比表

| 特性 | Golang CSP | Rust Async |
|------|-----------|-----------|
| **并发原语** | Goroutine + Channel | Future + Async/Await |
| **调度** | M:N调度器(Runtime) | 任务队列(可插拔) |
| **通信** | Channel（同步/异步） | Channel + Future |
| **select** | `select { case }` | `tokio::select! { }` |
| **内存模型** | 共享内存 + Channel | 所有权 + Send/Sync |
| **类型安全** | 运行时竞态检测 | 编译时防止竞态 |
| **开销** | 每个Goroutine ~2KB | 每个Future ~0-100B |

### 4.3 形式化等价性

#### 定理4.1（通信等价）

```text
在纯消息传递场景下，Golang CSP与Rust Async语义等价：

∀P ∈ CSP_Go. ∃Q ∈ Async_Rust. traces(P) ≈ traces(Q)
```

**示例证明**:

```rust
// Golang: ch <- v
// Rust等价: tx.send(v).await

// Golang: v := <-ch
// Rust等价: v = rx.recv().await

// Golang:
// select {
// case v := <-ch1:
//     处理v
// case ch2 <- x:
//     发送x
// }

// Rust等价:
tokio::select! {
    v = rx1.recv() => {
        // 处理v
    }
    _ = tx2.send(x) => {
        // 发送x
    }
}
```

---

## 5. 调度机制原理

### 5.1 Actor调度

```text
Actor调度器（Mailbox-based）:

┌────────────────┐
│  Actor Pool    │
├────────────────┤
│ Actor 1 [░░░]  │ ← Mailbox队列
│ Actor 2 [░░░░] │
│ Actor 3 [░]    │
└────────────────┘
        ↓
   调度策略:
   1. FIFO：先到先服务
   2. Priority：优先级调度
   3. Fair：公平调度
```

### 5.2 Reactor调度

```text
Reactor调度器（Event-driven）:

┌─────────────────┐
│   Event Loop    │
└─────────────────┘
        ↓
┌─────────────────┐
│  epoll_wait()   │ ← IO事件
└─────────────────┘
        ↓
┌─────────────────┐
│  Ready Queue    │
├─────────────────┤
│ Task 1  [ready] │
│ Task 2  [ready] │
│ Task 3  [ready] │
└─────────────────┘
        ↓
   调度策略:
   1. FIFO：就绪顺序
   2. Work-Stealing：负载均衡
```

### 5.3 CSP调度

```text
CSP调度器（Go Runtime）:

┌─────────────────────────┐
│    M:N Scheduler        │
├─────────────────────────┤
│ M (OS线程)              │
│ ├─ P (Processor)        │
│ │  ├─ G1 (Goroutine)    │
│ │  ├─ G2                │
│ │  └─ Local Run Queue   │
│ └─ P                    │
│    └─ Global Run Queue  │
└─────────────────────────┘

调度策略:
1. Work-Stealing：P间任务窃取
2. Syscall处理：G阻塞时P转移
3. Preemption：协作式抢占
```

---

## 6. 算法应用示例

### 6.1 并行归并排序（Actor模式）

```rust
use tokio::sync::oneshot;

#[derive(Debug)]
pub enum MergeSortMessage {
    Sort {
        data: Vec<i32>,
        reply: oneshot::Sender<Vec<i32>>,
    },
}

impl ActorMessage for MergeSortMessage {}

pub struct MergeSortActor;

impl Actor for MergeSortActor {
    type Message = MergeSortMessage;
    type State = ();
    
    fn handle(
        &mut self,
        msg: Self::Message,
        state: Self::State,
        ctx: &mut ActorContext<Self>,
    ) -> Self::State {
        match msg {
            MergeSortMessage::Sort { data, reply } => {
                if data.len() <= 1 {
                    let _ = reply.send(data);
                    return state;
                }
                
                let mid = data.len() / 2;
                let (left, right) = data.split_at(mid);
                
                // 创建子Actor
                let left_actor = ctx.spawn(MergeSortActor);
                let right_actor = ctx.spawn(MergeSortActor);
                
                // 发送消息并等待结果
                let (left_tx, left_rx) = oneshot::channel();
                let (right_tx, right_rx) = oneshot::channel();
                
                ctx.send(left_actor, MergeSortMessage::Sort {
                    data: left.to_vec(),
                    reply: left_tx,
                });
                
                ctx.send(right_actor, MergeSortMessage::Sort {
                    data: right.to_vec(),
                    reply: right_tx,
                });
                
                // 合并（需要异步等待，这里简化）
                tokio::spawn(async move {
                    let left_sorted = left_rx.await.unwrap();
                    let right_sorted = right_rx.await.unwrap();
                    let merged = merge(left_sorted, right_sorted);
                    let _ = reply.send(merged);
                });
            }
        }
        state
    }
    
    fn initial_state(&self) -> Self::State {
        ()
    }
}

fn merge(left: Vec<i32>, right: Vec<i32>) -> Vec<i32> {
    let mut result = Vec::new();
    let (mut i, mut j) = (0, 0);
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }
    
    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);
    result
}
```

### 6.2 图遍历（Reactor模式）

```rust
use std::collections::{HashMap, VecDeque, HashSet};

/// 异步BFS（Reactor风格）
pub async fn bfs_reactor<T: Eq + std::hash::Hash + Clone + Send>(
    graph: Arc<HashMap<T, Vec<T>>>,
    start: T,
) -> Vec<T> {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    let mut result = Vec::new();
    
    queue.push_back(start.clone());
    visited.insert(start);
    
    while let Some(node) = queue.pop_front() {
        result.push(node.clone());
        
        // Reactor：异步获取邻居节点
        if let Some(neighbors) = graph.get(&node) {
            for neighbor in neighbors {
                if visited.insert(neighbor.clone()) {
                    queue.push_back(neighbor.clone());
                }
            }
        }
        
        // Yield给事件循环
        tokio::task::yield_now().await;
    }
    
    result
}
```

### 6.3 MapReduce（CSP风格）

```rust
use tokio::sync::mpsc;

/// MapReduce框架（CSP风格）
pub async fn map_reduce_csp<T, K, V>(
    data: Vec<T>,
    map_fn: impl Fn(T) -> (K, V) + Send + Sync + 'static + Copy,
    reduce_fn: impl Fn(V, V) -> V + Send + Sync + 'static + Copy,
) -> HashMap<K, V>
where
    T: Send + 'static,
    K: Eq + std::hash::Hash + Send + 'static,
    V: Send + 'static,
{
    let (map_tx, mut map_rx) = mpsc::channel(100);
    let (reduce_tx, mut reduce_rx) = mpsc::channel(100);
    
    // Map阶段
    let map_workers: Vec<_> = data.into_iter().map(|item| {
        let tx = map_tx.clone();
        tokio::spawn(async move {
            let result = map_fn(item);
            tx.send(result).await.unwrap();
        })
    }).collect();
    
    drop(map_tx); // 关闭发送端
    
    // Shuffle阶段
    let shuffle = tokio::spawn(async move {
        let mut groups: HashMap<K, Vec<V>> = HashMap::new();
        
        while let Some((key, value)) = map_rx.recv().await {
            groups.entry(key).or_default().push(value);
        }
        
        for (key, values) in groups {
            reduce_tx.send((key, values)).await.unwrap();
        }
    });
    
    drop(reduce_tx);
    
    // Reduce阶段
    let mut results = HashMap::new();
    while let Some((key, values)) = reduce_rx.recv().await {
        let reduced = values.into_iter().reduce(reduce_fn).unwrap();
        results.insert(key, reduced);
    }
    
    // 等待所有任务完成
    for worker in map_workers {
        worker.await.unwrap();
    }
    shuffle.await.unwrap();
    
    results
}
```

---

## 7. 形式化验证

### 7.1 Actor系统的性质

#### 性质7.1（消息传递保序性）

```text
对于同一发送者α₁发送给同一接收者α₂的消息序列：

send(α₂, m₁); send(α₂, m₂) ⇒ receive(m₁) happens-before receive(m₂)
```

#### 性质7.2（Actor隔离性）

```text
不同Actor的状态互不干扰：

∀α₁, α₂ ∈ Actors, α₁ ≠ α₂. state(α₁) ⊥ state(α₂)
```

### 7.2 Reactor系统的性质

#### 性质7.3（事件处理的完整性）

```text
所有就绪事件最终会被处理：

∀e ∈ Events. ready(e) ⇒ ◇ handled(e)
```

### 7.3 CSP系统的性质

#### 性质7.4（死锁自由）

```text
正确设计的CSP系统不会死锁：

∀P ∈ CSP. wellformed(P) ⇒ ¬deadlock(P)
```

---

## 8. 总结

### 对比表

| 维度 | Actor | Reactor | CSP |
|------|-------|---------|-----|
| **抽象层级** | 高（业务逻辑） | 中（IO多路复用） | 高（进程通信） |
| **通信方式** | 消息传递 | 事件回调 | Channel |
| **状态管理** | Actor内部 | Handler内部 | 进程局部 |
| **适用场景** | 分布式系统 | 网络服务器 | 并发pipeline |
| **Rust支持** | 库实现(Actix) | 原生(Tokio) | 库实现(Crossbeam) |

### 选择指南

1. **Actor**: 需要独立状态和消息传递
2. **Reactor**: 需要高性能异步IO
3. **CSP**: 需要进程间协作和pipeline

---

**文档版本**: 1.0.0  
**Rust版本**: 1.90+  
**最后更新**: 2025-10-02
