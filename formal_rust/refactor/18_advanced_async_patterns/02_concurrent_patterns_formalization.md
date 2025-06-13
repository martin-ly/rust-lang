# 2. 并发模式形式化理论 (Concurrent Patterns Formalization)

## 目录

1. [2. 并发模式形式化理论](#2-并发模式形式化理论)
   1. [2.1. 理论基础](#21-理论基础)
   2. [2.2. 线程池模式](#22-线程池模式)
   3. [2.3. Actor模型](#23-actor模型)
   4. [2.4. 消息传递模式](#24-消息传递模式)
   5. [2.5. 同步原语](#25-同步原语)
   6. [2.6. 核心定理证明](#26-核心定理证明)
   7. [2.7. Rust实现](#27-rust实现)
   8. [2.8. 性能分析](#28-性能分析)

---

## 2.1. 理论基础

### 2.1.1. 并发模型

**定义 2.1.1** (并发模型)
并发模型是一个五元组 $\mathcal{C} = (T, R, S, \mu, \sigma)$，其中：

- $T$ 是线程集合
- $R$ 是资源集合
- $S$ 是状态集合
- $\mu: T \times R \rightarrow \{0,1\}$ 是资源分配函数
- $\sigma: T \times S \rightarrow S$ 是状态转换函数

**定义 2.1.2** (并发执行)
对于线程集合 $T' \subseteq T$，并发执行定义为：
$$\text{concurrent}(T') = \bigcup_{t \in T'} \text{execute}(t)$$

### 2.1.2. 并发安全性

**定义 2.1.3** (数据竞争)
对于两个线程 $t_1, t_2 \in T$ 和共享资源 $r \in R$，存在数据竞争当且仅当：
$$\exists t_1, t_2: \mu(t_1, r) = 1 \land \mu(t_2, r) = 1 \land \text{conflict}(t_1, t_2, r)$$

**定义 2.1.4** (并发安全)
并发程序是安全的，当且仅当不存在数据竞争：
$$\text{safe}(\mathcal{C}) \iff \neg \exists \text{race}(\mathcal{C})$$

---

## 2.2. 线程池模式

### 2.2.1. 线程池模型

**定义 2.2.1** (线程池)
线程池是一个四元组 $\mathcal{P} = (W, Q, S, \pi)$，其中：

- $W$ 是工作线程集合
- $Q$ 是任务队列
- $S$ 是调度策略
- $\pi: Q \rightarrow W$ 是任务分配函数

**定义 2.2.2** (线程池状态)
线程池状态是一个三元组 $\text{state}(\mathcal{P}) = (|W|, |Q|, \text{load}(W))$，其中：

- $|W|$ 是活跃线程数
- $|Q|$ 是队列长度
- $\text{load}(W)$ 是线程负载

### 2.2.2. 调度策略

**算法 2.2.1** (FIFO调度)
```rust
fn fifo_schedule(queue: &mut VecDeque<Task>) -> Option<Task> {
    queue.pop_front()
}
```

**算法 2.2.2** (优先级调度)
```rust
fn priority_schedule(queue: &mut BinaryHeap<Task>) -> Option<Task> {
    queue.pop()
}
```

**算法 2.2.3** (负载均衡调度)
```rust
fn load_balance_schedule(workers: &[Worker], task: Task) -> Worker {
    workers.iter()
        .min_by_key(|w| w.load())
        .unwrap()
}
```

**定理 2.2.1** (线程池公平性)
如果调度函数 $\pi$ 满足公平性条件，则：
$$\forall t \in Q: \lim_{n \to \infty} P(\pi(t) = w) = \frac{1}{|W|}$$

**证明**:
根据公平性定义，每个工作线程被选中的概率相等，因此：
$$\lim_{n \to \infty} P(\pi(t) = w) = \frac{1}{|W|}$$

---

## 2.3. Actor模型

### 2.3.1. Actor定义

**定义 2.3.1** (Actor)
Actor是一个五元组 $\mathcal{A} = (S, M, B, \delta, \lambda)$，其中：

- $S$ 是状态集合
- $M$ 是消息集合
- $B$ 是行为集合
- $\delta: S \times M \rightarrow S$ 是状态转换函数
- $\lambda: S \times M \rightarrow B$ 是行为函数

**定义 2.3.2** (Actor系统)
Actor系统是一个三元组 $\mathcal{S} = (A, C, \tau)$，其中：

- $A$ 是Actor集合
- $C$ 是通信通道集合
- $\tau: A \times A \rightarrow C$ 是通道映射函数

### 2.3.2. 消息传递

**定义 2.3.3** (消息传递)
从Actor $a_1$ 到Actor $a_2$ 的消息传递定义为：
$$a_1 \xrightarrow{m} a_2 = \text{send}(a_1, m, a_2)$$

**定义 2.3.4** (消息处理)
Actor $a$ 处理消息 $m$ 的过程定义为：
$$\text{process}(a, m) = \lambda(\text{state}(a), m)$$

**定理 2.3.1** (Actor隔离性)
任意两个Actor $a_1, a_2$ 的状态是隔离的：
$$\text{state}(a_1) \cap \text{state}(a_2) = \emptyset$$

**证明**:
根据Actor模型的定义，每个Actor都有独立的状态空间，因此状态是隔离的。

---

## 2.4. 消息传递模式

### 2.4.1. 同步消息传递

**定义 2.4.1** (同步消息传递)
同步消息传递是一个三元组 $\text{sync}(s, m, r)$，其中：

- $s$ 是发送者
- $m$ 是消息
- $r$ 是接收者

**算法 2.4.1** (同步发送)
```rust
fn sync_send<T>(sender: &Actor, message: T, receiver: &Actor) -> Result<(), Error> {
    let channel = get_channel(sender, receiver);
    channel.send(message)?;
    Ok(())
}
```

### 2.4.2. 异步消息传递

**定义 2.4.2** (异步消息传递)
异步消息传递是一个四元组 $\text{async}(s, m, r, f)$，其中：

- $s$ 是发送者
- $m$ 是消息
- $r$ 是接收者
- $f$ 是回调函数

**算法 2.4.2** (异步发送)
```rust
fn async_send<T, F>(sender: &Actor, message: T, receiver: &Actor, callback: F) 
where 
    F: FnOnce(Result<T, Error>) + Send + 'static
{
    let channel = get_channel(sender, receiver);
    tokio::spawn(async move {
        let result = channel.send(message).await;
        callback(result);
    });
}
```

### 2.4.3. 广播模式

**定义 2.4.3** (广播)
广播是一个三元组 $\text{broadcast}(s, m, R)$，其中：

- $s$ 是发送者
- $m$ 是消息
- $R$ 是接收者集合

**算法 2.4.3** (广播实现)
```rust
fn broadcast<T>(sender: &Actor, message: T, receivers: &[Actor]) {
    for receiver in receivers {
        let channel = get_channel(sender, receiver);
        tokio::spawn(async move {
            let _ = channel.send(message.clone()).await;
        });
    }
}
```

---

## 2.5. 同步原语

### 2.5.1. 互斥锁

**定义 2.5.1** (互斥锁)
互斥锁是一个三元组 $\mathcal{M} = (S, L, U)$，其中：

- $S \in \{\text{Locked}, \text{Unlocked}\}$ 是锁状态
- $L: T \rightarrow \text{Locked}$ 是加锁操作
- $U: \text{Locked} \rightarrow \text{Unlocked}$ 是解锁操作

**算法 2.5.1** (互斥锁实现)
```rust
use std::sync::{Arc, Mutex};

pub struct MutexLock<T> {
    inner: Arc<Mutex<T>>,
}

impl<T> MutexLock<T> {
    pub fn new(data: T) -> Self {
        Self {
            inner: Arc::new(Mutex::new(data)),
        }
    }

    pub fn lock(&self) -> Result<std::sync::MutexGuard<T>, Error> {
        self.inner.lock().map_err(|_| Error::LockFailed)
    }
}
```

### 2.5.2. 信号量

**定义 2.5.2** (信号量)
信号量是一个四元组 $\mathcal{S} = (C, P, V, \text{count})$，其中：

- $C$ 是容量
- $P$ 是P操作（获取）
- $V$ 是V操作（释放）
- $\text{count}$ 是当前计数

**算法 2.5.2** (信号量实现)
```rust
use std::sync::{Arc, Mutex, Condvar};

pub struct Semaphore {
    inner: Arc<(Mutex<usize>, Condvar)>,
    capacity: usize,
}

impl Semaphore {
    pub fn new(capacity: usize) -> Self {
        Self {
            inner: Arc::new((Mutex::new(capacity), Condvar::new())),
            capacity,
        }
    }

    pub fn acquire(&self) -> Result<(), Error> {
        let (lock, cvar) = &*self.inner;
        let mut count = lock.lock().unwrap();
        
        while *count == 0 {
            count = cvar.wait(count).unwrap();
        }
        
        *count -= 1;
        Ok(())
    }

    pub fn release(&self) -> Result<(), Error> {
        let (lock, cvar) = &*self.inner;
        let mut count = lock.lock().unwrap();
        
        if *count < self.capacity {
            *count += 1;
            cvar.notify_one();
        }
        
        Ok(())
    }
}
```

### 2.5.3. 条件变量

**定义 2.5.3** (条件变量)
条件变量是一个三元组 $\mathcal{C} = (M, W, N)$，其中：

- $M$ 是关联的互斥锁
- $W$ 是等待队列
- $N$ 是通知操作

**算法 2.5.3** (条件变量实现)
```rust
use std::sync::{Arc, Mutex, Condvar};

pub struct ConditionVariable {
    inner: Arc<(Mutex<bool>, Condvar)>,
}

impl ConditionVariable {
    pub fn new() -> Self {
        Self {
            inner: Arc::new((Mutex::new(false), Condvar::new())),
        }
    }

    pub fn wait(&self, mutex: &Mutex<()>) -> Result<(), Error> {
        let (lock, cvar) = &*self.inner;
        let _guard = mutex.lock().unwrap();
        
        let mut signaled = lock.lock().unwrap();
        while !*signaled {
            signaled = cvar.wait(signaled).unwrap();
        }
        
        *signaled = false;
        Ok(())
    }

    pub fn notify_one(&self) {
        let (lock, cvar) = &*self.inner;
        let mut signaled = lock.lock().unwrap();
        *signaled = true;
        cvar.notify_one();
    }

    pub fn notify_all(&self) {
        let (lock, cvar) = &*self.inner;
        let mut signaled = lock.lock().unwrap();
        *signaled = true;
        cvar.notify_all();
    }
}
```

---

## 2.6. 核心定理证明

### 2.6.1. 死锁避免定理

**定理 2.6.1** (死锁避免)
如果资源分配图是无环的，则系统不会发生死锁。

**证明**:
假设系统发生死锁，则存在循环等待链：
$$t_1 \rightarrow r_1 \rightarrow t_2 \rightarrow r_2 \rightarrow \cdots \rightarrow t_n \rightarrow r_n \rightarrow t_1$$

这构成了资源分配图中的环，与假设矛盾。

### 2.6.2. 并发正确性定理

**定理 2.6.2** (并发正确性)
如果所有共享资源的访问都是串行化的，则并发执行的结果是确定的。

**证明**:
串行化确保了执行顺序的一致性，因此结果确定。

### 2.6.3. Actor隔离性定理

**定理 2.6.3** (Actor隔离性)
Actor模型天然避免了数据竞争。

**证明**:
根据Actor模型的定义，每个Actor都有独立的状态，只能通过消息传递进行通信，因此不存在共享状态的数据竞争。

---

## 2.7. Rust实现

### 2.7.1. 线程池实现

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::collections::VecDeque;
use std::thread;
use std::time::Duration;

/// 任务类型
pub type Task = Box<dyn FnOnce() + Send + 'static>;

/// 工作线程
struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<VecDeque<Task>>>) -> Self {
        let thread = thread::spawn(move || {
            loop {
                let task = {
                    let mut queue = receiver.lock().unwrap();
                    queue.pop_front()
                };

                match task {
                    Some(task) => {
                        println!("Worker {} got a job; executing.", id);
                        task();
                    }
                    None => {
                        println!("Worker {} disconnected; shutting down.", id);
                        break;
                    }
                }
            }
        });

        Self {
            id,
            thread: Some(thread),
        }
    }
}

/// 线程池
pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: std::sync::mpsc::Sender<Task>,
}

impl ThreadPool {
    pub fn new(size: usize) -> ThreadPool {
        assert!(size > 0);

        let (sender, receiver) = std::sync::mpsc::channel();
        let receiver = Arc::new(Mutex::new(VecDeque::new()));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        // 启动任务分发线程
        let sender_clone = sender.clone();
        thread::spawn(move || {
            while let Ok(task) = receiver.recv() {
                if let Ok(mut queue) = receiver.lock() {
                    queue.push_back(task);
                }
            }
        });

        ThreadPool { workers, sender }
    }

    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let task = Box::new(f);
        self.sender.send(task).unwrap();
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}
```

### 2.7.2. Actor系统实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;
use serde::{Serialize, Deserialize};

/// 消息类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Message {
    Text(String),
    Number(i32),
    Data(Vec<u8>),
    Custom(serde_json::Value),
}

/// Actor trait
#[async_trait::async_trait]
pub trait Actor: Send + Sync {
    async fn receive(&mut self, message: Message) -> Result<(), Error>;
    fn get_id(&self) -> &str;
}

/// 简单Actor实现
pub struct SimpleActor {
    id: String,
    state: HashMap<String, serde_json::Value>,
    mailbox: mpsc::Receiver<Message>,
}

impl SimpleActor {
    pub fn new(id: String) -> (Self, mpsc::Sender<Message>) {
        let (tx, rx) = mpsc::channel(100);
        let actor = Self {
            id,
            state: HashMap::new(),
            mailbox: rx,
        };
        (actor, tx)
    }

    pub async fn run(mut self) {
        while let Some(message) = self.mailbox.recv().await {
            if let Err(e) = self.receive(message).await {
                eprintln!("Actor {} error: {:?}", self.id, e);
            }
        }
    }
}

#[async_trait::async_trait]
impl Actor for SimpleActor {
    async fn receive(&mut self, message: Message) -> Result<(), Error> {
        match message {
            Message::Text(text) => {
                println!("Actor {} received text: {}", self.id, text);
                self.state.insert("last_text".to_string(), serde_json::Value::String(text));
            }
            Message::Number(num) => {
                println!("Actor {} received number: {}", self.id, num);
                self.state.insert("last_number".to_string(), serde_json::Value::Number(num.into()));
            }
            Message::Data(data) => {
                println!("Actor {} received {} bytes", self.id, data.len());
                self.state.insert("last_data_size".to_string(), serde_json::Value::Number(data.len() as i64));
            }
            Message::Custom(value) => {
                println!("Actor {} received custom message: {:?}", self.id, value);
                self.state.insert("last_custom".to_string(), value);
            }
        }
        Ok(())
    }

    fn get_id(&self) -> &str {
        &self.id
    }
}

/// Actor系统
pub struct ActorSystem {
    actors: Arc<Mutex<HashMap<String, mpsc::Sender<Message>>>>,
}

impl ActorSystem {
    pub fn new() -> Self {
        Self {
            actors: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    pub async fn spawn_actor(&self, id: String) -> Result<mpsc::Sender<Message>, Error> {
        let (actor, sender) = SimpleActor::new(id.clone());
        let actor_id = actor.get_id().to_string();
        
        // 启动Actor
        tokio::spawn(actor.run());
        
        // 注册Actor
        let mut actors = self.actors.lock().unwrap();
        actors.insert(actor_id, sender.clone());
        
        Ok(sender)
    }

    pub async fn send_message(&self, actor_id: &str, message: Message) -> Result<(), Error> {
        let actors = self.actors.lock().unwrap();
        let sender = actors.get(actor_id).ok_or(Error::ActorNotFound)?;
        sender.send(message).await.map_err(|_| Error::SendFailed)
    }

    pub async fn broadcast(&self, message: Message) -> Result<(), Error> {
        let actors = self.actors.lock().unwrap();
        for sender in actors.values() {
            let _ = sender.send(message.clone()).await;
        }
        Ok(())
    }
}
```

### 2.7.3. 高级同步原语

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// 读写锁
pub struct ReadWriteLock<T> {
    inner: Arc<Mutex<ReadWriteState<T>>>,
}

struct ReadWriteState<T> {
    data: T,
    readers: usize,
    writer: bool,
    condvar: Condvar,
}

impl<T> ReadWriteLock<T> {
    pub fn new(data: T) -> Self {
        Self {
            inner: Arc::new(Mutex::new(ReadWriteState {
                data,
                readers: 0,
                writer: false,
                condvar: Condvar::new(),
            })),
        }
    }

    pub fn read(&self) -> Result<ReadGuard<T>, Error> {
        let mut state = self.inner.lock().unwrap();
        
        while state.writer {
            state = state.condvar.wait(state).unwrap();
        }
        
        state.readers += 1;
        Ok(ReadGuard {
            lock: self.inner.clone(),
        })
    }

    pub fn write(&self) -> Result<WriteGuard<T>, Error> {
        let mut state = self.inner.lock().unwrap();
        
        while state.writer || state.readers > 0 {
            state = state.condvar.wait(state).unwrap();
        }
        
        state.writer = true;
        Ok(WriteGuard {
            lock: self.inner.clone(),
        })
    }
}

pub struct ReadGuard<T> {
    lock: Arc<Mutex<ReadWriteState<T>>>,
}

impl<T> std::ops::Deref for ReadGuard<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        let state = self.lock.lock().unwrap();
        unsafe { &*(&state.data as *const T) }
    }
}

impl<T> Drop for ReadGuard<T> {
    fn drop(&mut self) {
        let mut state = self.lock.lock().unwrap();
        state.readers -= 1;
        if state.readers == 0 {
            state.condvar.notify_all();
        }
    }
}

pub struct WriteGuard<T> {
    lock: Arc<Mutex<ReadWriteState<T>>>,
}

impl<T> std::ops::Deref for WriteGuard<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        let state = self.lock.lock().unwrap();
        unsafe { &*(&state.data as *const T) }
    }
}

impl<T> std::ops::DerefMut for WriteGuard<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let mut state = self.lock.lock().unwrap();
        unsafe { &mut *(&mut state.data as *mut T) }
    }
}

impl<T> Drop for WriteGuard<T> {
    fn drop(&mut self) {
        let mut state = self.lock.lock().unwrap();
        state.writer = false;
        state.condvar.notify_all();
    }
}

/// 屏障同步
pub struct Barrier {
    inner: Arc<Mutex<BarrierState>>,
}

struct BarrierState {
    count: usize,
    generation: usize,
    condvar: Condvar,
}

impl Barrier {
    pub fn new(count: usize) -> Self {
        Self {
            inner: Arc::new(Mutex::new(BarrierState {
                count,
                generation: 0,
                condvar: Condvar::new(),
            })),
        }
    }

    pub fn wait(&self) -> Result<bool, Error> {
        let mut state = self.inner.lock().unwrap();
        let generation = state.generation;
        state.count -= 1;
        
        if state.count == 0 {
            // 最后一个到达的线程
            state.count = state.count;
            state.generation += 1;
            state.condvar.notify_all();
            Ok(true)
        } else {
            // 等待其他线程
            while state.generation == generation {
                state = state.condvar.wait(state).unwrap();
            }
            Ok(false)
        }
    }
}
```

---

## 2.8. 性能分析

### 2.8.1. 时间复杂度分析

**定理 2.8.1** (线程池复杂度)
线程池的任务调度时间复杂度为：
$$T(n) = O(\log n)$$

其中 $n$ 是任务数量。

**证明**:
使用优先队列进行任务调度，插入和删除操作的时间复杂度都是 $O(\log n)$。

### 2.8.2. 空间复杂度分析

**定理 2.8.2** (Actor系统空间复杂度)
Actor系统的空间复杂度为：
$$S(n) = O(n + m)$$

其中 $n$ 是Actor数量，$m$ 是消息数量。

**证明**:
每个Actor需要独立的内存空间，消息队列也需要存储空间。

### 2.8.3. 性能基准

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    #[tokio::test]
    async fn test_thread_pool_performance() {
        let pool = ThreadPool::new(4);
        let start = Instant::now();
        
        for i in 0..1000 {
            let pool_clone = &pool;
            pool_clone.execute(move || {
                std::thread::sleep(Duration::from_millis(1));
                println!("Task {} completed", i);
            });
        }
        
        // 等待所有任务完成
        std::thread::sleep(Duration::from_millis(2000));
        
        let duration = start.elapsed();
        println!("Thread pool processed 1000 tasks in {:?}", duration);
        
        assert!(duration.as_millis() < 3000);
    }

    #[tokio::test]
    async fn test_actor_system_performance() {
        let system = ActorSystem::new();
        let start = Instant::now();
        
        // 创建10个Actor
        let mut senders = Vec::new();
        for i in 0..10 {
            let sender = system.spawn_actor(format!("actor_{}", i)).await.unwrap();
            senders.push(sender);
        }
        
        // 发送1000条消息
        for i in 0..1000 {
            let sender = &senders[i % 10];
            let _ = sender.send(Message::Number(i as i32)).await;
        }
        
        // 等待消息处理
        tokio::time::sleep(Duration::from_millis(1000)).await;
        
        let duration = start.elapsed();
        println!("Actor system processed 1000 messages in {:?}", duration);
        
        assert!(duration.as_millis() < 2000);
    }

    #[test]
    fn test_rwlock_performance() {
        let lock = ReadWriteLock::new(0);
        let start = Instant::now();
        
        // 并发读取
        let handles: Vec<_> = (0..100).map(|_| {
            let lock_clone = lock.clone();
            std::thread::spawn(move || {
                for _ in 0..1000 {
                    let _guard = lock_clone.read().unwrap();
                }
            })
        }).collect();
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        let duration = start.elapsed();
        println!("RWLock handled 100000 reads in {:?}", duration);
        
        assert!(duration.as_millis() < 1000);
    }
}
```

---

## 总结

本章建立了并发模式的形式化理论体系，包括：

1. **理论基础**: 定义了并发模型和安全性概念
2. **线程池模式**: 建立了线程池的数学模型和调度算法
3. **Actor模型**: 提供了Actor的代数理论和消息传递机制
4. **消息传递模式**: 定义了同步和异步消息传递
5. **同步原语**: 实现了互斥锁、信号量、条件变量等
6. **核心定理证明**: 证明了死锁避免、并发正确性和Actor隔离性
7. **Rust实现**: 提供了完整的并发模式实现
8. **性能分析**: 分析了时间复杂度和空间复杂度

这些理论为并发编程提供了严格的数学基础，确保了程序的正确性和性能。 