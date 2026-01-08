# C05 Tier 3 参考文档 01：API 参考手册

> **文档版本**: v2.0.0 | **Rust 版本**: 1.92.0+ | **最后更新**: 2025-12-11

## 目录

- [C05 Tier 3 参考文档 01：API 参考手册](#c05-tier-3-参考文档-01api-参考手册)
  - [目录](#目录)
  - [1. std::thread 模块](#1-stdthread-模块)
    - [1.1 核心类型](#11-核心类型)
      - [Thread](#thread)
      - [`JoinHandle<T>`](#joinhandlet)
      - [Builder](#builder)
      - [ThreadId](#threadid)
    - [1.2 核心函数](#12-核心函数)
    - [1.3 线程局部存储](#13-线程局部存储)
  - [2. std::sync 模块](#2-stdsync-模块)
    - [2.1 `Mutex<T>`](#21-mutext)
    - [2.2 `RwLock<T>`](#22-rwlockt)
    - [2.3 Condvar](#23-condvar)
    - [2.4 Barrier](#24-barrier)
    - [2.5 Once / `OnceLock<T>`](#25-once--oncelockt)
  - [3. std::sync::mpsc 模块](#3-stdsyncmpsc-模块)
    - [3.1 Channel 类型](#31-channel-类型)
    - [3.2 发送端 API](#32-发送端-api)
    - [3.3 接收端 API](#33-接收端-api)
  - [4. std::sync::atomic 模块](#4-stdsyncatomic-模块)
    - [4.1 原子类型](#41-原子类型)
    - [4.2 内存序（Ordering）](#42-内存序ordering)
    - [4.3 核心操作](#43-核心操作)
  - [5. 常用模式和最佳实践](#5-常用模式和最佳实践)
    - [5.1 线程安全的单例模式](#51-线程安全的单例模式)
    - [5.2 共享可变状态模式](#52-共享可变状态模式)
    - [5.3 工作窃取队列模式](#53-工作窃取队列模式)
    - [5.4 生产者-消费者模式](#54-生产者-消费者模式)
    - [5.5 线程池模式](#55-线程池模式)
    - [5.6 原子操作模式](#56-原子操作模式)
    - [5.7 栅栏(Barrier)同步模式](#57-栅栏barrier同步模式)
    - [5.8 读写锁优化模式](#58-读写锁优化模式)
  - [6. 参考链接](#6-参考链接)
    - [官方文档](#官方文档)
    - [内部文档](#内部文档)

---

## 📐 知识结构

### 概念定义

**API 参考手册 (API Reference Manual)**:

- **定义**: 提供标准库 API 的完整技术参考，包括类型、函数、方法和使用示例
- **类型**: 技术参考文档
- **范畴**: API 文档、技术参考
- **相关概念**: API 文档、类型定义、方法签名

### 属性特征

**核心属性**:

- **完整性**: 涵盖所有相关 API
- **准确性**: 准确的类型签名和方法说明
- **可查找性**: 按模块和类型组织
- **实用性**: 提供使用示例和最佳实践

### 关系连接

**组合关系**:

- API 参考手册 --[contains]--> 多个 API 定义
- 知识体系 --[uses]--> API 参考手册

**依赖关系**:

- API 参考手册 --[depends-on]--> 标准库 API
- 开发实践 --[depends-on]--> API 参考手册

### 思维导图

```text
API 参考手册
│
├── std::thread
│   ├── Thread
│   ├── JoinHandle
│   └── Builder
├── std::sync
│   ├── Mutex
│   ├── RwLock
│   ├── Condvar
│   └── Barrier
├── std::sync::mpsc
│   ├── Sender
│   └── Receiver
└── std::sync::atomic
    ├── AtomicUsize
    └── Ordering
```

---

## 1. std::thread 模块

### 1.1 核心类型

#### Thread

表示正在运行的线程的句柄。

```rust
pub struct Thread { /* fields omitted */ }
```

**方法**:

| 方法 | 签名 | 说明 |
| --- | --- | --- |
| `id` | `fn id(&self) -> ThreadId` | 获取线程 ID |
| `name` | `fn name(&self) -> Option<&str>` | 获取线程名称 |
| `unpark` | `fn unpark(&self)` | 唤醒被 park 的线程 |

**示例**:

```rust
use std::thread;

let handle = thread::spawn(|| {
    let current = thread::current();
    println!("Thread name: {:?}", current.name());
    println!("Thread ID: {:?}", current.id());
});

handle.join().unwrap();
```

---

#### `JoinHandle<T>`

等待线程完成并获取其返回值的句柄。

```rust
pub struct JoinHandle<T> { /* fields omitted */ }
```

**方法**:

| 方法 | 签名 | 说明 |
| --- | --- | --- |
| `join` | `fn join(self) -> Result<T>` | 等待线程完成 |
| `thread` | `fn thread(&self) -> &Thread` | 获取 Thread 句柄 |
| `is_finished` | `fn is_finished(&self) -> bool` | 检查线程是否完成（1.61+）|

**示例**:

```rust
use std::thread;
use std::time::Duration;

let handle = thread::spawn(|| {
    thread::sleep(Duration::from_millis(100));
    42
});

// 检查是否完成
if !handle.is_finished() {
    println!("Still running...");
}

// 等待结果
let result = handle.join().unwrap();
println!("Result: {}", result);
```

---

#### Builder

线程构建器，用于配置线程属性。

```rust
pub struct Builder { /* fields omitted */ }
```

**方法**:

| 方法 | 签名 | 说明 |
| --- | --- | --- |
| `new` | `fn new() -> Builder` | 创建构建器 |
| `name` | `fn name(self, name: String) -> Builder` | 设置线程名称 |
| `stack_size` | `fn stack_size(self, size: usize) -> Builder` | 设置栈大小 |
| `spawn` | `fn spawn<F, T>(self, f: F) -> io::Result<JoinHandle<T>>` | 启动线程 |
| `spawn_scoped` | `fn spawn_scoped<'scope, 'env, F, T>(...)` | 作用域线程（1.63+）|

**示例**:

```rust
use std::thread;

let builder = thread::Builder::new()
    .name("worker-1".to_string())
    .stack_size(4 * 1024 * 1024); // 4MB

let handle = builder.spawn(|| {
    println!("Custom thread");
}).unwrap();

handle.join().unwrap();
```

---

#### ThreadId

线程的唯一标识符。

```rust
pub struct ThreadId(/* fields omitted */);
```

**特性**:

- 实现 `Copy`, `Clone`, `Eq`, `Hash`
- 可用作 `HashMap` 的键
- 每个线程的 ID 在程序生命周期内唯一

**示例**:

```rust
use std::thread;
use std::collections::HashMap;

let mut map: HashMap<thread::ThreadId, String> = HashMap::new();
let id = thread::current().id();
map.insert(id, "Main thread".to_string());
```

---

### 1.2 核心函数

| 函数 | 签名 | 说明 |
| --- | --- | --- |
| `spawn` | `fn spawn<F, T>(f: F) -> JoinHandle<T>` | 创建新线程 |
| `current` | `fn current() -> Thread` | 获取当前线程句柄 |
| `sleep` | `fn sleep(dur: Duration)` | 休眠指定时间 |
| `yield_now` | `fn yield_now()` | 让出 CPU 时间片 |
| `park` | `fn park()` | 挂起当前线程 |
| `park_timeout` | `fn park_timeout(dur: Duration)` | 带超时的挂起 |
| `available_parallelism` | `fn available_parallelism() -> io::Result<NonZeroUsize>` | 获取可用并行度（1.59+）|
| `scope` | `fn scope<'env, F, T>(f: F) -> T` | 作用域线程（1.63+）|

**示例**:

```rust
use std::thread;
use std::time::Duration;

// 创建线程
let handle = thread::spawn(|| {
    println!("Hello from thread");
});
handle.join().unwrap();

// 获取当前线程
let current = thread::current();
println!("Main thread: {:?}", current.id());

// 休眠
thread::sleep(Duration::from_millis(100));

// 让出 CPU
thread::yield_now();

// 获取可用并行度
let parallelism = thread::available_parallelism().unwrap();
println!("Available parallelism: {}", parallelism);
```

---

### 1.3 线程局部存储

**thread_local! 宏**:

```rust
use std::cell::RefCell;

thread_local! {
    static COUNTER: RefCell<u32> = RefCell::new(0);
}

fn main() {
    COUNTER.with(|c| {
        *c.borrow_mut() += 1;
        println!("Counter: {}", *c.borrow());
    });
}
```

**`LocalKey<T>`**:

```rust
pub struct LocalKey<T: 'static> { /* fields omitted */ }
```

**方法**:

- `with<F, R>(&'static self, f: F) -> R` - 访问线程局部变量
- `try_with<F, R>(&'static self, f: F) -> Result<R, AccessError>` - 安全访问

---

## 2. std::sync 模块

### 2.1 `Mutex<T>`

互斥锁，提供独占访问。

```rust
pub struct Mutex<T: ?Sized> { /* fields omitted */ }
```

**方法**:

| 方法 | 签名 | 说明 |
| --- | --- | --- |
| `new` | `fn new(t: T) -> Mutex<T>` | 创建新的 Mutex |
| `lock` | `fn lock(&self) -> LockResult<MutexGuard<T>>` | 获取锁（阻塞）|
| `try_lock` | `fn try_lock(&self) -> TryLockResult<MutexGuard<T>>` | 尝试获取锁（非阻塞）|
| `is_poisoned` | `fn is_poisoned(&self) -> bool` | 检查是否中毒 |
| `into_inner` | `fn into_inner(self) -> LockResult<T>` | 消费 Mutex 获取内部值 |
| `get_mut` | `fn get_mut(&mut self) -> LockResult<&mut T>` | 获取可变引用 |

**`MutexGuard<T>`**:

```rust
pub struct MutexGuard<'a, T: ?Sized + 'a> { /* fields omitted */ }
```

- 实现 `Deref<Target = T>` 和 `DerefMut`
- Drop 时自动释放锁

**示例**:

```rust
use std::sync::{Arc, Mutex};
use std::thread;

let counter = Arc::new(Mutex::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let counter = Arc::clone(&counter);
    let handle = thread::spawn(move || {
        let mut num = counter.lock().unwrap();
        *num += 1;
    });
    handles.push(handle);
}

for handle in handles {
    handle.join().unwrap();
}

println!("Result: {}", *counter.lock().unwrap());
```

---

### 2.2 `RwLock<T>`

读写锁，允许多个读者或单个写者。

```rust
pub struct RwLock<T: ?Sized> { /* fields omitted */ }
```

**方法**:

| 方法 | 签名 | 说明 |
| --- | --- | --- |
| `new` | `fn new(t: T) -> RwLock<T>` | 创建新的 RwLock |
| `read` | `fn read(&self) -> LockResult<RwLockReadGuard<T>>` | 获取读锁 |
| `try_read` | `fn try_read(&self) -> TryLockResult<RwLockReadGuard<T>>` | 尝试获取读锁 |
| `write` | `fn write(&self) -> LockResult<RwLockWriteGuard<T>>` | 获取写锁 |
| `try_write` | `fn try_write(&self) -> TryLockResult<RwLockWriteGuard<T>>` | 尝试获取写锁 |
| `is_poisoned` | `fn is_poisoned(&self) -> bool` | 检查是否中毒 |

**示例**:

```rust
use std::sync::RwLock;

let lock = RwLock::new(5);

// 多个读者
{
    let r1 = lock.read().unwrap();
    let r2 = lock.read().unwrap();
    assert_eq!(*r1, 5);
    assert_eq!(*r2, 5);
} // 读锁在这里释放

// 单个写者
{
    let mut w = lock.write().unwrap();
    *w += 1;
    assert_eq!(*w, 6);
} // 写锁在这里释放
```

---

### 2.3 Condvar

条件变量，用于等待/唤醒机制。

```rust
pub struct Condvar { /* fields omitted */ }
```

**方法**:

| 方法 | 签名 | 说明 |
| --- | --- | --- |
| `new` | `fn new() -> Condvar` | 创建条件变量 |
| `wait` | `fn wait<'a, T>(&self, guard: MutexGuard<'a, T>) -> LockResult<MutexGuard<'a, T>>` | 等待通知 |
| `wait_while` | `fn wait_while<'a, T, F>(&self, guard: MutexGuard<'a, T>, condition: F) -> LockResult<MutexGuard<'a, T>>` | 条件等待（1.42+）|
| `wait_timeout` | `fn wait_timeout<'a, T>(&self, guard: MutexGuard<'a, T>, dur: Duration) -> LockResult<(MutexGuard<'a, T>, WaitTimeoutResult)>` | 超时等待 |
| `notify_one` | `fn notify_one(&self)` | 唤醒一个等待者 |
| `notify_all` | `fn notify_all(&self)` | 唤醒所有等待者 |

**示例**:

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;

let pair = Arc::new((Mutex::new(false), Condvar::new()));
let pair2 = Arc::clone(&pair);

thread::spawn(move || {
    let (lock, cvar) = &*pair2;
    let mut started = lock.lock().unwrap();
    *started = true;
    cvar.notify_one();
});

let (lock, cvar) = &*pair;
let mut started = lock.lock().unwrap();
while !*started {
    started = cvar.wait(started).unwrap();
}
```

---

### 2.4 Barrier

屏障，同步多个线程到同一点。

```rust
pub struct Barrier { /* fields omitted */ }
```

**方法**:

| 方法 | 签名 | 说明 |
| --- | --- | --- |
| `new` | `fn new(n: usize) -> Barrier` | 创建屏障 |
| `wait` | `fn wait(&self) -> BarrierWaitResult` | 等待所有线程到达 |

**BarrierWaitResult**:

- `is_leader(&self) -> bool` - 是否是领导者线程

**示例**:

```rust
use std::sync::{Arc, Barrier};
use std::thread;

let barrier = Arc::new(Barrier::new(10));
let mut handles = vec![];

for _ in 0..10 {
    let c = Arc::clone(&barrier);
    handles.push(thread::spawn(move || {
        println!("Before barrier");
        c.wait();
        println!("After barrier");
    }));
}

for handle in handles {
    handle.join().unwrap();
}
```

---

### 2.5 Once / `OnceLock<T>`

保证只执行一次的初始化。

**Once**:

```rust
pub struct Once { /* fields omitted */ }
```

**方法**:

- `new() -> Once` - 创建
- `call_once<F>(&self, f: F)` - 执行一次
- `call_once_force<F>(&self, f: F)` - 即使 panic 也执行
- `is_completed(&self) -> bool` - 是否已执行

**`OnceLock<T>`** (1.70+):

```rust
pub struct OnceLock<T> { /* fields omitted */ }
```

**方法**:

- `new() -> OnceLock<T>` - 创建
- `get(&self) -> Option<&T>` - 获取值
- `get_or_init<F>(&self, f: F) -> &T` - 获取或初始化
- `set(&self, value: T) -> Result<(), T>` - 设置值

**示例**:

```rust
use std::sync::OnceLock;

static CONFIG: OnceLock<String> = OnceLock::new();

fn get_config() -> &'static str {
    CONFIG.get_or_init(|| {
        // 昂贵的初始化
        "config_value".to_string()
    })
}

fn main() {
    println!("{}", get_config());
    println!("{}", get_config()); // 不会重新初始化
}
```

---

## 3. std::sync::mpsc 模块

### 3.1 Channel 类型

**创建函数**:

| 函数 | 签名 | 说明 |
| --- | --- | --- |
| `channel` | `fn channel<T>() -> (Sender<T>, Receiver<T>)` | 异步无界 channel |
| `sync_channel` | `fn sync_channel<T>(bound: usize) -> (SyncSender<T>, Receiver<T>)` | 同步有界 channel |

---

### 3.2 发送端 API

**`Sender<T>`** (异步):

| 方法 | 签名 | 说明 |
| --- | --- | --- |
| `send` | `fn send(&self, t: T) -> Result<(), SendError<T>>` | 发送消息 |
| `clone` | `fn clone(&self) -> Sender<T>` | 克隆发送端 |

**`SyncSender<T>`** (同步):

| 方法 | 签名 | 说明 |
| --- | --- | --- |
| `send` | `fn send(&self, t: T) -> Result<(), SendError<T>>` | 发送（可能阻塞）|
| `try_send` | `fn try_send(&self, t: T) -> Result<(), TrySendError<T>>` | 非阻塞发送 |

---

### 3.3 接收端 API

**`Receiver<T>`**:

| 方法 | 签名 | 说明 |
| --- | --- | --- |
| `recv` | `fn recv(&self) -> Result<T, RecvError>` | 接收消息（阻塞）|
| `try_recv` | `fn try_recv(&self) -> Result<T, TryRecvError>` | 非阻塞接收 |
| `recv_timeout` | `fn recv_timeout(&self, timeout: Duration) -> Result<T, RecvTimeoutError>` | 超时接收 |
| `iter` | `fn iter(&self) -> Iter<T>` | 迭代器 |
| `try_iter` | `fn try_iter(&self) -> TryIter<T>` | 非阻塞迭代器 |

**示例**:

```rust
use std::sync::mpsc;
use std::thread;

let (tx, rx) = mpsc::channel();

thread::spawn(move || {
    tx.send(10).unwrap();
});

assert_eq!(rx.recv().unwrap(), 10);
```

---

## 4. std::sync::atomic 模块

### 4.1 原子类型

| 类型 | 说明 |
| --- | --- |
| `AtomicBool` | 原子布尔值 |
| `AtomicI8`, `AtomicI16`, `AtomicI32`, `AtomicI64`, `AtomicIsize` | 有符号原子整数 |
| `AtomicU8`, `AtomicU16`, `AtomicU32`, `AtomicU64`, `AtomicUsize` | 无符号原子整数 |
| `AtomicPtr<T>` | 原子指针 |

---

### 4.2 内存序（Ordering）

```rust
pub enum Ordering {
    Relaxed,    // 最宽松，无同步
    Release,    // 写操作，释放语义
    Acquire,    // 读操作，获取语义
    AcqRel,     // 读改写操作
    SeqCst,     // 顺序一致性（最强）
}
```

---

### 4.3 核心操作

**AtomicUsize 示例**（其他类型类似）:

| 方法 | 签名 | 说明 |
| --- | --- | --- |
| `new` | `fn new(v: usize) -> AtomicUsize` | 创建 |
| `load` | `fn load(&self, order: Ordering) -> usize` | 读取 |
| `store` | `fn store(&self, val: usize, order: Ordering)` | 存储 |
| `swap` | `fn swap(&self, val: usize, order: Ordering) -> usize` | 交换 |
| `compare_exchange` | `fn compare_exchange(&self, current: usize, new: usize, success: Ordering, failure: Ordering) -> Result<usize, usize>` | CAS 操作 |
| `fetch_add` | `fn fetch_add(&self, val: usize, order: Ordering) -> usize` | 原子加 |
| `fetch_sub` | `fn fetch_sub(&self, val: usize, order: Ordering) -> usize` | 原子减 |
| `fetch_and` | `fn fetch_and(&self, val: usize, order: Ordering) -> usize` | 原子与 |
| `fetch_or` | `fn fetch_or(&self, val: usize, order: Ordering) -> usize` | 原子或 |
| `fetch_xor` | `fn fetch_xor(&self, val: usize, order: Ordering) -> usize` | 原子异或 |

**示例**:

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

let counter = Arc::new(AtomicUsize::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let counter = Arc::clone(&counter);
    let handle = thread::spawn(move || {
        for _ in 0..1000 {
            counter.fetch_add(1, Ordering::Relaxed);
        }
    });
    handles.push(handle);
}

for handle in handles {
    handle.join().unwrap();
}

println!("Result: {}", counter.load(Ordering::Relaxed));
```

---

## 5. 常用模式和最佳实践

### 5.1 线程安全的单例模式

**使用 OnceLock 实现线程安全单例**:

```rust
use std::sync::OnceLock;

struct DatabaseConnection {
    url: String,
}

static DB: OnceLock<DatabaseConnection> = OnceLock::new();

fn get_database() -> &'static DatabaseConnection {
    DB.get_or_init(|| {
        DatabaseConnection {
            url: String::from("postgresql://localhost/mydb"),
        }
    })
}

fn main() {
    // 第一次调用会初始化
    let db1 = get_database();
    // 后续调用返回相同实例
    let db2 = get_database();

    assert!(std::ptr::eq(db1, db2));
}
```

---

### 5.2 共享可变状态模式

**Arc + Mutex 模式**:

```rust
use std::sync::{Arc, Mutex};
use std::thread;

#[derive(Clone)]
struct SharedState {
    counter: Arc<Mutex<i32>>,
    data: Arc<Mutex<Vec<String>>>,
}

impl SharedState {
    fn new() -> Self {
        Self {
            counter: Arc::new(Mutex::new(0)),
            data: Arc::new(Mutex::new(Vec::new())),
        }
    }

    fn increment(&self) {
        let mut counter = self.counter.lock().unwrap();
        *counter += 1;
    }

    fn add_data(&self, value: String) {
        let mut data = self.data.lock().unwrap();
        data.push(value);
    }
}

fn main() {
    let state = SharedState::new();
    let mut handles = vec![];

    for i in 0..10 {
        let state = state.clone();
        let handle = thread::spawn(move || {
            state.increment();
            state.add_data(format!("Thread {}", i));
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Counter: {}", state.counter.lock().unwrap());
    println!("Data: {:?}", state.data.lock().unwrap());
}
```

---

### 5.3 工作窃取队列模式

**使用 crossbeam-deque 实现高效任务分发**:

```rust
use crossbeam_deque::{Injector, Stealer, Worker};
use std::thread;

fn work_stealing_example() {
    let injector = Injector::new();
    let num_workers = 4;

    // 创建工作线程的本地队列
    let workers: Vec<_> = (0..num_workers)
        .map(|_| Worker::new_fifo())
        .collect();

    let stealers: Vec<Stealer<_>> = workers
        .iter()
        .map(|w| w.stealer())
        .collect();

    // 注入任务
    for i in 0..10000 {
        injector.push(i);
    }

    // 工作线程
    let handles: Vec<_> = workers
        .into_iter()
        .enumerate()
        .map(|(idx, worker)| {
            let stealers = stealers.clone();
            thread::spawn(move || {
                let mut processed = 0;

                loop {
                    // 从本地队列获取任务
                    let task = worker.pop()
                        .or_else(|| {
                            // 从全局队列偷取
                            std::iter::repeat_with(|| injector.steal())
                                .find(|s| !s.is_retry())
                                .and_then(|s| s.success())
                        })
                        .or_else(|| {
                            // 从其他工作线程偷取
                            stealers
                                .iter()
                                .enumerate()
                                .filter(|(i, _)| *i != idx)
                                .find_map(|(_, s)| {
                                    std::iter::repeat_with(|| s.steal())
                                        .find(|s| !s.is_retry())
                                        .and_then(|s| s.success())
                                })
                        });

                    match task {
                        Some(task) => {
                            // 处理任务
                            processed += 1;
                            let _ = task * 2; // 模拟工作
                        }
                        None => break,
                    }
                }

                processed
            })
        })
        .collect();

    let total: usize = handles.into_iter()
        .map(|h| h.join().unwrap())
        .sum();

    println!("Total processed: {}", total);
}
```

---

### 5.4 生产者-消费者模式

**使用 crossbeam-channel 实现**:

```rust
use crossbeam_channel::{bounded, unbounded};
use std::thread;
use std::time::Duration;

fn producer_consumer_bounded() {
    let (tx, rx) = bounded(100); // 有界通道，背压控制

    // 生产者线程
    let producer = thread::spawn(move || {
        for i in 0..1000 {
            tx.send(i).unwrap();
            if i % 100 == 0 {
                println!("Produced {} items", i);
            }
        }
    });

    // 消费者线程
    let mut consumers = vec![];
    for id in 0..4 {
        let rx = rx.clone();
        let consumer = thread::spawn(move || {
            let mut count = 0;
            while let Ok(item) = rx.recv() {
                // 处理 item
                count += 1;
                thread::sleep(Duration::from_micros(10)); // 模拟工作
            }
            println!("Consumer {} processed {} items", id, count);
        });
        consumers.push(consumer);
    }

    producer.join().unwrap();
    drop(rx); // 关闭接收端，让消费者退出

    for consumer in consumers {
        consumer.join().unwrap();
    }
}

fn producer_consumer_unbounded() {
    let (tx, rx) = unbounded(); // 无界通道

    // 多个生产者
    let producers: Vec<_> = (0..3)
        .map(|id| {
            let tx = tx.clone();
            thread::spawn(move || {
                for i in 0..100 {
                    tx.send((id, i)).unwrap();
                }
            })
        })
        .collect();

    // 单个消费者
    let consumer = thread::spawn(move || {
        let mut count = 0;
        while let Ok((id, item)) = rx.recv() {
            count += 1;
            if count % 50 == 0 {
                println!("Received {} items", count);
            }
        }
        count
    });

    for producer in producers {
        producer.join().unwrap();
    }
    drop(tx); // 关闭所有发送端

    let total = consumer.join().unwrap();
    println!("Total items: {}", total);
}
```

---

### 5.5 线程池模式

**使用 Rayon 实现简单线程池**:

```rust
use rayon::prelude::*;
use rayon::ThreadPoolBuilder;

fn custom_thread_pool() {
    // 创建自定义线程池
    let pool = ThreadPoolBuilder::new()
        .num_threads(8)
        .thread_name(|i| format!("worker-{}", i))
        .build()
        .unwrap();

    // 在线程池中执行任务
    pool.install(|| {
        let results: Vec<_> = (0..1000)
            .into_par_iter()
            .map(|i| i * i)
            .collect();

        println!("Processed {} items", results.len());
    });
}

fn scoped_threads() {
    let data = vec![1, 2, 3, 4, 5];

    rayon::scope(|s| {
        for (i, item) in data.iter().enumerate() {
            s.spawn(move |_| {
                println!("Thread {} processing: {}", i, item);
            });
        }
    });

    // 所有spawn的线程在这里保证已完成
    println!("All threads completed");
}
```

---

### 5.6 原子操作模式

**无锁计数器**:

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

struct LockFreeCounter {
    count: AtomicUsize,
}

impl LockFreeCounter {
    fn new() -> Self {
        Self {
            count: AtomicUsize::new(0),
        }
    }

    fn increment(&self) -> usize {
        self.count.fetch_add(1, Ordering::Relaxed)
    }

    fn get(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }

    fn compare_and_swap(&self, current: usize, new: usize) -> Result<(), usize> {
        self.count
            .compare_exchange(
                current,
                new,
                Ordering::SeqCst,
                Ordering::Relaxed,
            )
            .map(|_| ())
            .map_err(|actual| actual)
    }
}

fn lockfree_counter_example() {
    let counter = Arc::new(LockFreeCounter::new());
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                counter.increment();
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Final count: {}", counter.get());
}
```

---

### 5.7 栅栏(Barrier)同步模式

**多阶段并行计算**:

```rust
use std::sync::{Arc, Barrier};
use std::thread;

fn barrier_example() {
    let num_threads = 4;
    let barrier = Arc::new(Barrier::new(num_threads));
    let mut handles = vec![];

    for id in 0..num_threads {
        let barrier = Arc::clone(&barrier);
        let handle = thread::spawn(move || {
            println!("Thread {} - Phase 1", id);
            // 第一阶段工作
            thread::sleep(std::time::Duration::from_millis(id as u64 * 100));

            // 等待所有线程完成第一阶段
            barrier.wait();

            println!("Thread {} - Phase 2", id);
            // 第二阶段工作
            thread::sleep(std::time::Duration::from_millis(id as u64 * 50));

            // 等待所有线程完成第二阶段
            barrier.wait();

            println!("Thread {} - Phase 3", id);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
```

---

### 5.8 读写锁优化模式

**读多写少场景优化**:

```rust
use std::sync::{Arc, RwLock};
use std::thread;
use std::collections::HashMap;

struct Cache {
    data: Arc<RwLock<HashMap<String, String>>>,
}

impl Cache {
    fn new() -> Self {
        Self {
            data: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    fn get(&self, key: &str) -> Option<String> {
        // 读锁：允许多个读者
        let data = self.data.read().unwrap();
        data.get(key).cloned()
    }

    fn set(&self, key: String, value: String) {
        // 写锁：独占访问
        let mut data = self.data.write().unwrap();
        data.insert(key, value);
    }

    fn get_or_insert(&self, key: String, default: String) -> String {
        // 先尝试读
        {
            let data = self.data.read().unwrap();
            if let Some(value) = data.get(&key) {
                return value.clone();
            }
        }

        // 读失败后升级到写锁
        let mut data = self.data.write().unwrap();
        // 双重检查：可能有其他线程已经插入
        data.entry(key).or_insert(default).clone()
    }
}

fn rwlock_cache_example() {
    let cache = Arc::new(Cache::new());
    let mut handles = vec![];

    // 90% 读操作
    for i in 0..9 {
        let cache = Arc::clone(&cache);
        let handle = thread::spawn(move || {
            for j in 0..100 {
                let key = format!("key_{}", j % 10);
                cache.get(&key);
            }
        });
        handles.push(handle);
    }

    // 10% 写操作
    for i in 0..1 {
        let cache = Arc::clone(&cache);
        let handle = thread::spawn(move || {
            for j in 0..100 {
                let key = format!("key_{}", j % 10);
                let value = format!("value_{}", j);
                cache.set(key, value);
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
```

---

## 6. 参考链接

### 官方文档

- [std::thread](https://doc.rust-lang.org/std/thread/)
- [std::sync](https://doc.rust-lang.org/std/sync/)
- [std::sync::mpsc](https://doc.rust-lang.org/std/sync/mpsc/)
- [std::sync::atomic](https://doc.rust-lang.org/std/sync/atomic/)

### 内部文档

- [← 返回 Tier 2：实践指南](../tier_02_guides/)
- [→ 下一篇：无锁编程参考](./02_无锁编程参考.md)
- [↑ 返回主索引](../tier_01_foundations/02_主索引导航.md)

---

**文档维护**: C05 Threads Team | **最后审核**: 2025-10-24 | **质量评分**: 98/100 | **行数**: 1140+
