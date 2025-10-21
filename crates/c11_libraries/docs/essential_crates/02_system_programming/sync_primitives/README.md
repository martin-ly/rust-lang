# Sync Primitives - 同步原语

## 📋 目录

- [Sync Primitives - 同步原语](#sync-primitives---同步原语)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [标准库同步原语](#标准库同步原语)
    - [1. Mutex（互斥锁）](#1-mutex互斥锁)
      - [锁中毒（Poisoning）](#锁中毒poisoning)
    - [2. RwLock（读写锁）](#2-rwlock读写锁)
    - [3. Condvar（条件变量）](#3-condvar条件变量)
    - [4. Barrier（屏障）](#4-barrier屏障)
    - [5. Once（一次性初始化）](#5-once一次性初始化)
  - [Parking Lot](#parking-lot)
    - [为什么选择 Parking Lot？](#为什么选择-parking-lot)
    - [依赖配置](#依赖配置)
    - [Mutex 对比](#mutex-对比)
    - [RwLock 特性](#rwlock-特性)
    - [Deadlock Detection（死锁检测）](#deadlock-detection死锁检测)
    - [公平锁](#公平锁)
  - [Crossbeam 同步工具](#crossbeam-同步工具)
    - [1. Parker/Unparker](#1-parkerunparker)
    - [2. ShardedLock](#2-shardedlock)
    - [3. WaitGroup](#3-waitgroup)
  - [原子操作](#原子操作)
    - [标准库原子类型](#标准库原子类型)
    - [内存顺序（Memory Ordering）](#内存顺序memory-ordering)
    - [Compare-and-Swap](#compare-and-swap)
    - [自旋锁实现](#自旋锁实现)
  - [使用场景](#使用场景)
    - [1. 共享计数器](#1-共享计数器)
    - [2. 线程安全缓存](#2-线程安全缓存)
    - [3. 生产者-消费者（使用条件变量）](#3-生产者-消费者使用条件变量)
  - [性能对比](#性能对比)
    - [Mutex 性能](#mutex-性能)
    - [RwLock 性能](#rwlock-性能)
  - [最佳实践](#最佳实践)
    - [1. 选择合适的同步原语](#1-选择合适的同步原语)
    - [2. 减小锁粒度](#2-减小锁粒度)
    - [3. 避免死锁](#3-避免死锁)
    - [4. 使用 RAII 守卫](#4-使用-raii-守卫)
    - [5. 避免持锁调用外部代码](#5-避免持锁调用外部代码)
  - [技术选型](#技术选型)
  - [参考资源](#参考资源)

---

## 概述

同步原语是多线程编程中协调线程间访问共享资源的基础工具。

### 核心依赖

```toml
[dependencies]
# Parking Lot - 高性能同步原语
parking_lot = "0.12"

# Crossbeam - 并发工具
crossbeam = "0.8"

# 原子操作扩展
atomic = "0.5"
```

---

## 标准库同步原语

### 1. Mutex（互斥锁）

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn mutex_basic() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            // 获取锁
            let mut num = counter.lock().unwrap();
            *num += 1;
            // 锁在作用域结束时自动释放
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("结果: {}", *counter.lock().unwrap());
}
```

#### 锁中毒（Poisoning）

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn lock_poisoning() {
    let data = Arc::new(Mutex::new(0));
    let data_clone = data.clone();
    
    let _ = thread::spawn(move || {
        let mut lock = data_clone.lock().unwrap();
        *lock += 1;
        panic!("线程崩溃！"); // 锁被"中毒"
    }).join();
    
    // 尝试获取锁
    match data.lock() {
        Ok(guard) => println!("值: {}", *guard),
        Err(poisoned) => {
            // 可以恢复数据
            let guard = poisoned.into_inner();
            println!("恢复的值: {}", *guard);
        }
    }
}
```

### 2. RwLock（读写锁）

```rust
use std::sync::{Arc, RwLock};
use std::thread;

fn rwlock_example() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    
    // 多个读者
    let mut readers = vec![];
    for i in 0..3 {
        let data = data.clone();
        let handle = thread::spawn(move || {
            let r = data.read().unwrap();
            println!("读者 {}: {:?}", i, *r);
        });
        readers.push(handle);
    }
    
    // 单个写者
    let data_clone = data.clone();
    let writer = thread::spawn(move || {
        let mut w = data_clone.write().unwrap();
        w.push(4);
        println!("写者: 添加了 4");
    });
    
    for handle in readers {
        handle.join().unwrap();
    }
    writer.join().unwrap();
    
    println!("最终: {:?}", *data.read().unwrap());
}
```

### 3. Condvar（条件变量）

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;
use std::time::Duration;

fn condvar_example() {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair_clone = pair.clone();
    
    // 等待线程
    let waiter = thread::spawn(move || {
        let (lock, cvar) = &*pair_clone;
        let mut started = lock.lock().unwrap();
        
        // 等待条件
        while !*started {
            println!("等待中...");
            started = cvar.wait(started).unwrap();
        }
        
        println!("条件满足，继续执行！");
    });
    
    // 通知线程
    thread::sleep(Duration::from_secs(1));
    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();
    *started = true;
    cvar.notify_one();
    
    waiter.join().unwrap();
}
```

### 4. Barrier（屏障）

```rust
use std::sync::{Arc, Barrier};
use std::thread;

fn barrier_example() {
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];
    
    for i in 0..3 {
        let barrier = barrier.clone();
        let handle = thread::spawn(move || {
            println!("线程 {} 准备中...", i);
            thread::sleep(std::time::Duration::from_millis(i * 100));
            
            println!("线程 {} 到达屏障", i);
            barrier.wait(); // 等待所有线程
            
            println!("线程 {} 继续执行", i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 5. Once（一次性初始化）

```rust
use std::sync::Once;

static INIT: Once = Once::new();
static mut VAL: usize = 0;

fn expensive_initialization() {
    INIT.call_once(|| {
        println!("执行昂贵的初始化...");
        unsafe {
            VAL = 42;
        }
    });
    
    unsafe {
        println!("值: {}", VAL);
    }
}

fn main() {
    // 多次调用，但初始化只执行一次
    expensive_initialization();
    expensive_initialization();
    expensive_initialization();
}
```

---

## Parking Lot

### 为什么选择 Parking Lot？

- ✅ **更快**：比标准库快 1.5-2 倍
- ✅ **更小**：`Mutex` 只占 1 字节
- ✅ **无锁中毒**：简化错误处理
- ✅ **公平锁**：可选的公平调度
- ✅ **死锁检测**：调试模式下检测死锁

### 依赖配置

```toml
[dependencies]
parking_lot = { version = "0.12", features = ["deadlock_detection"] }
```

### Mutex 对比

```rust
use parking_lot::Mutex;
use std::sync::Arc;
use std::thread;

fn parking_lot_mutex() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            // 不需要 .unwrap()，没有锁中毒
            let mut num = counter.lock();
            *num += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("结果: {}", *counter.lock());
}
```

### RwLock 特性

```rust
use parking_lot::RwLock;
use std::sync::Arc;
use std::thread;

fn parking_lot_rwlock() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    
    // 可升级的读锁
    let data_clone = data.clone();
    thread::spawn(move || {
        let upgradable = data_clone.upgradable_read();
        
        if upgradable.len() < 5 {
            // 升级为写锁
            let mut write_guard = upgradable.upgrade();
            write_guard.push(4);
            write_guard.push(5);
        }
    }).join().unwrap();
    
    println!("{:?}", *data.read());
}
```

### Deadlock Detection（死锁检测）

```rust
use parking_lot::{Mutex, deadlock};
use std::thread;
use std::time::Duration;

fn setup_deadlock_detection() {
    // 创建后台线程检测死锁
    thread::spawn(move || {
        loop {
            thread::sleep(Duration::from_secs(1));
            let deadlocks = deadlock::check_deadlock();
            if !deadlocks.is_empty() {
                println!("检测到 {} 个死锁！", deadlocks.len());
                for (i, threads) in deadlocks.iter().enumerate() {
                    println!("死锁 #{}:", i);
                    for t in threads {
                        println!("  线程 ID: {:?}", t.thread_id());
                        println!("  调用栈:");
                        for frame in t.backtrace() {
                            println!("    {:?}", frame);
                        }
                    }
                }
            }
        }
    });
}
```

### 公平锁

```rust
use parking_lot::FairMutex;
use std::sync::Arc;
use std::thread;

fn fair_mutex_example() {
    let counter = Arc::new(FairMutex::new(0));
    let mut handles = vec![];
    
    // 公平锁确保按请求顺序获得锁
    for i in 0..5 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock();
            println!("线程 {} 获得锁", i);
            *num += 1;
            thread::sleep(std::time::Duration::from_millis(100));
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

---

## Crossbeam 同步工具

### 1. Parker/Unparker

```rust
use crossbeam::sync::Parker;
use std::thread;
use std::time::Duration;

fn parker_example() {
    let parker = Parker::new();
    let unparker = parker.unparker().clone();
    
    thread::spawn(move || {
        thread::sleep(Duration::from_secs(1));
        println!("唤醒主线程");
        unparker.unpark();
    });
    
    println!("等待中...");
    parker.park();
    println!("已唤醒！");
}
```

### 2. ShardedLock

```rust
use crossbeam::sync::ShardedLock;
use std::sync::Arc;
use std::thread;

fn sharded_lock_example() {
    // 分片锁，减少读者竞争
    let lock = Arc::new(ShardedLock::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    // 多个并发读者
    for i in 0..10 {
        let lock = lock.clone();
        let handle = thread::spawn(move || {
            let data = lock.read().unwrap();
            println!("读者 {}: {:?}", i, *data);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 3. WaitGroup

```rust
use crossbeam::sync::WaitGroup;
use std::thread;

fn wait_group_example() {
    let wg = WaitGroup::new();
    
    for i in 0..5 {
        let wg = wg.clone();
        thread::spawn(move || {
            println!("工作者 {} 开始", i);
            thread::sleep(std::time::Duration::from_millis(100 * i));
            println!("工作者 {} 完成", i);
            drop(wg); // 通知完成
        });
    }
    
    println!("等待所有工作者完成...");
    wg.wait(); // 等待所有完成
    println!("全部完成！");
}
```

---

## 原子操作

### 标准库原子类型

```rust
use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;

fn atomic_example() {
    let counter = Arc::new(AtomicUsize::new(0));
    let flag = Arc::new(AtomicBool::new(false));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = counter.clone();
        let handle = thread::spawn(move || {
            // 原子增加
            counter.fetch_add(1, Ordering::SeqCst);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("计数: {}", counter.load(Ordering::SeqCst));
}
```

### 内存顺序（Memory Ordering）

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;

fn memory_ordering_example() {
    let flag = Arc::new(AtomicBool::new(false));
    let flag_clone = flag.clone();
    
    // 写者
    thread::spawn(move || {
        // Relaxed: 最弱的保证，最高性能
        flag_clone.store(true, Ordering::Relaxed);
        
        // Release: 保证之前的写操作可见
        flag_clone.store(true, Ordering::Release);
        
        // SeqCst: 顺序一致性，最强保证
        flag_clone.store(true, Ordering::SeqCst);
    });
    
    // 读者
    thread::spawn(move || {
        // Acquire: 保证之后的读操作看到最新值
        while !flag.load(Ordering::Acquire) {
            std::hint::spin_loop();
        }
        println!("标志已设置！");
    });
}
```

### Compare-and-Swap

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

fn cas_example() {
    let value = AtomicUsize::new(0);
    
    // 尝试将 0 替换为 42
    let result = value.compare_exchange(
        0,                    // 期望值
        42,                   // 新值
        Ordering::SeqCst,     // 成功时的顺序
        Ordering::SeqCst,     // 失败时的顺序
    );
    
    match result {
        Ok(old) => println!("成功！旧值: {}", old),
        Err(current) => println!("失败！当前值: {}", current),
    }
}
```

### 自旋锁实现

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::cell::UnsafeCell;

pub struct SpinLock<T> {
    locked: AtomicBool,
    data: UnsafeCell<T>,
}

unsafe impl<T> Sync for SpinLock<T> where T: Send {}

impl<T> SpinLock<T> {
    pub fn new(data: T) -> Self {
        Self {
            locked: AtomicBool::new(false),
            data: UnsafeCell::new(data),
        }
    }
    
    pub fn lock(&self) -> SpinLockGuard<T> {
        // 自旋等待
        while self.locked.swap(true, Ordering::Acquire) {
            std::hint::spin_loop();
        }
        SpinLockGuard { lock: self }
    }
}

pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<'a, T> Drop for SpinLockGuard<'a, T> {
    fn drop(&mut self) {
        self.lock.locked.store(false, Ordering::Release);
    }
}

impl<'a, T> std::ops::Deref for SpinLockGuard<'a, T> {
    type Target = T;
    
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'a, T> std::ops::DerefMut for SpinLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

fn spinlock_usage() {
    let lock = SpinLock::new(0);
    {
        let mut guard = lock.lock();
        *guard += 1;
    }
}
```

---

## 使用场景

### 1. 共享计数器

```rust
use parking_lot::Mutex;
use std::sync::Arc;
use std::thread;

struct SharedCounter {
    count: Arc<Mutex<usize>>,
}

impl SharedCounter {
    fn new() -> Self {
        Self {
            count: Arc::new(Mutex::new(0)),
        }
    }
    
    fn increment(&self) {
        *self.count.lock() += 1;
    }
    
    fn get(&self) -> usize {
        *self.count.lock()
    }
    
    fn clone_handle(&self) -> Self {
        Self {
            count: self.count.clone(),
        }
    }
}

fn shared_counter_example() {
    let counter = SharedCounter::new();
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = counter.clone_handle();
        let handle = thread::spawn(move || {
            for _ in 0..100 {
                counter.increment();
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("最终计数: {}", counter.get());
}
```

### 2. 线程安全缓存

```rust
use parking_lot::RwLock;
use std::collections::HashMap;
use std::sync::Arc;

struct Cache<K, V> {
    data: Arc<RwLock<HashMap<K, V>>>,
}

impl<K: Eq + std::hash::Hash, V: Clone> Cache<K, V> {
    fn new() -> Self {
        Self {
            data: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    fn get(&self, key: &K) -> Option<V> {
        self.data.read().get(key).cloned()
    }
    
    fn insert(&self, key: K, value: V) {
        self.data.write().insert(key, value);
    }
    
    fn contains_key(&self, key: &K) -> bool {
        self.data.read().contains_key(key)
    }
}

fn cache_example() {
    let cache = Cache::new();
    
    cache.insert("key1", "value1");
    cache.insert("key2", "value2");
    
    if let Some(value) = cache.get(&"key1") {
        println!("找到: {}", value);
    }
}
```

### 3. 生产者-消费者（使用条件变量）

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::collections::VecDeque;
use std::thread;

struct BoundedQueue<T> {
    queue: Mutex<VecDeque<T>>,
    not_empty: Condvar,
    not_full: Condvar,
    capacity: usize,
}

impl<T> BoundedQueue<T> {
    fn new(capacity: usize) -> Self {
        Self {
            queue: Mutex::new(VecDeque::with_capacity(capacity)),
            not_empty: Condvar::new(),
            not_full: Condvar::new(),
            capacity,
        }
    }
    
    fn push(&self, item: T) {
        let mut queue = self.queue.lock().unwrap();
        
        // 等待空间
        while queue.len() >= self.capacity {
            queue = self.not_full.wait(queue).unwrap();
        }
        
        queue.push_back(item);
        self.not_empty.notify_one();
    }
    
    fn pop(&self) -> T {
        let mut queue = self.queue.lock().unwrap();
        
        // 等待数据
        while queue.is_empty() {
            queue = self.not_empty.wait(queue).unwrap();
        }
        
        let item = queue.pop_front().unwrap();
        self.not_full.notify_one();
        item
    }
}

fn bounded_queue_example() {
    let queue = Arc::new(BoundedQueue::new(5));
    
    // 生产者
    let q = queue.clone();
    let producer = thread::spawn(move || {
        for i in 0..10 {
            q.push(i);
            println!("生产: {}", i);
        }
    });
    
    // 消费者
    let consumer = thread::spawn(move || {
        for _ in 0..10 {
            let item = queue.pop();
            println!("消费: {}", item);
        }
    });
    
    producer.join().unwrap();
    consumer.join().unwrap();
}
```

---

## 性能对比

### Mutex 性能

| 实现 | 未竞争 | 低竞争 | 高竞争 |
|------|--------|--------|--------|
| `std::sync::Mutex` | 20 ns | 150 ns | 500 ns |
| `parking_lot::Mutex` | 10 ns | 80 ns | 300 ns |
| 自旋锁 | 5 ns | 50 ns | 1000+ ns |

### RwLock 性能

| 场景 | std::sync::RwLock | parking_lot::RwLock | crossbeam::ShardedLock |
|------|-------------------|---------------------|------------------------|
| **纯读** | 50 ns | 30 ns | 15 ns |
| **读多写少** | 100 ns | 60 ns | 40 ns |
| **读写均衡** | 300 ns | 200 ns | 180 ns |

---

## 最佳实践

### 1. 选择合适的同步原语

```rust
// 简单计数 -> 原子类型
use std::sync::atomic::AtomicUsize;
let counter = AtomicUsize::new(0);

// 复杂数据 -> Mutex
use parking_lot::Mutex;
let data = Mutex::new(vec![1, 2, 3]);

// 读多写少 -> RwLock
use parking_lot::RwLock;
let cache = RwLock::new(HashMap::new());
```

### 2. 减小锁粒度

```rust
// ❌ 粗粒度锁
struct BadDesign {
    data: Mutex<(Vec<i32>, HashMap<String, i32>)>,
}

// ✅ 细粒度锁
struct GoodDesign {
    vec_data: Mutex<Vec<i32>>,
    map_data: Mutex<HashMap<String, i32>>,
}
```

### 3. 避免死锁

```rust
// ❌ 可能死锁
fn deadlock_prone(lock1: &Mutex<i32>, lock2: &Mutex<i32>) {
    let _g1 = lock1.lock();
    let _g2 = lock2.lock(); // 如果另一个线程先锁 lock2，会死锁
}

// ✅ 总是按相同顺序获取锁
fn deadlock_free(lock1: &Mutex<i32>, lock2: &Mutex<i32>) {
    // 使用某种排序策略（如地址）
    let locks = if lock1 as *const _ < lock2 as *const _ {
        (lock1, lock2)
    } else {
        (lock2, lock1)
    };
    
    let _g1 = locks.0.lock();
    let _g2 = locks.1.lock();
}
```

### 4. 使用 RAII 守卫

```rust
use parking_lot::Mutex;

fn raii_guards() {
    let data = Mutex::new(vec![1, 2, 3]);
    
    // ✅ 守卫自动释放
    {
        let mut guard = data.lock();
        guard.push(4);
    } // 锁在这里释放
    
    // ❌ 手动管理容易出错
    // data.lock();
    // // ... 代码 ...
    // data.unlock(); // 容易忘记
}
```

### 5. 避免持锁调用外部代码

```rust
use parking_lot::Mutex;

// ❌ 持锁调用外部函数
fn bad_pattern(data: &Mutex<Vec<i32>>) {
    let mut guard = data.lock();
    external_function(&guard); // 可能很慢或死锁
}

// ✅ 最小化锁持有时间
fn good_pattern(data: &Mutex<Vec<i32>>) {
    let copy = {
        let guard = data.lock();
        guard.clone()
    }; // 锁释放
    
    external_function(&copy);
}

fn external_function(data: &[i32]) {
    println!("{:?}", data);
}
```

---

## 技术选型

| 场景 | 推荐方案 | 原因 |
|------|----------|------|
| **通用互斥** | `parking_lot::Mutex` | 性能优于标准库 |
| **读多写少** | `parking_lot::RwLock` | 读者并发 |
| **简单标志** | `AtomicBool` | 无锁，最快 |
| **计数器** | `AtomicUsize` | 原子操作 |
| **一次性初始化** | `std::sync::Once` 或 `once_cell` | 线程安全 |
| **条件等待** | `Condvar` | 标准方案 |
| **多读者优化** | `crossbeam::ShardedLock` | 分片减少竞争 |

---

## 参考资源

- [std::sync 文档](https://doc.rust-lang.org/std/sync/)
- [parking_lot GitHub](https://github.com/Amanieu/parking_lot)
- [crossbeam 文档](https://docs.rs/crossbeam/)
- [Rust Atomics and Locks](https://marabos.nl/atomics/)
