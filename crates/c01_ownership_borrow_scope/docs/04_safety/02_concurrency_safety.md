# 并发安全 - Concurrency Safety

**版本**: 2.0  
**最后更新**: 2025-01-27  
**状态**: 完整版（已扩展）  

## 📋 目录

- [并发安全 - Concurrency Safety](#并发安全---concurrency-safety)
  - [📋 目录](#-目录)
  - [1. 并发安全基础](#1-并发安全基础)
    - [1.1 数据竞争问题](#11-数据竞争问题)
    - [1.2 Rust 的并发安全保证](#12-rust-的并发安全保证)
  - [2. Send 和 Sync Traits 深入解析](#2-send-和-sync-traits-深入解析)
    - [2.1 Send Trait](#21-send-trait)
    - [2.2 Sync Trait](#22-sync-trait)
    - [2.3 Send 和 Sync 的关系](#23-send-和-sync-的关系)
    - [2.4 自动实现规则](#24-自动实现规则)
    - [2.5 手动实现 Send/Sync](#25-手动实现-sendsync)
  - [3. 数据竞争预防机制](#3-数据竞争预防机制)
    - [3.1 编译时检查](#31-编译时检查)
    - [3.2 运行时检测工具](#32-运行时检测工具)
    - [3.3 实际案例分析](#33-实际案例分析)
  - [4. 并发原语详解](#4-并发原语详解)
    - [4.1 Mutex 互斥锁](#41-mutex-互斥锁)
    - [4.2 RwLock 读写锁](#42-rwlock-读写锁)
    - [4.3 Channel 通道](#43-channel-通道)
    - [4.4 Atomic 原子操作](#44-atomic-原子操作)
    - [4.5 Arc 原子引用计数](#45-arc-原子引用计数)
  - [5. 并发设计模式](#5-并发设计模式)
    - [5.1 共享状态模式](#51-共享状态模式)
    - [5.2 消息传递模式](#52-消息传递模式)
    - [5.3 Actor 模式](#53-actor-模式)
    - [5.4 Pipeline 模式](#54-pipeline-模式)
    - [5.5 工作窃取模式](#55-工作窃取模式)
  - [6. 死锁预防](#6-死锁预防)
    - [6.1 死锁的四个条件](#61-死锁的四个条件)
    - [6.2 预防策略](#62-预防策略)
  - [7. 性能考虑](#7-性能考虑)
    - [7.1 锁粒度](#71-锁粒度)
    - [7.2 无锁数据结构](#72-无锁数据结构)
  - [📚 总结](#-总结)

## 1. 并发安全基础

### 1.1 数据竞争问题

数据竞争（Data Race）是并发编程中最常见的问题之一。

```rust
// 数据竞争的定义
// 两个或多个线程同时访问同一内存位置
// 至少有一个访问是写操作
// 没有使用同步机制

// ❌ C/C++ 中的数据竞争示例（Rust 会阻止）
// let mut counter = 0;
// thread::spawn(|| { counter += 1; }); // 无法编译
// thread::spawn(|| { counter += 1; }); // 无法编译

use std::sync::{Arc, Mutex};
use std::thread;

// ✅ Rust 强制使用同步机制
fn safe_counter_example() {
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
}
```

### 1.2 Rust 的并发安全保证

Rust 通过类型系统在编译时保证并发安全。

```rust
// Rust 的并发安全保证
// 1. 无数据竞争
// 2. 无悬垂指针
// 3. 无死锁（编译时无法完全保证，但提供工具）

use std::sync::Arc;
use std::thread;

fn rust_concurrency_guarantees() {
    // 编译时保证 1: 不可变数据可以安全共享
    let data = Arc::new(vec![1, 2, 3, 4, 5]);
    let mut handles = vec![];

    for i in 0..3 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            println!("Thread {}: {:?}", i, &data);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 编译时保证 2: 可变数据需要独占访问
    let mut mutable_data = vec![1, 2, 3];
    // let handle = thread::spawn(move || {
    //     mutable_data.push(4); // 移动所有权
    // });
    // mutable_data.push(5); // ❌ 编译错误：已被移动
}
```

## 2. Send 和 Sync Traits 深入解析

### 2.1 Send Trait

`Send` trait 表示类型可以安全地在线程间传递所有权。

```rust
use std::thread;

// Send trait 的定义（简化）
// pub unsafe auto trait Send { }

// Send 的含义：值可以在线程间移动
fn send_trait_example() {
    // String 实现了 Send
    let s = String::from("hello");
    thread::spawn(move || {
        println!("{}", s); // s 的所有权移动到新线程
    });
    // println!("{}", s); // ❌ 编译错误：s 已被移动
}

// 大多数类型自动实现 Send
struct SafeToSend {
    data: Vec<i32>,
    name: String,
}

// 不实现 Send 的类型示例
use std::rc::Rc;

fn not_send_example() {
    let rc = Rc::new(42);
    // thread::spawn(move || {
    //     println!("{}", rc); // ❌ Rc<T> 不是 Send
    // });
}

// Send 的实际应用
fn use_send<T: Send>(value: T) {
    thread::spawn(move || {
        // 可以安全地使用 value
    });
}
```

### 2.2 Sync Trait

`Sync` trait 表示类型可以安全地在线程间共享引用。

```rust
use std::sync::Arc;
use std::thread;

// Sync trait 的定义（简化）
// pub unsafe auto trait Sync { }

// Sync 的含义：&T 可以在线程间共享
fn sync_trait_example() {
    // Arc 使得共享引用成为可能
    let data = Arc::new(vec![1, 2, 3]);
    let mut handles = vec![];

    for _ in 0..3 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            // &data 可以安全地在线程间共享
            println!("{:?}", &data);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}

// 实现 Sync 的类型
// 如果 T: Sync，则 &T 可以在线程间安全共享
struct SyncType {
    data: i32,
}

// 不实现 Sync 的类型示例
use std::cell::Cell;

fn not_sync_example() {
    let cell = Arc::new(Cell::new(42));
    // thread::spawn(move || {
    //     cell.set(43); // ❌ Cell<T> 不是 Sync
    // });
}
```

### 2.3 Send 和 Sync 的关系

```rust
// Send 和 Sync 的关系
// T: Sync ⟺ &T: Send
// 如果 T 是 Sync，则 &T 是 Send

use std::sync::Arc;
use std::thread;

fn send_sync_relationship() {
    // Vec<i32> 是 Sync，所以 &Vec<i32> 是 Send
    let vec = vec![1, 2, 3];
    let vec_ref = &vec;
    
    // 可以通过 Arc 在线程间共享
    let data = Arc::new(vec);
    let data_clone = Arc::clone(&data);
    
    thread::spawn(move || {
        // data_clone 是 Arc<Vec<i32>>
        // &*data_clone 是 &Vec<i32>，可以安全共享
        println!("{:?}", &*data_clone);
    });
}

// 类型组合的 Send/Sync 规则
struct Container<T> {
    value: T,
}

// 如果 T: Send，则 Container<T>: Send
// 如果 T: Sync，则 Container<T>: Sync

// 示例：不同组合的 Send/Sync 实现
use std::rc::Rc;
use std::cell::RefCell;

fn type_combinations() {
    // Vec<i32>: Send + Sync
    let vec: Vec<i32> = vec![1, 2, 3];
    
    // Rc<i32>: !Send + !Sync
    let rc: Rc<i32> = Rc::new(42);
    
    // Arc<i32>: Send + Sync
    let arc: Arc<i32> = Arc::new(42);
    
    // RefCell<i32>: Send + !Sync
    let refcell: RefCell<i32> = RefCell::new(42);
}
```

### 2.4 自动实现规则

```rust
// 编译器自动实现 Send 和 Sync 的规则

// 规则 1: 如果所有字段都是 Send，则类型自动实现 Send
struct AutoSend {
    field1: Vec<i32>,      // Send
    field2: String,        // Send
    field3: i32,           // Send
}
// AutoSend 自动实现 Send

// 规则 2: 如果所有字段都是 Sync，则类型自动实现 Sync
struct AutoSync {
    field1: i32,           // Sync
    field2: &'static str,  // Sync
}
// AutoSync 自动实现 Sync

// 规则 3: 如果任何字段不是 Send，则类型不是 Send
use std::rc::Rc;

struct NotSend {
    field1: Vec<i32>,      // Send
    field2: Rc<i32>,       // !Send
}
// NotSend 不实现 Send

// 规则 4: 泛型类型的 Send/Sync 依赖于类型参数
struct Generic<T> {
    value: T,
}
// Generic<T>: Send 当且仅当 T: Send
// Generic<T>: Sync 当且仅当 T: Sync
```

### 2.5 手动实现 Send/Sync

```rust
use std::marker::PhantomData;

// 手动实现 Send 和 Sync（需要 unsafe）
// 只有在确保安全的情况下才应该手动实现

// 示例：包装原始指针
struct RawPointerWrapper {
    ptr: *mut i32,
    _marker: PhantomData<i32>,
}

// 默认情况下，*mut T 不是 Send 也不是 Sync
// 如果我们能保证安全，可以手动实现

unsafe impl Send for RawPointerWrapper {}
unsafe impl Sync for RawPointerWrapper {}

// 实现这些 trait 的安全条件：
// 1. ptr 指向的数据必须是线程安全的
// 2. 没有未同步的内部可变性
// 3. 生命周期管理正确

// 实际应用示例：线程安全的计数器
use std::sync::atomic::{AtomicUsize, Ordering};

struct ThreadSafeCounter {
    count: AtomicUsize,
}

// AtomicUsize 是 Send + Sync
// ThreadSafeCounter 自动实现 Send + Sync

impl ThreadSafeCounter {
    fn new() -> Self {
        Self {
            count: AtomicUsize::new(0),
        }
    }

    fn increment(&self) {
        self.count.fetch_add(1, Ordering::SeqCst);
    }

    fn get(&self) -> usize {
        self.count.load(Ordering::SeqCst)
    }
}
```

## 3. 数据竞争预防机制

### 3.1 编译时检查

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// Rust 的编译时数据竞争检查
fn compile_time_checks() {
    let data = vec![1, 2, 3];

    // ❌ 示例 1: 尝试在多线程中访问可变数据
    // let mut data = vec![1, 2, 3];
    // thread::spawn(|| {
    //     data.push(4); // 编译错误：data 未实现 Send
    // });
    // data.push(5);

    // ✅ 正确方式：使用 Mutex
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let data_clone = Arc::clone(&data);

    thread::spawn(move || {
        data_clone.lock().unwrap().push(4);
    });

    // ❌ 示例 2: 尝试同时持有多个可变引用
    let mut vec = vec![1, 2, 3];
    // let ref1 = &mut vec;
    // let ref2 = &mut vec; // 编译错误：不能同时有两个可变引用

    // ✅ 正确方式：使用作用域分离
    {
        let ref1 = &mut vec;
        ref1.push(4);
    }
    {
        let ref2 = &mut vec;
        ref2.push(5);
    }
}

// 借用检查器防止数据竞争
fn borrow_checker_prevents_races() {
    let mut counter = 0;

    // ❌ 这会导致数据竞争（如果能编译）
    // let inc1 = || { counter += 1; };
    // let inc2 = || { counter += 1; };
    // thread::spawn(inc1);
    // thread::spawn(inc2);

    // ✅ 正确方式
    let counter = Arc::new(Mutex::new(0));
    let counter1 = Arc::clone(&counter);
    let counter2 = Arc::clone(&counter);

    let h1 = thread::spawn(move || {
        *counter1.lock().unwrap() += 1;
    });

    let h2 = thread::spawn(move || {
        *counter2.lock().unwrap() += 1;
    });

    h1.join().unwrap();
    h2.join().unwrap();
}
```

### 3.2 运行时检测工具

```rust
// 虽然 Rust 在编译时防止数据竞争，但仍有运行时工具可用于检测其他问题

// 1. ThreadSanitizer (TSan)
// cargo build --target x86_64-unknown-linux-gnu -Z build-std --target-dir=target/tsan
// RUSTFLAGS="-Z sanitizer=thread" cargo build

// 2. Miri - Rust 的解释器，用于检测未定义行为
// cargo +nightly miri test

// 3. Loom - 并发测试工具
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

// 示例：使用 loom 测试并发代码（需要 loom crate）
#[cfg(test)]
mod loom_tests {
    use super::*;
    
    // #[test]
    // fn test_concurrent_increment() {
    //     loom::model(|| {
    //         let counter = Arc::new(AtomicUsize::new(0));
    //         
    //         let threads: Vec<_> = (0..2)
    //             .map(|_| {
    //                 let counter = counter.clone();
    //                 loom::thread::spawn(move || {
    //                     counter.fetch_add(1, Ordering::SeqCst);
    //                 })
    //             })
    //             .collect();
    //         
    //         for thread in threads {
    //             thread.join().unwrap();
    //         }
    //         
    //         assert_eq!(counter.load(Ordering::SeqCst), 2);
    //     });
    // }
}
```

### 3.3 实际案例分析

```rust
use std::sync::{Arc, Mutex, RwLock};
use std::thread;
use std::time::Duration;

// 案例 1: 银行账户转账
struct BankAccount {
    balance: Mutex<f64>,
}

impl BankAccount {
    fn new(initial_balance: f64) -> Self {
        Self {
            balance: Mutex::new(initial_balance),
        }
    }

    fn transfer(&self, other: &BankAccount, amount: f64) -> Result<(), String> {
        // 正确的锁顺序防止死锁
        let mut from_balance = self.balance.lock().unwrap();
        let mut to_balance = other.balance.lock().unwrap();

        if *from_balance >= amount {
            *from_balance -= amount;
            *to_balance += amount;
            Ok(())
        } else {
            Err("Insufficient funds".to_string())
        }
    }
}

// 案例 2: 缓存系统
struct Cache {
    data: RwLock<std::collections::HashMap<String, String>>,
}

impl Cache {
    fn new() -> Self {
        Self {
            data: RwLock::new(std::collections::HashMap::new()),
        }
    }

    fn get(&self, key: &str) -> Option<String> {
        // 多个读者可以同时访问
        let data = self.data.read().unwrap();
        data.get(key).cloned()
    }

    fn set(&self, key: String, value: String) {
        // 写者需要独占访问
        let mut data = self.data.write().unwrap();
        data.insert(key, value);
    }
}

// 案例 3: 生产者-消费者模式
use std::sync::mpsc;

fn producer_consumer_example() {
    let (tx, rx) = mpsc::channel();

    // 生产者线程
    thread::spawn(move || {
        for i in 0..5 {
            tx.send(i).unwrap();
            thread::sleep(Duration::from_millis(100));
        }
    });

    // 消费者线程
    for received in rx {
        println!("Got: {}", received);
    }
}
```

## 4. 并发原语详解

### 4.1 Mutex 互斥锁

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// Mutex 提供互斥访问
fn mutex_detailed_example() {
    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            // lock() 获取锁，返回 MutexGuard
            let mut num = data.lock().unwrap();
            *num += 1;
            // MutexGuard 在离开作用域时自动释放锁
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Result: {}", *data.lock().unwrap());
}

// Mutex 的内部工作原理
// 1. 使用操作系统提供的原语（如 futex）
// 2. 维护一个等待队列
// 3. 提供公平性保证

// Mutex 的使用模式
struct SharedResource {
    data: Mutex<Vec<i32>>,
}

impl SharedResource {
    fn new() -> Self {
        Self {
            data: Mutex::new(Vec::new()),
        }
    }

    // 短暂持有锁
    fn add(&self, value: i32) {
        let mut data = self.data.lock().unwrap();
        data.push(value);
        // 锁在这里自动释放
    }

    // 避免长时间持有锁
    fn process(&self) {
        // ❌ 不好的做法
        // let mut data = self.data.lock().unwrap();
        // expensive_operation(&data); // 长时间持有锁

        // ✅ 好的做法
        let data = {
            let data = self.data.lock().unwrap();
            data.clone() // 复制数据，快速释放锁
        };
        expensive_operation(&data);
    }
}

fn expensive_operation(data: &[i32]) {
    // 耗时操作
}
```

### 4.2 RwLock 读写锁

```rust
use std::sync::{Arc, RwLock};
use std::thread;

// RwLock 允许多个读者或一个写者
fn rwlock_detailed_example() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];

    // 多个读者线程
    for i in 0..5 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            // 多个读者可以同时持有读锁
            let data = data.read().unwrap();
            println!("Reader {}: {:?}", i, &*data);
        });
        handles.push(handle);
    }

    // 一个写者线程
    let data_writer = Arc::clone(&data);
    let write_handle = thread::spawn(move || {
        // 写者需要独占访问
        let mut data = data_writer.write().unwrap();
        data.push(4);
    });
    handles.push(write_handle);

    for handle in handles {
        handle.join().unwrap();
    }
}

// RwLock 的性能特性
// - 读操作频繁时性能好
// - 写操作会阻塞所有读者
// - 可能存在写者饥饿问题

// RwLock 使用场景
struct Config {
    settings: RwLock<std::collections::HashMap<String, String>>,
}

impl Config {
    fn new() -> Self {
        Self {
            settings: RwLock::new(std::collections::HashMap::new()),
        }
    }

    // 频繁的读操作
    fn get(&self, key: &str) -> Option<String> {
        self.settings.read().unwrap().get(key).cloned()
    }

    // 偶尔的写操作
    fn set(&self, key: String, value: String) {
        self.settings.write().unwrap().insert(key, value);
    }
}
```

### 4.3 Channel 通道

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

// Channel 用于线程间通信
fn channel_detailed_example() {
    // 创建通道
    let (tx, rx) = mpsc::channel();

    // 发送者线程
    thread::spawn(move || {
        for i in 0..5 {
            tx.send(i).unwrap();
            thread::sleep(Duration::from_millis(100));
        }
    });

    // 接收者线程
    for received in rx {
        println!("Got: {}", received);
    }
}

// 多生产者单消费者
fn mpsc_example() {
    let (tx, rx) = mpsc::channel();

    for i in 0..3 {
        let tx = tx.clone();
        thread::spawn(move || {
            tx.send(format!("Message from thread {}", i)).unwrap();
        });
    }
    drop(tx); // 关闭原始发送者

    for received in rx {
        println!("{}", received);
    }
}

// 同步通道
fn sync_channel_example() {
    let (tx, rx) = mpsc::sync_channel(2); // 缓冲区大小为 2

    thread::spawn(move || {
        tx.send(1).unwrap(); // 立即成功
        tx.send(2).unwrap(); // 立即成功
        tx.send(3).unwrap(); // 阻塞，直到接收者消费
    });

    thread::sleep(Duration::from_secs(1));
    println!("{}", rx.recv().unwrap());
    println!("{}", rx.recv().unwrap());
    println!("{}", rx.recv().unwrap());
}
```

### 4.4 Atomic 原子操作

```rust
use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;

// Atomic 提供无锁原子操作
fn atomic_detailed_example() {
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                counter.fetch_add(1, Ordering::SeqCst);
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Result: {}", counter.load(Ordering::SeqCst));
}

// 内存顺序（Memory Ordering）
fn memory_ordering_example() {
    let flag = Arc::new(AtomicBool::new(false));
    let data = Arc::new(AtomicUsize::new(0));

    let flag_clone = Arc::clone(&flag);
    let data_clone = Arc::clone(&data);

    // 写者线程
    thread::spawn(move || {
        data_clone.store(42, Ordering::Release); // Release 语义
        flag_clone.store(true, Ordering::Release);
    });

    // 读者线程
    while !flag.load(Ordering::Acquire) {
        // Acquire 语义
    }
    assert_eq!(data.load(Ordering::Acquire), 42);
}

// Compare-and-swap (CAS)
fn cas_example() {
    let value = Arc::new(AtomicUsize::new(0));
    
    // 尝试将值从 0 改为 1
    let result = value.compare_exchange(
        0,                    // 期望的当前值
        1,                    // 新值
        Ordering::SeqCst,     // 成功时的内存顺序
        Ordering::SeqCst,     // 失败时的内存顺序
    );

    match result {
        Ok(prev) => println!("成功，之前的值: {}", prev),
        Err(current) => println!("失败，当前值: {}", current),
    }
}
```

### 4.5 Arc 原子引用计数

```rust
use std::sync::Arc;
use std::thread;

// Arc 实现线程安全的引用计数
fn arc_detailed_example() {
    let data = Arc::new(vec![1, 2, 3, 4, 5]);
    let mut handles = vec![];

    for i in 0..3 {
        // clone() 增加引用计数
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            println!("Thread {}: {:?}", i, data);
            // data 在这里被 drop，引用计数减 1
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
    // 最后一个引用被 drop 时，数据被释放
}

// Arc vs Rc
// Arc: 原子引用计数，线程安全，性能略低
// Rc:  非原子引用计数，非线程安全，性能略高

// Arc 的内部实现
// struct Arc<T> {
//     ptr: NonNull<ArcInner<T>>,
// }
// struct ArcInner<T> {
//     strong: AtomicUsize,  // 强引用计数
//     weak: AtomicUsize,    // 弱引用计数
//     data: T,
// }

// Arc 与 Mutex 的组合
use std::sync::Mutex;

fn arc_mutex_example() {
    let shared_data = Arc::new(Mutex::new(Vec::new()));
    let mut handles = vec![];

    for i in 0..5 {
        let data = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            let mut data = data.lock().unwrap();
            data.push(i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Result: {:?}", shared_data.lock().unwrap());
}
```

## 5. 并发设计模式

### 5.1 共享状态模式

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// 共享状态模式：多个线程通过锁访问共享数据
struct SharedState {
    counter: Arc<Mutex<i32>>,
}

impl SharedState {
    fn new() -> Self {
        Self {
            counter: Arc::new(Mutex::new(0)),
        }
    }

    fn increment(&self) {
        let mut counter = self.counter.lock().unwrap();
        *counter += 1;
    }

    fn get(&self) -> i32 {
        *self.counter.lock().unwrap()
    }
}

fn shared_state_pattern() {
    let state = Arc::new(SharedState::new());
    let mut handles = vec![];

    for _ in 0..10 {
        let state = Arc::clone(&state);
        let handle = thread::spawn(move || {
            for _ in 0..100 {
                state.increment();
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Final count: {}", state.get());
}
```

### 5.2 消息传递模式

```rust
use std::sync::mpsc;
use std::thread;

// 消息传递模式：通过 channel 通信，不共享状态
enum Message {
    NewJob(i32),
    Terminate,
}

fn message_passing_pattern() {
    let (tx, rx) = mpsc::channel();

    // 工作线程
    let handle = thread::spawn(move || {
        loop {
            match rx.recv() {
                Ok(Message::NewJob(job)) => {
                    println!("Processing job: {}", job);
                }
                Ok(Message::Terminate) => {
                    println!("Terminating worker");
                    break;
                }
                Err(_) => break,
            }
        }
    });

    // 发送任务
    for i in 0..5 {
        tx.send(Message::NewJob(i)).unwrap();
    }
    tx.send(Message::Terminate).unwrap();

    handle.join().unwrap();
}
```

### 5.3 Actor 模式

```rust
use std::sync::mpsc;
use std::thread;

// Actor 模式：每个 Actor 有自己的状态和消息队列
struct Actor {
    receiver: mpsc::Receiver<ActorMessage>,
    state: i32,
}

enum ActorMessage {
    Increment,
    GetValue(mpsc::Sender<i32>),
    Stop,
}

impl Actor {
    fn new() -> (mpsc::Sender<ActorMessage>, thread::JoinHandle<()>) {
        let (tx, rx) = mpsc::channel();
        
        let handle = thread::spawn(move || {
            let mut actor = Actor {
                receiver: rx,
                state: 0,
            };
            actor.run();
        });

        (tx, handle)
    }

    fn run(&mut self) {
        loop {
            match self.receiver.recv() {
                Ok(ActorMessage::Increment) => {
                    self.state += 1;
                }
                Ok(ActorMessage::GetValue(sender)) => {
                    sender.send(self.state).unwrap();
                }
                Ok(ActorMessage::Stop) => break,
                Err(_) => break,
            }
        }
    }
}

fn actor_pattern_example() {
    let (actor_tx, actor_handle) = Actor::new();

    // 发送消息给 Actor
    actor_tx.send(ActorMessage::Increment).unwrap();
    actor_tx.send(ActorMessage::Increment).unwrap();

    // 获取 Actor 状态
    let (response_tx, response_rx) = mpsc::channel();
    actor_tx.send(ActorMessage::GetValue(response_tx)).unwrap();
    println!("Actor state: {}", response_rx.recv().unwrap());

    actor_tx.send(ActorMessage::Stop).unwrap();
    actor_handle.join().unwrap();
}
```

### 5.4 Pipeline 模式

```rust
use std::sync::mpsc;
use std::thread;

// Pipeline 模式：数据流经多个处理阶段
fn pipeline_pattern() {
    // 阶段 1: 生成数据
    let (tx1, rx1) = mpsc::channel();
    thread::spawn(move || {
        for i in 0..10 {
            tx1.send(i).unwrap();
        }
    });

    // 阶段 2: 处理数据（乘以 2）
    let (tx2, rx2) = mpsc::channel();
    thread::spawn(move || {
        for value in rx1 {
            tx2.send(value * 2).unwrap();
        }
    });

    // 阶段 3: 过滤数据（只保留偶数）
    let (tx3, rx3) = mpsc::channel();
    thread::spawn(move || {
        for value in rx2 {
            if value % 4 == 0 {
                tx3.send(value).unwrap();
            }
        }
    });

    // 消费结果
    for value in rx3 {
        println!("Final value: {}", value);
    }
}
```

### 5.5 工作窃取模式

```rust
// 工作窃取模式通常由并发库实现（如 rayon）
// 这里展示概念性实现

use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use std::thread;

struct WorkQueue {
    tasks: Mutex<VecDeque<Box<dyn FnOnce() + Send>>>,
}

impl WorkQueue {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            tasks: Mutex::new(VecDeque::new()),
        })
    }

    fn push(&self, task: Box<dyn FnOnce() + Send>) {
        self.tasks.lock().unwrap().push_back(task);
    }

    fn pop(&self) -> Option<Box<dyn FnOnce() + Send>> {
        self.tasks.lock().unwrap().pop_front()
    }

    fn steal(&self) -> Option<Box<dyn FnOnce() + Send>> {
        self.tasks.lock().unwrap().pop_back()
    }
}

// 实际应用中，推荐使用 rayon 等成熟的库
```

## 6. 死锁预防

### 6.1 死锁的四个条件

```rust
// 死锁需要同时满足四个条件：
// 1. 互斥：资源不能被共享
// 2. 持有并等待：持有资源的同时等待其他资源
// 3. 不可抢占：不能强制获取其他线程的资源
// 4. 循环等待：存在资源等待的循环

use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

// ❌ 死锁示例
fn deadlock_example() {
    let resource1 = Arc::new(Mutex::new(1));
    let resource2 = Arc::new(Mutex::new(2));

    let r1 = Arc::clone(&resource1);
    let r2 = Arc::clone(&resource2);
    let thread1 = thread::spawn(move || {
        let _guard1 = r1.lock().unwrap();
        thread::sleep(Duration::from_millis(1));
        let _guard2 = r2.lock().unwrap(); // 可能死锁
    });

    let r1 = Arc::clone(&resource1);
    let r2 = Arc::clone(&resource2);
    let thread2 = thread::spawn(move || {
        let _guard2 = r2.lock().unwrap();
        thread::sleep(Duration::from_millis(1));
        let _guard1 = r1.lock().unwrap(); // 可能死锁
    });

    // thread1.join().unwrap();
    // thread2.join().unwrap();
}
```

### 6.2 预防策略

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// 策略 1: 锁排序 - 总是以相同的顺序获取锁
fn lock_ordering() {
    let resource1 = Arc::new(Mutex::new(1));
    let resource2 = Arc::new(Mutex::new(2));

    let r1 = Arc::clone(&resource1);
    let r2 = Arc::clone(&resource2);
    let thread1 = thread::spawn(move || {
        let _guard1 = r1.lock().unwrap(); // 先锁 1
        let _guard2 = r2.lock().unwrap(); // 后锁 2
    });

    let r1 = Arc::clone(&resource1);
    let r2 = Arc::clone(&resource2);
    let thread2 = thread::spawn(move || {
        let _guard1 = r1.lock().unwrap(); // 先锁 1
        let _guard2 = r2.lock().unwrap(); // 后锁 2
    });

    thread1.join().unwrap();
    thread2.join().unwrap();
}

// 策略 2: 尝试获取锁 - 使用 try_lock
fn try_lock_pattern() {
    let resource1 = Arc::new(Mutex::new(1));
    let resource2 = Arc::new(Mutex::new(2));

    let r1 = Arc::clone(&resource1);
    let r2 = Arc::clone(&resource2);

    thread::spawn(move || {
        loop {
            if let Ok(_guard1) = r1.try_lock() {
                if let Ok(_guard2) = r2.try_lock() {
                    // 获取了两个锁
                    break;
                }
                // 获取第二个锁失败，释放第一个锁并重试
            }
            thread::yield_now();
        }
    });
}

// 策略 3: 使用超时
use std::time::Duration;

fn timeout_pattern() {
    // 需要使用支持超时的锁实现
    // 标准库的 Mutex 不支持超时
    // 可以使用 parking_lot crate
}

// 策略 4: 减少锁的持有时间
fn minimize_lock_duration() {
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));

    // ❌ 不好的做法
    // let guard = data.lock().unwrap();
    // expensive_computation(&guard);

    // ✅ 好的做法
    let snapshot = {
        let guard = data.lock().unwrap();
        guard.clone() // 快速释放锁
    };
    expensive_computation(&snapshot);
}

fn expensive_computation(data: &[i32]) {
    // 耗时操作
}
```

## 7. 性能考虑

### 7.1 锁粒度

```rust
use std::sync::{Arc, Mutex, RwLock};
use std::collections::HashMap;

// 粗粒度锁：简单但可能导致争用
struct CoarseGrainedCache {
    data: Mutex<HashMap<String, String>>,
}

// 细粒度锁：复杂但减少争用
struct FineGrainedCache {
    shards: Vec<Mutex<HashMap<String, String>>>,
}

impl FineGrainedCache {
    fn new(num_shards: usize) -> Self {
        let mut shards = Vec::with_capacity(num_shards);
        for _ in 0..num_shards {
            shards.push(Mutex::new(HashMap::new()));
        }
        Self { shards }
    }

    fn get(&self, key: &str) -> Option<String> {
        let shard_index = self.hash(key) % self.shards.len();
        self.shards[shard_index].lock().unwrap().get(key).cloned()
    }

    fn set(&self, key: String, value: String) {
        let shard_index = self.hash(&key) % self.shards.len();
        self.shards[shard_index].lock().unwrap().insert(key, value);
    }

    fn hash(&self, key: &str) -> usize {
        // 简单的哈希函数
        key.bytes().fold(0usize, |acc, b| acc.wrapping_add(b as usize))
    }
}
```

### 7.2 无锁数据结构

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

// 无锁栈示例（简化版）
struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

impl<T> LockFreeStack<T> {
    fn new() -> Self {
        Self {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: ptr::null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Acquire);
            unsafe {
                (*new_node).next = head;
            }

            if self.head
                .compare_exchange(head, new_node, Ordering::Release, Ordering::Acquire)
                .is_ok()
            {
                break;
            }
        }
    }

    // pop 实现省略（需要处理 ABA 问题）
}

// 实际应用中，推荐使用成熟的无锁库，如 crossbeam
```

## 📚 总结

Rust 的并发安全特性：

1. **编译时保证**
   - 通过 Send 和 Sync trait 防止数据竞争
   - 借用检查器确保线程安全
   - 类型系统编码并发约束

2. **并发原语**
   - Mutex：互斥访问
   - RwLock：读写分离
   - Channel：消息传递
   - Atomic：无锁操作
   - Arc：线程安全引用计数

3. **设计模式**
   - 共享状态模式
   - 消息传递模式
   - Actor 模式
   - Pipeline 模式
   - 工作窃取模式

4. **最佳实践**
   - 优先使用消息传递而非共享状态
   - 减少锁的持有时间
   - 避免死锁（锁排序）
   - 选择合适的锁粒度
   - 考虑使用无锁数据结构

---

**相关文档**：

- [内存安全保证](./01_memory_safety.md)
- [性能优化](./03_performance_optimization.md)
- [高级借用模式](../03_advanced/02_advanced_borrowing.md)

**最后更新**: 2025年1月27日  
**维护状态**: 活跃维护中  
**质量等级**: 完整版
