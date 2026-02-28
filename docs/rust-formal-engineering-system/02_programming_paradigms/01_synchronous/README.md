# 同步编程范式

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至： [c05_threads/](../../../../crates/c05_threads/)

[返回主索引](../../00_master_index.md)

---

## 同步编程核心概念

### 线程与并发

Rust 通过标准库提供 OS 线程支持：

```rust
use std::thread;
use std::sync::mpsc;

// 基本线程创建
fn basic_threading() {
    // spawn 创建新线程
    let handle = thread::spawn(|| {
        println!("Hello from spawned thread!");
        42  // 返回值
    });

    println!("Hello from main thread!");

    // join 等待线程完成并获取结果
    let result = handle.join().unwrap();
    println!("Thread returned: {}", result);
}

// 线程间通信（mpsc：多生产者单消费者）
fn channel_communication() {
    let (tx, rx) = mpsc::channel();

    // 发送者可以克隆给多个线程
    let tx2 = tx.clone();

    thread::spawn(move || {
        tx.send("Hello from thread 1").unwrap();
    });

    thread::spawn(move || {
        tx2.send("Hello from thread 2").unwrap();
    });

    // 接收消息
    for _ in 0..2 {
        let msg = rx.recv().unwrap();
        println!("Received: {}", msg);
    }
}
```

### 共享状态并发

```rust
use std::sync::{Arc, Mutex, RwLock};
use std::thread;

// Mutex：互斥锁
fn mutex_demo() {
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

    println!("Result: {}", *counter.lock().unwrap());  // 10
}

// RwLock：读写锁
fn rwlock_demo() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));

    // 多个读锁可以同时持有
    let r1 = data.read().unwrap();
    let r2 = data.read().unwrap();
    println!("{:?} {:?}", r1, r2);
    drop(r1);
    drop(r2);

    // 写锁独占
    let mut w = data.write().unwrap();
    w.push(4);
}

// 原子类型
use std::sync::atomic::{AtomicUsize, Ordering};

fn atomic_demo() {
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            // 原子操作，无需加锁
            counter.fetch_add(1, Ordering::Relaxed);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Result: {}", counter.load(Ordering::Relaxed));  // 10
}
```

### 线程同步原语

```rust
use std::sync::{Barrier, Condvar};
use std::thread;
use std::time::Duration;

// Barrier：屏障同步
fn barrier_demo() {
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];

    for i in 0..3 {
        let b = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            println!("Thread {} before barrier", i);
            b.wait();  // 等待所有线程到达
            println!("Thread {} after barrier", i);
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
}

// Condvar：条件变量
use std::sync::Mutex;

fn condvar_demo() {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair2 = Arc::clone(&pair);

    thread::spawn(move || {
        let (lock, cvar) = &*pair2;
        let mut started = lock.lock().unwrap();
        *started = true;
        cvar.notify_one();
        println!("Child thread notified");
    });

    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();
    while !*started {
        started = cvar.wait(started).unwrap();
    }
    println!("Main thread awakened");
}
```

### Scoped 线程（无需 'static 生命周期）

```rust
use std::thread;

// 使用 scope 允许线程借用非 'static 数据
fn scoped_threads_demo() {
    let data = vec![1, 2, 3, 4, 5];
    let mut results = vec![];

    thread::scope(|s| {
        for i in 0..5 {
            s.spawn(|| {
                // 可以安全借用 data，因为 scope 保证线程在作用域结束前完成
                println!("Processing: {}", data[i]);
                data[i] * 2
            });
        }
    });

    // data 在这里仍然有效
    println!("Original data: {:?}", data);
}

// 并行处理数组
fn parallel_map<F, T, R>(input: &[T], f: F) -> Vec<R>
where
    F: Fn(&T) -> R + Sync + Send + Copy,
    T: Sync,
    R: Send,
{
    let mut results = Vec::with_capacity(input.len());
    results.resize_with(input.len(), || unsafe { std::mem::zeroed() });

    thread::scope(|s| {
        for (i, item) in input.iter().enumerate() {
            let result_slot = &results[i];
            s.spawn(move || {
                let result = f(item);
                // 安全地写入结果
                unsafe {
                    *(result_slot as *const _ as *mut R) = result;
                }
            });
        }
    });

    results
}
```

### 线程局部存储

```rust
use std::cell::RefCell;
use std::thread;

// 线程局部变量
thread_local! {
    static COUNTER: RefCell<u32> = RefCell::new(0);
}

fn thread_local_demo() {
    COUNTER.with(|c| {
        *c.borrow_mut() += 1;
        println!("Main thread counter: {}", c.borrow());
    });

    let handle = thread::spawn(|| {
        COUNTER.with(|c| {
            *c.borrow_mut() += 1;
            println!("Spawned thread counter: {}", c.borrow());
        });
    });

    handle.join().unwrap();

    // 主线程的值不变
    COUNTER.with(|c| {
        println!("Main thread counter after: {}", c.borrow());
    });
}
```

---

## 使用场景

| 场景 | 同步原语 | 适用说明 |
| :--- | :--- | :--- |
| 简单的共享计数器 | `AtomicUsize` | 无锁，最高性能 |
| 多线程共享可变状态 | `Mutex<T>` | 互斥访问，简单易用 |
| 多读少写场景 | `RwLock<T>` | 并发读，独占写 |
| 任务分发与收集 | `mpsc` 通道 | 生产者-消费者模式 |
| 多阶段并行计算 | `Barrier` | 同步多个线程的阶段 |
| 等待特定条件 | `Condvar` | 条件变量等待/通知 |
| 借用栈数据的多线程 | `thread::scope` | 避免 'static 约束 |
| 线程私有缓存 | `thread_local!` | 每个线程独立数据 |

---

## 相关研究笔记

### 软件设计理论

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 同步执行模型 | 同步模型理论 | [../../../research_notes/software_design_theory/03_execution_models/01_synchronous.md](../../../research_notes/software_design_theory/03_execution_models/01_synchronous.md) |
| 并发执行模型 | 并发模型理论 | [../../../research_notes/software_design_theory/03_execution_models/03_concurrent.md](../../../research_notes/software_design_theory/03_execution_models/03_concurrent.md) |
| 并行执行模型 | 并行模型理论 | [../../../research_notes/software_design_theory/03_execution_models/04_parallel.md](../../../research_notes/software_design_theory/03_execution_models/04_parallel.md) |

### 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| Send/Sync 形式化 | 线程安全 trait 形式化 | [../../../research_notes/formal_methods/send_sync_formalization.md](../../../research_notes/formal_methods/send_sync_formalization.md) |
| 所有权模型 | 所有权与并发 | [../../../research_notes/formal_methods/ownership_model.md](../../../research_notes/formal_methods/ownership_model.md) |

### 实验分析

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 并发性能 | 并发性能测试 | [../../../research_notes/experiments/concurrency_performance.md](../../../research_notes/experiments/concurrency_performance.md) |

---

## 相关 crates

| crate | 描述 | 路径 |
| :--- | :--- | :--- |
| c05_threads | 线程并发实现 | [../../../../crates/c05_threads/](../../../../crates/c05_threads/) |
| c09_design_pattern | 并发设计模式 | [../../../../crates/c09_design_pattern/](../../../../crates/c09_design_pattern/) |
