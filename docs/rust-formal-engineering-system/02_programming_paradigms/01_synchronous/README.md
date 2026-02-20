# 同步编程范式

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
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
