# 并发编程基础（Concurrent Programming Foundations）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [并发编程基础（Concurrent Programming Foundations）](#并发编程基础concurrent-programming-foundations)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [并发 vs 并行](#并发-vs-并行)
    - [并发（Concurrency）](#并发concurrency)
    - [并行（Parallelism）](#并行parallelism)
  - [线程基础](#线程基础)
    - [创建线程](#创建线程)
    - [传递数据到线程](#传递数据到线程)
  - [消息传递](#消息传递)
    - [Channel 基础](#channel-基础)
    - [多个发送者](#多个发送者)
  - [共享状态](#共享状态)
    - [Mutex（互斥锁）](#mutex互斥锁)
    - [RwLock（读写锁）](#rwlock读写锁)
  - [同步原语](#同步原语)
    - [Barrier（屏障）](#barrier屏障)
    - [Condvar（条件变量）](#condvar条件变量)
  - [实践示例](#实践示例)
    - [示例 1：生产者-消费者模式](#示例-1生产者-消费者模式)
    - [示例 2：线程池](#示例-2线程池)
  - [参考资料](#参考资料)

---

## 概述

并发编程允许程序同时处理多个任务。Rust 通过类型系统保证并发安全，避免了数据竞争等常见并发问题。

## 并发 vs 并行

### 并发（Concurrency）

多个任务交替执行，看起来同时进行：

```rust
use std::thread;
use std::time::Duration;

fn main() {
    let handle1 = thread::spawn(|| {
        for i in 1..5 {
            println!("线程 1: {}", i);
            thread::sleep(Duration::from_millis(100));
        }
    });

    let handle2 = thread::spawn(|| {
        for i in 1..5 {
            println!("线程 2: {}", i);
            thread::sleep(Duration::from_millis(100));
        }
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
}
```

### 并行（Parallelism）

多个任务真正同时执行，需要多核 CPU：

```rust
use rayon::prelude::*;

fn main() {
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    let result: Vec<i32> = data
        .par_iter()
        .map(|x| x * 2)
        .collect();

    println!("结果: {:?}", result);
}
```

## 线程基础

### 创建线程

```rust
use std::thread;

fn main() {
    let handle = thread::spawn(|| {
        println!("在新线程中执行");
    });

    handle.join().unwrap();
}
```

### 传递数据到线程

```rust
use std::thread;

fn main() {
    let data = vec![1, 2, 3, 4, 5];

    let handle = thread::spawn(move || {
        println!("数据: {:?}", data);
    });

    handle.join().unwrap();
}
```

## 消息传递

### Channel 基础

使用 `mpsc`（多生产者单消费者）channel：

```rust
use std::thread;
use std::sync::mpsc;

fn main() {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let val = String::from("hi");
        tx.send(val).unwrap();
    });

    let received = rx.recv().unwrap();
    println!("收到: {}", received);
}
```

### 多个发送者

```rust
use std::thread;
use std::sync::mpsc;

fn main() {
    let (tx, rx) = mpsc::channel();
    let tx1 = tx.clone();

    thread::spawn(move || {
        let vals = vec![
            String::from("hi"),
            String::from("from"),
            String::from("the"),
            String::from("thread"),
        ];

        for val in vals {
            tx.send(val).unwrap();
            thread::sleep(Duration::from_secs(1));
        }
    });

    thread::spawn(move || {
        let vals = vec![
            String::from("more"),
            String::from("messages"),
            String::from("for"),
            String::from("you"),
        ];

        for val in vals {
            tx1.send(val).unwrap();
            thread::sleep(Duration::from_secs(1));
        }
    });

    for received in rx {
        println!("收到: {}", received);
    }
}
```

## 共享状态

### Mutex（互斥锁）

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
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

    println!("结果: {}", *counter.lock().unwrap());
}
```

### RwLock（读写锁）

```rust
use std::sync::{Arc, RwLock};
use std::thread;

fn main() {
    let data = Arc::new(RwLock::new(0));

    // 多个读线程
    let mut handles = vec![];
    for i in 0..5 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let value = data.read().unwrap();
            println!("读线程 {}: {}", i, *value);
        });
        handles.push(handle);
    }

    // 写线程
    let data = Arc::clone(&data);
    let write_handle = thread::spawn(move || {
        let mut value = data.write().unwrap();
        *value += 1;
        println!("写线程: 更新值为 {}", *value);
    });
    handles.push(write_handle);

    for handle in handles {
        handle.join().unwrap();
    }
}
```

## 同步原语

### Barrier（屏障）

```rust
use std::sync::{Arc, Barrier};
use std::thread;

fn main() {
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];

    for i in 0..3 {
        let barrier = Arc::clone(&barrier);
        let handle = thread::spawn(move || {
            println!("线程 {} 到达屏障", i);
            barrier.wait();
            println!("线程 {} 通过屏障", i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
```

### Condvar（条件变量）

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;

fn main() {
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
    println!("条件满足！");
}
```

## 实践示例

### 示例 1：生产者-消费者模式

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn main() {
    let (tx, rx) = mpsc::channel();

    // 生产者
    let producer = thread::spawn(move || {
        for i in 0..10 {
            tx.send(i).unwrap();
            thread::sleep(Duration::from_millis(100));
        }
    });

    // 消费者
    let consumer = thread::spawn(move || {
        for received in rx {
            println!("消费: {}", received);
        }
    });

    producer.join().unwrap();
    consumer.join().unwrap();
}
```

### 示例 2：线程池

```rust
use std::sync::{Arc, Mutex, mpsc};
use std::thread;

type Job = Box<dyn FnOnce() + Send + 'static>;

struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<mpsc::Sender<Job>>,
}

impl ThreadPool {
    fn new(size: usize) -> ThreadPool {
        assert!(size > 0);

        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        ThreadPool {
            workers,
            sender: Some(sender),
        }
    }

    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.as_ref().unwrap().send(job).unwrap();
    }
}

struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Job>>>) -> Worker {
        let thread = thread::spawn(move || loop {
            let job = receiver.lock().unwrap().recv();

            match job {
                Ok(job) => {
                    println!("Worker {} 执行任务", id);
                    job();
                }
                Err(_) => {
                    println!("Worker {} 关闭", id);
                    break;
                }
            }
        });

        Worker {
            id,
            thread: Some(thread),
        }
    }
}
```

## 参考资料

- [Rust 并发模型理论](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- [C05 线程模块](../../../../crates/c05_threads/)
- [Rust 标准库并发文档](https://doc.rust-lang.org/std/sync/)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回编程范式: [`../00_index.md`](../00_index.md)
