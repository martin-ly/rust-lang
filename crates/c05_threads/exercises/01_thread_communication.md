# C05 线程通信练习

> 难度: 中级 | 预计时间: 45 分钟

---

## 🎯 练习目标

- 掌握线程间通信机制
- 理解 mpsc 通道
- 掌握共享状态同步

---

## 练习 1: 生产者-消费者

实现一个多生产者单消费者模式。

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn main() {
    let (tx, rx) = mpsc::channel();

    // 创建多个生产者线程
    for i in 0..3 {
        let tx = tx.clone();
        thread::spawn(move || {
            for j in 0..5 {
                tx.send(format!("Producer {}: Message {}", i, j))
                    .unwrap();
                thread::sleep(Duration::from_millis(100));
            }
        });
    }

    drop(tx); // 关闭原始发送端

    // 消费者接收所有消息
    for msg in rx {
        println!("Received: {}", msg);
    }
}
```

**任务**:

1. 统计每个生产者的消息数量
2. 实现优雅关闭机制

---

## 练习 2: 共享计数器

使用 Arc 和 Mutex 实现线程安全的计数器。

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

    println!("Result: {}", *counter.lock().unwrap());
}
```

**任务**:

1. 优化性能（减少锁持有时间）
2. 处理 poison error

<details>
<summary>优化答案</summary>

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            // 减少锁持有时间
            let local_count = {
                let mut num = counter.lock().unwrap();
                *num += 1;
                *num
            };
            // 其他不需要锁的操作...
            local_count
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Result: {}", *counter.lock().unwrap());
}
```

</details>

---

## 练习 3: 线程池实现

实现一个简单的工作线程池。

```rust
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

type Job = Box<dyn FnOnce() + Send + 'static>;

pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: mpsc::Sender<Job>,
}

struct Worker {
    id: usize,
    thread: thread::JoinHandle<()>,
}

impl ThreadPool {
    pub fn new(size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            let receiver = Arc::clone(&receiver);
            let thread = thread::spawn(move || {
                loop {
                    let job = receiver.lock().unwrap().recv().unwrap();
                    println!("Worker {} executing job", id);
                    job();
                }
            });
            workers.push(Worker { id, thread });
        }

        Self { workers, sender }
    }

    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.send(job).unwrap();
    }
}

fn main() {
    let pool = ThreadPool::new(4);

    for i in 0..8 {
        pool.execute(move || {
            println!("Job {} started", i);
            thread::sleep(std::time::Duration::from_millis(500));
            println!("Job {} completed", i);
        });
    }

    thread::sleep(std::time::Duration::from_secs(5));
}
```

**任务**:

1. 添加优雅关闭功能
2. 实现任务优先级

---

## 📚 相关文档

- [C05 线程模块](../README.md)
- [Rust 并发编程](https://doc.rust-lang.org/book/ch16-00-concurrency.html)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
