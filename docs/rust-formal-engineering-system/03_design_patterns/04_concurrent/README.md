# 并发设计模式

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [c09_design_pattern/docs/](../../../../crates/c09_design_pattern/docs/)

[返回主索引](../../00_master_index.md)

---

## 并发安全的设计模式

### 无锁数据结构模式

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

// 原子计数器（无锁）
struct AtomicCounter {
    count: AtomicUsize,
}

impl AtomicCounter {
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
}

// 使用示例
fn lock_free_demo() {
    use std::thread;
    use std::sync::Arc;

    let counter = Arc::new(AtomicCounter::new());
    let mut handles = vec![];

    for _ in 0..10 {
        let c = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            for _ in 0..1000 {
                c.increment();
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(counter.get(), 10000);
}
```

### 线程池模式

```rust
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

// 线程池实现
pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<mpsc::Sender<Job>>,
}

type Job = Box<dyn FnOnce() + Send + 'static>;

impl ThreadPool {
    pub fn new(size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        Self {
            workers,
            sender: Some(sender),
        }
    }

    pub fn execute<F>(&self, f: F)
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
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Job>>>) -> Self {
        let thread = thread::spawn(move || loop {
            let job = receiver.lock().unwrap().recv();

            match job {
                Ok(job) => {
                    println!("Worker {} got a job; executing.", id);
                    job();
                }
                Err(_) => break,
            }
        });

        Self {
            id,
            thread: Some(thread),
        }
    }
}

// 使用示例
fn thread_pool_demo() {
    let pool = ThreadPool::new(4);

    for i in 0..8 {
        pool.execute(move || {
            println!("Processing task {}", i);
        });
    }
}
```

### 读写锁模式

```rust
use std::sync::{Arc, RwLock};
use std::thread;

// 多读单写模式
fn rwlock_pattern() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));

    // 多个读线程
    let mut handles = vec![];
    for _ in 0..5 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let read_guard = data.read().unwrap();
            println!("Read: {:?}", *read_guard);
        }));
    }

    // 一个写线程
    let data = Arc::clone(&data);
    handles.push(thread::spawn(move || {
        let mut write_guard = data.write().unwrap();
        write_guard.push(4);
        println!("Written");
    }));

    for h in handles {
        h.join().unwrap();
    }
}
```

## 相关 crates

| crate | 描述 | 路径 |
| :--- | :--- | :--- |
| c09_design_pattern | 并发设计模式实现 | [../../../../crates/c09_design_pattern/docs/](../../../../crates/c09_design_pattern/docs/) |
| c05_threads | 线程并发 | [../../../../crates/c05_threads/](../../../../crates/c05_threads/) |
| c06_async | 异步并发 | [../../../../crates/c06_async/](../../../../crates/c06_async/) |
