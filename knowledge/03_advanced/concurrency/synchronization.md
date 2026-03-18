# Rust 同步原语深度解析

> 掌握 Rust 并发编程的核心同步机制，构建安全高效的多线程应用。
>
> **预计学习时间**: 90-120 分钟 | **难度**: 高级

---

## 🎯 学习目标

完成本章学习后，你将能够：

- 理解并正确运用 Rust 标准库提供的各类同步原语
- 掌握 `Mutex`、`RwLock`、`Condvar`、`Barrier` 的适用场景与性能特征
- 识别并避免常见的并发陷阱，包括死锁和 Poisoning
- 实现经典的并发模式：线程池、生产者-消费者、读者-写者
- 在多线程环境中安全地共享和操作数据

---

## 📋 先决条件

在学习本章之前，请确保你已掌握：

- Rust 所有权、借用和生命周期的基本概念
- 线程创建与基础并发（`std::thread`）
- `Arc` 智能指针的使用
- 基础的 `mpsc` 通道通信

---

## 🧠 核心概念

### Mutex - 互斥锁

`Mutex<T>` 提供独占访问，同一时刻只有一个线程可以获取锁。

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    // 使用 Arc 共享所有权，Mutex 提供互斥访问
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            // lock() 返回 MutexGuard，离开作用域自动释放
            let mut num = counter.lock().unwrap();
            *num += 1;
            // MutexGuard 在这里 drop，锁自动释放
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("结果: {}", *counter.lock().unwrap());
}
```

**关键要点**：

- `lock()` 可能阻塞当前线程，直到获取锁
- `MutexGuard` 实现 `Deref` 和 `DerefMut`，可直接操作内部数据
- 锁的释放遵循 RAII 原则，无需手动解锁

---

### RwLock - 读写锁

当读多写少时，`RwLock<T>` 比 `Mutex<T>` 更高效，允许多个读者或一个写者。

```rust
use std::sync::{Arc, RwLock};
use std::thread;
use std::time::Duration;

fn main() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];

    // 启动多个读者线程
    for i in 0..3 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let reader = data.read().unwrap();
            println!("读者 {} 读取数据: {:?}", i, *reader);
            thread::sleep(Duration::from_millis(100));
            // 多个读锁可以同时持有
        }));
    }

    // 启动写者线程
    let data_writer = Arc::clone(&data);
    handles.push(thread::spawn(move || {
        thread::sleep(Duration::from_millis(50));
        let mut writer = data_writer.write().unwrap();
        writer.push(4);
        println!("写者添加了新元素");
    }));

    for handle in handles {
        handle.join().unwrap();
    }
}
```

**性能考量**：

- 读锁可并发，适合读密集型场景
- 写锁独占，会阻塞所有读锁请求
- 避免写锁饥饿：长时间持有读锁可能阻塞写者

---

### Condvar - 条件变量

`Condvar` 用于线程间的事件通知，常与 `Mutex` 配合使用实现复杂的同步逻辑。

```rust
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

fn main() {
    // 使用元组 (Mutex, Condvar) 作为同步原语组合
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair_clone = Arc::clone(&pair);

    // 工作线程：等待条件满足后执行
    let worker = thread::spawn(move || {
        let (lock, cvar) = &*pair_clone;
        let mut started = lock.lock().unwrap();

        // 等待条件变为 true
        while !*started {
            // wait 会自动释放锁并阻塞，被唤醒后重新获取锁
            started = cvar.wait(started).unwrap();
        }

        println!("工作线程: 收到通知，开始执行！");
    });

    // 主线程：模拟一些准备工作
    thread::sleep(Duration::from_secs(1));

    {
        let (lock, cvar) = &*pair;
        let mut started = lock.lock().unwrap();
        *started = true;
        // 通知一个等待的线程
        cvar.notify_one();
    }

    worker.join().unwrap();
}
```

**使用模式**：

- 总是将条件变量与布尔条件一起使用（while 循环检查）
- `wait` 可能产生虚假唤醒，必须用 while 而非 if 检查条件
- `notify_one()` 唤醒一个线程，`notify_all()` 唤醒所有等待线程

---

### Barrier - 屏障

`Barrier` 用于同步多个线程，使它们在执行后续代码前全部到达某个同步点。

```rust
use std::sync::{Arc, Barrier};
use std::thread;
use std::time::Duration;

fn main() {
    // 创建一个需要 3 个线程的屏障
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];

    for i in 0..3 {
        let b = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            println!("线程 {}: 正在执行阶段 1", i);
            thread::sleep(Duration::from_millis(i as u64 * 100));

            // 所有线程到达这里后才继续
            let barrier_result = b.wait();

            // barrier_result 为领导者返回 true
            if barrier_result.is_leader() {
                println!("线程 {} 是领导者，协调后续任务", i);
            }

            println!("线程 {}: 开始执行阶段 2（所有线程已同步）", i);
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
```

**典型应用场景**：

- 并行计算中的分阶段处理（MapReduce 风格）
- 游戏开发中的逻辑帧同步
- 分布式系统的检查点同步

---

### Semaphore - 信号量

虽然标准库没有直接提供 `Semaphore`，但可通过 `tokio::sync::Semaphore` 或自定义实现。

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() {
    // 限制最多 3 个并发任务
    let semaphore = Arc::new(Semaphore::new(3));
    let mut handles = vec![];

    for i in 0..10 {
        let sem = Arc::clone(&semaphore);
        handles.push(tokio::spawn(async move {
            // 获取许可，如果没有可用则等待
            let _permit = sem.acquire().await.unwrap();

            println!("任务 {} 开始执行", i);
            sleep(Duration::from_secs(1)).await;
            println!("任务 {} 完成", i);
            // _permit 在这里 drop，释放许可
        }));
    }

    for handle in handles {
        handle.await.unwrap();
    }
}
```

**使用场景**：

- 限制并发连接数（数据库连接池）
- 限流控制（API 请求限制）
- 资源池管理

---

### mpsc 通道进阶

多生产者单消费者模式的高级用法：

```rust
use std::sync::mpsc::{self, Sender, Receiver};
use std::thread;
use std::time::Duration;

// 定义带优先级的消息
#[derive(Debug)]
enum Task {
    HighPriority(String),
    NormalPriority(String),
    LowPriority(String),
}

fn worker(id: usize, receiver: Receiver<Task>) {
    loop {
        match receiver.recv() {
            Ok(Task::HighPriority(msg)) => {
                println!("工作者 {} 紧急处理: {}", id, msg);
            }
            Ok(Task::NormalPriority(msg)) => {
                thread::sleep(Duration::from_millis(100));
                println!("工作者 {} 正常处理: {}", id, msg);
            }
            Ok(Task::LowPriority(msg)) => {
                thread::sleep(Duration::from_millis(300));
                println!("工作者 {} 延迟处理: {}", id, msg);
            }
            Err(_) => {
                println!("工作者 {}: 通道关闭，退出", id);
                break;
            }
        }
    }
}

fn main() {
    let (tx, rx) = mpsc::channel::<Task>();

    // 多个生产者
    let tx1 = tx.clone();
    let producer1 = thread::spawn(move || {
        for i in 0..5 {
            tx1.send(Task::NormalPriority(format!("P1-任务{}", i))).unwrap();
        }
    });

    let tx2 = tx.clone();
    let producer2 = thread::spawn(move || {
        tx2.send(Task::HighPriority("紧急任务".to_string())).unwrap();
        for i in 0..3 {
            tx2.send(Task::LowPriority(format!("P2-任务{}", i))).unwrap();
        }
    });

    // 单消费者
    let consumer = thread::spawn(move || worker(1, rx));

    producer1.join().unwrap();
    producer2.join().unwrap();
    drop(tx); // 关闭发送端，让接收者知道不会再有消息
    consumer.join().unwrap();
}
```

---

### 死锁避免

死锁发生的四个必要条件：互斥、占有等待、不可抢占、循环等待。

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

// 死锁示例（错误示范）
fn deadlock_example() {
    let lock1 = Arc::new(Mutex::new(0));
    let lock2 = Arc::new(Mutex::new(0));

    let l1 = Arc::clone(&lock1);
    let l2 = Arc::clone(&lock2);

    let t1 = thread::spawn(move || {
        let _a = l1.lock().unwrap();
        thread::sleep(Duration::from_millis(10));
        let _b = l2.lock().unwrap(); // 可能在这里死锁！
    });

    let l1 = Arc::clone(&lock1);
    let l2 = Arc::clone(&lock2);

    let t2 = thread::spawn(move || {
        let _a = l2.lock().unwrap();
        thread::sleep(Duration::from_millis(10));
        let _b = l1.lock().unwrap(); // 可能在这里死锁！
    });

    t1.join().unwrap();
    t2.join().unwrap();
}

// 解决方案 1：统一的加锁顺序
fn ordered_locking() {
    let lock1 = Arc::new(Mutex::new(0));
    let lock2 = Arc::new(Mutex::new(0));

    // 总是先锁 1，再锁 2
    let handles: Vec<_> = (0..2).map(|_| {
        let l1 = Arc::clone(&lock1);
        let l2 = Arc::clone(&lock2);
        thread::spawn(move || {
            let _a = l1.lock().unwrap();
            let _b = l2.lock().unwrap();
        })
    }).collect();

    for h in handles {
        h.join().unwrap();
    }
}

// 解决方案 2：使用 try_lock 避免阻塞
fn try_lock_example() {
    let lock1 = Arc::new(Mutex::new(0));
    let lock2 = Arc::new(Mutex::new(0));

    let l1 = Arc::clone(&lock1);
    let l2 = Arc::clone(&lock2);

    thread::spawn(move || {
        loop {
            if let Ok(guard1) = l1.try_lock() {
                if let Ok(guard2) = l2.try_lock() {
                    // 成功获取两把锁
                    drop(guard1);
                    drop(guard2);
                    break;
                }
                // 获取 lock2 失败，释放 lock1 重试
            }
            thread::sleep(Duration::from_millis(10));
        }
    });
}
```

**死锁预防策略**：

1. **锁顺序一致**：所有线程按相同顺序获取锁
2. **锁范围最小化**：尽快释放锁，减少持有时间
3. **避免在持有锁时调用外部代码**：防止未知的锁嵌套
4. **使用 try_lock**：非阻塞获取，失败时重试

---

### Poisoning 处理

当线程在持有锁时 panic，锁会被标记为 "poisoned" 状态。

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let data = Arc::new(Mutex::new(0));
    let data_clone = Arc::clone(&data);

    let handle = thread::spawn(move || {
        let mut lock = data_clone.lock().unwrap();
        *lock += 1;
        panic!("故意 panic！"); // 持有锁时 panic
    });

    // handle.join() 会返回 Err，因为子线程 panic
    let _ = handle.join();

    // 尝试获取锁会返回 PoisonError
    match data.lock() {
        Ok(guard) => println!("数据: {}", *guard),
        Err(poisoned) => {
            // 可以恢复使用被污染的数据
            let guard = poisoned.into_inner();
            println!("锁被污染，但数据仍可访问: {}", *guard);
        }
    }
}
```

**处理策略**：

- 对于关键数据，Poisoning 是一种安全机制，提示数据可能处于不一致状态
- 使用 `into_inner()` 恢复访问，或选择 panic 终止程序
- 考虑使用 `parking_lot` crate，它不提供 poisoning 机制（性能更好）

---

## 💡 最佳实践

### 1. 优先使用消息传递而非共享内存

```rust
// 推荐：使用通道传递数据
use std::sync::mpsc;
use std::thread;

fn process_in_parallel(items: Vec<i32>) -> Vec<i32> {
    let (tx, rx) = mpsc::channel();

    for item in items {
        let tx = tx.clone();
        thread::spawn(move || {
            let result = item * item; // 计算
            tx.send(result).unwrap();
        });
    }

    drop(tx); // 关闭发送端
    rx.iter().collect()
}
```

### 2. 避免在 async 代码中使用阻塞锁

```rust
// 错误：在 async 函数中使用 Mutex::lock 会阻塞执行器
async fn bad_example(data: std::sync::Arc<std::sync::Mutex<i32>>) {
    let mut guard = data.lock().unwrap(); // 阻塞！
    *guard += 1;
}

// 正确：使用 tokio::sync::Mutex
use tokio::sync::Mutex;

async fn good_example(data: std::sync::Arc<Mutex<i32>>) {
    let mut guard = data.lock().await; // 非阻塞
    *guard += 1;
}
```

### 3. 使用作用域线程简化生命周期

```rust
use std::thread;

fn scoped_threads_example() {
    let mut data = vec![1, 2, 3, 4, 5];

    // Rust 1.63+ 的 scoped threads
    thread::scope(|s| {
        s.spawn(|| {
            println!("线程 A 访问: {:?}", &data[..2]);
        });
        s.spawn(|| {
            println!("线程 B 访问: {:?}", &data[2..]);
        });
    });

    // 所有线程在这里保证已完成
    println!("所有线程完成: {:?}", data);
}
```

---

## ⚠️ 常见陷阱

### 陷阱 1：持有锁跨越 await 点

```rust
// 错误示例
async fn bad(data: Arc<Mutex<Data>>) {
    let guard = data.lock().unwrap();
    some_async_operation().await; // 锁在整个 await 期间被持有！
    drop(guard);
}

// 正确做法
async fn good(data: Arc<Mutex<Data>>) {
    {
        let guard = data.lock().unwrap();
        // 同步操作
    } // 锁在这里释放
    some_async_operation().await;
}
```

### 陷阱 2：Mutex 包裹不需要同步的类型

```rust
// 不必要的 Mutex
let counter = Mutex::new(Cell::new(0)); // Cell 本身不是 Sync

// 正确做法：使用 Atomic 类型
use std::sync::atomic::{AtomicUsize, Ordering};
let counter = AtomicUsize::new(0);
```

### 陷阱 3：在单线程上下文中过度同步

```rust
// 如果确定只在单线程使用，使用 RefCell 而非 Mutex
use std::cell::RefCell;

struct SingleThreadContext {
    data: RefCell<Vec<i32>>, // 运行时借用检查，无锁开销
}
```

---

## 🎮 动手练习

### 练习 1：实现线程池

```rust
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

type Job = Box<dyn FnOnce() + Send + 'static>;

pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<mpsc::Sender<Job>>,
}

struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl ThreadPool {
    pub fn new(size: usize) -> ThreadPool {
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

    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.as_ref().unwrap().send(job).unwrap();
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        drop(self.sender.take());

        for worker in &mut self.workers {
            println!("关闭工作者 {}", worker.id);
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Job>>>) -> Worker {
        let thread = thread::spawn(move || loop {
            let message = receiver.lock().unwrap().recv();

            match message {
                Ok(job) => {
                    println!("工作者 {} 获得任务", id);
                    job();
                }
                Err(_) => {
                    println!("工作者 {} 关闭", id);
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

### 练习 2：读者-写者锁的实现模式

```rust
use std::sync::{Arc, RwLock};
use std::thread;

fn reader_writer_pattern() {
    let cache = Arc::new(RwLock::new(std::collections::HashMap::new()));

    // 多个读者
    let mut readers = vec![];
    for i in 0..5 {
        let cache = Arc::clone(&cache);
        readers.push(thread::spawn(move || {
            let data = cache.read().unwrap();
            println!("读者 {} 读取: {:?}", i, data.get(&"key"));
        }));
    }

    // 一个写者
    let cache_writer = Arc::clone(&cache);
    let writer = thread::spawn(move || {
        let mut data = cache_writer.write().unwrap();
        data.insert("key", "value");
        println!("写者更新缓存");
    });

    for r in readers {
        r.join().unwrap();
    }
    writer.join().unwrap();
}
```

---

## 📖 延伸阅读

### 官方文档

- [The Rust Programming Language - 并发章节](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [std::sync 文档](https://doc.rust-lang.org/std/sync/index.html)
- [Rust By Example - 并发](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html)

### 推荐书籍

- **《Programming Rust》** - Jim Blandy 等著（第 19 章并发详解）
- **《Rust Atomics and Locks》** - Mara Bos 著（深入内存序和原子操作）
- **《Concurrent Programming: Algorithms, Principles, and Foundations》** - 并发理论基础

### 优秀 Crate

- `parking_lot`：更快速、更紧凑的同步原语
- `crossbeam`：高级并发工具，包括 epoch-based 内存管理
- `rayon`：数据并行库，轻松将顺序迭代转为并行
- `tokio::sync`：异步环境下的同步原语

### 相关主题

- [Rust 内存模型与原子操作](./atomics.md)
- [异步编程与并发](./async-concurrency.md)
- [并行迭代器与数据并行](./data-parallelism.md)

---

> 💡 **学习提示**：并发编程需要大量实践。建议从简单的多线程计数器开始，逐步增加复杂度，使用 `cargo test` 和 loom 等工具测试并发正确性。
