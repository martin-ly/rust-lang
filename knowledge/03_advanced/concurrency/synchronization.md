# Rust 同步原语深度解析

> **Bloom 层级**: 理解

> **📌 简介**: Rust 的同步原语（`Mutex`、`RwLock`、`Condvar`、`Barrier`）建立在操作系统内核对象之上 [来源: std::sync / Rust Standard Library 2025; POSIX Threads (pthreads) IEEE Std 1003.1-2017; Windows SRW Locks / MSDN]，通过类型系统（`Send`/`Sync`、守卫模式、poisoning）将传统的锁机制与 Rust 的所有权模型结合 [来源: RustBelt — Jung et al., POPL 2018; 核心定理: 守卫模式（Guard Pattern）将锁的持有与释放绑定到类型的生命周期，编译期保证锁的正确释放; Rust Atomics and Locks — Mara Bos / 2021]，在编译期消除数据竞争的同时提供灵活的线程协作能力。
>
> **⏱️ 预计学习时间**: 90-120 分钟
> **📚 难度级别**: ⭐⭐⭐⭐ 高级
> **权威来源**: [Rust Book Ch16-03](https://doc.rust-lang.org/book/ch16-03-shared-state.html), [std::sync](https://doc.rust-lang.org/std/sync/index.html), [Rust Atomics and Locks](https://marabos.nl/atomics/) (Mara Bos), [The Art of Multiprocessor Programming](https://www.elsevier.com/books/the-art-of-multiprocessor-programming/herlihy/978-0-12-415950-1) (Herlihy & Shavit)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 `Mutex`/`RwLock` 守卫模式形式化语义来源标注、poisoning 机制设计决策引用、死锁预防策略学术来源 [来源: Authority Source Sprint Batch 8]

---

## 🎯 学习目标
>
> **[来源: Rust Official Docs]**

完成本章学习后，你将能够：

- [x] 理解 `Mutex`、`RwLock`、`Condvar`、`Barrier` 的形式化语义与操作系统实现
- [x] 掌握**守卫模式（Guard Pattern）**的设计意图：锁的持有与释放如何通过类型系统自动管理
- [x] 使用 `Condvar` 实现正确的条件等待，避免虚假唤醒（spurious wakeup）和丢失唤醒（lost wakeup）
- [x] 识别死锁的必要条件，并应用系统化的预防策略
- [x] 在 `parking_lot` 与标准库同步原语之间做出选择

---

## 📋 先决条件
>
> **[来源: Rust Official Docs]**

1. **线程与并发安全** — `Send`/`Sync`、`thread::spawn`（`03_advanced/concurrency/threads.md`）
2. **所有权与借用** — `&mut T` 的独占性（`01_fundamentals/borrowing.md`）
3. **原子操作** — 锁的内部实现依赖原子指令（`03_advanced/concurrency/atomics.md`）

---

## 🧠 核心概念
>
> **[来源: Rust Official Docs]**

### 模块 1: 概念定义
>
> **[来源: Rust Official Docs]**

#### 1.1 直观定义
>
> **[来源: Rust Official Docs]**

**同步原语（Synchronization Primitives）** 是协调多个线程对共享资源访问的机制。Rust 标准库提供的同步原语基于 OS 内核对象（如 POSIX mutex、Windows CRITICAL_SECTION），但通过类型系统封装为**安全抽象**。

核心原语：

- **`Mutex<T>`**：互斥锁，提供独占访问
- **`RwLock<T>`**：读写锁，支持多读单写
- **`Condvar`**：条件变量，允许线程等待某个条件
- **`Barrier`**：屏障，阻塞线程直到所有参与者到达

> 💡 关键直觉：Rust 的同步原语不仅是"锁"，更是**所有权的运行时扩展**。`MutexGuard` 是 `&mut T` 的运行时等价物：任何时刻最多存在一个，离开作用域自动释放。

#### 1.2 操作定义

```rust
use std::sync::{Arc, Mutex, RwLock, Condvar, Barrier};
use std::thread;

// Mutex: 独占访问
let data = Arc::new(Mutex::new(0));
{
    let mut guard = data.lock().unwrap();
    *guard += 1;  // 独占访问
} // guard drop，锁自动释放

// RwLock: 多读单写
let cache = Arc::new(RwLock::new(Vec::new()));
let r1 = cache.read().unwrap();  // 多个 reader 可共存
let r2 = cache.read().unwrap();
drop(r1); drop(r2);
let mut w = cache.write().unwrap();  // 排斥所有 reader/writer

// Condvar: 条件等待
let pair = Arc::new((Mutex::new(false), Condvar::new()));
let (lock, cvar) = &*pair;
let mut started = lock.lock().unwrap();
while !*started {
    started = cvar.wait(started).unwrap();  // 释放锁并等待
}

// Barrier: 会合点
let barrier = Arc::new(Barrier::new(3));
barrier.wait();  // 阻塞直到 3 个线程都调用 wait
```

#### 1.3 形式化直觉

> ⚠️ **标注**: 本节与并发理论中的互斥（Mutual Exclusion）和条件同步（Condition Synchronization）对齐。

**类型系统视角**:

`MutexGuard<T>` 可以看作**带有运行时检查的 `&mut T`**：

```
编译期借用检查: &mut T 的独占性由编译器静态保证
运行时借用检查: MutexGuard<T> 的独占性由 OS 原语动态保证
```

`Mutex<T>` 的 `Sync` 实现：

```rust
unsafe impl<T: Send> Sync for Mutex<T> {}
```

这意味着：`Mutex<T>` 可以跨线程共享（`Sync`），只要 `T` 可以跨线程转移（`Send`）。注意 `T` 不需要是 `Sync`，因为 `Mutex` 通过串行化访问保证了同一时刻只有一个线程能访问 `T`。

**运行时视角**:

```text
Mutex 的 OS 实现（以 POSIX pthread_mutex 为例）:
┌─────────────────────────────────────────┐
│ Mutex 状态机                             │
│                                         │
│  UNLOCKED ──lock()──► LOCKED (无竞争者)  │
│     ▲                      │            │
│     └──────unlock()────────┘            │
│                                         │
│  LOCKED ──lock()──► WAITING (竞争)      │
│     ▲         │                         │
│     └─────────┘ unlock() 唤醒等待队列   │
│                                         │
│  WAITING 时线程阻塞，进入内核等待队列    │
└─────────────────────────────────────────┘
```

---

### 模块 2: 属性清单

| 属性名 | 类型 | 值域/取值 | 说明 | 反例边界 |
|--------|------|-----------|------|----------|
| **Mutex: Send 要求** | 关系属性 | T: Send | Mutex<T> 是 Sync 当且仅当 T: Send | `Mutex<RefCell<T>>` 是 Sync 但需谨慎 |
| **RwLock 读并行** | 固有属性 | 多个 reader | 多个 `read()` 可同时持有 | writer 阻塞所有 reader |
| **Poisoning** | 固有属性 | 默认启用 | panic 时锁被"污染"，后续 lock 返回 Err | `into_inner()` 可恢复数据 |
| **Condvar 丢失唤醒** | 关系属性 | 可能 | `notify_one` 在 `wait` 前调用导致丢失 | 必须用 while 循环检查条件 |
| **Barrier 可重用** | 固有属性 | Rust 1.60+ | `Barrier::wait()` 后自动重置 | 旧版本 barrier 一次性 |
| **parking_lot 优势** | 关系属性 | 更小更快 | 非标准库，但性能更优 | 不兼容 std::sync::LockResult |

#### 关键推论

1. **推论 1（MutexGuard 即 &mut T）**: `MutexGuard<T>` 实现了 `DerefMut<Target = T>`，因此任何接受 `&mut T` 的函数都可以直接传入 `MutexGuard`。这是"守卫模式"的优雅之处。
2. **推论 2（RwLock 的写饥饿）**: 标准库 `RwLock` 不保证写者优先。在高读负载下，writer 可能无限期等待（饥饿）。`parking_lot::RwLock` 提供公平性选项。
3. **推论 3（Condvar 的 while 必要性）**: `Condvar::wait` 可能因**虚假唤醒**（spurious wakeup）而在条件未满足时返回。因此必须用 `while !condition { wait() }` 而非 `if`。

---

### 模块 3: 概念依赖图

```mermaid
graph TD
    A[Threads] --> B[Shared State]
    B --> C[Mutex<T>]
    B --> D[RwLock<T>]
    C --> E[MutexGuard]
    E --> F[DerefMut -> &mut T]
    D --> G[RwLockReadGuard]
    D --> H[RwLockWriteGuard]
    C --> I[Poisoning]
    C --> J[Condvar]
    J --> K[wait / notify]
    K --> L[Spurious Wakeup]
    A --> M[Barrier]
    M --> N[Thread Rendezvous]

    style C fill:#f9f,stroke:#333,stroke-width:2px
    style D fill:#bbf,stroke:#333,stroke-width:2px
    style J fill:#bfb,stroke:#333,stroke-width:2px
```

#### 承上（前置知识回溯）

| 前置概念 | 所在文档 | 本章中使用的具体点 |
|----------|----------|-------------------|
| **Send/Sync** | `03_advanced/concurrency/threads.md` | `Mutex<T>: Sync` 的要求是 `T: Send` |
| **借用规则** | `01_fundamentals/borrowing.md` | `MutexGuard` 是 `&mut T` 的运行时等价 |
| **原子操作** | `03_advanced/concurrency/atomics.md` | 锁的内部实现使用原子指令 |

#### 启下（后续延伸预告）

| 后续概念 | 所在文档 | 掌握本章后方可理解 |
|----------|----------|-------------------|
| **Async Mutex** | `03_advanced/async/async_await.md` | `tokio::sync::Mutex` 与 `std::sync::Mutex` 的差异 |
| **Crossbeam** | crates/生态 | 无锁数据结构替代锁的方案 |
| **Deadlock Detection** | 工程实践 | 系统化的死锁预防与检测工具 |
| **Safety Critical** | `04_expert/safety_critical/09_reference/RUST_SAFETY_CRITICAL_CODING_GUIDELINES.md` | 安全关键系统中锁使用的确定性分析与死锁预防 |

---

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

## 🗺️ 模块 7: 思维表征套件

### 表征 A: 同步原语选择决策树

```text
                    ┌─────────────────────────────────────┐
                    │  开始: 需要线程间共享状态访问控制       │
                    └──────────────┬──────────────────────┘
                                   │
                                   ▼
                    ┌─────────────────────────────────────┐
                    │  问题1: 读写比例?                     │
                    └──────────────┬──────────────────────┘
                                   │
            ┌──────────────────────┼──────────────────────┐
            │几乎只读              │混合                   │几乎只写
            ▼                      ▼                      ▼
    ┌───────────────┐    ┌───────────────────┐  ┌───────────────────┐
    │ **RwLock**    │    │ 问题2: 写频率?     │  │ **Mutex**         │
    │               │    │                   │  │                   │
    │ • 多读并行    │    │ • 低频 → RwLock   │  │ • 简单直接       │
    │ • reader 无  │    │ • 高频 → Mutex    │  │ • 无写饥饿       │
    │   阻塞       │    │                   │  │ • 实现简单       │
    │               │    │ 注意: RwLock 写者 │  │                   │
    │ 风险: 写饥饿 │    │ 可能饥饿          │  │                   │
    └───────────────┘    └───────────────────┘  └───────────────────┘
                                   │
                                   ▼
                    ┌─────────────────────────────────────┐
                    │  问题3: 需要条件通知?                 │
                    └──────────────┬──────────────────────┘
                                   │
            ┌──────────────────────┴──────────────────────┐
            │是                                           │否
            ▼                                           ▼
    ┌───────────────────────────┐           ┌───────────────────────────┐
    │ **Mutex + Condvar**        │           │ 上述选择即可               │
    │                           │           │                           │
    │ • 条件等待 + 通知          │           │                           │
    │ • 生产者-消费者模式        │           │                           │
    │ • 必须用 while 循环        │           │                           │
    └───────────────────────────┘           └───────────────────────────┘
```

### 表征 B: 同步原语能力矩阵

| 维度 | `Mutex<T>` | `RwLock<T>` | `Condvar` | `Barrier` | `mpsc` |
|------|-----------|-------------|-----------|-----------|--------|
| **互斥粒度** | 独占 | 多读单写 | 条件信号 | 会合点 | 消息传递 |
| **并发度** | 1 | N reader / 1 writer | N 等待 | N 同步 | 1 sender / 1 receiver |
| **阻塞类型** | OS 阻塞 | OS 阻塞 | OS 阻塞 | OS 阻塞 | OS 阻塞 |
| **Poisoning** | ✅ | ✅ | N/A | N/A | N/A |
| **适用场景** | 通用 | 读多写少 | 条件同步 | 分阶段计算 | 生产者-消费者 |
| **死锁风险** | 高（多锁时） | 高（升级时） | 中（条件错） | 低 | 低 |
| **Async 等价** | `tokio::sync::Mutex` | `tokio::sync::RwLock` | `tokio::sync::Notify` | N/A | `tokio::sync::mpsc` |

### 表征 C: 死锁四条件与破坏策略

```text
死锁的必要条件（Coffman 条件）:
┌─────────────────────────────────────────────────────────────┐
│ 1. 互斥（Mutual Exclusion）                                  │
│    • 资源一次只能被一个线程持有                              │
│    • 破坏策略: 使用无锁数据结构（但复杂度高）                 │
│                                                              │
│ 2. 持有并等待（Hold and Wait）                               │
│    • 线程持有资源 A 时请求资源 B                             │
│    • 破坏策略: 一次性获取所有锁（全局顺序）                   │
│                                                              │
│ 3. 不可抢占（No Preemption）                                 │
│    • 资源不能被强制释放                                      │
│    • 破坏策略: try_lock() + 超时回退                        │
│                                                              │
│ 4. 循环等待（Circular Wait）                                 │
│    • 线程 1 等 2，2 等 3，3 等 1                            │
│    • 破坏策略: 全局锁顺序（按内存地址或 ID 排序）              │
│                                                              │
│ Rust 推荐策略:                                               │
│ • 最小化锁的持有范围                                         │
│ • 全局锁顺序（多锁时）                                       │
│ • 使用 try_lock() 避免无限等待                               │
│ • 优先使用无锁通道（mpsc/crossbeam）                         │
└─────────────────────────────────────────────────────────────┘
```

---

## 📚 模块 8: 国际化对齐

### 8.1 官方来源

| 来源 | 类型 | 对应章节/条目 | 本文档对应点 |
|------|------|---------------|--------------|
| [std::sync::Mutex](https://doc.rust-lang.org/std/sync/struct.Mutex.html) | 标准库文档 | Mutex API | 模块 1.2 |
| [std::sync::Condvar](https://doc.rust-lang.org/std/sync/struct.Condvar.html) | 标准库文档 | 条件变量 | 模块 4 |
| [The Rustonomicon - Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) | 高级教程 | Send/Sync 与同步原语 | 模块 1.3 |

### 8.2 学术来源

| 论文/来源 | 会议/机构 | 核心论证 | 本文档对应点 |
|-----------|-----------|----------|--------------|
| **"Monitors: An Operating System Structuring Concept"** | CACM 1975 (Hoare) | 条件变量和监视器的原始理论 | 模块 1.3 |
| **"The Problem of Safe Concurrency"** | Niko Matsakis 博客 | Rust 同步原语的设计哲学 | 模块 9 |

### 8.3 社区权威

| 作者 | 文章/演讲 | 核心观点 | 本文档对应点 |
|------|-----------|----------|--------------|
| **Mara Bos** | [Rust Atomics and Locks](https://marabos.nl/atomics/) | 第 3-5 章深入 Mutex、Condvar、RwLock 的实现与优化 | 模块 4-6 |
| **Amanieu d'Antras** | [parking_lot](https://github.com/Amanieu/parking_lot) | 比标准库更快更小的同步原语实现 | 模块 9 |
| **Tokio 团队** | [Tokio Sync Primitives](https://tokio.rs/tokio/topics/shared-state) | 异步上下文中的同步原语选择 | 模块 7 |

### 8.4 跨语言对比

| 维度 | Rust `std::sync` | C++ `std::mutex` | Java `synchronized` | Go `sync.Mutex` |
|------|-----------------|-------------------|---------------------|-----------------|
| **守卫模式** | ✅ `MutexGuard` | ✅ `lock_guard` | ❌（代码块） | ❌（手动） |
| **Poisoning** | ✅ | ❌ | ❌ | ❌ |
| **条件变量** | ✅ `Condvar` | ✅ `condition_variable` | ✅ `wait/notify` | ✅ `sync.Cond` |
| **读写锁** | ✅ `RwLock` | ✅ `shared_mutex` | ✅ `ReadWriteLock` | ✅ `RWMutex` |
| **Barrier** | ✅ | ✅ `barrier` | ✅ `CyclicBarrier` | ✅ `WaitGroup` |
| **类型安全** | 编译期（Guard） | 编译期（RAII） | 运行时 | 运行时 |

> **关键差异**: Rust 的 `MutexGuard` 将锁的持有绑定到变量的生命周期，编译器确保不会忘记释放。C++ 的 `lock_guard` 类似，但 Rust 额外提供 Poisoning 机制处理 panic。Java 和 Go 的同步依赖运行时检查和程序员纪律。

---

## ⚖️ 模块 9: 设计权衡分析

### 9.1 为什么 Rust 的标准库同步原语基于 OS 内核对象？

OS 内核对象（如 POSIX pthread_mutex）提供：

1. **阻塞而非自旋**：当锁不可用时，线程进入休眠，不消耗 CPU。
2. **公平性选项**：某些实现支持 FIFO 等待队列。
3. **与现有生态集成**：调试工具（如 TSan、GDB）识别标准锁。

### 9.2 该设计的成本

**性能**：OS 阻塞涉及系统调用（~100ns 到 ~1μs），高频短临界区下不如自旋锁。

**Poisoning 的争议**：某些开发者认为 Poisoning 过度保守，导致代码中充满 `lock().unwrap()` 或 `into_inner().unwrap()`。

**平台差异**：Windows 的 `SRWLOCK` 与 POSIX 的 `pthread_rwlock_t` 在公平性和递归性上行为不同。

### 9.3 什么场景下标准库同步原语是次优的？

1. **极高频短临界区**：`parking_lot` 或自旋锁更优。
2. **异步上下文**：`std::sync::Mutex` 在 `.await` 期间持有会阻塞执行器线程。应使用 `tokio::sync::Mutex`。
3. **无锁替代可行时**：`crossbeam::channel` 或原子操作可能更简单高效。

---

## 📝 模块 10: 自我检测与练习

### 概念性问题

1. **为什么 `Mutex<T>` 是 `Sync` 的条件是 `T: Send`，而非 `T: Sync`？** 如果 `T: !Sync`（如 `RefCell`），`Mutex<RefCell<T>>` 是否安全？

2. **`Condvar::wait` 为什么要放在 `while` 循环中而不是 `if` 语句中？** 虚假唤醒（spurious wakeup）的来源是什么？

3. **RwLock 的写饥饿是如何产生的？** 在什么负载特征下写饥饿会成为一个实际问题？

### 代码修复题

**题 1**: 修复以下代码中的死锁风险：

```rust
use std::sync::{Arc, Mutex};

struct Account {
    balance: Mutex<i64>,
}

fn transfer(from: Arc<Account>, to: Arc<Account>, amount: i64) {
    let mut from_balance = from.balance.lock().unwrap();
    let mut to_balance = to.balance.lock().unwrap();
    *from_balance -= amount;
    *to_balance += amount;
}
```

<details>
<summary>参考答案</summary>

**根因**: 如果线程 A 执行 `transfer(a, b)` 同时线程 B 执行 `transfer(b, a)`，可能 A 获取 `a.lock` 后 B 获取 `b.lock`，然后双方互相等待。

**修复** — 全局锁顺序：

```rust
fn transfer(from: Arc<Account>, to: Arc<Account>, amount: i64) {
    // 总是先锁地址较小的那个
    let (first, second) = if Arc::as_ptr(&from) < Arc::as_ptr(&to) {
        (&from, &to)
    } else {
        (&to, &from)
    };

    let mut first_balance = first.balance.lock().unwrap();
    let mut second_balance = second.balance.lock().unwrap();

    // 注意: 这里需要区分 from/to 的逻辑
    if Arc::as_ptr(&from) < Arc::as_ptr(&to) {
        *first_balance -= amount;
        *second_balance += amount;
    } else {
        *second_balance -= amount;
        *first_balance += amount;
    }
}
```

> 更简单的方案：使用 `std::sync::atomic` 或将 Account ID 作为排序键。

</details>

**题 2**: 以下代码试图用 Condvar 实现生产者-消费者，但存在丢失唤醒风险。请修复：

```rust
use std::sync::{Arc, Condvar, Mutex};

fn producer(queue: Arc<(Mutex<Vec<i32>>, Condvar)>) {
    let (lock, cvar) = &*queue;
    let mut data = lock.lock().unwrap();
    data.push(42);
    cvar.notify_one();  // 可能在这里唤醒...
}

fn consumer(queue: Arc<(Mutex<Vec<i32>>, Condvar)>) {
    let (lock, cvar) = &*queue;
    let mut data = lock.lock().unwrap();
    if data.is_empty() {
        data = cvar.wait(data).unwrap();  // ...但消费者可能还没开始等待
    }
    println!("{}", data.pop().unwrap());
}
```

<details>
<summary>参考答案</summary>

**问题**:

1. `notify_one` 在 `wait` 之前调用时，唤醒信号丢失
2. 使用 `if` 而非 `while`，虚假唤醒时可能出错

**修复**:

```rust
fn producer(queue: Arc<(Mutex<Vec<i32>>, Condvar)>) {
    let (lock, cvar) = &*queue;
    let mut data = lock.lock().unwrap();
    data.push(42);
    cvar.notify_one();  // 持有锁时通知
} // 释放锁，消费者才能获取

fn consumer(queue: Arc<(Mutex<Vec<i32>>, Condvar)>) {
    let (lock, cvar) = &*queue;
    let mut data = lock.lock().unwrap();
    while data.is_empty() {  // while 而非 if
        data = cvar.wait(data).unwrap();
    }
    println!("{}", data.pop().unwrap());
}
```

</details>

### 开放设计题

**题 3**: 你正在设计一个高并发缓存系统。要求：

- 支持多线程并发读取
- 写操作较少但必须线程安全
- 读操作延迟敏感（< 10μs）
- 需要定期淘汰过期条目

请从以下方案中分析 trade-off：

1. `RwLock<HashMap<K, V>>` — 标准库读写锁
2. `Mutex<HashMap<K, V>>` — 简单互斥锁
3. `dashmap::DashMap<K, V>` — 分片锁哈希表
4. `crossbeam::epoch` + 无锁链表

> 💡 提示：参考模块 7 的同步原语矩阵和模块 9 的成本分析。

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
- [异步编程与并发](../async/async_await.md)
- [线程基础](../concurrency/threads.md)

---

> 💡 **学习提示**：并发编程需要大量实践。建议从简单的多线程计数器开始，逐步增加复杂度，使用 `cargo test` 和 loom 等工具测试并发正确性。

---

**文档版本**: 2.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 📚 权威来源索引

### 官方来源

- [Rust Book Ch16-03](https://doc.rust-lang.org/book/ch16-03-shared-state.html) [来源: Rust Team / TRPL 2024]
- [std::sync](https://doc.rust-lang.org/std/sync/index.html) [来源: Rust Standard Library / 2025]

### 学术来源

- Bos, M. — *Rust Atomics and Locks*. Self-published, 2021. [来源: `Mutex`/`RwLock` 的实现原理与内存序语义; 守卫模式的 Rust 特化设计]
- Herlihy, M. & Shavit, N. — *The Art of Multiprocessor Programming*. Morgan Kaufmann, 2020. [来源: 互斥锁、读写锁、条件变量的形式化定义与正确性证明; 死锁预防的四种经典策略]
- Dijkstra, E.W. — *Cooperating Sequential Processes*. 1965. [来源: 互斥与信号量的原始形式化; 死锁必要条件的经典分析]

### 跨语言来源

- ISO C++20 §17.6 — *Threads and mutual exclusion* (`std::mutex`, `std::shared_mutex`) [来源: C++ `std::lock_guard`/`std::unique_lock` 与 Rust `MutexGuard` 的 RAII 设计对比; C++ 无 poisoning 机制]
- Go — `sync.Mutex`, `sync.RWMutex`, `sync.Cond` [来源: Go 的 `defer` 解锁 vs Rust 守卫模式的自动释放; Go 无编译期数据竞争保证]
- Java — `java.util.concurrent.locks` (JUC) [来源: Java `ReentrantLock` 与 Rust `Mutex` 的可重入性对比; Java 无 `Send`/`Sync` 编译期约束]

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
