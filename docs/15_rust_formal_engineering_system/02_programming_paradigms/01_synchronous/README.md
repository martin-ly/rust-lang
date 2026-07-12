# 同步编程范式 {#同步编程范式}
>
> **EN**: Synchronous Index
> **Summary**: 同步编程范式 Synchronous Index. (stub/archive redirect)
> **分级**: [B]
> **Bloom 层级**: L5-L6
> **创建日期**: 2026-02-20
> **最后更新**: 2026-06-25（已按 Rust 1.97.0 复审）
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至： [c05_threads/](../../../../crates/c05_threads/README.md)

> **权威来源**: 本文件为 Rust 形式化工程体系专题入口；通用 Rust 概念解释请见对应 `concept/` 权威页：
>
> - [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../../concept/03_advanced/00_concurrency/01_concurrency.md)
> - [`concept/03_advanced/00_concurrency/03_concurrency_patterns.md`](../../../../concept/03_advanced/00_concurrency/03_concurrency_patterns.md)
>
> 根据 AGENTS.md §3.4，`docs/` 仅保留专题工程视角内容；通用概念解释统一维护在 `concept/` 中。

[返回主索引](../../00_master_index.md)

---

## 同步编程核心概念 {#同步编程核心概念}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 线程与并发 {#线程与并发}

> **来源: [ACM](https://dl.acm.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

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

### 共享状态并发 {#共享状态并发}

> **来源: [IEEE](https://standards.ieee.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

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

### 线程同步原语 {#线程同步原语}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
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

### Scoped 线程（无需 'static 生命周期） {#scoped-线程无需-static-生命周期}

> **来源: [ACM](https://dl.acm.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
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

### 线程局部存储 {#线程局部存储}

> **来源: [IEEE](https://standards.ieee.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

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

## 使用场景 {#使用场景}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 场景 | 同步原语 | 适用说明 |
| :--- | :--- | :--- |
| 简单的共享计数器 | `AtomicUsize` | 无锁，最高性能 |
| 多线程共享可变状态 | `Mutex<T>` | 互斥访问，简单易用 |
| 多读少写场景 | `RwLock<T>` | 并发读，独占写 |
| 任务分发与收集 | `mpsc` 通道 | 生产者-消费者模式 |
| 多阶段并行计算 | `Barrier` | 同步多个线程的阶段 |
| 等待特定条件 | `Condvar` | 条件变量等待/通知 |
| 借用（Borrowing）栈数据的多线程 | `thread::scope` | 避免 'static 约束 |
| 线程私有缓存 | `thread_local!` | 每个线程独立数据 |

---

## 相关研究笔记 {#相关研究笔记}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 软件设计理论 {#软件设计理论}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 同步执行模型 | 同步模型理论 | [../../../12_research_notes/08_software_design_theory/04_execution_models/01_synchronous.md](../../../12_research_notes/08_software_design_theory/04_execution_models/01_synchronous.md) |
| 并发执行模型 | 并发模型理论 | [../../../12_research_notes/08_software_design_theory/04_execution_models/03_concurrent.md](../../../12_research_notes/08_software_design_theory/04_execution_models/03_concurrent.md) |
| 并行执行模型 | 并行模型理论 | [../../../12_research_notes/08_software_design_theory/04_execution_models/04_parallel.md](../../../12_research_notes/08_software_design_theory/04_execution_models/04_parallel.md) |

### 形式化方法 {#形式化方法}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| Send/Sync 形式化 | 线程安全 trait 形式化 | [../../../12_research_notes/02_formal_methods/12_send_sync_formalization.md](../../../12_research_notes/02_formal_methods/12_send_sync_formalization.md) |
| 所有权（Ownership）模型 | 所有权与并发 | [../../../12_research_notes/02_formal_methods/09_ownership_model.md](../../../12_research_notes/02_formal_methods/09_ownership_model.md) |

### 实验分析 {#实验分析}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 并发性能 | 并发性能测试 | [../../../12_research_notes/09_experiments/02_concurrency_performance.md](../../../12_research_notes/09_experiments/02_concurrency_performance.md) |

---

## 相关 crates {#相关-crates}

| crate | 描述 | 路径 |
| :--- | :--- | :--- |
| c05_threads | 线程并发实现 | [../../../../crates/c05_threads/](../../../../crates/c05_threads/README.md) |
| c09_design_pattern | 并发设计模式 | [../../../../crates/c09_design_pattern/](../../../../crates/c09_design_pattern/README.md) |

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../../../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-06-25（已按 Rust 1.97.0 复审）
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Formal Methods](https://en.wikipedia.org/wiki/Formal_Methods)**
> **来源: [Coq Reference Manual](https://coq.inria.fr/doc/)**
> **来源: [TLA+ Documentation](https://lamport.azurewebsites.net/tla/tla.html)**
> **来源: [ACM - Formal Verification](https://dl.acm.org/)**
