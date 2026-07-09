# 并发速查卡 {#并发速查卡}

> **EN**: Concurrency Cheatsheet
> **Summary**: 并发速查卡 Concurrency Cheatsheet.
>
> **概念族**: 速查卡
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **权威来源**:
>
> [Rust Reference](https://doc.rust-lang.org/reference/) |
> [The Rust Programming Language](https://doc.rust-lang.org/book/) |
> [Rust Standard Library](https://doc.rust-lang.org/std/) |
> [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **创建日期**: 2026-02-10
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级
> **一页纸速查** - 线程、同步原语、并发模式

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [并发速查卡 {#并发速查卡}](#并发速查卡-并发速查卡)
  - [📑 目录 {#目录}](#-目录-目录)
  - [Send（Send）与Sync（Sync） {#send与sync}](#send与sync-send与sync)
  - [同步原语 {#同步原语}](#同步原语-同步原语)
  - [创建线程 {#创建线程}](#创建线程-创建线程)
  - [Send/Sync {#sendsync}](#sendsync-sendsync)
  - [共享状态 {#共享状态}](#共享状态-共享状态)
    - [Mutex {#mutex}](#mutex-mutex)
    - [RwLock {#rwlock}](#rwlock-rwlock)
  - [通道通信 {#通道通信}](#通道通信-通道通信)
    - [mpsc {#mpsc}](#mpsc-mpsc)
    - [多生产者 {#多生产者}](#多生产者-多生产者)
  - [原子操作（Atomic Operations） {#原子操作}](#原子操作-原子操作)
    - [内存序 {#内存序}](#内存序-内存序)
  - [线程同步 {#线程同步}](#线程同步-线程同步)
    - [Barrier {#barrier}](#barrier-barrier)
    - [Condvar {#condvar}](#condvar-condvar)
  - [线程局部存储 {#线程局部存储}](#线程局部存储-线程局部存储)
  - [常见模式 {#常见模式}](#常见模式-常见模式)
    - [线程池 {#线程池}](#线程池-线程池)
    - [并行迭代 {#并行迭代}](#并行迭代-并行迭代)
  - [死锁预防 {#死锁预防}](#死锁预防-死锁预防)
  - [性能检查清单 {#性能检查清单}](#性能检查清单-性能检查清单)
  - [🌍 权威国际化资源链接 {#权威国际化资源链接}](#-权威国际化资源链接-权威国际化资源链接)
    - [Rust Reference 核心章节 {#rust-reference-核心章节}](#rust-reference-核心章节-rust-reference-核心章节)
    - [The Rust Programming Language 核心章节 {#the-rust-programming-language-核心章节}](#the-rust-programming-language-核心章节-the-rust-programming-language-核心章节)
    - [Rust Standard Library 核心 API / 模块（Module） {#rust-standard-library-核心-api-模块}](#rust-standard-library-核心-api--模块-rust-standard-library-核心-api-模块)
    - [Rust By Example / Rust Cookbook / cheats.rs {#rust-by-example-rust-cookbook-cheatsrs}](#rust-by-example--rust-cookbook--cheatsrs-rust-by-example-rust-cookbook-cheatsrs)
    - [并发专属权威链接 {#并发专属权威链接}](#并发专属权威链接-并发专属权威链接)
      - [std::sync / atomics {#stdsync-atomics}](#stdsync--atomics-stdsync-atomics)
      - [Rust By Example / Cookbook / cheats.rs {#rust-by-example-cookbook-cheatsrs}](#rust-by-example--cookbook--cheatsrs-rust-by-example-cookbook-cheatsrs)
      - [Nomicon / RFC / Miri {#nomicon-rfc-miri}](#nomicon--rfc--miri-nomicon-rfc-miri)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

## Send与Sync {#send与sync}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
Send: 可跨线程转移所有权
Sync: 可安全跨线程共享(&T: Send)

T: Send + Sync      T: Send + !Sync    !Send + !Sync
├── i32             ├── Cell<T>        ├── Rc<T>
├── String          ├── RefCell<T>     └── *const T
├── Vec<T>          └── mpsc::Sender
└── Arc<T>(T:Sync)
```

---

## 同步原语 {#同步原语}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 原语 | 用途 | 场景 |
| :--- | :--- | :--- |
| `Mutex<T>` | 互斥访问 | 通用 |
| `RwLock<T>` | 多读单写 | 读多写少 |
| `AtomicUsize` | 原子计数 | 高性能计数 |
| `mpsc::channel` | 消息传递 | 线程通信 |
| `Barrier` | 等待所有线程 | 并行计算 |

---

## 创建线程 {#创建线程}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
use std::thread;

// 基本线程
let handle = thread::spawn(|| {
    println!("Hello from thread!");
});
handle.join().unwrap();

// 带返回值
let handle = thread::spawn(|| {
    42
});
let result = handle.join().unwrap();

// 命名线程
thread::Builder::new()
    .name("worker".into())
    .spawn(|| { /* ... */ });
```

---

## Send/Sync {#sendsync}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 类型 | `Send` | `Sync` | 说明 |
| :--- | :--- | :--- | :--- |
| `i32`, `bool` | ✅ | ✅ | 原始类型 |
| `String`, `Vec<T>` | ✅(T) | ✅(T) | 拥有数据 |
| `Rc<T>` | ❌ | ❌ | 非原子 |
| `Arc<T>` | ✅(T) | ✅(T) | 原子计数 |
| `RefCell<T>` | ✅(T) | ❌ | 内部可变 |
| `Mutex<T>` | ✅(T) | ✅(T) | 提供Sync |
| `Cell<T>` | ✅(T) | ❌ | 内部可变 |

---

## 共享状态 {#共享状态}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### Mutex {#mutex}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
use std::sync::{Arc, Mutex};

let counter = Arc::new(Mutex::new(0));
let counter2 = Arc::clone(&counter);

thread::spawn(move || {
    let mut num = counter2.lock().unwrap();
    *num += 1;
}); // 锁在这里自动释放

let num = counter.lock().unwrap();
println!("{}", *num);
```

### RwLock {#rwlock}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
use std::sync::RwLock;

let data = RwLock::new(5);

// 多个读
let r1 = data.read().unwrap();
let r2 = data.read().unwrap();

// 单写(阻塞读)
{
    let mut w = data.write().unwrap();
    *w += 1;
}
```

---

## 通道通信 {#通道通信}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### mpsc {#mpsc}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
use std::sync::mpsc;
use std::thread;

let (tx, rx) = mpsc::channel();

thread::spawn(move || {
    tx.send(42).unwrap();
});

let received = rx.recv().unwrap();
println!("{}", received);

// 迭代接收
for received in rx {
    println!("{}", received);
}
```

### 多生产者 {#多生产者}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
let (tx, rx) = mpsc::channel();

for i in 0..3 {
    let tx = tx.clone();
    thread::spawn(move || {
        tx.send(i).unwrap();
    });
}
drop(tx); // 关闭所有发送者

for received in rx {
    println!("{}", received);
}
```

---

## 原子操作 {#原子操作}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
use std::sync::atomic::{AtomicUsize, Ordering};

let counter = AtomicUsize::new(0);

// 读
counter.load(Ordering::Relaxed);

// 写
counter.store(42, Ordering::Relaxed);

// 读-修改-写
counter.fetch_add(1, Ordering::Relaxed);
counter.fetch_sub(1, Ordering::SeqCst);

// CAS
counter.compare_exchange(
    current,    // 期望值
    new,        // 新值
    Ordering::Acquire,
    Ordering::Relaxed,
);
```

### 内存序 {#内存序}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

| 顺序 | 保证 | 性能 |
| :--- | :--- | :--- |
| `Relaxed` | 无 | 最高 |
| `Acquire`/`Release` | 同步 | 高 |
| `AcqRel` | 两者 | 高 |
| `SeqCst` | 全局顺序 | 较低 |

---

## 线程同步 {#线程同步}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### Barrier {#barrier}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

```rust,ignore
use std::sync::Barrier;

let barrier = Arc::new(Barrier::new(3));

for _ in 0..3 {
    let b = Arc::clone(&barrier);
    thread::spawn(move || {
        // 工作
        b.wait(); // 等待所有线程
        // 继续
    });
}
```

### Condvar {#condvar}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

```rust,ignore
use std::sync::{Arc, Condvar, Mutex};

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
```

---

## 线程局部存储 {#线程局部存储}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust
use std::cell::Cell;
use std::thread;

thread_local! {
    static COUNTER: Cell<u32> = Cell::new(0);
}

COUNTER.with(|c| {
    c.set(c.get() + 1);
});
```

---

## 常见模式 {#常见模式}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 线程池 {#线程池}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

```rust,ignore
use threadpool::ThreadPool;

let pool = ThreadPool::new(4);

for i in 0..8 {
    pool.execute(move || {
        println!("Task {}", i);
    });
}

pool.join();
```

### 并行迭代 {#并行迭代}

> **来源: [ACM](https://dl.acm.org/)**

```rust,ignore
use rayon::prelude::*;

let sum: i32 = (0..100).into_par_iter().sum();

let mut vec = vec![1, 2, 3, 4, 5];
vec.par_iter_mut().for_each(|x| *x *= 2);
```

---

## 死锁预防 {#死锁预防}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
□ 统一的锁获取顺序
□ 使用try_lock()避免阻塞
□ 锁的持有时间最小化
□ 考虑使用lock_bud检测
□ 优先使用通道而非共享状态
```

---

## 性能检查清单 {#性能检查清单}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```text
□ 减少锁竞争(细粒度锁)
□ 使用读多写少用RwLock
□ 考虑无锁数据结构
□ 使用线程池避免创建开销
□ 批处理减少同步
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 🌍 权威国际化资源链接 {#权威国际化资源链接}
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)**
> **来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)**
> **来源: [cheats.rs](https://cheats.rs/)**

本节为速查内容提供官方权威来源与社区经典参考的直通链接，便于深入验证与扩展阅读。

### Rust Reference 核心章节 {#rust-reference-核心章节}

- [Reference 首页](https://doc.rust-lang.org/reference/)
- [Types](https://doc.rust-lang.org/reference/types.html)
- [Items / Traits](https://doc.rust-lang.org/reference/items/traits.html)
- [Expressions](https://doc.rust-lang.org/reference/expressions.html)
- [Statements](https://doc.rust-lang.org/reference/statements.html)
- [Crates and Source Files](https://doc.rust-lang.org/reference/crates-and-source-files.html)

### The Rust Programming Language 核心章节 {#the-rust-programming-language-核心章节}

- [TRPL 首页](https://doc.rust-lang.org/book/)
- [Ch. 4 - Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Ch. 9 - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [Ch. 10 - Generic Types, Traits, Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [Ch. 13 - Closures](https://doc.rust-lang.org/book/ch13-00-functional-features.html)
- [Ch. 15 - Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)
- [Ch. 16 - Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Ch. 19 - Advanced Features / Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)

### Rust Standard Library 核心 API / 模块 {#rust-standard-library-核心-api-模块}

- [std 首页](https://doc.rust-lang.org/std/)
- [std::result](https://doc.rust-lang.org/std/result/)
- [std::option](https://doc.rust-lang.org/std/option/)
- [std::error::Error](https://doc.rust-lang.org/std/error/trait.Error.html)
- [std::fmt](https://doc.rust-lang.org/std/fmt/)
- [std::panic](https://doc.rust-lang.org/std/panic/)
- [std::marker (Send / Sync / PhantomData)](https://doc.rust-lang.org/std/marker/)

### Rust By Example / Rust Cookbook / cheats.rs {#rust-by-example-rust-cookbook-cheatsrs}

- [Rust By Example 首页](https://doc.rust-lang.org/rust-by-example/)
- [Rust Cookbook 首页](https://rust-lang-nursery.github.io/rust-cookbook/)
- [cheats.rs 首页](https://cheats.rs/)

---

### 并发专属权威链接 {#并发专属权威链接}

> **来源: [Rustonomicon - Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html)**
> **来源: [Rust Reference - Memory Model](https://doc.rust-lang.org/reference/memory-model.html)**

#### std::sync / atomics {#stdsync-atomics}

- [std::sync](https://doc.rust-lang.org/std/sync/)
- [std::sync::atomic](https://doc.rust-lang.org/std/sync/atomic/)
- [std::sync::Mutex](https://doc.rust-lang.org/std/sync/struct.Mutex.html)
- [std::sync::RwLock](https://doc.rust-lang.org/std/sync/struct.RwLock.html)
- [std::sync::Arc](https://doc.rust-lang.org/std/sync/struct.Arc.html)
- [std::sync::Barrier](https://doc.rust-lang.org/std/sync/struct.Barrier.html)
- [std::sync::Condvar](https://doc.rust-lang.org/std/sync/struct.Condvar.html)
- [std::thread](https://doc.rust-lang.org/std/thread/)
- [std::thread::LocalKey](https://doc.rust-lang.org/std/thread/struct.LocalKey.html)
- [AtomicUsize](https://doc.rust-lang.org/std/sync/atomic/type.AtomicUsize.html)
- [Ordering](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html)

#### Rust By Example / Cookbook / cheats.rs {#rust-by-example-cookbook-cheatsrs}

- [RBE - Threads](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html)
- [RBE - Channel](https://doc.rust-lang.org/rust-by-example/std_misc/channels.html)
- [RBE - Atomics](https://doc.rust-lang.org/std/sync/atomic/)
- [Rust Cookbook - Concurrency](https://rust-lang-nursery.github.io/rust-cookbook/concurrency.html)
- [cheats.rs - Concurrency](https://cheats.rs/#concurrency)

#### Nomicon / RFC / Miri {#nomicon-rfc-miri}

- [Rustonomicon - Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html)
- [Rustonomicon - Atomics](https://doc.rust-lang.org/nomicon/atomics.html)
- [RFC 0458 - Send trait improvements](https://rust-lang.github.io/rfcs/0458-send-improvements.html)
- [RFC 1543 - Integer atomics](https://rust-lang.github.io/rfcs/1543-integer_atomics.html)
- [Miri - Undefined Behavior detection](https://github.com/rust-lang/miri)
- [Miri README](https://github.com/rust-lang/miri/blob/master/README.md)
- [RFC 2394 - async/await](https://rust-lang.github.io/rfcs/2394-async_await.html)
- [RFC 3151 - Scoped threads](https://rust-lang.github.io/rfcs/3151-scoped-threads.html)

## 相关概念 {#相关概念}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**
> **来源: [TRPL Ch. 16 - Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)**
> **来源: [Rust Reference - std::sync](https://doc.rust-lang.org/std/sync/)**
> **来源: [ACM - Concurrent Programming](https://dl.acm.org/)**

---

## 社区权威参考 {#社区权威参考}

- [This Week in Rust](https://this-week-in-rust.org/)
- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ -->
