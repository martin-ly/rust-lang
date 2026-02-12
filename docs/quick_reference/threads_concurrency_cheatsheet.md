# 🔀 Rust 线程与并发速查卡

> **快速参考** | [完整文档](../../crates/c05_threads/docs/) | [代码示例](../../crates/c05_threads/examples/)
> **最后更新**: 2026-01-27 | **Rust 版本**: 1.93.0+ | **Edition**: 2024

---

## 📋 目录

- [🔀 Rust 线程与并发速查卡](#-rust-线程与并发速查卡)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [线程创建](#线程创建)
    - [作用域线程 (Rust 1.93.0+)](#作用域线程-rust-1930)
  - [📐 同步原语](#-同步原语)
    - [Mutex](#mutex)
    - [RwLock](#rwlock)
    - [Arc (原子引用计数)](#arc-原子引用计数)
  - [🎯 消息传递](#-消息传递)
    - [Channel](#channel)
    - [多生产者](#多生产者)
  - [🔧 无锁数据结构](#-无锁数据结构)
    - [Atomic 类型](#atomic-类型)
    - [内存顺序](#内存顺序)
  - [🚫 反例速查](#-反例速查)
    - [反例 1: 将非 Send 类型传入 spawn](#反例-1-将非-send-类型传入-spawn)
    - [反例 2: 死锁 - 重复获取同一 Mutex](#反例-2-死锁---重复获取同一-mutex)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码](#-相关示例代码)
  - [🔗 相关资源](#-相关资源)
  - [🆕 Rust 1.93.0 并发改进](#-rust-1930-并发改进)
    - [内存分配优化](#内存分配优化)
  - [📚 相关资源](#-相关资源-1)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [相关速查卡](#相关速查卡)

---

## 🎯 核心概念

### 线程创建

```rust
use std::thread;

// 基本线程创建
let handle = thread::spawn(|| {
    println!("在新线程中执行");
});

handle.join().unwrap();
```

### 作用域线程 (Rust 1.93.0+)

```rust
use std::thread;

let data = vec![1, 2, 3];

thread::scope(|s| {
    s.spawn(|| {
        println!("数据: {:?}", data);  // 可以借用外部数据
    });
});  // 自动等待所有线程完成
```

---

## 📐 同步原语

### Mutex

```rust
use std::sync::Mutex;

let m = Mutex::new(5);

{
    let mut num = m.lock().unwrap();
    *num = 6;
}  // 锁自动释放
```

### RwLock

```rust
use std::sync::RwLock;

let lock = RwLock::new(5);

// 多个读锁
{
    let r1 = lock.read().unwrap();
    let r2 = lock.read().unwrap();
}

// 单个写锁
{
    let mut w = lock.write().unwrap();
    *w += 1;
}
```

### Arc (原子引用计数)

```rust
use std::sync::Arc;
use std::thread;

let data = Arc::new(vec![1, 2, 3]);

for i in 0..3 {
    let data = Arc::clone(&data);
    thread::spawn(move || {
        println!("线程 {}: {:?}", i, data);
    });
}
```

---

## 🎯 消息传递

### Channel

```rust
use std::sync::mpsc;

let (tx, rx) = mpsc::channel();

thread::spawn(move || {
    tx.send("消息").unwrap();
});

let received = rx.recv().unwrap();
```

### 多生产者

```rust
use std::sync::mpsc;

let (tx, rx) = mpsc::channel();
let tx1 = tx.clone();

thread::spawn(move || {
    tx.send("消息1").unwrap();
});

thread::spawn(move || {
    tx1.send("消息2").unwrap();
});

for received in rx {
    println!("收到: {}", received);
}
```

---

## 🔧 无锁数据结构

### Atomic 类型

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

let counter = AtomicUsize::new(0);

counter.fetch_add(1, Ordering::SeqCst);
let value = counter.load(Ordering::SeqCst);
```

### 内存顺序

```rust
use std::sync::atomic::Ordering;

// 顺序一致性（最强）
Ordering::SeqCst

// 获取-释放
Ordering::Acquire
Ordering::Release
Ordering::AcqRel

// 宽松（最弱）
Ordering::Relaxed
```

---

## 🚫 反例速查

### 反例 1: 将非 Send 类型传入 spawn

**错误示例**:

```rust
let rc = std::rc::Rc::new(1);
thread::spawn(|| {
    println!("{}", rc);  // ❌ Rc 不是 Send
});
```

**原因**: `thread::spawn` 要求闭包捕获的类型实现 `Send`。

**修正**:

```rust
let arc = std::sync::Arc::new(1);
thread::spawn(move || {
    println!("{}", arc);
});
```

---

### 反例 2: 死锁 - 重复获取同一 Mutex

**错误示例**:

```rust
let m = Mutex::new(1);
let g1 = m.lock().unwrap();
let g2 = m.lock().unwrap();  // ❌ 死锁：同一线程重复获取
```

**原因**: `Mutex` 非递归，同一线程重复 lock 会死锁。

**修正**:

```rust
let g = m.lock().unwrap();
// 使用 g，作用域结束后释放
```

---

## 📚 相关文档

- [线程与并发完整文档](../../crates/c05_threads/docs/)
- [线程与并发 README](../../crates/c05_threads/README.md)

## 🧩 相关示例代码

以下示例位于 `crates/c05_threads/examples/`，可直接运行（例如：`cargo run -p c05_threads --example message_passing_demo`）。

- [消息传递与高级并发](../../crates/c05_threads/examples/message_passing_demo.rs)、[advanced_concurrency_patterns_demo.rs](../../crates/c05_threads/examples/advanced_concurrency_patterns_demo.rs)
- [背压与流式处理](../../crates/c05_threads/examples/backpressure_overview_demo.rs)、[stream_backpressure_demo.rs](../../crates/c05_threads/examples/stream_backpressure_demo.rs)、[stream_rate_batch_demo.rs](../../crates/c05_threads/examples/stream_rate_batch_demo.rs)
- [优先级通道与实战模式](../../crates/c05_threads/examples/priority_channels_demo.rs)、[real_world_threading_demo.rs](../../crates/c05_threads/examples/real_world_threading_demo.rs)、[performance_optimization_demo.rs](../../crates/c05_threads/examples/performance_optimization_demo.rs)
- [Rust 1.92 特性演示](../../crates/c05_threads/examples/rust_192_features_demo.rs)、[rust_190_features_demo.rs](../../crates/c05_threads/examples/rust_190_features_demo.rs)

---

## 🔗 相关资源

- [并发模式速查卡](./async_patterns.md)
- [Rust 官方文档 - 并发](https://doc.rust-lang.org/book/ch16-00-concurrency.html)

---

## 🆕 Rust 1.93.0 并发改进

### 内存分配优化

**改进**: 小对象分配性能提升 25-30%（并发场景）

```rust
// Rust 1.93.0 优化后的并发内存分配（全局分配器支持线程本地存储）
use std::sync::Arc;
use std::collections::HashMap;

// ✅ 并发场景下的内存分配性能提升
let shared_map: Arc<HashMap<i32, String>> = Arc::new(HashMap::new());
```

**影响**:

- 并发场景下的内存分配性能提升
- 同步原语性能优化
- 内存碎片减少

---

## 📚 相关资源

### 官方文档

- [Rust 并发文档](https://doc.rust-lang.org/book/ch16-00-fearless-concurrency.html)
- [std::thread 文档](https://doc.rust-lang.org/std/thread/)
- [std::sync 文档](https://doc.rust-lang.org/std/sync/)

### 项目内部文档

- [线程与并发完整文档](../../crates/c05_threads/docs/)
- [并发研究笔记](../../docs/research_notes/)

### 相关速查卡

- [异步编程速查卡](./async_patterns.md) - 异步并发对比
- [智能指针速查卡](./smart_pointers_cheatsheet.md) - Arc 和 Mutex
- [所有权系统速查卡](./ownership_cheatsheet.md) - 所有权与并发
- [错误处理速查卡](./error_handling_cheatsheet.md) - 并发错误处理

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.0+ (Edition 2024)
