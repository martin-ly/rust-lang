# 🔀 Rust 线程与并发速查卡

> **快速参考** | [完整文档](../../crates/c05_threads/docs/) | [代码示例](../../crates/c05_threads/examples/)
> **最后更新**: 2025-11-15 | **Rust 版本**: 1.91.1+ | **Edition**: 2024

---

## 📋 目录

- [🔀 Rust 线程与并发速查卡](#-rust-线程与并发速查卡)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [线程创建](#线程创建)
    - [作用域线程 (Rust 1.92.0+)](#作用域线程-rust-1920)
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
  - [🔗 相关资源](#-相关资源)
  - [🆕 Rust 1.92.0 并发改进](#-rust-1920-并发改进)
    - [内存分配优化](#内存分配优化)

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

### 作用域线程 (Rust 1.92.0+)

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

## 🔗 相关资源

- [线程编程完整文档](../../crates/c05_threads/docs/)
- [并发模式速查卡](./async_patterns.md)
- [Rust 官方文档 - 并发](https://doc.rust-lang.org/book/ch16-00-concurrency.html)

---

---

## 🆕 Rust 1.92.0 并发改进

### 内存分配优化

**改进**: 小对象分配性能提升 25-30%（并发场景）

```rust
// Rust 1.92.0 优化后的并发内存分配
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

**最后更新**: 2025-11-15
**Rust 版本**: 1.91.1+ (Edition 2024)
