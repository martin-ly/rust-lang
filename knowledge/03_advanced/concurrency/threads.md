# 线程并发

> **Rust  fearless 并发**
> **预计时间**: 5 小时

## 🎯 学习目标

- [ ] 创建和管理线程
- [ ] 使用线程间通信
- [ ] 理解线程安全

## 📋 先决条件

- 理解所有权系统
- 了解 Send 和 Sync trait

## 🧠 核心概念

### 1. 创建线程

```rust
use std::thread;

let handle = thread::spawn(|| {
    println!("Hello from thread!");
});

handle.join().unwrap();
```

### 2. 消息传递

```rust
use std::sync::mpsc;

let (tx, rx) = mpsc::channel();

thread::spawn(move || {
    tx.send("Hello").unwrap();
});

let msg = rx.recv().unwrap();
```

### 3. 共享状态

```rust
use std::sync::{Arc, Mutex};

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
```

## 📖 延伸阅读

- [Rust Book - Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
