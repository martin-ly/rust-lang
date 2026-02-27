# 并发速查卡

> **一页纸速查** - 线程、同步原语、并发模式

---

## Send与Sync

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

## 同步原语

| 原语 | 用途 | 场景 |
| :--- | :--- | :--- |
| `Mutex<T>` | 互斥访问 | 通用 |
| `RwLock<T>` | 多读单写 | 读多写少 |
| `AtomicUsize` | 原子计数 | 高性能计数 |
| `mpsc::channel` | 消息传递 | 线程通信 |
| `Barrier` | 等待所有线程 | 并行计算 |

---

## 创建线程

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

## Send/Sync

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

## 共享状态

### Mutex

```rust
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

### RwLock

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

## 通道通信

### mpsc

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

### 多生产者

```rust
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

## 原子操作

```rust
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

### 内存序

| 顺序 | 保证 | 性能 |
| :--- | :--- | :--- |
| `Relaxed` | 无 | 最高 |
| `Acquire`/`Release` | 同步 | 高 |
| `AcqRel` | 两者 | 高 |
| `SeqCst` | 全局顺序 | 较低 |

---

## 线程同步

### Barrier

```rust
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

### Condvar

```rust
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

## 线程局部存储

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

## 常见模式

### 线程池

```rust
use threadpool::ThreadPool;

let pool = ThreadPool::new(4);

for i in 0..8 {
    pool.execute(move || {
        println!("Task {}", i);
    });
}

pool.join();
```

### 并行迭代

```rust
use rayon::prelude::*;

let sum: i32 = (0..100).into_par_iter().sum();

let mut vec = vec![1, 2, 3, 4, 5];
vec.par_iter_mut().for_each(|x| *x *= 2);
```

---

## 死锁预防

```text
□ 统一的锁获取顺序
□ 使用try_lock()避免阻塞
□ 锁的持有时间最小化
□ 考虑使用lock_bud检测
□ 优先使用通道而非共享状态
```

---

## 性能检查清单

```text
□ 减少锁竞争(细粒度锁)
□ 使用读多写少用RwLock
□ 考虑无锁数据结构
□ 使用线程池避免创建开销
□ 批处理减少同步
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 并发速查卡完整版
