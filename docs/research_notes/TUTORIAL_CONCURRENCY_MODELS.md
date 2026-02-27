# 教程：并发模型

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **目标受众**: 进阶
> **预计阅读时间**: 35分钟
> **级别**: L1/L2

---

## 引言

Rust提供了多种并发模型，从传统的线程到现代的异步编程。本教程将深入讲解Rust的并发模型及其适用场景。

---

## 第一部分：并发基础

### 并发 vs 并行

| 概念 | 定义 | Rust支持 |
| :--- | :--- | :--- |
| **并发** | 同时处理多个任务 | ✅ 线程、async |
| **并行** | 同时执行多个任务 | ✅ `rayon`、多线程 |

```
并发: 任务交错执行 (单核)
┌─────────────────────────────────────>
│ Task1: [====][====][====]
│ Task2:      [====][====][====]
└─────────────────────────────────────>

并行: 任务同时执行 (多核)
┌─────────────────────────────────────>
│ Core1: [=================]
│ Core2: [=================]
└─────────────────────────────────────>
```

### Send 和 Sync

```rust
// Send: 可安全跨线程转移所有权
pub unsafe auto trait Send {}

// Sync: 可安全跨线程共享引用
pub unsafe auto trait Sync {}

// 规则: T: Sync 当且仅当 &T: Send
```

**自动实现规则:**

- 原始类型(i32, bool等): Send + Sync
- 只包含Send/Sync类型的结构体: Send + Sync
- `Rc`: !Send && !Sync(非原子)
- `Arc<T>`: Send(if T: Send) + Sync(if T: Sync)

---

## 第二部分：线程模型

### 创建线程

```rust
use std::thread;
use std::time::Duration;

// 基本线程
let handle = thread::spawn(|| {
    for i in 1..10 {
        println!("Hi {} from spawned thread!", i);
        thread::sleep(Duration::from_millis(1));
    }
});

// 等待线程完成
handle.join().unwrap();
```

### 线程间通信

```rust
use std::sync::mpsc;
use std::thread;

// 多生产者单消费者通道
let (tx, rx) = mpsc::channel();

thread::spawn(move || {
    let val = String::from("hi");
    tx.send(val).unwrap();
    // val 已被移动，不可用
});

let received = rx.recv().unwrap();
println!("Got: {}", received);
```

### 共享状态

```rust
use std::sync::{Arc, Mutex};
use std::thread;

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

println!("Result: {}", *counter.lock().unwrap()); // 10
```

---

## 第三部分：同步原语

### Mutex vs RwLock

| 原语 | 读并发 | 写并发 | 适用场景 |
| :--- | :--- | :--- | :--- |
| `Mutex<T>` | 互斥 | 互斥 | 读写相当 |
| `RwLock<T>` | 并发 | 互斥 | 读多写少 |

```rust
use std::sync::RwLock;

let data = RwLock::new(5);

// 多个读锁可以共存
let r1 = data.read().unwrap();
let r2 = data.read().unwrap();

// 写锁独占
{
    let mut w = data.write().unwrap();
    *w += 1;
} // 写锁释放
```

### 原子操作

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

let counter = AtomicUsize::new(0);

// 读
counter.load(Ordering::Relaxed);

// 写
counter.store(42, Ordering::Relaxed);

// 原子加
counter.fetch_add(1, Ordering::SeqCst);

// CAS
counter.compare_exchange(current, new, Ordering::Acquire, Ordering::Relaxed);
```

**内存序选择:**

- `Relaxed`: 无顺序约束，性能最高
- `Acquire/Release`: 同步配对
- `SeqCst`: 全局顺序，最安全但最慢

---

## 第四部分：异步模型

### Future基础

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// Future是惰性的
let f = async { 42 };  // 尚未执行

// 需要executor来运行
let result = f.await;  // 在async上下文中执行
```

### async/await

```rust
async fn fetch_data(url: &str) -> Result<String, Error> {
    let response = reqwest::get(url).await?;
    let data = response.text().await?;
    Ok(data)
}

// 并发执行
async fn fetch_multiple() -> Result<(), Error> {
    let (a, b, c) = tokio::join!(
        fetch_data("url1"),
        fetch_data("url2"),
        fetch_data("url3"),
    );
    Ok(())
}
```

### 运行时选择

| 运行时 | 特点 | 适用场景 |
| :--- | :--- | :--- |
| **Tokio** | 功能最全，生态丰富 | 生产环境首选 |
| **async-std** | 标准库风格 | 简洁项目 |
| **smol** | 轻量级 | 嵌入式/低资源 |
| **embassy** | no_std支持 | 嵌入式硬件 |

---

## 第五部分：并发模式

### Fork-Join

```rust
use rayon::prelude::*;

// 数据并行
let sum: i32 = (0..100).into_par_iter().sum();

// 任务并行
let (a, b) = rayon::join(
    || compute_a(),
    || compute_b(),
);
```

### 生产者-消费者

```rust
use crossbeam::channel;
use std::thread;

let (s, r) = channel::bounded(100);

// 生产者
thread::spawn(move || {
    for i in 0..1000 {
        s.send(i).unwrap();
    }
});

// 消费者
thread::spawn(move || {
    for msg in r {
        process(msg);
    }
});
```

### Actor模型

```rust
use actix::prelude::*;

struct MyActor {
    count: usize,
}

impl Actor for MyActor {
    type Context = Context<Self>;
}

struct MyMessage;

impl Message for MyMessage {
    type Result = usize;
}

impl Handler<MyMessage> for MyActor {
    type Result = usize;

    fn handle(&mut self, _msg: MyMessage, _ctx: &mut Context<Self>) -> Self::Result {
        self.count += 1;
        self.count
    }
}
```

---

## 第六部分：最佳实践

### 选择合适的并发模型

| 场景 | 推荐模型 | 理由 |
| :--- | :--- | :--- |
| CPU密集型 | `rayon` | 数据并行，自动负载均衡 |
| I/O密集型 | async/await | 高并发，低内存占用 |
| 实时处理 | 专用线程 | 避免延迟抖动 |
| 复杂状态 | Actor | 隔离性，容错 |

### 避免常见陷阱

```rust
// ❌ 跨越await持有std Mutex
async fn bad() {
    let guard = mutex.lock().unwrap();
    async_op().await;  // 阻塞其他任务!
}

// ✅ 使用tokio::sync::Mutex
async fn good() {
    let guard = async_mutex.lock().await;
    async_op().await;  // OK
}

// ❌ 在async块中使用阻塞IO
async fn bad2() {
    std::fs::read_to_string("file").unwrap();  // 阻塞!
}

// ✅ 使用异步IO
async fn good2() {
    tokio::fs::read_to_string("file").await?;  // 非阻塞
}
```

---

## 第一部分：OS线程

### 何时使用

- CPU密集型任务
- 需要真正的并行
- 阻塞操作

```rust
use std::thread;

let handle = thread::spawn(|| {
    // CPU密集型计算
    heavy_computation()
});

let result = handle.join().unwrap();
```

**限制**: 创建成本高，数量受限(~几百)。

---

## 第二部分：异步/任务

### 何时使用

- IO密集型
- 高并发(数万连接)
- 非阻塞

```rust
#[tokio::main]
async fn main() {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:8080").await.unwrap();

    loop {
        let (socket, _) = listener.accept().await.unwrap();
        tokio::spawn(handle_connection(socket));
    }
}
```

**优势**: 轻量级，可创建数百万任务。

---

## 第三部分：数据并行

### 何时使用

- 数据处理
- 集合操作

```rust
use rayon::prelude::*;

let sum: i32 = (0..1_000_000)
    .into_par_iter()  // 并行迭代器
    .map(|x| x * x)
    .sum();
```

**优势**: 自动工作窃取，负载均衡。

---

## 第四部分：Actor模型

### 何时使用

- 分布式系统
- 容错需求
- 状态封装

```rust
// actix示例
use actix::prelude::*;

struct MyActor;

impl Actor for MyActor {
    type Context = Context<Self>;
}

impl Handler<Message> for MyActor {
    type Result = ();

    fn handle(&mut self, msg: Message, _ctx: &mut Context<Self>) {
        // 处理消息
    }
}
```

---

## 第五部分：选择决策

```
任务类型？
├── CPU密集型
│   ├── 数据并行 → rayon
│   └── 通用并行 → OS线程
│
├── IO密集型
│   └── 异步 → tokio/async-std
│
└── 状态管理
    └── Actor → actix
```

---

## 总结

| 模型 | 适用场景 | 性能 | 复杂度 |
| :--- | :--- | :--- | :--- |
| OS线程 | CPU密集 | 高 | 低 |
| 异步 | IO密集 | 高 | 中 |
| 数据并行 | 数据处理 | 极高 | 低 |
| Actor | 分布式 | 中 | 高 |

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 并发模型教程完整版
