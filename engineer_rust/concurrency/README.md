# 并发模型（Concurrency Model）

## 1. 定义与软件工程对标

**并发（Concurrency）**指多个任务在同一时间段内交替推进，强调任务切换与资源共享。对标软件工程wiki，Concurrency 是系统设计的核心能力之一，直接影响可扩展性与响应性。
**Concurrency** means multiple tasks make progress within the same time period, focusing on task switching and resource sharing. In software engineering, concurrency is a key capability for scalable and responsive systems.

## 2. Rust 1.88 最新特性

- **`std::sync::LazyLock`/`LazyCell`**：全局/线程局部懒初始化，线程安全，零开销。
- **`async fn in traits`**：异步trait原生支持，极大简化异步并发设计。
- **`#[expect]`属性**：可控lint，提升并发代码开发体验。
- **trait对象向上转型**：支持trait对象的安全类型提升，便于并发抽象。

## 3. 典型惯用法（Idioms）

- 使用 `std::thread`/`tokio::task` 创建并发任务
- `Mutex`/`RwLock`/`Arc` 进行安全共享
- `channel`/`mpsc`/`crossbeam` 进行消息传递
- `rayon` 实现数据并行
- `LazyLock`/`LazyCell` 实现惰性并发初始化

## 4. 代码示例（含1.88新特性）

```rust
// 1.88 新特性：LazyLock 全局并发初始化
use std::sync::LazyLock;
static CONFIG: LazyLock<String> = LazyLock::new(|| "init".to_string());

// async fn in traits
trait AsyncJob {
    async fn run(&self);
}
```

## 5. 软件工程概念对照

- **线程安全（Thread Safety）**：Rust 通过类型系统（Send/Sync）静态保证。
- **死锁检测（Deadlock Detection）**：可用clippy/loom等工具辅助。
- **可扩展性（Scalability）**：并发模型设计直接影响系统可扩展性。

## 6. FAQ

- Q: Rust 如何避免数据竞争？
  A: 通过所有权、借用和类型系统静态消除绝大多数数据竞争。

---

## 理论基础

- 并发与并行的区别
- 线程模型与调度原理
- 共享内存与消息传递
- 死锁、竞态与同步机制

## 工程实践

- Rust 并发原语（thread、Mutex、RwLock、Arc、channel 等）
- 线程池与任务调度
- 无锁并发与原子操作
- 并发安全与数据一致性
- 并发测试与调试工具

## 形式化要点

- 并发状态空间的形式化建模
- 死锁与竞态检测的可验证性
- 并发安全属性的证明方法

## 推进计划

1. 理论基础与并发模型梳理
2. Rust 并发原语与工程实践
3. 形式化建模与安全验证
4. 并发测试与调试集成
5. 推进快照与断点恢复

## 断点快照

- [x] 目录结构与 README 初稿
- [ ] 理论基础与并发模型补全
- [ ] 工程案例与代码片段
- [ ] 形式化建模与验证
- [ ] 交叉引用与持续完善

---

## 深度扩展：理论阐释

### 并发与并行的区别

- 并发（Concurrency）强调多个任务在同一时间段内交替推进，关注任务切换与资源共享。
- 并行（Parallelism）强调多个任务在同一时刻真正同时执行，通常依赖多核硬件。
- Rust 通过线程、任务、异步等机制支持并发与并行的灵活组合。

### 线程模型与调度原理

- OS 线程（std::thread）与用户级线程（如 async 任务）的区别。
- 线程池（threadpool）用于复用线程资源，降低创建销毁开销。
- Rust 的 Send/Sync trait 保证多线程安全。

### 共享内存与消息传递

- 共享内存：Mutex、RwLock、Arc 等同步原语，适合高性能场景但需防止死锁。
- 消息传递：channel、mpsc、crossbeam，适合解耦与 Actor 模型。
- Rust 倾向于“消息传递优先”，减少共享状态。

### 死锁、竞态与同步机制

- 死锁：互斥锁循环等待导致系统停滞。
- 竞态：多个线程并发访问共享资源导致结果不确定。
- 同步机制：条件变量、Barrier、Once、atomic 原子操作等。

---

## 深度扩展：工程代码片段

### 1. 线程创建与 join

```rust
use std::thread;
let handle = thread::spawn(|| {
    println!("子线程执行");
});
handle.join().unwrap();
```

### 2. 线程池使用（rayon）

```rust
use rayon::prelude::*;
let v = vec![1, 2, 3, 4, 5];
let sum: i32 = v.par_iter().map(|x| x * 2).sum();
```

### 3. 互斥锁与原子操作

```rust
use std::sync::{Arc, Mutex};
let data = Arc::new(Mutex::new(0));
let mut handles = vec![];
for _ in 0..10 {
    let data = Arc::clone(&data);
    handles.push(thread::spawn(move || {
        let mut num = data.lock().unwrap();
        *num += 1;
    }));
}
for h in handles { h.join().unwrap(); }
```

### 4. 消息通道通信

```rust
use std::sync::mpsc;
let (tx, rx) = mpsc::channel();
thread::spawn(move || {
    tx.send(42).unwrap();
});
println!("收到: {}", rx.recv().unwrap());
```

---

## 深度扩展：典型场景案例

### 生产者-消费者模型

- 多线程生产者通过 channel 发送数据，消费者异步处理。
- 可用 crossbeam-channel 提升性能。

### 并发爬虫/下载器

- 多线程/异步任务分发 URL，主线程收集结果。
- 结合线程池与消息通道实现高吞吐。

### 并发数据处理流水线

- 多 stage 任务通过 channel 串联，形成流水线并发处理。

---

## 深度扩展：形式化证明与自动化测试

### 形式化证明思路

- 利用 Rust 类型系统（Send/Sync）静态保证线程安全。
- 死锁检测可用 clippy lint、loom 等工具进行模型检查。
- 竞态条件可用 miri、loom 进行动态/模型测试。

### 自动化测试用例

```rust
#[test]
fn test_concurrent_increment() {
    use std::sync::{Arc, Mutex};
    use std::thread;
    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    for _ in 0..10 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let mut num = data.lock().unwrap();
            *num += 1;
        }));
    }
    for h in handles { h.join().unwrap(); }
    assert_eq!(*data.lock().unwrap(), 10);
}
```
