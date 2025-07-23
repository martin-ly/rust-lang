# 并发模型（Concurrency Model）

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
