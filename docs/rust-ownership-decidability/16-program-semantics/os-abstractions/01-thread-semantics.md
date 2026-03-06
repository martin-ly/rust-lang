# 线程模型的完整形式化语义

## 1. 引言

线程是操作系统提供的基本并发原语，Rust 通过 `std::thread` 模块提供了对操作系统线程的抽象。
本文档从形式化角度定义线程的语义，包括线程生命周期、调度、局部存储以及线程安全 trait 的精确含义。

## 2. 线程状态机的形式化定义

### 2.1 线程状态

```
Thread 状态机:
  TState ::= New | Runnable | Running | Blocked | Terminated
```

**状态说明：**

- **New**: 线程已创建但未开始执行
- **Runnable**: 线程准备好执行，等待调度器分配 CPU
- **Running**: 线程正在 CPU 上执行
- **Blocked**: 线程等待某个事件（I/O、锁、信号量等）
- **Terminated**: 线程执行完毕，资源已释放

### 2.2 状态转换规则

```
Thread 转换规则:
  spawn(f): New → Runnable
  schedule: Runnable → Running
  block: Running → Blocked
  unblock: Blocked → Runnable
  exit: Running → Terminated
  preempt: Running → Runnable
```

**转换说明：**

| 转换 | 触发条件 | 语义 |
|------|----------|------|
| `spawn(f)` | 调用 `thread::spawn(f)` | 创建新线程，函数 f 准备执行 |
| `schedule` | OS 调度器选择该线程 | 分配 CPU 时间片 |
| `block` | 等待资源/事件 | 释放 CPU，进入等待队列 |
| `unblock` | 等待条件满足 | 重新进入就绪队列 |
| `exit` | 线程函数返回 | 清理资源，线程结束 |
| `preempt` | 时间片用完/更高优先级线程 | 强制让出 CPU |

## 3. 线程创建语义的形式化

### 3.1 Spawn 操作的形式化定义

```
spawn: (() → T) → JoinHandle<T>

前提条件:
  ∀f: () → T, f 满足 'static + Send

后置条件:
  1. 创建新线程 t，t ∈ Threads
  2. t.state = New
  3. 执行转换 spawn(f): New → Runnable
  4. 返回 JoinHandle<T>，用于后续 join
```

### 3.2 Rust 代码示例

```rust
use std::thread;
use std::time::Duration;

fn spawn_example() {
    // 创建新线程
    let handle = thread::spawn(|| {
        // 线程执行体
        println!("新线程正在执行");
        42  // 返回值
    });

    // 主线程继续执行
    println!("主线程继续执行");

    // 等待子线程完成并获取结果
    let result = handle.join().expect("线程 panic");
    assert_eq!(result, 42);
}
```

### 3.3 所有权转移语义

```
spawn 的所有权规则:

  闭包捕获: ∀v ∈ captured_vars,
    - 若 v: Send，则所有权可转移到新线程
    - 若 v: !Send，则编译错误

  返回值: T: Send，才能通过 JoinHandle 传递回父线程
```

```rust
// 合法：String 实现了 Send
thread::spawn(|| {
    let s = String::from("hello");
    s  // 返回值
});

// 非法：Rc 不实现 Send
// let rc = Rc::new(5);
// thread::spawn(move || {
//     println!("{}", rc);  // 编译错误
// });
```

## 4. 线程调度语义

### 4.1 OS 调度器的形式化模型

```
调度器状态:
  SchedulerState = {
    ready_queue: Queue<ThreadId>,
    current: Option<ThreadId>,
    time_slice: Duration
  }

调度操作:
  select_next: SchedulerState → Option<ThreadId>
  context_switch: ThreadId × ThreadId → ()

调度策略（平台相关）:
  - CFS (Linux): 完全公平调度
  - Round-Robin: 时间片轮转
  - Priority-based: 优先级调度
```

### 4.2 协作式 vs 抢占式调度

```rust
// 协作式让出 CPU
thread::yield_now();

// 休眠指定时间（自愿放弃 CPU）
thread::sleep(Duration::from_millis(100));
```

```
yield_now 语义:
  Running → Runnable → (调度器选择) → Running

sleep(d) 语义:
  Running → Blocked --(d 时间后)--> Runnable
```

## 5. 线程局部存储语义

### 5.1 `thread_local!` 的形式化定义

```
ThreadLocal<T> 的语义:

  存储模型:
    TLS: ThreadId → Option<T>

  初始化:
    init: () → T  （延迟初始化）

  访问操作:
    with(f): (T → R) → R

  约束:
    ∀t1, t2 ∈ Threads, t1 ≠ t2 →
      TLS[t1] 与 TLS[t2] 无数据竞争
```

### 5.2 Rust 代码示例

```rust
use std::cell::RefCell;
use std::thread;

thread_local! {
    static COUNTER: RefCell<u32> = RefCell::new(0);
}

fn tls_example() {
    COUNTER.with(|c| {
        *c.borrow_mut() += 1;
        println!("当前线程计数: {}", c.borrow());
    });

    thread::spawn(|| {
        // 新线程有自己的独立副本
        COUNTER.with(|c| {
            *c.borrow_mut() += 100;
            println!("子线程计数: {}", c.borrow());
        });
    }).join().unwrap();

    // 主线程的值不受影响
    COUNTER.with(|c| {
        println!("主线程计数仍为: {}", c.borrow());
    });
}
```

### 5.3 安全论证

```
ThreadLocal 的安全性证明:

定理: ThreadLocal<T> 在任何情况下都不会导致数据竞争

证明:
  1. 每个线程拥有独立的存储槽
  2. 访问 TLS 必须通过 with 方法
  3. with 方法确保当前线程只能访问自己的 TLS
  4. 因此不存在跨线程访问同一 TLS 变量的情况
  ∎
```

## 6. 线程取消语义

### 6.1 Park/Unpark 机制

```
park/unpark 状态机:

  状态:
    ParkState ::= Unparked | Parking | Parked

  操作:
    park():
      Unparked → Parking → Parked (阻塞)

    unpark(tid):
      Parked(tid) → Unparked(tid)
      Parking(tid) → Unparked(tid) (避免阻塞)
```

### 6.2 Rust 代码示例

```rust
use std::thread;
use std::time::Duration;

fn park_example() {
    let handle = thread::current();

    thread::spawn(move || {
        thread::sleep(Duration::from_millis(100));
        handle.unpark();  // 唤醒主线程
    });

    // 阻塞直到被 unpark 或超时
    thread::park_timeout(Duration::from_secs(1));
}
```

### 6.3 Park 的 happens-before 关系

```
unpark(t) happens-before t 从 park() 返回

形式化:
  若线程 A 调用 unpark(B)，
  且 unpark 发生在 B 调用 park 之前，
  则 A 中 unpark 之前的操作 happens-before B 中 park 返回后的操作
```

## 7. 线程安全 Trait 的形式化

### 7.1 Send Trait 语义

```
Send: 类型可以安全地在线程间转移所有权

形式化定义:
  T: Send ⟺
    ∀t1, t2: Thread,
    ∀v: T,
    将 v 从 t1 转移到 t2 不会导致数据竞争或内存不安全

自动推导规则:
  - 原始类型 (i32, bool 等): Send
  - 若 T: Send，则 Box<T>: Send
  - 若 T: Send，则 Vec<T>: Send
  - 若 T: Sync，则 &T: Send
  - 包含 !Send 字段的结构体: !Send
```

### 7.2 Sync Trait 语义

```
Sync: 类型可以安全地在多个线程间共享引用

形式化定义:
  T: Sync ⟺
    ∀t1, t2: Thread, t1 ≠ t2,
    ∀v: T,
    同时持有 &v 不会导致数据竞争

等价表述:
  T: Sync ⟺ &T: Send

自动推导规则:
  - 原始类型: Sync
  - 若 T: Sync，则 &T: Sync
  - 若 T: Send + Sync，则 Arc<T>: Send + Sync
  - 包含 Cell/RefCell 等内部可变性的类型: !Sync
```

### 7.3 重要类型的线程安全分类

```
类型分类矩阵:

                 Send          !Send
            +-------------+-------------+
Sync        | Arc<T>      | MutexGuard  |
            | Mutex<T>    | (某些情况)  |
            | AtomicU32   |             |
            +-------------+-------------+
!Sync       | Rc<T>       | *const T    |
            | Cell<T>     | 裸指针      |
            +-------------+-------------+
```

### 7.4 代码示例

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::rc::Rc;

fn thread_safety_example() {
    // Arc<T>: Send + Sync（当 T: Send + Sync）
    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let data_clone = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let mut guard = data_clone.lock().unwrap();
            *guard += 1;
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    // Rc<T>: !Send + !Sync
    // let rc = Rc::new(5);
    // thread::spawn(move || { println!("{}", rc); }); // 编译错误
}
```

## 8. 综合安全论证

### 8.1 线程安全定理

```
定理 (Rust 线程安全保证):
  若程序通过 Rust 编译器的类型检查，
  则程序不存在数据竞争

证明概要:
  1. 所有权系统确保每个值有唯一的所有者
  2. Send trait 控制跨线程所有权转移
  3. Sync trait 控制跨线程共享引用
  4. 借用检查器确保引用的有效性
  5. 以上机制共同保证无数据竞争
  ∎
```

### 8.2 形式化不变式

```
线程执行不变式:

  I1: ∀线程 t, t.state = Running →
       t 拥有其栈上所有值的独占访问权

  I2: ∀值 v, owner(v) = t ∧ v: !Send →
       v 永远不会被转移到其他线程

  I3: ∀引用 r = &v, ∀线程 t1, t2,
       t1 持有 r ∧ t2 持有 r ∧ v: !Sync →
       编译错误
```

## 9. 总结

本文档完整形式化了 Rust 线程模型的语义：

1. **状态机模型**：定义了线程的 5 种状态及其转换规则
2. **Spawn 语义**：明确了线程创建的约束条件和所有权转移规则
3. **调度语义**：描述了 OS 调度器的交互和协作式调度原语
4. **TLS 语义**：形式化了线程局部存储的安全保证
5. **Park/Unpark**：定义了线程阻塞/唤醒的语义和 happens-before 关系
6. **Send/Sync**：精确形式化了线程安全 trait 的含义和推导规则

这些形式化定义确保了 Rust 并发程序的安全性和正确性。
