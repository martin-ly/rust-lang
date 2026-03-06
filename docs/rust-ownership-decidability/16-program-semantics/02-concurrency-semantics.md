# Rust 并发执行模型语义

## 目录

- [Rust 并发执行模型语义](#rust-并发执行模型语义)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [1.1 并发与并行的语义区别](#11-并发与并行的语义区别)
    - [1.2 Rust 并发安全保证](#12-rust-并发安全保证)
    - [1.3 Send 和 Sync trait 语义](#13-send-和-sync-trait-语义)
  - [2. 线程模型语义](#2-线程模型语义)
    - [2.1 OS 线程语义](#21-os-线程语义)
      - [2.1.1 线程创建语义](#211-线程创建语义)
      - [2.1.2 线程连接语义](#212-线程连接语义)
      - [2.1.3 线程本地存储语义](#213-线程本地存储语义)
    - [2.2 线程间通信语义](#22-线程间通信语义)
      - [2.2.1 共享内存语义](#221-共享内存语义)
      - [2.2.2 消息传递语义](#222-消息传递语义)
      - [2.2.3 内存序语义](#223-内存序语义)
    - [2.3 线程安全边界语义](#23-线程安全边界语义)
      - [2.3.1 Send 边界语义](#231-send-边界语义)
      - [2.3.2 Sync 边界语义](#232-sync-边界语义)
      - [2.3.3 !Send 和 !Sync 语义](#233-send-和-sync-语义)
  - [3. 同步原语语义](#3-同步原语语义)
    - [3.1 互斥锁语义 (Mutex)](#31-互斥锁语义-mutex)
      - [3.1.1 锁获取语义](#311-锁获取语义)
      - [3.1.2 锁释放语义](#312-锁释放语义)
      - [3.1.3 死锁避免语义](#313-死锁避免语义)
      - [3.1.4 锁守卫语义](#314-锁守卫语义)
    - [3.2 读写锁语义 (RwLock)](#32-读写锁语义-rwlock)
      - [3.2.1 读锁共享语义](#321-读锁共享语义)
      - [3.2.2 写锁独占语义](#322-写锁独占语义)
      - [3.2.3 锁升级/降级语义](#323-锁升级降级语义)
      - [3.2.4 读偏好 vs 写偏好](#324-读偏好-vs-写偏好)
    - [3.3 条件变量语义 (Condvar)](#33-条件变量语义-condvar)
      - [3.3.1 等待语义](#331-等待语义)
      - [3.3.2 通知语义](#332-通知语义)
      - [3.3.3 虚假唤醒处理](#333-虚假唤醒处理)
      - [3.3.4 与锁的组合语义](#334-与锁的组合语义)
    - [3.4 屏障语义 (Barrier)](#34-屏障语义-barrier)
      - [3.4.1 同步点语义](#341-同步点语义)
      - [3.4.2 分阶段执行语义](#342-分阶段执行语义)
      - [3.4.3 领导者选举语义](#343-领导者选举语义)
  - [4. 无锁并发语义](#4-无锁并发语义)
    - [4.1 原子操作语义](#41-原子操作语义)
      - [4.1.1 原子读写语义](#411-原子读写语义)
      - [4.1.2 原子 CAS 语义](#412-原子-cas-语义)
      - [4.1.3 原子 fetch-and-update 语义](#413-原子-fetch-and-update-语义)
    - [4.2 内存序语义](#42-内存序语义)
      - [4.2.1 Relaxed 语义](#421-relaxed-语义)
      - [4.2.2 Acquire/Release 语义](#422-acquirerelease-语义)
      - [4.2.3 SeqCst 语义](#423-seqcst-语义)
      - [4.2.4 happens-before 关系](#424-happens-before-关系)
    - [4.3 无锁数据结构语义](#43-无锁数据结构语义)
      - [4.3.1 无锁队列语义](#431-无锁队列语义)
      - [4.3.2 无锁栈语义](#432-无锁栈语义)
      - [4.3.3 无锁哈希表语义](#433-无锁哈希表语义)
      - [4.3.4 ABA 问题与解决方案](#434-aba-问题与解决方案)
  - [5. 数据并行语义](#5-数据并行语义)
    - [5.1 迭代器并行语义](#51-迭代器并行语义)
      - [5.1.1 par\_iter 语义](#511-par_iter-语义)
      - [5.1.2 分块策略语义](#512-分块策略语义)
      - [5.1.3 工作窃取语义](#513-工作窃取语义)
    - [5.2 数据竞争自由语义](#52-数据竞争自由语义)
      - [5.2.1 只读并行语义](#521-只读并行语义)
      - [5.2.2 互斥写语义](#522-互斥写语义)
      - [5.2.3 归约操作语义](#523-归约操作语义)
  - [6. 并发控制流语义](#6-并发控制流语义)
    - [6.1 分叉-汇合语义 (Fork-Join)](#61-分叉-汇合语义-fork-join)
      - [6.1.1 作用域线程语义](#611-作用域线程语义)
      - [6.1.2 跨作用域借用语义](#612-跨作用域借用语义)
      - [6.1.3 Rayon 并行模式](#613-rayon-并行模式)
    - [6.2 生产者-消费者语义](#62-生产者-消费者语义)
      - [6.2.1 管道语义](#621-管道语义)
      - [6.2.2 背压语义](#622-背压语义)
      - [6.2.3 流控制语义](#623-流控制语义)
    - [6.3 读者-写者语义](#63-读者-写者语义)
      - [6.3.1 多读单写语义](#631-多读单写语义)
      - [6.3.2 锁优化语义](#632-锁优化语义)
      - [6.3.3 公平性语义](#633-公平性语义)
  - [7. 并发错误处理语义](#7-并发错误处理语义)
    - [7.1 恐慌传播语义](#71-恐慌传播语义)
      - [7.1.1 线程间恐慌传播](#711-线程间恐慌传播)
      - [7.1.2 恐慌恢复语义](#712-恐慌恢复语义)
      - [7.1.3 作用域线程恐慌](#713-作用域线程恐慌)
    - [7.2 超时语义](#72-超时语义)
      - [7.2.1 锁超时语义](#721-锁超时语义)
      - [7.2.2 通道超时语义](#722-通道超时语义)
      - [7.2.3 条件变量超时](#723-条件变量超时)
    - [7.3 取消语义](#73-取消语义)
      - [7.3.1 线程取消语义](#731-线程取消语义)
      - [7.3.2 协作取消语义](#732-协作取消语义)
      - [7.3.3 资源清理语义](#733-资源清理语义)
  - [8. 并发数据流语义](#8-并发数据流语义)
    - [8.1 共享状态数据流](#81-共享状态数据流)
      - [8.1.1 Arc\<Mutex\> 语义](#811-arcmutex-语义)
      - [8.1.2 读写分离语义](#812-读写分离语义)
      - [8.1.3 复制-on-写入语义](#813-复制-on-写入语义)
    - [8.2 消息传递数据流](#82-消息传递数据流)
      - [8.2.1 通道数据流](#821-通道数据流)
      - [8.2.2 Actor 消息流](#822-actor-消息流)
      - [8.2.3 事件驱动数据流](#823-事件驱动数据流)
  - [9. 并发运行时语义](#9-并发运行时语义)
    - [9.1 线程池语义](#91-线程池语义)
      - [9.1.1 固定线程池语义](#911-固定线程池语义)
      - [9.1.2 动态线程池语义](#912-动态线程池语义)
      - [9.1.3 工作队列语义](#913-工作队列语义)
    - [9.2 调度器语义](#92-调度器语义)
      - [9.2.1 抢占式调度语义](#921-抢占式调度语义)
      - [9.2.2 协作式调度语义](#922-协作式调度语义)
      - [9.2.3 优先级调度语义](#923-优先级调度语义)
  - [10. 并发程序验证](#10-并发程序验证)
    - [10.1 静态验证](#101-静态验证)
      - [10.1.1 类型系统验证](#1011-类型系统验证)
      - [10.1.2 借用检查验证](#1012-借用检查验证)
      - [10.1.3 死锁检测](#1013-死锁检测)
    - [10.2 动态验证](#102-动态验证)
      - [10.2.1 数据竞争检测 (Miri)](#1021-数据竞争检测-miri)
      - [10.2.2 线程安全检查](#1022-线程安全检查)
      - [10.2.3 性能分析](#1023-性能分析)
  - [11. 总结](#11-总结)
    - [11.1 核心语义概念回顾](#111-核心语义概念回顾)
    - [11.2 安全保证总结](#112-安全保证总结)
    - [11.3 性能与安全权衡](#113-性能与安全权衡)
    - [11.4 最佳实践](#114-最佳实践)
  - [参考](#参考)

---

## 1. 引言

### 1.1 并发与并行的语义区别

在程序语义层面，**并发（Concurrency）**与**并行（Parallelism）**具有本质区别：

$$
\begin{aligned}
\text{Concurrency} &: \text{ProgramStructure} \to \text{MultipleExecutionFlows} \\
&\quad \text{（逻辑上的同时执行，关注任务分解）} \\
\text{Parallelism} &: \text{MultipleExecutionUnits} \times \text{Program} \to \text{SimultaneousExecution} \\
&\quad \text{（物理上的同时执行，关注性能加速）}
\end{aligned}
$$

| 维度 | 并发 (Concurrency) | 并行 (Parallelism) |
|-----|-------------------|-------------------|
| **核心关注点** | 任务结构、独立性、交互 | 执行资源、性能、加速比 |
| **执行方式** | 交错执行（Interleaving） | 同时执行（Simultaneous） |
| **目标** | 响应性、模块化 | 吞吐量、计算加速 |
| **依赖** | 逻辑独立即可 | 需要物理硬件支持 |
| **语义复杂性** | 高（同步、竞态） | 中（负载均衡、调度） |

```rust
// 并发示例：多任务交错执行（单核亦可）
use std::thread;
use std::sync::mpsc;

fn concurrency_example() {
    let (tx, rx) = mpsc::channel();

    // 任务A：网络请求（IO密集型）
    let tx1 = tx.clone();
    thread::spawn(move || {
        // 模拟网络延迟
        thread::sleep(std::time::Duration::from_millis(100));
        tx1.send("Network result").unwrap();
    });

    // 任务B：文件读取（IO密集型）
    thread::spawn(move || {
        thread::sleep(std::time::Duration::from_millis(50));
        tx.send("File content").unwrap();
    });

    // 主线程处理结果（任务交错执行）
    for _ in 0..2 {
        println!("Received: {}", rx.recv().unwrap());
    }
}

// 并行示例：数据并行计算（需要多核）
use rayon::prelude::*;

fn parallelism_example() {
    let data: Vec<i32> = (0..1_000_000).collect();

    // 并行计算：利用多核同时处理
    let sum: i32 = data.par_iter()
        .map(|x| x * x)
        .sum();

    println!("Parallel sum: {}", sum);
}
```

### 1.2 Rust 并发安全保证

Rust 通过类型系统提供**零成本抽象**的并发安全保证：

$$
\text{SafeConcurrency} \iff \text{TypeSystem} \vdash \text{NoDataRaces} \land \text{NoUndefinedBehavior}
$$

**核心保证：**

1. **数据竞争自由（Data-Race Freedom）**
   - 编译时检测共享可变状态的不安全访问
   - 通过所有权和借用规则强制执行

2. **内存安全（Memory Safety）**
   - 无悬垂指针
   - 无使用-after-free
   - 无缓冲区溢出

3. **类型安全（Type Safety）**
   - 线程间传递的数据类型正确
   - 同步原语的正确使用

```rust
// Rust 在编译时防止数据竞争
fn data_race_prevention() {
    let mut data = vec![1, 2, 3];

    // 错误：不能将可变引用传递给线程
    // thread::spawn(|| {
    //     data.push(4);  // 编译错误：可能的数据竞争
    // });

    // 正确：使用 Arc<Mutex<T>> 进行同步访问
    use std::sync::{Arc, Mutex};
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let data_clone = Arc::clone(&data);

    thread::spawn(move || {
        let mut locked = data_clone.lock().unwrap();
        locked.push(4);  // 安全：互斥访问
    });
}
```

### 1.3 Send 和 Sync trait 语义

`Send` 和 `Sync` 是 Rust 并发安全的基石 trait：

$$
\begin{aligned}
\text{Send} &: T \to \text{SafeToTransferAcrossThreads}(T) \\
\text{Sync} &: T \to \text{SafeToShareAcrossThreads}(\&T) \\
\text{Sync}(T) &\iff \text{Send}(\&T) \quad \text{（自动推导）}
\end{aligned}
$$

**Send 语义规则：**

$$
\frac{\forall x : T. \text{Own}(x) \land \text{Send}(T)}{\text{SafeTransfer}(x, \text{Thread}_1 \to \text{Thread}_2)}
$$

**Sync 语义规则：**

$$
\frac{\forall x : T. \text{Sync}(T)}{\text{SafeShare}(\&x, \text{Thread}_1 \times \text{Thread}_2)}
$$

```rust
use std::marker::{Send, Sync};

// Send 实现示例
// 类型自动实现 Send，当且仅当其所有字段都实现 Send
struct SafeSend {
    data: String,  // String 是 Send
}

// !Send 示例：原始指针不是 Send
struct NotSend {
    ptr: *const u8,  // 原始指针不是 Send
}

// 手动标记（仅在 unsafe 块中）
// unsafe impl Send for NotSend {}

// Sync 实现示例
// 类型自动实现 Sync，当且仅当其引用 &T 是 Send
struct SafeSync {
    data: std::sync::Arc<i32>,  // Arc<T> 当 T: Sync 时是 Sync
}

// !Sync 示例：Cell 和 RefCell 不是 Sync
use std::cell::RefCell;
struct NotSync {
    cell: RefCell<i32>,  // RefCell 内部可变性，不是 Sync
}

// Send + Sync 类型矩阵
fn send_sync_matrix() {
    // T: Send + Sync - 可安全传递和共享
    let s: String = "hello".to_string();
    let arc = std::sync::Arc::new(s);

    // 可以转移到其他线程
    let arc2 = arc.clone();
    std::thread::spawn(move || {
        println!("{}", arc2);  // Send
    });

    // 可以同时共享引用
    let r1 = &*arc;
    let r2 = &*arc;
    println!("{} {}", r1, r2);  // Sync
}
```

**自动实现规则：**

| 类型 | Send | Sync | 说明 |
|-----|------|------|------|
| `i32`, `String`, `Vec<T>` | ✓ | ✓ | 基本类型 |
| `Rc<T>` | ✗ | ✗ | 非原子引用计数 |
| `Arc<T>` | ✓ | 当 T: Sync | 原子引用计数 |
| `RefCell<T>` | 当 T: Send | ✗ | 运行时借用检查 |
| `Mutex<T>` | ✓ | 当 T: Send | 互斥锁 |
| `*const T`, `*mut T` | ✗ | ✗ | 原始指针 |
| `Cell<T>` | 当 T: Send | ✗ | 内部可变性 |

---

## 2. 线程模型语义

### 2.1 OS 线程语义

#### 2.1.1 线程创建语义

操作系统线程是最基础的并发执行单元，其创建遵循特定的资源分配语义：

$$
\text{ThreadCreate} : \text{Closure} \times \text{StackSize} \to \text{JoinHandle}\langle T \rangle
$$

**形式化语义规则：**

$$
\frac{\Gamma \vdash f : F \quad \text{Send}(F) \quad \text{'static}(F)}{\text{spawn}(f) : \text{JoinHandle}\langle\text{Output}(F)\rangle}
$$

```rust
use std::thread;
use std::time::Duration;

fn thread_creation_semantics() {
    // 基本线程创建
    let handle1 = thread::spawn(|| {
        println!("Thread 1 executing");
        42  // 返回值
    });

    // 带命名的线程（调试友好）
    let handle2 = thread::Builder::new()
        .name("worker-thread".to_string())
        .stack_size(1024 * 1024)  // 1MB 栈空间
        .spawn(|| {
            println!("Named thread: {:?}", thread::current().name());
            "result"
        })
        .unwrap();

    // 线程 ID 语义
    let current_id = thread::current().id();
    println!("Main thread ID: {:?}", current_id);

    // 等待线程完成并获取结果
    let result1 = handle1.join().expect("Thread 1 panicked");
    let result2 = handle2.join().expect("Thread 2 panicked");

    println!("Results: {}, {}", result1, result2);
}
```

#### 2.1.2 线程连接语义

线程连接（Join）是同步线程完成的关键操作：

$$
\text{Join} : \text{JoinHandle}\langle T \rangle \to \text{Result}\langle T, \text{Box}\langle\text{Any}\rangle\rangle
$$

**语义保证：**

- **happens-before**: `join()` 返回后的代码一定在线程所有操作之后执行
- **资源回收**: 线程栈和内核资源在线程结束后回收
- **结果传递**: 线程的返回值通过 `Result` 传递

```rust
fn thread_join_semantics() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let counter = AtomicUsize::new(0);

    let handle = thread::scope(|s| {
        s.spawn(|| {
            for i in 0..1000 {
                counter.fetch_add(1, Ordering::Relaxed);
            }
            "completed"
        })
    });

    // join() 创建 happens-before 关系
    let result = handle.join().unwrap();

    // 保证：所有线程内的写操作在此处可见
    assert_eq!(counter.load(Ordering::Relaxed), 1000);
    println!("Thread completed with: {}", result);
}
```

#### 2.1.3 线程本地存储语义

线程本地存储（TLS）提供线程私有的全局变量语义：

$$
\text{ThreadLocal}\langle T \rangle : \text{Thread} \to T \quad \text{（每个线程独立实例）}
$$

```rust
use std::cell::RefCell;
use std::thread;

// 线程本地变量声明
thread_local! {
    static COUNTER: RefCell<u32> = RefCell::new(0);
}

fn thread_local_semantics() {
    // 主线程访问
    COUNTER.with(|c| {
        *c.borrow_mut() += 1;
        println!("Main thread counter: {}", c.borrow());
    });

    // 子线程有独立的副本
    thread::spawn(|| {
        COUNTER.with(|c| {
            *c.borrow_mut() += 10;
            println!("Child thread counter: {}", c.borrow());  // 10
        });
    }).join().unwrap();

    // 主线程的值不受影响
    COUNTER.with(|c| {
        println!("Main thread counter after: {}", c.borrow());  // 1
    });
}
```

### 2.2 线程间通信语义

#### 2.2.1 共享内存语义

共享内存是最直接的线程通信方式：

$$
\text{SharedMemory} : T \times \text{SyncPrimitive} \to \text{SafeShared}(T)
$$

```rust
use std::sync::{Arc, Mutex, RwLock};
use std::thread;

fn shared_memory_semantics() {
    // 共享可变状态：Arc<Mutex<T>>
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let mut handles = vec![];

    for i in 0..3 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let mut vec = data.lock().unwrap();
            vec.push(i);
            println!("Thread {} pushed {}", i, i);
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    println!("Final data: {:?}", data.lock().unwrap());
}

// 读写分离语义
fn rwlock_semantics() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));

    // 多个读者并发
    let r1 = Arc::clone(&data);
    let r2 = Arc::clone(&data);

    let handle1 = thread::spawn(move || {
        let read = r1.read().unwrap();
        println!("Reader 1: {:?}", *read);
    });

    let handle2 = thread::spawn(move || {
        let read = r2.read().unwrap();
        println!("Reader 2: {:?}", *read);
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
}
```

#### 2.2.2 消息传递语义

消息传递遵循所有权转移语义：

$$
\text{Channel} : T \to \text{Sender}\langle T \rangle \times \text{Receiver}\langle T \rangle \quad \text{where } \text{Send}(T)
$$

```rust
use std::sync::mpsc;
use std::thread;

fn message_passing_semantics() {
    // 创建通道
    let (tx, rx) = mpsc::channel::<String>();

    // 生产者线程
    let tx2 = tx.clone();
    thread::spawn(move || {
        let data = String::from("owned data");
        tx.send(data).unwrap();
        // data 的所有权已转移，不能再使用
        // println!("{}", data);  // 编译错误！
    });

    // 另一个生产者
    thread::spawn(move || {
        tx2.send(String::from("more data")).unwrap();
    });

    // 消费者
    drop(tx);  // 关闭发送端

    for msg in rx {
        println!("Received: {}", msg);
    }
    println!("Channel closed");
}

// 同步通道语义
fn sync_channel_semantics() {
    // 缓冲区大小为 0 的同步通道（ Rendezvous 语义）
    let (tx, rx) = mpsc::sync_channel::<i32>(0);

    thread::spawn(move || {
        println!("Sending...");
        tx.send(42).unwrap();  // 阻塞，直到接收者就绪
        println!("Sent!");
    });

    thread::sleep(std::time::Duration::from_millis(100));
    println!("Receiving...");
    let value = rx.recv().unwrap();
    println!("Received: {}", value);
}
```

#### 2.2.3 内存序语义

内存序定义了原子操作之间的可见性关系：

$$
\text{MemoryOrder} \in \{ \text{Relaxed}, \text{Acquire}, \text{Release}, \text{AcqRel}, \text{SeqCst} \}
$$

| 内存序 | 含义 | 使用场景 |
|-------|------|---------|
| `Relaxed` | 仅原子性 | 计数器、标志位 |
| `Acquire` | 获取语义 | 读取锁状态 |
| `Release` | 释放语义 | 释放锁状态 |
| `AcqRel` | 获取+释放 | CAS 操作 |
| `SeqCst` | 顺序一致性 | 严格同步要求 |

```rust
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::thread;

fn memory_order_semantics() {
    // Acquire-Release 语义示例
    let data = AtomicI32::new(0);
    let ready = AtomicBool::new(false);

    thread::scope(|s| {
        s.spawn(|| {
            // 写入数据
            data.store(42, Ordering::Relaxed);
            // Release: 确保前面的写操作对后续 Acquire 可见
            ready.store(true, Ordering::Release);
        });

        s.spawn(|| {
            // Acquire: 确保看到 Release 之前的所有写操作
            while !ready.load(Ordering::Acquire) {
                thread::yield_now();
            }
            // 保证看到 data = 42
            assert_eq!(data.load(Ordering::Relaxed), 42);
            println!("Data visible: {}", data.load(Ordering::Relaxed));
        });
    });
}
```

### 2.3 线程安全边界语义

#### 2.3.1 Send 边界语义

Send 边界定义了类型可以安全跨线程转移的界限：

$$
\text{SendBound} : \forall T. (\forall t \subseteq T. \text{Send}(t)) \implies \text{Send}(T)
$$

```rust
// 自动派生 Send
#[derive(Clone)]
struct SafeToSend {
    data: String,
    value: i32,
}

// 包含非 Send 字段
struct NotSafeToSend {
    ptr: *const u8,  // 原始指针不是 Send
}

// 手动实现 Send（需要 unsafe，且必须保证线程安全）
// unsafe impl Send for NotSafeToSend {}

// 泛型类型的 Send 边界
struct Container<T>(T);

// T: Send 时 Container<T>: Send
unsafe impl<T: Send> Send for Container<T> {}
```

#### 2.3.2 Sync 边界语义

Sync 边界定义了类型可以安全跨线程共享引用的界限：

$$
\text{SyncBound} : T : \text{Sync} \iff \&T : \text{Send}
$$

```rust
use std::cell::RefCell;
use std::sync::Mutex;

// Sync 示例：可以被多个线程同时引用
struct SafeToSync {
    data: Mutex<i32>,  // Mutex 提供内部同步
}

// 非 Sync：RefCell 不提供线程安全
struct NotSafeToSync {
    data: RefCell<i32>,
}

// 手动实现 Sync（需要 unsafe）
struct MySyncType {
    // 内部使用原子操作保证线程安全
}

unsafe impl Sync for MySyncType {}
```

#### 2.3.3 !Send 和 !Sync 语义

标记类型为 `!Send` 或 `!Sync` 是显式的安全声明：

```rust
use std::marker::PhantomData;
use std::rc::Rc;

// 标记类型为 !Send
struct ThreadBound {
    // PhantomData<*const ()> 标记为 !Send
    _marker: PhantomData<*const ()>,
}

// Rc<T> 是 !Send 且 !Sync
check_send_sync::<Rc<i32>>();

// 检查类型是否实现 Send/Sync 的辅助函数
fn check_send_sync<T: Send + Sync>() {}
fn check_not_send<T>() {}
fn check_not_sync<T>() {}
```

---

## 3. 同步原语语义

### 3.1 互斥锁语义 (Mutex)

#### 3.1.1 锁获取语义

互斥锁提供独占访问保证：

$$
\text{MutexAcquire} : \text{Mutex}\langle T \rangle \to \text{MutexGuard}\langle T \rangle \quad \text{（阻塞直到获取）}
$$

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn mutex_acquire_semantics() {
    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            // lock() 获取互斥锁
            // 语义：当前线程独占访问 data
            let mut guard = data.lock().unwrap();

            // 临界区开始
            *guard += 1;
            // 临界区结束

            // guard 在这里 drop，自动释放锁
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(*data.lock().unwrap(), 10);
}
```

#### 3.1.2 锁释放语义

锁释放遵循 RAII（资源获取即初始化）模式：

$$
\text{MutexRelease} : \text{MutexGuard}\langle T \rangle \to () \quad \text{（Drop 时自动释放）}
$$

```rust
use std::sync::Mutex;

fn mutex_release_semantics() {
    let data = Mutex::new(vec![1, 2, 3]);

    {
        let mut guard = data.lock().unwrap();
        guard.push(4);
        // guard 在这里离开作用域，锁自动释放
    }

    // 可以再次获取锁
    let guard = data.lock().unwrap();
    println!("{:?}", *guard);

    // 手动 drop（不推荐，除非需要精确控制）
    drop(guard);
}
```

#### 3.1.3 死锁避免语义

Rust 的类型系统和所有权机制帮助避免某些类型的死锁：

```rust
use std::sync::{Mutex, TryLockError};

fn deadlock_prevention() {
    let m1 = Mutex::new(1);
    let m2 = Mutex::new(2);

    // 潜在死锁场景（Rust 无法静态避免）
    // 线程 A: lock m1 -> lock m2
    // 线程 B: lock m2 -> lock m1

    // 死锁避免策略 1：固定顺序获取
    fn safe_lock_order() {
        let m1 = Mutex::new(1);
        let m2 = Mutex::new(2);

        // 总是先获取 m1，再获取 m2
        let _g1 = m1.lock().unwrap();
        let _g2 = m2.lock().unwrap();
    }

    // 死锁避免策略 2：try_lock 超时
    fn try_lock_timeout() {
        let m1 = Mutex::new(1);

        match m1.try_lock() {
            Ok(guard) => {
                println!("Got lock: {}", *guard);
            }
            Err(TryLockError::WouldBlock) => {
                println!("Lock would block, doing other work");
            }
            Err(TryLockError::Poisoned(e)) => {
                println!("Lock poisoned: {}", e);
            }
        }
    }
}
```

#### 3.1.4 锁守卫语义

`MutexGuard` 提供安全的锁管理：

$$
\text{MutexGuard}\langle T \rangle : \text{Deref}(T) \times \text{DerefMut}(T) \times \text{Drop}()
$$

```rust
use std::sync::{Mutex, MutexGuard};
use std::ops::Deref;

fn guard_semantics() {
    let data = Mutex::new(String::from("hello"));

    // guard 实现 Deref 和 DerefMut
    let mut guard: MutexGuard<String> = data.lock().unwrap();

    // 通过 Deref 访问内部数据
    guard.push_str(" world");

    // 可以通过 &*guard 获取 &T
    let str_ref: &str = &*guard;
    println!("{}", str_ref);

    // guard 离开作用域自动释放锁
    drop(guard);
}
```

### 3.2 读写锁语义 (RwLock)

#### 3.2.1 读锁共享语义

读写锁允许多个读者并发访问：

$$
\text{ReadLock} : \text{RwLock}\langle T \rangle \to \text{RwLockReadGuard}\langle T \rangle \quad \text{（多个读者允许）}
$$

```rust
use std::sync::{Arc, RwLock};
use std::thread;

fn read_lock_semantics() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];

    // 启动多个读者
    for i in 0..5 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let read_guard = data.read().unwrap();
            println!("Reader {} sees: {:?}", i, *read_guard);
            // 多个读锁可以同时持有
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
}
```

#### 3.2.2 写锁独占语义

写锁提供独占的写访问：

$$
\text{WriteLock} : \text{RwLock}\langle T \rangle \to \text{RwLockWriteGuard}\langle T \rangle \quad \text{（独占访问）}
$$

```rust
fn write_lock_semantics() {
    let data = RwLock::new(0);

    {
        let mut write_guard = data.write().unwrap();
        *write_guard = 42;
        // 写锁独占：此时不允许任何读锁或写锁
    }

    println!("Value: {}", *data.read().unwrap());
}
```

#### 3.2.3 锁升级/降级语义

RwLock 不支持直接的锁升级（读锁 -> 写锁），需要显式释放和重新获取：

```rust
fn lock_upgrade_semantics() {
    let data = RwLock::new(vec![1, 2, 3]);

    // 先获取读锁检查条件
    let needs_update = {
        let read_guard = data.read().unwrap();
        read_guard.len() < 5
    };  // 读锁在这里释放

    // 如果需要，获取写锁
    if needs_update {
        let mut write_guard = data.write().unwrap();
        write_guard.push(4);
    }

    println!("{:?}", data.read().unwrap());
}

// 锁降级（写锁 -> 读锁）
fn lock_downgrade_semantics() {
    let data = RwLock::new(vec![1, 2, 3]);

    let read_guard = {
        let mut write_guard = data.write().unwrap();
        write_guard.push(4);
        // 降级为读锁
        RwLockWriteGuard::downgrade(write_guard)
    };

    println!("{:?}", *read_guard);
}
```

#### 3.2.4 读偏好 vs 写偏好

不同 RwLock 实现对读者和写者的偏好不同：

| 实现 | 偏好 | 特点 |
|-----|------|------|
| `std::sync::RwLock` | 实现相关 | 依赖 OS 实现 |
| `parking_lot::RwLock` | 写偏好 | 防止写者饥饿 |

```rust
// parking_lot 提供更公平的锁
use parking_lot::RwLock;

fn fair_rwlock() {
    let lock = RwLock::new(0);

    // parking_lot 默认倾向于防止写者饥饿
    let _read = lock.read();
    // 即使有等待的写者，新读者也可能被阻塞
}
```

### 3.3 条件变量语义 (Condvar)

#### 3.3.1 等待语义

条件变量用于线程间的条件等待：

$$
\text{Wait} : \text{Condvar} \times \text{MutexGuard}\langle T \rangle \to \text{MutexGuard}\langle T \rangle
$$

```rust
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

fn wait_semantics() {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair2 = Arc::clone(&pair);

    thread::spawn(move || {
        let (lock, cvar) = &*pair2;
        thread::sleep(Duration::from_millis(100));

        let mut started = lock.lock().unwrap();
        *started = true;
        cvar.notify_one();  // 通知等待者
    });

    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();

    // 等待条件变为 true
    // 语义：原子释放锁 + 阻塞 + 被唤醒后重新获取锁
    while !*started {
        started = cvar.wait(started).unwrap();
    }

    println!("Condition met!");
}
```

#### 3.3.2 通知语义

条件变量支持两种通知方式：

```rust
use std::sync::{Condvar, Mutex};

fn notify_semantics() {
    let pair = Arc::new((Mutex::new(0), Condvar::new()));

    // notify_one: 唤醒一个等待者
    fn notify_one_example(cvar: &Condvar) {
        cvar.notify_one();
    }

    // notify_all: 唤醒所有等待者
    fn notify_all_example(cvar: &Condvar) {
        cvar.notify_all();
    }
}
```

#### 3.3.3 虚假唤醒处理

条件变量可能产生虚假唤醒，必须使用循环检查：

```rust
fn spurious_wakeup_handling() {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));

    let (lock, cvar) = &*pair;
    let mut ready = lock.lock().unwrap();

    // 必须使用 while 循环，而不是 if
    while !*ready {
        ready = cvar.wait(ready).unwrap();
        // 即使被唤醒，条件可能仍不满足
        // 循环确保条件确实满足
    }
}
```

#### 3.3.4 与锁的组合语义

Condvar 必须与 Mutex 一起使用：

$$
\text{Condvar} \times \text{Mutex}\langle T \rangle \to \text{SynchronizationPoint}
$$

```rust
use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex};

// 条件变量 + 互斥锁的常见模式：阻塞队列
struct BlockingQueue<T> {
    queue: Mutex<VecDeque<T>>,
    not_empty: Condvar,
}

impl<T> BlockingQueue<T> {
    fn new() -> Self {
        BlockingQueue {
            queue: Mutex::new(VecDeque::new()),
            not_empty: Condvar::new(),
        }
    }

    fn push(&self, item: T) {
        let mut queue = self.queue.lock().unwrap();
        queue.push_back(item);
        self.not_empty.notify_one();
    }

    fn pop(&self) -> T {
        let mut queue = self.queue.lock().unwrap();

        while queue.is_empty() {
            queue = self.not_empty.wait(queue).unwrap();
        }

        queue.pop_front().unwrap()
    }
}
```

### 3.4 屏障语义 (Barrier)

#### 3.4.1 同步点语义

屏障用于同步多个线程到达某点：

$$
\text{Barrier} : n \to \text{BarrierWait} \quad \text{（n 个线程到达后继续）}
$$

```rust
use std::sync::{Arc, Barrier};
use std::thread;

fn barrier_sync_semantics() {
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];

    for i in 0..3 {
        let barrier = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            println!("Thread {}: before barrier", i);

            // 等待所有线程到达
            barrier.wait();

            println!("Thread {}: after barrier", i);
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
}
```

#### 3.4.2 分阶段执行语义

屏障可以重置用于多阶段同步：

```rust
fn phased_execution() {
    let barrier = Arc::new(Barrier::new(3));

    thread::scope(|s| {
        for i in 0..3 {
            let barrier = Arc::clone(&barrier);
            s.spawn(move || {
                // 阶段 1
                println!("Thread {}: Phase 1", i);
                barrier.wait();

                // 阶段 2
                println!("Thread {}: Phase 2", i);
                barrier.wait();

                // 阶段 3
                println!("Thread {}: Phase 3", i);
            });
        }
    });
}
```

#### 3.4.3 领导者选举语义

屏障的返回值可以标识"领导者"线程：

```rust
use std::sync::BarrierWaitResult;

fn leader_election() {
    let barrier = Arc::new(Barrier::new(3));

    thread::scope(|s| {
        for i in 0..3 {
            let barrier = Arc::clone(&barrier);
            s.spawn(move || {
                let result = barrier.wait();

                if result.is_leader() {
                    println!("Thread {} is the leader", i);
                    // 领导者执行特殊任务
                } else {
                    println!("Thread {} is a follower", i);
                }
            });
        }
    });
}
```

---

## 4. 无锁并发语义

### 4.1 原子操作语义

#### 4.1.1 原子读写语义

原子操作保证操作的不可分性：

$$
\text{AtomicOp} : \text{Location} \times \text{Value} \to \text{Result} \quad \text{（原子执行）}
$$

```rust
use std::sync::atomic::{AtomicI32, AtomicUsize, Ordering};

fn atomic_read_write_semantics() {
    let counter = AtomicI32::new(0);

    // 原子读取
    let value = counter.load(Ordering::Relaxed);
    println!("Current value: {}", value);

    // 原子写入
    counter.store(42, Ordering::Relaxed);

    // 原子读取-修改-写入
    let old = counter.fetch_add(1, Ordering::Relaxed);
    println!("Old value: {}, New value: {}", old, counter.load(Ordering::Relaxed));
}
```

#### 4.1.2 原子 CAS 语义

比较并交换（Compare-And-Swap）是无锁算法的基石：

$$
\text{CAS}(location, expected, new) = \begin{cases}
\text{Ok}(()) & \text{if } *location = expected \land *location := new \\
\text{Err}(actual) & \text{otherwise}
\end{cases}
$$

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

fn cas_semantics() {
    let ptr = AtomicPtr::new(1 as *mut i32);

    // CAS 操作
    let old = ptr.load(Ordering::Relaxed);
    let new = 2 as *mut i32;

    match ptr.compare_exchange(old, new, Ordering::SeqCst, Ordering::Relaxed) {
        Ok(_) => println!("CAS succeeded"),
        Err(current) => println!("CAS failed, current value: {:?}", current),
    }

    // compare_exchange_weak：允许伪失败（更高效的循环）
    loop {
        let current = ptr.load(Ordering::Relaxed);
        match ptr.compare_exchange_weak(
            current,
            new,
            Ordering::Release,
            Ordering::Relaxed,
        ) {
            Ok(_) => break,
            Err(_) => continue,
        }
    }
}
```

#### 4.1.3 原子 fetch-and-update 语义

```rust
use std::sync::atomic::{AtomicI32, Ordering};

fn fetch_update_semantics() {
    let value = AtomicI32::new(5);

    // fetch_add / fetch_sub
    let prev = value.fetch_add(10, Ordering::Relaxed);
    println!("Previous: {}, Current: {}", prev, value.load(Ordering::Relaxed));

    // fetch_and / fetch_or / fetch_xor
    let flags = AtomicI32::new(0b1010);
    flags.fetch_or(0b0100, Ordering::Relaxed);
    println!("Flags: {:b}", flags.load(Ordering::Relaxed));

    // fetch_max / fetch_min (Rust 1.45+)
    let max = AtomicI32::new(10);
    max.fetch_max(20, Ordering::Relaxed);
    println!("Max: {}", max.load(Ordering::Relaxed));
}
```

### 4.2 内存序语义

#### 4.2.1 Relaxed 语义

Relaxed 只保证原子性，不保证顺序：

$$
\text{Relaxed} : \text{AtomicityOnly} \quad \text{（无 happens-before 关系）}
$$

```rust
use std::sync::atomic::{AtomicI32, Ordering};
use std::thread;

fn relaxed_semantics() {
    let x = AtomicI32::new(0);
    let y = AtomicI32::new(0);

    thread::scope(|s| {
        s.spawn(|| {
            x.store(1, Ordering::Relaxed);
            y.store(1, Ordering::Relaxed);
        });

        s.spawn(|| {
            let r1 = y.load(Ordering::Relaxed);
            let r2 = x.load(Ordering::Relaxed);
            // 可能的输出：r1 = 1, r2 = 0（重排序）
            println!("r1: {}, r2: {}", r1, r2);
        });
    });
}
```

#### 4.2.2 Acquire/Release 语义

Acquire-Release 建立 happens-before 关系：

$$
\begin{aligned}
\text{Release} &: \text{writes-before} \prec \text{store} \\
\text{Acquire} &: \text{load} \prec \text{reads-after}
\end{aligned}
$$

```rust
fn acquire_release_semantics() {
    use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};

    let data = AtomicI32::new(0);
    let ready = AtomicBool::new(false);

    thread::scope(|s| {
        s.spawn(|| {
            data.store(42, Ordering::Relaxed);
            // Release: 确保 data = 42 对后续的 Acquire 可见
            ready.store(true, Ordering::Release);
        });

        s.spawn(|| {
            // Acquire: 确保看到 Release 之前的写操作
            while !ready.load(Ordering::Acquire) {
                thread::yield_now();
            }
            // 保证看到 data = 42
            assert_eq!(data.load(Ordering::Relaxed), 42);
        });
    });
}
```

#### 4.2.3 SeqCst 语义

顺序一致性是最强的内存序：

$$
\text{SeqCst} : \text{TotalOrder} \quad \text{（所有线程看到一致的操作顺序）}
$$

```rust
fn seq_cst_semantics() {
    use std::sync::atomic::{fence, AtomicI32, Ordering};

    let x = AtomicI32::new(0);
    let y = AtomicI32::new(0);

    thread::scope(|s| {
        s.spawn(|| {
            x.store(1, Ordering::SeqCst);
            let r1 = y.load(Ordering::SeqCst);
            println!("Thread 1: r1 = {}", r1);
        });

        s.spawn(|| {
            y.store(1, Ordering::SeqCst);
            let r2 = x.load(Ordering::SeqCst);
            println!("Thread 2: r2 = {}", r2);
        });
    });

    // SeqCst 保证：不可能同时 r1 = 0 且 r2 = 0
}
```

#### 4.2.4 happens-before 关系

happens-before 是并发程序正确性的核心概念：

$$
e_1 \prec e_2 \iff \text{visible}(e_1, e_2)
$$

```rust
fn happens_before_demo() {
    use std::sync::atomic::{AtomicI32, Ordering};

    let x = AtomicI32::new(0);
    let y = AtomicI32::new(0);
    let z = AtomicI32::new(0);

    // 程序序（Program Order）
    x.store(1, Ordering::Relaxed);  // A
    y.store(1, Ordering::Release);  // B

    // A happens-before B（程序序）
    // Release 操作 happens-before 对应的 Acquire

    thread::scope(|s| {
        s.spawn(|| {
            if y.load(Ordering::Acquire) == 1 {  // C
                // B happens-before C
                // 因此 A happens-before C
                z.store(x.load(Ordering::Relaxed), Ordering::Relaxed);  // D
                // A 的写对 D 可见
            }
        });
    });
}
```

### 4.3 无锁数据结构语义

#### 4.3.1 无锁队列语义

无锁队列使用 CAS 操作实现线程安全的入队和出队：

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
}

struct LockFreeQueue<T> {
    head: AtomicPtr<Node<T>>,
    tail: AtomicPtr<Node<T>>,
}

impl<T> LockFreeQueue<T> {
    fn new() -> Self {
        let dummy = Box::into_raw(Box::new(Node {
            data: unsafe { std::mem::zeroed() },
            next: AtomicPtr::new(ptr::null_mut()),
        }));

        LockFreeQueue {
            head: AtomicPtr::new(dummy),
            tail: AtomicPtr::new(dummy),
        }
    }

    fn enqueue(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: AtomicPtr::new(ptr::null_mut()),
        }));

        loop {
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*tail).next.load(Ordering::Acquire) };

            if tail == self.tail.load(Ordering::Relaxed) {
                if next.is_null() {
                    if unsafe { (*tail).next.compare_exchange(
                        next,
                        new_node,
                        Ordering::Release,
                        Ordering::Relaxed,
                    ) }.is_ok() {
                        let _ = self.tail.compare_exchange(
                            tail,
                            new_node,
                            Ordering::Release,
                            Ordering::Relaxed,
                        );
                        return;
                    }
                } else {
                    let _ = self.tail.compare_exchange(
                        tail,
                        next,
                        Ordering::Release,
                        Ordering::Relaxed,
                    );
                }
            }
        }
    }
}
```

#### 4.3.2 无锁栈语义

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

impl<T> LockFreeStack<T> {
    fn new() -> Self {
        LockFreeStack {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: ptr::null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Relaxed);
            unsafe { (*new_node).next = head; }

            if self.head.compare_exchange_weak(
                head,
                new_node,
                Ordering::Release,
                Ordering::Relaxed,
            ).is_ok() {
                break;
            }
        }
    }

    fn pop(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            if head.is_null() {
                return None;
            }

            let next = unsafe { (*head).next };

            if self.head.compare_exchange_weak(
                head,
                next,
                Ordering::Release,
                Ordering::Relaxed,
            ).is_ok() {
                let node = unsafe { Box::from_raw(head) };
                return Some(node.data);
            }
        }
    }
}
```

#### 4.3.3 无锁哈希表语义

```rust
// 简化示例：基于分段锁的"几乎无锁"哈希表
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

struct ShardedHashTable<K, V> {
    shards: Vec<Mutex<HashMap<K, V>>>,
    mask: usize,
}

impl<K: Hash + Eq, V> ShardedHashTable<K, V> {
    fn with_shards(num_shards: usize) -> Self {
        let num_shards = num_shards.next_power_of_two();
        let mut shards = Vec::with_capacity(num_shards);
        for _ in 0..num_shards {
            shards.push(Mutex::new(HashMap::new()));
        }

        ShardedHashTable {
            shards,
            mask: num_shards - 1,
        }
    }

    fn get_shard(&self, key: &K) -> &Mutex<HashMap<K, V>> {
        let hash = self.hash(key);
        &self.shards[hash & self.mask]
    }

    fn hash(&self, key: &K) -> usize {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish() as usize
    }
}

use std::collections::HashMap;
use std::hash::Hash;
```

#### 4.3.4 ABA 问题与解决方案

ABA 问题是无锁算法中的经典问题：

```rust
// ABA 问题示例
// 线程1：读取 A
// 线程2：A -> B -> A
// 线程1：CAS(A, new) 成功，但状态已改变

// 解决方案 1：使用标记指针（Tagged Pointer）
use std::sync::atomic::{AtomicU64, Ordering};

struct TaggedPointer<T> {
    ptr_and_tag: AtomicU64,
    _marker: std::marker::PhantomData<T>,
}

impl<T> TaggedPointer<T> {
    fn new(ptr: *mut T) -> Self {
        TaggedPointer {
            ptr_and_tag: AtomicU64::new(ptr as u64),
            _marker: std::marker::PhantomData,
        }
    }

    fn load(&self, ordering: Ordering) -> (*mut T, u16) {
        let value = self.ptr_and_tag.load(ordering);
        let ptr = (value & !0xFFFF) as *mut T;
        let tag = (value & 0xFFFF) as u16;
        (ptr, tag)
    }

    fn compare_exchange(&self, old: (*mut T, u16), new: *mut T, ordering: Ordering) -> Result<(), (*mut T, u16)> {
        let old_value = ((old.0 as u64) & !0xFFFF) | (old.1 as u64);
        let new_value = ((new as u64) & !0xFFFF) | ((old.1.wrapping_add(1)) as u64);

        self.ptr_and_tag.compare_exchange(old_value, new_value, ordering, Ordering::Relaxed)
            .map_err(|v| (((v & !0xFFFF) as *mut T), (v & 0xFFFF) as u16))
            .map(|_| ())
    }
}

// 解决方案 2：使用 hazard pointer（crossbeam-epoch）
use crossbeam_epoch::{self as epoch, Atomic, Owned};

fn hazard_pointer_example() {
    let head = Atomic::new(42);

    let guard = &epoch::pin();
    let shared = head.load(Ordering::Acquire, guard);

    // 安全地访问共享数据
    if let Some(value) = unsafe { shared.as_ref() } {
        println!("Value: {}", value);
    }

    // guard 保护期间，数据不会被释放
}
```

---

## 5. 数据并行语义

### 5.1 迭代器并行语义

#### 5.1.1 par_iter 语义

Rayon 的 `par_iter` 提供声明式的数据并行：

$$
\text{ParIter} : \text{Iterator}\langle T \rangle \to \text{ParallelIterator}\langle T \rangle
$$

```rust
use rayon::prelude::*;

fn par_iter_semantics() {
    let data: Vec<i32> = (0..10000).collect();

    // 并行迭代
    let sum: i32 = data.par_iter()
        .map(|x| x * x)
        .sum();

    println!("Sum: {}", sum);

    // 并行过滤
    let evens: Vec<i32> = data.par_iter()
        .filter(|&&x| x % 2 == 0)
        .cloned()
        .collect();

    println!("Evens count: {}", evens.len());
}
```

#### 5.1.2 分块策略语义

```rust
fn chunking_semantics() {
    let data: Vec<i32> = (0..1000).collect();

    // 自动分块策略
    let sum = data.par_iter()
        .with_min_len(100)   // 最小块大小
        .with_max_len(500)   // 最大块大小
        .map(|x| x * 2)
        .sum::<i32>();

    // 手动分块
    let chunked_sum: i32 = data.par_chunks(100)
        .map(|chunk| chunk.iter().sum::<i32>())
        .sum();

    println!("Sum: {}, Chunked sum: {}", sum, chunked_sum);
}
```

#### 5.1.3 工作窃取语义

工作窃取调度器动态平衡负载：

```rust
// Rayon 使用工作窃取调度器
// 每个线程有自己的工作队列
// 空闲线程从繁忙线程"窃取"工作

fn work_stealing_demo() {
    let data: Vec<i32> = (0..1_000_000).collect();

    // 不平衡的计算负载
    let result: i64 = data.par_iter()
        .map(|&x| {
            // 模拟不平衡的计算
            let work = if x % 1000 == 0 { 1000 } else { 1 };
            (0..work).map(|i| i as i64 * x as i64).sum::<i64>()
        })
        .sum();

    println!("Result: {}", result);
}
```

### 5.2 数据竞争自由语义

#### 5.2.1 只读并行语义

只读并行是安全的，因为无数据修改：

$$
\forall x \in \text{Data}. \text{ReadOnly}(x) \implies \text{SafeParallel}(\text{read}(x))
$$

```rust
fn readonly_parallel_semantics() {
    let data = vec![1, 2, 3, 4, 5];

    // 多个线程只读访问是安全的
    let sum: i32 = data.par_iter().sum();
    let max = *data.par_iter().max().unwrap();
    let count = data.par_iter().filter(|&&x| x > 2).count();

    println!("Sum: {}, Max: {}, Count: {}", sum, max, count);
}
```

#### 5.2.2 互斥写语义

写操作需要互斥或分片：

```rust
use rayon::prelude::*;

fn exclusive_write_semantics() {
    // 方案 1：使用原子操作
    use std::sync::atomic::{AtomicUsize, Ordering};

    let counter = AtomicUsize::new(0);
    let data: Vec<i32> = (0..1000).collect();

    data.par_iter().for_each(|_| {
        counter.fetch_add(1, Ordering::Relaxed);
    });

    println!("Counter: {}", counter.load(Ordering::Relaxed));

    // 方案 2：使用 fold + reduce（推荐）
    let sum = data.par_iter()
        .fold(|| 0, |acc, &x| acc + x)
        .reduce(|| 0, |a, b| a + b);

    println!("Sum: {}", sum);
}
```

#### 5.2.3 归约操作语义

```rust
fn reduction_semantics() {
    let data: Vec<i32> = (0..1000).collect();

    // 并行归约
    let sum = data.par_iter().sum::<i32>();
    let product = data.par_iter().product::<i32>();
    let max = data.par_iter().max().unwrap();
    let min = data.par_iter().min().unwrap();

    // 自定义归约
    let (sum, count) = data.par_iter()
        .filter(|&&x| x % 2 == 0)
        .map(|&x| (x, 1))
        .reduce(|| (0, 0), |a, b| (a.0 + b.0, a.1 + b.1));

    println!("Sum: {}, Count: {}", sum, count);
}
```

---

## 6. 并发控制流语义

### 6.1 分叉-汇合语义 (Fork-Join)

#### 6.1.1 作用域线程语义

作用域线程允许借用非 `'static` 数据：

$$
\text{Scope} : \text{ThreadSet} \times \text{Lifetime} \to \text{JoinGuard}
$$

```rust
use std::thread;

fn scoped_thread_semantics() {
    let mut data = vec![1, 2, 3, 4, 5];

    // 作用域线程可以借用非 'static 数据
    thread::scope(|s| {
        s.spawn(|| {
            println!("Thread 1: {:?}", data);
        });

        s.spawn(|| {
            // 甚至可以修改数据（如果同步允许）
            for x in &mut data {
                *x *= 2;
            }
        });
    });

    // scope 结束后，所有线程已 join
    println!("Final data: {:?}", data);
}
```

#### 6.1.2 跨作用域借用语义

```rust
fn cross_scope_borrowing() {
    let data = vec![1, 2, 3];
    let results: Vec<_> = thread::scope(|s| {
        let mut handles = vec![];

        for i in 0..3 {
            handles.push(s.spawn(move || {
                data.get(i).copied().unwrap_or(0)
            }));
        }

        handles.into_iter()
            .map(|h| h.join().unwrap())
            .collect()
    });

    println!("Results: {:?}", results);
}
```

#### 6.1.3 Rayon 并行模式

```rust
use rayon::prelude::*;

fn rayon_parallel_patterns() {
    let data: Vec<i32> = (0..1000).collect();

    // join：分叉-汇合
    let (sum, max) = rayon::join(
        || data.iter().sum::<i32>(),
        || *data.iter().max().unwrap(),
    );

    println!("Sum: {}, Max: {}", sum, max);

    // 递归分叉-汇合
    fn parallel_sum(data: &[i32]) -> i32 {
        if data.len() <= 1000 {
            data.iter().sum()
        } else {
            let mid = data.len() / 2;
            let (left, right) = rayon::join(
                || parallel_sum(&data[..mid]),
                || parallel_sum(&data[mid..]),
            );
            left + right
        }
    }

    println!("Parallel sum: {}", parallel_sum(&data));
}
```

### 6.2 生产者-消费者语义

#### 6.2.1 管道语义

```rust
use std::sync::mpsc;
use std::thread;

fn pipeline_semantics() {
    // 阶段 1 -> 阶段 2 -> 阶段 3
    let (tx1, rx1) = mpsc::channel::<i32>();
    let (tx2, rx2) = mpsc::channel::<String>();

    // 生产者
    thread::spawn(move || {
        for i in 0..10 {
            tx1.send(i).unwrap();
        }
    });

    // 处理者
    thread::spawn(move || {
        for i in rx1 {
            let result = format!("Processed: {}", i * i);
            tx2.send(result).unwrap();
        }
    });

    // 消费者
    for result in rx2 {
        println!("{}", result);
    }
}
```

#### 6.2.2 背压语义

```rust
fn backpressure_semantics() {
    use std::sync::mpsc::sync_channel;

    // 有限缓冲区通道（背压）
    let (tx, rx) = sync_channel::<i32>(10);

    thread::spawn(move || {
        for i in 0..100 {
            // 当缓冲区满时阻塞
            tx.send(i).unwrap();
            println!("Sent: {}", i);
        }
    });

    // 慢速消费者
    for i in rx {
        thread::sleep(std::time::Duration::from_millis(100));
        println!("Received: {}", i);
    }
}
```

#### 6.2.3 流控制语义

```rust
fn flow_control_semantics() {
    use std::sync::mpsc;

    let (tx, rx) = mpsc::channel::<i32>();

    // 批量处理
    thread::spawn(move || {
        let mut batch = vec![];

        for item in rx {
            batch.push(item);

            if batch.len() >= 10 {
                // 处理批次
                println!("Processing batch: {:?}", batch);
                batch.clear();
            }
        }

        // 处理剩余
        if !batch.is_empty() {
            println!("Processing final batch: {:?}", batch);
        }
    });

    for i in 0..25 {
        tx.send(i).unwrap();
    }

    drop(tx);  // 关闭通道
}
```

### 6.3 读者-写者语义

#### 6.3.1 多读单写语义

```rust
use std::sync::RwLock;
use std::thread;

fn read_write_semantics() {
    let data = RwLock::new(vec![1, 2, 3]);

    // 多个读者并发
    thread::scope(|s| {
        for i in 0..5 {
            s.spawn(|| {
                let read = data.read().unwrap();
                println!("Reader {}: {:?}", i, *read);
            });
        }

        // 写者独占
        s.spawn(|| {
            let mut write = data.write().unwrap();
            write.push(4);
            println!("Writer: pushed 4");
        });
    });
}
```

#### 6.3.2 锁优化语义

```rust
// 读优化：使用 Arc 和原子操作
use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::Arc;

struct ReadOptimized<T> {
    ptr: AtomicPtr<T>,
}

impl<T> ReadOptimized<T> {
    fn read(&self) -> &T {
        // 无锁读取
        unsafe { &*self.ptr.load(Ordering::Acquire) }
    }

    fn write(&self, new_value: Box<T>) {
        let old = self.ptr.swap(Box::into_raw(new_value), Ordering::Release);
        // 延迟释放 old（使用 hazard pointer）
    }
}
```

#### 6.3.3 公平性语义

```rust
use parking_lot::RwLock;  // 更公平的实现

fn fairness_semantics() {
    let lock = RwLock::new(0);

    // parking_lot::RwLock 默认倾向于防止写者饥饿
    // 即使有等待的写者，新读者也可能被阻塞
}
```

---

## 7. 并发错误处理语义

### 7.1 恐慌传播语义

#### 7.1.1 线程间恐慌传播

```rust
use std::panic;
use std::thread;

fn panic_propagation_semantics() {
    let handle = thread::spawn(|| {
        panic!("Thread panic!");
    });

    // join 返回 Err，包含恐慌信息
    match handle.join() {
        Ok(result) => println!("Success: {:?}", result),
        Err(e) => println!("Thread panicked: {:?}", e),
    }
}
```

#### 7.1.2 恐慌恢复语义

```rust
fn panic_recovery_semantics() {
    let result = panic::catch_unwind(|| {
        // 可能恐慌的代码
        if true {
            panic!("Something went wrong");
        }
        42
    });

    match result {
        Ok(value) => println!("Got: {}", value),
        Err(_) => println!("Recovered from panic"),
    }
}
```

#### 7.1.3 作用域线程恐慌

```rust
fn scoped_thread_panic() {
    let result = thread::scope(|s| {
        s.spawn(|| {
            panic!("Scoped thread panic");
        });

        s.spawn(|| {
            42  // 这个线程正常完成
        });
    });

    // scope 在 panic 时会传播恐慌
}
```

### 7.2 超时语义

#### 7.2.1 锁超时语义

```rust
use std::sync::Mutex;
use std::time::Duration;

fn lock_timeout_semantics() {
    let lock = Mutex::new(0);

    // 标准库 Mutex 不支持超时，使用 parking_lot
    use parking_lot::Mutex as ParkingMutex;

    let lock = ParkingMutex::new(0);

    match lock.try_lock_for(Duration::from_millis(100)) {
        Some(guard) => println!("Got lock: {}", *guard),
        None => println!("Lock timeout"),
    }
}
```

#### 7.2.2 通道超时语义

```rust
use std::sync::mpsc;
use std::time::Duration;

fn channel_timeout_semantics() {
    let (tx, rx) = mpsc::channel::<i32>();

    match rx.recv_timeout(Duration::from_millis(100)) {
        Ok(value) => println!("Received: {}", value),
        Err(mpsc::RecvTimeoutError::Timeout) => println!("Timeout"),
        Err(mpsc::RecvTimeoutError::Disconnected) => println!("Channel closed"),
    }
}
```

#### 7.2.3 条件变量超时

```rust
use std::sync::{Condvar, Mutex};
use std::time::Duration;

fn condvar_timeout_semantics() {
    let pair = (Mutex::new(false), Condvar::new());

    let (lock, cvar) = &pair;
    let mut started = lock.lock().unwrap();

    // 带超时的等待
    let result = cvar.wait_timeout_while(
        started,
        Duration::from_millis(100),
        |started| !*started,
    ).unwrap();

    started = result.0;
    if result.1.timed_out() {
        println!("Wait timed out");
    } else {
        println!("Condition met");
    }
}
```

### 7.3 取消语义

#### 7.3.1 线程取消语义

Rust 不直接支持线程取消，需要协作式实现：

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

fn cooperative_cancellation() {
    let should_stop = Arc::new(AtomicBool::new(false));
    let should_stop_clone = Arc::clone(&should_stop);

    let handle = thread::spawn(move || {
        while !should_stop_clone.load(Ordering::Relaxed) {
            // 执行工作
            println!("Working...");
            thread::sleep(Duration::from_millis(100));
        }
        println!("Gracefully stopped");
    });

    thread::sleep(Duration::from_millis(500));
    should_stop.store(true, Ordering::Relaxed);
    handle.join().unwrap();
}
```

#### 7.3.2 协作取消语义

```rust
// 使用 select! 实现取消
fn select_cancellation() {
    use std::sync::mpsc;

    let (cancel_tx, cancel_rx) = mpsc::channel();
    let (work_tx, work_rx) = mpsc::channel();

    thread::spawn(move || {
        for i in 0..100 {
            work_tx.send(i).unwrap();
            thread::sleep(Duration::from_millis(50));
        }
    });

    // 取消信号
    thread::spawn(move || {
        thread::sleep(Duration::from_millis(200));
        cancel_tx.send(()).unwrap();
    });

    loop {
        match work_rx.recv_timeout(Duration::from_millis(100)) {
            Ok(value) => println!("Got: {}", value),
            Err(_) => {
                if cancel_rx.try_recv().is_ok() {
                    println!("Cancelled");
                    break;
                }
            }
        }
    }
}
```

#### 7.3.3 资源清理语义

```rust
fn resource_cleanup_semantics() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let counter = AtomicUsize::new(0);

    {
        struct Guard<'a>(&'a AtomicUsize);

        impl<'a> Drop for Guard<'a> {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::Relaxed);
                println!("Guard dropped, cleanup performed");
            }
        }

        let _guard = Guard(&counter);
        // 即使 panic，guard 也会被 drop
        // panic!("Something wrong");
    }  // Guard 在这里 drop

    assert_eq!(counter.load(Ordering::Relaxed), 1);
}
```

---

## 8. 并发数据流语义

### 8.1 共享状态数据流

#### 8.1.1 Arc<Mutex<T>> 语义

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn arc_mutex_semantics() {
    // Arc<Mutex<T>> 模式：共享可变状态
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let mut handles = vec![];

    for i in 0..5 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let mut locked = data.lock().unwrap();
            locked.push(i);
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    println!("Final: {:?}", data.lock().unwrap());
}
```

#### 8.1.2 读写分离语义

```rust
// 读写锁优化读多写少场景
use std::sync::{Arc, RwLock};

fn read_write_separation() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));

    // 大量读操作，少量写操作
    thread::scope(|s| {
        // 多个读者
        for i in 0..10 {
            let data = Arc::clone(&data);
            s.spawn(move || {
                let read = data.read().unwrap();
                println!("Reader {}: {:?}", i, *read);
            });
        }

        // 偶尔写
        s.spawn(|| {
            let mut write = data.write().unwrap();
            write.push(4);
        });
    });
}
```

#### 8.1.3 复制-on-写入语义

```rust
use std::sync::Arc;

fn cow_semantics() {
    // Arc 提供引用计数共享
    let data = Arc::new(vec![1, 2, 3]);

    // 只读共享
    let shared1 = Arc::clone(&data);
    let shared2 = Arc::clone(&data);

    // 需要修改时克隆（写时复制）
    let mut modified = (*data).clone();
    modified.push(4);

    println!("Original: {:?}", shared1);
    println!("Modified: {:?}", modified);
}
```

### 8.2 消息传递数据流

#### 8.2.1 通道数据流

```rust
use std::sync::mpsc;
use std::thread;

fn channel_dataflow() {
    let (tx, rx) = mpsc::channel();

    // 多生产者
    for i in 0..3 {
        let tx = tx.clone();
        thread::spawn(move || {
            for j in 0..5 {
                tx.send((i, j)).unwrap();
            }
        });
    }

    drop(tx);  // 关闭发送端

    // 单消费者
    for (producer, item) in rx {
        println!("From producer {}: item {}", producer, item);
    }
}
```

#### 8.2.2 Actor 消息流

```rust
// 简化 Actor 模型实现
use std::sync::mpsc::{self, Sender, Receiver};
use std::thread;

trait Actor {
    type Message;
    fn handle(&mut self, msg: Self::Message);
}

struct ActorSystem<T: Actor> {
    sender: Sender<T::Message>,
}

impl<T: Actor + Send + 'static> ActorSystem<T> {
    fn new(mut actor: T) -> Self {
        let (tx, rx): (Sender<T::Message>, Receiver<T::Message>) = mpsc::channel();

        thread::spawn(move || {
            for msg in rx {
                actor.handle(msg);
            }
        });

        ActorSystem { sender: tx }
    }

    fn send(&self, msg: T::Message) {
        self.sender.send(msg).unwrap();
    }
}

// 具体 Actor 实现
struct Counter {
    count: i32,
}

enum CounterMessage {
    Increment,
    Decrement,
    Get,
}

impl Actor for Counter {
    type Message = CounterMessage;

    fn handle(&mut self, msg: Self::Message) {
        match msg {
            CounterMessage::Increment => {
                self.count += 1;
                println!("Count: {}", self.count);
            }
            CounterMessage::Decrement => {
                self.count -= 1;
                println!("Count: {}", self.count);
            }
            CounterMessage::Get => {
                println!("Current count: {}", self.count);
            }
        }
    }
}

fn actor_example() {
    let counter = ActorSystem::new(Counter { count: 0 });

    counter.send(CounterMessage::Increment);
    counter.send(CounterMessage::Increment);
    counter.send(CounterMessage::Decrement);
    counter.send(CounterMessage::Get);
}
```

#### 8.2.3 事件驱动数据流

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

#[derive(Debug, Clone)]
enum Event {
    UserLogin(String),
    UserLogout(String),
    DataUpdate(i32),
}

fn event_driven_dataflow() {
    let (tx, rx) = mpsc::channel::<Event>();

    // 事件源
    let tx1 = tx.clone();
    thread::spawn(move || {
        tx1.send(Event::UserLogin("alice".to_string())).unwrap();
        thread::sleep(Duration::from_millis(100));
        tx1.send(Event::DataUpdate(42)).unwrap();
    });

    let tx2 = tx.clone();
    thread::spawn(move || {
        thread::sleep(Duration::from_millis(50));
        tx2.send(Event::UserLogin("bob".to_string())).unwrap();
        thread::sleep(Duration::from_millis(100));
        tx2.send(Event::UserLogout("alice".to_string())).unwrap();
    });

    drop(tx);

    // 事件处理器
    for event in rx {
        match event {
            Event::UserLogin(user) => println!("User logged in: {}", user),
            Event::UserLogout(user) => println!("User logged out: {}", user),
            Event::DataUpdate(data) => println!("Data updated: {}", data),
        }
    }
}
```

---

## 9. 并发运行时语义

### 9.1 线程池语义

#### 9.1.1 固定线程池语义

```rust
use rayon::ThreadPoolBuilder;

fn fixed_thread_pool_semantics() {
    // 创建固定大小的线程池
    let pool = ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap();

    // 在池内执行任务
    pool.install(|| {
        let sum: i32 = (0..1000).into_par_iter().sum();
        println!("Sum: {}", sum);
    });
}
```

#### 9.1.2 动态线程池语义

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::collections::VecDeque;

struct ThreadPool {
    workers: Vec<thread::JoinHandle<()>>,
    sender: std::sync::mpsc::Sender<Box<dyn FnOnce() + Send + 'static>>,
}

impl ThreadPool {
    fn new(size: usize) -> Self {
        let (sender, receiver) = std::sync::mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for _ in 0..size {
            let rx = Arc::clone(&receiver);
            workers.push(thread::spawn(move || {
                loop {
                    let job = rx.lock().unwrap().recv();
                    match job {
                        Ok(f) => f(),
                        Err(_) => break,
                    }
                }
            }));
        }

        ThreadPool { workers, sender }
    }

    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        self.sender.send(Box::new(f)).unwrap();
    }
}
```

#### 9.1.3 工作队列语义

```rust
// 工作窃取队列
use crossbeam::deque::{Worker, Stealer};

fn work_queue_semantics() {
    let worker = Worker::new_lifo();

    // 生产者推入任务
    worker.push(1);
    worker.push(2);
    worker.push(3);

    // 消费者弹出任务
    while let Some(task) = worker.pop() {
        println!("Processing: {}", task);
    }
}
```

### 9.2 调度器语义

#### 9.2.1 抢占式调度语义

```rust
// OS 线程是抢占式调度的
fn preemptive_scheduling() {
    use std::thread;

    let handle1 = thread::spawn(|| {
        for i in 0..5 {
            println!("Thread 1: {}", i);
            // 可能被抢占
        }
    });

    let handle2 = thread::spawn(|| {
        for i in 0..5 {
            println!("Thread 2: {}", i);
            // 可能被抢占
        }
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
}
```

#### 9.2.2 协作式调度语义

```rust
// async/await 是协作式调度的
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct YieldNow;

impl Future for YieldNow {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        cx.waker().wake_by_ref();
        Poll::Pending  // 让出执行权
    }
}

fn cooperative_scheduling() {
    // 在 async 函数中使用
    async fn task(id: i32) {
        for i in 0..5 {
            println!("Task {}: step {}", id, i);
            YieldNow.await;  // 协作式让出
        }
    }
}
```

#### 9.2.3 优先级调度语义

```rust
// Rust 标准库不直接支持线程优先级
// 可以使用第三方库或平台特定 API

#[cfg(target_os = "linux")]
fn priority_scheduling() {
    use std::thread;

    thread::spawn(|| {
        // Linux 特定的优先级设置
        unsafe {
            let mut param = libc::sched_param { sched_priority: 10 };
            libc::pthread_setschedparam(
                libc::pthread_self(),
                libc::SCHED_FIFO,
                &param,
            );
        }
    });
}
```

---

## 10. 并发程序验证

### 10.1 静态验证

#### 10.1.1 类型系统验证

Rust 的类型系统在编译时验证并发安全：

```rust
fn type_system_verification() {
    // 编译时检查：非 Send 类型不能跨线程
    let rc = std::rc::Rc::new(42);
    // std::thread::spawn(move || {
    //     println!("{}", rc);  // 编译错误：Rc 不是 Send
    // });

    // 编译时检查：非 Sync 类型不能共享引用
    let cell = std::cell::RefCell::new(42);
    // let r = &cell;
    // std::thread::spawn(move || {
    //     println!("{}", r.borrow());  // 编译错误：RefCell 不是 Sync
    // });
}
```

#### 10.1.2 借用检查验证

```rust
fn borrow_checking_verification() {
    let mut data = vec![1, 2, 3];

    // 编译时检查：不能同时持有可变和不可变引用
    let r1 = &data;
    // let r2 = &mut data;  // 编译错误！
    println!("{:?}", r1);

    // 编译时检查：引用不能比数据活得长
    // let r;
    // {
    //     let x = 5;
    //     r = &x;  // 编译错误：x 不够长
    // }
    // println!("{}", r);
}
```

#### 10.1.3 死锁检测

```rust
// 编译时无法检测所有死锁，需要运行时工具或代码审查

// 死锁模式示例（避免！）
fn deadlock_pattern() {
    let m1 = std::sync::Mutex::new(1);
    let m2 = std::sync::Mutex::new(2);

    // 线程 A
    std::thread::scope(|s| {
        s.spawn(|| {
            let _g1 = m1.lock().unwrap();
            std::thread::sleep(std::time::Duration::from_millis(10));
            let _g2 = m2.lock().unwrap();  // 可能死锁
        });

        // 线程 B
        s.spawn(|| {
            let _g2 = m2.lock().unwrap();
            std::thread::sleep(std::time::Duration::from_millis(10));
            let _g1 = m1.lock().unwrap();  // 可能死锁
        });
    });
}
```

### 10.2 动态验证

#### 10.2.1 数据竞争检测 (Miri)

```rust
// 使用 Miri 检测未定义行为和竞争条件
// cargo +nightly miri test

#[test]
fn miri_data_race_test() {
    use std::sync::atomic::{AtomicI32, Ordering};
    use std::thread;

    let x = AtomicI32::new(0);

    thread::scope(|s| {
        s.spawn(|| {
            x.fetch_add(1, Ordering::Relaxed);
        });
        s.spawn(|| {
            x.fetch_add(1, Ordering::Relaxed);
        });
    });

    assert_eq!(x.load(Ordering::Relaxed), 2);
}
```

#### 10.2.2 线程安全检查

```rust
// 使用 loom 进行模型检查
#[cfg(test)]
mod loom_tests {
    use loom::sync::atomic::AtomicUsize;
    use loom::thread;

    #[test]
    fn concurrent_increment() {
        loom::model(|| {
            let v = AtomicUsize::new(0);

            thread::spawn(|| {
                v.fetch_add(1, Ordering::SeqCst);
            });

            thread::spawn(|| {
                v.fetch_add(1, Ordering::SeqCst);
            });

            // loom 会检查所有可能的执行顺序
        });
    }
}
```

#### 10.2.3 性能分析

```rust
// 使用 criterion 进行并发基准测试
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use rayon::prelude::*;

fn parallel_sum(c: &mut Criterion) {
    let mut group = c.benchmark_group("parallel_sum");

    for size in [1000, 10000, 100000].iter() {
        let data: Vec<i32> = (0..*size).collect();

        group.bench_with_input(BenchmarkId::new("sequential", size), size, |b, _| {
            b.iter(|| data.iter().map(|&x| x * x).sum::<i32>())
        });

        group.bench_with_input(BenchmarkId::new("parallel", size), size, |b, _| {
            b.iter(|| data.par_iter().map(|&x| x * x).sum::<i32>())
        });
    }

    group.finish();
}

criterion_group!(benches, parallel_sum);
criterion_main!(benches);
```

---

## 11. 总结

### 11.1 核心语义概念回顾

| 概念 | 语义描述 | 安全保证 |
|-----|---------|---------|
| **Send** | 可跨线程转移所有权 | 数据竞争自由 |
| **Sync** | 可跨线程共享引用 | 数据竞争自由 |
| **Mutex** | 独占访问 | 互斥保护 |
| **RwLock** | 多读单写 | 读写分离 |
| **原子操作** | 不可分割的操作 | 内存安全 |
| **内存序** | 操作可见性顺序 | happens-before |
| **通道** | 所有权转移通信 | 无数据竞争 |

### 11.2 安全保证总结

Rust 的并发安全保证基于以下形式化规则：

$$
\begin{aligned}
\text{DataRaceFreedom} &\iff \forall x. \neg(\text{Write}(x) \land \text{ConcurrentAccess}(x)) \\
&\quad \lor \text{Synchronized}(\text{Write}(x), \text{Access}(x)) \\
\text{MemorySafety} &\iff \text{Ownership} + \text{Borrowing} + \text{Lifetime} \\
\text{ThreadSafety} &\iff \text{Send} \land \text{Sync}
\end{aligned}
$$

### 11.3 性能与安全权衡

| 机制 | 性能 | 安全 | 使用场景 |
|-----|------|------|---------|
| `Mutex<T>` | 低（阻塞） | 高 | 频繁写 |
| `RwLock<T>` | 中 | 高 | 读多写少 |
| 原子操作 | 高（无锁） | 中 | 计数器、标志 |
| 无锁数据结构 | 高 | 低（复杂） | 极致性能 |
| 消息传递 | 中 | 高 | Actor 模式 |

### 11.4 最佳实践

1. **优先使用消息传递**：`channel` 比共享状态更安全
2. **最小化锁粒度**：减少临界区代码
3. **避免在锁中调用未知代码**：防止死锁和性能问题
4. **使用作用域线程**：借用非 `'static` 数据
5. **使用线程池**：避免线程创建开销
6. **无锁需谨慎**：只有必要时使用，充分测试

---

## 参考

- [The Rust Programming Language - Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Rust Atomics and Locks](https://marabos.nl/atomics/)
- [Rayon Documentation](https://docs.rs/rayon/)
- [Crossbeam Documentation](https://docs.rs/crossbeam/)
