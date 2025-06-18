# 05.01 形式化线程与并发系统 (Formal Threads and Concurrency System)

## 目录

1. [引言与基础定义](#1-引言与基础定义)
2. [线程模型](#2-线程模型)
3. [并发安全](#3-并发安全)
4. [同步原语](#4-同步原语)
5. [内存模型](#5-内存模型)
6. [消息传递](#6-消息传递)
7. [无锁编程](#7-无锁编程)
8. [形式化验证](#8-形式化验证)
9. [定理与证明](#9-定理与证明)

---

## 1. 引言与基础定义

### 1.1 并发基础概念

**定义 1.1** (并发)
并发是多个计算任务在时间上重叠执行的能力：
$$\text{Concurrency} = \text{Overlapping}(\text{Task}_1, \text{Task}_2, ..., \text{Task}_n)$$

**定义 1.2** (并行)
并行是多个计算任务同时执行的能力：
$$\text{Parallelism} = \text{Simultaneous}(\text{Task}_1, \text{Task}_2, ..., \text{Task}_n)$$

**定义 1.3** (线程)
线程是程序执行的最小单位，具有独立的执行上下文：
$$\text{Thread} = (\text{Stack}, \text{Registers}, \text{ProgramCounter}, \text{State})$$

### 1.2 并发系统

**定义 1.4** (并发系统)
并发系统是四元组：
$$\mathcal{CS} = (\mathcal{T}, \mathcal{S}, \mathcal{R}, \mathcal{I})$$
其中：
- $\mathcal{T}$ 是线程集合
- $\mathcal{S}$ 是共享状态集合
- $\mathcal{R}$ 是同步关系集合
- $\mathcal{I}$ 是初始状态

### 1.3 数据竞争

**定义 1.5** (数据竞争)
数据竞争发生在两个并发访问之间：
$$\text{race}(a_1, a_2) \Leftrightarrow \text{concurrent}(a_1, a_2) \land \text{conflict}(a_1, a_2)$$
其中：
- $\text{concurrent}(a_1, a_2)$ 表示访问并发执行
- $\text{conflict}(a_1, a_2)$ 表示访问冲突（至少一个是写操作）

---

## 2. 线程模型

### 2.1 线程创建

**定义 2.1** (线程创建)
线程创建是从函数到线程的映射：
$$\text{spawn}: \text{Function} \rightarrow \text{ThreadHandle}$$

**类型规则 2.1** (线程创建类型)
$$\frac{\Gamma \vdash f: F \quad F: \text{Send}}{\Gamma \vdash \text{spawn}(f): \text{ThreadHandle}}$$

**示例 2.1** (线程创建)
```rust
use std::thread;

// 基本线程创建
let handle = thread::spawn(|| {
    println!("Hello from thread!");
});

// 带参数的线程
let value = 42;
let handle = thread::spawn(move || {
    println!("Value: {}", value);
});

// 等待线程完成
handle.join().unwrap();
```

### 2.2 线程生命周期

**定义 2.2** (线程状态)
线程状态是线程执行的不同阶段：
$$\text{ThreadState} = \text{Running} \mid \text{Blocked} \mid \text{Terminated}$$

**定义 2.3** (线程加入)
线程加入是等待线程完成的操作：
$$\text{join}: \text{ThreadHandle} \rightarrow \text{Result<T, E>}$$

**示例 2.2** (线程生命周期)
```rust
use std::thread;
use std::time::Duration;

let handle = thread::spawn(|| {
    thread::sleep(Duration::from_millis(100));
    "Thread completed"
});

// 线程正在运行
println!("Main thread continues");

// 等待线程完成
let result = handle.join().unwrap();
println!("{}", result);
```

### 2.3 线程本地存储

**定义 2.4** (线程本地存储)
线程本地存储是每个线程独立的数据：
$$\text{ThreadLocal} = \text{Thread} \rightarrow \text{Value}$$

**示例 2.3** (线程本地存储)
```rust
use std::cell::RefCell;
use std::thread_local;

thread_local! {
    static COUNTER: RefCell<u32> = RefCell::new(0);
}

fn increment_counter() {
    COUNTER.with(|counter| {
        let mut count = counter.borrow_mut();
        *count += 1;
        println!("Counter: {}", *count);
    });
}

// 每个线程有独立的计数器
for _ in 0..3 {
    thread::spawn(|| {
        increment_counter();
        increment_counter();
    });
}
```

---

## 3. 并发安全

### 3.1 Send和Sync Traits

**定义 3.1** (Send)
Send trait表示类型可以安全地转移所有权到另一个线程：
$$\text{Send}: \text{Type} \rightarrow \text{ThreadSafe}$$

**定义 3.2** (Sync)
Sync trait表示类型可以安全地在多个线程间共享引用：
$$\text{Sync}: \text{Type} \rightarrow \text{ShareSafe}$$

**定理 3.1** (Send/Sync关系)
如果类型T是Sync，则&T是Send：
$$\text{Sync}(T) \Rightarrow \text{Send}(\&T)$$

**证明**：
Sync表示&T可以安全地在线程间转移，这正是Send的定义。

**示例 3.1** (Send/Sync示例)
```rust
// 自动实现Send和Sync的类型
struct SafeType {
    data: Vec<i32>,
}
// SafeType自动实现Send和Sync

// 不能实现Send的类型
struct NotSend {
    data: *mut i32, // 裸指针不是Send
}
// 编译错误：NotSend没有实现Send

// 在线程间安全传递
let safe = SafeType { data: vec![1, 2, 3] };
thread::spawn(move || {
    println!("Safe data: {:?}", safe.data);
});
```

### 3.2 并发安全保证

**定义 3.3** (并发安全)
并发安全确保程序在并发执行时不会出现数据竞争：
$$\text{concurrent-safe}(P) \Leftrightarrow \forall t_1, t_2: \neg\text{race}(t_1, t_2)$$

**定理 3.2** (Rust并发安全)
Rust的类型系统在编译时保证并发安全：
$$\text{type-safe}(P) \Rightarrow \text{concurrent-safe}(P)$$

**证明**：
1. Send trait确保数据可以安全转移
2. Sync trait确保引用可以安全共享
3. 借用检查器防止数据竞争

---

## 4. 同步原语

### 4.1 互斥锁

**定义 4.1** (互斥锁)
互斥锁确保在任何时刻只有一个线程能访问受保护的数据：
$$\text{Mutex}(T) = \text{Lock} \times T$$

**定义 4.2** (锁操作)
锁操作包括获取和释放：
$$\text{lock}: \text{Mutex}(T) \rightarrow \text{MutexGuard}(T)$$
$$\text{unlock}: \text{MutexGuard}(T) \rightarrow \text{Mutex}(T)$$

**类型规则 4.1** (互斥锁类型)
$$\frac{\Gamma \vdash T: \text{Send}}{\Gamma \vdash \text{Mutex}(T): \text{Sync}}$$

**示例 4.1** (互斥锁)
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

println!("Final count: {}", *counter.lock().unwrap());
```

### 4.2 读写锁

**定义 4.3** (读写锁)
读写锁允许多个读者或一个写者：
$$\text{RwLock}(T) = \text{ReadLock} \times \text{WriteLock} \times T$$

**定义 4.4** (读写锁语义)
- 多个线程可以同时持有读锁
- 写锁与读锁和写锁互斥
- 写锁优先于读锁

**示例 4.2** (读写锁)
```rust
use std::sync::{Arc, RwLock};
use std::thread;

let data = Arc::new(RwLock::new(vec![1, 2, 3]));
let mut handles = vec![];

// 读者线程
for i in 0..3 {
    let data = Arc::clone(&data);
    let handle = thread::spawn(move || {
        let values = data.read().unwrap();
        println!("Reader {}: {:?}", i, *values);
    });
    handles.push(handle);
}

// 写者线程
let data = Arc::clone(&data);
let handle = thread::spawn(move || {
    let mut values = data.write().unwrap();
    values.push(4);
    println!("Writer: {:?}", *values);
});
handles.push(handle);

for handle in handles {
    handle.join().unwrap();
}
```

### 4.3 原子类型

**定义 4.5** (原子操作)
原子操作是不可分割的操作：
$$\text{atomic}(op) \Leftrightarrow \forall t: \text{interrupted}(op, t) = \text{false}$$

**定义 4.6** (原子类型)
原子类型提供原子操作的基本类型：
$$\text{Atomic}(T) = \text{AtomicOperations} \times T$$

**示例 4.3** (原子类型)
```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

let counter = Arc::new(AtomicUsize::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let counter = Arc::clone(&counter);
    let handle = thread::spawn(move || {
        for _ in 0..100 {
            counter.fetch_add(1, Ordering::SeqCst);
        }
    });
    handles.push(handle);
}

for handle in handles {
    handle.join().unwrap();
}

println!("Final count: {}", counter.load(Ordering::SeqCst));
```

---

## 5. 内存模型

### 5.1 内存序

**定义 5.1** (内存序)
内存序定义了原子操作之间的顺序关系：
$$\text{MemoryOrdering} = \text{Relaxed} \mid \text{Acquire} \mid \text{Release} \mid \text{AcqRel} \mid \text{SeqCst}$$

**定义 5.2** (内存序语义)
- **Relaxed**: 只保证原子性，不保证顺序
- **Acquire**: 确保后续操作不会重排到此操作之前
- **Release**: 确保之前的操作不会重排到此操作之后
- **AcqRel**: 同时具有Acquire和Release语义
- **SeqCst**: 提供全局顺序一致性

**示例 5.1** (内存序)
```rust
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

let flag = Arc::new(AtomicBool::new(false));
let data = Arc::new(AtomicUsize::new(0));

// 生产者线程
let flag_prod = Arc::clone(&flag);
let data_prod = Arc::clone(&data);
let producer = thread::spawn(move || {
    data_prod.store(42, Ordering::Relaxed);
    flag_prod.store(true, Ordering::Release); // 确保data的写入在flag之前
});

// 消费者线程
let flag_cons = Arc::clone(&flag);
let data_cons = Arc::clone(&data);
let consumer = thread::spawn(move || {
    while !flag_cons.load(Ordering::Acquire) {
        // 自旋等待
    }
    // 此时data的写入已经可见
    println!("Data: {}", data_cons.load(Ordering::Relaxed));
});

producer.join().unwrap();
consumer.join().unwrap();
```

### 5.2 内存屏障

**定义 5.3** (内存屏障)
内存屏障确保内存操作的顺序：
$$\text{MemoryBarrier}: \text{MemoryOrdering} \rightarrow \text{Barrier}$$

**定理 5.1** (内存屏障正确性)
内存屏障确保指定的内存序得到满足：
$$\text{barrier}(ordering) \Rightarrow \text{enforce}(ordering)$$

---

## 6. 消息传递

### 6.1 通道

**定义 6.1** (通道)
通道是线程间通信的机制：
$$\text{Channel}(T) = \text{Sender}(T) \times \text{Receiver}(T)$$

**定义 6.2** (通道操作)
通道操作包括发送和接收：
$$\text{send}: \text{Sender}(T) \times T \rightarrow \text{Result<(), SendError>}$$
$$\text{recv}: \text{Receiver}(T) \rightarrow \text{Result<T, RecvError>}$$

**示例 6.1** (通道)
```rust
use std::sync::mpsc;
use std::thread;

let (tx, rx) = mpsc::channel();

// 发送者线程
let sender = thread::spawn(move || {
    for i in 0..10 {
        tx.send(i).unwrap();
    }
});

// 接收者线程
let receiver = thread::spawn(move || {
    for received in rx {
        println!("Received: {}", received);
    }
});

sender.join().unwrap();
receiver.join().unwrap();
```

### 6.2 多生产者单消费者

**定义 6.3** (MPSC通道)
MPSC通道允许多个发送者，一个接收者：
$$\text{MPSC}(T) = \text{MultiSender}(T) \times \text{SingleReceiver}(T)$$

**示例 6.2** (MPSC通道)
```rust
use std::sync::mpsc;
use std::thread;

let (tx, rx) = mpsc::channel();
let mut handles = vec![];

// 多个发送者
for i in 0..3 {
    let tx = tx.clone();
    let handle = thread::spawn(move || {
        for j in 0..5 {
            tx.send(format!("Thread {}: {}", i, j)).unwrap();
        }
    });
    handles.push(handle);
}

// 丢弃最后一个发送者
drop(tx);

// 接收者
let receiver = thread::spawn(move || {
    for received in rx {
        println!("{}", received);
    }
});

for handle in handles {
    handle.join().unwrap();
}
receiver.join().unwrap();
```

---

## 7. 无锁编程

### 7.1 无锁数据结构

**定义 7.1** (无锁)
无锁数据结构不使用互斥锁进行同步：
$$\text{LockFree} = \text{NoMutex} \land \text{AtomicOperations}$$

**定义 7.2** (等待无关)
等待无关数据结构确保每个操作都能在有限步数内完成：
$$\text{WaitFree} = \text{LockFree} \land \text{FiniteSteps}$$

**示例 7.1** (无锁队列)
```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

struct LockFreeQueue<T> {
    buffer: Vec<Option<T>>,
    head: AtomicUsize,
    tail: AtomicUsize,
    capacity: usize,
}

impl<T> LockFreeQueue<T> {
    fn new(capacity: usize) -> Self {
        let mut buffer = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            buffer.push(None);
        }
        
        LockFreeQueue {
            buffer,
            head: AtomicUsize::new(0),
            tail: AtomicUsize::new(0),
            capacity,
        }
    }
    
    fn enqueue(&self, item: T) -> Result<(), ()> {
        let tail = self.tail.load(Ordering::Relaxed);
        let next_tail = (tail + 1) % self.capacity;
        
        if next_tail == self.head.load(Ordering::Acquire) {
            return Err(()); // 队列满
        }
        
        // 使用compare_exchange确保原子性
        if self.tail.compare_exchange(tail, next_tail, Ordering::Release, Ordering::Relaxed).is_ok() {
            unsafe {
                let slot = self.buffer.get_unchecked_mut(tail);
                *slot = Some(item);
            }
            Ok(())
        } else {
            Err(())
        }
    }
    
    fn dequeue(&self) -> Option<T> {
        let head = self.head.load(Ordering::Relaxed);
        
        if head == self.tail.load(Ordering::Acquire) {
            return None; // 队列空
        }
        
        // 使用compare_exchange确保原子性
        if self.head.compare_exchange(head, (head + 1) % self.capacity, Ordering::Release, Ordering::Relaxed).is_ok() {
            unsafe {
                let slot = self.buffer.get_unchecked_mut(head);
                slot.take()
            }
        } else {
            None
        }
    }
}

// 使用示例
let queue = Arc::new(LockFreeQueue::new(10));
let mut handles = vec![];

// 生产者
for i in 0..3 {
    let queue = Arc::clone(&queue);
    let handle = thread::spawn(move || {
        for j in 0..5 {
            while queue.enqueue(format!("Producer {}: {}", i, j)).is_err() {
                thread::yield_now();
            }
        }
    });
    handles.push(handle);
}

// 消费者
let queue = Arc::clone(&queue);
let consumer = thread::spawn(move || {
    let mut count = 0;
    while count < 15 {
        if let Some(item) = queue.dequeue() {
            println!("Consumed: {}", item);
            count += 1;
        } else {
            thread::yield_now();
        }
    }
});

for handle in handles {
    handle.join().unwrap();
}
consumer.join().unwrap();
```

### 7.2 原子引用计数

**定义 7.3** (原子引用计数)
原子引用计数使用原子操作管理引用计数：
$$\text{Arc}(T) = \text{AtomicRefCount} \times T$$

**示例 7.2** (Arc实现原理)
```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

// Arc的基本原理
struct MyArc<T> {
    data: *mut T,
    ref_count: *mut AtomicUsize,
}

impl<T> MyArc<T> {
    fn new(data: T) -> Self {
        let data = Box::into_raw(Box::new(data));
        let ref_count = Box::into_raw(Box::new(AtomicUsize::new(1)));
        
        MyArc { data, ref_count }
    }
}

impl<T> Clone for MyArc<T> {
    fn clone(&self) -> Self {
        unsafe {
            (*self.ref_count).fetch_add(1, Ordering::Relaxed);
        }
        MyArc {
            data: self.data,
            ref_count: self.ref_count,
        }
    }
}

impl<T> Drop for MyArc<T> {
    fn drop(&mut self) {
        unsafe {
            if (*self.ref_count).fetch_sub(1, Ordering::Release) == 1 {
                // 最后一个引用，释放数据
                let _ = Box::from_raw(self.data);
                let _ = Box::from_raw(self.ref_count);
            }
        }
    }
}
```

---

## 8. 形式化验证

### 8.1 并发正确性

**定义 8.1** (并发正确性)
并发正确性确保程序在并发执行时保持期望的行为：
$$\text{concurrent-correct}(P) \Leftrightarrow \forall \text{execution}: \text{correct}(\text{execution})$$

**定义 8.2** (线性化)
线性化确保并发操作看起来像按某种顺序执行：
$$\text{linearizable}(P) \Leftrightarrow \exists \text{sequential}: \text{equivalent}(P, \text{sequential})$$

### 8.2 死锁检测

**定义 8.3** (死锁)
死锁是多个线程相互等待对方释放资源的状态：
$$\text{deadlock}(T_1, T_2, ..., T_n) \Leftrightarrow \forall i: \text{waiting}(T_i, T_{(i+1)\bmod n})$$

**算法 8.1** (死锁检测)
```rust
fn detect_deadlock(threads: &[ThreadState]) -> bool {
    // 构建资源分配图
    let mut graph = HashMap::new();
    
    for thread in threads {
        for resource in &thread.held_resources {
            for waiting in &thread.waiting_resources {
                graph.entry(resource).or_insert_with(Vec::new).push(waiting);
            }
        }
    }
    
    // 检测环
    has_cycle(&graph)
}
```

---

## 9. 定理与证明

### 9.1 核心定理

**定理 9.1** (并发安全定理)
如果程序P通过Rust的类型检查，则P无数据竞争：
$$\text{type-check}(P) = \text{valid} \Rightarrow \neg\exists a_1, a_2: \text{race}(a_1, a_2)$$

**证明**：
1. Send trait确保数据可以安全转移
2. Sync trait确保引用可以安全共享
3. 借用检查器防止并发访问冲突
4. 因此不存在数据竞争

**定理 9.2** (互斥锁正确性)
互斥锁确保互斥访问：
$$\text{mutex-lock}(m) \land \text{mutex-lock}(m) \Rightarrow \text{false}$$

**证明**：
互斥锁的实现确保同一时刻只有一个线程能获取锁，因此不可能同时有两个线程持有同一个锁。

**定理 9.3** (原子操作正确性)
原子操作保证操作的原子性：
$$\text{atomic}(op) \Rightarrow \text{atomic-execution}(op)$$

**证明**：
原子操作使用CPU的原子指令，确保操作在执行过程中不会被中断。

### 9.2 实现验证

**验证 9.1** (线程实现正确性)
Rust的线程实现与形式化定义一致。

**验证方法**：
1. 类型检查器验证Send/Sync约束
2. 运行时系统确保线程隔离
3. 同步原语提供正确的语义

### 9.3 性能定理

**定理 9.4** (无锁性能)
无锁数据结构在高竞争环境下性能优于基于锁的数据结构。

**证明**：
1. 无锁操作避免线程阻塞
2. 原子操作比锁操作开销更小
3. 减少上下文切换开销

---

## 总结

Rust的线程与并发系统提供了：

1. **类型安全保证**：通过Send/Sync traits在编译时防止数据竞争
2. **丰富的同步原语**：Mutex、RwLock、原子类型等
3. **精确的内存模型**：支持多种内存序，平衡性能与正确性
4. **高效的消息传递**：通道机制简化线程间通信
5. **无锁编程支持**：原子操作和高级无锁数据结构

这些机制共同构成了一个安全、高效、易用的并发编程系统，在保证内存安全的同时提供强大的并发能力。 