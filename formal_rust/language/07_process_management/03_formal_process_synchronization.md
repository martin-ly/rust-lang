# 07.03 形式化进程同步机制

## 目录

1. [引言与基础定义](#1-引言与基础定义)
2. [同步原语分类](#2-同步原语分类)
3. [线程级同步](#3-线程级同步)
4. [进程级同步](#4-进程级同步)
5. [原子操作](#5-原子操作)
6. [内存模型](#6-内存模型)
7. [死锁预防](#7-死锁预防)
8. [形式化验证](#8-形式化验证)
9. [定理与证明](#9-定理与证明)

---

## 1. 引言与基础定义

### 1.1 同步基础

**定义 1.1** (同步)
同步是协调多个执行单元访问共享资源的机制：
$$\text{Synchronization} = \text{Coordination} \times \text{SharedResource} \times \text{ExecutionUnit}$$

**定义 1.2** (同步原语)
同步原语是同步机制的基本构建块：
$$\text{SyncPrimitive} = (\text{Type}, \text{State}, \text{Operations})$$

其中：

- $\text{Type}$ 是原语类型
- $\text{State}$ 是内部状态
- $\text{Operations}$ 是支持的操作

### 1.2 同步分类

**定义 1.3** (同步层次)
同步可分为两个层次：
$$\text{SyncLevel} = \{\text{IntraProcess}, \text{InterProcess}\}$$

**定义 1.4** (同步类型)
同步原语类型：
$$\text{SyncType} = \{\text{Mutex}, \text{RwLock}, \text{Semaphore}, \text{Barrier}, \text{CondVar}, \text{Atomic}\}$$

---

## 2. 同步原语分类

### 2.1 互斥同步

**定义 2.1** (互斥)
互斥确保同时只有一个执行单元访问资源：
$$\text{MutualExclusion} = \forall t_1, t_2: \text{Access}(t_1, R) \land \text{Access}(t_2, R) \Rightarrow t_1 = t_2$$

**定义 2.2** (临界区)
临界区是需要互斥访问的代码段：
$$\text{CriticalSection} = \text{Code} \times \text{SharedResource}$$

### 2.2 条件同步

**定义 2.3** (条件同步)
条件同步基于状态条件协调执行：
$$\text{ConditionalSync} = \text{State} \times \text{Condition} \times \text{Action}$$

**定义 2.4** (生产者-消费者)
生产者-消费者是经典的条件同步模式：
$$\text{ProducerConsumer} = \text{Producer} \times \text{Buffer} \times \text{Consumer}$$

---

## 3. 线程级同步

### 3.1 Mutex

**定义 3.1** (Mutex)
Mutex提供互斥访问保证：
$$\text{Mutex} = (\text{Locked}, \text{Unlocked}, \text{Owner})$$

**Mutex操作**：

- $\text{lock}: \text{Mutex} \rightarrow \text{Result}((), \text{Error})$
- $\text{try\_lock}: \text{Mutex} \rightarrow \text{Result}((), \text{Error})$
- $\text{unlock}: \text{Mutex} \rightarrow \text{Result}((), \text{Error})$

**代码示例 3.1** (基本Mutex)

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn mutex_example() {
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

    println!("最终计数: {}", *counter.lock().unwrap());
}
```

**代码示例 3.2** (Mutex毒化)

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn mutex_poisoning_example() {
    let data = Arc::new(Mutex::new(vec![1, 2, 3, 4]));

    let data_clone = Arc::clone(&data);
    let handle = thread::spawn(move || {
        let mut data = data_clone.lock().unwrap();
        data.push(5);
        panic!("线程panic，Mutex被毒化");
    });

    handle.join().unwrap_err();

    // 尝试访问被毒化的Mutex
    match data.lock() {
        Ok(_) => println!("Mutex未被毒化"),
        Err(poisoned) => {
            println!("Mutex被毒化，但数据仍然可用");
            let data = poisoned.into_inner();
            println!("数据: {:?}", data);
        }
    }
}
```

### 3.2 RwLock

**定义 3.2** (RwLock)
RwLock允许多个读取者或一个写入者：
$$\text{RwLock} = (\text{Readers}, \text{Writer}, \text{State})$$

**RwLock状态**：
$$\text{RwLockState} = \{\text{Unlocked}, \text{ReadLocked}(n), \text{WriteLocked}\}$$

**代码示例 3.3** (RwLock使用)

```rust
use std::sync::{Arc, RwLock};
use std::thread;

fn rwlock_example() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3, 4]));
    let mut handles = vec![];

    // 读取者线程
    for i in 0..3 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let data = data.read().unwrap();
            println!("读取者 {}: {:?}", i, *data);
        });
        handles.push(handle);
    }

    // 写入者线程
    let data = Arc::clone(&data);
    let handle = thread::spawn(move || {
        let mut data = data.write().unwrap();
        data.push(5);
        println!("写入者: 添加了元素");
    });
    handles.push(handle);

    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 3.3 CondVar

**定义 3.3** (CondVar)
CondVar用于条件等待和通知：
$$\text{CondVar} = (\text{Waiters}, \text{Notifications})$$

**CondVar操作**：

- $\text{wait}: \text{CondVar} \times \text{MutexGuard} \rightarrow \text{MutexGuard}$
- $\text{notify\_one}: \text{CondVar} \rightarrow \text{Result}((), \text{Error})$
- $\text{notify\_all}: \text{CondVar} \rightarrow \text{Result}((), \text{Error})$

**代码示例 3.4** (生产者-消费者)

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;

fn producer_consumer_example() {
    let pair = Arc::new((Mutex::new(Vec::new()), Condvar::new()));
    let pair_clone = Arc::clone(&pair);

    // 生产者
    let producer = thread::spawn(move || {
        let (lock, cvar) = &*pair_clone;
        for i in 0..10 {
            let mut data = lock.lock().unwrap();
            data.push(i);
            println!("生产者: 添加 {}", i);
            cvar.notify_one();
        }
    });

    // 消费者
    let consumer = thread::spawn(move || {
        let (lock, cvar) = &*pair;
        for _ in 0..10 {
            let mut data = lock.lock().unwrap();
            while data.is_empty() {
                data = cvar.wait(data).unwrap();
            }
            let item = data.remove(0);
            println!("消费者: 处理 {}", item);
        }
    });

    producer.join().unwrap();
    consumer.join().unwrap();
}
```

### 3.4 Barrier

**定义 3.4** (Barrier)
Barrier用于线程同步点：
$$\text{Barrier} = (\text{Count}, \text{Threshold}, \text{Generation})$$

**代码示例 3.5** (Barrier使用)

```rust
use std::sync::{Arc, Barrier};
use std::thread;

fn barrier_example() {
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];

    for i in 0..3 {
        let barrier = Arc::clone(&barrier);
        let handle = thread::spawn(move || {
            println!("线程 {} 开始工作", i);
            // 模拟工作
            thread::sleep(std::time::Duration::from_millis(100));
            println!("线程 {} 等待同步点", i);
            barrier.wait();
            println!("线程 {} 通过同步点", i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
```

---

## 4. 进程级同步

### 4.1 命名信号量

**定义 4.1** (命名信号量)
命名信号量是系统级同步原语：
$$\text{NamedSemaphore} = (\text{Name}, \text{Value}, \text{SystemWide})$$

**信号量操作**：

- $\text{wait}: \text{Semaphore} \rightarrow \text{Result}((), \text{Error})$
- $\text{post}: \text{Semaphore} \rightarrow \text{Result}((), \text{Error})$

**代码示例 4.1** (信号量概念)

```rust
use std::sync::{Arc, Mutex};
use std::process::{Command, Stdio};

// 简化的信号量实现
struct Semaphore {
    count: Arc<Mutex<i32>>,
}

impl Semaphore {
    fn new(initial: i32) -> Self {
        Self {
            count: Arc::new(Mutex::new(initial)),
        }
    }

    fn wait(&self) -> Result<(), Box<dyn std::error::Error>> {
        loop {
            let mut count = self.count.lock()?;
            if *count > 0 {
                *count -= 1;
                return Ok(());
            }
            // 在实际实现中，这里会阻塞
            drop(count);
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
    }

    fn post(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut count = self.count.lock()?;
        *count += 1;
        Ok(())
    }
}
```

### 4.2 系统互斥锁

**定义 4.2** (系统互斥锁)
系统互斥锁提供跨进程互斥：
$$\text{SystemMutex} = (\text{Name}, \text{Owner}, \text{SystemWide})$$

**代码示例 4.2** (文件锁)

```rust
use std::fs::File;
use std::io::{Read, Write};

fn file_lock_example() -> std::io::Result<()> {
    let file = File::open("shared.txt")?;
    
    // 获取排他锁
    file.lock_exclusive()?;
    
    // 执行需要同步的操作
    println!("持有文件锁，执行操作...");
    
    // 释放锁
    file.unlock()?;
    
    Ok(())
}
```

### 4.3 共享内存同步

**定义 4.3** (共享内存同步)
共享内存中的同步原语：
$$\text{SharedMemorySync} = \text{SharedMemory} \times \text{SyncPrimitive}$$

**代码示例 4.3** (共享内存互斥锁)

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn shared_memory_mutex_example() {
    // 模拟共享内存中的互斥锁
    let shared_mutex = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for i in 0..5 {
        let mutex = Arc::clone(&shared_mutex);
        let handle = thread::spawn(move || {
            let mut data = mutex.lock().unwrap();
            *data += 1;
            println!("线程 {}: 更新共享数据为 {}", i, *data);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("最终共享数据: {}", *shared_mutex.lock().unwrap());
}
```

---

## 5. 原子操作

### 5.1 原子类型

**定义 5.1** (原子操作)
原子操作是不可分割的操作：
$$\text{AtomicOperation} = \text{Indivisible} \times \text{Operation}$$

**定义 5.2** (原子类型)
原子类型提供原子操作：
$$\text{AtomicType} = \{\text{AtomicBool}, \text{AtomicI32}, \text{AtomicU64}, \text{AtomicPtr}\}$$

**代码示例 5.1** (原子计数器)

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

fn atomic_counter_example() {
    let counter = AtomicU64::new(0);
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = &counter;
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                counter.fetch_add(1, Ordering::Relaxed);
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("最终计数: {}", counter.load(Ordering::Relaxed));
}
```

### 5.2 内存顺序

**定义 5.3** (内存顺序)
内存顺序定义原子操作的内存语义：
$$\text{MemoryOrdering} = \{\text{Relaxed}, \text{Acquire}, \text{Release}, \text{AcqRel}, \text{SeqCst}\}$$

**代码示例 5.2** (内存顺序示例)

```rust
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::thread;

fn memory_ordering_example() {
    let ready = AtomicBool::new(false);
    let data = AtomicI32::new(0);

    // 生产者线程
    let producer = thread::spawn(move || {
        data.store(42, Ordering::Relaxed);
        ready.store(true, Ordering::Release);
    });

    // 消费者线程
    let consumer = thread::spawn(move || {
        while !ready.load(Ordering::Acquire) {
            // 自旋等待
        }
        let value = data.load(Ordering::Relaxed);
        println!("读取到数据: {}", value);
    });

    producer.join().unwrap();
    consumer.join().unwrap();
}
```

---

## 6. 内存模型

### 6.1 内存模型基础

**定义 6.1** (内存模型)
内存模型定义并发程序的内存行为：
$$\text{MemoryModel} = (\text{Ordering}, \text{Visibility}, \text{Coherence})$$

**定义 6.2** (顺序一致性)
顺序一致性是最强的内存模型：
$$\text{SequentialConsistency} = \text{TotalOrder} \times \text{ImmediateVisibility}$$

### 6.2 Rust内存模型

**定义 6.3** (Rust内存模型)
Rust采用C++11内存模型：
$$\text{RustMemoryModel} = \text{Cpp11Model} \times \text{TypeSafety}$$

**代码示例 6.1** (内存模型示例)

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

fn memory_model_example() {
    let flag = AtomicBool::new(false);
    let mut data = 0;

    let flag_clone = &flag;
    let data_ref = &mut data;

    let writer = thread::spawn(move || {
        *data_ref = 42;
        flag_clone.store(true, Ordering::Release);
    });

    let reader = thread::spawn(move || {
        while !flag.load(Ordering::Acquire) {
            // 等待
        }
        // 此时data的值是可见的
    });

    writer.join().unwrap();
    reader.join().unwrap();
}
```

---

## 7. 死锁预防

### 7.1 死锁条件

**定义 7.1** (死锁)
死锁是多个线程互相等待对方释放资源的状态：
$$\text{Deadlock} = \text{CircularWait} \land \text{MutualExclusion} \land \text{HoldAndWait} \land \text{NoPreemption}$$

**定义 7.2** (死锁预防)
死锁预防通过破坏死锁条件避免死锁：
$$\text{DeadlockPrevention} = \neg\text{CircularWait} \lor \neg\text{HoldAndWait} \lor \neg\text{NoPreemption}$$

### 7.2 死锁检测

**代码示例 7.1** (死锁检测)

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

fn deadlock_detection_example() {
    let mutex1 = Arc::new(Mutex::new(1));
    let mutex2 = Arc::new(Mutex::new(2));

    let mutex1_clone = Arc::clone(&mutex1);
    let mutex2_clone = Arc::clone(&mutex2);

    // 线程1: 先锁mutex1，再锁mutex2
    let thread1 = thread::spawn(move || {
        let _lock1 = mutex1_clone.lock().unwrap();
        thread::sleep(Duration::from_millis(100));
        let _lock2 = mutex2_clone.lock().unwrap();
    });

    // 线程2: 先锁mutex2，再锁mutex1 (可能导致死锁)
    let thread2 = thread::spawn(move || {
        let _lock2 = mutex2.lock().unwrap();
        thread::sleep(Duration::from_millis(100));
        let _lock1 = mutex1.lock().unwrap();
    });

    thread1.join().unwrap();
    thread2.join().unwrap();
}
```

### 7.3 死锁避免

**代码示例 7.2** (资源层次)

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn resource_hierarchy_example() {
    let mutex1 = Arc::new(Mutex::new(1));
    let mutex2 = Arc::new(Mutex::new(2));

    let mutex1_clone = Arc::clone(&mutex1);
    let mutex2_clone = Arc::clone(&mutex2);

    // 使用资源层次避免死锁
    let thread1 = thread::spawn(move || {
        // 总是按相同顺序获取锁
        let _lock1 = mutex1_clone.lock().unwrap();
        let _lock2 = mutex2_clone.lock().unwrap();
    });

    let thread2 = thread::spawn(move || {
        // 按相同顺序获取锁
        let _lock1 = mutex1.lock().unwrap();
        let _lock2 = mutex2.lock().unwrap();
    });

    thread1.join().unwrap();
    thread2.join().unwrap();
}
```

---

## 8. 形式化验证

### 8.1 同步正确性

**定义 8.1** (同步正确性)
同步正确性确保程序满足同步要求：
$$\text{SyncCorrectness} = \text{MutualExclusion} \land \text{Progress} \land \text{BoundedWaiting}$$

**验证规则 8.1** (互斥验证)
$$\frac{\Gamma \vdash L: \text{Mutex} \quad \text{ProperUsage}(L)}{\Gamma \vdash \text{MutualExclusion}(L)}$$

### 8.2 性能验证

**定义 8.2** (同步性能)
同步性能由延迟和吞吐量定义：
$$\text{SyncPerformance} = (\text{Latency}, \text{Throughput}, \text{Scalability})$$

**性能排序**：
$$\text{Performance}(\text{Atomic}) > \text{Performance}(\text{Mutex}) > \text{Performance}(\text{RwLock}) > \text{Performance}(\text{CondVar})$$

---

## 9. 定理与证明

### 9.1 核心定理

**定理 9.1** (互斥定理)
Mutex保证互斥访问：
$$\text{Mutex}(M) \Rightarrow \text{MutualExclusion}(M)$$

**证明**：

1. Mutex内部状态确保同时只有一个持有者
2. lock操作阻塞直到可用
3. unlock操作释放锁
4. 因此保证互斥访问

**定理 9.2** (读写锁定理)
RwLock允许多读一写：
$$\text{RwLock}(R) \Rightarrow \text{MultipleReaders}(R) \land \text{SingleWriter}(R)$$

**证明**：

1. 读取锁增加读者计数
2. 写入锁需要读者计数为0
3. 因此允许多读一写

**定理 9.3** (原子操作定理)
原子操作是不可分割的：
$$\text{Atomic}(A) \Rightarrow \text{Indivisible}(A)$$

**证明**：

1. 原子操作由硬件保证
2. 编译器不重排原子操作
3. 因此操作不可分割

### 9.2 实现验证

**验证 9.1** (同步原语正确性)
Rust的同步原语实现与形式化定义一致。

**验证方法**：

1. 类型系统验证接口正确性
2. 运行时保证语义正确性
3. 性能测试验证效率
4. 压力测试验证稳定性

### 9.3 安全定理

**定理 9.4** (同步安全定理)
Rust的同步机制提供内存安全：
$$\text{SyncPrimitive}(P) \Rightarrow \text{MemorySafe}(P)$$

**定理 9.5** (死锁预防定理)
资源层次可以预防死锁：
$$\text{ResourceHierarchy}(H) \Rightarrow \neg\text{Deadlock}(H)$$

---

## 总结

Rust的进程同步机制提供了：

1. **多样化原语**：支持Mutex、RwLock、CondVar等多种同步原语
2. **类型安全**：通过类型系统保证正确使用
3. **性能优化**：原子操作和内存模型优化
4. **死锁预防**：通过设计模式避免死锁
5. **形式化保证**：严格的语义定义和验证

这些特性使Rust的同步机制既安全又高效，能够满足各种并发编程需求。
