# 5. 并发系统理论基础

## 目录

- [5. 并发系统理论基础](#5-并发系统理论基础)
  - [目录](#目录)
  - [5.1 引言](#51-引言)
    - [5.1.1 并发系统的设计哲学](#511-并发系统的设计哲学)
  - [5.2 并发基础概念](#52-并发基础概念)
    - [5.2.1 并发与并行](#521-并发与并行)
    - [5.2.2 线程模型](#522-线程模型)
    - [5.2.3 并发原语](#523-并发原语)
  - [5.3 Rust并发系统架构](#53-rust并发系统架构)
    - [5.3.1 线程系统](#531-线程系统)
    - [5.3.2 锁机制](#532-锁机制)
    - [5.3.3 原子操作](#533-原子操作)
    - [5.3.4 通道通信](#534-通道通信)
  - [5.4 并发安全保证](#54-并发安全保证)
    - [5.4.1 Send和Sync Trait](#541-send和sync-trait)
    - [5.4.2 数据竞争预防](#542-数据竞争预防)
    - [5.4.3 死锁预防](#543-死锁预防)
  - [5.5 高级并发特性](#55-高级并发特性)
    - [5.5.1 无锁编程](#551-无锁编程)
    - [5.5.2 并发数据结构](#552-并发数据结构)
    - [5.5.3 并发模式](#553-并发模式)
  - [5.6 并发与内存安全](#56-并发与内存安全)
  - [5.7 总结](#57-总结)

## 5.1 引言

Rust的并发系统基于所有权和类型系统，提供了内存安全和线程安全的并发编程模型。通过编译时检查，Rust可以防止数据竞争、死锁等常见的并发问题。

### 5.1.1 并发系统的设计哲学

```rust
// 并发系统的核心价值
fn concurrency_philosophy() {
    // 1. 内存安全 - 编译时防止数据竞争
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
    
    println!("最终计数: {}", *counter.lock().unwrap());
    
    // 2. 零成本抽象 - 并发原语无运行时开销
    use std::sync::atomic::{AtomicUsize, Ordering};
    
    let atomic_counter = AtomicUsize::new(0);
    atomic_counter.fetch_add(1, Ordering::SeqCst);
    
    // 3. 类型安全 - Send和Sync Trait保证线程安全
    // 只有实现了Send的类型才能在线程间传递
    // 只有实现了Sync的类型才能在线程间共享引用
}
```

## 5.2 并发基础概念

### 5.2.1 并发与并行

**并发定义**：

并发是指多个任务在时间上重叠执行，但不一定同时执行。并行是指多个任务真正同时执行。

**形式化表示**：

```latex
并发: ∀t1, t2 ∈ Tasks. ∃t ∈ Time. t1(t) ∧ t2(t)
并行: ∀t1, t2 ∈ Tasks. ∃t ∈ Time. t1(t) ∧ t2(t) ∧ CPU(t1) ≠ CPU(t2)
```

**实现示例**：

```rust
fn concurrency_vs_parallelism() {
    use std::thread;
    use std::time::Duration;
    
    // 并发示例：任务在时间上重叠
    let handle1 = thread::spawn(|| {
        for i in 0..5 {
            println!("任务1: {}", i);
            thread::sleep(Duration::from_millis(100));
        }
    });
    
    let handle2 = thread::spawn(|| {
        for i in 0..5 {
            println!("任务2: {}", i);
            thread::sleep(Duration::from_millis(100));
        }
    });
    
    handle1.join().unwrap();
    handle2.join().unwrap();
    
    // 并行示例：使用rayon库实现真正的并行
    use rayon::prelude::*;
    
    let data = vec![1, 2, 3, 4, 5];
    let result: Vec<i32> = data.par_iter().map(|x| x * 2).collect();
    println!("并行结果: {:?}", result);
}
```

### 5.2.2 线程模型

**线程定义**：

线程是程序执行的最小单位，是CPU调度的基本单位。

**线程状态**：

```rust
// 线程状态的简化模型
#[derive(Debug)]
enum ThreadState {
    New,        // 新建
    Runnable,   // 可运行
    Running,    // 运行中
    Blocked,    // 阻塞
    Terminated, // 终止
}

struct Thread {
    id: usize,
    state: ThreadState,
    stack: Vec<u8>,
}
```

**线程创建与管理**：

```rust
fn thread_management() {
    use std::thread;
    use std::time::Duration;
    
    // 基本线程创建
    let handle = thread::spawn(|| {
        println!("线程开始执行");
        thread::sleep(Duration::from_millis(1000));
        println!("线程执行完成");
    });
    
    // 等待线程完成
    handle.join().unwrap();
    
    // 带参数的线程
    let value = 42;
    let handle = thread::spawn(move || {
        println!("线程中的值: {}", value);
    });
    
    handle.join().unwrap();
    
    // 线程属性设置
    let handle = thread::Builder::new()
        .name("自定义线程".to_string())
        .stack_size(1024 * 1024) // 1MB栈
        .spawn(|| {
            println!("自定义线程执行");
        })
        .unwrap();
    
    handle.join().unwrap();
}
```

### 5.2.3 并发原语

**并发原语定义**：

并发原语是构建并发程序的基本工具，包括锁、信号量、条件变量等。

**基本原语类型**：

```rust
fn concurrency_primitives() {
    // 1. 互斥锁 (Mutex)
    use std::sync::Mutex;
    
    let mutex = Mutex::new(0);
    {
        let mut value = mutex.lock().unwrap();
        *value += 1;
    } // 锁在这里自动释放
    
    // 2. 读写锁 (RwLock)
    use std::sync::RwLock;
    
    let rwlock = RwLock::new(vec![1, 2, 3]);
    {
        let read_guard = rwlock.read().unwrap();
        println!("读取: {:?}", *read_guard);
    }
    {
        let mut write_guard = rwlock.write().unwrap();
        write_guard.push(4);
    }
    
    // 3. 条件变量 (Condvar)
    use std::sync::{Mutex, Condvar};
    
    let pair = (Mutex::new(false), Condvar::new());
    let (lock, cvar) = &pair;
    
    let mut started = lock.lock().unwrap();
    while !*started {
        started = cvar.wait(started).unwrap();
    }
    
    // 4. 信号量 (Semaphore)
    use std::sync::Semaphore;
    
    let semaphore = Semaphore::new(3);
    for _ in 0..5 {
        let _permit = semaphore.acquire().unwrap();
        // 临界区
    }
}
```

## 5.3 Rust并发系统架构

### 5.3.1 线程系统

**线程创建**：

```rust
fn thread_system() {
    use std::thread;
    use std::time::Duration;
    
    // 基本线程创建
    let handle = thread::spawn(|| {
        println!("子线程执行");
    });
    
    println!("主线程执行");
    handle.join().unwrap();
    
    // 线程间数据传递
    let data = vec![1, 2, 3, 4, 5];
    let handle = thread::spawn(move || {
        println!("子线程数据: {:?}", data);
    });
    
    handle.join().unwrap();
    
    // 线程局部存储
    thread_local! {
        static THREAD_ID: std::cell::RefCell<usize> = std::cell::RefCell::new(0);
    }
    
    THREAD_ID.with(|id| {
        *id.borrow_mut() = 42;
        println!("线程ID: {}", *id.borrow());
    });
}
```

**线程池**：

```rust
fn thread_pool() {
    use std::sync::{Arc, Mutex};
    use std::thread;
    use std::collections::VecDeque;
    
    struct ThreadPool {
        workers: Vec<Worker>,
        sender: std::sync::mpsc::Sender<Message>,
    }
    
    struct Worker {
        id: usize,
        thread: Option<thread::JoinHandle<()>>,
    }
    
    enum Message {
        NewJob(Job),
        Terminate,
    }
    
    type Job = Box<dyn FnOnce() + Send + 'static>;
    
    impl ThreadPool {
        fn new(size: usize) -> ThreadPool {
            assert!(size > 0);
            
            let (sender, receiver) = std::sync::mpsc::channel();
            let receiver = Arc::new(Mutex::new(receiver));
            let mut workers = Vec::with_capacity(size);
            
            for id in 0..size {
                workers.push(Worker::new(id, Arc::clone(&receiver)));
            }
            
            ThreadPool { workers, sender }
        }
        
        fn execute<F>(&self, f: F)
        where
            F: FnOnce() + Send + 'static,
        {
            let job = Box::new(f);
            self.sender.send(Message::NewJob(job)).unwrap();
        }
    }
    
    impl Worker {
        fn new(id: usize, receiver: Arc<Mutex<std::sync::mpsc::Receiver<Message>>>) -> Worker {
            let thread = thread::spawn(move || loop {
                let message = receiver.lock().unwrap().recv().unwrap();
                
                match message {
                    Message::NewJob(job) => {
                        println!("Worker {} 执行任务", id);
                        job();
                    }
                    Message::Terminate => {
                        println!("Worker {} 终止", id);
                        break;
                    }
                }
            });
            
            Worker {
                id,
                thread: Some(thread),
            }
        }
    }
    
    // 使用线程池
    let pool = ThreadPool::new(4);
    
    for i in 0..8 {
        pool.execute(move || {
            println!("执行任务 {}", i);
            thread::sleep(Duration::from_millis(100));
        });
    }
}
```

### 5.3.2 锁机制

**互斥锁 (Mutex)**：

```rust
fn mutex_mechanism() {
    use std::sync::Mutex;
    use std::thread;
    
    // 基本Mutex使用
    let counter = Mutex::new(0);
    
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Mutex::clone(&counter);
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
    
    // Mutex错误处理
    let mutex = Mutex::new(0);
    
    // 尝试获取锁
    match mutex.try_lock() {
        Ok(mut guard) => {
            *guard += 1;
            println!("成功获取锁");
        }
        Err(_) => {
            println!("锁被占用");
        }
    }
    
    // 带超时的锁获取
    use std::time::Duration;
    match mutex.try_lock_for(Duration::from_millis(100)) {
        Ok(mut guard) => {
            *guard += 1;
            println!("在超时内获取锁");
        }
        Err(_) => {
            println!("获取锁超时");
        }
    }
}
```

**读写锁 (RwLock)**：

```rust
fn rwlock_mechanism() {
    use std::sync::RwLock;
    use std::thread;
    
    let data = RwLock::new(vec![1, 2, 3, 4, 5]);
    let mut handles = vec![];
    
    // 多个读线程
    for i in 0..3 {
        let data = RwLock::clone(&data);
        let handle = thread::spawn(move || {
            let read_guard = data.read().unwrap();
            println!("读线程 {}: {:?}", i, *read_guard);
        });
        handles.push(handle);
    }
    
    // 写线程
    let data = RwLock::clone(&data);
    let handle = thread::spawn(move || {
        let mut write_guard = data.write().unwrap();
        write_guard.push(6);
        println!("写线程: 添加元素");
    });
    handles.push(handle);
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("最终数据: {:?}", *data.read().unwrap());
}
```

### 5.3.3 原子操作

**原子类型**：

```rust
fn atomic_operations() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::thread;
    
    // 基本原子操作
    let atomic_counter = AtomicUsize::new(0);
    
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = &atomic_counter;
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                counter.fetch_add(1, Ordering::SeqCst);
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("原子计数: {}", atomic_counter.load(Ordering::SeqCst));
    
    // 内存序 (Memory Ordering)
    let atomic_bool = std::sync::atomic::AtomicBool::new(false);
    
    // Relaxed - 最弱的内存序
    atomic_bool.store(true, Ordering::Relaxed);
    
    // Acquire - 获取操作
    let value = atomic_bool.load(Ordering::Acquire);
    
    // Release - 释放操作
    atomic_bool.store(false, Ordering::Release);
    
    // AcqRel - 获取释放操作
    atomic_bool.compare_exchange(false, true, Ordering::AcqRel, Ordering::Relaxed);
    
    // SeqCst - 顺序一致性
    atomic_bool.store(true, Ordering::SeqCst);
}
```

**原子比较交换**：

```rust
fn atomic_compare_exchange() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    
    let atomic_value = AtomicUsize::new(0);
    
    // 比较并交换
    let result = atomic_value.compare_exchange(
        0,    // 期望值
        1,    // 新值
        Ordering::SeqCst,  // 成功时的内存序
        Ordering::Relaxed, // 失败时的内存序
    );
    
    match result {
        Ok(old_value) => {
            println!("交换成功，旧值: {}", old_value);
        }
        Err(current_value) => {
            println!("交换失败，当前值: {}", current_value);
        }
    }
    
    // 弱比较交换
    let weak_result = atomic_value.compare_exchange_weak(
        1,
        2,
        Ordering::SeqCst,
        Ordering::Relaxed,
    );
    
    match weak_result {
        Ok(old_value) => {
            println!("弱交换成功，旧值: {}", old_value);
        }
        Err(current_value) => {
            println!("弱交换失败，当前值: {}", current_value);
        }
    }
}
```

### 5.3.4 通道通信

**基本通道**：

```rust
fn channel_communication() {
    use std::sync::mpsc;
    use std::thread;
    
    // 创建通道
    let (sender, receiver) = mpsc::channel();
    
    // 发送线程
    let sender_handle = thread::spawn(move || {
        for i in 0..5 {
            sender.send(i).unwrap();
            println!("发送: {}", i);
        }
    });
    
    // 接收线程
    let receiver_handle = thread::spawn(move || {
        for received in receiver {
            println!("接收: {}", received);
        }
    });
    
    sender_handle.join().unwrap();
    receiver_handle.join().unwrap();
    
    // 多发送者通道
    let (sender, receiver) = mpsc::channel();
    let sender1 = sender.clone();
    let sender2 = sender.clone();
    
    let handle1 = thread::spawn(move || {
        for i in 0..3 {
            sender1.send(format!("发送者1: {}", i)).unwrap();
        }
    });
    
    let handle2 = thread::spawn(move || {
        for i in 0..3 {
            sender2.send(format!("发送者2: {}", i)).unwrap();
        }
    });
    
    drop(sender); // 关闭主发送者
    
    for received in receiver {
        println!("接收: {}", received);
    }
    
    handle1.join().unwrap();
    handle2.join().unwrap();
}
```

**异步通道**：

```rust
fn async_channel() {
    use std::sync::mpsc;
    use std::thread;
    use std::time::Duration;
    
    // 异步通道（无界）
    let (sender, receiver) = mpsc::channel();
    
    let sender_handle = thread::spawn(move || {
        for i in 0..10 {
            sender.send(i).unwrap();
            thread::sleep(Duration::from_millis(100));
        }
    });
    
    let receiver_handle = thread::spawn(move || {
        for received in receiver {
            println!("异步接收: {}", received);
        }
    });
    
    sender_handle.join().unwrap();
    receiver_handle.join().unwrap();
    
    // 同步通道（有界）
    let (sender, receiver) = mpsc::sync_channel(3); // 缓冲区大小为3
    
    let sender_handle = thread::spawn(move || {
        for i in 0..10 {
            sender.send(i).unwrap();
            println!("同步发送: {}", i);
        }
    });
    
    let receiver_handle = thread::spawn(move || {
        for received in receiver {
            println!("同步接收: {}", received);
            thread::sleep(Duration::from_millis(200));
        }
    });
    
    sender_handle.join().unwrap();
    receiver_handle.join().unwrap();
}
```

## 5.4 并发安全保证

### 5.4.1 Send和Sync Trait

**Send Trait**：

```rust
fn send_trait() {
    // Send Trait表示类型可以安全地在线程间转移所有权
    use std::thread;
    
    // 基本类型都实现了Send
    let x = 42;
    let handle = thread::spawn(move || {
        println!("线程中的值: {}", x);
    });
    handle.join().unwrap();
    
    // 自定义Send类型
    struct SafeStruct {
        data: i32,
    }
    
    // 自动实现Send（因为所有字段都实现了Send）
    let safe_struct = SafeStruct { data: 42 };
    let handle = thread::spawn(move || {
        println!("安全结构体: {}", safe_struct.data);
    });
    handle.join().unwrap();
    
    // 非Send类型示例
    struct NonSendStruct {
        _data: std::rc::Rc<i32>, // Rc不是Send
    }
    
    // 以下代码会编译错误
    // let non_send = NonSendStruct { _data: std::rc::Rc::new(42) };
    // let handle = thread::spawn(move || {
    //     println!("非Send结构体");
    // });
}
```

**Sync Trait**：

```rust
fn sync_trait() {
    // Sync Trait表示类型可以安全地在线程间共享引用
    use std::sync::{Arc, Mutex};
    use std::thread;
    
    // Arc实现了Sync
    let shared_data = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..3 {
        let data = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            let mut value = data.lock().unwrap();
            *value += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("共享数据: {}", *shared_data.lock().unwrap());
    
    // 自定义Sync类型
    struct SafeSharedStruct {
        data: Mutex<i32>,
    }
    
    // 自动实现Sync（因为所有字段都实现了Sync）
    let safe_shared = Arc::new(SafeSharedStruct {
        data: Mutex::new(0),
    });
    
    let mut handles = vec![];
    for _ in 0..3 {
        let shared = Arc::clone(&safe_shared);
        let handle = thread::spawn(move || {
            let mut value = shared.data.lock().unwrap();
            *value += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 5.4.2 数据竞争预防

**数据竞争定义**：

数据竞争是指两个或多个线程同时访问同一内存位置，其中至少有一个是写操作，且没有同步机制。

**Rust的预防机制**：

```rust
fn data_race_prevention() {
    use std::sync::{Arc, Mutex};
    use std::thread;
    
    // 1. 使用Mutex防止数据竞争
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut value = counter.lock().unwrap();
            *value += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("安全计数: {}", *counter.lock().unwrap());
    
    // 2. 使用原子操作
    use std::sync::atomic::{AtomicUsize, Ordering};
    
    let atomic_counter = AtomicUsize::new(0);
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = &atomic_counter;
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                counter.fetch_add(1, Ordering::SeqCst);
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("原子计数: {}", atomic_counter.load(Ordering::SeqCst));
    
    // 3. 使用通道避免共享状态
    use std::sync::mpsc;
    
    let (sender, receiver) = mpsc::channel();
    let mut handles = vec![];
    
    for i in 0..5 {
        let sender = sender.clone();
        let handle = thread::spawn(move || {
            sender.send(i).unwrap();
        });
        handles.push(handle);
    }
    
    drop(sender); // 关闭发送者
    
    for received in receiver {
        println!("接收: {}", received);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 5.4.3 死锁预防

**死锁定义**：

死锁是指两个或多个线程互相等待对方持有的资源，导致所有线程都无法继续执行。

**死锁预防策略**：

```rust
fn deadlock_prevention() {
    use std::sync::{Arc, Mutex};
    use std::thread;
    use std::time::Duration;
    
    // 1. 锁的顺序化
    let lock1 = Arc::new(Mutex::new(0));
    let lock2 = Arc::new(Mutex::new(0));
    
    let lock1_clone = Arc::clone(&lock1);
    let lock2_clone = Arc::clone(&lock2);
    
    let handle1 = thread::spawn(move || {
        let _guard1 = lock1_clone.lock().unwrap();
        thread::sleep(Duration::from_millis(100));
        let _guard2 = lock2_clone.lock().unwrap();
        println!("线程1获得两个锁");
    });
    
    let handle2 = thread::spawn(move || {
        let _guard1 = lock1.lock().unwrap(); // 相同的锁顺序
        thread::sleep(Duration::from_millis(100));
        let _guard2 = lock2.lock().unwrap();
        println!("线程2获得两个锁");
    });
    
    handle1.join().unwrap();
    handle2.join().unwrap();
    
    // 2. 超时机制
    let mutex = Arc::new(Mutex::new(0));
    let mutex_clone = Arc::clone(&mutex);
    
    let handle = thread::spawn(move || {
        // 尝试获取锁，带超时
        match mutex_clone.try_lock_for(Duration::from_millis(100)) {
            Ok(_guard) => {
                println!("成功获取锁");
            }
            Err(_) => {
                println!("获取锁超时，避免死锁");
            }
        }
    });
    
    // 主线程持有锁
    let _guard = mutex.lock().unwrap();
    thread::sleep(Duration::from_millis(200));
    
    handle.join().unwrap();
    
    // 3. 使用try_lock避免阻塞
    let mutex1 = Arc::new(Mutex::new(0));
    let mutex2 = Arc::new(Mutex::new(0));
    
    let mutex1_clone = Arc::clone(&mutex1);
    let mutex2_clone = Arc::clone(&mutex2);
    
    let handle = thread::spawn(move || {
        loop {
            // 尝试获取第一个锁
            if let Ok(guard1) = mutex1_clone.try_lock() {
                // 尝试获取第二个锁
                if let Ok(guard2) = mutex2_clone.try_lock() {
                    println!("成功获取两个锁");
                    break;
                }
                // 释放第一个锁
                drop(guard1);
            }
            thread::sleep(Duration::from_millis(10));
        }
    });
    
    handle.join().unwrap();
}
```

## 5.5 高级并发特性

### 5.5.1 无锁编程

**无锁数据结构**：

```rust
fn lock_free_programming() {
    use std::sync::atomic::{AtomicPtr, Ordering};
    use std::ptr;
    
    // 无锁栈实现
    struct Node<T> {
        data: T,
        next: AtomicPtr<Node<T>>,
    }
    
    struct LockFreeStack<T> {
        head: AtomicPtr<Node<T>>,
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
                next: AtomicPtr::new(ptr::null_mut()),
            }));
            
            loop {
                let head = self.head.load(Ordering::Acquire);
                unsafe {
                    (*new_node).next.store(head, Ordering::Relaxed);
                }
                
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
                
                let next = unsafe { (*head).next.load(Ordering::Relaxed) };
                
                if self.head.compare_exchange_weak(
                    head,
                    next,
                    Ordering::Release,
                    Ordering::Relaxed,
                ).is_ok() {
                    unsafe {
                        let data = ptr::read(&(*head).data);
                        drop(Box::from_raw(head));
                        return Some(data);
                    }
                }
            }
        }
    }
    
    // 使用无锁栈
    let stack = LockFreeStack::new();
    stack.push(1);
    stack.push(2);
    stack.push(3);
    
    while let Some(value) = stack.pop() {
        println!("弹出: {}", value);
    }
}
```

### 5.5.2 并发数据结构

**并发HashMap**：

```rust
fn concurrent_data_structures() {
    use std::collections::HashMap;
    use std::sync::{Arc, RwLock};
    use std::thread;
    
    // 并发HashMap
    struct ConcurrentHashMap<K, V> {
        data: Arc<RwLock<HashMap<K, V>>>,
    }
    
    impl<K, V> ConcurrentHashMap<K, V>
    where
        K: Eq + std::hash::Hash + Clone,
        V: Clone,
    {
        fn new() -> Self {
            ConcurrentHashMap {
                data: Arc::new(RwLock::new(HashMap::new())),
            }
        }
        
        fn insert(&self, key: K, value: V) {
            let mut map = self.data.write().unwrap();
            map.insert(key, value);
        }
        
        fn get(&self, key: &K) -> Option<V> {
            let map = self.data.read().unwrap();
            map.get(key).cloned()
        }
        
        fn remove(&self, key: &K) -> Option<V> {
            let mut map = self.data.write().unwrap();
            map.remove(key)
        }
    }
    
    // 使用并发HashMap
    let map = ConcurrentHashMap::new();
    let mut handles = vec![];
    
    // 多个写线程
    for i in 0..5 {
        let map = Arc::new(map);
        let handle = thread::spawn(move || {
            map.insert(format!("key{}", i), i);
        });
        handles.push(handle);
    }
    
    // 多个读线程
    for i in 0..5 {
        let map = Arc::new(map);
        let handle = thread::spawn(move || {
            if let Some(value) = map.get(&format!("key{}", i)) {
                println!("读取 key{}: {}", i, value);
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 5.5.3 并发模式

**生产者-消费者模式**：

```rust
fn producer_consumer_pattern() {
    use std::sync::mpsc;
    use std::thread;
    use std::time::Duration;
    
    // 生产者-消费者模式
    let (sender, receiver) = mpsc::channel();
    let mut handles = vec![];
    
    // 生产者
    for i in 0..3 {
        let sender = sender.clone();
        let handle = thread::spawn(move || {
            for j in 0..5 {
                sender.send(format!("生产者{}: 项目{}", i, j)).unwrap();
                thread::sleep(Duration::from_millis(100));
            }
        });
        handles.push(handle);
    }
    
    // 消费者
    let consumer_handle = thread::spawn(move || {
        for received in receiver {
            println!("消费: {}", received);
            thread::sleep(Duration::from_millis(50));
        }
    });
    
    drop(sender); // 关闭所有发送者
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    consumer_handle.join().unwrap();
    
    // 工作池模式
    use std::sync::{Arc, Mutex};
    
    struct WorkPool {
        workers: Vec<Worker>,
        sender: mpsc::Sender<Job>,
    }
    
    struct Worker {
        id: usize,
        thread: Option<thread::JoinHandle<()>>,
    }
    
    type Job = Box<dyn FnOnce() + Send + 'static>;
    
    impl WorkPool {
        fn new(size: usize) -> WorkPool {
            let (sender, receiver) = mpsc::channel();
            let receiver = Arc::new(Mutex::new(receiver));
            let mut workers = Vec::with_capacity(size);
            
            for id in 0..size {
                workers.push(Worker::new(id, Arc::clone(&receiver)));
            }
            
            WorkPool { workers, sender }
        }
        
        fn execute<F>(&self, f: F)
        where
            F: FnOnce() + Send + 'static,
        {
            let job = Box::new(f);
            self.sender.send(job).unwrap();
        }
    }
    
    impl Worker {
        fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Job>>>) -> Worker {
            let thread = thread::spawn(move || loop {
                let job = receiver.lock().unwrap().recv();
                
                match job {
                    Ok(job) => {
                        println!("Worker {} 执行任务", id);
                        job();
                    }
                    Err(_) => {
                        println!("Worker {} 终止", id);
                        break;
                    }
                }
            });
            
            Worker {
                id,
                thread: Some(thread),
            }
        }
    }
    
    // 使用工作池
    let pool = WorkPool::new(4);
    
    for i in 0..8 {
        pool.execute(move || {
            println!("执行任务 {}", i);
            thread::sleep(Duration::from_millis(100));
        });
    }
}
```

## 5.6 并发与内存安全

**并发内存安全保证**：

```rust
fn concurrency_memory_safety() {
    use std::sync::{Arc, Mutex};
    use std::thread;
    
    // 1. 所有权系统防止数据竞争
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    for i in 0..3 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let mut vec = data.lock().unwrap();
            vec.push(i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("安全数据: {:?}", *data.lock().unwrap());
    
    // 2. 生命周期系统防止悬垂引用
    let value = 42;
    let handle = thread::spawn(move || {
        println!("线程中的值: {}", value);
    });
    
    handle.join().unwrap();
    
    // 3. 类型系统保证线程安全
    // 只有实现了Send的类型才能在线程间传递
    // 只有实现了Sync的类型才能在线程间共享引用
    
    // 4. 编译时检查并发错误
    // Rust编译器会在编译时检查并发安全问题
    // 防止数据竞争、死锁等并发错误
}
```

## 5.7 总结

Rust的并发系统通过以下机制提供安全保障：

1. **编译时检查**：Send和Sync Trait确保线程安全
2. **所有权系统**：防止数据竞争和悬垂引用
3. **类型系统**：保证并发操作的类型安全
4. **零成本抽象**：并发原语无运行时开销

**核心优势**：

- 编译时并发安全保证
- 零运行时开销
- 内存安全保证
- 防止数据竞争
- 防止死锁

**适用场景**：

- 高性能并发应用
- 服务器编程
- 并行计算
- 实时系统
- 多线程数据处理

并发系统是Rust语言的重要组成部分，与所有权系统和类型系统共同构成了Rust的安全基础。
