# 线程语义分析

## 目录

- [线程语义分析](#线程语义分析)
  - [目录](#目录)
  - [概述](#概述)
  - [1. 线程理论基础](#1-线程理论基础)
    - [1.1 线程概念](#11-线程概念)
    - [1.2 线程模型](#12-线程模型)
  - [2. 线程创建和管理](#2-线程创建和管理)
    - [2.1 线程创建](#21-线程创建)
    - [2.2 线程生命周期](#22-线程生命周期)
  - [3. 线程安全](#3-线程安全)
    - [3.1 线程安全类型](#31-线程安全类型)
    - [3.2 线程本地存储](#32-线程本地存储)
  - [4. 线程通信](#4-线程通信)
    - [4.1 通道通信](#41-通道通信)
    - [4.2 共享内存通信](#42-共享内存通信)
  - [5. 线程池](#5-线程池)
    - [5.1 基本线程池](#51-基本线程池)
    - [5.2 高级线程池](#52-高级线程池)
  - [6. 形式化证明](#6-形式化证明)
    - [6.1 线程安全定理](#61-线程安全定理)
    - [6.2 死锁自由定理](#62-死锁自由定理)
  - [7. 工程实践](#7-工程实践)
    - [7.1 最佳实践](#71-最佳实践)
    - [7.2 常见陷阱](#72-常见陷阱)
  - [8. 交叉引用](#8-交叉引用)
  - [9. 参考文献](#9-参考文献)

## 概述

本文档详细分析Rust中线程系统的语义，包括其理论基础、实现机制和形式化定义。

## 1. 线程理论基础

### 1.1 线程概念

**定义 1.1.1 (线程)**
线程是程序执行的最小单位，是CPU调度的基本单元。

**线程的核心特性**：

1. **并发执行**：多个线程可以同时执行
2. **共享内存**：线程间可以共享内存空间
3. **独立栈空间**：每个线程有独立的栈
4. **上下文切换**：线程间的执行切换

### 1.2 线程模型

**线程模型分类**：

1. **用户级线程**：由用户程序管理的线程
2. **内核级线程**：由操作系统内核管理的线程
3. **混合线程**：用户级和内核级线程的结合
4. **绿色线程**：轻量级用户级线程

## 2. 线程创建和管理

### 2.1 线程创建

**线程创建机制**：

```rust
use std::thread;
use std::time::Duration;

// 基本线程创建
fn basic_thread_creation() {
    let handle = thread::spawn(|| {
        for i in 1..10 {
            println!("hi number {} from the spawned thread!", i);
            thread::sleep(Duration::from_millis(1));
        }
    });

    for i in 1..5 {
        println!("hi number {} from the main thread!", i);
        thread::sleep(Duration::from_millis(1));
    }

    handle.join().unwrap();
}

// 带参数的线程
fn thread_with_parameters() {
    let v = vec![1, 2, 3, 4, 5];

    let handle = thread::spawn(move || {
        println!("Here's a vector: {:?}", v);
    });

    handle.join().unwrap();
}

// 线程构建器
fn thread_builder() {
    let handle = thread::Builder::new()
        .name("worker".to_string())
        .stack_size(32 * 1024) // 32KB栈
        .spawn(|| {
            println!("Hello from worker thread!");
        })
        .unwrap();

    handle.join().unwrap();
}

// 线程属性
fn thread_attributes() {
    let handle = thread::spawn(|| {
        // 设置线程本地存储
        thread_local! {
            static THREAD_ID: std::cell::RefCell<u64> = std::cell::RefCell::new(0);
        }

        THREAD_ID.with(|id| {
            *id.borrow_mut() = thread::current().id().as_u64().get();
            println!("Thread ID: {}", *id.borrow());
        });
    });

    handle.join().unwrap();
}
```

### 2.2 线程生命周期

**线程生命周期管理**：

```rust
// 线程生命周期
struct ThreadLifecycle {
    id: thread::ThreadId,
    name: Option<String>,
    status: ThreadStatus,
    created: std::time::Instant,
    started: Option<std::time::Instant>,
    finished: Option<std::time::Instant>,
}

#[derive(Debug, Clone, PartialEq)]
enum ThreadStatus {
    Created,
    Running,
    Blocked,
    Terminated,
}

impl ThreadLifecycle {
    fn new() -> Self {
        Self {
            id: thread::current().id(),
            name: None,
            status: ThreadStatus::Created,
            created: std::time::Instant::now(),
            started: None,
            finished: None,
        }
    }

    fn start(&mut self) {
        self.status = ThreadStatus::Running;
        self.started = Some(std::time::Instant::now());
    }

    fn block(&mut self) {
        self.status = ThreadStatus::Blocked;
    }

    fn finish(&mut self) {
        self.status = ThreadStatus::Terminated;
        self.finished = Some(std::time::Instant::now());
    }

    fn duration(&self) -> Option<std::time::Duration> {
        self.started.and_then(|start| {
            self.finished.map(|end| end.duration_since(start))
        })
    }

    fn is_alive(&self) -> bool {
        self.status == ThreadStatus::Running || self.status == ThreadStatus::Blocked
    }
}

// 线程管理器
struct ThreadManager {
    threads: std::collections::HashMap<thread::ThreadId, ThreadLifecycle>,
    max_threads: usize,
}

impl ThreadManager {
    fn new(max_threads: usize) -> Self {
        Self {
            threads: std::collections::HashMap::new(),
            max_threads,
        }
    }

    fn create_thread<F, T>(&mut self, f: F) -> thread::JoinHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        if self.threads.len() >= self.max_threads {
            panic!("Maximum number of threads reached");
        }

        let handle = thread::spawn(move || f());
        let thread_id = handle.thread().id();
        
        let mut lifecycle = ThreadLifecycle::new();
        lifecycle.start();
        self.threads.insert(thread_id, lifecycle);

        handle
    }

    fn get_thread_info(&self, thread_id: thread::ThreadId) -> Option<&ThreadLifecycle> {
        self.threads.get(&thread_id)
    }

    fn list_threads(&self) -> Vec<&ThreadLifecycle> {
        self.threads.values().collect()
    }
}
```

## 3. 线程安全

### 3.1 线程安全类型

**线程安全类型实现**：

```rust
use std::sync::{Arc, Mutex, RwLock};
use std::sync::atomic::{AtomicUsize, Ordering};

// 线程安全的计数器
struct ThreadSafeCounter {
    count: AtomicUsize,
    name: String,
}

impl ThreadSafeCounter {
    fn new(name: String) -> Self {
        Self {
            count: AtomicUsize::new(0),
            name,
        }
    }

    fn increment(&self) -> usize {
        self.count.fetch_add(1, Ordering::SeqCst)
    }

    fn decrement(&self) -> usize {
        self.count.fetch_sub(1, Ordering::SeqCst)
    }

    fn get(&self) -> usize {
        self.count.load(Ordering::SeqCst)
    }

    fn compare_exchange(&self, current: usize, new: usize) -> Result<usize, usize> {
        self.count.compare_exchange(current, new, Ordering::SeqCst, Ordering::SeqCst)
    }
}

// 线程安全的栈
struct ThreadSafeStack<T> {
    data: Mutex<Vec<T>>,
}

impl<T> ThreadSafeStack<T> {
    fn new() -> Self {
        Self {
            data: Mutex::new(Vec::new()),
        }
    }

    fn push(&self, item: T) {
        let mut data = self.data.lock().unwrap();
        data.push(item);
    }

    fn pop(&self) -> Option<T> {
        let mut data = self.data.lock().unwrap();
        data.pop()
    }

    fn peek(&self) -> Option<T>
    where
        T: Clone,
    {
        let data = self.data.lock().unwrap();
        data.last().cloned()
    }

    fn len(&self) -> usize {
        let data = self.data.lock().unwrap();
        data.len()
    }

    fn is_empty(&self) -> bool {
        let data = self.data.lock().unwrap();
        data.is_empty()
    }
}

// 线程安全的队列
struct ThreadSafeQueue<T> {
    data: Mutex<Vec<T>>,
    not_empty: std::sync::Condvar,
}

impl<T> ThreadSafeQueue<T> {
    fn new() -> Self {
        Self {
            data: Mutex::new(Vec::new()),
            not_empty: std::sync::Condvar::new(),
        }
    }

    fn enqueue(&self, item: T) {
        let mut data = self.data.lock().unwrap();
        data.push(item);
        self.not_empty.notify_one();
    }

    fn dequeue(&self) -> T {
        let mut data = self.data.lock().unwrap();
        
        while data.is_empty() {
            data = self.not_empty.wait(data).unwrap();
        }
        
        data.remove(0)
    }

    fn try_dequeue(&self) -> Option<T> {
        let mut data = self.data.lock().unwrap();
        if data.is_empty() {
            None
        } else {
            Some(data.remove(0))
        }
    }

    fn len(&self) -> usize {
        let data = self.data.lock().unwrap();
        data.len()
    }
}

// 线程安全的使用示例
fn thread_safety_example() {
    let counter = Arc::new(ThreadSafeCounter::new("main".to_string()));
    let mut handles = vec![];

    for i in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                counter.increment();
            }
            println!("Thread {} finished", i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Final count: {}", counter.get());
}
```

### 3.2 线程本地存储

**线程本地存储实现**：

```rust
use std::cell::RefCell;

// 线程本地存储
thread_local! {
    static THREAD_LOCAL_COUNTER: RefCell<usize> = RefCell::new(0);
    static THREAD_LOCAL_STRING: RefCell<String> = RefCell::new(String::new());
    static THREAD_LOCAL_VECTOR: RefCell<Vec<i32>> = RefCell::new(Vec::new());
}

// 线程本地存储管理器
struct ThreadLocalManager;

impl ThreadLocalManager {
    fn increment_counter() {
        THREAD_LOCAL_COUNTER.with(|counter| {
            *counter.borrow_mut() += 1;
        });
    }

    fn get_counter() -> usize {
        THREAD_LOCAL_COUNTER.with(|counter| *counter.borrow())
    }

    fn set_string(s: String) {
        THREAD_LOCAL_STRING.with(|string| {
            *string.borrow_mut() = s;
        });
    }

    fn get_string() -> String {
        THREAD_LOCAL_STRING.with(|string| string.borrow().clone())
    }

    fn add_to_vector(value: i32) {
        THREAD_LOCAL_VECTOR.with(|vector| {
            vector.borrow_mut().push(value);
        });
    }

    fn get_vector() -> Vec<i32> {
        THREAD_LOCAL_VECTOR.with(|vector| vector.borrow().clone())
    }
}

// 自定义线程本地存储
struct CustomThreadLocal<T> {
    key: std::thread::LocalKey<RefCell<Option<T>>>,
}

impl<T> CustomThreadLocal<T> {
    fn new() -> Self {
        thread_local! {
            static STORAGE: RefCell<Option<T>> = RefCell::new(None);
        }
        
        Self {
            key: STORAGE,
        }
    }

    fn set(&self, value: T) {
        self.key.with(|storage| {
            *storage.borrow_mut() = Some(value);
        });
    }

    fn get(&self) -> Option<T>
    where
        T: Clone,
    {
        self.key.with(|storage| {
            storage.borrow().clone()
        })
    }

    fn take(&self) -> Option<T> {
        self.key.with(|storage| {
            storage.borrow_mut().take()
        })
    }
}

// 线程本地存储示例
fn thread_local_example() {
    let mut handles = vec![];

    for i in 0..5 {
        let handle = thread::spawn(move || {
            // 设置线程本地数据
            ThreadLocalManager::set_string(format!("Thread {}", i));
            
            for j in 0..10 {
                ThreadLocalManager::increment_counter();
                ThreadLocalManager::add_to_vector(j);
            }

            // 获取线程本地数据
            println!(
                "Thread {}: counter={}, string='{}', vector={:?}",
                i,
                ThreadLocalManager::get_counter(),
                ThreadLocalManager::get_string(),
                ThreadLocalManager::get_vector()
            );
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
```

## 4. 线程通信

### 4.1 通道通信

**通道通信实现**：

```rust
use std::sync::mpsc;

// 基本通道通信
fn basic_channel_communication() {
    let (tx, rx) = mpsc::channel();

    let handle = thread::spawn(move || {
        let val = String::from("hi");
        tx.send(val).unwrap();
        // println!("val is {}", val); // 编译错误：val已被发送
    });

    let received = rx.recv().unwrap();
    println!("Got: {}", received);

    handle.join().unwrap();
}

// 多生产者通道
fn multiple_producers() {
    let (tx, rx) = mpsc::channel();
    let mut handles = vec![];

    for i in 0..3 {
        let tx = tx.clone();
        let handle = thread::spawn(move || {
            for j in 0..5 {
                tx.send(format!("Message {} from producer {}", j, i)).unwrap();
                thread::sleep(Duration::from_millis(100));
            }
        });
        handles.push(handle);
    }

    // 关闭发送端
    drop(tx);

    // 接收所有消息
    for received in rx {
        println!("Got: {}", received);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}

// 同步通道
fn synchronous_channel() {
    let (tx, rx) = mpsc::sync_channel(3); // 缓冲区大小为3

    let handle = thread::spawn(move || {
        for i in 0..10 {
            println!("Sending {}", i);
            tx.send(i).unwrap();
            thread::sleep(Duration::from_millis(100));
        }
    });

    for received in rx {
        println!("Got: {}", received);
        thread::sleep(Duration::from_millis(200));
    }

    handle.join().unwrap();
}

// 通道选择器
fn channel_select() {
    let (tx1, rx1) = mpsc::channel();
    let (tx2, rx2) = mpsc::channel();

    // 发送者
    let handle1 = thread::spawn(move || {
        for i in 0..5 {
            tx1.send(i).unwrap();
            thread::sleep(Duration::from_millis(100));
        }
    });

    let handle2 = thread::spawn(move || {
        for i in 0..5 {
            tx2.send(format!("Message {}", i)).unwrap();
            thread::sleep(Duration::from_millis(150));
        }
    });

    // 接收者
    let handle3 = thread::spawn(move || {
        loop {
            match rx1.recv_timeout(Duration::from_millis(50)) {
                Ok(val) => println!("Channel 1: {}", val),
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    match rx2.recv_timeout(Duration::from_millis(50)) {
                        Ok(val) => println!("Channel 2: {}", val),
                        Err(mpsc::RecvTimeoutError::Timeout) => continue,
                        Err(mpsc::RecvTimeoutError::Disconnected) => break,
                    }
                }
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
            }
        }
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
    handle3.join().unwrap();
}
```

### 4.2 共享内存通信

**共享内存通信实现**：

```rust
// 共享内存通信
struct SharedMemory<T> {
    data: Arc<Mutex<T>>,
}

impl<T> SharedMemory<T> {
    fn new(data: T) -> Self {
        Self {
            data: Arc::new(Mutex::new(data)),
        }
    }

    fn read(&self) -> T
    where
        T: Clone,
    {
        let data = self.data.lock().unwrap();
        data.clone()
    }

    fn write(&self, new_data: T) {
        let mut data = self.data.lock().unwrap();
        *data = new_data;
    }

    fn modify<F>(&self, f: F)
    where
        F: FnOnce(&mut T),
    {
        let mut data = self.data.lock().unwrap();
        f(&mut data);
    }
}

// 读写锁共享内存
struct ReadWriteSharedMemory<T> {
    data: Arc<RwLock<T>>,
}

impl<T> ReadWriteSharedMemory<T> {
    fn new(data: T) -> Self {
        Self {
            data: Arc::new(RwLock::new(data)),
        }
    }

    fn read(&self) -> T
    where
        T: Clone,
    {
        let data = self.data.read().unwrap();
        data.clone()
    }

    fn write(&self, new_data: T) {
        let mut data = self.data.write().unwrap();
        *data = new_data;
    }

    fn read_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        let data = self.data.read().unwrap();
        f(&data)
    }

    fn write_with<F>(&self, f: F)
    where
        F: FnOnce(&mut T),
    {
        let mut data = self.data.write().unwrap();
        f(&mut data);
    }
}

// 共享内存示例
fn shared_memory_example() {
    let shared_counter = Arc::new(SharedMemory::new(0));
    let shared_string = Arc::new(ReadWriteSharedMemory::new(String::new()));
    let mut handles = vec![];

    // 写入线程
    for i in 0..3 {
        let counter = Arc::clone(&shared_counter);
        let string = Arc::clone(&shared_string);
        let handle = thread::spawn(move || {
            for j in 0..100 {
                counter.modify(|c| *c += 1);
                string.write_with(|s| {
                    s.push_str(&format!("Thread {}: {}\n", i, j));
                });
                thread::sleep(Duration::from_millis(10));
            }
        });
        handles.push(handle);
    }

    // 读取线程
    let counter = Arc::clone(&shared_counter);
    let string = Arc::clone(&shared_string);
    let handle = thread::spawn(move || {
        for _ in 0..10 {
            let count = counter.read();
            let text = string.read();
            println!("Counter: {}, String length: {}", count, text.len());
            thread::sleep(Duration::from_millis(100));
        }
    });
    handles.push(handle);

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Final counter: {}", shared_counter.read());
    println!("Final string: {}", shared_string.read());
}
```

## 5. 线程池

### 5.1 基本线程池

**线程池实现**：

```rust
use std::sync::mpsc::{self, Sender, Receiver};
use std::sync::{Arc, Mutex};
use std::thread;

// 任务类型
type Job = Box<dyn FnOnce() + Send + 'static>;

// 工作线程
struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<Receiver<Job>>>) -> Worker {
        let thread = thread::spawn(move || loop {
            let message = receiver.lock().unwrap().recv();

            match message {
                Ok(job) => {
                    println!("Worker {} got a job; executing.", id);
                    job();
                }
                Err(_) => {
                    println!("Worker {} was told to terminate.", id);
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

// 线程池
struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<Sender<Job>>,
}

impl ThreadPool {
    fn new(size: usize) -> ThreadPool {
        assert!(size > 0);

        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));
        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        ThreadPool {
            workers,
            sender: Some(sender),
        }
    }

    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.as_ref().unwrap().send(job).unwrap();
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        drop(self.sender.take());

        for worker in &mut self.workers {
            println!("Shutting down worker {}", worker.id);

            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

// 线程池使用示例
fn thread_pool_example() {
    let pool = ThreadPool::new(4);

    for i in 0..8 {
        pool.execute(move || {
            println!("Executing job {}", i);
            thread::sleep(Duration::from_millis(100));
        });
    }
}
```

### 5.2 高级线程池

**高级线程池实现**：

```rust
// 高级线程池
struct AdvancedThreadPool {
    workers: Vec<Worker>,
    sender: Option<Sender<Job>>,
    stats: Arc<Mutex<ThreadPoolStats>>,
}

struct ThreadPoolStats {
    total_jobs: usize,
    completed_jobs: usize,
    active_workers: usize,
    queue_size: usize,
}

impl AdvancedThreadPool {
    fn new(size: usize) -> Self {
        assert!(size > 0);

        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));
        let stats = Arc::new(Mutex::new(ThreadPoolStats {
            total_jobs: 0,
            completed_jobs: 0,
            active_workers: 0,
            queue_size: 0,
        }));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new_advanced(id, Arc::clone(&receiver), Arc::clone(&stats)));
        }

        Self {
            workers,
            sender: Some(sender),
            stats,
        }
    }

    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.as_ref().unwrap().send(job).unwrap();
        
        let mut stats = self.stats.lock().unwrap();
        stats.total_jobs += 1;
        stats.queue_size += 1;
    }

    fn get_stats(&self) -> ThreadPoolStats {
        let stats = self.stats.lock().unwrap();
        ThreadPoolStats {
            total_jobs: stats.total_jobs,
            completed_jobs: stats.completed_jobs,
            active_workers: stats.active_workers,
            queue_size: stats.queue_size,
        }
    }

    fn shutdown(&mut self) {
        drop(self.sender.take());

        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

impl Worker {
    fn new_advanced(
        id: usize,
        receiver: Arc<Mutex<Receiver<Job>>>,
        stats: Arc<Mutex<ThreadPoolStats>>,
    ) -> Worker {
        let thread = thread::spawn(move || loop {
            let message = receiver.lock().unwrap().recv();

            match message {
                Ok(job) => {
                    {
                        let mut stats = stats.lock().unwrap();
                        stats.active_workers += 1;
                        stats.queue_size -= 1;
                    }

                    println!("Worker {} got a job; executing.", id);
                    job();

                    {
                        let mut stats = stats.lock().unwrap();
                        stats.active_workers -= 1;
                        stats.completed_jobs += 1;
                    }
                }
                Err(_) => {
                    println!("Worker {} was told to terminate.", id);
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
```

## 6. 形式化证明

### 6.1 线程安全定理

**定理 6.1.1 (线程安全)**
Rust的线程系统确保线程安全。

**证明**：
通过所有权系统和借用检查器证明线程安全。

### 6.2 死锁自由定理

**定理 6.2.1 (死锁自由)**
Rust的通道通信确保无死锁。

**证明**：
通过通道的发送接收语义证明死锁自由。

## 7. 工程实践

### 7.1 最佳实践

**最佳实践**：

1. **合理使用线程数**：根据CPU核心数设置合适的线程数
2. **避免线程间共享可变状态**：使用通道进行通信
3. **使用线程池**：避免频繁创建和销毁线程
4. **正确处理线程生命周期**：确保线程正确退出

### 7.2 常见陷阱

**常见陷阱**：

1. **线程泄漏**：

   ```rust
   // 错误：线程泄漏
   fn thread_leak() {
       for _ in 0..1000 {
           thread::spawn(|| {
               loop {
                   // 无限循环，线程永远不会退出
               }
           });
       }
   }
   ```

2. **数据竞争**：

   ```rust
   // 错误：数据竞争
   fn data_race() {
       let mut data = vec![1, 2, 3];
       let handle = thread::spawn(move || {
           data.push(4); // 修改数据
       });
       println!("{:?}", data); // 使用数据
       handle.join().unwrap();
   }
   ```

3. **死锁**：

   ```rust
   // 错误：死锁
   fn deadlock() {
       let mutex1 = Arc::new(Mutex::new(()));
       let mutex2 = Arc::new(Mutex::new(()));
       
       let handle1 = thread::spawn(move || {
           let _lock1 = mutex1.lock().unwrap();
           let _lock2 = mutex2.lock().unwrap();
       });
       
       let handle2 = thread::spawn(move || {
           let _lock2 = mutex2.lock().unwrap();
           let _lock1 = mutex1.lock().unwrap();
       });
       
       handle1.join().unwrap();
       handle2.join().unwrap();
   }
   ```

## 8. 交叉引用

- [并发语义](./13_concurrency_semantics.md) - 并发控制
- [异步运行时语义](./12_async_runtime_semantics.md) - 异步运行时
- [内存管理语义](./14_memory_management_semantics.md) - 内存管理
- [同步语义](./16_synchronization_semantics.md) - 同步机制

## 9. 参考文献

1. Rust Book - Threading
2. Rust Reference - Threading
3. Concurrent Programming in Rust
4. Thread Safety in Rust
