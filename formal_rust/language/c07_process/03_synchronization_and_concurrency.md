# 同步与并发控制

## 概述

在进程间通信中，同步机制是确保数据一致性和避免竞态条件的关键。Rust 提供了丰富的同步原语，包括信号量、互斥锁、条件变量和原子操作。本章深入探讨这些同步机制的设计原理、实现方式以及在进程间通信中的应用。

## 进程间同步原语

### 信号量

信号量是最基础的同步原语，用于控制对共享资源的访问。

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;

struct Semaphore {
    permits: Arc<Mutex<usize>>,
    condvar: Arc<Condvar>,
}

impl Semaphore {
    fn new(permits: usize) -> Self {
        Semaphore {
            permits: Arc::new(Mutex::new(permits)),
            condvar: Arc::new(Condvar::new()),
        }
    }
    
    fn acquire(&self) {
        let mut permits = self.permits.lock().unwrap();
        while *permits == 0 {
            permits = self.condvar.wait(permits).unwrap();
        }
        *permits -= 1;
    }
    
    fn release(&self) {
        let mut permits = self.permits.lock().unwrap();
        *permits += 1;
        self.condvar.notify_one();
    }
}

fn semaphore_example() {
    let semaphore = Arc::new(Semaphore::new(3)); // 最多3个并发访问
    let mut handles = vec![];
    
    for i in 0..10 {
        let sem = semaphore.clone();
        let handle = thread::spawn(move || {
            println!("Thread {} waiting for permit", i);
            sem.acquire();
            println!("Thread {} acquired permit", i);
            
            // 模拟工作
            thread::sleep(std::time::Duration::from_millis(100));
            
            println!("Thread {} releasing permit", i);
            sem.release();
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 读写锁

读写锁允许多个读取者或单个写入者同时访问共享资源。

```rust
use std::sync::RwLock;
use std::thread;

struct SharedResource {
    data: RwLock<String>,
}

impl SharedResource {
    fn new() -> Self {
        SharedResource {
            data: RwLock::new("Initial data".to_string()),
        }
    }
    
    fn read(&self) -> String {
        self.data.read().unwrap().clone()
    }
    
    fn write(&self, new_data: String) {
        *self.data.write().unwrap() = new_data;
    }
}

fn rwlock_example() {
    let resource = Arc::new(SharedResource::new());
    let mut handles = vec![];
    
    // 多个读取者
    for i in 0..5 {
        let resource_clone = resource.clone();
        let handle = thread::spawn(move || {
            for _ in 0..3 {
                let data = resource_clone.read();
                println!("Reader {}: {}", i, data);
                thread::sleep(std::time::Duration::from_millis(50));
            }
        });
        handles.push(handle);
    }
    
    // 写入者
    let writer = thread::spawn(move || {
        for i in 1..=3 {
            let new_data = format!("Updated data {}", i);
            resource.write(new_data);
            println!("Writer updated data");
            thread::sleep(std::time::Duration::from_millis(200));
        }
    });
    handles.push(writer);
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

## 互斥锁与条件变量

### 互斥锁基础

```rust
use std::sync::{Arc, Mutex};
use std::thread;

struct Counter {
    value: Mutex<i32>,
}

impl Counter {
    fn new() -> Self {
        Counter {
            value: Mutex::new(0),
        }
    }
    
    fn increment(&self) {
        let mut value = self.value.lock().unwrap();
        *value += 1;
    }
    
    fn get(&self) -> i32 {
        *self.value.lock().unwrap()
    }
}

fn mutex_example() {
    let counter = Arc::new(Counter::new());
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter_clone = counter.clone();
        let handle = thread::spawn(move || {
            for _ in 0..100 {
                counter_clone.increment();
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Final counter value: {}", counter.get());
}
```

### 条件变量

条件变量用于线程间的协调，允许线程等待特定条件满足。

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;

struct ProducerConsumer {
    buffer: Mutex<Vec<i32>>,
    not_empty: Condvar,
    not_full: Condvar,
    capacity: usize,
}

impl ProducerConsumer {
    fn new(capacity: usize) -> Self {
        ProducerConsumer {
            buffer: Mutex::new(Vec::new()),
            not_empty: Condvar::new(),
            not_full: Condvar::new(),
            capacity,
        }
    }
    
    fn produce(&self, item: i32) {
        let mut buffer = self.buffer.lock().unwrap();
        while buffer.len() >= self.capacity {
            buffer = self.not_full.wait(buffer).unwrap();
        }
        buffer.push(item);
        self.not_empty.notify_one();
    }
    
    fn consume(&self) -> i32 {
        let mut buffer = self.buffer.lock().unwrap();
        while buffer.is_empty() {
            buffer = self.not_empty.wait(buffer).unwrap();
        }
        let item = buffer.remove(0);
        self.not_full.notify_one();
        item
    }
}

fn producer_consumer_example() {
    let pc = Arc::new(ProducerConsumer::new(5));
    let pc_clone = pc.clone();
    
    // 生产者
    let producer = thread::spawn(move || {
        for i in 0..10 {
            pc.produce(i);
            println!("Produced: {}", i);
            thread::sleep(std::time::Duration::from_millis(100));
        }
    });
    
    // 消费者
    let consumer = thread::spawn(move || {
        for _ in 0..10 {
            let item = pc_clone.consume();
            println!("Consumed: {}", item);
            thread::sleep(std::time::Duration::from_millis(150));
        }
    });
    
    producer.join().unwrap();
    consumer.join().unwrap();
}
```

## 原子操作

### 原子类型

原子操作提供了无锁的同步机制，适用于高性能场景。

```rust
use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering};
use std::thread;

struct AtomicCounter {
    value: AtomicUsize,
}

impl AtomicCounter {
    fn new() -> Self {
        AtomicCounter {
            value: AtomicUsize::new(0),
        }
    }
    
    fn increment(&self) {
        self.value.fetch_add(1, Ordering::SeqCst);
    }
    
    fn get(&self) -> usize {
        self.value.load(Ordering::SeqCst)
    }
    
    fn compare_and_swap(&self, expected: usize, new: usize) -> usize {
        self.value.compare_exchange(
            expected,
            new,
            Ordering::SeqCst,
            Ordering::SeqCst,
        ).unwrap_or_else(|x| x)
    }
}

fn atomic_example() {
    let counter = Arc::new(AtomicCounter::new());
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter_clone = counter.clone();
        let handle = thread::spawn(move || {
            for _ in 0..100 {
                counter_clone.increment();
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Final atomic counter value: {}", counter.get());
}
```

### 原子布尔值

```rust
use std::sync::atomic::{AtomicBool, Ordering};

struct Flag {
    flag: AtomicBool,
}

impl Flag {
    fn new() -> Self {
        Flag {
            flag: AtomicBool::new(false),
        }
    }
    
    fn set(&self) {
        self.flag.store(true, Ordering::SeqCst);
    }
    
    fn is_set(&self) -> bool {
        self.flag.load(Ordering::SeqCst)
    }
    
    fn try_set(&self) -> bool {
        self.flag.compare_exchange(
            false,
            true,
            Ordering::SeqCst,
            Ordering::SeqCst,
        ).is_ok()
    }
}

fn atomic_flag_example() {
    let flag = Arc::new(Flag::new());
    let flag_clone = flag.clone();
    
    // 设置线程
    let setter = thread::spawn(move || {
        thread::sleep(std::time::Duration::from_millis(100));
        flag.set();
        println!("Flag set");
    });
    
    // 检查线程
    let checker = thread::spawn(move || {
        while !flag_clone.is_set() {
            thread::sleep(std::time::Duration::from_millis(10));
        }
        println!("Flag detected as set");
    });
    
    setter.join().unwrap();
    checker.join().unwrap();
}
```

## 进程间同步模式

### 屏障同步

屏障确保多个进程在某个点同步。

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;

struct Barrier {
    count: Mutex<usize>,
    generation: Mutex<usize>,
    condvar: Condvar,
    parties: usize,
}

impl Barrier {
    fn new(parties: usize) -> Self {
        Barrier {
            count: Mutex::new(0),
            generation: Mutex::new(0),
            condvar: Condvar::new(),
            parties,
        }
    }
    
    fn wait(&self) {
        let mut count = self.count.lock().unwrap();
        let generation = *self.generation.lock().unwrap();
        
        *count += 1;
        
        if *count < self.parties {
            // 等待其他线程
            while *self.generation.lock().unwrap() == generation {
                count = self.condvar.wait(count).unwrap();
            }
        } else {
            // 最后一个线程，重置屏障
            *count = 0;
            *self.generation.lock().unwrap() += 1;
            self.condvar.notify_all();
        }
    }
}

fn barrier_example() {
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];
    
    for i in 0..3 {
        let barrier_clone = barrier.clone();
        let handle = thread::spawn(move || {
            println!("Thread {} starting", i);
            thread::sleep(std::time::Duration::from_millis(100 * (i + 1) as u64));
            println!("Thread {} waiting at barrier", i);
            barrier_clone.wait();
            println!("Thread {} passed barrier", i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 读写锁的进程间版本

```rust
use std::sync::{Arc, RwLock, Mutex, Condvar};
use std::collections::HashMap;

struct ProcessRwLock {
    readers: Mutex<usize>,
    writers: Mutex<usize>,
    waiting_writers: Mutex<usize>,
    condvar: Condvar,
}

impl ProcessRwLock {
    fn new() -> Self {
        ProcessRwLock {
            readers: Mutex::new(0),
            writers: Mutex::new(0),
            waiting_writers: Mutex::new(0),
            condvar: Condvar::new(),
        }
    }
    
    fn read_lock(&self) {
        let mut readers = self.readers.lock().unwrap();
        let waiting_writers = *self.waiting_writers.lock().unwrap();
        
        while *self.writers.lock().unwrap() > 0 || waiting_writers > 0 {
            readers = self.condvar.wait(readers).unwrap();
        }
        
        *readers += 1;
    }
    
    fn read_unlock(&self) {
        let mut readers = self.readers.lock().unwrap();
        *readers -= 1;
        
        if *readers == 0 {
            self.condvar.notify_all();
        }
    }
    
    fn write_lock(&self) {
        let mut waiting_writers = self.waiting_writers.lock().unwrap();
        *waiting_writers += 1;
        drop(waiting_writers);
        
        let mut writers = self.writers.lock().unwrap();
        let mut readers = self.readers.lock().unwrap();
        
        while *writers > 0 || *readers > 0 {
            writers = self.condvar.wait(writers).unwrap();
            readers = self.readers.lock().unwrap();
        }
        
        *writers += 1;
        
        let mut waiting_writers = self.waiting_writers.lock().unwrap();
        *waiting_writers -= 1;
    }
    
    fn write_unlock(&self) {
        let mut writers = self.writers.lock().unwrap();
        *writers -= 1;
        self.condvar.notify_all();
    }
}
```

## 死锁预防

### 资源分配图

```rust
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

struct ResourceAllocationGraph {
    processes: HashMap<String, HashSet<String>>, // 进程 -> 资源
    resources: HashMap<String, HashSet<String>>, // 资源 -> 进程
}

impl ResourceAllocationGraph {
    fn new() -> Self {
        ResourceAllocationGraph {
            processes: HashMap::new(),
            resources: HashMap::new(),
        }
    }
    
    fn request_resource(&mut self, process: &str, resource: &str) -> bool {
        // 检查是否会导致死锁
        if self.would_cause_deadlock(process, resource) {
            return false;
        }
        
        // 分配资源
        self.processes.entry(process.to_string())
            .or_insert_with(HashSet::new)
            .insert(resource.to_string());
        
        self.resources.entry(resource.to_string())
            .or_insert_with(HashSet::new)
            .insert(process.to_string());
        
        true
    }
    
    fn release_resource(&mut self, process: &str, resource: &str) {
        if let Some(process_resources) = self.processes.get_mut(process) {
            process_resources.remove(resource);
        }
        
        if let Some(resource_processes) = self.resources.get_mut(resource) {
            resource_processes.remove(process);
        }
    }
    
    fn would_cause_deadlock(&self, process: &str, resource: &str) -> bool {
        // 简化的死锁检测算法
        // 在实际应用中，这里应该实现完整的死锁检测算法
        false
    }
}
```

### 银行家算法

```rust
struct BankerAlgorithm {
    available: Vec<i32>,
    maximum: Vec<Vec<i32>>,
    allocation: Vec<Vec<i32>>,
    need: Vec<Vec<i32>>,
}

impl BankerAlgorithm {
    fn new(available: Vec<i32>, maximum: Vec<Vec<i32>>) -> Self {
        let allocation = vec![vec![0; available.len()]; maximum.len()];
        let need = maximum.clone();
        
        BankerAlgorithm {
            available,
            maximum,
            allocation,
            need,
        }
    }
    
    fn request_resources(&mut self, process_id: usize, request: Vec<i32>) -> bool {
        // 检查请求是否超过需求
        for i in 0..request.len() {
            if request[i] > self.need[process_id][i] {
                return false;
            }
        }
        
        // 检查是否有足够的可用资源
        for i in 0..request.len() {
            if request[i] > self.available[i] {
                return false;
            }
        }
        
        // 尝试分配资源
        for i in 0..request.len() {
            self.available[i] -= request[i];
            self.allocation[process_id][i] += request[i];
            self.need[process_id][i] -= request[i];
        }
        
        // 检查安全性
        if self.is_safe() {
            true
        } else {
            // 回滚分配
            for i in 0..request.len() {
                self.available[i] += request[i];
                self.allocation[process_id][i] -= request[i];
                self.need[process_id][i] += request[i];
            }
            false
        }
    }
    
    fn is_safe(&self) -> bool {
        let mut work = self.available.clone();
        let mut finish = vec![false; self.maximum.len()];
        
        loop {
            let mut found = false;
            for i in 0..self.maximum.len() {
                if !finish[i] && self.can_allocate(i, &work) {
                    for j in 0..work.len() {
                        work[j] += self.allocation[i][j];
                    }
                    finish[i] = true;
                    found = true;
                }
            }
            
            if !found {
                break;
            }
        }
        
        finish.iter().all(|&x| x)
    }
    
    fn can_allocate(&self, process_id: usize, work: &[i32]) -> bool {
        for i in 0..work.len() {
            if self.need[process_id][i] > work[i] {
                return false;
            }
        }
        true
    }
}
```

## 性能优化

### 无锁数据结构

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
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
                (*new_node).next.store(head, Ordering::Release);
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
            
            unsafe {
                let next = (*head).next.load(Ordering::Release);
                if self.head.compare_exchange_weak(
                    head,
                    next,
                    Ordering::Release,
                    Ordering::Relaxed,
                ).is_ok() {
                    let data = ptr::read(&(*head).data);
                    drop(Box::from_raw(head));
                    return Some(data);
                }
            }
        }
    }
}
```

## 总结

Rust 的同步机制通过类型安全的抽象提供了强大的进程间协调能力。从基础的互斥锁到高级的无锁数据结构，Rust 确保了同步操作的安全性和效率。

### 关键要点

1. **类型安全** - 所有同步原语都通过类型系统保证安全性
2. **性能优化** - 原子操作和无锁数据结构提供高性能同步
3. **死锁预防** - 通过算法和设计模式预防死锁
4. **错误处理** - 全面的错误处理机制确保系统稳定性

### 下一步

在下一章中，我们将探讨形式化模型与类型系统，包括进程状态的形式化表示、通信协议的类型安全和资源管理的形式化验证。
