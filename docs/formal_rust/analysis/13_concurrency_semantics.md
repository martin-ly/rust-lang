# 并发语义分析

## 目录

- [并发语义分析](#并发语义分析)
  - [目录](#目录)
  - [概述](#概述)
  - [1. 并发理论基础](#1-并发理论基础)
    - [1.1 并发概念](#11-并发概念)
    - [1.2 并发模型](#12-并发模型)
  - [2. 同步原语](#2-同步原语)
    - [2.1 互斥锁](#21-互斥锁)
    - [2.2 读写锁](#22-读写锁)
    - [2.3 条件变量](#23-条件变量)
  - [3. 原子操作](#3-原子操作)
    - [3.1 原子类型](#31-原子类型)
    - [3.2 内存序](#32-内存序)
  - [4. 死锁检测](#4-死锁检测)
    - [4.1 死锁检测算法](#41-死锁检测算法)
    - [4.2 死锁预防](#42-死锁预防)
  - [5. 形式化证明](#5-形式化证明)
    - [5.1 互斥定理](#51-互斥定理)
    - [5.2 死锁自由定理](#52-死锁自由定理)
  - [6. 工程实践](#6-工程实践)
    - [6.1 最佳实践](#61-最佳实践)
    - [6.2 常见陷阱](#62-常见陷阱)
  - [7. 交叉引用](#7-交叉引用)
  - [8. 参考文献](#8-参考文献)

## 概述

本文档详细分析Rust中并发控制的语义，包括其理论基础、实现机制和形式化定义。

## 1. 并发理论基础

### 1.1 并发概念

**定义 1.1.1 (并发)**
并发是指多个计算任务在时间上重叠执行的能力。

**并发系统的核心特性**：

1. **并行性**：多个任务同时执行
2. **互斥性**：对共享资源的互斥访问
3. **同步性**：任务间的协调和通信
4. **原子性**：操作的不可分割性

### 1.2 并发模型

**并发模型分类**：

1. **共享内存模型**：线程间通过共享内存通信
2. **消息传递模型**：线程间通过消息传递通信
3. **Actor模型**：基于消息传递的并发模型
4. **CSP模型**：通信顺序进程模型

## 2. 同步原语

### 2.1 互斥锁

**互斥锁实现**：

```rust
// 互斥锁
pub struct Mutex<T> {
    inner: std::sync::Mutex<T>,
}

impl<T> Mutex<T> {
    pub fn new(value: T) -> Self {
        Self {
            inner: std::sync::Mutex::new(value),
        }
    }
    
    pub fn lock(&self) -> Result<MutexGuard<T>, PoisonError<T>> {
        self.inner.lock().map(MutexGuard::new)
    }
    
    pub fn try_lock(&self) -> Result<MutexGuard<T>, TryLockError<T>> {
        self.inner.try_lock().map(MutexGuard::new)
    }
}

// 互斥锁守卫
pub struct MutexGuard<'a, T> {
    guard: std::sync::MutexGuard<'a, T>,
}

impl<'a, T> MutexGuard<'a, T> {
    fn new(guard: std::sync::MutexGuard<'a, T>) -> Self {
        Self { guard }
    }
}

impl<'a, T> Deref for MutexGuard<'a, T> {
    type Target = T;
    
    fn deref(&self) -> &Self::Target {
        &*self.guard
    }
}

impl<'a, T> DerefMut for MutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.guard
    }
}

// 使用示例
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
    
    println!("Final count: {}", *counter.lock().unwrap());
}
```

### 2.2 读写锁

**读写锁实现**：

```rust
// 读写锁
pub struct RwLock<T> {
    inner: std::sync::RwLock<T>,
}

impl<T> RwLock<T> {
    pub fn new(value: T) -> Self {
        Self {
            inner: std::sync::RwLock::new(value),
        }
    }
    
    pub fn read(&self) -> Result<RwLockReadGuard<T>, PoisonError<T>> {
        self.inner.read().map(RwLockReadGuard::new)
    }
    
    pub fn write(&self) -> Result<RwLockWriteGuard<T>, PoisonError<T>> {
        self.inner.write().map(RwLockWriteGuard::new)
    }
    
    pub fn try_read(&self) -> Result<RwLockReadGuard<T>, TryLockError<T>> {
        self.inner.try_read().map(RwLockReadGuard::new)
    }
    
    pub fn try_write(&self) -> Result<RwLockWriteGuard<T>, TryLockError<T>> {
        self.inner.try_write().map(RwLockWriteGuard::new)
    }
}

// 读锁守卫
pub struct RwLockReadGuard<'a, T> {
    guard: std::sync::RwLockReadGuard<'a, T>,
}

impl<'a, T> RwLockReadGuard<'a, T> {
    fn new(guard: std::sync::RwLockReadGuard<'a, T>) -> Self {
        Self { guard }
    }
}

impl<'a, T> Deref for RwLockReadGuard<'a, T> {
    type Target = T;
    
    fn deref(&self) -> &Self::Target {
        &*self.guard
    }
}

// 写锁守卫
pub struct RwLockWriteGuard<'a, T> {
    guard: std::sync::RwLockWriteGuard<'a, T>,
}

impl<'a, T> RwLockWriteGuard<'a, T> {
    fn new(guard: std::sync::RwLockWriteGuard<'a, T>) -> Self {
        Self { guard }
    }
}

impl<'a, T> Deref for RwLockWriteGuard<'a, T> {
    type Target = T;
    
    fn deref(&self) -> &Self::Target {
        &*self.guard
    }
}

impl<'a, T> DerefMut for RwLockWriteGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.guard
    }
}

// 使用示例
fn rwlock_example() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3, 4, 5]));
    let mut handles = vec![];
    
    // 读取线程
    for i in 0..3 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let values = data.read().unwrap();
            println!("Reader {}: {:?}", i, *values);
        });
        handles.push(handle);
    }
    
    // 写入线程
    let data = Arc::clone(&data);
    let handle = thread::spawn(move || {
        let mut values = data.write().unwrap();
        values.push(6);
        println!("Writer: {:?}", *values);
    });
    handles.push(handle);
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 2.3 条件变量

**条件变量实现**：

```rust
// 条件变量
pub struct Condvar {
    inner: std::sync::Condvar,
}

impl Condvar {
    pub fn new() -> Self {
        Self {
            inner: std::sync::Condvar::new(),
        }
    }
    
    pub fn wait<T>(&self, guard: MutexGuard<T>) -> Result<MutexGuard<T>, PoisonError<T>> {
        self.inner.wait(guard.into_inner()).map(MutexGuard::new)
    }
    
    pub fn wait_timeout<T>(
        &self,
        guard: MutexGuard<T>,
        timeout: Duration,
    ) -> Result<(MutexGuard<T>, bool), PoisonError<T>> {
        let (guard, timed_out) = self.inner.wait_timeout(guard.into_inner(), timeout);
        Ok((MutexGuard::new(guard), timed_out.timed_out()))
    }
    
    pub fn notify_one(&self) {
        self.inner.notify_one();
    }
    
    pub fn notify_all(&self) {
        self.inner.notify_all();
    }
}

// 生产者-消费者示例
struct ProducerConsumer {
    buffer: Mutex<Vec<i32>>,
    not_empty: Condvar,
    not_full: Condvar,
    capacity: usize,
}

impl ProducerConsumer {
    pub fn new(capacity: usize) -> Self {
        Self {
            buffer: Mutex::new(Vec::new()),
            not_empty: Condvar::new(),
            not_full: Condvar::new(),
            capacity,
        }
    }
    
    pub fn produce(&self, value: i32) {
        let mut buffer = self.buffer.lock().unwrap();
        
        while buffer.len() >= self.capacity {
            buffer = self.not_full.wait(buffer).unwrap();
        }
        
        buffer.push(value);
        self.not_empty.notify_one();
    }
    
    pub fn consume(&self) -> i32 {
        let mut buffer = self.buffer.lock().unwrap();
        
        while buffer.is_empty() {
            buffer = self.not_empty.wait(buffer).unwrap();
        }
        
        let value = buffer.remove(0);
        self.not_full.notify_one();
        value
    }
}

// 使用示例
fn producer_consumer_example() {
    let pc = Arc::new(ProducerConsumer::new(5));
    let mut handles = vec![];
    
    // 生产者
    for i in 0..3 {
        let pc = Arc::clone(&pc);
        let handle = thread::spawn(move || {
            for j in 0..10 {
                pc.produce(i * 10 + j);
                thread::sleep(Duration::from_millis(100));
            }
        });
        handles.push(handle);
    }
    
    // 消费者
    for i in 0..2 {
        let pc = Arc::clone(&pc);
        let handle = thread::spawn(move || {
            for _ in 0..15 {
                let value = pc.consume();
                println!("Consumer {}: {}", i, value);
                thread::sleep(Duration::from_millis(200));
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

## 3. 原子操作

### 3.1 原子类型

**原子类型实现**：

```rust
// 原子整数
pub struct AtomicI32 {
    inner: std::sync::atomic::AtomicI32,
}

impl AtomicI32 {
    pub fn new(value: i32) -> Self {
        Self {
            inner: std::sync::atomic::AtomicI32::new(value),
        }
    }
    
    pub fn load(&self, order: Ordering) -> i32 {
        self.inner.load(order)
    }
    
    pub fn store(&self, value: i32, order: Ordering) {
        self.inner.store(value, order);
    }
    
    pub fn fetch_add(&self, value: i32, order: Ordering) -> i32 {
        self.inner.fetch_add(value, order)
    }
    
    pub fn fetch_sub(&self, value: i32, order: Ordering) -> i32 {
        self.inner.fetch_sub(value, order)
    }
    
    pub fn compare_exchange(
        &self,
        current: i32,
        new: i32,
        success: Ordering,
        failure: Ordering,
    ) -> Result<i32, i32> {
        self.inner.compare_exchange(current, new, success, failure)
    }
    
    pub fn compare_exchange_weak(
        &self,
        current: i32,
        new: i32,
        success: Ordering,
        failure: Ordering,
    ) -> Result<i32, i32> {
        self.inner.compare_exchange_weak(current, new, success, failure)
    }
}

// 原子布尔值
pub struct AtomicBool {
    inner: std::sync::atomic::AtomicBool,
}

impl AtomicBool {
    pub fn new(value: bool) -> Self {
        Self {
            inner: std::sync::atomic::AtomicBool::new(value),
        }
    }
    
    pub fn load(&self, order: Ordering) -> bool {
        self.inner.load(order)
    }
    
    pub fn store(&self, value: bool, order: Ordering) {
        self.inner.store(value, order);
    }
    
    pub fn compare_exchange(
        &self,
        current: bool,
        new: bool,
        success: Ordering,
        failure: Ordering,
    ) -> Result<bool, bool> {
        self.inner.compare_exchange(current, new, success, failure)
    }
}

// 原子指针
pub struct AtomicPtr<T> {
    inner: std::sync::atomic::AtomicPtr<T>,
}

impl<T> AtomicPtr<T> {
    pub fn new(ptr: *mut T) -> Self {
        Self {
            inner: std::sync::atomic::AtomicPtr::new(ptr),
        }
    }
    
    pub fn load(&self, order: Ordering) -> *mut T {
        self.inner.load(order)
    }
    
    pub fn store(&self, ptr: *mut T, order: Ordering) {
        self.inner.store(ptr, order);
    }
    
    pub fn compare_exchange(
        &self,
        current: *mut T,
        new: *mut T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<*mut T, *mut T> {
        self.inner.compare_exchange(current, new, success, failure)
    }
}

// 使用示例
fn atomic_example() {
    let counter = Arc::new(AtomicI32::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
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
    
    println!("Final count: {}", counter.load(Ordering::Relaxed));
}
```

### 3.2 内存序

**内存序类型**：

```rust
// 内存序
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ordering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
}

// 内存序语义
impl Ordering {
    pub fn is_relaxed(&self) -> bool {
        matches!(self, Ordering::Relaxed)
    }
    
    pub fn is_acquire(&self) -> bool {
        matches!(self, Ordering::Acquire | Ordering::AcqRel | Ordering::SeqCst)
    }
    
    pub fn is_release(&self) -> bool {
        matches!(self, Ordering::Release | Ordering::AcqRel | Ordering::SeqCst)
    }
    
    pub fn is_seq_cst(&self) -> bool {
        matches!(self, Ordering::SeqCst)
    }
}

// 内存序示例
fn memory_ordering_example() {
    let flag = Arc::new(AtomicBool::new(false));
    let data = Arc::new(AtomicI32::new(0));
    
    // 线程1：设置数据，然后设置标志
    let flag1 = Arc::clone(&flag);
    let data1 = Arc::clone(&data);
    let handle1 = thread::spawn(move || {
        data1.store(42, Ordering::Relaxed);
        flag1.store(true, Ordering::Release);
    });
    
    // 线程2：检查标志，然后读取数据
    let flag2 = Arc::clone(&flag);
    let data2 = Arc::clone(&data);
    let handle2 = thread::spawn(move || {
        while !flag2.load(Ordering::Acquire) {
            thread::yield_now();
        }
        let value = data2.load(Ordering::Relaxed);
        println!("Data: {}", value);
    });
    
    handle1.join().unwrap();
    handle2.join().unwrap();
}
```

## 4. 死锁检测

### 4.1 死锁检测算法

**死锁检测实现**：

```rust
// 资源分配图
pub struct ResourceAllocationGraph {
    processes: HashMap<ProcessId, Process>,
    resources: HashMap<ResourceId, Resource>,
    allocations: HashMap<ProcessId, Vec<ResourceId>>,
    requests: HashMap<ProcessId, Vec<ResourceId>>,
}

// 进程ID
pub type ProcessId = usize;

// 资源ID
pub type ResourceId = usize;

// 进程
pub struct Process {
    id: ProcessId,
    state: ProcessState,
}

// 进程状态
pub enum ProcessState {
    Running,
    Waiting,
    Blocked,
}

// 资源
pub struct Resource {
    id: ResourceId,
    total_units: usize,
    available_units: usize,
}

impl ResourceAllocationGraph {
    pub fn new() -> Self {
        Self {
            processes: HashMap::new(),
            resources: HashMap::new(),
            allocations: HashMap::new(),
            requests: HashMap::new(),
        }
    }
    
    pub fn add_process(&mut self, process_id: ProcessId) {
        self.processes.insert(process_id, Process {
            id: process_id,
            state: ProcessState::Running,
        });
        self.allocations.insert(process_id, Vec::new());
        self.requests.insert(process_id, Vec::new());
    }
    
    pub fn add_resource(&mut self, resource_id: ResourceId, total_units: usize) {
        self.resources.insert(resource_id, Resource {
            id: resource_id,
            total_units,
            available_units: total_units,
        });
    }
    
    pub fn request_resource(&mut self, process_id: ProcessId, resource_id: ResourceId) -> bool {
        if let Some(resource) = self.resources.get_mut(&resource_id) {
            if resource.available_units > 0 {
                resource.available_units -= 1;
                self.allocations.get_mut(&process_id).unwrap().push(resource_id);
                return true;
            } else {
                self.requests.get_mut(&process_id).unwrap().push(resource_id);
                if let Some(process) = self.processes.get_mut(&process_id) {
                    process.state = ProcessState::Waiting;
                }
                return false;
            }
        }
        false
    }
    
    pub fn release_resource(&mut self, process_id: ProcessId, resource_id: ResourceId) {
        if let Some(allocations) = self.allocations.get_mut(&process_id) {
            allocations.retain(|&id| id != resource_id);
        }
        
        if let Some(resource) = self.resources.get_mut(&resource_id) {
            resource.available_units += 1;
        }
        
        // 检查是否有等待该资源的进程
        for (pid, requests) in &self.requests {
            if requests.contains(&resource_id) {
                if self.request_resource(*pid, resource_id) {
                    self.requests.get_mut(pid).unwrap().retain(|&id| id != resource_id);
                    if let Some(process) = self.processes.get_mut(pid) {
                        process.state = ProcessState::Running;
                    }
                }
            }
        }
    }
    
    pub fn detect_deadlock(&self) -> Option<Vec<ProcessId>> {
        let mut visited = HashSet::new();
        let mut recursion_stack = HashSet::new();
        let mut cycle = Vec::new();
        
        for process_id in self.processes.keys() {
            if !visited.contains(process_id) {
                if self.dfs_deadlock_detection(
                    *process_id,
                    &mut visited,
                    &mut recursion_stack,
                    &mut cycle,
                ) {
                    return Some(cycle);
                }
            }
        }
        
        None
    }
    
    fn dfs_deadlock_detection(
        &self,
        process_id: ProcessId,
        visited: &mut HashSet<ProcessId>,
        recursion_stack: &mut HashSet<ProcessId>,
        cycle: &mut Vec<ProcessId>,
    ) -> bool {
        visited.insert(process_id);
        recursion_stack.insert(process_id);
        cycle.push(process_id);
        
        // 检查该进程请求的资源
        if let Some(requests) = self.requests.get(&process_id) {
            for &resource_id in requests {
                // 找到持有该资源的进程
                for (pid, allocations) in &self.allocations {
                    if allocations.contains(&resource_id) {
                        if !visited.contains(pid) {
                            if self.dfs_deadlock_detection(*pid, visited, recursion_stack, cycle) {
                                return true;
                            }
                        } else if recursion_stack.contains(pid) {
                            // 找到循环
                            return true;
                        }
                    }
                }
            }
        }
        
        recursion_stack.remove(&process_id);
        cycle.pop();
        false
    }
}

// 使用示例
fn deadlock_detection_example() {
    let mut rag = ResourceAllocationGraph::new();
    
    // 添加进程和资源
    rag.add_process(1);
    rag.add_process(2);
    rag.add_resource(1, 1);
    rag.add_resource(2, 1);
    
    // 模拟死锁情况
    rag.request_resource(1, 1); // P1 持有 R1
    rag.request_resource(2, 2); // P2 持有 R2
    rag.request_resource(1, 2); // P1 请求 R2 (阻塞)
    rag.request_resource(2, 1); // P2 请求 R1 (阻塞)
    
    // 检测死锁
    if let Some(cycle) = rag.detect_deadlock() {
        println!("Deadlock detected! Cycle: {:?}", cycle);
    } else {
        println!("No deadlock detected");
    }
}
```

### 4.2 死锁预防

**死锁预防策略**：

```rust
// 死锁预防器
pub struct DeadlockPreventor {
    resource_allocation_policy: ResourceAllocationPolicy,
    timeout_policy: TimeoutPolicy,
}

// 资源分配策略
pub enum ResourceAllocationPolicy {
    // 一次性分配所有资源
    AllOrNothing,
    // 按顺序分配资源
    OrderedAllocation,
    // 银行家算法
    BankersAlgorithm,
}

// 超时策略
pub struct TimeoutPolicy {
    max_wait_time: Duration,
    retry_count: usize,
}

impl DeadlockPreventor {
    pub fn new(policy: ResourceAllocationPolicy, timeout: Duration, retries: usize) -> Self {
        Self {
            resource_allocation_policy: policy,
            timeout_policy: TimeoutPolicy {
                max_wait_time: timeout,
                retry_count: retries,
            },
        }
    }
    
    pub fn can_allocate_safely(
        &self,
        process_id: ProcessId,
        resources: &[ResourceId],
        rag: &ResourceAllocationGraph,
    ) -> bool {
        match &self.resource_allocation_policy {
            ResourceAllocationPolicy::AllOrNothing => {
                self.all_or_nothing_check(process_id, resources, rag)
            }
            ResourceAllocationPolicy::OrderedAllocation => {
                self.ordered_allocation_check(process_id, resources, rag)
            }
            ResourceAllocationPolicy::BankersAlgorithm => {
                self.bankers_algorithm_check(process_id, resources, rag)
            }
        }
    }
    
    fn all_or_nothing_check(
        &self,
        _process_id: ProcessId,
        resources: &[ResourceId],
        rag: &ResourceAllocationGraph,
    ) -> bool {
        // 检查是否所有资源都可用
        for &resource_id in resources {
            if let Some(resource) = rag.resources.get(&resource_id) {
                if resource.available_units == 0 {
                    return false;
                }
            }
        }
        true
    }
    
    fn ordered_allocation_check(
        &self,
        _process_id: ProcessId,
        resources: &[ResourceId],
        _rag: &ResourceAllocationGraph,
    ) -> bool {
        // 检查资源是否按顺序请求
        for i in 1..resources.len() {
            if resources[i] <= resources[i - 1] {
                return false;
            }
        }
        true
    }
    
    fn bankers_algorithm_check(
        &self,
        process_id: ProcessId,
        resources: &[ResourceId],
        rag: &ResourceAllocationGraph,
    ) -> bool {
        // 简化的银行家算法实现
        // 检查分配后系统是否处于安全状态
        let mut available = HashMap::new();
        let mut allocation = HashMap::new();
        let mut need = HashMap::new();
        
        // 初始化可用资源
        for (resource_id, resource) in &rag.resources {
            available.insert(*resource_id, resource.available_units);
        }
        
        // 初始化分配矩阵
        for (pid, allocations) in &rag.allocations {
            allocation.insert(*pid, allocations.clone());
        }
        
        // 初始化需求矩阵
        for (pid, requests) in &rag.requests {
            need.insert(*pid, requests.clone());
        }
        
        // 模拟分配
        for &resource_id in resources {
            if let Some(available_units) = available.get_mut(&resource_id) {
                if *available_units > 0 {
                    *available_units -= 1;
                    allocation.get_mut(&process_id).unwrap().push(resource_id);
                } else {
                    return false;
                }
            }
        }
        
        // 检查安全状态
        self.is_safe_state(&available, &allocation, &need)
    }
    
    fn is_safe_state(
        &self,
        available: &HashMap<ResourceId, usize>,
        allocation: &HashMap<ProcessId, Vec<ResourceId>>,
        need: &HashMap<ProcessId, Vec<ResourceId>>,
    ) -> bool {
        let mut work = available.clone();
        let mut finish = HashSet::new();
        
        loop {
            let mut found = false;
            
            for (process_id, need_resources) in need {
                if !finish.contains(process_id) {
                    let mut can_allocate = true;
                    
                    for &resource_id in need_resources {
                        if work.get(&resource_id).unwrap_or(&0) < &1 {
                            can_allocate = false;
                            break;
                        }
                    }
                    
                    if can_allocate {
                        // 分配资源给进程
                        for &resource_id in need_resources {
                            *work.get_mut(&resource_id).unwrap() -= 1;
                        }
                        
                        // 进程完成后释放资源
                        if let Some(allocated) = allocation.get(process_id) {
                            for &resource_id in allocated {
                                *work.get_mut(&resource_id).unwrap() += 1;
                            }
                        }
                        
                        finish.insert(*process_id);
                        found = true;
                    }
                }
            }
            
            if !found {
                break;
            }
        }
        
        finish.len() == need.len()
    }
}
```

## 5. 形式化证明

### 5.1 互斥定理

**定理 5.1.1 (互斥性)**
互斥锁确保同一时间只有一个线程能访问共享资源。

**证明**：
通过互斥锁的状态机模型证明互斥性。

### 5.2 死锁自由定理

**定理 5.2.1 (死锁自由)**
银行家算法确保系统不会进入死锁状态。

**证明**：
通过安全状态的定义和银行家算法的正确性证明死锁自由。

## 6. 工程实践

### 6.1 最佳实践

**最佳实践**：

1. **避免嵌套锁**：避免在持有锁时获取其他锁
2. **固定锁顺序**：按固定顺序获取多个锁
3. **使用原子操作**：对于简单操作使用原子操作
4. **超时机制**：为锁操作设置超时

### 6.2 常见陷阱

**常见陷阱**：

1. **死锁**：

   ```rust
   // 错误：死锁
   let mutex1 = Mutex::new(());
   let mutex2 = Mutex::new(());
   
   let handle1 = thread::spawn(move || {
       let _lock1 = mutex1.lock().unwrap();
       let _lock2 = mutex2.lock().unwrap();
   });
   
   let handle2 = thread::spawn(move || {
       let _lock2 = mutex2.lock().unwrap();
       let _lock1 = mutex1.lock().unwrap();
   });
   ```

2. **活锁**：

   ```rust
   // 错误：活锁
   let mutex = Mutex::new(());
   let handle1 = thread::spawn(move || {
       loop {
           if let Ok(_lock) = mutex.try_lock() {
               break;
           }
           thread::yield_now();
       }
   });
   ```

3. **饥饿**：

   ```rust
   // 错误：饥饿
   let mutex = Mutex::new(());
   let handle1 = thread::spawn(move || {
       loop {
           let _lock = mutex.lock().unwrap();
           // 长时间持有锁
           thread::sleep(Duration::from_secs(1));
       }
   });
   ```

## 7. 交叉引用

- [异步运行时语义](./12_async_runtime_semantics.md) - 异步运行时
- [内存管理语义](./14_memory_management_semantics.md) - 内存管理
- [线程语义](./15_thread_semantics.md) - 线程系统
- [同步语义](./16_synchronization_semantics.md) - 同步机制

## 8. 参考文献

1. Rust Concurrency Book
2. Operating System Concepts
3. Concurrent Programming in Rust
4. Deadlock Detection and Prevention
