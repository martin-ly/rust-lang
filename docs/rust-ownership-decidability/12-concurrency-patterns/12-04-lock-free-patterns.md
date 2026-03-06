# Rust 无锁编程模式

> **Rust版本**: 1.94
> **覆盖范围**: CAS操作、原子内存序、无锁数据结构、内存回收
> **权威参考**: Rust Atomics and Locks by Mara Bos, C++ Concurrency in Action

---

## 目录

- [Rust 无锁编程模式](#rust-无锁编程模式)
  - [目录](#目录)
  - [1. 内存模型基础](#1-内存模型基础)
    - [1.1 Happens-Before 关系](#11-happens-before-关系)
    - [1.2 Sequentially Consistent](#12-sequentially-consistent)
    - [1.3 内存序详解](#13-内存序详解)
  - [2. 原子操作](#2-原子操作)
    - [2.1 原子类型](#21-原子类型)
    - [2.2 加载与存储](#22-加载与存储)
    - [2.3 读-修改-写操作](#23-读-修改-写操作)
    - [2.4 比较并交换 CAS](#24-比较并交换-cas)
  - [3. CAS 循环模式](#3-cas-循环模式)
    - [3.1 基本 CAS 循环](#31-基本-cas-循环)
    - [3.2 ABA 问题与解决](#32-aba-问题与解决)
    - [3.3 帮助机制](#33-帮助机制)
  - [4. 无锁延迟初始化 (Rust 1.94)](#4-无锁延迟初始化-rust-194)
    - [LazyLock 的无锁语义](#lazylock-的无锁语义)
    - [LazyLock 与无锁数据结构组合](#lazylock-与无锁数据结构组合)
  - [4. 无锁数据结构](#4-无锁数据结构)
    - [4.1 无锁栈](#41-无锁栈)
    - [4.2 无锁队列](#42-无锁队列)

---

## 1. 内存模型基础

### 1.1 Happens-Before 关系

Happens-before 关系是并发程序分析的基础概念：

```text
定义: 如果操作 A happens-before 操作 B，则 A 的效果对 B 可见。

传递性: A →hb B ∧ B →hb C ⇒ A →hb C

程序序: 同一线程中的操作按程序顺序 happens-before
```

**Rust 中的 Happens-Before**:

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;

fn happens_before_example() {
    let data = AtomicUsize::new(0);
    let ready = AtomicUsize::new(0);

    thread::scope(|s| {
        // 写线程
        s.spawn(|| {
            data.store(42, Ordering::Relaxed);
            // Release 操作 happens-before 后续的 Acquire
            ready.store(1, Ordering::Release);
        });

        // 读线程
        s.spawn(|| {
            // Acquire 操作看到 Release 之前的所有写入
            while ready.load(Ordering::Acquire) == 0 {
                thread::yield_now();
            }
            // 保证看到 data = 42
            assert_eq!(data.load(Ordering::Relaxed), 42);
        });
    });
}
```

### 1.2 Sequentially Consistent

```rust
/// 顺序一致性是最强的内存序
/// 所有线程以相同的顺序看到所有操作
fn sequential_consistency_example() {
    use std::sync::atomic::{AtomicBool, Ordering};

    let x = AtomicBool::new(false);
    let y = AtomicBool::new(false);

    thread::scope(|s| {
        s.spawn(|| {
            x.store(true, Ordering::SeqCst);
            if !y.load(Ordering::SeqCst) {
                println!("Thread 1 first");
            }
        });

        s.spawn(|| {
            y.store(true, Ordering::SeqCst);
            if !x.load(Ordering::SeqCst) {
                println!("Thread 2 first");
            }
        });
    });

    // 顺序一致性保证：不可能同时打印两个消息
}
```

### 1.3 内存序详解

```rust
use std::sync::atomic::Ordering;

/// ## Ordering::Relaxed
/// 无同步或排序约束，仅原子性保证
/// 适用场景：简单计数器，不需要与其他操作同步

fn relaxed_example() {
    let counter = std::sync::atomic::AtomicUsize::new(0);
    counter.fetch_add(1, Ordering::Relaxed);
}

/// ## Ordering::Acquire
/// 在此加载操作之后的所有读/写操作不能被重排序到此操作之前
/// 形成 acquire-release 对的消费者端

fn acquire_example() {
    let flag = std::sync::atomic::AtomicBool::new(false);
    let data = 42;

    // 生产者
    thread::spawn(move || {
        // ... 写入数据
        flag.store(true, Ordering::Release);
    });

    // 消费者
    while !flag.load(Ordering::Acquire) {
        thread::yield_now();
    }
    // 保证看到所有 Release 之前的写入
}

/// ## Ordering::Release
/// 在此存储操作之前的所有读/写操作不能被重排序到此操作之后
/// 形成 acquire-release 对的生产者端

fn release_example() {
    let ptr = std::sync::atomic::AtomicPtr::new(std::ptr::null_mut());
    let data = Box::into_raw(Box::new(42));

    // Release 保证：data 的初始化对此操作的 Acquire 可见
    ptr.store(data, Ordering::Release);
}

/// ## Ordering::AcqRel
/// 读用 Acquire，写用 Release
/// 适用场景：read-modify-write 操作

fn acq_rel_example() {
    let lock = std::sync::atomic::AtomicBool::new(false);

    // CAS 操作同时需要看到之前的状态（Acquire）
    // 并保证后续操作看到当前修改（Release）
    lock.compare_exchange(
        false, true,
        Ordering::AcqRel,
        Ordering::Acquire
    ).unwrap();
}

/// ## Ordering::SeqCst
/// 顺序一致性：所有线程以相同顺序看到所有 SeqCst 操作
/// 性能成本最高，通常仅在需要全局顺序时使用

fn seq_cst_example() {
    let a = std::sync::atomic::AtomicUsize::new(0);
    let b = std::sync::atomic::AtomicUsize::new(0);

    thread::scope(|s| {
        s.spawn(|| {
            a.store(1, Ordering::SeqCst);
            let _ = b.load(Ordering::SeqCst);
        });

        s.spawn(|| {
            b.store(1, Ordering::SeqCst);
            let _ = a.load(Ordering::SeqCst);
        });
    });

    // SeqCst 保证：两个线程不可能都先看到对方的存储
}
```

---

## 2. 原子操作

### 2.1 原子类型

```rust
use std::sync::atomic::{
    AtomicUsize, AtomicU64, AtomicU32, AtomicU16, AtomicU8,
    AtomicIsize, AtomicI64, AtomicI32, AtomicI16, AtomicI8,
    AtomicBool, AtomicPtr
};

/// 原子类型概述
pub fn atomic_types_overview() {
    // 整数类型
    let _ = AtomicUsize::new(0); // 指针大小的无符号整数
    let _ = AtomicU64::new(0);   // 64位无符号
    let _ = AtomicU32::new(0);   // 32位无符号
    let _ = AtomicU16::new(0);   // 16位无符号
    let _ = AtomicU8::new(0);    // 8位无符号

    // 有符号变体
    let _ = AtomicIsize::new(0);
    let _ = AtomicI64::new(0);

    // 布尔和指针
    let _ = AtomicBool::new(false);
    let _: AtomicPtr<String> = AtomicPtr::new(std::ptr::null_mut());
}

/// 平台相关能力
pub fn platform_capabilities() {
    // 检查平台支持的原子操作
    println!("Usize lock free: {}", AtomicUsize::is_lock_free());
    println!("U64 lock free: {}", AtomicU64::is_lock_free());

    // 注意：32位平台可能对64位原子操作使用锁
}
```

### 2.2 加载与存储

```rust
use std::sync::atomic::{AtomicUsize, AtomicPtr, Ordering};

/// 安全的原子加载/存储模式
pub struct AtomicBox<T> {
    ptr: AtomicPtr<T>,
}

impl<T> AtomicBox<T> {
    pub fn new(value: T) -> Self {
        let ptr = Box::into_raw(Box::new(value));
        Self {
            ptr: AtomicPtr::new(ptr),
        }
    }

    /// 加载当前值（创建新引用）
    ///
    /// # Safety
    /// 返回值的生命周期不能超过 &self，且不能并发调用 store
    pub unsafe fn load(&self, ordering: Ordering) -> Option<&T> {
        let ptr = self.ptr.load(ordering);
        if ptr.is_null() {
            None
        } else {
            Some(&*ptr)
        }
    }

    /// 存储新值，返回旧值
    ///
    /// # Safety
    /// 调用者负责释放返回的 Box
    pub unsafe fn store(&self, value: T, ordering: Ordering) -> Option<Box<T>> {
        let new_ptr = Box::into_raw(Box::new(value));
        let old_ptr = self.ptr.swap(new_ptr, ordering);

        if old_ptr.is_null() {
            None
        } else {
            Some(Box::from_raw(old_ptr))
        }
    }

    /// 比较并交换
    pub unsafe fn compare_exchange(
        &self,
        current: *mut T,
        new: T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<*mut T, (*mut T, Box<T>)> {
        let new_ptr = Box::into_raw(Box::new(new));

        match self.ptr.compare_exchange(current, new_ptr, success, failure) {
            Ok(old) => Ok(old),
            Err(actual) => {
                let new_box = Box::from_raw(new_ptr);
                Err((actual, new_box))
            }
        }
    }
}

impl<T> Drop for AtomicBox<T> {
    fn drop(&mut self) {
        let ptr = self.ptr.load(Ordering::Acquire);
        if !ptr.is_null() {
            unsafe {
                drop(Box::from_raw(ptr));
            }
        }
    }
}
```

### 2.3 读-修改-写操作

```rust
use std::sync::atomic::{AtomicUsize, AtomicI64, Ordering};

/// 原子计数器实现
pub struct AtomicCounter {
    value: AtomicUsize,
}

impl AtomicCounter {
    pub fn new() -> Self {
        Self { value: AtomicUsize::new(0) }
    }

    /// 增加并返回旧值
    pub fn fetch_add(&self, delta: usize) -> usize {
        self.value.fetch_add(delta, Ordering::Relaxed)
    }

    /// 减少并返回旧值
    pub fn fetch_sub(&self, delta: usize) -> usize {
        self.value.fetch_sub(delta, Ordering::Relaxed)
    }

    /// 按位与
    pub fn fetch_and(&self, val: usize) -> usize {
        self.value.fetch_and(val, Ordering::Relaxed)
    }

    /// 按位或
    pub fn fetch_or(&self, val: usize) -> usize {
        self.value.fetch_or(val, Ordering::Relaxed)
    }

    /// 按位异或
    pub fn fetch_xor(&self, val: usize) -> usize {
        self.value.fetch_xor(val, Ordering::Relaxed)
    }

    /// 取最大值
    pub fn fetch_max(&self, val: usize) -> usize {
        self.value.fetch_max(val, Ordering::Relaxed)
    }

    /// 取最小值
    pub fn fetch_min(&self, val: usize) -> usize {
        self.value.fetch_min(val, Ordering::Relaxed)
    }

    /// 获取当前值
    pub fn load(&self) -> usize {
        self.value.load(Ordering::Acquire)
    }

    /// 获取并递增（返回新值）
    pub fn increment(&self) -> usize {
        self.value.fetch_add(1, Ordering::Relaxed) + 1
    }
}

/// 原子自增 ID 生成器
pub struct IdGenerator {
    next_id: AtomicU64,
}

impl IdGenerator {
    pub fn new(start: u64) -> Self {
        Self { next_id: AtomicU64::new(start) }
    }

    pub fn next(&self) -> u64 {
        self.next_id.fetch_add(1, Ordering::Relaxed)
    }

    /// 批量分配 ID
    pub fn allocate_batch(&self, count: u64) -> std::ops::Range<u64> {
        let start = self.next_id.fetch_add(count, Ordering::Relaxed);
        start..start + count
    }
}

/// 位标志操作
pub struct AtomicFlags {
    bits: AtomicUsize,
}

impl AtomicFlags {
    pub fn new() -> Self {
        Self { bits: AtomicUsize::new(0) }
    }

    /// 设置标志位
    pub fn set(&self, bit: usize) -> bool {
        let mask = 1usize << bit;
        let old = self.bits.fetch_or(mask, Ordering::AcqRel);
        (old & mask) != 0
    }

    /// 清除标志位
    pub fn clear(&self, bit: usize) -> bool {
        let mask = !(1usize << bit);
        let old = self.bits.fetch_and(mask, Ordering::AcqRel);
        (old & (1usize << bit)) != 0
    }

    /// 切换标志位
    pub fn toggle(&self, bit: usize) -> bool {
        let mask = 1usize << bit;
        let old = self.bits.fetch_xor(mask, Ordering::AcqRel);
        (old & mask) != 0
    }

    /// 测试标志位
    pub fn test(&self, bit: usize) -> bool {
        (self.bits.load(Ordering::Acquire) & (1usize << bit)) != 0
    }
}
```

### 2.4 比较并交换 CAS

```rust
use std::sync::atomic::{AtomicUsize, AtomicPtr, Ordering};
use std::ptr::null_mut;

/// CAS 操作详解
///
/// compare_exchange 返回 Result<*mut T, *mut T>
/// - Ok(old) 表示成功，old 是被替换的值
/// - Err(actual) 表示失败，actual 是实际值（与 expected 不同）

pub struct CASExample<T> {
    data: AtomicPtr<T>,
}

impl<T> CASExample<T> {
    pub fn new() -> Self {
        Self { data: AtomicPtr::new(null_mut()) }
    }

    /// 基本的 CAS 循环
    pub fn cas_loop_store(&self, new_value: T) -> Option<Box<T>> {
        let new_ptr = Box::into_raw(Box::new(new_value));

        loop {
            let current = self.data.load(Ordering::Acquire);

            match self.data.compare_exchange(
                current,
                new_ptr,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(old) => {
                    // 成功，返回旧值
                    if old.is_null() {
                        return None;
                    } else {
                        return Some(unsafe { Box::from_raw(old) });
                    }
                }
                Err(actual) => {
                    // 失败，actual 是新的当前值
                    // 继续循环
                    std::hint::spin_loop();
                }
            }
        }
    }

    /// CAS 弱版本（可能伪失败）
    /// 在某些架构上更高效，适合循环使用
    pub fn cas_weak_loop(&self, new_value: T) {
        let new_ptr = Box::into_raw(Box::new(new_value));

        loop {
            let current = self.data.load(Ordering::Relaxed);

            // compare_exchange_weak 可能因伪失败返回 Err
            match self.data.compare_exchange_weak(
                current,
                new_ptr,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(_) => std::hint::spin_loop(),
            }
        }
    }
}

/// 原子更新模式
pub struct AtomicUpdate<T> {
    value: AtomicUsize,
    _marker: std::marker::PhantomData<T>,
}

impl<T: Copy + Into<usize> + From<usize>> AtomicUpdate<T> {
    pub fn new(initial: T) -> Self {
        Self {
            value: AtomicUsize::new(initial.into()),
            _marker: std::marker::PhantomData,
        }
    }

    /// 使用 CAS 实现原子更新函数
    pub fn update<F>(&self, f: F) -> T
    where
        F: Fn(T) -> T,
    {
        loop {
            let current = self.value.load(Ordering::Acquire);
            let current_t = T::from(current);
            let new = f(current_t);
            let new_usize = new.into();

            match self.value.compare_exchange(
                current,
                new_usize,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(_) => return new,
                Err(_) => std::hint::spin_loop(),
            }
        }
    }
}
```

---

## 3. CAS 循环模式

### 3.1 基本 CAS 循环

```rust
use std::sync::atomic::{AtomicUsize, AtomicPtr, Ordering};
use std::ptr::null_mut;

/// 无锁计数器（带上限）
pub struct BoundedCounter {
    value: AtomicUsize,
    max: usize,
}

impl BoundedCounter {
    pub fn new(max: usize) -> Self {
        Self {
            value: AtomicUsize::new(0),
            max,
        }
    }

    /// 尝试增加，超过上限返回 false
    pub fn try_increment(&self) -> bool {
        loop {
            let current = self.value.load(Ordering::Acquire);

            if current >= self.max {
                return false;
            }

            match self.value.compare_exchange(
                current,
                current + 1,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(_) => return true,
                Err(_) => std::hint::spin_loop(),
            }
        }
    }

    /// 尝试减少
    pub fn try_decrement(&self) -> bool {
        loop {
            let current = self.value.load(Ordering::Acquire);

            if current == 0 {
                return false;
            }

            match self.value.compare_exchange(
                current,
                current - 1,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(_) => return true,
                Err(_) => std::hint::spin_loop(),
            }
        }
    }
}

/// 原子累加器（支持任意增量）
pub struct AtomicAccumulator {
    value: AtomicUsize,
}

impl AtomicAccumulator {
    pub fn new() -> Self {
        Self { value: AtomicUsize::new(0) }
    }

    /// 原子增加指定值
    pub fn add(&self, delta: usize) -> usize {
        // 简单情况：使用 fetch_add
        self.value.fetch_add(delta, Ordering::Relaxed)
    }

    /// 有条件的原子增加
    pub fn add_if<F>(&self, delta: usize, predicate: F) -> Option<usize>
    where
        F: Fn(usize) -> bool,
    {
        loop {
            let current = self.value.load(Ordering::Acquire);

            if !predicate(current) {
                return None;
            }

            let new = current.saturating_add(delta);

            match self.value.compare_exchange(
                current,
                new,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(old) => return Some(old),
                Err(_) => std::hint::spin_loop(),
            }
        }
    }
}
```

### 3.2 ABA 问题与解决

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::ptr::null_mut;

/// ABA 问题说明：
/// 1. 线程 A 读取值 X（地址为 P）
/// 2. 线程 B 将 P 改为 Y，再改回 X
/// 3. 线程 A 的 CAS 成功（值相同），但实际状态已改变
///
/// 解决方案：使用带版本号的指针（Tagged Pointer）

/// 64位打包指针 + 版本号
/// 在 64 位系统上，指针实际使用 48 位，剩余位用于版本号
pub struct TaggedPtr<T> {
    packed: AtomicU64,
    _marker: std::marker::PhantomData<T>,
}

impl<T> TaggedPtr<T> {
    const VERSION_BITS: u64 = 16;
    const POINTER_MASK: u64 = !((1u64 << Self::VERSION_BITS) - 1);
    const VERSION_MASK: u64 = (1u64 << Self::VERSION_BITS) - 1;

    pub fn new(ptr: *mut T) -> Self {
        Self {
            packed: AtomicU64::new(Self::pack(ptr, 0)),
            _marker: std::marker::PhantomData,
        }
    }

    fn pack(ptr: *mut T, version: u64) -> u64 {
        ((ptr as u64) & Self::POINTER_MASK) | (version & Self::VERSION_MASK)
    }

    fn unpack(packed: u64) -> (*mut T, u64) {
        let ptr = (packed & Self::POINTER_MASK) as *mut T;
        let version = packed & Self::VERSION_MASK;
        (ptr, version)
    }

    pub fn load(&self, ordering: Ordering) -> (*mut T, u64) {
        Self::unpack(self.packed.load(ordering))
    }

    pub fn store(&self, ptr: *mut T, version: u64, ordering: Ordering) {
        self.packed.store(Self::pack(ptr, version), ordering);
    }

    /// 安全的 CAS：检查版本号防止 ABA
    pub fn compare_exchange(
        &self,
        current_ptr: *mut T,
        current_version: u64,
        new_ptr: *mut T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<(*mut T, u64), (*mut T, u64)> {
        let current = Self::pack(current_ptr, current_version);
        let new_version = (current_version + 1) & Self::VERSION_MASK;
        let new = Self::pack(new_ptr, new_version);

        match self.packed.compare_exchange(current, new, success, failure) {
            Ok(old) => Ok(Self::unpack(old)),
            Err(old) => Err(Self::unpack(old)),
        }
    }
}

/// 使用 Tagged Pointer 的无锁栈（解决 ABA）
pub struct ABAFreeStack<T> {
    head: TaggedPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: TaggedPtr<Node<T>>,
}

impl<T> ABAFreeStack<T> {
    pub fn new() -> Self {
        Self { head: TaggedPtr::new(null_mut()) }
    }

    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: TaggedPtr::new(null_mut()),
        }));

        loop {
            let (head, version) = self.head.load(Ordering::Acquire);

            // 设置新节点的 next
            unsafe { (*new_node).next.store(head, version, Ordering::Relaxed); }

            match self.head.compare_exchange(
                head,
                version,
                new_node,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(_) => break,
                Err(_) => {
                    std::hint::spin_loop();
                }
            }
        }
    }

    pub fn pop(&self) -> Option<T> {
        loop {
            let (head, version) = self.head.load(Ordering::Acquire);

            if head.is_null() {
                return None;
            }

            let (next, _) = unsafe { (*head).next.load(Ordering::Acquire) };

            match self.head.compare_exchange(
                head,
                version,
                next,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    let node = unsafe { Box::from_raw(head) };
                    return Some(node.data);
                }
                Err(_) => {
                    std::hint::spin_loop();
                }
            }
        }
    }
}
```

### 3.3 帮助机制

```rust
/// 帮助机制（Helping）用于无锁数据结构
/// 当线程无法完成操作时，帮助其他线程完成

use std::sync::atomic::{AtomicUsize, AtomicPtr, Ordering};

/// 操作描述符（用于帮助机制）
#[repr(align(8))]
pub struct Operation<T> {
    state: AtomicUsize,
    data: *mut T,
}

const STATE_IDLE: usize = 0;
const STATE_IN_PROGRESS: usize = 1;
const STATE_COMPLETED: usize = 2;

pub struct HelpingStack<T> {
    head: AtomicPtr<Node<T>>,
    pending_op: AtomicPtr<Operation<Node<T>>>,
}

struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

impl<T> HelpingStack<T> {
    pub fn new() -> Self {
        Self {
            head: AtomicPtr::new(std::ptr::null_mut()),
            pending_op: AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    /// 尝试完成待处理的操作
    fn help_complete(&self) {
        let op_ptr = self.pending_op.load(Ordering::Acquire);
        if op_ptr.is_null() {
            return;
        }

        let op = unsafe { &*op_ptr };
        let state = op.state.load(Ordering::Acquire);

        if state == STATE_IN_PROGRESS {
            // 帮助完成操作
            // 这里简化处理，实际取决于具体操作类型
            let _ = op.state.compare_exchange(
                STATE_IN_PROGRESS,
                STATE_COMPLETED,
                Ordering::Release,
                Ordering::Relaxed,
            );
        }
    }

    pub fn push(&self, data: T) {
        // 首先尝试帮助完成其他操作
        self.help_complete();

        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: std::ptr::null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Acquire);
            unsafe { (*new_node).next = head; }

            match self.head.compare_exchange(
                head,
                new_node,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(_) => return,
                Err(_) => {
                    std::hint::spin_loop();
                    self.help_complete();
                }
            }
        }
    }
}
```

---

## 4. 无锁延迟初始化 (Rust 1.94)

### LazyLock 的无锁语义

Rust 1.94 引入的 `LazyLock::get()` 和相关方法提供了一种无锁的延迟初始化模式，与传统的 `std::sync::Once` 相比具有更好的可组合性：

```rust
use std::sync::LazyLock;
use std::sync::atomic::{AtomicPtr, Ordering};

/// 比较：传统 Once vs LazyLock (Rust 1.94)

// 传统方式 - 使用 Once
static mut TRADITIONAL_DATA: Option<ExpensiveResource> = None;
static INIT: std::sync::Once = std::sync::Once::new();

fn get_traditional() -> &'static ExpensiveResource {
    unsafe {
        INIT.call_once(|| {
            TRADITIONAL_DATA = Some(ExpensiveResource::new());
        });
        TRADITIONAL_DATA.as_ref().unwrap()
    }
}

// Rust 1.94 方式 - 使用 LazyLock
static LAZY_DATA: LazyLock<ExpensiveResource> = LazyLock::new(|| {
    ExpensiveResource::new()
});

fn get_lazy() -> &'static ExpensiveResource {
    // 更安全、更简洁的 API
    LAZY_DATA.get()
}

pub struct ExpensiveResource {
    data: Vec<u8>,
    ptr: AtomicPtr<u8>,
}

impl ExpensiveResource {
    fn new() -> Self {
        let data = vec![0u8; 1024 * 1024]; // 1MB
        let ptr = AtomicPtr::new(data.as_ptr() as *mut u8);
        Self { data, ptr }
    }

    /// 无锁获取数据指针
    pub fn get_ptr(&self) -> *mut u8 {
        self.ptr.load(Ordering::Acquire)
    }
}

/// 在高并发场景中使用 LazyLock
fn concurrent_access() {
    use std::thread;

    let handles: Vec<_> = (0..100)
        .map(|_| {
            thread::spawn(|| {
                // 所有线程都能安全地并发访问
                // 初始化只发生一次
                let resource = LAZY_DATA.get();
                let _ptr = resource.get_ptr();
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }
}
```

### LazyLock 与无锁数据结构组合

```rust
use std::sync::LazyLock;
use crossbeam::epoch::{self, Atomic, Owned, Shared};
use std::sync::atomic::Ordering;

/// 延迟初始化的无锁栈
static LAZY_STACK: LazyLock<LockFreeStack<i32>> = LazyLock::new(|| {
    LockFreeStack::new()
});

pub struct LockFreeStack<T> {
    head: Atomic<Node<T>>,
}

struct Node<T> {
    data: T,
    next: Atomic<Node<T>>,
}

impl<T> LockFreeStack<T> {
    fn new() -> Self {
        Self {
            head: Atomic::null(),
        }
    }

    pub fn push(&self, data: T) {
        let guard = &epoch::pin();
        let new_node = Owned::new(Node {
            data,
            next: Atomic::null(),
        }).into_shared(guard);

        loop {
            let head = self.head.load(Ordering::Acquire, guard);
            unsafe { new_node.deref().next.store(head, Ordering::Relaxed) }

            match self.head.compare_exchange(
                head,
                new_node,
                Ordering::Release,
                Ordering::Acquire,
                guard,
            ) {
                Ok(_) => break,
                Err(_) => continue,
            }
        }
    }
}

/// 获取全局无锁栈（Rust 1.94）
pub fn get_lazy_stack() -> &'static LockFreeStack<i32> {
    LAZY_STACK.get()
}
```

## 4. 无锁数据结构

### 4.1 无锁栈

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr::null_mut;

/// Treiber Stack - 经典无锁栈
pub struct TreiberStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

impl<T> TreiberStack<T> {
    pub fn new() -> Self {
        Self { head: AtomicPtr::new(null_mut()) }
    }

    /// 压栈 - Lock-free
    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Acquire);
            unsafe { (*new_node).next = head; }

            match self.head.compare_exchange_weak(
                head,
                new_node,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(_) => std::hint::spin_loop(),
            }
        }
    }

    /// 弹栈 - Lock-free
    pub fn pop(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);

            if head.is_null() {
                return None;
            }

            let next = unsafe { (*head).next };

            match self.head.compare_exchange_weak(
                head,
                next,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    let node = unsafe { Box::from_raw(head) };
                    return Some(node.data);
                }
                Err(_) => std::hint::spin_loop(),
            }
        }
    }

    /// 判断是否为空
    pub fn is_empty(&self) -> bool {
        self.head.load(Ordering::Acquire).is_null()
    }
}

impl<T> Drop for TreiberStack<T> {
    fn drop(&mut self) {
        while self.pop().is_some() {}
    }
}

// 性能优化：批量弹栈
impl<T> TreiberStack<T> {
    /// 批量弹出（减少 CAS 次数）
    pub fn pop_batch(&self, max: usize) -> Vec<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            if head.is_null() {
                return vec![];
            }

            // 找到第 max 个节点
            let mut tail = head;
            let mut count = 1;

            while count < max {
                let next = unsafe { (*tail).next };
                if next.is_null() {
                    break;
                }
                tail = next;
                count += 1;
            }

            let next = unsafe { (*tail).next };

            // 尝试一次 CAS 获取整个批次
            match self.head.compare_exchange(
                head,
                next,
                Ordering::Release,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    // 收集数据
                    let mut result = Vec::with_capacity(count);
                    let mut current = head;

                    while current != next {
                        let node = unsafe { Box::from_raw(current) };
                        result.push(node.data);
                        current = node.next;
                    }

                    return result;
                }
                Err(_) => {
                    std::hint::spin_loop();
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_concurrent_push_pop() {
        let stack = Arc::new(TreiberStack::new());
        let mut handles = vec![];

        // 多个线程并发 push
        for i in 0..100 {
            let s = stack.clone();
            handles.push(thread::spawn(move || {
                s.push(i);
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        // 验证所有元素都能被弹出
        let mut count = 0;
        while stack.pop().is_some() {
            count += 1;
        }

        assert_eq!(count, 100);
    }
}
```

### 4.2 无锁队列

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr::null_mut;

/// Michael-Scott Queue - 经典无锁队列
pub struct MSQueue<T> {
    head: AtomicPtr<Node<T>>,
    tail: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
}

impl<T> MSQueue<T> {
    pub fn new() -> Self {
        let dummy = Box::into_raw(Box::new(Node {
            data: unsafe { std::mem::zeroed() }, // 哑节点的数据不会被使用
            next: AtomicPtr::new(null_mut()),
        }));

        Self {
            head: AtomicPtr::new(dummy),
            tail: AtomicPtr::new(dummy),
        }
    }

    /// 入队 - Lock-free
    pub fn enqueue(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: AtomicPtr::new(null_mut()),
        }));

        loop {
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*tail).next.load(Ordering::Acquire) };

            // 检查 tail 是否仍然是最新的
            if tail == self.tail.load(Ordering::Acquire) {
                if next.is_null() {
                    // 尝试链接新节点
                    if unsafe { (*tail).next.compare_exchange(
                        next,
                        new_node,
                        Ordering::Release,
                        Ordering::Relaxed,
                    ).is_ok() } {
                        // 尝试更新 tail（失败也没关系，其他线程会帮助完成）
                        let _ = self.tail.compare_exchange(
                            tail,
                            new_node,
                            Ordering::Release,
                            Ordering::Relaxed,
                        );
                        return;
                    }
                } else {
                    // tail 落后了，帮助推进
                    let _ = self.tail.compare_exchange(
                        tail,
                        next,
                        Ordering::Release,
                        Ordering::Relaxed,
                    );
                }
            }

            std::hint::spin_loop();
        }
    }

    /// 出队 - Lock-free
    pub fn dequeue(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*head).next.load(Ordering::Acquire) };

            if head == self.head.load(Ordering::Acquire) {
                if head == tail {
                    // 队列可能为空
                    if next.is_null() {
                        return None;
                    }
                    // tail 落后了，帮助推进
                    let _ = self.tail.compare_exchange(
                        tail,
                        next,
                        Ordering::Release,
                        Ordering::Relaxed,
                    );
                } else {
                    // 尝试出队
                    let data = unsafe { &(*next).data };

                    if self.head.compare_exchange(
                        head,
                        next,
                        Ordering::Release,
                        Ordering::Relaxed,
                    ).is_ok() {
                        // 安全地获取数据
                        let data = unsafe { std::ptr::read(data) };
                        // 释放旧的头节点
                        unsafe { drop(Box::from_raw(head)); }
                        return Some(data);
                    }
                }
            }

            std::hint::spin_loop();
        }
    }
}

// 优化版本：使用计数器避免 ABA
pub struct CountedMSQueue<T> {
    head: AtomicPtr<Node<T>>,
    head_count: AtomicUsize,
    tail: AtomicPtr<Node<T>>,
    tail_count: AtomicUsize,
}

struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
}

use std::sync::atomic::AtomicUsize;

impl<T> CountedMSQueue<T> {
    pub fn new() -> Self {
        let dummy = Box::into_raw(Box::new(Node {
            data: unsafe { std::mem::zeroed() },
            next: AtomicPtr::new(null_mut()),
        }));

        Self {
            head: AtomicPtr::new(dummy),
            head_count: AtomicUsize::new(0),
            tail: AtomicPtr::new(dummy),
            tail_count: AtomicUsize::new(0),
        }
    }
}
```

（继续...）
