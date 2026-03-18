# Rust 原子操作 (Atomic Operations)

> 掌握无锁编程的核心：深入理解 Rust 中的原子类型、内存顺序和 CAS 操作，构建高性能并发程序。
>
> **预计学习时间**: 60-90 分钟
> **难度**: 高级

---

## 🎯 学习目标

完成本章节后，你将能够：

- 理解原子操作的硬件基础和语义保证
- 熟练使用 `AtomicBool`、`AtomicUsize`、`AtomicPtr` 等类型
- **掌握内存顺序**（Relaxed、Acquire、Release、AcqRel、SeqCst）的选择原则
- 使用 CAS（Compare-and-swap）实现无锁算法
- 实现基础的无锁数据结构
- 在性能与正确性之间做出明智的权衡

---

## 📋 先决条件

在学习本章之前，请确保你已经掌握：

- Rust 所有权和生命周期系统
- 基础并发概念（线程、互斥锁 `Mutex`、读写锁 `RwLock`）
- `std::sync::Arc` 和线程间共享数据
- Unsafe Rust 的基础知识

---

## 🧠 核心概念

### 什么是原子操作

**原子操作**（Atomic Operation）是指不可中断的操作——要么完全执行，要么完全不执行，不存在中间状态。从硬件层面看，现代 CPU 提供专门的指令来保证对单个内存位置的操作的原子性。

原子操作的核心优势：

1. **无锁**（Lock-free）：不会阻塞线程，避免死锁风险
2. **低开销**：通常比互斥锁更快（无上下文切换）
3. **确定性强**：提供精确的内存语义控制

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

fn main() {
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                // 原子递增，无需加锁
                counter.fetch_add(1, Ordering::Relaxed);
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(counter.load(Ordering::Relaxed), 10000);
    println!("计数器最终值: {}", counter.load(Ordering::Relaxed));
}
```

### 原子类型概览

Rust 标准库在 `std::sync::atomic` 模块中提供以下原子类型：

| 类型 | 用途 | 对应普通类型 |
|------|------|-------------|
| `AtomicBool` | 布尔标志 | `bool` |
| `AtomicU8` / `AtomicI8` | 8位整数 | `u8` / `i8` |
| `AtomicU16` / `AtomicI16` | 16位整数 | `u16` / `i16` |
| `AtomicU32` / `AtomicI32` | 32位整数 | `u32` / `i32` |
| `AtomicU64` / `AtomicI64` | 64位整数 | `u64` / `i64` |
| `AtomicUsize` / `AtomicIsize` | 平台相关整数 | `usize` / `isize` |
| `AtomicPtr<T>` | 原始指针 | `*mut T` |

**重要限制**：

- 原子类型不是 `Copy` 类型，但可以通过引用共享
- 只能存储在堆上或通过 `static` 声明
- 不支持复合类型（如结构体），需要使用 `AtomicPtr` 配合 `Box`

### 内存顺序 (Memory Ordering)

**内存顺序是原子操作中最复杂、最关键的概念**。它决定了操作之间的可见性保证和指令重排的约束。

#### 1. Relaxed —— 最弱约束

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

fn increment() {
    // Relaxed: 仅保证原子性，无顺序约束
    // 编译器和 CPU 可以自由重排指令
    COUNTER.fetch_add(1, Ordering::Relaxed);
}
```

**适用场景**：

- 简单的计数器（只关心最终值，不关心中间状态的可见性）
- 性能敏感的统计场景

**风险**：其他线程可能以意想不到的顺序看到这个操作的结果。

#### 2. Acquire / Release —— 成对使用

**Acquire**（获取）用于**读**操作，**Release**（释放）用于**写**操作。它们共同建立 **happens-before** 关系。

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

// 使用 Acquire/Release 实现简单的线程同步
static READY: AtomicBool = AtomicBool::new(false);
static mut DATA: u64 = 0;

fn producer() {
    unsafe {
        // 先写入数据
        DATA = 42;
    }
    // Release: 之前的所有写操作对后续的 Acquire 可见
    READY.store(true, Ordering::Release);
}

fn consumer() -> u64 {
    // Acquire: 确保看到 Release 之前的所有写操作
    while !READY.load(Ordering::Acquire) {
        // 自旋等待
        std::hint::spin_loop();
    }
    unsafe {
        // 保证能看到 DATA = 42
        DATA
    }
}
```

**语义图解**：

```
Producer Thread              Consumer Thread
-------------                ---------------
DATA = 42                     READY.load(Acquire)
    ↓                                 ↑
READY.store(Release) ───────→ happens-before
```

#### 3. AcqRel —— 读写组合

用于**读-修改-写**操作（如 `fetch_add`、`compare_exchange`）：

- 作为**读取**部分：使用 Acquire 语义
- 作为**写入**部分：使用 Release 语义

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

fn fetch_and_increment(counter: &AtomicUsize) -> usize {
    // 读取时 Acquire，写入时 Release
    counter.fetch_add(1, Ordering::AcqRel)
}
```

#### 4. SeqCst —— 顺序一致性

最严格的内存顺序，提供**全局顺序**保证：

```rust
use std::sync::atomic::{AtomicBool, Ordering};

// 使用 SeqCst 实现 Dekker 算法（互斥锁）
static FLAG_A: AtomicBool = AtomicBool::new(false);
static FLAG_B: AtomicBool = AtomicBool::new(false);

// SeqCst 保证所有线程以相同的顺序看到操作
```

**适用场景**：

- 需要全局同步顺序的复杂算法
- 多个原子变量之间的依赖关系

**代价**：性能开销最大，通常比 Relaxed 慢 2-10 倍。

#### 内存顺序选择决策树

```
是否需要同步其他数据？
├── 否 → Relaxed（仅计数器、统计）
└── 是 → 是否涉及多个原子变量？
    ├── 是 → SeqCst（安全但慢）
    └── 否 → 使用 Acquire/Release 或 AcqRel
        ├── 仅读 → Acquire
        ├── 仅写 → Release
        └── 读改写 → AcqRel
```

### Compare-and-Swap (CAS) 操作

CAS 是无锁算法的核心原语，提供**原子性的条件更新**：

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

/// 使用 CAS 实现无锁栈的 Push 操作（简化版）
pub struct Node<T> {
    pub value: T,
    pub next: Option<Box<Node<T>>>,
}

pub struct LockFreeStack<T> {
    head: AtomicUsize, // 实际存储 *mut Node<T>
}

impl<T> LockFreeStack<T> {
    pub fn push(&self, value: T) {
        let new_node = Box::into_raw(Box::new(Node {
            value,
            next: None,
        })) as usize;

        loop {
            let current_head = self.head.load(Ordering::Acquire);

            // 将新节点的 next 指向当前 head
            unsafe {
                (*(new_node as *mut Node<T>)).next =
                    if current_head == 0 {
                        None
                    } else {
                        Some(Box::from_raw(current_head as *mut Node<T>))
                    };
            }

            // CAS: 如果 head 仍等于 current_head，则更新为 new_node
            match self.head.compare_exchange(
                current_head,
                new_node,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break, // 成功，退出循环
                Err(_) => continue, // 失败，重试
            }
        }
    }
}
```

**ABA 问题**：CAS 的经典陷阱。如果值从 A→B→A，CAS 会认为没有变化。解决方案包括：

- 使用带标签的指针（Tagged Pointer）
- 使用 hazard pointers 或 epoch-based 内存回收

### Fetch-and-Modify 操作

常见的原子修改操作：

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

let value = AtomicUsize::new(10);

// fetch_add: 加并返回旧值
let old = value.fetch_add(5, Ordering::Relaxed); // old = 10, value = 15

// fetch_sub: 减并返回旧值
let old = value.fetch_sub(3, Ordering::Relaxed); // old = 15, value = 12

// fetch_and / fetch_or / fetch_xor: 位运算
value.fetch_and(0b1110, Ordering::Relaxed); // 位与

// swap: 交换值并返回旧值
let old = value.swap(100, Ordering::Relaxed);

// compare_exchange: CAS 操作
let result = value.compare_exchange(
    100,        // 期望值
    200,        // 新值
    Ordering::SeqCst,  // 成功时的内存序
    Ordering::Relaxed, // 失败时的内存序
);
```

### 无锁数据结构基础

#### 自旋锁实现

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};

/// 简单的自旋锁（Spinlock）
pub struct SpinLock<T> {
    locked: AtomicBool,
    data: UnsafeCell<T>,
}

// 标记为 Sync，允许多线程共享
unsafe impl<T> Sync for SpinLock<T> where T: Send {}

pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<T> Drop for SpinLockGuard<'_, T> {
    fn drop(&mut self) {
        // Release: 确保临界区的所有写操作在解锁前完成
        self.lock.locked.store(false, Ordering::Release);
    }
}

impl<T> Deref for SpinLockGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<T> DerefMut for SpinLockGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<T> SpinLock<T> {
    pub const fn new(data: T) -> Self {
        Self {
            locked: AtomicBool::new(false),
            data: UnsafeCell::new(data),
        }
    }

    pub fn lock(&self) -> SpinLockGuard<T> {
        // Acquire: 确保临界区的读操作能看到之前的写操作
        while self.locked.compare_exchange_weak(
            false,
            true,
            Ordering::Acquire,
            Ordering::Relaxed,
        ).is_err() {
            // 自旋等待，可选：加入退避策略
            while self.locked.load(Ordering::Relaxed) {
                std::hint::spin_loop();
            }
        }
        SpinLockGuard { lock: self }
    }
}
```

### 原子与互斥锁的对比

| 特性 | 原子操作 | 互斥锁 (`Mutex`) |
|------|---------|-----------------|
| **阻塞** | 非阻塞（忙等或立即失败） | 阻塞线程（可休眠） |
| **开销** | 低（无上下文切换） | 高（可能涉及系统调用） |
| **复杂度** | 高（需处理内存序、ABA 等） | 低（简单直观） |
| **适用场景** | 简单计数、无锁结构 | 复杂数据结构、长临界区 |
| **死锁风险** | 低 | 高（需小心加锁顺序） |
| **公平性** | 无保证（可能饥饿） | 通常有公平性保证 |

**选择建议**：

- 优先使用 `Mutex`，除非性能分析证明它是瓶颈
- 原子操作适合：计数器、标志位、简单的无锁队列
- 无锁编程是高级技术，需要严格的正确性验证

---

## 💡 最佳实践

1. **默认使用最弱的内存序**：从 `Relaxed` 开始，仅在必要时增强

   ```rust
   // 好的做法：计数器用 Relaxed
   counter.fetch_add(1, Ordering::Relaxed);
   ```

2. **成对使用 Acquire/Release**：确保同步语义完整

   ```rust
   // 生产者用 Release
   data.store(value, Ordering::Release);
   ready.store(true, Ordering::Release);

   // 消费者用 Acquire
   while !ready.load(Ordering::Acquire) {}
   let value = data.load(Ordering::Acquire); // 或 Relaxed
   ```

3. **CAS 使用退避策略**：在高竞争场景避免无限自旋

   ```rust
   let mut backoff = 1;
   loop {
       match atomic.compare_exchange(...) {
           Ok(_) => break,
           Err(_) => {
               std::thread::sleep(std::time::Duration::from_nanos(backoff));
               backoff = (backoff * 2).min(1000); // 指数退避
           }
       }
   }
   ```

4. **使用 `compare_exchange_weak` 在循环中**：在 ARM 等架构上更高效

   ```rust
   while atomic.compare_exchange_weak(
       expected, new, success, failure
   ).is_err() {
       // 重试
   }
   ```

5. **考虑使用 `crossbeam` 库**：专业的无锁数据结构库

   ```toml
   [dependencies]
   crossbeam = "0.8"
   ```

---

## ⚠️ 常见陷阱

1. **忘记 Unsafe Rust**：原子操作常与 `UnsafeCell`、原始指针配合使用

   ```rust
   // 错误：无法直接获得可变引用
   let value = atomic.load(Ordering::Relaxed);
   value += 1; // 这不是原子操作！
   ```

2. **混合使用不同的内存序**：可能导致数据竞争

   ```rust
   // 危险：生产者用 Relaxed
   data.store(42, Ordering::Relaxed);

   // 消费者用 Acquire - 可能看不到 42！
   while !flag.load(Ordering::Acquire) {}
   ```

3. **ABA 问题**：指针重用导致 CAS 误判

   ```rust
   // 危险：如果指针被释放并重新分配相同地址
   if head.compare_exchange(ptr_a, ptr_b, ...).is_ok() {
       // ptr_a 可能已经被释放并重新分配了！
   }
   ```

4. **忽视架构差异**：64位原子操作在 32位架构上可能不原生支持

   ```rust
   // 在 32位 ARM 上，AtomicU64 操作可能使用锁
   use std::sync::atomic::AtomicU64;
   ```

5. **过度优化内存序**：过早优化可能导致微妙的 bug

   ```rust
   // 除非确定性能瓶颈，否则信号标志用 SeqCst 更安全
   static FLAG: AtomicBool = AtomicBool::new(false);
   ```

---

## 🎮 动手练习

### 练习 1: 无锁计数器

实现一个线程安全的计数器，支持 `increment()` 和 `get()` 方法：

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct LockFreeCounter {
    value: AtomicUsize,
}

impl LockFreeCounter {
    pub fn new() -> Self {
        Self {
            value: AtomicUsize::new(0),
        }
    }

    pub fn increment(&self) {
        // TODO: 实现原子递增
        todo!()
    }

    pub fn get(&self) -> usize {
        // TODO: 实现原子读取
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_concurrent_counter() {
        let counter = Arc::new(LockFreeCounter::new());
        let mut handles = vec![];

        for _ in 0..100 {
            let counter = Arc::clone(&counter);
            handles.push(thread::spawn(move || {
                for _ in 0..1000 {
                    counter.increment();
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(counter.get(), 100_000);
    }
}
```

### 练习 2: 单次初始化 (One-shot Initialization)

使用原子操作实现一个只执行一次的初始化：

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::mem::MaybeUninit;

pub struct OnceCell<T> {
    state: AtomicUsize,
    value: MaybeUninit<T>,
}

// 状态常量
const UNINITIALIZED: usize = 0;
const INITIALIZING: usize = 1;
const INITIALIZED: usize = 2;

impl<T> OnceCell<T> {
    pub const fn new() -> Self {
        Self {
            state: AtomicUsize::new(UNINITIALIZED),
            value: MaybeUninit::uninit(),
        }
    }

    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        // TODO: 使用 CAS 实现线程安全的延迟初始化
        todo!()
    }
}
```

<details>
<summary>点击查看答案</summary>

```rust
pub fn get_or_init<F>(&self, f: F) -> &T
where
    F: FnOnce() -> T,
{
    // 快速路径：已初始化
    if self.state.load(Ordering::Acquire) == INITIALIZED {
        return unsafe { &*self.value.as_ptr() };
    }

    // 尝试获取初始化权
    match self.state.compare_exchange(
        UNINITIALIZED,
        INITIALIZING,
        Ordering::Acquire,
        Ordering::Relaxed,
    ) {
        Ok(_) => {
            // 执行初始化
            let value = f();
            unsafe {
                (*self.value.as_mut_ptr()) = value;
            }
            // 标记为已完成，使用 Release 确保初始化结果可见
            self.state.store(INITIALIZED, Ordering::Release);
            unsafe { &*self.value.as_ptr() }
        }
        Err(_) => {
            // 其他线程正在初始化，等待完成
            while self.state.load(Ordering::Acquire) != INITIALIZED {
                std::hint::spin_loop();
            }
            unsafe { &*self.value.as_ptr() }
        }
    }
}
```

</details>

---

## 📖 延伸阅读

### 官方文档

- [The Rust Programming Language - Shared-State Concurrency](https://doc.rust-lang.org/book/ch16-03-shared-state.html)
- [std::sync::atomic - Rust 标准库文档](https://doc.rust-lang.org/std/sync/atomic/index.html)

### 推荐书籍

- **《Rust Atomics and Locks》** by Mara Bos —— 原子操作和并发编程的权威指南
- **《The Art of Multiprocessor Programming》** by Herlihy & Shavit —— 无锁算法经典

### 相关 crate

| Crate | 用途 |
|-------|------|
| `crossbeam` | 高级无锁数据结构（队列、栈、epoch GC） |
| `parking_lot` | 高性能锁原语 |
| `loom` | 并发代码的模型检测工具 |
| `sharded-slab` | 无锁的 slab 分配器 |

### 硬件基础

- [内存屏障（Memory Barrier）](https://en.wikipedia.org/wiki/Memory_barrier)
- [CPU 缓存一致性协议（MESI）](https://en.wikipedia.org/wiki/MESI_protocol)
- [Load-Link/Store-Conditional (LL/SC)](https://en.wikipedia.org/wiki/Load-link/store-conditional)

---

> 💡 **总结**：原子操作是 Rust 并发编程的强大工具，但伴随而来的是对内存模型的深入理解需求。牢记：**除非必要，优先使用互斥锁；当性能成为瓶颈且你能证明正确性时，才考虑无锁编程**。
