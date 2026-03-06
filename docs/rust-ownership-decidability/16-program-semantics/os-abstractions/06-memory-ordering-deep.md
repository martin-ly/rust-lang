# 内存序的深度语义分析

## 1. 引言

内存序（Memory Ordering）定义了原子操作之间的可见性和执行顺序保证。
在弱内存模型架构（如 ARM、RISC-V）上，理解和正确使用内存序对编写正确的并发代码至关重要。
本文档深入分析 Rust 中五种内存序的形式化语义。

## 2. Happens-Before 关系的形式化

### 2.1 基本定义

```
Happens-Before 关系 (hb):

  定义:
    hb ⊆ Event × Event

    对于事件 e1, e2:
      e1 →hb e2 (e1 happens-before e2)

  性质:
    1. 传递性: e1 →hb e2 ∧ e2 →hb e3 ⟹ e1 →hb e3
    2. 非自反: ¬(e →hb e)
    3. 非对称: e1 →hb e2 ⟹ ¬(e2 →hb e1)

  意义:
    e1 →hb e2 意味着 e1 的效果对 e2 可见
```

### 2.2 Happens-Before 的构成

```
Happens-Before 的来源:

  1. 程序序 (Program Order, po):
     同一线程内的操作按程序顺序 happens-before

  2. 同步边 (Synchronizes-With, sw):
     同步操作建立的跨线程 happens-before

  3. 传递闭包:
     hb = (po ∪ sw)+

  图示:
    线程 A:  W(x) ──po──> R(y)
                │
               sw
                │
    线程 B:  W(y) ──po──> R(x)

    若 W(x) sw W(y)，则 W(x) hb R(x)
```

### 2.3 Rust 中的同步边

```
Rust 中的 Synchronizes-With 关系:

  1. 互斥锁:
     unlock(m) → sw → lock(m)

  2. 原子操作:
     store(x, ord) → sw → load(x, ord')
     当 ord 是 Release/AcqRel/SeqCst
     且 ord' 是 Acquire/AcqRel/SeqCst

  3. 线程创建:
     spawn 之前的操作 → sw → 新线程的开始

  4. 线程 join:
     被 join 线程的最后操作 → sw → join 之后的操作
```

## 3. 五种内存序的精确语义

### 3.1 Relaxed 语义

```
Relaxed 形式化定义:

  约束:
    仅保证原子性，无顺序约束

  允许的重排序:
    - 编译器重排序: 允许
    - CPU 重排序: 允许

  原子性保证:
    读: 读到完整的值（不会读到写一半的值）
    写: 写操作原子完成
    RMW: 读-改-写操作原子完成

  使用场景:
    - 简单的计数器（不需要同步）
    - 标志位（配合其他同步机制）
```

### 3.2 Acquire/Release 语义

```
Acquire 语义:

  load(x, Acquire) 保证:
    该 load 操作 happens-before 之后所有的读/写操作

  形式化:
    load(x, Acquire) →hb 后续操作

Release 语义:

  store(x, Release) 保证:
    之前所有的读/写操作 happens-before 该 store

  形式化:
    前置操作 →hb store(x, Release)

Acquire-Release 对:
  store(x, Release) →sw load(x, Acquire)

  因此:
    线程 A 的前置操作 →hb 线程 B 的后续操作
```

### 3.3 AcqRel 语义

```
AcqRel 形式化定义:

  RMW 操作的内存序:
    - 读部分: Acquire 语义
    - 写部分: Release 语义

  效果:
    前置操作 →hb RMW →hb 后续操作

  使用场景:
    - 原子自增/自减（计数器）
    - Compare-And-Swap 操作
    - 无锁数据结构
```

### 3.4 SeqCst 语义

```
SeqCst (顺序一致性) 形式化定义:

  保证:
    1. 所有线程以相同的顺序看到所有 SeqCst 操作
    2. 程序序在 SeqCst 操作之间保持

  形式化:
    存在一个全局总序 S，包含所有 SeqCst 操作
    且 S 与每个线程的程序序一致

  与其他内存序的关系:
    SeqCst 是最强的内存序
    SeqCst →hb 包含所有其他 happens-before 关系

  开销:
    性能代价最高，通常需要更多的内存屏障
```

### 3.5 内存序对比表

```
内存序能力对比:

| 内存序    | 原子性 | 阻止前序重排 | 阻止后序重排 | 全局顺序 |
|-----------|--------|--------------|--------------|----------|
| Relaxed   | ✓      | ✗            | ✗            | ✗        |
| Acquire   | ✓      | ✗            | ✓            | ✗        |
| Release   | ✓      | ✓            | ✗            | ✗        |
| AcqRel    | ✓      | ✓            | ✓            | ✗        |
| SeqCst    | ✓      | ✓            | ✓            | ✓        |

阻止重排的含义:
  - 阻止前序重排: 前面的操作不能重排到后面
  - 阻止后序重排: 后面的操作不能重排到前面
```

## 4. Rust 代码示例

### 4.1 Relaxed 使用示例

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;

fn relaxed_counter() {
    let counter = AtomicUsize::new(0);

    let mut handles = vec![];

    for _ in 0..10 {
        handles.push(thread::spawn(|| {
            for _ in 0..1000 {
                // Relaxed 对于纯计数器是安全的
                counter.fetch_add(1, Ordering::Relaxed);
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    println!("计数结果: {}", counter.load(Ordering::Relaxed));
}
```

### 4.2 Acquire-Release 使用示例

```rust
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::thread;

fn acquire_release_example() {
    let ready = AtomicBool::new(false);
    let data = AtomicI32::new(0);

    thread::spawn(|| {
        // 准备数据
        data.store(123, Ordering::Relaxed);

        // Release: 确保前面的写操作对获取方可见
        ready.store(true, Ordering::Release);
    });

    // Acquire: 确保看到 Release 之前的所有写操作
    while !ready.load(Ordering::Acquire) {
        thread::yield_now();
    }

    // 现在可以安全地读取 data
    assert_eq!(data.load(Ordering::Relaxed), 123);
}
```

### 4.3 SeqCst 使用示例

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

fn seqcst_example() {
    let x = AtomicBool::new(false);
    let y = AtomicBool::new(false);

    let mut handles = vec![];

    // 线程 1
    let x1 = x.clone();
    let y1 = y.clone();
    handles.push(thread::spawn(move || {
        x1.store(true, Ordering::SeqCst);
        if !y1.load(Ordering::SeqCst) {
            println!("线程 1 先执行");
        }
    }));

    // 线程 2
    let x2 = x.clone();
    let y2 = y.clone();
    handles.push(thread::spawn(move || {
        y2.store(true, Ordering::SeqCst);
        if !x2.load(Ordering::SeqCst) {
            println!("线程 2 先执行");
        }
    }));

    for h in handles {
        h.join().unwrap();
    }

    // 使用 SeqCst，不可能同时打印两句话
}
```

## 5. 内存模型的公理化

### 5.1 C++11 内存模型基础

```
Rust 内存模型基于 C++11:

  核心概念:
    1. 数据竞争自由 (Data-Race-Free, DRF)
    2. 顺序一致性 (Sequential Consistency, SC)
    3. Release-Acquire 同步

  DRF 保证:
    若程序没有数据竞争，则行为等价于顺序一致性执行

  数据竞争定义:
    两个操作访问同一内存位置，且:
    - 至少一个是写操作
    - 至少一个不是原子操作
    - 不存在 happens-before 关系
```

### 5.2 公理化规则

```
内存模型的公理化规则:

  A1 (原子性):
    每个原子操作都是不可分割的

  A2 (一致性):
    对同一位置的操作，所有线程看到相同的修改顺序

  A3 ( happens-before 传递性):
    hb 是传递的

  A4 ( synchronizes-with 一致性):
    sw 关系与程序序和修改顺序一致

  A5 ( coherence):
    对同一位置的读写满足 coherence 规则:
    - Read-Read Coherence
    - Read-Write Coherence
    - Write-Read Coherence
    - Write-Write Coherence
```

### 5.3 Coherence 规则

```
Coherence 规则详细:

  设 M 是内存位置的所有修改操作的序列

  Read-Write Coherence:
    若 read r 读取 write w 的值
    则 r →hb 后续的 write w' 是不可能的

  Write-Read Coherence:
    若 write w →hb read r
    则 r 读取的值必须是 w 或更晚的 write

  Write-Write Coherence:
    write 操作按 happens-before 顺序出现在 M 中

  Read-Read Coherence:
    若 read r1 →hb read r2，
    且 r1 和 r2 都读取 write w
    则它们不能读取 w 之前的不同值
```

## 6. 弱内存行为的形式化

### 6.1 弱内存模型的特征

```
弱内存模型（ARM、RISC-V）:

  特征:
    1. 允许更多的重排序
    2. 每个核有自己的写缓冲区
    3. 没有全局统一的内存视图

  允许的重排序:
    - Load-Load: 允许
    - Load-Store: 允许
    - Store-Load: 允许（x86 不允许）
    - Store-Store: 通常不允许

  内存屏障需求:
    需要显式的内存屏障来保证顺序
```

### 6.2 Store Buffer 的形式化

```
Store Buffer 模型:

  每个核心:
    - Store Buffer: 待写入内存的操作队列
    - Cache: 本地缓存

  Store 操作:
    1. 写入 Store Buffer（立即返回）
    2. 异步刷新到内存

  Load 操作:
    1. 检查 Store Buffer
    2. 检查本地 Cache
    3. 读取内存

  问题:
    其他核心可能看不到本核心的写操作
    需要内存屏障强制刷新
```

### 6.3 内存屏障的形式化

```
内存屏障类型:

  Load-Load Barrier:
    屏障前的 Load 必须在屏障后的 Load 之前完成

  Load-Store Barrier:
    屏障前的 Load 必须在屏障后的 Store 之前完成

  Store-Store Barrier:
    屏障前的 Store 必须在屏障后的 Store 之前完成

  Store-Load Barrier:
    屏障前的 Store 必须在屏障后的 Load 之前完成
    （最强的屏障）

Full Barrier (Fence):
  包含以上所有屏障的效果
```

## 7. 常见模式的内存序选择

### 7.1 计数器

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

// 纯计数器：使用 Relaxed
struct Counter {
    value: AtomicUsize,
}

impl Counter {
    fn increment(&self) {
        self.value.fetch_add(1, Ordering::Relaxed);
    }

    fn get(&self) -> usize {
        self.value.load(Ordering::Relaxed)
    }
}

// 需要获取精确值的计数器：使用 SeqCst
struct PreciseCounter {
    value: AtomicUsize,
}

impl PreciseCounter {
    fn increment(&self) {
        self.value.fetch_add(1, Ordering::SeqCst);
    }

    fn get(&self) -> usize {
        self.value.load(Ordering::SeqCst)
    }
}
```

### 7.2 标志位与数据传递

```rust
use std::sync::atomic::{AtomicBool, Ordering};

// 标志位 + 数据：使用 Release/Acquire
struct FlagWithData<T> {
    ready: AtomicBool,
    data: std::cell::UnsafeCell<T>,
}

unsafe impl<T: Send> Send for FlagWithData<T> {}
unsafe impl<T: Send> Sync for FlagWithData<T> {}

impl<T> FlagWithData<T> {
    fn set(&self, value: T) {
        unsafe {
            *self.data.get() = value;
        }
        self.ready.store(true, Ordering::Release);
    }

    fn get(&self) -> Option<&T> {
        if self.ready.load(Ordering::Acquire) {
            Some(unsafe { &*self.data.get() })
        } else {
            None
        }
    }
}
```

### 7.3 无锁队列

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

// 无锁栈：使用 AcqRel
struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

impl<T> LockFreeStack<T> {
    fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: ptr::null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Acquire);
            unsafe { (*new_node).next = head; }

            if self.head.compare_exchange(
                head,
                new_node,
                Ordering::AcqRel,  // 成功：Release
                Ordering::Acquire  // 失败：Acquire
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

            if self.head.compare_exchange(
                head,
                next,
                Ordering::AcqRel,
                Ordering::Acquire
            ).is_ok() {
                return Some(unsafe {
                    let node = Box::from_raw(head);
                    node.data
                });
            }
        }
    }
}
```

## 8. 常见陷阱与最佳实践

### 8.1 常见错误

```rust
use std::sync::atomic::{AtomicI32, Ordering};
use std::thread;

// 错误 1：Relaxed 用于同步
fn wrong_relaxed_sync() {
    let flag = AtomicI32::new(0);
    let data = AtomicI32::new(0);

    thread::scope(|s| {
        s.spawn(|| {
            data.store(42, Ordering::Relaxed);  // 错误！
            flag.store(1, Ordering::Relaxed);   // 错误！
        });

        s.spawn(|| {
            while flag.load(Ordering::Relaxed) == 0 {}  // 错误！
            assert_eq!(data.load(Ordering::Relaxed), 42);  // 可能失败！
        });
    });
}

// 错误 2：混合使用不同的内存序
fn wrong_mixed_ordering() {
    let x = AtomicI32::new(0);

    // 生产者使用 Relaxed
    x.store(1, Ordering::Relaxed);

    // 消费者使用 Acquire
    // 不匹配！需要 Release/Acquire 对
    while x.load(Ordering::Acquire) == 0 {}
}

// 正确做法
fn correct_sync() {
    let flag = AtomicI32::new(0);
    let data = AtomicI32::new(0);

    thread::scope(|s| {
        s.spawn(|| {
            data.store(42, Ordering::Relaxed);
            flag.store(1, Ordering::Release);  // 正确
        });

        s.spawn(|| {
            while flag.load(Ordering::Acquire) == 0 {}  // 正确
            assert_eq!(data.load(Ordering::Relaxed), 42);  // 保证成功
        });
    });
}
```

### 8.2 最佳实践

```rust
// 1. 默认使用 SeqCst，优化时再降级
use std::sync::atomic::{AtomicI32, Ordering};

fn default_seqcst() {
    let x = AtomicI32::new(0);
    x.store(1, Ordering::SeqCst);
    let _ = x.load(Ordering::SeqCst);
}

// 2. 成对使用 Release/Acquire
fn paired_ordering() {
    let x = AtomicI32::new(0);
    // 生产者
    x.store(1, Ordering::Release);
    // 消费者
    let _ = x.load(Ordering::Acquire);
}

// 3. RMW 操作使用 AcqRel
fn rmw_acqrel() {
    use std::sync::atomic::AtomicUsize;
    let x = AtomicUsize::new(0);
    x.fetch_add(1, Ordering::AcqRel);
}

// 4. 纯计数器使用 Relaxed
fn counter_relaxed() {
    use std::sync::atomic::AtomicUsize;
    let counter = AtomicUsize::new(0);
    counter.fetch_add(1, Ordering::Relaxed);
}
```

## 9. 综合安全论证

### 9.1 内存序正确性定理

```
定理 (内存序保证):

  1. Release-Acquire 对:
     store(x, Release) →sw load(x, Acquire)
     建立跨线程的 happens-before 关系

  2. SeqCst 全局顺序:
     所有 SeqCst 操作有一个全局一致的顺序

  3. DRF-SC:
     无数据竞争的程序表现为顺序一致性

  证明概要:
    - Release 阻止前置操作重排到后面
    - Acquire 阻止后续操作重排到前面
    - 两者配对建立同步边
    - 传递性传播 happens-before
    ∎
```

### 9.2 不变式总结

```
内存序使用的核心不变式:

I1 (配对原则):
  Release 操作必须与 Acquire 操作配对使用

I2 (传递性):
  happens-before 关系是传递的

I3 (原子性):
  所有原子操作都是不可分割的

I4 (可见性):
  happens-before 保证操作的可见性

I5 (无数据竞争):
  使用原子操作避免数据竞争
```

## 10. 总结

本文档深入分析了 Rust 内存序的形式化语义：

1. **Happens-Before**：定义了操作间的可见性关系
2. **五种内存序**：
   - Relaxed：仅原子性
   - Acquire/Release：建立同步边
   - AcqRel：RMW 操作的组合
   - SeqCst：全局顺序一致性
3. **内存模型公理化**：DRF-SC 保证
4. **弱内存行为**：Store Buffer 和内存屏障
5. **常见模式**：计数器、标志位、无锁队列
6. **最佳实践**：避免常见陷阱，选择合适的内存序

这些形式化定义确保了 Rust 并发程序在使用原子操作时的正确性和可移植性。
