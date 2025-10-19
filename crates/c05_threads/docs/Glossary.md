# C05: 术语表 (Glossary)

> **文档定位**: 并发编程相关术语的快速参考手册  
> **使用方式**: 查找不理解的术语，了解准确定义  
> **相关文档**: [FAQ](./FAQ.md) | [主索引](./00_MASTER_INDEX.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.89+  
**文档类型**: 📚 参考资料

---

## 📋 术语索引

本术语表收录了 Rust 并发编程中的核心概念和术语。按字母顺序排列，方便快速查找。

---

## 目录

- [C05: 术语表 (Glossary)](#c05-术语表-glossary)
  - [📋 术语索引](#-术语索引)
  - [目录](#目录)
  - [术语](#术语)
    - [`Arc<T>` (Atomically Reference Counted)](#arct-atomically-reference-counted)
    - [Atomics (原子类型)](#atomics-原子类型)
    - [Concurrency (并发)](#concurrency-并发)
    - [Data Race (数据竞争)](#data-race-数据竞争)
    - [Deadlock (死锁)](#deadlock-死锁)
    - [Lock-Free (无锁编程)](#lock-free-无锁编程)
    - [Memory Ordering (内存排序)](#memory-ordering-内存排序)
    - [Message Passing (消息传递)](#message-passing-消息传递)
    - [`Mutex<T>` (Mutual Exclusion)](#mutext-mutual-exclusion)
    - [Parallelism (并行)](#parallelism-并行)
    - [Rayon](#rayon)
    - [`RwLock<T>` (Read-Write Lock)](#rwlockt-read-write-lock)
    - [Send (Trait)](#send-trait)
    - [Shared-State Concurrency (共享状态并发)](#shared-state-concurrency-共享状态并发)
    - [Sync (Trait)](#sync-trait)
    - [Work-Stealing (工作窃取)](#work-stealing-工作窃取)

## 术语

### `Arc<T>` (Atomically Reference Counted)

一个线程安全的引用计数智能指针。`Arc<T>` 允许多个所有者（通常在不同线程中）共享对同一份数据 `T` 的所有权。它使用原子操作来管理引用计数，确保其在多线程环境下的安全。

### Atomics (原子类型)

提供在硬件级别上保证为原子（不可分割）操作的类型，如 `AtomicI32`, `AtomicBool`。它们是构建更高级同步原语（如 `Mutex`）的基石。

### Concurrency (并发)

一种程序**构造**，用于处理多个逻辑上独立的任务。这些任务可以在时间上重叠执行，其核心在于管理任务间的交互与访问。

### Data Race (数据竞争)

一个严格定义的未定义行为，当两个或以上线程并发访问同一内存位置，其中至少一个是写操作，且没有使用任何同步机制时发生。Rust 的所有权系统在编译时就旨在消除数据竞争。

### Deadlock (死锁)

两个或多个并发进程（或线程）因各自持有对方需要的资源而无限期等待对方释放资源的状态。例如，线程 A 持有锁 1 并等待锁 2，而线程 B 持有锁 2 并等待锁 1。

### Lock-Free (无锁编程)

一种不使用锁（如 `Mutex`）来编写并发代码的编程范式，完全依赖于原子操作。它能避免死锁，但在实践中极其复杂和困难。

### Memory Ordering (内存排序)

用于控制 CPU 如何对内存操作（读/写）进行排序的指令。它是在原子层面进行编程时必须处理的复杂问题，用于确保一个线程的写入对其他线程可见。

### Message Passing (消息传递)

一种并发模型，线程通过通道（Channel）发送和接收消息来进行通信，而不是直接共享内存。它遵循"不要通过共享内存来通信"的哲学。

### `Mutex<T>` (Mutual Exclusion)

一个互斥锁，它确保在任何时刻只有一个线程能够访问其内部保护的数据 `T`。这是最常见的同步原语之一。

### Parallelism (并行)

一种程序**执行**方式，指同时执行多个计算任务以加速处理。它需要多核等硬件支持，其核心在于将计算任务分解并同时处理。

### Rayon

Rust 生态中一个著名的数据并行库。它提供了并行迭代器（`par_iter`），可以轻松地将顺序的、计算密集的代码转换为高性能的并行代码。

### `RwLock<T>` (Read-Write Lock)

一个读写锁。它允许多个线程同时读取数据（读锁），但写操作（写锁）必须是完全排他的。适用于"读多写少"的场景以提高性能。

### Send (Trait)

一个标记 Trait，表示一个类型的所有权可以被安全地**转移**到另一个线程。

### Shared-State Concurrency (共享状态并发)

一种并发模型，多个线程通过访问同一块共享内存来进行通信，并使用锁等同步原语来协调访问。

### Sync (Trait)

一个标记 Trait，表示一个类型的**引用** (`&T`) 可以被安全地在多个线程之间**共享**。

### Work-Stealing (工作窃取)

一种高效的并行任务调度算法，被 `Rayon` 使用。当一个工作线程变为空闲时，它会从其他繁忙线程的任务队列中"窃取"任务来执行，以实现负载均衡。
