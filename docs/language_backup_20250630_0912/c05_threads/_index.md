# C05. 并发：线程、消息与同步 (Concurrency: Threads, Messaging, and Synchronization)

本分册深入探讨 Rust 的并发编程模型，展示该语言如何通过其核心的所有权和类型系统来实现"无畏并发"(Fearless Concurrency)。我们将从创建原生操作系统线程开始，逐步学习 Rust 中两种主要的并发范式：用于在线程间传递所有权的**消息传递 (Message Passing)**，以及允许多个线程安全访问同一份数据的**共享状态并发 (Shared-State Concurrency)**。

## 核心哲学 (Core Philosophy)

1. **所有权是并发安全的关键**: Rust 将所有权模型扩展到并发领域。通过 `move` 关键字将数据的所有权转移给线程，以及通过 `Mutex` 等智能指针临时出借所有权，Rust 在编译时就消除了整类的数据竞争 (Data Race) 问题。
2. **明确区分 `Send` 和 `Sync`**: Rust 的类型系统通过 `Send` 和 `Sync` 这两个标记 Trait，精确地定义了哪些类型可以在线程间安全地转移所有权 (`Send`)，哪些可以被多线程安全地共享引用 (`Sync`)。这种编译时的精细控制是实现"无畏并发"的又一基石。
3. **拥抱多种并发模型**: Rust 并不强制开发者使用单一的并发模型。标准库同时提供了一流的通道 (Channel) 实现以支持消息传递，也提供了如 `Mutex`, `RwLock`, `Arc` 等同步原语以支持共享状态。开发者可以根据具体场景选择最合适的工具。

## 章节目录

- **`01_threads_and_ownership.md`**: 线程与所有权
  - *核心概念：`thread::spawn`, `JoinHandle`, `move` 闭包*
  - *机制：所有权如何防止数据竞争*
- **`02_message_passing.md`**: 使用消息传递在线程间通信
  - *核心概念：通道 (Channels), `mpsc`*
  - *机制：所有权如何通过消息传递保证安全*
- **`03_synchronization_primitives.md`**: 共享状态并发与同步原语
  - *核心概念：`Mutex`, `Arc`, `RwLock`*
  - *机制：`Send` 与 `Sync` Trait 如何在编译时保证安全*
- **`04_parallelism_and_beyond.md`**: 并行计算与生态系统
  - *核心概念：并发 vs. 并行, Rayon*
  - *机制：工作窃取调度与数据并行*
- **`05_advanced_topics_and_summary.md`**: 高级主题与总结
  - *核心概念：原子类型, 无锁编程*
  - *机制：内存排序与本章回顾*

<!-- LATER_CHAPTERS -->