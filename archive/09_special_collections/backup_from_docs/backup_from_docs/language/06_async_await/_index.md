# C06. 异步编程 (Asynchronous Programming)

本分册深入探讨 Rust 的异步编程模型，这是 Rust 解决高并发 I/O 密集型问题的核心武器。与 `c05_threads` 中讨论的基于线程的并发不同，异步编程允许在极少数的操作系统线程上管理成千上万的并发任务。

## 核心哲学 (Core Philosophy)

1. **零成本抽象 (Zero-Cost Abstraction)**: `async/await` 语法在编译时被转换为高效的状态机，没有运行时的虚拟机或垃圾回收开销，性能接近手动优化的底层代码。
2. **内存安全 (Memory Safety)**: 异步模型与 Rust 的所有权和借用系统深度集成。`Future` 的生命周期和 `Send`/`Sync` 约束在编译时就保证了异步任务的内存安全，消除了数据竞争。
3. **运行时与语言分离**: Rust 语言本身只提供 `Future` Trait 和 `async/await` 语法等核心原语。具体的执行器 (Executor) 和运行时 (Runtime) 则由社区生态系统提供（如 `tokio`, `async-std`），允许用户根据场景选择最合适的执行策略。
4. **协作式调度 (Cooperative Scheduling)**: Rust 的异步任务是协作式的。任务在遇到 `.await` 时会主动让出控制权，而不是被动地被操作系统抢占。这减少了不必要的上下文切换，提高了效率。

## 章节目录

- **`01_introduction_and_philosophy.md`**: 异步编程导论与哲学
  - *核心概念：`Future`, `async/await`, 状态机, `Waker`*
  - *机制：轮询 (Polling) 模型*
- **`02_runtime_and_execution_model.md`**: 运行时与执行模型
  - *核心概念：执行器 (Executor), 运行时 (Runtime), 任务 (Task)*
  - *机制：`tokio` vs `async-std`, 任务调度*
- **`03_pinning_and_unsafe_foundations.md`**: Pinning 与 Unsafe 基础
  - *核心概念：`Pin<T>`, `Unpin`*
  - *机制：自引用结构与内存固定*
- **`04_streams_and_sinks.md`**: 异步流 (Streams)
  - *核心概念：`Stream` Trait*
  - *机制：异步的迭代器*
- **`05_async_in_traits_and_ecosystem.md`**: 异步 Trait 与生态
  - *核心概念：`async-trait` crate*
  - *机制：动态与静态分派下的异步 Trait*
- **`06_critical_analysis_and_advanced_topics.md`**: 批判性分析与高级主题
  - *核心概念：函数"颜色", 架构兼容性*
  - *机制：与同步代码交互，设计权衡*

<!-- LATER_CHAPTERS -->