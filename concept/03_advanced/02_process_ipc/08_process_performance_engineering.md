> **EN**: Process Performance Engineering in Rust
> **Summary**: Performance analysis, profiling tools, zero-copy IPC, process pool optimization, and production monitoring for Rust process management.

# Rust 进程性能工程

> **权威页地位**：本页为 Rust 进程级性能工程概念的 canonical 解释来源。
>
> 通用性能优化方法论请参见 [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/15_performance_optimization.md)。

## 1. 概念定义

**进程性能工程 (Process Performance Engineering)** 关注进程创建、执行、通信与回收全链路的性能：减少进程创建开销、降低 I/O 延迟、避免资源泄漏、实现可观测的度量闭环。

## 2. 关键性能指标

| 指标 | 说明 | 测量方式 |
| :--- | :--- | :--- |
| 进程创建延迟 | spawn 到 exec 完成的时间 | 高分辨率计时 |
| 吞吐量 | 单位时间处理任务数 | Criterion / 自定义计数 |
| 内存占用 | 子进程 RSS、句柄数 | sysinfo / procfs |
| I/O 等待 | 管道阻塞时间 | strace / perf |
| 回收延迟 | `wait` 返回时间 | 高分辨率计时 |

## 3. 性能分析工具

- **perf**：Linux 采样分析，定位热点。
- **cargo-flamegraph**：可视化调用栈。
- **strace/ltrace**：追踪系统调用与库调用。
- **pprof**：运行时 CPU profiling。
- **dhat/heaptrack**：堆分配分析。

## 4. 优化策略

### 4.1 减少进程创建开销

- 使用进程池复用长期运行的 worker。
- 预创建 worker，避免任务到达时才 spawn。
- Windows 上进程创建成本更高，优先使用进程池。

### 4.2 I/O 优化

- 使用异步管道与 `tokio::process` 避免阻塞线程。
- 合理设置缓冲区大小，批量读写。
- 避免父子进程同时双向写入导致的死锁。

### 4.3 零拷贝 IPC

- **splice**：Linux 上在两个文件描述符之间直接移动数据，避免用户空间拷贝。
- **sendfile**：文件到 socket 的高效传输。
- **mmap**：大文件共享访问，减少 `read`/`write` 次数。

## 5. 进程池性能

- 池大小应根据 CPU 核心数、I/O 密集度和外部资源限制调整。
- 使用有界队列防止任务无限堆积。
- 监控队列深度、worker 利用率、任务等待时间。

## 6. 生产监控

- 暴露进程创建/退出速率、活跃进程数、退出码分布。
- 使用 Prometheus 等指标系统建立基线与告警。
- 定期进行回归测试，防止性能退化。

## 7. 相关概念

- [进程模型与生命周期](01_process_model_and_lifecycle.md)
- [异步进程管理](03_async_process_management.md)
- [IPC 机制](05_ipc_mechanisms.md)
- [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/15_performance_optimization.md)

---

> **权威来源**: [Rust Performance Book](https://nnethercote.github.io/perf-book/) · [cargo-flamegraph](https://github.com/flamegraph-rs/flamegraph) · [nix crate](https://docs.rs/nix/) · [memmap2 crate](https://docs.rs/memmap2/)
