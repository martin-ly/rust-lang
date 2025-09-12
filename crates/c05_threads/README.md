# Rust 线程编程模块 (c05_threads)

> 导航：返回 [`rust-formal-engineering-system`](../../rust-formal-engineering-system/README.md) · 同步范式 [`01_synchronous/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/01_synchronous/00_index.md) · 异步范式 [`02_async/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/02_async/00_index.md)

本模块展示了Rust 1.89中线程编程的各种高级特性，包括作用域线程、工作窃取、无锁数据结构、高级同步原语等。

## 快速开始

- 安装 Rust 工具链：建议使用 `rustup` 并选择稳定版 (>= 1.89)
- 在工作区根目录执行：

```bash
cargo build --release
cargo test -p c05_threads
```

- 运行示例：

```bash
cargo run -p c05_threads --example basic
```

- 运行基准（如有 benches）：

```bash
cargo bench -p c05_threads
```

## 模块结构

### 1. 并发控制 (concurrency)

- **作用域线程** (`scoped_threads.rs`): 展示Rust 1.89的`thread::scope`功能
- **工作窃取** (`work_stealing.rs`): 多种工作窃取算法实现
- **并发模式** (`concurrency_patterns.rs`): 各种并发编程模式

### 2. 无锁数据结构 (lockfree)

- **无锁环形缓冲区** (`lockfree_ring_buffer.rs`): SPSC、MPSC、MPMC实现
- **无锁哈希表** (`lockfree_hashmap.rs`): 高性能并发哈希表
- **无锁B+树** (`lockfree_bplus_tree.rs`): 无锁B+树实现
- **无锁栈和队列** (`lockfree_stack.rs`, `lockfree_queue.rs`): 基础无锁数据结构

### 3. 同步原语 (synchronization)

- **自适应锁** (`adaptive_locks.rs`): 根据负载自动调整的锁
- **无锁屏障** (`lockfree_barrier.rs`): 高性能无锁屏障实现
- **优先级继承** (`priority_inheritance.rs`): 优先级继承机制
- **性能监控** (`performance_monitoring.rs`): 锁性能监控和分析

### 4. 并行计算 (paralelism)

- **NUMA感知** (`numa_aware.rs`): NUMA拓扑感知的并行计算
- **SIMD操作** (`simd_operations.rs`): SIMD向量化操作
- **高级并行算法** (`advanced_parallel_algorithms.rs`): 并行排序、图算法等
- **线程池** (`thread_pools.rs`): 各种线程池实现

### 5. 消息传递 (message_passing)

- **优先级通道** (`priority_channels.rs`): 支持优先级的消息通道
- **背压处理** (`backpressure_handling.rs`): 流量控制和背压处理
- **异步通道** (`async_channels.rs`): 异步消息传递

### 6. 线程管理 (threads)

- **线程亲和性** (`thread_affinity.rs`): CPU亲和性管理
- **优先级调度** (`priority_scheduling.rs`): 线程优先级调度
- **线程管理** (`thread_management.rs`): 高级线程管理功能

## 精选文件索引（快速定位关键实现）

- 并发控制：
  - `src/concurrency/scoped_threads.rs`：作用域线程与借用安全示例
  - `src/concurrency/work_stealing.rs`：多种工作窃取双端队列/全局队列策略
  - `src/concurrency/concurrency_patterns.rs`：常见并发模式集合
- 无锁数据结构：
  - `src/lockfree/lockfree_ring_buffer.rs`：SPSC/MPSC/MPMC 环形缓冲
  - `src/lockfree/lockfree_hashmap.rs`：分段/桶级并行哈希表
  - `src/lockfree/lockfree_bplus_tree.rs`：基于 epoch 的 B+ 树
- 同步原语：
  - `src/synchronization/adaptive_locks.rs`：自适应锁与统计
  - `src/synchronization/lockfree_barrier.rs`：无锁屏障
  - `src/synchronization/priority_inheritance.rs`：优先级继承
- 并行计算：
  - `src/paralelism/numa_aware.rs`：NUMA 感知执行与内存绑定
  - `src/paralelism/simd_operations.rs`：SIMD 示例
  - `src/paralelism/advanced_parallel_algorithms.rs`：并行排序/图算法
- 线程管理：
  - `src/threads/thread_affinity.rs`：CPU 亲和性绑定
  - `src/threads/priority_scheduling.rs`：优先级调度接口
  - `src/threads/thread_management.rs`：线程生命周期、监控、编排

## 主要特性

### 1. 作用域线程 (Rust 1.89 新特性)

```rust
use std::thread;

let mut data = vec![1, 2, 3, 4, 5];

thread::scope(|s| {
    // 可以安全地借用data的可变引用
    let data_ref = &mut data;
    
    s.spawn(|| {
        // 安全地访问data_ref
        for item in data_ref.iter_mut() {
            *item *= 2;
        }
    });
});

// 所有线程在作用域结束前完成
println!("处理后的数据: {:?}", data);
```

### 2. 工作窃取调度器

```rust
let scheduler = WorkStealingScheduler::new(4);

// 推送任务
scheduler.push_global_task(1);
scheduler.push_global_task(2);

// 窃取任务
if let Some(task) = scheduler.steal_task(0) {
    // 处理任务
    println!("处理任务: {}", task);
}
```

### 3. 无锁环形缓冲区

```rust
let buffer = SpscRingBuffer::new(1000);

// 生产者
buffer.try_push(42).unwrap();

// 消费者
if let Some(value) = buffer.try_pop() {
    println!("接收到: {}", value);
}
```

### 4. 自适应锁

```rust
let lock = AdaptiveMutex::new(0);

lock.lock(|data| {
    *data += 1;
});

// 获取性能统计
let stats = lock.get_stats();
println!("锁竞争率: {:.2}%", stats.get_contention_ratio() * 100.0);
```

### 5. 优先级通道

```rust
let channel = PriorityChannel::new();

// 发送不同优先级的消息
channel.send(1, "高优先级消息").unwrap();
channel.send(3, "低优先级消息").unwrap();

// 接收消息（按优先级顺序）
let message = channel.recv();
```

## 性能优化

### 1. 内存布局优化

- 使用`CachePadded`避免伪共享
- 结构体字段重排序优化缓存局部性
- NUMA感知的内存分配

### 2. 并发优化

- 无锁数据结构减少锁竞争
- 工作窃取平衡负载
- 自适应锁根据负载调整策略

### 3. 并行算法

- 并行归并排序
- 并行快速排序
- 并行图算法（BFS、DFS）
- SIMD向量化操作

## 使用示例

### 运行综合演示

```rust
use c05_threads::demo;

// 运行所有演示
demo::run_all_demos();

// 运行性能基准测试
demo::run_performance_benchmarks();

// 运行内存分析
demo::run_memory_analysis();
```

### 运行特定模块演示

```rust
use c05_threads::concurrency::scoped_threads;
use c05_threads::lockfree::lockfree_ring_buffer;
use c05_threads::synchronization::adaptive_locks;

// 作用域线程演示
scoped_threads::demonstrate_scoped_threads();

// 无锁环形缓冲区演示
lockfree_ring_buffer::demonstrate_lockfree_ring_buffers();

// 自适应锁演示
adaptive_locks::demonstrate_adaptive_locks();
```

### 消息传递综合示例

运行示例：

```bash
cargo run -p c05_threads --example message_passing_demo
```

示例覆盖：标准库 channel、crossbeam mpsc、sync_channel、watch 与基于 `ReceiverStream` 的同步流。

### 限速 + 批量示例

运行示例：

```bash
cargo run -p c05_threads --example stream_rate_batch_demo
```

示例覆盖：限速桥接、`next_batch_with_max_wait` 批处理消费。

### 优先级通道示例

运行示例：

```bash
cargo run -p c05_threads --example priority_channels_demo
```

示例覆盖：简化与完整优先级通道的发送与接收顺序对比。

### Stream + 背压综合示例

运行示例：

```bash
cargo run -p c05_threads --example stream_backpressure_demo
```

示例覆盖：用丢弃型背压通道调节生产者速率，桥接为 `ReceiverStream` 并通过超时消费。

### 背压处理总览示例

运行示例：

```bash
cargo run -p c05_threads --example backpressure_overview_demo
```

示例覆盖：Blocking/Dropping/Adaptive/FlowControl 四种背压策略的基础行为对比。

## 基准测试与性能调优

运行基准：

```bash
cargo bench -p c05_threads
```

可选优化：

```bash
RUSTFLAGS="-C target-cpu=native" cargo bench -p c05_threads
```

在 Windows PowerShell 下：

```powershell
$env:RUSTFLAGS = "-C target-cpu=native"
cargo bench -p c05_threads
```

- 构建优化：使用 `--release`，在 `Cargo.toml` 的 `[profile.release]` 中可考虑开启 `lto = true`、`codegen-units = 1`、`opt-level = "z"|"s"|3` 视场景调整。
- 绑定亲和性：在多核/NUMA 机器上结合 `threads/thread_affinity.rs` 将计算线程绑定至本地节点，减少跨 NUMA 访存。
- 伪共享规避：关键共享结构使用 `crossbeam_utils::CachePadded` 或等价手段做缓存行填充。
- 内存回收：对无锁结构启用 `crossbeam-epoch`，并合理选择 `pin` 的频率，平衡延迟与吞吐。
- 工作窃取调参：根据任务粒度调双端队列大小与窃取阈值，避免过度窃取导致的抖动。
- 观测与剖析：结合 `perf`/`vtune`/`Windows Performance Analyzer` 与 crate 内部统计（如自适应锁统计）定位瓶颈。

## 测试

运行所有测试：

```bash
cargo test
```

运行特定模块测试：

```bash
cargo test concurrency::scoped_threads
cargo test lockfree::lockfree_ring_buffer
cargo test synchronization::adaptive_locks
```

## 平台与环境注意事项

1. Windows 线程亲和性与优先级：请参考 `threads/os_thread_features.rs` 与 `threads/thread_affinity.rs`，部分策略在不同版本的 Windows 上权限/效果有所差异。
2. NUMA 支持：Linux 建议安装 `numactl` 并允许绑定节点；Windows 可结合组策略/服务器版本特性，功能覆盖可能不同。
3. 指令集优化：在支持 AVX2/AVX-512 的机器上，添加 `RUSTFLAGS=-C target-cpu=native` 以启用对应优化。
4. 释放构建：务必使用 `--release` 进行性能评测；debug 构建仅用于开发调试。
5. 观测工具：
   - Linux：`perf`, `numactl`, `hwloc`, `flamegraph`
   - Windows：`WPA`, `xperf`, `ProcMon`, `Process Explorer`

### 参数建议（参考）

- 背压缓冲区：通用建议 `512~4096`；CPU 核数×队列深度作为上界起点。
- Dropping 阈值：`0.8~0.95`；吞吐优先上调，延迟优先下调。
- Adaptive 水位线：高水位 `0.6~0.8`，低水位 `0.2~0.4`；间隔 `50~200ms`。
- FlowControl 窗口：窗口大小≈消费速率×重置周期；重置 `100~500ms`。
- 公平策略：`fairness_ratio=2~4`；高优先级阈值根据业务优先级层数取 `1~3`。
- NUMA：将线程与内存绑定至同一 NUMA 节点；跨节点通信优先使用无锁/批量化接口减少跳变。

## 常见问题（FAQ）

- 如何在不引入数据竞争的情况下复用可变引用？
  - 使用 `thread::scope` 与作用域受限的借用，或通过 `Arc<Mutex<_>>`/无锁结构封装共享可变状态。
- 工作窃取为何在轻负载时波动较大？
  - 任务过细导致窃取/协调开销相对放大；增大任务粒度或设置本地队列优先策略可改善。
- 无锁结构什么时候优于基于锁的结构？
  - 高竞争、短临界区、读多写少等场景更适合；否则简单锁往往更稳健。

## 路线图

- 扩展更多并行算法范式（分块矩阵乘、图匹配、最短路并行变体）。
- 引入自适应工作窃取策略（基于拥塞和缓存命中率信号）。
- 增强监控面板：统一导出 `metrics`，支持 `prometheus`/`opentelemetry` 集成。
- 增补跨平台亲和性/优先级抽象层，细化到核心/NUMA 节点级策略。

## 依赖

主要依赖：

- `crossbeam`: 无锁数据结构和并发原语
- `rayon`: 数据并行处理
- `parking_lot`: 高性能锁实现
- `dashmap`: 并发哈希表

## 注意事项

1. **线程安全**: 所有实现都经过仔细设计以确保线程安全
2. **性能**: 使用最新的Rust优化技术和无锁编程模式
3. **内存管理**: 使用`crossbeam-epoch`进行安全的内存管理
4. **错误处理**: 完善的错误处理和恢复机制

## 贡献

欢迎贡献代码、报告问题或提出改进建议！

## 许可证

本项目采用MIT许可证。
