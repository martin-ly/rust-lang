# C05 线程与并发 - 示例中心

> **创建日期**: 2025-10-20
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 100% 完成
> **概念说明**: 本示例集展示 Rust 线程编程的各种技术，包括作用域线程、消息传递、共享状态、无锁数据结构和高级同步原语。

---

## 示例概览

本目录包含 **15+ 个核心示例**，涵盖线程与并发编程的所有重要主题：

- ✅ 线程创建与管理
- ✅ 消息传递 (mpsc)
- ✅ 共享状态同步
- ✅ 线程安全 trait (Send/Sync)
- ✅ 无锁数据结构
- ✅ Rust 1.93.0 新特性

---

## 示例分类导航

### 基础示例 ⭐

适合了解 Rust 并发基础的开发者。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `thread_spawning.rs` | 线程创建 | `spawn`、`join` | `cargo run --example thread_spawning` |
| `message_passing.rs` | 消息传递 | `mpsc` 通道 | `cargo run --example message_passing` |
| `shared_state.rs` | 共享状态 | `Mutex`、`Arc` | `cargo run --example shared_state` |
| `thread_safety.rs` | 线程安全 | `Send`、`Sync` | `cargo run --example thread_safety` |

### 进阶示例 ⭐⭐

适合需要高级并发模式的开发者。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `thread_pools.rs` | 线程池 | 工作窃取 | `cargo run --example thread_pools` |
| `parallel_patterns.rs` | 并行模式 | 分治、流水线 | `cargo run --example parallel_patterns` |
| `lock_free.rs` | 无锁编程 | `Atomic`、`CAS` | `cargo run --example lock_free` |
| `crossbeam_demo.rs` | Crossbeam | epoch 内存管理 | `cargo run --example crossbeam_demo` |

### 高级示例 ⭐⭐⭐

适合需要极致性能的高级开发者。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `rayon_parallel.rs` | Rayon 并行 | 数据并行 | `cargo run --example rayon_parallel` |
| `thread_affinity.rs` | 线程亲和性 | CPU 绑定 | `cargo run --example thread_affinity` |
| `message_passing_demo.rs` | 消息传递综合 | 多种 channel | `cargo run --example message_passing_demo` |
| `priority_channels_demo.rs` | 优先级通道 | 优先级队列 | `cargo run --example priority_channels_demo` |

### Rust 1.93.0 特性示例 ⭐ NEW

展示最新 Rust 版本的线程相关改进。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `rust_192_features_demo.rs` | Rust 1.93.0 特性演示 | `rotate_right`、`div_ceil` | `cargo run --example rust_192_features_demo` |
| `stream_backpressure_demo.rs` | 背压处理 | Stream + 背压 | `cargo run --example stream_backpressure_demo` |
| `backpressure_overview_demo.rs` | 背压策略总览 | 四种背压策略 | `cargo run --example backpressure_overview_demo` |
| `stream_rate_batch_demo.rs` | 限速+批量 | 流控制 | `cargo run --example stream_rate_batch_demo` |
| `rust_190_features_demo.rs` | Rust 1.90 特性演示 | 历史参考 | `cargo run --example rust_190_features_demo` |
| `advanced_rust190_demo.rs` | 高级 Rust 1.90 特性 | 综合演示 | `cargo run --example advanced_rust190_demo` |

---

## 如何运行示例

### 基础运行

```bash
# 进入模块目录
cd crates/c05_threads

# 运行线程基础示例
cargo run --example thread_spawning

# 运行消息传递示例
cargo run --example message_passing

# 运行共享状态示例
cargo run --example shared_state
```

### 运行特定模块演示

```bash
# 作用域线程演示
cargo run -p c05_threads --example basic

# 消息传递综合示例
cargo run -p c05_threads --example message_passing_demo

# 优先级通道示例
cargo run -p c05_threads --example priority_channels_demo

# Stream + 背压综合示例
cargo run -p c05_threads --example stream_backpressure_demo

# 背压处理总览示例
cargo run -p c05_threads --example backpressure_overview_demo

# 限速 + 批量示例
cargo run -p c05_threads --example stream_rate_batch_demo
```

### 运行测试

```bash
# 运行所有测试
cargo test -p c05_threads

# 运行 Rust 1.93.0 特性测试
cargo test --test rust_192_comprehensive_tests

# 运行特定模块测试
cargo test concurrency::scoped_threads
cargo test lockfree::lockfree_ring_buffer
cargo test synchronization::adaptive_locks
cargo test rust_192_features
```

### 运行基准测试

```bash
# 运行所有基准测试
cargo bench -p c05_threads

# 运行 Rust 1.93.0 特性基准测试
cargo bench --bench rust_192_benchmarks

# 运行并发基准测试
cargo bench --bench concurrency_benchmark

# 启用 CPU 原生优化
RUSTFLAGS="-C target-cpu=native" cargo bench -p c05_threads
```

---

## 学习建议

### 初学者路径 (第1-2周)

1. **学习线程创建**

   ```bash
   cargo run --example thread_spawning
   ```

   - `thread::spawn()`
   - `JoinHandle` 和 `join()`
   - 闭包在线程中的使用

2. **掌握消息传递**

   ```bash
   cargo run --example message_passing
   cargo run --example message_passing_demo
   ```

   - `mpsc::channel()`
   - 发送和接收消息
   - 多生产者单消费者

3. **理解共享状态**

   ```bash
   cargo run --example shared_state
   ```

   - `Arc<T>` - 原子引用计数
   - `Mutex<T>` - 互斥锁
   - `RwLock<T>` - 读写锁

### 进阶路径 (第3-4周)

1. **学习线程安全**

   ```bash
   cargo run --example thread_safety
   ```

   - `Send` trait
   - `Sync` trait
   - 线程安全边界

2. **掌握无锁编程**

   ```bash
   cargo run --example lock_free
   cargo run --example crossbeam_demo
   ```

   - 原子操作
   - 内存顺序
   - epoch 内存管理

3. **学习并行模式**

   ```bash
   cargo run --example parallel_patterns
   cargo run --example thread_pools
   ```

   - 分治模式
   - 工作窃取
   - 线程池管理

### 高级路径 (第5周+)

1. **探索高级特性**

   ```bash
   cargo run --example rayon_parallel
   cargo run --example thread_affinity
   ```

   - 数据并行 (Rayon)
   - CPU 亲和性
   - NUMA 感知

2. **Rust 1.93.0 新特性**

   ```bash
   cargo run --example rust_192_features_demo
   ```

   - `rotate_right` 在任务队列中的应用
   - `NonZero::div_ceil` 在线程池计算中的应用
   - 增强的线程管理 API

---

## 关键概念速查

### 创建线程

```rust
use std::thread;

let handle = thread::spawn(|| {
    println!("Hello from thread!");
});

handle.join().unwrap();
```

### 消息传递

```rust
use std::sync::mpsc;
use std::thread;

let (tx, rx) = mpsc::channel();

thread::spawn(move || {
    tx.send("Hello").unwrap();
});

let msg = rx.recv().unwrap();
```

### 共享状态

```rust
use std::sync::{Arc, Mutex};
use std::thread;

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

println!("Result: {}", *counter.lock().unwrap());
```

### 作用域线程 (Rust 1.93.0+)

```rust
use std::thread;

let mut data = vec![1, 2, 3, 4, 5];

thread::scope(|s| {
    s.spawn(|| {
        for item in data.iter_mut() {
            *item *= 2;
        }
    });
});

println!("Processed: {:?}", data);
```

---

## ⚠️ 安全注意事项

并发代码必须遵守 Rust 的线程安全规则：

- **只有实现了 `Send` 的类型可以跨线程传递**
  - 所有权可以在线程间转移
  - 大多数类型都实现了 `Send`

- **只有实现了 `Sync` 的类型可以跨线程共享引用**
  - `&T` 可以安全地在多个线程间共享
  - `Mutex<T>`、`RwLock<T>` 提供了内部可变性

### 常见陷阱

```rust
// ❌ 错误：在闭包中捕获引用可能导致生命周期问题
let data = vec![1, 2, 3];
thread::spawn(|| {
    println!("{:?}", data); // 错误！data 可能在线程结束前被释放
});

// ✅ 正确：使用 move 闭包转移所有权
thread::spawn(move || {
    println!("{:?}", data);
});
```

---

## 相关文档

### 模块文档

- [模块主页](../README.md) - 完整学习指南
- [文档中心](../docs/README.md) - 详细文档导航
- [Tier 2 实践指南](../docs/tier_02_guides/README.md) - 核心实践指南
- [Tier 3 参考文档](../docs/tier_03_references/README.md) - 技术参考

### 理论文档

- [线程与并发指南](../docs/README.md)
- [并发安全概念族谱](../../../docs/research_notes/CONCURRENCY_CONCEPT_MINDMAP.md)
- [多维概念矩阵](../../../docs/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)

### 使用指南

- [线程并发使用指南](../../../docs/THREADS_CONCURRENCY_USAGE_GUIDE.md)
- [快速参考卡片](../../../docs/02_reference/quick_reference/threads_concurrency_cheatsheet.md)

### 外部资源

- [The Rust Book - 并发](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Rust  nomicon - 并发](https://doc.rust-lang.org/nomicon/concurrency.html)
- [Crossbeam 文档](https://docs.rs/crossbeam/)
- [Rayon 文档](https://docs.rs/rayon/)

---

## 性能优化提示

```bash
# 启用 LTO 和优化
# Cargo.toml
[profile.release]
lto = true
codegen-units = 1
opt-level = 3

# 使用 CachePadded 避免伪共享
# crossbeam_utils::CachePadded

# 绑定到 NUMA 节点 (Linux)
# numactl --membind=0 --cpunodebind=0 ./program
```

---

*示例基于 Rust 1.94+，Edition 2024*:

[返回模块主页](../README.md) | [返回上级](../README.md)
