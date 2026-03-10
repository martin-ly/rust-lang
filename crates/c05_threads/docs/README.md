# C05 线程与并发编程

> **文档定位**: 本文档是C05线程模块的主入口，提供模块概览和快速导航
> **先修知识**: [C04 泛型](../../c04_generic/docs/README.md)
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [FAQ](./FAQ.md) | [术语表](./Glossary.md)

**最后更新**: 2025-12-11
**适用版本**: Rust 1.89+ (推荐 1.93.0+)
**难度等级**: ⭐⭐⭐
**文档类型**: 📖 入门指南

---

## 📋 本文内容

本模块系统性探讨了 Rust 并发编程模型，涵盖线程、消息传递、共享状态、并行计算和无锁编程等核心主题，展示了 Rust 如何通过所有权系统和 `Send`/`Sync` Trait，将传统的并发编程转变为一种编译器保驾护航的、"无畏"的工程实践。

---

## 🚀 快速开始

### 安装与运行

```bash
# 构建项目
cargo build --release -p c05_threads

# 运行测试
cargo test -p c05_threads

# 运行示例
cargo run -p c05_threads --example basic

# 运行基准测试
cargo bench -p c05_threads
```

### 推荐学习路径

**新手入门** (3-5天):

1. [01_threads_and_ownership](./01_threads_and_ownership.md) - 线程与所有权
2. [02_message_passing](./02_message_passing.md) - 消息传递
3. [03_synchronization_primitives](./03_synchronization_primitives.md) - 同步原语

**进阶学习** (1-2周):

- [04_parallelism_and_beyond](./04_parallelism_and_beyond.md) - 并发与并行
- [06_parallel_algorithms](./06_parallel_algorithms.md) - 并行算法
- [04_lock_free_programming](./04_lock_free_programming.md) - 无锁编程

**完整导航**: 查看 [主索引](./00_MASTER_INDEX.md)

---

## 📚 内容结构

### 1. 基础并发 (Foundation)

#### 线程基础

- **[01_threads_and_ownership.md](./01_threads_and_ownership.md)** - 线程与所有权原理
- **[01_basic_threading.md](./01_basic_threading.md)** - 基础线程操作实践

#### 并发范式

- **[02_message_passing.md](./02_message_passing.md)** - 消息传递并发模型
- **[02_thread_synchronization.md](./02_thread_synchronization.md)** - 线程同步实践
- **[03_synchronization_primitives.md](./03_synchronization_primitives.md)** - 同步原语详解
- **[03_concurrency_patterns.md](./03_concurrency_patterns.md)** - 常见并发模式

### 2. 并行与优化 (Parallelism & Performance)

- **[04_parallelism_and_beyond.md](./04_parallelism_and_beyond.md)** - 并发与并行的区别
- **[06_parallel_algorithms.md](./06_parallel_algorithms.md)** - 并行算法详解
- **[advanced_concurrency_optimization.md](./advanced_concurrency_optimization.md)** - 高级优化

### 3. 高级主题 (Advanced Topics)

- **[04_lock_free_programming.md](./04_lock_free_programming.md)** - 无锁编程
- **[05_advanced_topics_and_summary.md](./05_advanced_topics_and_summary.md)** - 高级主题总结
- **[05_message_passing.md](./05_message_passing.md)** - 高级消息传递

### 4. 参考资料 (Reference)

- **[FAQ.md](./FAQ.md)** - 常见问题解答
- **[Glossary.md](./Glossary.md)** - 并发术语表
- **[rust_189_features_analysis.md](./rust_189_features_analysis.md)** - Rust 1.89特性分析（历史版本，文件已归档）

---

## 🎯 核心理念

### Rust 并发编程的三大支柱

1. **所有权系统** - 编译时防止数据竞争
2. **Send/Sync Trait** - 类型系统保证线程安全
3. **零成本抽象** - 安全不牺牲性能

### 两种并发范式

**消息传递** (Message Passing):

```rust
use std::sync::mpsc;

let (tx, rx) = mpsc::channel();
// 不要通过共享内存来通信
```

**共享状态** (Shared State):

```rust
use std::sync::{Arc, Mutex};

let data = Arc::new(Mutex::new(0));
// 使用Mutex保护共享数据
```

---

## 🌟 核心概念

### Send 和 Sync

- **`Send`**: 类型可以安全地在线程间传递所有权
- **`Sync`**: 类型可以安全地在线程间共享引用

### 同步原语

- **`Mutex<T>`**: 互斥锁，保护共享数据
- **`RwLock<T>`**: 读写锁，允许多读单写
- **`Arc<T>`**: 原子引用计数，共享所有权
- **`Channel`**: 通道，线程间通信

### 无畏并发

Rust 的编译器确保：

- ✅ 无数据竞争
- ✅ 无悬垂指针
- ✅ 线程安全保证
- ✅ 零成本抽象

---

## 📖 学习资源

### 模块资源

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [示例代码](../examples/README.md) - 实践示例
- [源代码](../src/) - 模块实现
- [基准测试](../benches/) - 性能测试

### 外部资源

- [Rust Book - 并发](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [The Rustonomicon - 并发](https://doc.rust-lang.org/nomicon/concurrency.html)
- [Rayon 文档](https://docs.rs/rayon/)

---

## 💡 使用建议

### 新用户

1. 从线程基础开始学习
2. 理解所有权与并发的关系
3. 掌握两种并发范式
4. 通过示例加深理解

### 常见问题

- **Send vs Sync**: 查看 [FAQ Q1](./FAQ.md#q1-send-和-sync-到底有什么区别我总是搞混)
- **何时用Mutex**: 查看 [FAQ Q2](./FAQ.md#q2-既然-mutex-这么好用为什么-rust-还推崇消息传递)
- **性能优化**: 查看 [advanced_concurrency_optimization](./advanced_concurrency_optimization.md)

---

## 📝 模块状态

**当前版本**: v1.0
**文档状态**: 🔧 整理中
**完成度**: 80%

**最近更新**:

- 2025-10-19: 创建主索引和标准化文档格式
- 2025-01-27: 完成基础文档

---

🚀 **开始学习**: 前往 [主索引](./00_MASTER_INDEX.md) 查看完整导航！
