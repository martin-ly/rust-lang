# C06 异步编程示例

本目录包含 Rust 异步编程的核心示例代码。

---

## 📚 示例列表

### 基础示例 ⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `async_basics.rs` | 异步基础 | async/await |
| `futures_demo.rs` | Future 详解 | Future trait |
| `tokio_runtime.rs` | Tokio 运行时 | 运行时选择 |
| `async_channels.rs` | 异步通道 | mpsc、oneshot |

### 进阶示例 ⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `async_traits.rs` | 异步 Trait | async_trait |
| `stream_processing.rs` | 流处理 | Stream、Sink |
| `cancellation.rs` | 取消机制 | CancellationToken |
| `async_locks.rs` | 异步锁 | Mutex、RwLock |

### 高级示例 ⭐⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `pin_unpin.rs` | Pin 与 Unpin | 自引用结构 |
| `async_state_machine.rs` | 异步状态机 | 编译器转换 |
| `io_uring_demo.rs` | io_uring | Linux 异步IO |

---

## 🚀 快速开始

```bash
# 运行异步基础示例
cargo run --example async_basics

# 运行 Tokio 示例
cargo run --example tokio_runtime

# 运行流处理示例
cargo run --example stream_processing
```

---

## 🔗 相关文档

- [异步编程指南](../docs/)
- [异步概念族谱](../../../docs/research_notes/ASYNC_CONCEPT_MINDMAP.md)
- [异步状态机形式化](../../../docs/research_notes/formal_methods/async_state_machine.md)

---

*示例基于 Rust 1.94+，Edition 2024*
