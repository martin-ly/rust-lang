# C05 线程与并发示例

本目录包含 Rust 线程和并发编程的核心示例代码。

---

## 📚 示例列表

### 基础示例 ⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `thread_spawning.rs` | 线程创建 | spawn、join |
| `message_passing.rs` | 消息传递 | mpsc 通道 |
| `shared_state.rs` | 共享状态 | Mutex、Arc |
| `thread_safety.rs` | 线程安全 | Send、Sync |

### 进阶示例 ⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `thread_pools.rs` | 线程池 | 工作窃取 |
| `parallel_patterns.rs` | 并行模式 | 分治、流水线 |
| `lock_free.rs` | 无锁编程 | Atomic、CAS |
| `crossbeam_demo.rs` | Crossbeam | epoch 内存管理 |

### 高级示例 ⭐⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `rayon_parallel.rs` | Rayon 并行 | 数据并行 |
| `thread_affinity.rs` | 线程亲和性 | CPU 绑定 |

---

## 🚀 快速开始

```bash
# 运行线程基础示例
cargo run --example thread_spawning

# 运行消息传递示例
cargo run --example message_passing

# 运行共享状态示例
cargo run --example shared_state
```

---

## ⚠️ 安全注意

并发代码必须遵守 Rust 的线程安全规则：

- 只有实现了 `Send` 的类型可以跨线程传递
- 只有实现了 `Sync` 的类型可以跨线程共享引用

---

## 🔗 相关文档

- [线程与并发指南](../docs/README.md)
- [并发安全概念族谱](../../../docs/research_notes/CONCURRENCY_CONCEPT_MINDMAP.md)

---

*示例基于 Rust 1.94+，Edition 2024*
