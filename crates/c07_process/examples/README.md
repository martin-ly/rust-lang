# C07 进程与 IPC 示例

本目录包含 Rust 进程管理和进程间通信的核心示例代码。

---

## 📚 示例列表

### 基础示例 ⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `process_spawning.rs` | 进程创建 | Command |
| `ipc_pipes.rs` | 管道通信 | stdin/stdout |
| `signals.rs` | 信号处理 | SIGTERM |
| `environment.rs` | 环境变量 | env::var |

### 进阶示例 ⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `shared_memory.rs` | 共享内存 | mmap |
| `message_queues.rs` | 消息队列 | POSIX MQ |
| `process_pools.rs` | 进程池 | 预分叉 |

---

## 🚀 快速开始

```bash
# 运行进程创建示例
cargo run --example process_spawning

# 运行管道通信示例
cargo run --example ipc_pipes
```

---

## 🔗 相关文档

- [进程与 IPC 指南](../docs/README.md)

---

*示例基于 Rust 1.94+，Edition 2024*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
