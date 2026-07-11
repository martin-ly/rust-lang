> **EN**: Inter-Process Communication (IPC) Mechanisms in Rust (c07_process example index)
> **Summary**: A stub page pointing to the canonical concept authority for Rust IPC mechanisms. The c07_process crate provides runnable pipe, socket, shared-memory, signal, and message-queue examples.

# C07-02. 进程间通信机制（IPC Mechanisms）（c07_process 示例索引）

> **权威来源**: 管道、命名管道、套接字、共享内存、信号、消息队列等 IPC 机制的完整解释见
> [`concept/03_advanced/08_process_ipc/05_ipc_mechanisms.md`](../../../concept/03_advanced/08_process_ipc/05_ipc_mechanisms.md)。

本文件原为 `c07_process` crate 的通用 IPC 概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/03_advanced/08_process_ipc/`，此处仅保留索引与
canonical 链接。

## 本 crate 相关示例

- `crates/c07_process/examples/`：`std::process` 管道、Unix 域套接字、信号处理等可运行示例。
- `crates/c07_process/src/bin/`：IPC 机制演示程序。

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| IPC 机制 | [`concept/03_advanced/08_process_ipc/05_ipc_mechanisms.md`](../../../concept/03_advanced/08_process_ipc/05_ipc_mechanisms.md) |
| 进程模型与生命周期 | [`concept/03_advanced/08_process_ipc/01_process_model_and_lifecycle.md`](../../../concept/03_advanced/08_process_ipc/01_process_model_and_lifecycle.md) |
| 高级进程管理 | [`concept/03_advanced/08_process_ipc/02_advanced_process_management.md`](../../../concept/03_advanced/08_process_ipc/02_advanced_process_management.md) |
