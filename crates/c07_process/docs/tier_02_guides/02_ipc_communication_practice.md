> **EN**: Inter-Process Communication Mechanisms in Rust (c07_process example index)
> **Summary**: A stub page pointing to the canonical concept authority for IPC mechanisms. The c07_process crate provides runnable pipe, socket, and shared-memory examples.

# C07 Tier 2: IPC 通信实践（c07_process 示例索引）

> **权威来源**: 管道、命名管道、Unix 套接字、TCP/UDP 套接字、共享内存、消息队列、信号等完整解释见
> [`concept/03_advanced/02_process_ipc/05_ipc_mechanisms.md`](../../../../concept/03_advanced/02_process_ipc/05_ipc_mechanisms.md)。

本文件原为 `c07_process` crate 的通用进程概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/03_advanced/02_process_ipc/`，此处仅保留索引与
canonical 链接。

## 本 crate 相关示例

- `crates/c07_process/examples/`：管道、套接字、共享内存等 IPC 示例。
- `crates/c07_process/src/bin/`：IPC 机制演示程序。

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| IPC 机制 | [`concept/03_advanced/02_process_ipc/05_ipc_mechanisms.md`](../../../../concept/03_advanced/02_process_ipc/05_ipc_mechanisms.md) |
| 进程模型与生命周期 | [`concept/03_advanced/02_process_ipc/01_process_model_and_lifecycle.md`](../../../../concept/03_advanced/02_process_ipc/01_process_model_and_lifecycle.md) |
| 并发模型 | [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../../concept/03_advanced/00_concurrency/01_concurrency.md) |
