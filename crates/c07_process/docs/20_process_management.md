> **EN**: Process Management in Rust (c07_process example index)
> **Summary**: A stub page pointing to the canonical concept authority for Rust process management. The c07_process crate provides runnable examples of process creation, lifecycle, and IPC.

# 进程管理详解（c07_process 示例索引）

> **权威来源**: 进程创建、子进程生命周期、进程间通信、环境变量、信号处理、资源监控等完整解释见
> [`concept/03_advanced/08_process_ipc/01_process_model_and_lifecycle.md`](../../../concept/03_advanced/08_process_ipc/01_process_model_and_lifecycle.md)。

本文件原为 `c07_process` crate 的通用进程管理概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/03_advanced/08_process_ipc/`，此处仅保留索引与
canonical 链接。

## 本 crate 相关示例

- `crates/c07_process/examples/`：`std::process` 与 `tokio::process` 可运行示例。
- `crates/c07_process/src/bin/`：进程创建、生命周期与 IPC 演示程序。

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| 进程模型与生命周期 | [`concept/03_advanced/08_process_ipc/01_process_model_and_lifecycle.md`](../../../concept/03_advanced/08_process_ipc/01_process_model_and_lifecycle.md) |
| IPC 机制 | [`concept/03_advanced/08_process_ipc/05_ipc_mechanisms.md`](../../../concept/03_advanced/08_process_ipc/05_ipc_mechanisms.md) |
| 异步进程管理 | [`concept/03_advanced/08_process_ipc/03_async_process_management.md`](../../../concept/03_advanced/08_process_ipc/03_async_process_management.md) |
