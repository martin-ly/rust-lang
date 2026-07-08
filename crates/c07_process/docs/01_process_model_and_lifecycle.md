> **EN**: Process Model and Lifecycle in Rust (c07_process example index)
> **Summary**: A stub page pointing to the canonical concept authority for Rust process management. The c07_process crate provides runnable std::process, tokio::process, and IPC examples.

# C07-01. 进程模型与生命周期（c07_process 示例索引）

> **权威来源**: 进程模型、生命周期、资源控制、跨平台安全抽象等完整解释见
> [`concept/03_advanced/02_process_ipc/01_process_model_and_lifecycle.md`](../../../concept/03_advanced/02_process_ipc/01_process_model_and_lifecycle.md)。

本文件原为 `c07_process` crate 的通用进程概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/03_advanced/02_process_ipc/`，此处仅保留索引与
canonical 链接。

## 本 crate 相关示例

- `crates/c07_process/examples/`：`std::process`、`tokio::process`、IPC、信号、进程池等可运行示例。
- `crates/c07_process/src/bin/`：进程管理、超时控制、资源限制等演示程序。

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| 进程模型与生命周期 | [`concept/03_advanced/02_process_ipc/01_process_model_and_lifecycle.md`](../../../concept/03_advanced/02_process_ipc/01_process_model_and_lifecycle.md) |
| 异步编程 | [`concept/03_advanced/01_async/02_async.md`](../../../concept/03_advanced/01_async/02_async.md) |
| 并发模型 | [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../concept/03_advanced/00_concurrency/01_concurrency.md) |
