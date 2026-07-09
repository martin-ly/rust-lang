> **EN**: C07 Process Management — One-Page Summary (c07_process example index)
> **Summary**: A stub page pointing to the canonical concept authority for Rust process management. The c07_process crate provides runnable process/IPC examples.

# C07 进程管理 - 一页纸总结（c07_process 示例索引）

> **权威来源**: 进程模型、生命周期、`std::process::Command`、IPC 等完整解释见
> [`concept/03_advanced/02_process_ipc/01_process_model_and_lifecycle.md`](../../../concept/03_advanced/02_process_ipc/01_process_model_and_lifecycle.md)。

本文件原为 `c07_process` crate 的通用进程管理一页纸总结。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/03_advanced/02_process_ipc/`，此处仅保留索引与 canonical 链接。

## 本 crate 相关示例

- `crates/c07_process/examples/`：进程与 IPC 可运行示例。
- `crates/c07_process/src/bin/`：进程管理演示程序。

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| 进程创建、`Command`、`spawn`、`output` | [`concept/03_advanced/02_process_ipc/01_process_model_and_lifecycle.md`](../../../concept/03_advanced/02_process_ipc/01_process_model_and_lifecycle.md) |
| 标准 IO 重定向、管道 | 同上 |
| 信号处理、SIGINT/SIGTERM | 同上 |
| IPC、Unix domain socket | [`concept/03_advanced/02_process_ipc/05_ipc_mechanisms.md`](../../../concept/03_advanced/02_process_ipc/05_ipc_mechanisms.md) |
| 速查练习 | [`concept/SUMMARY.md`](../../../concept/SUMMARY.md) |
